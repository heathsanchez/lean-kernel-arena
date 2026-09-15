import { Kernel, Stop, REJECT } from "./kernel-base.mjs";

// Retained execution consequence from the constructor-local separator.
//
// When both raw terms are applications of the exact same verified constructor,
// compare their arguments in a cheap-first order before outer evaluation.
// A retained REJECT on any constructor argument is a sound negative consequence
// of constructor rigidity. UNKNOWN / host-stack exhaustion declines the
// shortcut and restores the exact retained conversion state.
//
// Installation is explicit so kernel.mjs can apply this layer only after every
// retained conversion wrapper has finished initializing. This matches the
// independently replayed full-corpus separator exactly.

const SPECULATION_CAP = 50_000;
let installed = false;

function rawSpine(e) {
  const args = [];
  while (Array.isArray(e) && e[0] === "app") {
    args.push(e[2]);
    e = e[1];
  }
  args.reverse();
  return { head: e, args };
}

function cheapPair(a, b) {
  if (a === b) return -1_000_000;
  if (!Array.isArray(a) || !Array.isArray(b)) return -10_000;
  if (a[0] !== b[0]) return -100_000;
  if (["const", "var", "nat", "strlit", "sort"].includes(a[0])) return -50_000;

  let score = 0;
  const stack = [a, b];
  const seen = new Set();
  while (stack.length && score < 256) {
    const x = stack.pop();
    if (!Array.isArray(x) || seen.has(x)) continue;
    seen.add(x);
    score++;
    for (let i = 1; i < x.length; i++)
      if (Array.isArray(x[i])) stack.push(x[i]);
  }
  return score;
}

export function installCtorLocalCheapest() {
  if (installed) return;
  installed = true;
  const retainedEqual = Kernel.prototype.equal;

  Kernel.prototype.equal = function(a, b, ctx = []) {
    if (this.localDefs || (this._ctorLocalDepth ?? 0) > 0)
      return retainedEqual.call(this, a, b, ctx);
    if (this.same(a, b)) return;

    const sa = rawSpine(a);
    const sb = rawSpine(b);
    const sameHead =
      sa.args.length > 0 &&
      sa.args.length === sb.args.length &&
      (sa.head === sb.head || this.same(sa.head, sb.head));
    const declaration =
      sameHead && sa.head?.[0] === "const" ? this.env.get(sa.head[1]) : null;

    if (!sameHead || declaration?.kind !== "ctor")
      return retainedEqual.call(this, a, b, ctx);

    const snapshot = {
      steps: this.steps,
      budget: this.budget,
      frontier: this.conversionFrontier
    };
    this.budget = Math.min(this.budget, this.steps + SPECULATION_CAP);
    this._ctorLocalDepth = 1;

    const order = sa.args
      .map((_, i) => i)
      .sort(
        (i, j) =>
          cheapPair(sa.args[i], sb.args[i]) -
          cheapPair(sa.args[j], sb.args[j])
      );

    try {
      for (const i of order)
        retainedEqual.call(this, sa.args[i], sb.args[i], ctx);
      this._ctorLocalDepth = 0;
      this.budget = snapshot.budget;
      return;
    } catch (e) {
      this._ctorLocalDepth = 0;
      this.budget = snapshot.budget;

      if (e instanceof Stop && e.status === REJECT) throw e;
      if (!(e instanceof Stop || e instanceof RangeError)) throw e;

      this.steps = snapshot.steps;
      this.conversionFrontier = snapshot.frontier;
      return retainedEqual.call(this, a, b, ctx);
    }
  };
}
