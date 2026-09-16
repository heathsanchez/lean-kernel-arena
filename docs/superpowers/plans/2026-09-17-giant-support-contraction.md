# Giant Support Contraction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development when available, otherwise superpowers:executing-plans. Execute test-first and stop at the admission gate if the evidence does not improve the declared residual.

**Goal:** Requalify the kernel's already-verified loose-variable-range consequence as compositional term metadata so the existing exact binder transport can avoid rediscovering support during substitution, then decide by frozen giant and 190-case replay whether the contraction deserves production retention.

**Architecture:** Preserve the current production substitution semantics and `exact-binder-transport-layer.mjs`. Add one execution-only metadata layer that computes the exact existing loose-range summary bottom-up when validated terms and canonical constructed nodes enter the term DAG. Binder transport consumes that summary in O(1) when present and falls back to the current iterative `looseRange` calculation when it is absent. Do not replace substitution, do not add target-name rules, and do not import the old five-argument dynamic-slot special case.

**Tech Stack:** Node.js 24 ESM, JavaScript `WeakMap` metadata, current MathGraph kernel layers, GitHub Actions, Lean Kernel Arena NDJSON witnesses.

**Spec:** `docs/superpowers/specs/2026-09-17-arena-kernel-completion-design.md`

## Global constraints

- Branch: `mda-arena-qualification-v1` only.
- No upstream pull request.
- Frozen pre-change public-corpus baseline: 183 correct / 0 wrong / 7 UNKNOWN / 0 errors at 2,000,000 semantic steps.
- Existing `exact-binder-transport-layer.mjs` remains the semantic implementation of `shift` and `substitute`.
- The new layer may store only an exact structural consequence already computed by `looseRange`: max loose de-Bruijn index + 1 relative to the node.
- Unknown/unsupported syntax must not receive a finite support certificate.
- Every focused semantic regression must stay green.
- Candidate retention requires zero newly wrong verdicts and a measured improvement to at least one declared giant residual under the same semantic budget. If the candidate does not improve the residual, revert it from `production.mjs` and keep only the experiment/evidence in provenance.

---

### Task 1: Add a red test for compositional support reuse

**Files:**
- Create: `genesis/support-metadata.test.mjs`
- Reference: `genesis/binder-transport.test.mjs`
- Reference: `genesis/exact-binder-transport-layer.mjs`

**Step 1: Write the failing test**

Create a Node test that imports production capabilities and the real `Kernel`, builds a term with a large closed/binder-independent application prefix plus one loose-variable tail, validates it, then performs substitution. Assert all of the following:

```js
assert.equal(k.__support?.get(closedPrefix), 0);
assert.ok(k.__support?.get(root) > 0);
assert.deepEqual(substituted, expected);
assert.ok(k.__binderStats.supportHits > 0);
assert.equal(k.__binderStats.supportFallbacks, 0);
```

Also include a dependent binder case proving that a finite support summary does not incorrectly skip substitution:

```js
const dependent=["lam",S,["app",V(0),V(1)]];
assert.deepEqual(k.substitute(dependent,V(3)),["lam",S,["app",V(0),V(4)]]);
```

The first test must fail on the current production kernel because `__support`, `supportHits`, and `supportFallbacks` do not exist.

**Step 2: Run the focused test and confirm RED**

Run:

```bash
node --test genesis/support-metadata.test.mjs
```

Expected: FAIL on the support-metadata assertions, not on unrelated setup.

**Step 3: Commit the red witness**

Commit only the test as `Add red witness for compositional binder support`.

---

### Task 2: Compile the existing loose-range theorem into node metadata

**Files:**
- Create: `genesis/support-metadata-layer.mjs`
- Modify: `genesis/production.mjs`
- Modify: `genesis/exact-binder-transport-layer.mjs`
- Test: `genesis/support-metadata.test.mjs`

**Step 1: Implement a generic support metadata layer**

Extract only the exact structural support calculation already prototyped in `compiled-dynamic-slot-layer.mjs`; do not copy its five-argument substitution shortcut.

The metadata definition is exactly:

```text
sort/const/nat/strlit -> 0
var i                 -> i + 1
app f a               -> max(support(f), support(a))
proj e                 -> support(e)
pi/lam A body          -> max(support(A), max(0, support(body)-1))
let A value body       -> max(support(A), support(value), max(0, support(body)-1))
```

Implement:

```js
k.__support = new WeakMap();
k.__supportStats = {seedVisits:0, makeKnown:0, makeUnknown:0};
```

Wrap `Kernel.prototype.validate` so successful validation is followed by an iterative bottom-up seed of the validated DAG. Wrap `Kernel.prototype.make` so support for a newly returned canonical node is derived in O(1) from child metadata whenever all required child summaries are known. Never call semantic `tick()` solely for metadata bookkeeping.

**Step 2: Make binder transport consume metadata before fallback discovery**

Extend binder stats with:

```js
supportHits: 0,
supportFallbacks: 0
```

At the start of `looseRange(k,root)`, do:

```js
const known=k.__support?.get(root);
if(known!==undefined){
  k.__binderStats.supportHits++;
  return known;
}
k.__binderStats.supportFallbacks++;
```

Keep the current iterative `looseRange` body unchanged as the fallback. When fallback computes a finite exact value and `k.__support` exists, write that same value back to `__support` so future queries become O(1).

**Step 3: Load metadata before exact binder transport in production**

In `genesis/production.mjs`, import:

```js
import "./support-metadata-layer.mjs";
```

immediately before:

```js
import "./exact-binder-transport-layer.mjs";
```

No other production layer changes in this task.

**Step 4: Run focused and full local regressions**

Run:

```bash
node --test genesis/support-metadata.test.mjs
node --test genesis/binder-transport.test.mjs
node genesis/test.mjs
node --test genesis/*.test.mjs
```

Expected: all green. The new support test must show metadata hits and zero fallback for the fully validated witness.

**Step 5: Commit the minimal implementation**

Commit as `Compile exact binder support into term metadata`.

---

### Task 3: Measure the candidate on the two giant residuals without changing semantics

**Files:**
- Create: `genesis/production-support-frontier.mjs`
- Create: `.github/workflows/mda-production-support-frontier.yml`

**Step 1: Add a production-only giant runner**

The runner imports `production.mjs`, checks exactly:

```text
init-prelude                  expected ACCEPT
perf/grind-ring-5             expected ACCEPT
perf/shared-subterm           expected ACCEPT control
```

at a budget supplied by `BUDGET`. Capture for each result:

- status/reason,
- semantic steps,
- constructed nodes,
- elapsed ms,
- frontier declaration,
- summed `__binderStats.supportHits`, `supportFallbacks`, `rangeSkips`, `rangeHits`, `rangeMisses` across kernel runs,
- `__supportStats.seedVisits`, `makeKnown`, `makeUnknown`.

Write `genesis/evidence/production-support-frontier-<budget>.json` and fail only on a wrong verdict or a broken `shared-subterm` control.

**Step 2: Add a focused workflow**

Use the existing giant witness cache key and run the candidate at:

```text
1,000,000
2,000,000
4,000,000
```

Upload each evidence JSON. Do not alter the production semantic budget globally.

**Step 3: Push and read the authoritative CI evidence**

Because `mda-arena-qualification.yml` runs on every push, the same commit also produces the frozen 190-case replay. Record both the giant frontier result and corpus totals before making any further production change.

**Step 4: Apply the admission rule**

Retain support metadata in production only if:

1. wrong verdicts remain 0,
2. all focused regressions pass,
3. at least one giant shows one of: fewer semantic steps to ACCEPT, ACCEPT at a budget where baseline was UNKNOWN, or a strictly later reproducible frontier at the same budget,
4. the other giant does not materially regress its frontier/correctness,
5. `shared-subterm` remains ACCEPT.

If none of those is true, remove the support-metadata import from `production.mjs` and restore binder transport to baseline behavior, leaving the test/experiment as provenance.

---

### Task 4: Causal ablation and next-boundary handoff

**Files:**
- Create: `genesis/production-support-ablation.mjs`
- Modify only if retained: `docs/kernel-handoff/README.md`

**Step 1: Run an ablated production composition**

Construct the same production import sequence but omit `support-metadata-layer.mjs`. Run the same giant witnesses at the smallest budget that separated the retained candidate from baseline.

Expected: the measured support-driven frontier/cost improvement disappears or substantially collapses. If it does not, the causal claim fails and the metadata layer must not be retained as a claimed giant repair.

**Step 2: Replay the 190-case corpus from a clean process**

Use the existing qualification workflow. Promotion requires zero wrong verdicts and no increase in UNKNOWN count attributable to the candidate.

**Step 3: Freeze the resulting residual, not the hoped-for story**

If either giant becomes ACCEPT, record the next remaining UNKNOWN family from the qualification artifact. If neither closes, record the exact post-contraction frontier and charged-work profile and use that evidence to write the next implementation plan. Do not add another optimization in this plan.

**Step 4: Update handoff only with warranted claims**

Record commit SHA, workflow run, before/after giant evidence, 190-case totals, ablation result, and the precise claim boundary. No first-place or completeness claim is allowed at this stage unless the corresponding Arena gates have actually passed.

---

## Plan completion condition

This plan ends when the compositional support contraction has been either:

- **ADMITTED:** focused tests green, zero wrong corpus verdicts, measured giant progress, and causal ablation confirmed; or
- **REVOKED:** no reproducible giant progress or any correctness/control regression.

The next plan must be written from the resulting residual evidence rather than precommitted now.