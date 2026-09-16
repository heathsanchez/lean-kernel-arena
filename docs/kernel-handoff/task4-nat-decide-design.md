# `Nat.decLt` next repair design

No workspace source was modified.

## Simpler root cause

A new `Nat.decLt` certificate is premature. The expensive path already exposes the existing supported primitive `Nat.ble`, but installed execution engines do not consistently redispatch through the native Nat reducer.

Instrumentation of the native Nat wrapper on `isValidChar_UInt32` found:

- the outer wrapper sees three `Nat.ble` applications in the target declaration;
- zero of those become native Nat hits;
- the target still performs about 293K substitutions and 60K WHNF calls.

`native-nat-reduction-layer.mjs` captures `whnf0` when it is imported. Its operand normalization calls that captured predecessor, excluding reducers installed later. Meanwhile `scoped-beta-spine.mjs` and the stack-safe iterative loops directly unfold `d.kind === "def"` inside private evaluator loops rather than returning through the final `Kernel.prototype.whnf` dispatch chain.

An isolated dynamic-operand experiment made the latent primitive call explicit:

```text
Nat.ble (nat 55297) (nat 4294967296)
```

but the inner iterative evaluator still unfolded it instead of invoking the native rule. This confirms both halves of the dispatch gap: later reducers can make the operands compact, and the primitive head then bypasses the native hook inside the engine loop.

## Concrete repair

Refactor existing primitive reduction into one internal dispatcher used by every evaluator:

```js
// null means “no primitive rule matched”; a term is a completed reduction.
Kernel.prototype.tryNativeNat = function (term, reduceOperand) { ... };
```

The dispatcher should contain the current exact primitive cases only (`succ`, `add`, `sub`, `mul`, `div`, `mod`, `beq`, `ble`). It must retain the current capability checks, BigInt parsing, division/mod-zero behavior, and constructor/literal recognition. This adds no `Nat.decLt`, `Decidable.decide`, Char, UInt32, dictionary, or declaration-name shortcut.

Call the same dispatcher at three locations:

1. the ordinary native `Kernel.prototype.whnf` wrapper;
2. `scoped-beta-spine`'s `iterativeRecWhnf`, after a complete head/application spine is available and before a `def` head is unfolded;
3. both stack-safe head loops (`fullStackWhnf` and the multi-beta/continuation loop), at the equivalent point before direct definition unfolding.

The engine supplies its own `reduceOperand` callback, so operands stay in that engine and later installed primitive reducers remain reachable. Use a narrow reentrancy token around operand dispatch rather than a captured predecessor function. A primitive miss must return `null` without changing the term, steps, frontier, or evaluator state; the existing loop then unfolds normally.

For an iterative engine, the successful result must be fed back through its existing `attach`/frame-resume mechanism rather than returned blindly, so projections, recursor frames, and extra application arguments remain intact.

## Why this is warranted

The rule is already part of the retained native Nat primitive set. The repair changes only dispatch reachability: identical fully applied primitive terms receive the identical reducer regardless of whether ordinary, scoped-beta, local-continuation, or full-stack execution reached them. It does not infer semantics from `Nat.decLt`, `Decidable.decide`, `UInt32.size`, a dictionary name, or the enclosing declaration.

The source equality then reduces by existing definitions:

1. `Nat.decLt a b` unfolds to `Nat.decLe (Nat.succ a) b`.
2. `Nat.decLe` branches on `Nat.ble (Nat.succ a) b = true`.
3. Existing compact reducers produce `a = 55296`, `Nat.succ a = 55297`, and `b = UInt32.size = 4294967296`.
4. The already-supported native `Nat.ble` rule computes `55297 ≤ 4294967296`, yielding `Bool.true`.
5. Ordinary `dite` and `Decidable.decide` reduction selects the true constructors. No proof body is inspected or synthesized.

Because this path uses the actual checked definitions for `decLt`, `decLe`, and `decide`, no new 65-declaration/135,512-byte transitive fingerprint is needed. A proposed smaller 15-declaration fingerprint was still 12,112 bytes and brittle; the dispatch fix is both smaller and more general.

## Required tests

- For each evaluator mode (ordinary, scoped multi-beta, local continuation, full-stack), reduce the same fully applied compact `Nat.ble` and assert identical true and false results.
- Exercise large operands such as `55297 ≤ 4294967296` under each mode and require bounded steps.
- Compare all existing primitive cases across evaluator modes, including divide/mod by zero.
- Ensure partial applications and noncompact operands miss and follow retained unfolding.
- Mutation controls: wrong arity, swapped primitive head, fake similarly typed declaration, changed dictionary term, malformed literal, and a definition whose body resembles `ble` must all miss unless it is the already-authorized primitive identity.
- Run `isValidChar_UInt32` and require native-hit evidence for the compact `Nat.ble`; its dominant 449K-step equality should disappear.
- Retain reject fixtures to ensure a primitive miss cannot turn a false judgment into a verdict.

## Prototype limitations

A WHNF-first schedule and exact equality cache were already negative. A partial prototype that changed operand redispatch exposed compact `Nat.ble 55297 4294967296`, but did not improve the target because the private iterative loop still bypassed primitive dispatch. Patching only one loop is insufficient and risks path-dependent semantics. The production change should introduce the shared dispatcher once and wire every loop to it together.

## Refined implementation after prototype review

The first shared-hook prototype was reverted completely. Although synthetic ordinary/local/full-stack examples passed, actual `isValidChar_UInt32` did not improve. Recursive `k.whnf` operand callbacks are the wrong mechanism: they re-enter private evaluators, risk deep nested primitive recursion, and still leave compact primitive heads inside iterative state.

Use a pure `nat-primitives.mjs` descriptor table instead:

- exact authorized head identity;
- exact arity;
- `compute(values)` returning a compact Nat or Bool constructor;
- the existing bounded `Nat.pow` policy in the same table.

The table has no declaration lookup, unfolding, or recursive WHNF. `compiled-nat-pow-layer.mjs` becomes a compatibility import of this shared implementation, so power does not remain a separate bypass.

Each iterative evaluator handles a recognized fully applied primitive by pushing a `native-operands` frame containing the original head/arguments, descriptor, next operand index, and completed compact values. It evaluates one operand through its existing state machine. If the operand reaches a compact Nat, it advances to the next. Once all operands are compact, it invokes the pure descriptor exactly once and resumes existing projection/recursor/application frames with the result. If any operand is noncompact, it restores the original primitive application and follows ordinary definition unfolding. Extra or missing arguments miss immediately.

This frame belongs at the same const-head point in `scoped-beta-spine` and both stack-safe loops. The ordinary wrapper can use the same descriptor after its retained operand normalization, without duplicating arithmetic. No iterative engine should call `k.whnf` recursively to normalize descriptor operands.

Required frame-specific tests: deeply nested primitive operands under scoped and full-stack modes; primitive inside projection/recursor frames; compact power feeding `ble`; false `HPow` dictionaries; power resource bounds; miss restoration identity/semantics; and actual target evidence that compact `Nat.ble 55297 4294967296` increments the shared primitive-hit counter and removes the dominant equality.
