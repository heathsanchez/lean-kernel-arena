# Retained WHNF Re-entry Trampoline Plan

**Goal:** Eliminate the certified `host-stack-limit` residual on `init-prelude` and `perf/grind-ring-5` without routing the whole checker through the expensive `_fullStackSafe` evaluator and without changing Lean semantics.

**Certified residual:** Fresh giant diagnostics show both cases overflow through the same cycle:

`kernel-base.whnf -> stack-safe.whnf -> scoped-beta-spine -> recursor-gated-conversion -> native-nat -> compiled-nat-pow -> compiled-semantic-consequence -> kernel-base.whnf -> ...`

The crash occurs at ~657k and ~370k charged steps respectively, while the existing whole-kernel `_fullStackSafe` fallback avoids the host stack but exhausts the 2M semantic budget. Therefore the warranted repair is execution-local: break recursive public-WHNF re-entry only after the retained fast evaluator has entered `baseWhnf`.

## Invariants

- No new reduction, typing, conversion, or declaration rule.
- Later WHNF wrappers (native Nat, compiled pow, semantic consequences, etc.) still get first refusal on every public `this.whnf` call.
- Ordinary top-level WHNF remains on the retained fast path.
- Only a recursive `this.whnf` call made while `baseWhnf` is already active is diverted to the existing iterative `fullStackWhnf` engine.
- No arbitrary host-stack depth threshold.
- The re-entry state is synchronous, exception-safe, and reset with `finally`.
- Existing focused tests, 190-case verdict vector, and `shared-subterm` must not regress.

## Task 1: RED witness

Create `genesis/whnf-reentry.test.mjs` with a several-thousand-deep nested projection chain whose inner object is a rigid variable. Projection WHNF recursively normalizes its object before discovering there is no reducible structure, so the current retained base evaluator must overflow the host stack. Assert the production kernel returns the same chain without throwing and without requiring `_fullStackSafe=true`.

Run `node --test genesis/whnf-reentry.test.mjs`; current production must fail with `RangeError`.

## Task 2: Minimal trampoline

Modify only `genesis/stack-safe.mjs` around the final retained `baseWhnf.call(this,e)` fallback.

Add a per-kernel synchronous re-entry counter/flag. The first ordinary fallback enters retained `baseWhnf`; any recursive public WHNF call that reaches `stack-safe.mjs` while that retained base call is active routes to `fullStackWhnf.call(this,e)` instead of entering `baseWhnf` recursively. Use `try/finally` to restore the counter.

Do not set `_fullStackSafe=true` globally and do not bypass later wrapper layers.

## Task 3: Focused verification

Run:

- `node --test genesis/whnf-reentry.test.mjs`
- `node --test genesis/binder-transport.test.mjs`
- `node genesis/test.mjs`
- `node --test genesis/*.test.mjs`

All must pass.

## Task 4: Giant causal separator

Run the exact frozen `init-prelude`, `perf/grind-ring-5`, and `perf/shared-subterm` witnesses at the production 2M budget with the ordinary checker.

Admission requires:

- neither giant ends in `host-stack-limit`,
- no wrong verdict,
- `shared-subterm` remains ACCEPT,
- the replacement residual is reproducible and no earlier than the old stack failure.

Then run the full 190-case qualification. Retain the trampoline if it removes the host-stack failure with zero correctness regressions even if a later budget/conversion residual remains; host-stack elimination is itself a certified execution repair.

## Task 5: Ablation

Run the same giant diagnostic with the trampoline disabled. The `host-stack-limit` must return at the prior frontier. If ablation does not restore the stack failure, the claimed cause is not isolated and the repair is not admitted.

## Completion

End this plan with either:

- **ADMITTED:** host-stack residual removed causally, focused tests green, 190 verdicts no worse; or
- **REVOKED:** stack failure persists, correctness regresses, or the claimed causal effect fails ablation.

The next plan is written from the new residual only after this gate.