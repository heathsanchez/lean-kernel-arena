# Native Closure WHNF Implementation Plan

**Goal:** Replace repeated eager substitution in the semantic evaluator with a small closure/environment machine that preserves Lean definitional equality while eliminating the substitution-dominated execution path seen in `init-prelude` and `perf/grind-ring-5`.

**Protected baseline:** `mda-arena-qualification-v1` remains untouched until this branch beats the verified 183/190, 0-wrong result and passes the full frozen public corpus.

## Task 1 — Freeze parity witnesses

Files: `genesis/native-closure-whnf.test.mjs`, existing `genesis/whnf-reentry.test.mjs`, `genesis/recursor-independent.test.mjs`, `genesis/quotient-evaluator-parity.test.mjs`.

1. Add tests for closure lookup under binder depth, beta without materialization, nested lambdas, local definitions, projection after beta, recursor major reduction after beta, proof irrelevance, quotient reduction, and exact reification parity with the existing substitution implementation.
2. Add a deep beta-chain witness that must normalize without host-stack growth.
3. Run only the new test first and verify RED because the closure evaluator module does not yet exist.
4. Commit RED tests before implementation.

## Task 2 — Minimal closure representation

Files: `genesis/native-closure-whnf.mjs`, `genesis/native-closure-whnf.test.mjs`.

Implement only:
- closure = `{ expr, env, depth }`;
- environment as persistent parent-linked slots rather than copied arrays;
- O(1) push and de Bruijn lookup;
- exact `reifyClosure` used only at semantic boundaries/tests;
- no name-based or corpus-specific shortcuts.

Run the focused test until GREEN. Then run all `genesis/*.test.mjs` and `genesis/test.mjs`.

## Task 3 — Iterative WHNF machine

Files: `genesis/native-closure-whnf.mjs`.

Extend the machine one reduction rule at a time with explicit continuation frames:
- application spine;
- beta;
- let/local-definition unfolding;
- delta unfolding using the existing declaration environment/transparency policy;
- projection;
- recursor/iota;
- quotient rules;
- proof irrelevance only through the existing semantic checks.

Each rule gets a failing focused test before implementation. Reification remains outside the hot path.

## Task 4 — Differential parity against existing evaluator

Files: `genesis/native-closure-differential.test.mjs`.

Construct a deterministic corpus of small expressions from the existing constructors and compare:
- WHNF head class;
- reified WHNF expression;
- accept/reject result for declaration witnesses;
- expected exceptions/UNKNOWN boundaries.

Any mismatch is investigated as a semantic bug; do not weaken tests.

## Task 5 — Feature-branch separator workflow

Files: `.github/workflows/mda-native-closure-whnf.yml`, `genesis/native-closure-giant-separator.mjs`.

Run baseline and native closure evaluator on:
- `init-prelude.ndjson`;
- `perf/grind-ring-5.ndjson`;
- `perf/shared-subterm.ndjson` control.

Measure verdict, charged steps, wall time, constructed nodes, peak RSS when available, and frontier. Budgets: 1M, 2M, 4M. Preserve all outputs as artifacts.

Promotion threshold for the giant family: zero semantic regressions, no host-stack failure, and a material reduction in either charged work or wall time versus baseline. Closure only if it earns the result.

## Task 6 — Integrate through one production seam

Files: `genesis/production.mjs` and, only if necessary, one small adapter module.

Route the existing production WHNF call through the native closure evaluator. Do not stack another speculative cache/layer. Preserve current checker I/O and exit semantics.

Run focused regressions, full unit suite, then the frozen public Arena corpus at the normal 2M budget.

## Task 7 — Close the remaining residual families

After the giant family is stable, reuse the same closure machine for the other residuals only where diagnostics show the same reconstruction mechanism:
- `perf/fueled-chain.ndjson`;
- `perf/magma-list-deep-n21.ndjson` / `n36`;
- `perf/magma-list-pair-n7.ndjson` / `n21`.

If a residual is not caused by closure/materialization, diagnose it independently instead of adding complexity to this machine.

## Task 8 — Qualification and ablation

Promotion requires, in order:
1. all unit/regression tests green;
2. 190/190 frozen public corpus, 0 wrong, 0 errors;
3. clean restart/replay with empty process caches;
4. ablation showing removal of the native closure seam restores the measured obstruction or slowdown;
5. full currently prescribed Arena workload including large tests;
6. Mathlib timing profile and memory profile.

Only after all six are evidenced may the qualification branch be fast-forwarded. No upstream PR is created without explicit authorization.

## Performance finish

Once correctness is frozen, profile the native machine itself. Optimize only measured dominant costs, prioritizing representation and allocation over memo layers. The final kernel should contain the smallest evaluator that explains its wins: persistent environments, iterative continuations, exact reduction rules, and only evidence-backed caches.