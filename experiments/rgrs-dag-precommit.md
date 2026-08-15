# RGRS experiment: persistent expression reuse separator

Status: PRECOMMITTED and IMPLEMENTED, not yet executed.

## Residual

Primary: R3 Redundancy.
Secondary: R8 Access.

Source audit sharpened the hypothesis: sokonanoda already has both a persistent `ExportFile.dag` and a per-`TcCtx` local `Dag`. Names, levels, strings, big integers, and universe-parameter slices probe the persistent DAG before allocating locally. Expressions do not: `alloc_expr` probes only `self.dag.exprs` and otherwise allocates into the local typechecking-context DAG.

Therefore the current representation residual is not "missing canonicalization" in general. It is a specific persistence boundary: globally parsed expressions can be canonical, while equivalent expressions reconstructed during later typechecking contexts may be canonical only within that local context.

## Representation hypothesis

When a newly constructed expression is structurally identical to an expression already interned in the persistent export-file DAG, reusing the persistent expression pointer will remove reconstruction and enable downstream identity-level reuse without changing evaluation semantics.

This is deliberately narrower than introducing a new DAG architecture.

## Smallest separator question

Does probing and reusing the persistent global expression interner before allocating a `TcCtx`-local expression reduce end-to-end checking cost, beyond the cost of performing the extra global lookup itself?

## Arms

D0 — pinned baseline:
- Arena-pinned sokonanoda `0fab8874080e379a774a9a27f7538d8a1ddd786b`;
- unchanged lazy evaluation policy.

D1 — persistent global expression reuse:
- same pinned source and evaluation policy;
- in `alloc_expr`, probe `self.export_file.dag.exprs` first;
- on hit, return a global `ExprPtr`;
- otherwise preserve the existing local interning path.

D2 — global-probe causal ablation:
- same pinned source and evaluation policy;
- perform the identical global expression lookup;
- deliberately discard the result;
- preserve the original local interning path.

Thus D1 vs D2 isolates the value of persistent identity/reuse from the cost of the additional hash-table probe.

## Frozen discriminators

Cedar, CSLib, and init-prelude first. Mathlib only after the focused gate passes.

## Required measurements

Initial gate:
- semantic pass/fail;
- wall time;
- CPU time when exposed by the Arena runner;
- peak RSS when exposed by the Arena runner.

If D1 shows a material performance signal, instrument a second mechanism run for:
- global-expression probe count;
- global-expression hit count;
- local-expression hit count;
- local-expression allocation count;
- conversion identity short-circuits;
- WHNF request/reuse counts.

Primary mechanism ratio for the instrumented follow-up:

`global_expr_hit_rate = global_expr_hits / global_expr_probes`

Secondary:

`persistent_reuse_fraction = global_expr_hits / total_alloc_expr_requests`

## Admission criteria

Semantic gate: all frozen positive cases accepted and no known semantic regression.

Causal gate: D1 must outperform D2 materially; D2 controls for the added persistent-table lookup.

Resource gate: D1 must improve the predeclared aggregate wall/CPU metric without a disqualifying RSS increase.

Mechanism gate: if the performance gate passes, instrumentation must show nontrivial persistent-expression hits consistent with the runtime change.

Reproducibility gate: repeat with the same pinned runner procedure before escalation.

## Decision table

- D1 faster than D0 and D2, semantics preserved -> retain R3 hypothesis; instrument hit rates and repeat.
- D1 ~= D2 and both slower than D0 -> global probe cost dominates; reject this boundary and retain the negative law.
- D1 ~= D0 while D2 slower -> reuse approximately pays for lookup but does not create a material gain; do not escalate yet.
- D1 slower than D2 -> returned global identity is causing downstream cost or applicability mismatch; classify R5/R12 and locate the interaction.
- D1 wins Cedar but loses CSLib (or vice versa) -> R5 applicability; identify which expression classes should be promoted globally.
- semantic change -> R9 reject immediately.
- build/runner failure -> R10 only; no architecture conclusion.

## Boundary robustness

If D1 passes, the next boundary test is selective global promotion by expression class, followed only then by broader persistence of reconstructed semantic objects/environments. Do not claim a general persistent-DAG result from this single boundary.

## Execution discipline

The workflow is dispatch-only and lives on `mathgraph-rgrs-dag` so it cannot cancel or contaminate the currently running `mathgraph-architecture-swing` separator. Do not execute it until that run has resolved and RGRS selects the R3 branch.