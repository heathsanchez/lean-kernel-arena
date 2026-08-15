# RGRS post-gate decision table

Status: PRECOMMITTED before Mathlib latest result and before semantic battery result.

## Gate 1 — Mathlib scale

Compare pinned A0 vs latest A4 on the same built Mathlib export and runner.

Outcomes:

- A4 semantically correct and materially faster than A0 -> PASS scale gate; proceed to Gate 2 and launch the five-arm causal interaction experiment.
- A4 semantically correct but within noise / slower -> classify R2 Cost or R5 Applicability; do not launch the interaction experiment as a performance-admission path. Preserve focused wins as workload-local evidence only.
- A4 semantic failure -> R9 Soundness; reject latest architecture path regardless of speed.
- Infrastructure/build failure -> R10 only; no architecture conclusion.

## Gate 2 — semantic battery

All accept cases must accept and all reject cases must reject. No decline/fallback counts as success unless explicitly predeclared by the Arena test.

Only after both Gate 1 and Gate 2 pass may the five-arm interaction experiment run.

## Gate 3 — five-arm mechanism separator

Arms:

- A0 pinned
- A1 eagerness only
- A2 structural absence only
- A3 eagerness + structural absence core
- A4 full latest

For each workload define gain relative to pinned as G(X) = T(A0) - T(X), with positive G meaning faster.

Primary interaction statistic:

I = G(A3) - G(A1) - G(A2)

Interpretation:

- A1 explains most of A4, A2 small, I ~ 0 -> eagerness is primary mechanism.
- A2 explains most of A4, A1 small -> structural absence/irrelevance is primary mechanism.
- A1 and A2 weak alone, A3 strong, I materially positive -> ADMIT interaction law: structural observability changes the economics of eagerness.
- A3 strong but A4 materially stronger -> residual mechanism remains in eval/conv/expr changes; classify and decompose only that residual.
- Any arm changes semantics -> R9 reject that arm/mechanism.
- Gains differ by workload sign -> R5 Applicability; search for structural separator rather than global activation.

## Gate 4 — mechanism counters

Mechanism claim requires counters to move in the predicted direction. Record at least:

- arg_value calls
- direct eager evals
- thunk creations
- thunk-cache probes/hits/misses
- structurally absent / ignorable arguments
- ignored binders
- conversions skipped due to structural irrelevance
- wall time, CPU, peak RSS

A runtime gain without a matching mechanism shift is not attributed to the proposed mechanism; classify R12 Displacement / unrelated implementation effect until explained.

## Gate 5 — persistent-expression DAG separator

Independently classify D0/D1/D2:

- D1 faster than D0 and D2 while preserving semantics -> persistent identity is causal; ADMIT R3 mechanism and instrument hit classes.
- D1 ~= D2 and both slower than D0 -> global probe cost with little reusable identity; reject this boundary and record R2/R8 negative law.
- D1 and D2 both similar and faster than D0 -> unrelated build/code effect; do not claim identity mechanism.
- D1 wins only one workload -> R5 scope boundary for persistence.
- semantic change -> R9 reject immediately.

## Composition rule

Do not combine the eager/absence mechanism with persistent-expression reuse until each independently clears its own causal and semantic gates.

If both independently clear, test composition as a new experiment with its own ablation and interaction term. No additive assumption is permitted.