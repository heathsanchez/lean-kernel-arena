# RGRS precommit: eagerness × structural absence interaction

Status: PRECOMMITTED. Do not execute unless latest sokonanoda clears the Mathlib + semantic escalation gate.

## Residual

Primary: R5 Applicability / mechanism interaction.
Secondary: R4 Observability.

The focused three-arm experiment showed that latest upstream (9b4ea12) beats pinned 0fab887 on Cedar, CSLib, and init-prelude, while the irrelevance-only arm recovers only part of the Cedar gain and none of the CSLib gain. Therefore the strong claim that broad eagerness is globally harmful is rejected on the focused corpus.

Upstream 9b4ea12 is one commit ahead of 0fab887 and changes only conv.rs, eval.rs, expr.rs, infer.rs, and relevance.rs. The structural change is broader than proof irrelevance: it tracks absent/ignorable arguments and allows conversion/inference to skip structurally unobservable work.

## Representation hypothesis

Eager argument evaluation becomes profitable when structural absence/observability information prevents those eager values from participating in unnecessary downstream conversion and inference work.

The gain may therefore be super-additive:

`gain(E+A) > gain(E) + gain(A)`

where E = eager evaluation and A = structural absence/ignorable-argument machinery.

## Smallest deciding question

Is the latest upstream speedup explained by eagerness alone, structural-absence machinery alone, or a causal interaction between them?

## Arms

All arms use the same pinned toolchain, runner, PGO procedure, config, and tests.

A0 — PINNED
- exact 0fab887

A1 — EAGERNESS ONLY
- start from 0fab887
- apply only the arg_value/evaluation changes required to make arguments eager
- do not add absent_arg, ignores_binder, or arg_is_ignorable semantics

A2 — STRUCTURAL ABSENCE ONLY
- start from 9b4ea12 structural machinery
- restore the 0fab887 lazy/thunk argument-value path
- this is equivalent in intent to the already-tested irrelevance-only arm and should be reproduced under the same interaction workflow

A3 — EAGERNESS + STRUCTURAL ABSENCE CORE
- combine A1 eagerness with absent_arg / ignores_binder / arg_is_ignorable machinery
- exclude any remaining incidental latest changes that are not required for this mechanism

A4 — FULL LATEST
- exact 9b4ea12

## Frozen first-stage corpus

Cedar
CSLib
init-prelude

Only if A3/A4 pass the focused gate: Mathlib and the frozen semantic corpus.

## Metrics

Primary resource metric: aggregate wall time across the three frozen focused workloads.
Secondary: per-workload wall time.
Semantic status is mandatory and dominates performance.

When feasible, instrument:
- arg_value calls
- eager argument evaluations
- thunk creations
- thunk forces
- arg_is_ignorable hits
- absent_arg hits
- ignores_binder hits
- conversion argument skips
- inference binder skips

## Interaction statistic

Let T(X) be aggregate runtime and define gain relative to pinned as G(X)=T(A0)-T(X).

Interaction:

`I = G(A3) - G(A1) - G(A2)`

Interpretation:
- I materially > 0: super-additive interaction; structural observability makes eagerness profitable.
- I approximately 0: mostly additive independent mechanisms.
- I < 0: mechanisms interfere; latest gain likely comes from another changed path or workload mixture.

Because wall-time noise can make exact additivity unstable, require the qualitative ordering to reproduce before making an interaction claim.

## Admission / decision table

1. A1 ~= A4 and A2 weak -> eagerness is sufficient. Residual becomes R2/R4 on where eagerness saves work; do not claim applicability interaction.
2. A2 ~= A4 and A1 weak -> structural absence is sufficient. Eagerness is incidental.
3. A1 and A2 each partial, A3 ~= A4 and I > 0 -> ADMIT interaction mechanism. Next representation target: observability-guided eager evaluation.
4. A3 materially beats A4 -> latest contains displacement/overhead; isolate the extra latest change before escalation.
5. A3/A4 split by workload -> R5 applicability. Search for structural separator, not benchmark-name routing.
6. Any semantic regression -> R9 reject that arm immediately.
7. No reproducible resource movement -> reject mechanism claim and retain negative law.
8. Infrastructure failure -> R10 only.

## Boundary robustness

If the interaction is admitted, repeat the separator using at least one narrower structural boundary (e.g. binder absence only vs full ignorable-argument signature) to show the effect is not an artifact of the chosen grouping of upstream changes.

## External-verifier gate

No architecture claim is admitted until:
- focused semantics pass;
- Mathlib accepts;
- frozen invalid controls remain rejected;
- the gain reproduces;
- ablation supports the claimed mechanism.

## Governing law under test

`Compute early only when representation exposes enough structure to prove where the result can matter.`
