# RGRS experiment: canonical DAG separator

Status: PRECOMMITTED, not yet executed.

## Residual

Primary: R3 Redundancy.
Secondary: R8 Access.
Candidate upstream cause: semantically equivalent expressions/environments are represented by distinct runtime objects, forcing repeated hashing, reconstruction, normalization, and conversion work.

## Representation hypothesis

A persistent canonical DAG that interns verifier-equivalent structural objects earlier will reduce distinct semantic computations by allowing identity-level reuse. Combined with lazy/selective forcing, this should reduce work without changing accepted semantics.

## Smallest separator question

Does canonical identity reduce the number of distinct semantic computations on workloads with high repeated structure, while preserving the lazy regime on workloads where eager forcing is harmful?

## Required measurements

For matched Cedar, CSLib, and init-prelude runs, record at minimum:

- parsed expression count;
- unique interned expression count;
- environment constructions and unique canonical environments;
- WHNF requests and distinct WHNF computations;
- conversion requests and identity/pointer short-circuits;
- thunk creations, forced thunks, and unforced thunks;
- wall time, CPU time, peak RSS;
- semantic pass/fail.

Primary mechanism ratio:

`reuse_ratio = logical_semantic_requests / distinct_canonical_computations`

Secondary ratios:

`expr_share = parsed_or_created_exprs / unique_exprs`
`whnf_share = whnf_requests / distinct_whnf_computations`
`conv_identity_rate = identity_short_circuits / conversion_requests`

## Arms

D0: existing pinned sokonanoda representation/evaluation.
D1: same semantics/evaluation policy with canonical interning at the narrowest feasible expression/environment boundary.
D2: D1 with identity shortcut disabled (causal ablation while retaining construction overhead).

Do not combine broad eagerness changes into this experiment. Evaluation policy must remain fixed so this isolates representation identity.

## Frozen discriminators

Cedar, CSLib, init-prelude first. Mathlib only after the focused gate passes.

## Admission criteria

Semantic gate: all frozen positive cases accepted and no known semantic regression.
Causal gate: D1 gain must materially weaken in D2.
Resource gate: D1 must improve the predeclared aggregate wall/CPU metric without a disqualifying RSS increase.
Mechanism gate: at least one reuse ratio must move in the predicted direction and explain a material part of the runtime change.
Reproducibility gate: repeat on the same pinned runner procedure before escalation.

## Decision table

- D1 faster, reuse ratios improve, D2 loses gain -> ADMIT mechanism and escalate to Mathlib.
- D1 faster, ratios unchanged -> classify R12/displaced or unrelated implementation effect; do not claim DAG mechanism.
- D1 ratios improve but runtime does not -> R2 cost of canonicalization; optimize construction only if measured overhead dominates.
- D1 wins Cedar but loses CSLib (or vice versa) -> R5 applicability; search for scope boundary of interning/canonicalization.
- semantic change -> R9 reject immediately.
- build/runner failure -> R10 only; no architecture conclusion.

## Boundary robustness

If D1 passes, repeat with at least one alternate canonicalization boundary (e.g. expressions only vs expressions+environments). The architectural claim survives only if the gain is not an artifact of one arbitrary boundary.