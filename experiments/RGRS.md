# Residual-Guided Representation Search (RGRS)

RGRS is the operating protocol for architecture experiments in this fork.

## Residual taxonomy

- R1 Search: representation appears sufficient; search has not exhausted plausible moves.
- R2 Cost: semantics pass, resource gate fails.
- R3 Redundancy: equivalent work is repeatedly reconstructed or recomputed.
- R4 Observability: work is performed although it cannot affect the verified result.
- R5 Applicability: a mechanism wins in one regime and loses in another.
- R6 Representation: the current language/IR cannot express the distinction required to remove the residual.
- R7 Composition: known mechanisms may close the gap only when composed.
- R8 Access: useful structure exists but is expensive to recover.
- R9 Soundness: a speed/capability gain changes accepted semantics. Immediate reject.
- R10 Infrastructure: build, runner, timeout, provisioning, or network failure. No semantic conclusion.
- R11 Boundary: claimed novelty depends on an arbitrary granularity boundary.
- R12 Displacement: complexity moved elsewhere instead of being reduced in total.

Record each residual as `(class, location, evidence, scope, confidence)`.

## Representation-change rules

1. Change representation after the same residual survives materially different interventions, not after a single loss.
2. If workloads prefer incompatible mechanisms, classify R5 and search for the separator governing activation; do not pick one global regime.
3. If distinctions are repeatedly recomputed but verifier-equivalent, quotient/canonicalize them.
4. If a value cannot affect any verified observable, do not force it eagerly.
5. If the needed separator cannot be stated in the current representation, extend or replace the representation.
6. Test composition before inventing a new primitive.
7. Measure total cost: construction + activation + verification + runtime + memory.
8. Require robustness under at least one alternate reasonable representation boundary.

## Smallest deciding test

A deciding test must contain: frozen baseline, one representation intervention, causal ablation, at least two opposing discriminators, predeclared semantic gate, and predeclared resource metric.

The test must answer one separator question. Each possible outcome must imply a different next action.

## External-verifier gate

A candidate is ADMITTED only when all four gates pass:

`semantic && causal && resource && reproducible`

- Semantic: frozen external corpus/verifier accepts exactly the required cases.
- Causal: ablating the representation change removes or materially weakens the gain.
- Resource: the predeclared metric improves; no post-hoc metric switching.
- Reproducible: same commit/config/corpus/runner procedure reproduces the result.

State transitions: `PROPOSED -> SEPARATED -> VERIFIED -> ADMITTED`, otherwise `REJECTED` or `OBSTRUCTED`.

## Current Lean application

Primary residual: **R5 Applicability**.
Suspected mechanism: **R4 Observability**.
Supporting secondary hypothesis: **R3 Redundancy** through non-canonical expression/environment reconstruction.

Current separator question: does structural irrelevance retain the favorable eager-regime gain while removing the broad-eagerness penalty?

Frozen arms:
- pinned sokonanoda (`0fab887...`): older lazy/thunk path;
- latest sokonanoda (`9b4ea12...`): broad eagerness + structural irrelevance;
- irrelevance-only: structural irrelevance with older lazy/thunk path restored.

Frozen discriminators: Cedar, CSLib, init-prelude.

Decision table:
- irrelevance-only ~= best arm across opposing discriminators -> escalate to Mathlib/full semantic corpus;
- irrelevance-only ~= pinned -> irrelevance contributes little; decompose eagerness;
- irrelevance-only helps only one regime -> retain R5 and search for activation separator;
- any semantic failure -> R9 immediate reject;
- runner/build failure -> R10, repair experiment only.

Next representation hypothesis after this separator: **persistent canonical DAG + selective forcing**, tested by counting logical evaluation requests versus distinct canonical computations actually performed.