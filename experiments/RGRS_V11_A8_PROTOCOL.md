# RGRS v1.1 — A8 Decision Protocol

Date: 2026-08-16
Goal: progress toward #1 on Lean Kernel Arena without post-hoc tuning.

## Frozen evidence

- Arena-pinned sokonanoda: `0fab8874080e379a774a9a27f7538d8a1ddd786b`.
- Upstream studied revision: `9b4ea12f4cd437d00b6bcd0e34743065c58dea08`.
- A6 unrestricted E0030 is invalid for large-suite performance claims because Cedar, CSLib and Mathlib were rejected despite small semantic controls passing.
- A7 restores semantic correctness by bypassing `key_env` only where upstream already returns `env` unchanged (`num_loose_bvars > 64`).
- A7 focused result: Cedar 33.3 s -> 23.7 s (correct, ~28.8% faster); CSLib 33.5 s -> 86.1 s (correct, ~157% slower); init-prelude 43 ms -> 43 ms; reject controls correct.

## Current residual

Primary: **R5 Applicability**.
Location: Lambda closure environment canonicalization / `key_env`.
Evidence: opposite large-suite regimes under the same semantically valid A7 intervention.
Strongest rival explanations:
1. `key_env` is valuable mainly when it actually removes captured slots.
2. Canonicalization/reuse benefits can matter even when pruning removes no slots.
3. The Cedar gain comes from another A3-A5 interaction and the A7 result is incidental/code-layout/PGO interaction.

## A8 intervention

A8 retains A3-A5 and bypasses Lambda `key_env` only when static expression/environment structure proves that pruning cannot remove any currently captured slot, plus the existing `num_loose_bvars > 64` identity region.

This is a closure-before-invention composition of already-known mechanisms, not a new high-level primitive.

## Frozen smallest deciding test

Workloads: Cedar, CSLib, init-prelude, plus `bogus1`, `constlevels`, `ctor-num-fields` semantic controls.
Baseline: Arena-pinned sokonanoda.
Runner/build: same GitHub Actions workflow and PGO recipe for both checkers.

### Interpretation table

1. **A8 correct; Cedar <= 26 s; CSLib <= 40 s**
   - Transition: PROMOTE -> PROJECT.
   - Next action: full Mathlib gate immediately, unchanged A8.

2. **A8 correct; Cedar keeps >=15% gain; CSLib improves materially over A7 but remains >40 s**
   - Transition: RETAIN + REFRAME.
   - Residual: no-shrink is directionally right but insufficient; measure canonicalization/reuse value conditional on environment shape.
   - Next test: instrument `key_env` calls by `(env_len, kept_slots, framed/cons, cache/prune hit)` on Cedar vs CSLib; no new optimization arm before those measurements.

3. **A8 correct; Cedar falls back near pinned while CSLib recovers**
   - Transition: REFRAME.
   - Conclusion: Cedar's A7 gain requires cases in which pruning does remove slots or another interaction removed by A8.
   - Next test: causal ablation over shrink-size buckets, not workload routing.

4. **A8 correct; CSLib remains near A7 (~80+ s)**
   - Transition: SUPPRESS no-shrink sufficiency hypothesis.
   - Next test: measure canonicalization/reuse effects even at zero shrink; inspect earliest performance divergence.

5. **Any semantic failure**
   - Transition: INVALIDATE A8.
   - No performance claim from that arm.
   - Trace earliest semantic divergence before any further optimization.

6. **Infrastructure failure before verdict**
   - Classify R10 only; repair harness without changing scientific hypothesis.

## Promotion hierarchy

- This focused run can produce OBSERVED/CAUSAL evidence only.
- A8 is not TRANSFERRED until Mathlib or a source-distinct large suite passes.
- A8 is not ADMITTED until protected negatives, reproducibility, and full Arena-relevant semantic gates pass.
- Public leaderboard claims require an exact immutable Arena submission/result.

## Anti-wandering rule

No threshold fitting, workload-name routing, or unrelated cache variant is allowed before the A8 outcome changes state according to the table above.

## Frontier-expansion question

If A8 survives, test whether the newly scoped `key_env` capability exposes the next optimization residual that was not reachable from A5/A7 alone. Record that lineage explicitly.