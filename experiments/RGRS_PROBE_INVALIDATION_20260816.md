# RGRS applicability probe invalidation — 2026-08-16

## Trigger

The held-out `perf/beta-ladder` source explicitly constructs a 2,000-binder beta ladder whose innermost body reads every binder, yet the exploratory offline probe reported an absent-binder rate of 92.8%.

## Root cause

`experiments/export_structure_probe.py` used a 64-bit free-variable mask:

- `bvar k` was represented as `1 << k` only for `k < 64`;
- every `bvar k` with `k >= 64` was replaced by zero;
- masks were additionally truncated with `MASK64` after every expression.

Therefore deep de Bruijn dependencies were silently erased. The measurement is invalid for terms with binder depth above 64 and may bias aggregate rates even on ordinary corpora containing deep terms.

## Evidence status changes

- The frozen threshold `tau = 0.1580774332` is **INVALIDATED as an applicability rule** because it was derived from a lossy observable.
- The prospective Std timing result (pinned 9.6 s vs latest 8.7 s) remains a valid timing observation, but it no longer counts as prospective validation of the claimed exact absent-binder statistic.
- The five perf-fixture timings remain valid performance observations.
- The 64-bit structure values for Cedar, CSLib, Mathlib, Std, init-prelude and the five perf fixtures are retained only as historical exploratory measurements and MUST NOT be used for routing or admission.

## Repair

Branch `mathgraph-rgrs-applicability-v2` adds `experiments/export_structure_probe_exact.py`, using Python arbitrary-precision integers as exact free-variable bitsets. First validation target is the five small performance fixtures. Workflow run: `31914430012`.

The exact probe is intentionally scoped to focused fixtures first; large-corpus scalability must be measured separately before using it on Mathlib-scale exports.

## RGRS classification

Primary: **R10 Infrastructure / distorted adapter**.
Secondary: **R4 Observability** because the intended observable was not actually being measured.

This is not evidence against local binder irrelevance as a kernel mechanism. It is evidence against the measurement adapter.

## Next gate

1. Exact probe must recover `beta-ladder` as strongly binder-dependent.
2. Compare exact structural statistics against the already-frozen five timing outcomes.
3. Only then define a local mechanism separator.
4. Any A7 candidate is built on retained A6, not on the invalidated workload threshold.
