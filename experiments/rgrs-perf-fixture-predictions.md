# RGRS prospective performance-fixture predictions

Status: frozen before comparative checker timing.

Frozen workload-level selector threshold from prior acquisition set:

- tau = 0.1580774332 absent-binder rate
- A >= tau => predict latest sokonanoda (9b4ea12) faster than pinned (0fab887)
- A < tau => predict pinned faster

Structure-only held-out measurements:

| fixture | absent-binder rate | frozen sign prediction |
|---|---:|---|
| perf/app-lam | 0.9521770164 | latest faster |
| perf/beta-ladder | 0.9280000000 | latest faster |
| perf/discarded-argument | 0.3571428571 | latest faster |
| perf/args-before-unfold | 0.3414634146 | latest faster |
| perf/church-numerals | 0.2727272727 | latest faster |

Because all five lie above tau, these fixtures do not provide an opposite-sign test of the frozen binary threshold. They instead provide a precommitted magnitude/ordering test:

1. The very-high-A pair (app-lam, beta-ladder) should show at least as much benefit from latest as the lower-A group, absent overwhelming fixture-specific mechanism effects.
2. Across these five fixtures, the rank association between A and latest-vs-pinned performance delta should be positive if absent-binder structure is not merely a coarse workload correlate.
3. No threshold or metric may be changed after timings are revealed for these fixtures.
4. A sign miss on any fixture is retained as a counterexample and triggers REFRAME rather than threshold retuning.

This is a prospective mechanism test, not a claim that A alone is sufficient for local evaluator routing.
