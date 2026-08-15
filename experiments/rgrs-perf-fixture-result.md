# RGRS prospective perf-fixture result

Source run: `31912455339` on `mathgraph-rgrs-applicability-probe`.

Frozen rule before timing:
- `tau = 0.1580774332` absent-binder rate;
- all five fixtures had `A >= tau` and were predicted to favor latest sokonanoda `9b4ea12` over pinned `0fab887`;
- the high-A pair (`app-lam`, `beta-ladder`) was predicted to show at least as much benefit as the lower-A group, absent overwhelming fixture-specific effects;
- any sign miss triggers REFRAME, not threshold retuning.

Observed one-shot Arena-formatted timings (all semantics correct):

| fixture | A | pinned | latest | sign |
|---|---:|---:|---:|---|
| app-lam | 0.9521770164 | 65 ms | 56 ms | latest faster |
| beta-ladder | 0.9280000000 | 620 ms | 626 ms | **pinned faster; sign miss** |
| discarded-argument | 0.3571428571 | 9 ms | 8 ms | latest faster |
| args-before-unfold | 0.3414634146 | 10 ms | 11 ms | **pinned faster; sign miss** |
| church-numerals | 0.2727272727 | 12 ms | 11 ms | latest faster |

Verdict: **REFRAME**.

The simple workload-level absent-binder threshold is not sufficient: 2/5 prospective sign predictions missed. The magnitude/ordering hypothesis also fails because one of the two highest-A fixtures (`beta-ladder`) reverses sign.

Do not retune `tau` on these outcomes. Preserve `A(W)` as a coarse correlate that prospectively succeeded on Std but now has explicit micro-workload counterexamples.

Updated residual: the useful mechanism depends on *where/how* absent binders interact with evaluator demand, not merely their global frequency. Candidate next observables must distinguish demanded vs discarded arguments, beta-chain shape, unfolding timing, conversion/recursor pressure, or other local evaluator context.

This result does not invalidate MathGraph Kernel A6. The comparison was unpatched latest upstream versus Arena-pinned upstream, and A6 remains the retained protected performance frontier.