# RGRS result: latest sokonanoda Mathlib escalation

Status: NOT ADMITTED GLOBALLY.

## Frozen comparison

Pinned: `0fab8874080e379a774a9a27f7538d8a1ddd786b`
Latest: `9b4ea12f4cd437d00b6bcd0e34743065c58dea08`
Workflow run: `31895029719`
Runner: ubuntu-24.04, 4 vCPU, 15 GiB RAM.

## Focused evidence that triggered escalation

On the prior controlled focused run, latest beat pinned on Cedar, CSLib and init-prelude while preserving expected semantics. That authorized escalation to Mathlib.

## Mathlib result

Both checkers accepted the 5.2 GB / 100.0 M-line Mathlib export.

Raw workflow timestamps:
- pinned invocation start: 16:29:56.405
- pinned result: 16:31:49.097
- latest invocation start: 16:31:49.868
- latest result: 16:33:45.840

Approximate wall durations from those timestamps:
- pinned: 112.69 s
- latest: 115.97 s
- latest delta: +3.28 s, about +2.9%

The Arena formatter rounded both to `1.9 m`, so this result must be treated as a small adverse difference, not a large regression.

## Semantic battery

Latest produced the expected outcomes on:
- `bogus1`: reject
- `constlevels`: reject
- `ctor-num-fields`: reject
- `init`: accept
- `init-prelude`: accept

Thus this is not R9 soundness failure.

## RGRS classification

Primary: R5 Applicability / scale dependence.
Secondary: R2 Cost residual.

The focused-suite speedup did not generalize monotonically to full Mathlib. Therefore broad eagerness + structural absence is not admitted as a global replacement under the frozen resource gate.

Do NOT launch the five-arm interaction experiment as a global-admission study solely on the basis of the focused wins. It remains available as a mechanism probe if a workload separator is later identified.

## Updated question

What measurable workload property separates the focused regimes where latest wins from full Mathlib where it loses slightly?

Candidate separators must be measurable without knowing the outcome, for example:
- ratio of argument evaluations to declarations;
- fraction of arguments structurally absent/ignorable;
- thunk-cache reuse rate under pinned;
- expression/environment reconstruction rate;
- conversion density;
- recursor/iota density;
- declaration-size or dependency-depth distribution.

## Next admissible actions

1. Preserve this as a negative global-admission result.
2. Continue the independent R3 persistent-expression separator.
3. If the R3 mechanism passes, escalate it independently to Mathlib.
4. For eagerness, instrument pinned/latest on at least one winning focused workload and Mathlib and search for a pre-outcome separator before any selective activation experiment.
