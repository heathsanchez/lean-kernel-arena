# Qualification evidence and remaining work

User constraint: do not open or submit a PR. Work remains on `mda-arena-qualification-v1`.

## Frozen revision

Remote source: `8f402138672db66e8b040b67aaa83fd0212b5b6c`.
Runtime import-closure SHA-256: `896085734c57be9275261a2d3c79fec922667d8e247674aebb414b6a62a48d96`.
CI run: https://github.com/heathsanchez/lean-kernel-arena/actions/runs/35069462552

The strict public-corpus gate reports **FAIL**: 182 correct, zero wrong, seven UNKNOWN, one timeout. This means 111/119 valid exports accepted and 71/71 invalid exports rejected. It is not full Arena qualification: the downloadable corpus omits eight larger valid exports, including Mathlib.

The local source-identity-checked replay matches CI totals. Its complete evidence is `genesis/evidence/qualification-8f402138.json`. The source manifest and individual export hashes are included there.

## Retained repairs

1. A bounded Nat power calculation may return its result only after the exponentiation loop completes. The previous code could return a partial accumulator for large powers. Tests use real Kernel reduction and independently computed integer expectations; a mutation restoring the old guard reproduces the failure. Independent review approved.
2. Nat literal/constructor comparison now also runs after normalization. This closes a cache-sensitive disagreement between literal zero and `Nat.zero`. Both orientations, cold/warm caches, exact large literals and capability removal are covered. Removing only the new normalization-boundary hook restores the two warm-cache failures. Independent review approved.
3. The packaged CLI and qualification worker use one production import list and one resource configuration. A gate success cannot silently use a larger semantic/input/record allowance than deployment. Tests include a valid input larger than 2 MB and budget-exhaustion parity. Per-worker source identity prevents mixed-version reports. Independent review approved.

## Measured residuals

| Export | Frozen result | Next supported investigation |
| --- | --- | --- |
| init-prelude | UNKNOWN at UInt64.ofNatLT, 2,000,001 steps | Delete unary normalization of the existing exact 2^64 literal. An isolated larger-power shortcut made no difference before this obstruction. |
| perf/grind-ring-5 | UNKNOWN at Int.add_assoc, 2,000,001 steps | Prior Nat.zero_sub rejection is passed; inspect the next conversion after numeral normalization. |
| perf/app-lam | 60-second timeout | Existing LocalDefKernel-first isolated replay accepts in 86,936 steps / 5.82 s. Test structural depth-based evaluator order. |
| perf/fueled-chain | UNKNOWN at chain6_datF | Profile repeated conversion before changing budget. |
| perf/magma-list-deep-n21, n36 | UNKNOWN at List.get?Internal._sparseCasesOn_1 | Profile shared conversion work. |
| perf/magma-list-pair-n21, n7 | UNKNOWN at countermodel | Profile shared conversion work. |

Resource defaults for this revision are 2M semantic steps, 20M input bytes and 400K records. Changing these limits is not a performance optimization.

## Remaining qualification requirements

Complete all valid exports without changing invalid verdicts; preserve small semantic counterexamples for every repair; replace whole-input materialization before attempting multi-gigabyte Mathlib; replay the omitted exports with the pinned exporter/toolchain; measure actual Arena instructions on the same workloads. Wall time and the kernel's internal step counter are not substitutes for the ranking metric. No first-place claim is warranted by the current results.
