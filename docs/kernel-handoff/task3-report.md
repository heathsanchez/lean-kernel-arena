# Task 3 — Nat conversion boundary

The exact representation boundary is repaired. Nat.zero_sub is no longer the final rejection in the exported grind-ring-5 replay. The replay advances to Int.add_assoc, where the existing 2,000,000-step budget is exhausted (UNKNOWN, 2,000,001 steps; 199196 parsed records; 22.467 seconds). This does not establish acceptance of the whole export.

## Change and reasoning

The Nat offset layer retains its raw-input fast path and exposes the same rule as `equalNatOffset`. The kernel invokes that optional rule immediately after normalizing both operands, before rigid-head rejection. This reuses the existing conversion boundary without eager additional normalization or catching/reinterpreting rejections. The rule requires `nat-literals`; arbitrary mixed symbolic terms fall back. Literal pairs compare directly with BigInt, avoiding the prior recursive decrement of huge unequal literals. Constructor peeling is charged to the kernel budget.

No Nat.zero_sub name shortcut or additional theorem rule was added. No normalization cache change is needed: native arithmetic yields a primitive literal, whereas literal WHNF yields zero/succ. Both are lawful definitional representations, and cached successful results need not enforce one syntax. Conversion must recognize their equivalence where those cached forms become visible. Re-normalizing every result could cause enormous unary expansion and would address representation choice rather than conversion scheduling.

## Regression and evidence

The committed 61-line fixture is the exported inductive N package from `_build/tests/tutorial/044_natDef.ndjson`, with only the root name N renamed Nat. It passes the real export checker. Every test kernel revalidates that package and a lawful Nat.add definition constructed with Nat.rec; no fabricated environment or injected normalization result is used.

The focused regression compares an actual Nat.rec computation returning Nat.zero against a primitive zero. Warm cases obtain the literal from normalizing Nat.add 0 0, and explicitly verify the two cached outputs are `const Nat.zero` and `nat 0`. Both operand orientations and cold/warm cache paths are exercised, with repeat conversion. Controls reject 0 vs 1, 2^64 vs 2^64+1 in both orientations, and distinct symbolic successor terms; exact big successor equivalence and capability gating also pass.

Before implementation, the initial computed-zero fixture (beta reduction) failed in both warm orientations with rigid-head-mismatch, and a huge-numeral control overflowed the host stack: 2 passed, 3 failed. The final stronger Nat.rec regression passes 6/6.

Causal ablation: a separate scratch copy removes only the normalized-form hook from kernel-base.mjs, preserving the raw fast path, direct BigInt comparison, and all other source. The final regression then has 4 passes and precisely 2 failures: both warm-cache orientations again reject with rigid-head-mismatch. The main working tree was never reverted for ablation.

Commands/results:

- `node --test genesis/nat-offset-defeq.test.mjs`: 6/6 pass; `/workspace/scratch/feacdaa61cc5/task3-focused.log`.
- `node genesis/test.mjs`: exit 0, FAST_GROWTH_PASS, training 16 / heldout 96; `/workspace/scratch/feacdaa61cc5/task3-core-test.log`.
- `node --test /workspace/scratch/feacdaa61cc5/task3-ablation/nat-offset-defeq.test.mjs`: expected exit 1, 4 pass / 2 fail; `/workspace/scratch/feacdaa61cc5/task3-ablation.log`.
- `ulimit -s 65536` followed by `MATHGRAPH_INPUT_BYTE_LIMIT=20000000 MATHGRAPH_RECORD_LIMIT=400000 node --stack-size=32768 genesis/zero-sub-diagnostic.mjs`: process exit 0, semantic UNKNOWN budget-exhausted at Int.add_assoc; `/workspace/scratch/feacdaa61cc5/task3-giant.json`, empty `.err`. Its two Nat.zero_sub diagnostic rows are internal speculative rejects; the final checked declaration advances beyond Nat.zero_sub.
- `git diff --check`: clean.

Parent owns CI and the full corpus gate. Only the two semantic source files, regression test, and fixture are included in this task's commit. The remaining Int.add_assoc budget frontier is reported without speculative further changes.

Commit: `71c7dd9` — Repair Nat literal conversion after normalization.
