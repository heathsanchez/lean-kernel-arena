# Kernel development handoff — 2026-09-16

Continue on `heathsanchez/lean-kernel-arena`, branch `mda-arena-qualification-v1`.
Do not open a PR to the official Arena repository without Heath's approval.
Development-branch pushes are authorized. This is unfinished development, not an Arena-qualified submission.

## State and evidence

The preceding remote checkpoint was `2114166590a3050989263a7ad358ed8a94f8cf2d`.
This handoff adds the reviewed K/unit-eta/theorem-major and quotient evaluator parity repairs, flat internal Lean name encoding, and the binder traversal candidate. It preserves the complete remote repository tree. Local source commits were made in a selected-file snapshot, so their hashes are provenance references rather than remote ancestors:

- `c979107`: shared K/unit-eta and theorem-major rules in iterative evaluators.
- `ff70c9b`: shared quotient reduction in iterative evaluators.
- `9b39e94`: flat, tagged, collision-resistant internal name representation; NDJSON wire format unchanged.

The full 190-case public run on local `9b39e94` completed with **183 correct, 0 wrong, 7 UNKNOWN, 0 errors**. Its exact runtime hashes, input hashes, and per-case results are in `genesis/evidence/qualification-flat-9b39e94.json`. All 71 invalid cases rejected; 112 of 119 valid cases accepted. The gate is FAIL because UNKNOWN is not success.

After adding explicit-stack binder range/shift/substitution traversal, fresh validation before this handoff passed **40/40 focused tests** and **16 training / 96 held-out core cases**. The three binder tests reproduced two stack overflows before repair and passed afterward. Independent static review approved preservation of cache keys, binder depth, tick ordering, and completed-result publication. Full public-corpus validation of the binder candidate was interrupted by an execution-environment outage and has NOT completed. Do not attribute the 183/190 result to this newer candidate.

## Run

Use Node 24, the production default stack, and the checked-in qualification workflow. It downloads the public corpus, builds a SHA-256 manifest, runs core and all `genesis/*.test.mjs` tests, and requires every case to return the expected verdict. A branch push runs this workflow automatically.

```sh
node genesis/test.mjs
node --test genesis/*.test.mjs
# After retrieving _build/tests and its manifest using the workflow:
node genesis/qualify-corpus.mjs
```

`genesis/production.mjs` is the shared production import stack and limit configuration. `checkers/mathgraph/main.mjs` imports it. CLI exit codes are 0 ACCEPT, 1 REJECT, 2 UNKNOWN, 3 error. Default semantic budget is 2M, input cap 20MB, record cap 400K. Larger diagnostic budgets do not constitute default-contract qualification. The checker descriptor's submission revision is not yet updated; pin it only after the desired runtime is qualified.

## Exact remaining public cases

- `init-prelude.ndjson` and `perf/grind-ring-5.ndjson`: host-stack limit at `_private.Init.Prelude.0.isValidChar_UInt32` in the last full run. Iterative fallbacks then hit the 2M budget. The new binder traversal removes one known recursive implementation; replay to establish the next frontier.
- `perf/fueled-chain.ndjson`: budget at `chain6_datF`.
- `perf/magma-list-deep-n21.ndjson` and `perf/magma-list-deep-n36.ndjson`: budget at `List.get?Internal._sparseCasesOn_1`.
- `perf/magma-list-pair-n21.ndjson` and `perf/magma-list-pair-n7.ndjson`: budget at `countermodel`.

## Next repair: native arithmetic dispatch

Read `task4-nat-decide-design.md`, especially its final refined implementation section, which supersedes the earlier callback sketch. Implementation has NOT started.

Existing native Nat wrappers are bypassed inside private iterative evaluators. The real Char witness exposes `Nat.ble 55297 4294967296`, but the evaluator unfolds the recursive definition rather than invoking the already-supported primitive rule. Factor a pure descriptor table for the existing Nat primitives, including bounded `Nat.pow`, then evaluate operands with explicit continuation frames in each iterative engine. Preserve miss restoration and all existing caps/bounds. Avoid recursive `k.whnf` operand callbacks; a reverted prototype passed synthetic checks without improving the actual witness.

Require actual Char native-hit evidence and before/after steps, along with partial-application, nonliteral, deeply nested operand, quotient/recursor continuation, and false-HPow controls. Do not restore any of the six deleted nonprimitive name shortcuts. Lean primitive Nat rules are distinct from arbitrary typeclass/dictionary names.

## Other findings

Flat encoding reduced measured corpus name characters from 954,520,809 to 4,162,802. This measures one representation cost, not total memory or Arena instructions. Reports retain their local diagnostic paths as historical provenance; those scratch paths will not exist on a new machine.

For fueled-chain, profiling at 500K steps found broad repeated inference/conversion, not a single expensive equality or substitution. Counts: infer 6,907; whnf 27,282; declaration instantiation 19,916; equal 23,713; substitute 22,646. Exclusive ticks: infer 52,878; equal 34,696; proofType 21,279; whnf 3,258; substitute 398. A structural inference cache reduced duplicate calls but did not advance the 500K/2M frontier and worsened wall time; do not retain it. Universal LocalDef-first and global early proof irrelevance also failed to help. Profile the root lambda's child inference before choosing another cache.

## Full Arena and Mathlib

The public archive contains 190 cases, while the complete Arena set has 198. The eight missing large valid cases, full Mathlib execution, and comparable instruction measurements remain unverified. No first-place claim is warranted.

Read `mathlib-streaming-design.md`. Streaming ingress alone is insufficient: current Map/expanded-AST retention requires a compact or disk-backed expression representation for the roughly 5.2GB Mathlib export. Preserve EOF validation, malformed-tail precedence, hashes, and fallback replay when introducing streaming. The published native Rust MathGraph checker is a different implementation from this JS kernel; its leaderboard score is not evidence for this branch.

Follow the requested method: question requirements and semantic warrants; delete unsupported work; repair the smallest demonstrated obstruction; independently check and ablate; retain measured improvements; automate last.
