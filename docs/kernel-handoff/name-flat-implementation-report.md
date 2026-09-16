# Flat-name implementation handoff

Implementation is isolated in `name-flat-work` at baseline `d9ce12f`; `kernel-work` was not edited. The review patch is `name-flat.patch`.

## Changed files

- New: `genesis/name-codec.mjs`, `genesis/name-codec.test.mjs`
- Runtime: `kernel-base.mjs`, `kernel-semantic.mjs`, `native-nat-reduction-layer.mjs`, `nat-offset-defeq-layer.mjs`, `compiled-nat-pow-layer.mjs`, `char-proof1-reject-profile.mjs`
- Tests: `test.mjs`, `nat-offset-defeq.test.mjs`, `nat-pow-soundness.test.mjs`, `declaration-warrant.test.mjs`

Inactive duplicated code under `checkers/` was not touched. The untracked diagnostic `zero-sub-diagnostic.mjs` in the source snapshot was locally adjusted but deliberately excluded from the review patch because it is not part of baseline `d9ce12f`.

## Encoding and compatibility

Canonical names are versioned flat JSON arrays: `["$lean-name-v1",["str","Nat"],["str","succ"]]`. String and numeric components remain tagged. `appendName` wraps a noncanonical API prefix in an explicit `["atom", value]` base, so derived children of arbitrary string names remain supported and cannot collide with root-structured export names. NDJSON input records are unchanged.

Both the main parser and semantic obstruction prepass use the shared codec. Recursor derivation and active native Nat helpers use the same constructors. The diagnostic display helper decodes flat components.

## Verification

- Codec collision/deep-name tests: pass.
- `node genesis/test.mjs`: pass, including 96 held-out cases and arena fixture checks.
- `node --test genesis/*.test.mjs`: 26/26 pass.
- All 190 local NDJSON fixtures completed in both baseline and flat snapshots.

Exact 190-corpus comparison has three output differences:

1. `tutorial/014_selfProof` remains `REJECT`; only its diagnostic embeds the new canonical spelling.
2. `init-prelude` changes from `UNKNOWN/host-stack-limit` to `REJECT/rigid-head-mismatch`.
3. `perf/grind-ring-5` changes from `UNKNOWN/host-stack-limit` to `REJECT/rigid-head-mismatch`.

The last two are a review blocker for direct production adoption. The encoding is bijective and all name producers agree, but removing the enormous strings lets the current primitive checker advance past its former host-stack resource frontier and expose a later rejection. Mapping that rejection back to UNKNOWN inside the name patch would hide a checker issue, so the isolated patch leaves the result visible for review.

## Measurements

Fresh Node processes, identical input/config, `process.resourceUsage().maxRSS`:

| Fixture | Baseline elapsed / max RSS | Flat elapsed / max RSS | RSS reduction |
|---|---:|---:|---:|
| `init-prelude` | 13.30 s / 1,300,740 KiB | 3.89 s / 532,028 KiB | 59.1% |
| `grind-ring-5` | 15.53 s / 2,338,468 KiB | 4.31 s / 675,168 KiB | 71.1% |
| Entire 190 corpus, one process | 87.30 s / 4,134,052 KiB | 60.15 s / 2,575,480 KiB | 37.7% |

These are single runs, useful for bounding the effect rather than performance claims. The isolated name-string count measured earlier falls from 805,324,028 to 1,882,384 characters on `grind-ring-5`.
