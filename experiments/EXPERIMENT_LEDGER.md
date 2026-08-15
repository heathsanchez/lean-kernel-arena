# MathGraph Lean Kernel Experiment Ledger

Purpose: preserve every decision-changing performance experiment separately from the current narrative. Raw speed records, semantic admission, causal understanding, and public leaderboard status are distinct fields.

## Reference revisions

- Arena-pinned sokonanoda: `0fab8874080e379a774a9a27f7538d8a1ddd786b`
- upstream sokonanoda latest studied: `9b4ea12f4cd437d00b6bcd0e34743065c58dea08`
- MathGraph Kernel release wrapper: `metalogiclabs/mathgraph-kernel@07f7d884bdc1bbd0e6d161bf541908cdf9d14e2f`

## Frontier summary

### A6 — strongest preserved validated performance asset

Source: `metalogiclabs/mathgraph-kernel`.

A6 patches upstream `9b4ea12` with:
1. session budget 1 MiB -> 2.5 MiB (A3),
2. avoid transient environment pruning while consuming nested lambdas in `apply_many` (E0018),
3. bypass open-eval cache/canonicalization for `App` and `Lambda` (E0024/E0025),
4. capture the current environment directly for `Lambda` closure construction rather than `key_env` (E0030).

Recorded protected evidence:
- semantic corpus: 161/161, 0 declines,
- A5 -> A6 protected PGO gate: wall -2.652%, CPU -0.495%, RSS -0.193%, wall wins 9/12,
- same-runner calibration vs Arena-pinned `0fab887`: median 1.0893 s -> 0.8276 s, paired median -23.96%, 16/16 wins, ~1.3162x speedup,
- status: **RETAIN / validated calibration; not yet a public Arena leaderboard result**.

Do not lose or replace A6 merely because later RGRS experiments use pinned/latest upstream as cleaner causal controls.

### A5 — strongest conditional raw speed signal on Cedar

Branch: `mathgraph-local-headtohead`, run `31881003667`.

Same-runner focused measurements:
- pinned Cedar: 31.6 s; A5 Cedar: 23.4 s (~25.9% faster), both correct,
- pinned CSLib: 33.7 s; A5 CSLib: ~1.4 min, both correct,
- pinned Mathlib: ~1.7 min; A5 Mathlib did not finish before runner shutdown, so no valid A5 Mathlib result,
- pinned Std: 10.0 s; pinned Init: 5.9 s; pinned init-prelude: 45 ms (A5 step terminated before these were reached).

A5 is A6 with E0030 reverted. Status: **RETAIN as a conditional speed record and regime-split witness; not globally admissible**.

The Cedar/CSLib split is a root observation that motivated architecture/applicability work. Never summarize A5 simply as “failed.”

## Architecture swing — eager vs irrelevance-only

Branch: `mathgraph-architecture-swing`, run `31893417057`.

Arms:
- pinned lazy `0fab887`,
- upstream latest `9b4ea12` (broad eager argument evaluation + structural irrelevance/absence changes),
- irrelevance-only: retain new structural machinery but restore older lazy/thunk path.

Focused results (all correct):
- Cedar: pinned 34.3 s, latest 30.9 s, irrelevance-only 32.5 s,
- CSLib: pinned 34.8 s, latest 32.3 s, irrelevance-only 34.8 s,
- init-prelude: pinned 46 ms, latest 43 ms, irrelevance-only 47 ms.

Verdict: broad eagerness was not the poison on these focused workloads; structural irrelevance alone did not explain the full gain. **REFRAME to R5 applicability and scale.**

## Full Mathlib latest-vs-pinned escalation

Branches: `mathgraph-rgrs-latest-escalation` / result copied into applicability branch.

Raw workflow timing was approximately:
- pinned `0fab887`: 112.69 s,
- latest `9b4ea12`: 115.97 s,
- latest ~2.9% slower.

Semantic battery passed. Verdict: **R5 applicability / scale dependence**. Do not infer universal eager or lazy superiority.

This result is about unpatched latest upstream, not A6. It does **not** invalidate A6's separate protected calibration.

## Persistent-expression DAG / identity experiment

Branch: `mathgraph-rgrs-dag`.

Source inspection found sokonanoda already has persistent + per-TcCtx DAG/interning; expression allocation did not mirror persistent lookup used by several other object classes.

Arms:
- D0 pinned,
- D1 persistent expression lookup + reuse global identity,
- D2 same persistent lookup but discard hit (probe-only ablation).

Focused timing:
- Cedar: D0 37.0 s, D1 33.7 s, D2 34.8 s,
- CSLib: D0 39.6 s, D1 36.9 s, D2 37.1 s,
- init-prelude: about 58 / 55 / 56 ms.

Because D2 retained most of D1's gain, broad persistent identity was not causally established. Instrumented non-PGO follow-up even had probe-only faster than reuse (Cedar ~29.3 vs 30.8; CSLib ~31.1 vs 32.0). Verdict: **SUPPRESS broad global-expression-reuse theory unless new causal evidence reopens it.**

Infrastructure failures preceding the valid run were R10 only and do not count against the scientific mechanism.

## R5 static applicability observable

Branch: `mathgraph-rgrs-applicability-probe`.

Static export probe reconstructs free-variable masks and computes absent-binder rate:

`A(W) = structurally absent binders / all binders`.

Acquisition observations:
- Cedar 25.59% -> latest faster,
- init-prelude 24.41% -> latest faster,
- CSLib 16.78% -> latest faster,
- Mathlib 14.84% -> pinned faster.

Frozen acquisition midpoint threshold: `tau = 0.1580774332`.

### Prospective Std test

- structure measured before timing: A(Std) = 19.31346547%,
- frozen prediction: latest faster,
- observed: pinned 9.6 s, latest 8.7 s (~9.4% faster), both correct.

This was a genuine prospective success and justified PROJECT rather than immediate suppression.

### Prospective perf-fixture test — selector counterexamples

Frozen before timing:
- app-lam A=95.22% -> latest faster,
- beta-ladder A=92.80% -> latest faster,
- discarded-argument A=35.71% -> latest faster,
- args-before-unfold A=34.15% -> latest faster,
- church-numerals A=27.27% -> latest faster,
- high-A pair predicted to show at least as much latest benefit as lower-A group,
- any sign miss required REFRAME; no threshold retuning permitted.

Corrected workflow: `31912455339`. All semantic outcomes correct.

Observed Arena-formatted timings:
- app-lam: pinned 65 ms, latest 56 ms — hit,
- beta-ladder: pinned 620 ms, latest 626 ms — **sign miss**,
- discarded-argument: pinned 9 ms, latest 8 ms — hit,
- args-before-unfold: pinned 10 ms, latest 11 ms — **sign miss**,
- church-numerals: pinned 12 ms, latest 11 ms — hit.

Verdict: **REFRAME**. The simple workload-level absent-binder threshold is not sufficient (2/5 prospective sign misses), and global A magnitude is not a monotone mechanism signal because beta-ladder is both extremely high-A and adverse.

Preserve absent-binder rate as a coarse correlate with one macro prospective success (Std), but not as an admitted routing law. The updated residual is local interaction: *where/how* binder absence meets evaluator demand matters more than global frequency. Candidate refinements include demanded-vs-discarded argument structure, beta-chain shape, unfolding timing, conversion density, and recursor/iota pressure.

Do not retune `tau` on the revealed fixtures.

## Eager + structural-absence causal interaction experiment

Branch: `mathgraph-rgrs-eager-absence-interaction`.

Precommitted arms:
- A0 pinned,
- A1 eagerness only,
- A2 structural absence only,
- A3 eagerness + structural-absence core,
- A4 full latest.

Causal interaction target: `I = G(E+A) - G(E) - G(A)`.

The workflow is dispatch-only and was deliberately not globally launched after latest lost on full Mathlib. **RETAIN design; scope it only when local interaction evidence makes the comparison admissible.**

## Current interpretation

Do not collapse these records into one “best kernel.” Maintain four frontiers:

1. **Best protected calibrated kernel:** A6 (~23.96% paired median gain vs pinned, 161/161 semantics).
2. **Best conditional raw local result:** A5 on Cedar (~25.9% faster than pinned), with severe CSLib regression.
3. **Best current causal/applicability discovery:** absent-binder rate exposed a real regime distinction but failed as a sufficient global selector; the live target is now local evaluator-demand interaction.
4. **Current public leaderboard frontier:** separate; only an actual Arena run of an exact immutable checker revision establishes it.

The next architectural target should use A6 as the retained performance base, not forget it. RGRS experiments should explain/scope mechanisms and then attempt to **compose admitted discoveries back onto A6**, under semantic, causal, resource, and reproducibility gates.

## Branch inventory to preserve

- `add-mathgraph-kernel-a6`
- `mathgraph-local-headtohead`
- `mathgraph-architecture-swing`
- `mathgraph-rgrs`
- `mathgraph-rgrs-applicability-probe`
- `mathgraph-rgrs-dag`
- `mathgraph-rgrs-dag-instrument`
- `mathgraph-rgrs-eager-absence-interaction`
- `mathgraph-rgrs-latest-escalation`
- `mathgraph-experiment-ledger`

## Rule for future work

Every new experiment must record:
- exact parent/revision,
- intervention and ablation,
- workload and runner,
- raw timing/CPU/RSS,
- semantic/verifier status,
- RGRS residual class,
- verdict/state transition,
- whether the result is raw-local, protected-calibration, or public-Arena evidence.

Never overwrite a faster rejected/scoped arm; retain it as a conditional capability and as evidence about applicability boundaries.