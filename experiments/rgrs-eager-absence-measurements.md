# RGRS measurement plan: eager + structural absence

Status: PRECOMMITTED measurement plan. Do not use post-hoc metrics as primary evidence.

## Purpose

If latest sokonanoda clears the Mathlib + semantic gate, explain the gain mechanistically rather than merely reproducing it.

## Frozen counters

Record per workload and arm:

- `arg_value_calls`
- `direct_eval_arg_calls`
- `thunk_create_calls`
- `thunk_hc_probes`
- `thunk_hc_hits`
- `thunk_hc_misses`
- `absent_arg_queries`
- `absent_arg_true`
- `arg_is_ignorable_queries`
- `arg_is_ignorable_true`
- `ignores_binder_queries`
- `ignores_binder_true`
- `conversion_calls`
- `conversion_skipped_ignorable_arg`
- wall time
- CPU time if available
- peak RSS
- semantic outcome

## Primary ratios

`thunk_avoidance = 1 - thunk_create_calls / arg_value_calls`

`absence_rate = absent_arg_true / absent_arg_queries`

`ignorable_rate = arg_is_ignorable_true / arg_is_ignorable_queries`

`binder_absence_rate = ignores_binder_true / ignores_binder_queries`

`conv_skip_rate = conversion_skipped_ignorable_arg / conversion_calls`

## Causal interpretation

- If eagerness-only wins with little structural skipping, classify the gain primarily as evaluator simplification / thunk avoidance.
- If absence-only wins with little eagerness contribution, classify as R4 observability / R3 redundant comparison elimination.
- If the combined arm exceeds the sum of isolated gains, classify as a positive interaction: structural absence changes the economics of eager evaluation.
- If full latest materially beats eager+absence-core, attribute the residual to the remaining eval/conv changes and decompose only that residual.
- If counters move but wall/CPU do not, classify R12 displacement or R2 instrumentation/overhead rather than claiming the mechanism.

## External-verifier gate

No mechanism is admitted unless the semantic outcomes remain correct on the frozen accept/reject battery and the performance direction reproduces on the same pinned procedure.
