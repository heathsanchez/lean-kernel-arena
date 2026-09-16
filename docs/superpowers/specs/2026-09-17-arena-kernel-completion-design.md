# Arena Kernel Completion and First-Place Design

Date: 2026-09-17
Branch: `mda-arena-qualification-v1`
Status: frozen implementation design

## Objective

Produce a minimal, elegant Lean kernel implementation for Lean Kernel Arena that is:

1. sound on every prescribed reject case,
2. complete on every prescribed accept case,
3. free of runtime errors and unsupported regressions on the current Arena workload,
4. fast enough on Mathlib to rank first under the Arena ordering,
5. structurally smaller than the accumulated experimental stack by compiling verified repeated work into a small production core.

No upstream pull request is created until explicitly authorized.

## Governing development law

Apply the Boundary Learns / MSI / MDA loop literally:

`encounter -> witness -> residual -> necessary constraint -> reuse/requalify/expand -> verify -> replay -> admit -> persist/compound -> ablate -> repeat`

A candidate change is admitted only when it advances a measured residual, preserves all protected verdicts, and survives causal testing. Failed candidates remain provenance only and do not stay on the production path.

## Current frozen state

The qualification branch currently passes the focused semantic and runtime regressions and the 96-case held-out set. The frozen 190-case downloadable Arena corpus is at:

- 183 correct
- 0 wrong
- 7 UNKNOWN
- 0 errors

The remaining seven cases form four execution-residual families rather than seven independent semantic gaps:

1. giant Prelude/conversion: `init-prelude`, `perf/grind-ring-5`,
2. fueled computation: `perf/fueled-chain`,
3. deep list machinery: `magma-list-deep-n21`, `magma-list-deep-n36`,
4. pair/countermodel: `magma-list-pair-n7`, `magma-list-pair-n21`.

The downloadable corpus is not the final Arena qualification because large tests are omitted from that bundle.

## Non-negotiable invariants

Every retained production change must satisfy all of the following:

- zero newly wrong ACCEPT/REJECT verdicts,
- no weakening of existing semantic guards,
- no target-name special cases when a general execution consequence is available,
- no optimization justified only by wall-clock noise,
- no promotion from timeout/search failure to a new semantic capability without an actual completeness/obstruction certificate,
- exact restart/replay reproducibility,
- ablation must restore the claimed cost or residual effect for causal claims,
- provenance and experiments remain separate from active production execution.

## Phase 1: close the four residual families

### 1. Giant Prelude/conversion residual

Existing evidence shows the dominant charged work is substitution, not missing Nat semantics or broad WHNF reuse. Exact-identity substitution memoization produced many hits without moving the semantic frontier. Broad structural-WHNF caching was rejected because of memory growth. Free-variable/support pruning materially reduced constructed nodes and advanced at least one frontier, but on-demand discovery remained too expensive.

The next preferred candidate is therefore intrinsic exact free-support metadata on canonical term nodes.

For each immutable term node, retain the smallest exact support summary needed to answer whether substitution at depth `d` can affect that subtree. If the support proves irrelevance, substitution returns the original node by identity without traversing or rebuilding it. Metadata must be derived compositionally at node construction/validation and must not change semantic equality.

Candidate admission sequence:

1. add a focused red witness demonstrating repeated large binder-independent substitution,
2. implement compositional support metadata,
3. replay the giant witnesses at 1M/2M/4M semantic budgets,
4. compare semantic steps, constructed nodes, RSS, and frontier declarations against baseline,
5. replay all 190 cases at 2M,
6. ablate support pruning and require the giant cost/frontier regression to return,
7. retain only if the 190-case frontier improves with zero wrong verdicts.

If intrinsic support alone is insufficient, compose it only with an independently justified dynamic-slot or recursor-prefix consequence, again under replay and ablation.

### 2. Fueled-chain residual

Instrument the root-lambda/fuel path and separate:

- substitution cost,
- repeated inference,
- recursor-prefix reconstruction,
- normalization/conversion recurrence.

Construct the smallest focused witness on which rival explanations predict different charged work. Compile only the recurrent exact consequence demonstrated by that witness. No `chain6_datF` name-specific path is admitted.

### 3. Deep list residual

The shared `_sparseCasesOn_1` frontier indicates one common execution obstruction. Profile both N21 and N36 together, looking for repeated recursor/pattern-match spines, binder transforms, or structurally identical conversion states.

Prefer a shared stack-safe support-aware recursor/pattern-match consequence over any `List.get?Internal` special case. A retained mechanism should improve both scales from one implementation.

### 4. Pair/countermodel residual

Run the current countermodel atlas on N7 and N21 and identify which exact computation scales superlinearly or is repeatedly reconstructed. Retain a compiled consequence only if the same mechanism appears at both scales and survives controls. Otherwise leave the residual typed rather than polluting the kernel.

## Phase 2: freeze 190/190

The first completion gate is:

`190/190 correct, 0 wrong, 0 UNKNOWN, 0 errors`

at the production semantic budget.

After first green:

- rerun from a clean process,
- rerun with caches cold,
- run all focused semantic controls,
- run malformed/negative controls,
- ablate each newly retained mechanism independently,
- reconstruct the production state from immutable source rather than warm process state.

Only then freeze the semantic behavior of the candidate.

## Phase 3: full Arena qualification

The 190-case archive excludes large tests. The completed kernel must then be run through the full official Arena harness and prescribed current-round tests.

Qualification requires:

- every reject case rejected or handled exactly as the Arena contract permits,
- every accept case accepted,
- no checker errors,
- no hidden dependence on the local diagnostic harness,
- the exact checker build/run command intended for release.

Do not claim complete Arena coverage from the downloadable 190-case corpus alone.

## Phase 4: Mathlib performance contraction

Only after correctness is frozen, profile the complete kernel on Mathlib under the real Arena build/run environment.

Measure at least:

- parse/import cost,
- substitution and shifting,
- inference/checking,
- WHNF/reduction,
- definitional equality/conversion,
- declaration lookup/instantiation,
- allocation and constructed-node count,
- peak RSS and GC pressure,
- cache hit rates and cache memory cost.

Optimize the largest measured contributor only. Every performance candidate must preserve the frozen full-Arena verdict vector.

The expected high-leverage contraction is representation-level: canonical shared term nodes carrying exact compact metadata, allowing substitution, binder movement, and rigid conversion to avoid reconstructing work. If Mathlib profiling falsifies that priority, follow the profile rather than the hypothesis.

## Phase 5: descaffold into the final kernel

The submitted production architecture should not preserve the historical experiment stack merely because it exists. After capabilities are verified, collapse them into the smallest set of direct invariants.

Target production shape:

1. parser and validated declaration environment,
2. canonical shared term representation with exact compact metadata,
3. stack-safe binder transforms,
4. one WHNF/reduction machine,
5. one exact conversion machine,
6. Lean inductive/recursor/projection/quotient semantics,
7. declaration checker,
8. only measured caches whose causal value survives ablation.

Delete redundant wrappers, shadow implementations, speculative caches, and target-specific probes.

## First-place performance gate

Arena correctness ordering dominates speed, so performance work never trades away a verdict.

The release target is a repeatable Mathlib time with enough margin over the current leading checker to survive runner variance. Use repeated clean runs and retain the exact release candidate binary/source revision.

A single marginally faster run is not sufficient evidence for first-place readiness.

## Evidence and acceptance record

For every retained mechanism, store:

- frozen residual witness,
- before/after semantic step counts,
- constructed-node counts,
- wall time and RSS as secondary measurements,
- corpus verdict vector,
- control results,
- ablation result,
- commit SHA and workflow run,
- exact claim boundary.

## Completion conditions

The work is complete only when all are true:

1. downloadable public corpus is fully decided with zero wrong verdicts,
2. complete official Arena workload is fully qualified,
3. Mathlib completes under the exact release checker interface,
4. repeated clean benchmarks place the candidate ahead with credible margin,
5. the final active kernel has been descaffolded to the minimal retained architecture,
6. all release evidence is replayable from a clean checkout,
7. no upstream PR has been opened without explicit authorization.

## Anti-drift rule

A green workflow is not enough. A candidate earns retention only through the declared verifier, replay, controls, and ablation. When evidence is insufficient, keep UNKNOWN and run the next separating experiment rather than widening the kernel by narrative.
