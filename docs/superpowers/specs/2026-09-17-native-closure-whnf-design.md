# Native Closure WHNF Design

## Objective

Close the remaining giant Lean Kernel Arena residuals without weakening soundness by replacing eager evaluator-side substitution materialization with a transient closure machine. The first implementation is intentionally evaluator-only: inference, equality, declarations, stored syntax, caches that assume ordinary syntax, and external results continue to receive canonical immutable term arrays.

## Evidence that earns this change

The repaired production kernel is currently 183/190 on the frozen public corpus with 0 wrong verdicts and 7 UNKNOWNs. `init-prelude` and `grind-ring-5` no longer fail from host recursion; they reach the semantic budget at `_private.Init.Prelude.0.isValidChar_UInt32`.

Repeated exact-cache experiments did not move that frontier: support metadata, support-pruned substitution, dynamic-slot specialization, exact `lowerBound` caching, exact context-aware WHNF caching, and the existing narrow multi-beta closure separator all remained at the same declaration. The narrow beta-closure layer was safe but activated only 279 / 246 spines across the giants even at 8M steps. The remaining problem is therefore the eager evaluator representation, not a missing cache around it.

## Chosen architecture

The WHNF evaluator executes over transient closure states rather than eagerly substituting ordinary syntax.

A closure is:

```text
Closure := { term, env }
Env     := immutable sequence of Closure bindings
State   := { closure, spine, frames }
```

`spine` is a sequence of pending argument closures. `frames` are exact continuation frames needed for projection, recursor, quotient, and other existing WHNF head rules.

### Core transitions

- application: push argument closure onto `spine`; continue with function closure.
- lambda + pending argument: extend the environment; continue with the lambda body without calling eager `substitute`.
- let: extend the environment with the value closure; continue with the body.
- bound variable: resolve through the closure environment; only shift/materialize when an ordinary-term boundary requires it.
- definition head: instantiate universes exactly as retained code does; continue as a closure with the same environment.
- projection / recursor / quotient: inspect the major premise through closure WHNF, then apply the same retained semantic rule. Unsupported or not-yet-migrated cases materialize and delegate to retained WHNF.

## Semantic firewall

Closures are not Lean syntax and never escape evaluator execution. In version 1 they must not enter:

- `infer`
- `equal`
- declaration storage or declaration validation
- structural / normalization caches whose contract is ordinary immutable syntax
- exported checker results
- serialized evidence

Every exit to one of these consumers goes through one `materializeClosure` operation that produces exactly the ordinary de-Bruijn term represented by the closure.

If the closure machine cannot prove it can execute an existing WHNF case with identical semantics, it materializes the current state and delegates to the retained evaluator. No new proof rule or reduction rule is introduced.

## Materialization

Materialization is iterative and stack-safe. It interprets a closure under binder depth:

- variables below binder depth remain bound locally;
- variables represented by the environment resolve to their bound closure;
- unresolved variables are lowered by the number of consumed environment slots;
- resolved non-closed values are shifted by the current binder depth exactly as eager substitution would require;
- composite terms are rebuilt through retained `make`, preserving canonical sharing.

Materialization may memoize only exact successful `(term identity, environment identity, depth)` results within one run. Failed/incomplete materializations are never cached.

## Integration

The initial implementation is a new `native-closure-whnf-layer.mjs` imported as the outermost evaluator execution layer after the retained WHNF stack, including the WHNF re-entry trampoline. It captures the already-qualified retained WHNF as its fallback.

The layer is first exercised by a dedicated separator and regression tests. It is not added to `kernel.mjs` until it demonstrates causal progress on at least one giant while preserving every protected verdict. Promotion then requires the full frozen public-corpus qualification.

## Tests

### Unit parity

1. deep beta chain: closure WHNF equals retained eager WHNF without repeated substitution materialization.
2. nested lets: environment extension matches retained substitution semantics.
3. application spine with local definition head: preserves the `fueled-chain` regression fixed by the trampoline.
4. projection after beta/let: same ordinary WHNF result.
5. de-Bruijn capture under nested binders: materialization equals retained sequential substitution.
6. unsupported recursor/quotient shape: fallback is byte/structure-equivalent to retained WHNF.

### Protected integration

- existing core regression suite must stay green;
- `perf/shared-subterm` must remain ACCEPT;
- `perf/fueled-chain` must not become a false REJECT;
- all forged / reject controls must remain unchanged.

### Causal giant separator

Run current production + candidate at 2M, then 4M if needed, on `init-prelude`, `grind-ring-5`, and `shared-subterm`. Record status, reason, steps, constructed nodes, frontier, closure transitions, environment lookups, materializations, fallbacks, and eager substitute calls avoided.

A candidate is retained only if it has 0 wrong verdicts and either closes a giant or materially advances the frontier / reduces the charged work while preserving downstream progress. Mere cache hits or wall-clock-only gains with an identical semantic frontier do not qualify.

## Promotion gates

1. unit/regression parity green;
2. giant separator shows causal progress;
3. frozen public corpus: no wrong verdicts and no regression from the safe baseline;
4. candidate is imported into production only after gate 3;
5. rerun frozen 190 corpus on production composition;
6. then attack the remaining list / pair / fueled residual families;
7. after 190/190, run the complete official Arena corpus including large omitted tests;
8. only after correctness completeness, profile Mathlib and contract the dominant runtime costs until the submission has a reproducible leaderboard margin.

## Non-goals

This phase does not change inference, equality, type theory, declaration semantics, public term syntax, or the upstream Arena repository. It does not open a pull request. It does not special-case declaration names, test files, or expected verdicts.
