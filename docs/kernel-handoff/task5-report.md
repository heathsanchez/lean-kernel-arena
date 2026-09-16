# Task 5: default-stack false rejection in fallback execution

The default-stack false REJECT at eq_of_heq is repaired without changing stack flags, raising budgets, or weakening rejection globally. The final default production replay now returns UNKNOWN host-stack-limit at _private.Init.Prelude.0.isValidChar_UInt32; both subsequent stack-safe and LocalDef attempts exhaust their 2M budgets. Its final elapsed time is 12.840 seconds, retained steps 657015, parsed records 63723.

## Root cause and exact boundary

On an isolated snapshot after d9ce12f, the ordinary retained checker progressed through eq_of_heq and eventually exhausted the default Node stack at isValidChar_UInt32. The captured stack showed recursive substitution in exact-binder-transport-layer.mjs. checkExport then restarted the export in a fresh Kernel with _fullStackSafe=true. That replay rejected eq_of_heq after only 7237 steps and the harness promoted its result to the final verdict.

The first rejected leaf was an Eq.rec with a variable proof major and identical endpoints (var5), compared with its minor (var3), in context depth 10. The retained reducer's rule-K branch reduces that term. Both iterative recursor continuations implemented constructor matching only and omitted rule K and unit eta, returning the unreduced recursor as if it were a complete WHNF. Core conversion then rejected app versus var. This was not evidence that eq_of_heq was invalid, and not speculative cache poisoning by a caught RangeError.

The same isolated snapshot with Node stack size 32768 never entered the defective stack-safe replay: it reached UNKNOWN budget-exhausted at isValidChar_UInt32 after 2M steps. The profiling wrapper changes stack depth and timing, so these pre-fix counts are diagnostic, not performance comparisons. Evidence: task5-default.json, task5-large.json, corresponding stderr files; isolated source under task5-stack-profile.

## Repair

The exact existing constructor-independent K and unit-eta branches were factored into `recursorRhsWithoutConstructor`. All original capability, recursor metadata, constructor field-count, universe, derived-index, and unit-like-shape conditions are preserved. The helper returns an RHS without recursively reducing it. Base WHNF and both iterative engines continue evaluation themselves.

A direct normalized-text comparison confirmed the helper body is identical to the prior two branches except that `return this.whnf(rhs)` becomes `return rhs`. This avoids a second independent implementation of those semantic guards.

Both iterative engines also now use the existing unfoldTheoremHead operation on a neutral major before rule matching. The continuation resumes reduction of the unfolded body with the same 10000-unfold guard as base whnfMajor. No unconditional proof rewriting or theorem-name shortcut was added.

The literal terminal / one-constructor-major changes from d9ce12f remain intact. Source files changed here are kernel-base.mjs, scoped-beta-spine.mjs, and stack-safe.mjs, plus one focused test and its small exact exported fixture.

## Tests and evidence

The new fixture contains the exact Eq and PUnit inductive packages decoded from tests/init-prelude.ndjson (about 4KB). Real Kernel instances validate these packages together with the existing exported Nat fixture. Tests run in retained and full-stack modes and cover:

- Eq.rec with a variable major and matching derived index reduces to its minor.
- A mismatched endpoint stays stuck.
- Rule-K capability absence stays stuck.
- Unit-eta reduction requires its capability and does not apply to a multi-constructor inductive.
- Two validated theorem aliases unfold to an Eq constructor with rule K disabled, proving the theorem-major path itself works.

Before implementation the K/unit suite had 4 passes and 2 failures, both in full-stack mode. After factoring it passed 6/6. The added theorem-alias test then showed 7 passes and 1 full-stack failure before theorem-major continuation support; the final new suite passes 8/8.

Final combined focused tests: 26/26 pass, including the existing Nat literal/major and primitive-pow controls. `node genesis/test.mjs`: FAST_GROWTH_PASS, training 16 / heldout 96. `git diff --check`: clean. Logs: task5-red.log, task5-green.log, task5-theorem-red.log, task5-final-focused.log, task5-final-core.log.

The final actual-production command used the default Node stack and a 60-second process timeout. It returned UNKNOWN with retained host-stack-limit and stack/local attempt reasons budget-exhausted, rather than false rejection. Full result: task5-final-default.json; stderr is empty. A large-stack replay after K/unit factoring likewise returned UNKNOWN budget-exhausted at the same declaration (task5-fixed-large.json).

The remaining Char cost and iterative native-primitive dispatch are separate work. No global REJECT-to-UNKNOWN demotion was introduced: the missing semantic rules were restored, and negative controls remain effective.

Commit: `c979107` — Preserve recursor rules in iterative execution.
