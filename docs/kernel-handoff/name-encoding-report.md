# Recursive versus flat Lean-name encoding

## Measurement

I scanned only `in` name records in the 190 NDJSON fixtures under `kernel-work/_build/tests`; no expression or declaration records were retained. For every name I reproduced the current encoding exactly in shape:

```js
JSON.stringify([encodedPrefix, "str" | "num", payload])
```

and compared it with a collision-free flat component encoding:

```js
JSON.stringify([["str", "Init"], ["str", "Prelude"], ["num", 12]])
```

The character totals are sums of the strings retained by each fixture's name map. V8 normally stores these as one- or two-byte strings depending on representation/content; the UTF-16 column is therefore a conservative payload illustration, not a heap measurement. Map/object overhead is excluded.

| Scope | Names | Current chars | Flat chars | Reduction | Largest current / flat | Max depth |
|---|---:|---:|---:|---:|---:|---:|
| All 190 fixtures (aggregate, not simultaneous) | 47,241 | 954,520,809 | 4,162,802 | 99.56% | 100,333,333 / 384 | 24 |
| `init-prelude.ndjson` | 7,297 | 15,408,921 | 620,106 | 95.98% | 48,650 / 205 | 13 |
| `perf/grind-ring-5.ndjson` | 15,962 | 805,324,028 | 1,882,384 | 99.77% | 100,333,333 / 384 | 24 |

At two bytes per character, name-string payload alone is about 29.4 MiB versus 1.18 MiB for `init-prelude`, and 1.50 GiB versus 3.59 MiB for `grind-ring-5`. The latter fixture is only 9.71 MiB on disk. The maximum `grind-ring-5` name is a 24-component hygienic name; its flat spelling is 384 characters, while repeated JSON escaping expands the current spelling to 100,333,333 characters. This isolates a real memory blocker before any packed expression arena work.

## Minimal migration surface

Introduce one shared name module with:

- `appendName(prefix, tag, payload)` for `str` and `num` components;
- `leanName(...stringParts)` implemented only through `appendName`;
- optionally `displayName` for diagnostics, decoding the same flat representation.

Runtime sites that must migrate together:

1. `genesis/kernel-base.mjs`: local `leanName`, both `in` parser branches, and the recursor-name construction in `addSingleInductive` (`JSON.stringify([d.name,"str","rec"])`). Quotient, Nat, and String built-ins already route through `leanName` once that helper is shared.
2. `genesis/kernel-semantic.mjs`: the second name-record parser used by `unresolvedPropProjectionObstruction`; leaving it recursive would make its constant/declaration keys disagree with the main parser.
3. Runtime native helpers: `native-nat-reduction-layer.mjs`, `nat-offset-defeq-layer.mjs`, and `compiled-nat-pow-layer.mjs`, each of which has its own recursive `N` helper.
4. `zero-sub-diagnostic.mjs`: `pretty` decodes the recursive representation and needs a flat decoder.
5. The deployable copies under `checkers/mathgraph/kernel-base.mjs` and `checkers/mathgraph/kernel-semantic.mjs` must be regenerated or changed by the normal source-sync process, not allowed to drift.

Tests/helpers needing migration include `nat-pow-soundness.test.mjs`, `nat-offset-defeq.test.mjs`, `declaration-warrant.test.mjs`, and the local name helper plus explicit recursive constructions in `test.mjs` (recursor, String, Quot, and projection cases). A repository search should gate the change for remaining `JSON.stringify([...,"str"|"num",...])` constructions.

## Compatibility risks

- NDJSON names are rooted structural names, but many handwritten unit tests and direct `Kernel.run` callers use arbitrary strings such as `Ntest`, `Ntest.zero`, or `UnitLike`. Those strings are atoms under the current API, while tests construct a recursor child with `JSON.stringify([d.name,"str","rec"])`. Blindly treating an arbitrary string as flat JSON will either throw or change equality.
- Keep `appendName` dual-mode during migration: append flat components when the prefix carries the new canonical marker/shape; for an unencoded legacy atom, preserve the old append result. Alternatively migrate all direct callers to canonical `leanName` in one atomic change. The first approach protects the public string-based `Kernel.run` surface.
- A flat encoding needs an unambiguous root/version marker so an arbitrary handwritten JSON-looking string cannot be misclassified as a canonical name. Component tags also must retain the `str`/`num` distinction.
- Equality remains exact JavaScript string equality only if every producer uses the same serializer and component order. Main parser, semantic prepass, native layers, expected recursor names, and tests must switch together.
- Flattening removes exponential escaping but still copies the component prefix at each append. That is quadratic in qualified depth, though linear in the emitted flat string and tiny at the measured maximum depth of 24. Keeping component arrays internally can remove even that cost later; it is not required to capture the measured benefit.

## Small-step validation plan

1. Add shared helpers plus unit tests for root, string, numeric, quoted/backslash payloads, and structural non-collision.
2. Migrate all producers/decoders atomically while retaining legacy-atom behavior.
3. Assert unchanged verdict, reason, frontier, and fallback mode across the 190 fixtures.
4. Measure peak RSS on `init-prelude` and `grind-ring-5`; the character counts above provide the expected direction without claiming V8 heap savings in advance.
5. Only then reassess whether a packed name or expression arena is still needed.
