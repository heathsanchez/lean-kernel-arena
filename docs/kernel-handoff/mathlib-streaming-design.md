# Streaming design for multi-gigabyte Lean exports

## Evidence from the current runtime

The largest local files are `perf/grind-ring-5.ndjson` (10,184,724 bytes, 199,196 records) and `init-prelude.ndjson` (3,714,854 bytes, 63,723 records). The workspace has no Mathlib/LKA large export, no `lka.py`, and no Lean project/toolchain inputs from which to build it. The repository documentation says the downloadable Arena archive excludes large tests. The local public corpus is 23 MB total; therefore a true 5.2 GB replay cannot be performed from stored files.

With semantic budget 1, after `checkExport`:

| Input | Records | RSS after check | Heap used |
|---|---:|---:|---:|
| 3.7 MB prelude | 63,723 | 118.8 MB | 30.1 MB |
| 10.2 MB grind-ring | 199,196 | 215.6 MB | 83.6 MB |

The 10.2 MB case is already about 21 times input size in RSS. Linear extrapolation exceeds 100 GB for 5.2 GB, before accounting for approximately 100 million `Map` entries.

## Current memory blockers

1. Both `checkers/mathgraph/main.mjs` and `genesis/qualify-worker.mjs` use `readFileSync`. The worker holds the file `Buffer`, converts it to a second UTF-16 string, then passes it onward.
2. `checkExport` calls `input.split(/\r?\n/)`, allocating an array with one string per record. At 100 million records this alone is infeasible.
3. Parsing retains global `Map`s for every name, level, expression, and expression depth. `exprs` and `exprDepths` duplicate the 100-million-key index overhead.
4. Expressions are expanded into nested JavaScript arrays. Even after streaming removes the source text, a multi-gigabyte export can expand far beyond the default V8 heap.
5. Every normalized declaration is retained in `decls`. `Kernel.run` then creates an environment map containing those same declaration objects. The array is only a reference duplication, but it is also the replay source for retained, stack-safe, and local-definition attempts.
6. Parser precedence matters: the entire export is parsed before any semantic verdict today. A late malformed record overrides a semantic result that an online checker might have reached earlier.
7. Attempt selection depends on global `maxExpressionDepth`, known only at EOF. Fallback replays require either retained declarations, a replayable store, or running multiple kernels in lockstep.

Flat names help name size but do not address the expression table, depth table, expanded AST, source buffering, or fallback replay.

## Minimal patch sequence

### Patch 1: streaming ingress with exact parity

Create a parser state object in `kernel-base.mjs` with synchronous methods `consumeLine(line)`, `finishParse()`, and `result()`. Move the existing per-row logic into it unchanged.

Expose two adapters:

- `checkExport(input, capabilities, budget)`: compatibility adapter using an index-based line scanner over the existing string. It must not call `split`.
- `checkExportFile(path, capabilities, budget, limits, expectedIdentity)`: asynchronous adapter using `createReadStream` plus `StringDecoder`, carrying incomplete UTF-8 and line fragments between chunks.

The file adapter must:

- `stat` and compare the manifest byte count before opening;
- enforce the byte cap on raw bytes, not JavaScript string length;
- update SHA-256 while consuming each chunk;
- enforce the record cap per nonblank line;
- accept LF and CRLF and process an unterminated final line exactly once;
- withhold the semantic result until EOF, byte count, SHA-256, header, quotient-package completion, and all parse validation have succeeded.

Update both `qualify-worker.mjs` and packaged `checkers/mathgraph/main.mjs` to call the same `checkExportFile`. Keep `runtimeIdentity()` before execution and compare it again after execution, exactly as the gate does now. Worker JSON and CLI exit mapping remain unchanged.

This patch removes the Buffer/string/split peak and is independently useful, but it is not sufficient for Mathlib.

Tests: split every fixture at every byte position for a small UTF-8/CRLF export; malformed final line; blank final line; multibyte character across chunks; byte and record caps; wrong expected size; wrong SHA; late parse error after an early semantic failure; direct-string/file status parity over the full local manifest; packaged-main/worker parity; runtime-source mismatch behavior. Add a generated 10 MB many-line fixture and assert peak RSS stays below a fixed regression threshold in a child process.

### Patch 2: parser table boundary

Introduce internal `NameStore`, `LevelStore`, and `ExprStore` interfaces with `has/get/put/clear`. Keep in-memory implementations first, so this is a behavior-preserving refactor.

Replace `exprs` plus `exprDepths` with one entry per expression containing both node and depth. A chunked dense table (for example 65,536-entry chunks with occupancy bitmaps and a sparse fallback) avoids `Map` object overhead while preserving sparse-index tests. Apply the same layout to names and levels only after measuring index density.

Explicitly clear parser-only indexes before semantic execution where their values are no longer required. This reduces execution-phase retention but not parse peak.

Tests: sparse, duplicate, out-of-order, and unresolved indices; exact `maxExpressionDepth`; memory comparison on the 199k-record fixture.

### Patch 3: incremental kernel session and replay contract

Refactor `Kernel.run` into:

- `beginRun(term, expected, parameters)`;
- `consumeDeclaration(d)` containing the current declaration loop body;
- `finishRun()` containing the final judgment and result handling.

Keep `run(..., declarations)` as a compatibility wrapper. This establishes a testable declaration-stream boundary without changing semantics.

Do not simply run all fallback kernels online: it triples semantic work and environment-map entries, and selection order depends on EOF depth. Instead define a replayable `DeclarationStore`. The in-memory implementation wraps the existing array; a later disk-backed implementation can append declarations and replay them sequentially. Parser errors remain authoritative because no verdict is returned until parsing finishes.

Tests: `run` versus session parity for every local fixture; late parser error precedence; retained-first/local-first selection; host-stack fallback metadata; budget reset and frontier parity across replay.

### Patch 4: compact/lazy expression storage, required for 5.2 GB

A streaming reader alone cannot retain 100 million nested JS-array expressions. Add a disk-backed expression store indexed by expression ID and backed by chunked 64-bit offsets into the original NDJSON or a compact binary spool. Materialize declaration roots lazily with memoization.

This still may not suffice if most Mathlib expressions remain reachable from declaration types and bodies. The durable solution is a compact numeric-node arena used directly by the kernel (tag plus integer child IDs), with declarations storing root IDs and the evaluator dereferencing through an arena interface. `Array.isArray` and positional array access are pervasive, so this is a separate measured migration, not part of the ingress patch.

A 100-million-entry 64-bit offset index is about 800 MB before occupancy/depth metadata. The current environment has about 29 GB free disk, enough for one 5.2 GB source and a compact index/spool, but the actual omitted workload is unavailable locally.

## Recommended immediate boundary

Implement Patch 1 first and merge it only after direct/file/gate parity passes. Implement the table interfaces in Patch 2 next. Do not claim Mathlib support until a compact or disk-backed expression design survives an actual omitted large export under a stated heap limit. Patch 3 can proceed independently and gives the persistent store a clean consumer boundary.
