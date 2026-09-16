# Task 2 report

Implemented and committed as `06c331b` (`Add production runtime and corpus qualification gate`).

## Files

- `genesis/production.mjs`: deterministic production import stack, the single capability list, and the production `checkExport` wrapper.
- `checkers/mathgraph/main.mjs`: uses the production runtime while preserving the file argument and Arena exit codes 0/1/2 (operational errors remain 3).
- `genesis/qualify-corpus.mjs`: strict-by-default manifest runner and JSON report aggregation.
- `genesis/qualify-worker.mjs`: fresh-process checker with byte/hash verification and bounded input/record/semantic resources.
- `genesis/runtime-gate.test.mjs`: process-level runtime and corpus gate regression coverage.

## Red / green

Red command:

```sh
node --test genesis/runtime-gate.test.mjs
```

It failed with `ERR_MODULE_NOT_FOUND` for `genesis/production.mjs` before implementation.

Green command:

```sh
node --test genesis/runtime-gate.test.mjs genesis/nat-pow-soundness.test.mjs
```

Result: 3 tests passed. The runtime test exercises actual `checkers/mathgraph/main.mjs` processes for good => 0, bad => 1, unsupported => 2, and checks parity with production `checkExport`. It also uses real child processes for correct aggregation, wrong and UNKNOWN strict failure, diagnostic labeling, empty manifest failure, and unsafe path failure.

`git diff --check` also passed before commit.

## CI command

```sh
node genesis/qualify-corpus.mjs
```

Defaults: `_build/tests/manifest.json`, `genesis/evidence/qualification.json`, 2,000,000 semantic budget, 60-second timeout per child, 20,000,000-byte input cap, and 400,000-record cap. `--diagnostic` collects results with a zero exit but labels the report `DIAGNOSTIC`, never `PASS`. Paths and limits can be overridden with the documented CLI flags visible in the source.

## Limitations

The focused suite uses a tiny local corpus and does not establish full Arena qualification. I did not run or overwrite the concurrently retrieved `_build/tests` corpus or alter the workflow. The default strict runner will fail on every wrong verdict, UNKNOWN/decline, crash, timeout, invalid row, hash mismatch, or byte mismatch and records every manifest row in its report.

## Review fix

Addressed the deployment/qualification mismatch in follow-up commit `bebcdf1` (`Align qualification with production limits`).

- `genesis/production.mjs` now exports the shared defaults and environment contract: 2,000,000 semantic steps, 20,000,000 input bytes, and 400,000 records. Both the packaged main and qualification worker use `productionConfig()` and the same `checkExport` path.
- Runner overrides propagate through `MATHGRAPH_SEMANTIC_BUDGET`, `MATHGRAPH_INPUT_BYTE_LIMIT`, and `MATHGRAPH_RECORD_LIMIT`; the packaged main accepts the same environment variables.
- Both file-consuming entry points use `statSync` to enforce the byte cap before `readFileSync` allocates the input.
- The regression suite now checks a valid input larger than 2 MB through both packaged main and a qualification child, and checks that a semantic budget of 1 produces UNKNOWN through both the packaged environment override and runner `--budget 1`.
- `genesis/runtime-identity.mjs` derives and hashes the complete local static import closure rooted at `production.mjs`. The qualifier captures its per-file source manifest, requires every worker hash to match, rechecks after each child, and fails if sources change. Reports also contain `runtime_revision`, `manifest_sha256`, and each corpus row's declared/verified SHA-256.

Green command after the fix:

```sh
node --test genesis/runtime-gate.test.mjs genesis/nat-pow-soundness.test.mjs
```

Result: 3 tests passed. `git diff --check` passed. A claimed full-corpus run remains intentionally deferred until the parent freezes concurrent source changes.
