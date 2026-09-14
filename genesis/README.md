# Kernel genesis: short, falsifiable growth loops

Experimental new implementation, written independently of the existing Rust checkers.
The empty capability set returns UNKNOWN for every input. A developmental harness
tries supplied rule implementations, retains coverage gains, replays prior results,
ablates additions and attempts deletion after every growth step.

## Run

Requires Node.js 22; the independent corpus gate also uses Python 3 and internet.

```sh
node genesis/test.mjs
node genesis/arena.mjs
node genesis/check.mjs --state genesis/evidence/retained.json < tests/sparse-name-index.ndjson
```

Without --state, check.mjs runs the empty present. Exit codes are 0 ACCEPT,
1 REJECT, 2 UNKNOWN, 3 usage failure. Unexpected programming errors are failures,
not proof rejections. The core accepts a deliberately bounded monomorphic fragment:
numeric and symbolic universes (at most eight parameters per equality), dependent binders, application, beta/let reduction, and validated
axioms, definitions, opaque theorem declarations and proof irrelevance. Eta,
inductives, recursors, quotient rules and primitive literal extensions remain explicit
frontiers. Failed structural conversion returns UNKNOWN
unless distinct numeric sorts supply a decisive mismatch.

This is not a complete or formally verified Lean kernel and has no Mathlib speed claim.

## What grows, and what is supplied

The retained capability set starts empty. The host interpreter, typed-term input
schema, budgets, test evaluator and candidate rule implementations are supplied.
The current search enumerates single additions, then pairs if singles cannot
progress; it is finite capability selection, not autonomous program synthesis.
No test names, expected verdicts or corpus hashes are available to the checker.

The smallest initial sort-only procedure can be retained, then dissolved when the
general sort capability plus binder checking subsumes it. This is removal from
the retained capability set; the candidate library remains available to the
development process. Producing source code that physically omits all unretained
procedures is a further compiler step, not claimed here.

## Immediate feedback

1. The seed must return UNKNOWN on all 16 training obligations.
2. Each candidate gets the small corpus immediately; any wrong verdict vetoes it.
3. Every accepted addition must increase coverage and preserve established verdicts.
4. Removing the addition must restore the previous coverage.
5. Each deletion must preserve all coverage with no increased counted work.
6. 96 separate generated cases test new universes and capture-sensitive binders.
7. Mutation, resource exhaustion, unsupported syntax, malformed axioms and process
   exit-code controls run before any external download.
8. Existing repository Arena fixtures check sparse and out-of-order references.
9. The published small Arena corpus runs after the above, stopping immediately
   on the first wrong verdict and saving the exact counterexample.

The 16-case corpus participates in selection; the 96-case set is a held-out
parameter expansion, not an independently authored theorem corpus. The downloaded
Arena tests are independent integration evidence. Their exact SHA-256 and all
declines are recorded. The corpus is pinned to SHA-256
85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118;
a changed download fails instead of silently changing the comparison.

## Cost and trust

Steps count explicitly instrumented core operations; they are not retired machine
instructions. Constructed-node counts and elapsed milliseconds are separate.
Parsing reports record counts and is included in end-to-end elapsed time; JSON
decoding, host GC, context-array copies and toolchain costs are not captured by the
step counter. No total-cost or universal optimality claim follows from these tests.

Finite tests and source review do not prove soundness. Every extension needs a
semantic argument and adversarial evidence before use as a trusted kernel. The
checker never treats an unsupported feature or exhausted budget as mathematical
invalidity. Inputs and traversals are bounded to keep this first feedback loop short.

## Evidence

The workflow prints every transition immediately and saves events.jsonl,
retained.json, summary.json, arena.json and frontier.json. Local V8 execution during development
showed coverage 0 -> 2 -> 5 -> 8 -> 12 -> 16 and one redundant capability removed.
GitHub Actions is the reproducible check of the committed files and CLI.

## Earlier workflow failure

Run 34874829913, job 104079318875 reached `test -s /tmp/mathlib-warm.out`
after the checker command returned zero under `set -e`. It failed because the
output was empty, not because the checker returned rejection. The short harness
contains a silent-success process control to prevent that gate error. The earlier
expensive workflow is not rerun by this branch.

## Second increment: symbolic universes

The first run's 151 universe-frontier declines motivated this extension. Level
comparison splits each parameter into zero or positive, represents a positive
parameter as q+1, and compares max-of-affine forms on every branch. This is exact
within the resource bound; numeric sampling is only an independent test, never
the reason to accept equality. The module includes universe parameter scope and
constant instantiation/arity validation. Ten laws and 196 independent expression
pairs precede the protected replay and pinned Arena corpus. Removing the universe
capability restores UNKNOWN on the polymorphic probe. This is still a supplied
candidate implementation admitted by tests, not generated mathematical rules.


## Third increment: theorem declarations

The post-universe Arena residual separated seven theorem-declaration cases from the
149 inductive-frontier cases. This increment therefore does not jump to inductives.
It adds the smaller independently ablatable theorem capability: the declared type
must itself inhabit Prop, the proof term must check against that type, earlier
theorems may be referenced, self/forward references are rejected because installation
still happens only after validation, and theorem bodies remain opaque to conversion.
Hand-written format-3.1 exports exercise both acceptance and rejection before the
protected replay and pinned Arena corpus. Removing the capability restores UNKNOWN.


## Fourth increment: proof irrelevance

The theorem increment closed six of seven theorem-frontier cases and exposed the
seventh as a different obstruction: conversion under a binder. The isolated Arena
case requires two applications of the same function to different data arguments to
be definitionally equal because both results are proofs of the same proposition.
The new capability recognizes exactly that condition during recursive conversion.
Ablation restores conversion-frontier, while a negative control with ordinary data
terms remains UNKNOWN rather than being collapsed. No inductive capability is used.


## Fifth increment: the inductive envelope

Once proof irrelevance dissolved, all 149 remaining Arena cases stopped at the
first inductive record. A diagnostic pass over all 149 first records found a
strictly smaller certified layer before inductive semantics: complete groups
have one recursor per inductive type, every recursor has one minor premise per
constructor, and constructor identities are unique within the group.

This capability checks only those envelope invariants. Violations are REJECT;
a structurally valid inductive is still UNKNOWN with
`inductive-semantics-frontier`. It does not yet claim constructor typing,
positivity, elimination, recursor typing, projection rules, eta, or recursor
reduction. Ablation restores `declaration-frontier:inductive`.
