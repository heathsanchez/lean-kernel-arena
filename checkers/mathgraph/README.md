# MathGraph Lean checker

Production Arena package derived from the qualified `genesis` kernel on
`mda-kernel-genesis-v1`.

The runtime is intentionally self-contained: no developmental search, RealityGraph
controller, network access, corpus hashes, expected verdicts, or test names are on
the checking path.

Exit codes:

- 0: accepted
- 1: rejected
- 2: declined / unsupported / resource frontier
- 3: checker/runtime error

The capability basis is frozen in `main.mjs`. Unsupported syntax and exhausted
resources remain declines rather than being converted into mathematical rejection.
