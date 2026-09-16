# Arena qualification implementation plan

Goal: qualify the independent kernel for full Arena correctness and competitive Mathlib instruction count. No PR or upstream submission is authorized.

Method: question each shortcut's warrant; remove incorrect or unnecessary work; make the smallest justified repair; replay protected consequences; measure instructions; automate promotion only after a trustworthy gate.

Base: upstream 05901df511b4352a1a18ece31dd62a2a1496090d. Local checkout is a selected-file snapshot retrieved through the authenticated GitHub connector, because direct git transport is unavailable. Remote changes must preserve the complete upstream tree.

1. Reproduce the Nat power truncation with real Kernel.whnf, including 2^128, and assert that every returned literal equals independent BigInt exponentiation. Repair the return guard so an interrupted calculation falls back. Test zero, one, machine boundary, large exponents, and malformed instance shapes. Record red/green evidence.
2. Read current giant evidence, import only independently justified layers into a single production module, and add a packaged-executable gate. Reject false proofs, accept valid proofs, and report UNKNOWN without calling it a correctness pass.
3. Capture each giant's exact residual and dependency context. Compare a minimal fixture with the pinned official kernel. Make one semantic change at a time and keep counterexamples in the regression corpus. Do not infer that closure of one declaration completes a stream.
4. Replace whole-input materialization with streaming before claiming Mathlib support. Measure full-corpus correctness and total instructions against current Arena contenders on the same exports; use ablations to remove non-contributing machinery.
5. Review changes independently, commit source and evidence on mda-arena-qualification-v1, and leave the PR unopened. Do not claim first place without a full-corpus measured result.

Task 1 implementation: in genesis/compiled-nat-pow-layer.mjs require n === 0n as well as a representable out before returning the optimized literal. Fallback is the existing whnf0 call. New regression: genesis/nat-pow-soundness.test.mjs, using real kernel methods, with node --test. Later semantic repairs are conditioned on exact residual evidence, not predetermined.
