# QCKN Lean Negative Reuse V1 — Qualified Result

Authoritative run:
https://github.com/heathsanchez/lean-kernel-arena/actions/runs/35406435819

Artifact:
`10573075153`

Artifact digest:
`sha256:b198c6a94858641b129cfb3e040d28626b7e37064e8feff6bf013fd47b6479c2`

This qualification stays strictly inside the existing trust boundary:

`diagnostic-routing-only; never changes ACCEPT/REJECT semantics`

The source bank contains eight previously retained falsified diagnostic probes
and a retained kernel snapshot with zero wrong verdicts.

Three repeated waves over those eight exact diagnostic routes gave:

- COLD diagnostic verifier calls: **24**
- WARM calls: **8**
- WARM exact refutations compiled: **8**
- future repeated calls blocked during the same run: **16**
- RESTART future proposals: **16**
- RESTART verifier calls: **0**
- ABLATION calls: **24**

So the warm pass reduced repeated diagnostic-verifier work by **66.67%**, and
after restart the exact future repeated-work reduction was **100%** for those
same fingerprints.

Controls:

- changed residual scope was **not blocked** and returned `UNKNOWN_SCOPE`;
- stale source identity was rejected;
- ablation restored the complete cold routing cost.

This does **not** claim checker-runtime speedup, does not modify Lean
ACCEPT/REJECT semantics, and does not generalize a diagnostic refutation to a
different frontier signature.
