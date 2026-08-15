# RGRS result: eagerness decomposition

Status: FOCUSED GATE PASSED; ESCALATE.

Run: 31893417057
Runner: GitHub ubuntu-24.04, 4 CPUs, same-runner sequential comparison.

## Arms

- P0: Arena-pinned sokonanoda 0fab887 (lazy baseline)
- P1: upstream 9b4ea12 (broad eagerness + structural irrelevance)
- P2: 9b4ea12 structural irrelevance with old lazy eval.rs and lazy arg_value restored

## Focused results

| Test | P0 pinned | P1 latest | P2 irrelevance-only | P1 vs P0 | P2 vs P0 |
|---|---:|---:|---:|---:|---:|
| cedar | 34.3 s | 30.9 s | 32.5 s | -9.9% | -5.2% |
| cslib | 34.8 s | 32.3 s | 34.8 s | -7.2% | 0.0% |
| init-prelude | 46 ms | 43 ms | 47 ms | -6.5% | +2.2% |

All nine checker/test executions matched expected semantics.

## RGRS classification

The strong hypothesis "broad eagerness is the poison and irrelevance is the useful mechanism" is REJECTED on the controlled focused gate.

Structural irrelevance alone explains part of the Cedar improvement but none of the CSLib improvement. The combined latest arm wins on all three discriminators. Therefore the prior Cedar/CSLib split cannot be attributed to broad eagerness in general from this evidence; it was likely specific to the A5/A6 intervention mix or another interaction.

Residual update:

- R5 Applicability: weakened for upstream broad eagerness on these focused tests; not eliminated globally.
- R4 Observability: remains a plausible optimization principle but is not the dominant explanation for P1's focused gain.
- R2/R3 remain open for larger-suite scaling and repeated reconstruction.

## Admission decision

P1 passes the focused semantic and resource direction gate, but is NOT yet admitted as a project architecture result. Escalate to full Mathlib and a small accept/reject semantic battery.

If P1 wins Mathlib with semantics preserved, retain it as the new upstream reference point. If it reverses badly on Mathlib, classify R5 and isolate the large-suite applicability boundary. If it fails semantic negatives, classify R9 and reject immediately.
