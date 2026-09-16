# LocalDefKernel-first ablation at 2M

Source snapshot: `950a789` (`Route deep expressions through continuation evaluator`). The production checkout was not edited. In an isolated copy, `checkExport` ran `LocalDefKernel` as the first and only semantic attempt. Each fixture had a 60-second process timeout.

| Fixture | Status | Reason | Frontier | Steps | Constructed | Wall time |
|---|---|---|---|---:|---:|---:|
| `fueled-chain.ndjson` | UNKNOWN | budget-exhausted | `funext` | 2,000,001 | 21,295 | 1,089 ms |
| `magma-list-pair-n7.ndjson` | UNKNOWN | budget-exhausted | `Nat.succ_le_succ` | 2,000,001 | 195,509 | 2,595 ms |

Command shape:

```sh
timeout 60s node <one-off LocalDefKernel-first runner> <fixture> 2000000
```

Both commands exited normally (`exit=0`); neither hit the 60-second process timeout. Existing local-definition continuation alone does not qualify either fixture. It moves both failures substantially earlier in declaration order than the retained path (`chain6_datF` and `countermodel`, respectively), so LocalDefKernel-first is not a viable general repair for these cases.
