# RGRS held-out applicability precommit

Discovery workloads and observed static absent-binder rates:
- Cedar: 0.2558725195 (latest faster)
- init-prelude: 0.2440998902 (latest faster)
- CSLib: 0.1678025490 (latest faster)
- Mathlib: 0.1483523174 (latest slower)

The discovery separator is the midpoint between the weakest known winner (CSLib) and the known loser (Mathlib):

`tau = (0.16780254902206945 + 0.1483523173944631) / 2 = 0.15807743320826628`

Frozen prediction rule for held-out workloads:
- if `absent_binder_rate >= 0.15807743320826628`, predict latest `9b4ea12` faster than pinned `0fab887`;
- otherwise predict pinned faster than latest.

Protocol:
1. Select a held-out Arena module not used in deriving this rule and do not inspect its pinned/latest timing result.
2. Build/export it and compute `absent_binder_rate` using the already-frozen `export_structure_probe.py`.
3. Record the prediction implied by the rule in a commit before running either checker on that workload.
4. Only then run pinned and latest under the same PGO runner and semantic gate.
5. A correct sign prediction is one held-out confirmation, not a universal law; a wrong sign rejects this scalar rule as sufficient.

No threshold changes are permitted after the held-out structure is observed.