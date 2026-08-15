# RGRS Std post-gate decision table

Frozen before held-out Std timing results are observed.

Acquisition-derived observable: absent_binder_rate A(W).
Frozen threshold: tau = 0.1580774332.
Held-out Std structure: A(Std) = 0.19313465467733243.
Frozen prospective prediction: latest sokonanoda (9b4ea12) is faster than pinned sokonanoda (0fab887) on Std.

## If prediction succeeds

Primary transition: PROMOTE (experimental applicability observable), then PROJECT.

Do not retune tau. Preserve the exact rule and test it prospectively on at least one additional untouched performance corpus. Prefer a workload on the opposite side of tau if available, to test both selector branches. The next workflow must again measure structure first, freeze the predicted sign, and only then reveal timing.

The observable remains experimental until it has multiple prospective successes spanning both sides of the threshold and semantic acceptance remains unchanged.

## If prediction fails

Primary transition: REFRAME.

Do not move tau and do not replace A after inspecting only the failed timing. Treat the failure as R5 Applicability with missing structural information. Compare the already-recorded pre-outcome structural features (app density, binder density, declaration mix, export scale, dependent-binder rate) and design the smallest new prospective separator. Preserve A as a useful but insufficient observable unless evidence warrants suppression.

## In either outcome

A timing result must change solver state. No extra tuning variant is allowed unless it tests a named residual. Global expression reuse remains independently suppressed pending a new causal channel.
