# RGRS held-out Std prediction

Status: frozen before any pinned-vs-latest Std timing run.

## Frozen selector

Discovery statistic:

A(W) = absent_binders / all_binders

Threshold frozen previously:

τ = 0.1580774332

Decision rule:

- if A(W) >= τ, predict latest sokonanoda (9b4ea12) faster than pinned sokonanoda (0fab887)
- if A(W) < τ, predict pinned faster

## Held-out workload

Std structure-only run 31908746030 measured:

A(Std) = 0.19313465467733243

This is above τ.

## Frozen prospective prediction

LATEST FASTER THAN PINNED ON STD.

No Std pinned/latest performance result was consulted before this prediction was committed.

The next admissible action is a same-runner PGO comparison using checker definitions sokonanoda and sokonanoda-latest on the same Std export. The sign of the timing difference is the deciding outcome; no threshold revision is allowed from this held-out result.
