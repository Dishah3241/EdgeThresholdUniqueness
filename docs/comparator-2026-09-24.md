# Comparator run, 2026-09-24

Comparator checks that `Solution.lean` proves exactly the statement in `Challenge.lean`, with only the
permitted axioms. It then replays the proof through two independent kernels.

- **Tree:** commit `5d4621b`. `GraphDimension` is a git dependency pinned to
  `103e26bc705a61f93ef7985c74498668cbdf7e01`. Lean and Mathlib `v4.35.0-rc2`.
- **`comparator.json`:**
  - target `EdgeThresholdUniqueness.Palomar.target`: `UniqueKComplete`: for `d ≥ 6`, the only graph with `C(d + 2, 2)` edges, no isolated vertex and no representation in `ℝᵈ` is `K_{d+2}`
  - permitted axioms `propext`, `Quot.sound`, `Classical.choice`
  - `enable_nanoda: true`
- **Sandbox:** none. `lake comparator` requires `bwrap`, which needs Linux, so this run checks the
  mathematics, not isolation. Palomar and the `Palomar preflight` workflow run it sandboxed.

## Result

```text
Building Challenge … Build completed successfully (2428 jobs).
Exporting … EdgeThresholdUniqueness.Palomar.target … from Challenge
Building Solution … Build completed successfully (3415 jobs).
Exporting … EdgeThresholdUniqueness.Palomar.target … from Solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

## Command

```sh
PATH="$HOME/src/nanoda_lib/target/release:$PATH" lake comparator --config comparator.json --inadvisably-no-sandbox
```
