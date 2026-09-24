/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniquenessProof

/-!
# Uniqueness of `K_{d+2}` at `C(d+2, 2)` edges

Connects Palomar's advertised declaration to the proof. This module contains no mathematics: it
restates the theorem Comparator checks and discharges it from the development.

The statement here must match `Challenge.lean`'s. Comparator compiles the two modules in separate
sandboxes and rejects any difference.
-/

public section

namespace EdgeThresholdUniqueness.Palomar

/-- For every natural number `d ≥ 6`, every finite simple graph with exactly
`C(d + 2, 2)` edges, with no isolated vertex, and with no unit-distance
representation in Euclidean `d`-space, is isomorphic to `K_{d+2}`. -/
theorem target :
    EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniqueness.UniqueKComplete :=
  EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniqueness.UniqueKComplete.proof

end EdgeThresholdUniqueness.Palomar
