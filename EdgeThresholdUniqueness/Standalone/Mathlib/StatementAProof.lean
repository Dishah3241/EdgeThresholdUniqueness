/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import EdgeThresholdUniqueness.Standalone.Mathlib.StatementA

import EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniquenessProof

/-!
# Proofs of statement A

Statement A and the inline statement have the same bodies, so each companion is the corresponding
inline proof.
-/

public section

open EdgeThresholdUniqueness.Standalone.Mathlib

namespace EdgeThresholdUniqueness.StatementA

theorem UnitDistanceRepresentable.separating.proof : UnitDistanceRepresentable.separating :=
  InlineEdgeThresholdUniqueness.UnitDistanceRepresentable.separating.proof

theorem UniqueKComplete.proof : UniqueKComplete :=
  InlineEdgeThresholdUniqueness.UniqueKComplete.proof

theorem UniqueKComplete.witness.proof : UniqueKComplete.witness :=
  InlineEdgeThresholdUniqueness.UniqueKComplete.witness.proof

theorem UniqueKComplete.dropHd.proof : UniqueKComplete.dropHd :=
  InlineEdgeThresholdUniqueness.UniqueKComplete.dropHd.proof

theorem UniqueKComplete.dropHcard.proof : UniqueKComplete.dropHcard :=
  InlineEdgeThresholdUniqueness.UniqueKComplete.dropHcard.proof

theorem UniqueKComplete.dropHdeg.proof : UniqueKComplete.dropHdeg :=
  InlineEdgeThresholdUniqueness.UniqueKComplete.dropHdeg.proof

theorem UniqueKComplete.dropHrep.proof : UniqueKComplete.dropHrep :=
  InlineEdgeThresholdUniqueness.UniqueKComplete.dropHrep.proof

end EdgeThresholdUniqueness.StatementA
