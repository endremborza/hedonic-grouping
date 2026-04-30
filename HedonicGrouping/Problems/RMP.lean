import Mathlib
import HedonicGrouping.Core

namespace HedonicGrouping.Problems.RMP
/-!
# Stable Roommates Problem

Size-2 matching with strict preferences, no bipartite restriction. Decided
by Irving — may or may not admit a stable matching. Bipartite instances
are included as a strict subset (they are also `IsSMP`).
-/

open HedonicGrouping.Core

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- RMP instance: valid and size-2. -/
def IsRMP (prof : PreferenceProfile α) : Prop :=
  IsValidProfile prof ∧ SizeTwo prof

end HedonicGrouping.Problems.RMP
