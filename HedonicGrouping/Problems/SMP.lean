import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.Pairwise

namespace HedonicGrouping.Problems.SMP
/-!
# Stable Marriage Problem

Bipartite size-2 matching with strict preferences. Solved by Gale-Shapley.
The solution concept is `PairwiseStable` (equivalently `CoreStable` under
size-2 — see `Unification`).
-/

open HedonicGrouping.Core

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Partition of agents into two sides. -/
structure BipartiteStructure (α : Type*) where
  isMen : α → Bool

def BipartiteStructure.isWomen (bp : BipartiteStructure α) (a : α) : Bool :=
  !bp.isMen a

/-- Every listed coalition is cross-side: in any size-2 pair, one member
    from each side. -/
def BipartitePref (bp : BipartiteStructure α) (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ G ∈ prof a, ∀ b ∈ G, ∀ c ∈ G, b ≠ c → bp.isMen b ≠ bp.isMen c

/-- SMP instance: valid, size-2, bipartite for some partition. -/
def IsSMP (prof : PreferenceProfile α) : Prop :=
  IsValidProfile prof ∧ SizeTwo prof ∧
    ∃ bp : BipartiteStructure α, BipartitePref bp prof

end HedonicGrouping.Problems.SMP
