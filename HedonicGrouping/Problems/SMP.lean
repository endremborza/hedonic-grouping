import Mathlib
import HedonicGrouping.Core

namespace HedonicGrouping.Problems.SMP
/-!
# Stable Marriage Problem

Bipartite size-2 matching with strict preferences. Solved by Gale-Shapley.
The solution concept is `PairwiseStable` (equivalently `CoreStable` under
size-2 — see `Unification`).
-/

open HedonicGrouping.Core

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Partition of agents into two sides; `isMen a` holds iff `a` is on the
    "men" side. -/
structure BipartiteStructure (α : Type*) where
  isMen : α → Prop

/-- Every listed coalition is cross-side: in any size-2 pair the two members
    sit on opposite sides (exactly one is a man). -/
def BipartitePref (bp : BipartiteStructure α) (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ G ∈ prof a, ∀ b ∈ G, ∀ c ∈ G, b ≠ c → (bp.isMen b ↔ ¬ bp.isMen c)

/-- SMP instance: valid, size-2, bipartite for some partition. -/
def IsSMP (prof : PreferenceProfile α) : Prop :=
  IsValidProfile prof ∧ SizeTwo prof ∧
    ∃ bp : BipartiteStructure α, BipartitePref bp prof

end HedonicGrouping.Problems.SMP
