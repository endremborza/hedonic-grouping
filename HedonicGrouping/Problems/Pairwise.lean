import Mathlib
import HedonicGrouping.Core

namespace HedonicGrouping.Problems.Pairwise
/-!
# Pairwise stability

Stability as a pair phenomenon. Shared by SMP and RMP — both restrict to
size-2 coalitions, where every deviation is a pair. The bridge to HCP's
core stability under `SizeTwo` lives in `Unification`.
-/

open HedonicGrouping.Core

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Blocking pair: both agents strictly prefer being together to their
    current assignment. -/
def BlockingPair (prof : PreferenceProfile α) (μ : Grouping α) (a b : α) : Prop :=
  a ≠ b ∧ Ranks prof a {a, b} (μ a) ∧ Ranks prof b {a, b} (μ b)

/-- No blocking pair exists. -/
def PairwiseStable (prof : PreferenceProfile α) (μ : Grouping α) : Prop :=
  ∀ a b : α, ¬ BlockingPair prof μ a b

end HedonicGrouping.Problems.Pairwise
