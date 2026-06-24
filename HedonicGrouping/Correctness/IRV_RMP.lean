import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.RMP
import HedonicGrouping.Problems.HCP
import HedonicGrouping.Algorithms.Irving
import HedonicGrouping.Unification

namespace HedonicGrouping.Correctness.IRV_RMP
/-!
# Irving decides RMP

Lifts the algorithm-internal `PairwiseStable` disjunction to an HCP-level
`CoreStable` disjunction via the size-2 bridge.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.RMP
open HedonicGrouping.Problems.HCP
open HedonicGrouping.Algorithms.Irving
open HedonicGrouping.Unification

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **Irving decides core-stability for every RMP instance.** The
    negative branch quantifies over genuine matchings (`IsPairMatching`);
    bare `CoreStable` is vacuously satisfiable on size-2 profiles, e.g.
    by all-singleton groupings. -/
theorem irving_decides_rmp (prof : PreferenceProfile α) (h : IsRMP prof) :
    (∃ μ : Grouping α, CoreStable prof μ) ∨
    (∀ μ : Grouping α, IsPairMatching prof μ → ¬ CoreStable prof μ) := by
  obtain ⟨hvalid, hsize⟩ := h
  rcases irving_decides_stability prof hsize hvalid with ⟨μ, hμ⟩ | hno
  · exact Or.inl ⟨μ, (coreStable_iff_pairwiseStable prof μ hsize).mpr hμ⟩
  · exact Or.inr fun μ hmatch hcore =>
      hno μ hmatch ((coreStable_iff_pairwiseStable prof μ hsize).mp hcore)

end HedonicGrouping.Correctness.IRV_RMP
