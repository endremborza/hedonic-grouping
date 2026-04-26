import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.Pairwise
import HedonicGrouping.Problems.SMP
import HedonicGrouping.Problems.HCP
import HedonicGrouping.Algorithms.GaleShapley
import HedonicGrouping.Unification

namespace HedonicGrouping.Correctness.GS_SMP
/-!
# Gale-Shapley solves SMP

Lifts the algorithm-internal `gs_pairwiseStable` conclusion to the
HCP-level `CoreStable` via the size-2 bridge, and packages the existence
theorem against the `IsSMP` predicate.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.SMP
open HedonicGrouping.Problems.HCP
open HedonicGrouping.Algorithms.GaleShapley
open HedonicGrouping.Unification

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem gs_coreStable (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof) (hsize : SizeTwo prof)
    (hbip : BipartitePref bp prof) :
    CoreStable prof (gsGrouping (GSState.run bp prof (gsProposalBound bp))) :=
  (coreStable_iff_pairwiseStable prof _ hsize).mpr
    (gs_pairwiseStable bp prof hvalid hsize hbip)

/-- **GS produces a core-stable grouping for every SMP instance.** -/
theorem gs_solves_smp (prof : PreferenceProfile α) (h : IsSMP prof) :
    ∃ μ : Grouping α, CoreStable prof μ := by
  obtain ⟨hvalid, hsize, bp, hbip⟩ := h
  exact ⟨gsGrouping (GSState.run bp prof (gsProposalBound bp)),
    gs_coreStable bp prof hvalid hsize hbip⟩

end HedonicGrouping.Correctness.GS_SMP
