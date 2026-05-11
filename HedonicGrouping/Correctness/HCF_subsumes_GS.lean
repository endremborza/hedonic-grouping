import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.SMP
import HedonicGrouping.Algorithms.GaleShapley
import HedonicGrouping.Algorithms.HCF

namespace HedonicGrouping.Correctness.HCF_subsumes_GS
/-!
# HCF subsumes Gale-Shapley on SMP

Sharper than `hcf_solves_smp`: on a bipartite size-2 instance, HCF computes
the same matching as GS. Not needed for the existence-level unification
(see `HCF_HCP.lean`), but useful for the trajectory-equivalence claim in
the paper.

The proof strategy (not yet executed): show that under bipartite size-2,
the iterative HCF `step` reduces to a single GS-style proposal, and the
final fixpoints coincide.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.SMP
open HedonicGrouping.Algorithms.GaleShapley
open HedonicGrouping.Algorithms.HCF

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **HCF's output equals GS's output on every SMP instance.** -/
theorem hcfGrouping_eq_gsGrouping_on_SMP
    (prof : PreferenceProfile α) (bp : BipartiteStructure α)
    (_hvalid : IsValidProfile prof) (_hsize : SizeTwo prof)
    (_hbip : BipartitePref bp prof) :
    hcfGrouping prof = gsGrouping (GSState.run bp prof (gsProposalBound α)) := by
  sorry

end HedonicGrouping.Correctness.HCF_subsumes_GS
