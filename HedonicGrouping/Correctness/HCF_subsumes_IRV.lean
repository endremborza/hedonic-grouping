import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.RMP
import HedonicGrouping.Algorithms.Irving
import HedonicGrouping.Algorithms.HCF

namespace HedonicGrouping.Correctness.HCF_subsumes_IRV
/-!
# HCF subsumes Irving on RMP

Sharper than `hcf_solves_rmp`: on a size-2 instance, HCF either produces
the same matching as Irving (when Irving succeeds) or also fails (when
Irving certifies no stable matching exists). Not needed for the
existence-level unification (see `HCF_HCP.lean`).

Two statements because Irving is a decision procedure that can fail
"correctly" (no stable matching exists); HCF on the same instance must
agree on the outcome.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.RMP
open HedonicGrouping.Algorithms.Irving
open HedonicGrouping.Algorithms.HCF

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **HCF and Irving agree on whether a stable matching exists.** -/
theorem hcf_irving_agree_on_solvability
    (prof : PreferenceProfile α)
    (_hvalid : IsValidProfile prof) (_hsize : SizeTwo prof) :
    (∃ μ : Grouping α, PairwiseStable prof μ) ↔
      PairwiseStable prof (hcfGrouping prof) := by
  sorry

end HedonicGrouping.Correctness.HCF_subsumes_IRV
