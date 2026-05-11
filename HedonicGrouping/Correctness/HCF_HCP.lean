import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.SMP
import HedonicGrouping.Problems.RMP
import HedonicGrouping.Problems.HCP
import HedonicGrouping.Algorithms.HCF
import HedonicGrouping.Unification

namespace HedonicGrouping.Correctness.HCF_HCP
/-!
# HCF solves HCP

Existence-level unification. Each of the three problem classes embeds into
HCP, and HCF solves HCP, so HCF solves all three:

  IsSMP / IsRMP / IsHCP  ─►  ∃ μ, CoreStable prof μ

The sharper claim that HCF *computes the same matching* as GS on SMP and
Irving on RMP lives in `HCF_subsumes_{GS,IRV}.lean`.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.SMP
open HedonicGrouping.Problems.RMP
open HedonicGrouping.Problems.HCP
open HedonicGrouping.Algorithms.HCF
open HedonicGrouping.Unification

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **HCF produces a core-stable grouping for every HCP instance.** -/
theorem hcf_solves_hcp (prof : PreferenceProfile α) (h : IsHCP prof) :
    ∃ μ : Grouping α, CoreStable prof μ :=
  ⟨hcfGrouping prof, hcf_coreStable prof h⟩

/-- **HCF solves SMP**, by composition with `isSMP_to_isHCP`. -/
theorem hcf_solves_smp (prof : PreferenceProfile α) (h : IsSMP prof) :
    ∃ μ : Grouping α, CoreStable prof μ :=
  hcf_solves_hcp prof (isSMP_to_isHCP h)

/-- **HCF solves RMP**, by composition with `isRMP_to_isHCP`. The full
    decidability story for RMP (some instances have no solution) is in
    `IRV_RMP.lean`; this theorem just says when a solution exists, HCF
    finds one. -/
theorem hcf_solves_rmp (prof : PreferenceProfile α) (h : IsRMP prof) :
    ∃ μ : Grouping α, CoreStable prof μ :=
  hcf_solves_hcp prof (isRMP_to_isHCP h)

end HedonicGrouping.Correctness.HCF_HCP
