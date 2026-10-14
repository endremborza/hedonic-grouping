import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.SMP
import HedonicGrouping.Problems.RMP
import HedonicGrouping.Problems.HCP
import HedonicGrouping.Algorithms.HCF
import HedonicGrouping.Unification

namespace HedonicGrouping.Correctness.HCF_HCP
/-!
# HCF solves HCP — partial correctness

Each of the three problem classes embeds into HCP, and any grouping HCF
returns on an HCP instance is core-stable, so HCF is sound on all three:

  IsSMP / IsRMP / IsHCP  ─►  hcfGrouping prof = some g → CoreStable prof g

Completeness (`some` on every solvable instance) and the guarantee-level
subsumption of GS/Irving live in `HCF_subsumes_{GS,IRV}.lean`.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.SMP
open HedonicGrouping.Problems.RMP
open HedonicGrouping.Problems.HCP
open HedonicGrouping.Algorithms.HCF
open HedonicGrouping.Unification

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **HCF is sound on HCP**: whatever it returns is core-stable. -/
theorem hcf_solves_hcp [LinearOrder α] (prof : PreferenceProfile α)
    (h : IsHCP prof) {g : Grouping α} (hsome : hcfGrouping prof = some g) :
    CoreStable prof g :=
  hcf_coreStable prof h hsome

/-- **HCF is sound on SMP**, by composition with `isSMP_to_isHCP`. -/
theorem hcf_solves_smp [LinearOrder α] (prof : PreferenceProfile α)
    (h : IsSMP prof) {g : Grouping α} (hsome : hcfGrouping prof = some g) :
    CoreStable prof g :=
  hcf_solves_hcp prof (isSMP_to_isHCP h) hsome

/-- **HCF is sound on RMP**, by composition with `isRMP_to_isHCP`. The
    decides-shape guarantee (mirroring `irving_decides_rmp`) is
    `hcf_subsumes_irv`. -/
theorem hcf_solves_rmp [LinearOrder α] (prof : PreferenceProfile α)
    (h : IsRMP prof) {g : Grouping α} (hsome : hcfGrouping prof = some g) :
    CoreStable prof g :=
  hcf_solves_hcp prof (isRMP_to_isHCP h) hsome

end HedonicGrouping.Correctness.HCF_HCP
