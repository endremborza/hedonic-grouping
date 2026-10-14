import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.RMP
import HedonicGrouping.Problems.HCP
import HedonicGrouping.Algorithms.HCF

namespace HedonicGrouping.Correctness.HCF_subsumes_IRV
/-!
# HCF subsumes Irving on RMP

Guarantee subsumption (D1): on the embedded RMP instance, HCF's own named
output carries the guarantee `irving_decides_rmp` establishes for Irving —
it decides solvability. Either HCF returns a core-stable grouping, or it
returns `none` and no genuine pair matching is core-stable. Negative
conclusions quantify over `IsPairMatching` (bare `CoreStable` is vacuously
satisfiable under size-2 profiles).

Step-by-step trajectory equivalence with Irving's run is a strictly
stronger, unscheduled claim — future work, revisited only if a reviewer
asks.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.RMP
open HedonicGrouping.Problems.HCP
open HedonicGrouping.Algorithms.HCF

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **HCF subsumes Irving**: HCF decides RMP solvability — a core-stable
    output, or `none` with no core-stable genuine pair matching. -/
theorem hcf_subsumes_irv [LinearOrder α] (prof : PreferenceProfile α)
    (h : IsRMP prof) :
    (∃ g : Grouping α, hcfGrouping prof = some g ∧ CoreStable prof g) ∨
    (hcfGrouping prof = none ∧
      ∀ μ : Grouping α, IsPairMatching prof μ → ¬ CoreStable prof μ) := by
  sorry

end HedonicGrouping.Correctness.HCF_subsumes_IRV
