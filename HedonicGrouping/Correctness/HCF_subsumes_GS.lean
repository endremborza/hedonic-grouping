import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.SMP
import HedonicGrouping.Problems.HCP
import HedonicGrouping.Algorithms.HCF

namespace HedonicGrouping.Correctness.HCF_subsumes_GS
/-!
# HCF subsumes Gale-Shapley on SMP

Guarantee subsumption (D1): on the embedded SMP instance, HCF's own named
output carries the guarantee `gs_solves_smp` establishes for GS — it always
succeeds, and its output is core-stable. The existence half may consume
GS's own witness (`gs_solves_smp`) together with HCF completeness.

Step-by-step trajectory equivalence (HCF's run *equals* GS's run) is a
strictly stronger, unscheduled claim — future work, revisited only if a
reviewer asks.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.SMP
open HedonicGrouping.Problems.HCP
open HedonicGrouping.Algorithms.HCF

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **HCF subsumes GS**: on every SMP instance HCF succeeds and its output
    is core-stable — GS's guarantee, held by HCF's own output. -/
theorem hcf_subsumes_gs [LinearOrder α] (prof : PreferenceProfile α)
    (h : IsSMP prof) :
    ∃ g : Grouping α, hcfGrouping prof = some g ∧ CoreStable prof g := by
  sorry

end HedonicGrouping.Correctness.HCF_subsumes_GS
