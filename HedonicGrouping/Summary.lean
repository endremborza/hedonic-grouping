import HedonicGrouping.Correctness.GS_SMP
import HedonicGrouping.Correctness.IRV_RMP
import HedonicGrouping.Correctness.HCF_HCP

/-!
# Top-level re-exports

One-stop import point for the headline results. No proofs, no
definitions — just re-exports.
-/

export HedonicGrouping.Correctness.GS_SMP (gs_solves_smp)
export HedonicGrouping.Correctness.IRV_RMP (irving_decides_rmp)
export HedonicGrouping.Correctness.HCF_HCP (hcf_solves_hcp hcf_solves_smp hcf_solves_rmp)
