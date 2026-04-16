import Mathlib
import HedonicGrouping.Defs

namespace HedonicGrouping.Stability

open HedonicGrouping.Defs
open HedonicGrouping.Irving
open HedonicGrouping.GaleShapley

/-!
# Stability Theorems — GS, Irving, and Hedonic Equivalence (Paper §5)

Bridges the hedonic framework to classical stability theory.

## Key results

### Proven
- `blocking_coalition_sizeTwo`: under size-2 preferences, blocking coalitions are pairs
- `coreStable_iff_pairwiseStable`: CoreStable ↔ PairwiseStable under size-2
- `hedonic_phase1_eq_gs` / `considerable_size2_iff`: considerable collapses on pairs

### Delegated to algorithm files
- `gs_stable_matching_exists`: via GaleShapley.gs_stable_matching_exists
- `irving_decides_stability`: via Irving.irving_decides_stability
- `reducedTable_singleton_stable`: via Irving.reducedTable_singleton_stable
- `reducedTable_empty_no_stable`: via Irving.reducedTable_empty_no_stable
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Hedonic ↔ GS correspondence -/

/-- Under bipartite size-2 preferences, the hedonic algorithm's Phase 1
    (Simplified Reduction) reduces to Gale-Shapley. -/
theorem hedonic_phase1_eq_gs
    (prop : α → Option (Finset α))
    (a b : α) (hab : a ≠ b) :
    Considerable {a, b} a prop ↔ prop b = some {a, b} := by
  exact considerable_iff_mutual_proposal a b hab {a, b} rfl prop

/-- Under size-2 preferences, `Considerable` on `{a, b}` reduces to:
    `b` proposes `{a, b}`. -/
theorem considerable_size2_iff
    (prop : α → Option (Finset α))
    (a b : α) (hab : a ≠ b) :
    Considerable {a, b} a prop ↔ prop b = some {a, b} := by
  exact considerable_iff_mutual_proposal a b hab {a, b} rfl prop

/-! ## Main existence and decidability theorems

These delegate to the algorithm files where the full proofs live. -/

/-- **Gale-Shapley existence theorem.** Under bipartite size-2 preferences,
    a core-stable grouping always exists. Delegates to GaleShapley.lean. -/
theorem gs_exists
    (bp : BipartiteStructure α)
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof)
    (hbip : BipartitePref bp prof) :
    ∃ μ : Grouping α, CoreStable prof μ :=
  HedonicGrouping.GaleShapley.gs_stable_matching_exists bp prof hvalid hsize hbip

/-- **Irving's algorithm decides stability.** Under size-2 preferences,
    either a core-stable grouping exists or none does.
    Delegates to Irving.lean. -/
theorem irving_decides
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof) :
    (∃ μ : Grouping α, CoreStable prof μ) ∨
    (∀ μ : Grouping α, ¬ CoreStable prof μ) :=
  HedonicGrouping.Irving.irving_decides_stability prof hsize hvalid

end HedonicGrouping.Stability
