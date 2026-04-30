import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.SMP
import HedonicGrouping.Problems.HCP

namespace HedonicGrouping.Unification
/-!
# Unification layer

Bridges between the three problem formulations and the three algorithms.

## Current contents (Phase 1)

- Size-2 bridge: every blocking coalition is a pair, so `CoreStable` and
  `PairwiseStable` coincide under `SizeTwo`.
- GS ↔ HCP bridge: under size-2, `Considerable {a, b} a prop` collapses to
  `prop b = some {a, b}` — the GS proposal-acceptance predicate.

## Later phases

- Phase 4: `IsSMP prof → IsHCP prof`, `IsRMP prof → IsHCP prof` (problem
  embeddings).
- Phase 6: trajectory bridges (HCF on SMP ≡ GS, HCF on RMP ≡ IRV).
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.HCP

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Size-2 bridges -/

/-- Under size-2 preferences, any blocking coalition has exactly 2 members. -/
lemma blocking_coalition_sizeTwo
    (prof : PreferenceProfile α) (μ : Grouping α) (S : Finset α)
    (hsize : SizeTwo prof)
    (hblock : BlockingCoalition prof μ S) :
    S.card = 2 := by
  obtain ⟨_, hpref⟩ := hblock
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨i, _, _, hi, _⟩ := hpref a ha
  exact hsize a S (hi ▸ List.getElem_mem (by exact i.isLt))

/-- **Core stability equals pairwise stability under size-2 preferences.** -/
theorem coreStable_iff_pairwiseStable
    (prof : PreferenceProfile α) (μ : Grouping α)
    (hsize : SizeTwo prof) :
    CoreStable prof μ ↔ PairwiseStable prof μ := by
  constructor
  · intro hcore a b hbp
    obtain ⟨hab, ha_ranks, hb_ranks⟩ := hbp
    apply hcore {a, b}
    refine ⟨by simp [Finset.card_pair hab], fun x hx => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    cases hx with
    | inl h => subst h; exact ha_ranks
    | inr h => subst h; exact hb_ranks
  · intro hpair S hblock
    have hcard := blocking_coalition_sizeTwo prof μ S hsize hblock
    obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hcard
    subst hS
    exact hpair a b ⟨hab, hblock.2 a (Finset.mem_insert_self a {b}),
      hblock.2 b (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))⟩

/-! ## Considerable ↔ GS proposal-acceptance -/

omit [Fintype α] in
/-- Under size-2, `Considerable G a prop` reduces to a single proposal
    check: the other member proposes the pair. -/
lemma considerable_iff_mutual_proposal
    (a b : α) (hab : a ≠ b)
    (G : Finset α) (hG : G = {a, b})
    (prop : α → Option (Finset α)) :
    Considerable G a prop ↔ prop b = some G := by
  constructor
  · intro hcons
    apply hcons b
    · rw [hG]; simp
    · exact hab.symm
  · intro hb x hxG hxa
    have : x = b := by
      rw [hG] at hxG
      simp [Finset.mem_insert, Finset.mem_singleton] at hxG
      rcases hxG with rfl | rfl
      · exact absurd rfl hxa
      · rfl
    rw [this]
    exact hb

/-- GS proposal-acceptance: `b` proposes `{a, b}`. -/
def GSHolds (prop : α → Option (Finset α)) (a b : α) : Prop :=
  prop b = some {a, b}

omit [Fintype α] in
/-- **Considerable matches GS proposal-acceptance on pairs.** -/
lemma considerable_matches_gs
    (a b : α) (hab : a ≠ b)
    (prop : α → Option (Finset α)) :
    Considerable {a, b} a prop ↔ GSHolds prop a b := by
  unfold GSHolds
  exact considerable_iff_mutual_proposal a b hab {a, b} rfl prop

end HedonicGrouping.Unification
