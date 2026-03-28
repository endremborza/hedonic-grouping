import Mathlib
import HedonicGrouping.Defs

namespace HedonicGrouping.GaleShapley

open HedonicGrouping.Defs

/-!
# Gale-Shapley — Definitions and Correspondence Proof (Paper §5, Lemma 1)

Defines the bipartite structure and GS "holds" relation, then proves that
the hedonic grouping algorithm's "considerable" condition reduces to GS's
mutual proposal on size-2 pairs.

**Claim:** Under bipartite, size-2 preferences, considerable = GS holds.
The universal quantifier in `Considerable` has only one witness on a pair
`{a, b}`, so it collapses to a single check on `prop b`.

## Key results

- `considerable_iff_mutual_proposal`: size-2 collapse of `Considerable`
- `considerable_eq_gsHolds`: considerable = `GSHolds`
- `lemma1_considerable_matches_gs`: main statement with full bipartite hypotheses
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A bipartite partition of agents into two sides (Gale-Shapley roles). -/
structure BipartiteStructure (α : Type*) where
  isMen : α → Bool

def BipartiteStructure.isWomen (bp : BipartiteStructure α) (a : α) : Bool :=
  !bp.isMen a

/-- Every preferred coalition is cross-partition: in any size-2 pair,
    one member is from each side. -/
def BipartitePref (bp : BipartiteStructure α) (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ G ∈ prof a, ∀ b ∈ G, ∀ c ∈ G, b ≠ c → bp.isMen b ≠ bp.isMen c

omit [Fintype α] in
/-- For a size-2 pair `{a, b}`, considerable for `a` reduces to: `b` proposes `{a, b}`.
    The universal quantifier in `Considerable` has only one witness (`b`), so the
    condition collapses to a single equality check on `prop b`. -/
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

/-- Gale-Shapley "holds" relation: `b` is currently proposing the pair `{a, b}`. -/
def GSHolds (prop : α → Option (Finset α)) (a b : α) : Prop :=
  prop b = some {a, b}

omit [Fintype α] in
/-- The considerable condition on `{a, b}` is precisely `GSHolds` — linking
    the hedonic grouping algorithm's acceptance test to Gale-Shapley's proposal
    acceptance. This is the core of Lemma 1. -/
lemma considerable_eq_gsHolds
    (a b : α) (hab : a ≠ b)
    (prop : α → Option (Finset α)) :
    Considerable {a, b} a prop ↔ GSHolds prop a b := by
  unfold GSHolds
  exact considerable_iff_mutual_proposal a b hab {a, b} rfl prop

omit [Fintype α] in
/-- **Lemma 1.** Under bipartite structure and size-2 preferences, the hedonic
    grouping algorithm's considerable condition equals Gale-Shapley's proposal
    acceptance (`GSHolds`). The bipartite and size-2 hypotheses are carried for
    context; the proof depends only on the pair structure `{a, b}`. -/
lemma lemma1_considerable_matches_gs
    (_bp : BipartiteStructure α)
    (prof : PreferenceProfile α)
    (_hsize : SizeTwo prof)
    (_hbip : BipartitePref _bp prof)
    (prop : α → Option (Finset α))
    (a b : α) (hab : a ≠ b)
    (_haMen : _bp.isMen a = true)
    (_hbWomen : _bp.isMen b = false) :
    Considerable {a, b} a prop ↔ GSHolds prop a b := by
  exact considerable_eq_gsHolds a b hab prop

end HedonicGrouping.GaleShapley
