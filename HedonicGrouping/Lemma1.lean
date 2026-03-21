import Mathlib
import HedonicGrouping.Defs

open HedonicGrouping.Defs

variable {α : Type*} [DecidableEq α] [Fintype α]

structure BipartiteStructure (α : Type*) where
  isMen : α → Bool

def BipartiteStructure.isWomen (bp : BipartiteStructure α) (a : α) : Bool :=
  !bp.isMen a

def SizeTwo (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ G ∈ prof a, G.card = 2

def BipartitePref (bp : BipartiteStructure α) (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ G ∈ prof a, ∀ b ∈ G, ∀ c ∈ G, b ≠ c → bp.isMen b ≠ bp.isMen c

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

def GSHolds (prop : α → Option (Finset α)) (a b : α) : Prop :=
  prop b = some {a, b}

lemma considerable_eq_gsHolds
    (a b : α) (hab : a ≠ b)
    (prop : α → Option (Finset α)) :
    Considerable {a, b} a prop ↔ GSHolds prop a b := by
  unfold GSHolds
  exact considerable_iff_mutual_proposal a b hab {a, b} rfl prop

lemma lemma1_considerable_matches_gs
    (bp : BipartiteStructure α)
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hbip : BipartitePref bp prof)
    (prop : α → Option (Finset α))
    (a b : α) (hab : a ≠ b)
    (haMen : bp.isMen a = true)
    (hbWomen : bp.isMen b = false) :
    Considerable {a, b} a prop ↔ GSHolds prop a b := by
  exact considerable_eq_gsHolds a b hab prop
