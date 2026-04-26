import Mathlib

namespace HedonicGrouping.Core
/-!
# Hedonic Grouping — Core Definitions

Problem-agnostic types and utilities shared across every problem and
algorithm: preference profiles, groupings, validity predicates, and
size-2 pair helpers.

Bipartite structure lives in `Problems.SMP`; pairwise stability lives in
`Problems.Pairwise`; core stability and `Considerable` live in
`Problems.HCP`.
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `PreferenceProfile α` — each agent's strict ranking of admissible
    coalitions, most preferred first. -/
def PreferenceProfile (β : Type*) := β → List (Finset β)

/-- `Ranks prof a G H` — agent `a` strictly prefers `G` to `H`. -/
def Ranks (prof : PreferenceProfile α) (a : α) (G H : Finset α) : Prop :=
  ∃ i j : Fin (prof a).length, i < j ∧ (prof a)[i] = G ∧ (prof a)[j] = H

/-- `Grouping α` — assignment of each agent to its coalition. -/
def Grouping (α : Type*) := α → Finset α

/-- `a` could belong to coalition `G`. -/
def IsAdmissibleCoalition (a : α) (G : Finset α) : Prop :=
  a ∈ G

/-- Preferences are well-formed: no duplicates, each listed coalition
    contains the agent. -/
def IsValidProfile (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, (prof a).Nodup ∧ ∀ G ∈ prof a, IsAdmissibleCoalition a G

/-- Every agent belongs to their assigned coalition. -/
def IsValidGrouping (μ : Grouping α) : Prop :=
  ∀ a : α, a ∈ μ a

/-- All listed coalitions have exactly two members — the classical
    pairwise-matching regime (marriage, roommates). -/
def SizeTwo (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ G ∈ prof a, G.card = 2

/-! ### Size-2 pair utilities -/

/-- Extract the other member of a size-2 coalition containing `a`. -/
noncomputable def pairPartner (a : α) (G : Finset α) : α :=
  ((G.erase a).toList.head?.getD a)

omit [Fintype α] in
private lemma erase_nonempty_of_card_two {a : α} {G : Finset α}
    (ha : a ∈ G) (hcard : G.card = 2) : (G.erase a).Nonempty :=
  Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha, hcard]; omega)

omit [Fintype α] in
private lemma erase_toList_ne_nil {a : α} {G : Finset α}
    (ha : a ∈ G) (hcard : G.card = 2) : (G.erase a).toList ≠ [] :=
  Finset.Nonempty.toList_ne_nil (erase_nonempty_of_card_two ha hcard)

omit [Fintype α] in
lemma pairPartner_mem {a : α} {G : Finset α} (ha : a ∈ G) (hcard : G.card = 2) :
    pairPartner a G ∈ G := by
  unfold pairPartner
  have hne := erase_toList_ne_nil ha hcard
  rw [List.head?_eq_some_head hne, Option.getD_some]
  have := List.head_mem hne
  exact Finset.mem_of_mem_erase (Finset.mem_toList.mp this)

omit [Fintype α] in
lemma pairPartner_ne {a : α} {G : Finset α} (ha : a ∈ G) (hcard : G.card = 2) :
    pairPartner a G ≠ a := by
  unfold pairPartner
  have hne := erase_toList_ne_nil ha hcard
  rw [List.head?_eq_some_head hne, Option.getD_some]
  intro heq
  have := List.head_mem hne
  have hmem := Finset.mem_toList.mp this
  rw [Finset.mem_erase] at hmem
  exact hmem.1 heq

/-- Agent `a` prefers partner `b` to partner `c`. -/
def PrefersPartner (prof : PreferenceProfile α) (a b c : α) : Prop :=
  Ranks prof a {a, b} {a, c}

end HedonicGrouping.Core
