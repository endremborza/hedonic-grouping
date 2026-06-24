import Mathlib

namespace HedonicGrouping.Core
/-!
# Hedonic Grouping — Core Definitions

Problem-agnostic types and utilities shared across every problem and
algorithm: preference profiles, groupings, validity predicates, and
size-2 pair helpers.

Bipartite structure lives in `Problems.SMP`; core stability and `Considerable` live in
`Problems.HCP`.
-/

variable {α : Type*}

/-- `PreferenceProfile α` — each agent's strict ranking of admissible
    coalitions, most preferred first. -/
def PreferenceProfile (β : Type*) := β → List (Finset β)

/-- `Ranks prof a G H` — agent `a` strictly prefers `G` to `H`. -/
def Ranks (prof : PreferenceProfile α) (a : α) (G H : Finset α) : Prop :=
  ∃ i j : Fin (prof a).length, i < j ∧ (prof a)[i] = G ∧ (prof a)[j] = H

/-- `Grouping α` — assignment of each agent to its coalition. -/
def Grouping (α : Type*) := α → Finset α

/-- Preferences are well-formed: no duplicates, each listed coalition
    contains the agent. -/
def IsValidProfile (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, (prof a).Nodup ∧ ∀ G ∈ prof a, a ∈ G

lemma Ranks.trans {prof : PreferenceProfile α} (hvalid : IsValidProfile prof) {a : α}
    {G H K : Finset α} (h1 : Ranks prof a G H) (h2 : Ranks prof a H K) :
    Ranks prof a G K := by
  obtain ⟨i, j, hij, hGi, hHj⟩ := h1
  obtain ⟨i', j', hi'j', hHi', hKj'⟩ := h2
  refine ⟨i, j', ?_, hGi, hKj'⟩
  have hnodup := (hvalid a).1
  have heq : (prof a)[j.val] = (prof a)[i'.val] := hHj.trans hHi'.symm
  have hjj' : j.val = i'.val := (List.Nodup.getElem_inj_iff hnodup).mp heq
  have h1' : i.val < j.val := hij
  have h2' : i'.val < j'.val := hi'j'
  show i.val < j'.val
  omega

lemma Ranks.irrefl {prof : PreferenceProfile α} (hvalid : IsValidProfile prof)
    {a : α} {G : Finset α} : ¬ Ranks prof a G G := by
  rintro ⟨i, j, hij, hGi, hGj⟩
  have hnodup := (hvalid a).1
  have heq : (prof a)[i.val] = (prof a)[j.val] := hGi.trans hGj.symm
  have hij_eq : i.val = j.val := (List.Nodup.getElem_inj_iff hnodup).mp heq
  have hij_lt : i.val < j.val := hij
  omega

/-- The preferred side of a `Ranks` comparison is listed in the profile. -/
lemma Ranks.fst_mem {prof : PreferenceProfile α} {a : α} {G H : Finset α}
    (h : Ranks prof a G H) : G ∈ prof a := by
  obtain ⟨_, _, _, hGi, _⟩ := h
  rw [← hGi]; exact List.getElem_mem _

variable [DecidableEq α] in
/-- On a duplicate-free list, `Ranks` is reflected by list position: the
    preferred coalition has the smaller `idxOf`. -/
lemma Ranks.idxOf_lt {prof : PreferenceProfile α} {a : α} {G H : Finset α}
    (h : Ranks prof a G H) (hnodup : (prof a).Nodup) :
    (prof a).idxOf G < (prof a).idxOf H := by
  obtain ⟨i, j, hij, hGi, hHj⟩ := h
  have hi' : (prof a)[i.val]'i.isLt = G := hGi
  have hj' : (prof a)[j.val]'j.isLt = H := hHj
  have hG : (prof a).idxOf G = i.val := by
    have h1 := List.Nodup.idxOf_getElem hnodup i.val i.isLt
    rw [hi'] at h1; exact h1
  have hH : (prof a).idxOf H = j.val := by
    have h1 := List.Nodup.idxOf_getElem hnodup j.val j.isLt
    rw [hj'] at h1; exact h1
  rw [hG, hH]; exact hij

/-- Every agent belongs to their assigned coalition. -/
def IsValidGrouping (μ : Grouping α) : Prop :=
  ∀ a : α, a ∈ μ a

/-- All listed coalitions have exactly two members — the classical
    pairwise-matching regime (marriage, roommates). -/
def SizeTwo (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ G ∈ prof a, G.card = 2

/-! ### Size-2 pair utilities -/

variable [DecidableEq α]

/-- Extract the other member of a size-2 coalition containing `a`. -/
noncomputable def pairPartner (a : α) (G : Finset α) : α :=
  ((G.erase a).toList.head?.getD a)

private lemma erase_nonempty_of_card_two {a : α} {G : Finset α}
    (ha : a ∈ G) (hcard : G.card = 2) : (G.erase a).Nonempty :=
  Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha, hcard]; omega)

private lemma erase_toList_ne_nil {a : α} {G : Finset α}
    (ha : a ∈ G) (hcard : G.card = 2) : (G.erase a).toList ≠ [] :=
  Finset.Nonempty.toList_ne_nil (erase_nonempty_of_card_two ha hcard)

/-- On a size-2 coalition the `head?.getD` defaulting never fires:
    `pairPartner` is exactly the head of the (nonempty) erased list. -/
lemma pairPartner_eq_head {a : α} {G : Finset α} (ha : a ∈ G) (hcard : G.card = 2) :
    pairPartner a G = (G.erase a).toList.head (erase_toList_ne_nil ha hcard) := by
  unfold pairPartner
  rw [List.head?_eq_some_head (erase_toList_ne_nil ha hcard), Option.getD_some]

lemma pairPartner_mem {a : α} {G : Finset α} (ha : a ∈ G) (hcard : G.card = 2) :
    pairPartner a G ∈ G := by
  rw [pairPartner_eq_head ha hcard]
  exact Finset.mem_of_mem_erase (Finset.mem_toList.mp (List.head_mem _))

lemma pairPartner_ne {a : α} {G : Finset α} (ha : a ∈ G) (hcard : G.card = 2) :
    pairPartner a G ≠ a := by
  rw [pairPartner_eq_head ha hcard]
  intro heq
  have hmem := Finset.mem_toList.mp (List.head_mem (erase_toList_ne_nil ha hcard))
  rw [Finset.mem_erase] at hmem
  exact hmem.1 heq

/-- In a two-element coalition, the partner of `x` is the unique other
    member: any `y ∈ G` with `y ≠ x` equals `pairPartner x G`. -/
lemma pairPartner_eq_of_card_two {G : Finset α} (hcard : G.card = 2)
    {x y : α} (hx : x ∈ G) (hy : y ∈ G) (hne : y ≠ x) :
    pairPartner x G = y := by
  have hmem := pairPartner_mem hx hcard
  have hne' := pairPartner_ne hx hcard
  have hcard1 : (G.erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hx, hcard]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard1
  have hpz : pairPartner x G ∈ G.erase x := Finset.mem_erase.mpr ⟨hne', hmem⟩
  have hyz : y ∈ G.erase x := Finset.mem_erase.mpr ⟨hne, hy⟩
  rw [hz, Finset.mem_singleton] at hpz hyz
  rw [hpz, hyz]

/-- Agent `a` prefers partner `b` to partner `c`. -/
def PrefersPartner (prof : PreferenceProfile α) (a b c : α) : Prop :=
  Ranks prof a {a, b} {a, c}

/-!
# Pairwise stability

Stability as a pair phenomenon. Shared by SMP and RMP — both restrict to
size-2 coalitions, where every deviation is a pair. The bridge to HCP's
core stability under `SizeTwo` lives in `Unification`.
-/

/-- Blocking pair: both agents strictly prefer being together to their
    current assignment. -/
def BlockingPair (prof : PreferenceProfile α) (μ : Grouping α) (a b : α) : Prop :=
  a ≠ b ∧ Ranks prof a {a, b} (μ a) ∧ Ranks prof b {a, b} (μ b)

/-- No blocking pair exists. -/
def PairwiseStable (prof : PreferenceProfile α) (μ : Grouping α) : Prop :=
  ∀ a b : α, ¬ BlockingPair prof μ a b

/-- A genuine pairwise matching: every agent's coalition is one of its
    ranked pairs, and partners agree on their shared pair. `PairwiseStable`
    alone is vacuously satisfiable — `Ranks` only compares listed
    coalitions, and a `SizeTwo` profile lists no singletons, so e.g. the
    all-singletons grouping admits no blocking pair. Negative stability
    results therefore quantify over `IsPairMatching` groupings. -/
def IsPairMatching (prof : PreferenceProfile α) (μ : Grouping α) : Prop :=
  ∀ a : α, μ a ∈ prof a ∧ μ (pairPartner a (μ a)) = μ a


end HedonicGrouping.Core
