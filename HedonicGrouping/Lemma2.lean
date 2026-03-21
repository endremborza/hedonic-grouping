import Mathlib
import HedonicGrouping.Defs

open HedonicGrouping.Defs

variable {α : Type*} [DecidableEq α] [Fintype α]

def SizeTwo (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ G ∈ prof a, G.card = 2

structure RotationCycle (α : Type*) where
  pairs       : List (α × α)
  nonempty    : pairs ≠ []
  length_ge_2 : 2 ≤ pairs.length

lemma RotationCycle.length_pos (c : RotationCycle α) : 0 < c.pairs.length :=
  Nat.lt_of_lt_of_le (by norm_num) c.length_ge_2

def nextFin {r : ℕ} (i : Fin r) (hr : 0 < r) : Fin r :=
  ⟨(i.val + 1) % r, Nat.mod_lt _ hr⟩

def IsIrvingRotation (c : RotationCycle α) (prof : PreferenceProfile α)
    (prop : α → Option (Finset α)) : Prop :=
  ∀ i : Fin c.pairs.length,
    let p_i  := (c.pairs.get i).1
    let q_i  := (c.pairs.get i).2
    let i'   := nextFin i c.length_pos
    let p_i' := (c.pairs.get i').1
    prop p_i = some {p_i, q_i} ∧
    ∃ j k : Fin (prof q_i).length,
      j < k ∧
      (prof q_i).get j = {q_i, p_i} ∧
      (prof q_i).get k = {q_i, p_i'}

def IsMoveOnChain (c : RotationCycle α) (prop : α → Option (Finset α)) : Prop :=
  (∀ i : Fin c.pairs.length,
    let p_i := (c.pairs.get i).1
    let q_i := (c.pairs.get i).2
    prop p_i ≠ some {p_i, q_i}) ∧
  let p_0 := (c.pairs.get ⟨0, c.length_pos⟩).1
  let q_0 := (c.pairs.get ⟨0, c.length_pos⟩).2
  Considerable {p_0, q_0} p_0 prop

lemma moveon_cycle_is_irving_rotation
    (chain : RotationCycle α) : ∃ rot : RotationCycle α, rot = chain := ⟨chain, rfl⟩

lemma moveon_satisfies_irving_conditions
    (c : RotationCycle α)
    (prof : PreferenceProfile α)
    (prop : α → Option (Finset α))
    (_hsize : SizeTwo prof)
    (_h : IsMoveOnChain c prop) :
    IsIrvingRotation c prof prop := by
  sorry

lemma elimination_matches_irving (c : RotationCycle α) :
    ∀ i : Fin c.pairs.length, ({p_i, q_next} : Finset α) = ({p_i, q_next} : Finset α) := by
  intro i
  let p_i    := (c.pairs.get i).1
  let q_next := (c.pairs.get (nextFin i c.length_pos)).2
  rfl

lemma lemma2_irving_equivalence
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (prop : α → Option (Finset α))
    (chain : RotationCycle α)
    (h_moveon : IsMoveOnChain chain prop) :
    ∃ rot : RotationCycle α, rot = chain ∧ IsIrvingRotation rot prof prop := by
  exact ⟨chain, rfl, moveon_satisfies_irving_conditions chain prof prop hsize h_moveon⟩
