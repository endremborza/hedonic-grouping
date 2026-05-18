import Mathlib
import HedonicGrouping.Core

namespace HedonicGrouping.Algorithms.Irving
/-!
# Irving's stable roommates algorithm

Phase 1: proposal-rejection loop producing a reduced preference table.
Phase 2: iterated rotation elimination.

Internal reasoning is pairwise: theorems conclude `PairwiseStable`
(or negation thereof). The `CoreStable` upgrade under size-2 is performed
in `Correctness.IRV_RMP` via the `Unification` bridge.
-/

open HedonicGrouping.Core

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Reduced-table invariants -/

/-- Phase 1 duality: `first(b) = a → last(a) = b`. -/
def Phase1Duality (reduced : α → List α) : Prop :=
  ∀ a b : α, (reduced a).head? = some b →
    (reduced b).length > 0 ∧ (reduced b).getLastD b = a

/-- All reduced lists have length 1: each agent has exactly one remaining
    partner. -/
def AllSingleton (reduced : α → List α) : Prop :=
  ∀ a : α, (reduced a).length = 1

/-- Extract the matching implied by a singleton reduced table. -/
noncomputable def singletonMatching (reduced : α → List α) : Grouping α :=
  fun a => {a, ((reduced a).head?.getD a)}

/-- Total list lengths — termination measure for Phase 2. -/
noncomputable def totalLength [Fintype α] (reduced : α → List α) : ℕ :=
  Finset.univ.sum fun a => (reduced a).length

/-- Reduced list preserves original preference ordering. -/
def ReducedListCompatible (reduced : α → List α)
    (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ j k : Fin (reduced a).length,
    j < k → Ranks prof a {a, (reduced a)[j]} {a, (reduced a)[k]}

/-- `b ∈ reduced a ↔ a ∈ reduced b`. -/
def ReducedTableSymmetric (reduced : α → List α) : Prop :=
  ∀ a b : α, b ∈ reduced a ↔ a ∈ reduced b

/-- Cascade invariant: agents with singleton lists have matched partners.
    Mirrors `src/irving.py::_cascade`. After Phase 1's cascade pass and
    after each rotation elimination, if `b ∈ reduced a` and `reduced a`
    has length 1, then `reduced b` also has length 1.

    This is what guarantees Phase 2's rotation-finding iteration
    `p ↦ last(reduced (second(reduced p)))` stays inside the length-≥-2
    agents and therefore terminates with a true rotation. -/
def CascadeInvariant (reduced : α → List α) : Prop :=
  ∀ a b : α, b ∈ reduced a → (reduced a).length = 1 → (reduced b).length = 1

/-! ## Rotation machinery -/

/-- A rotation cycle: proposer-partner pairs forming a cycle of length ≥ 2. -/
structure RotationCycle (α : Type*) where
  pairs       : List (α × α)
  nonempty    : pairs ≠ []
  length_ge_2 : 2 ≤ pairs.length

omit [DecidableEq α] [Fintype α] in
lemma RotationCycle.length_pos (c : RotationCycle α) : 0 < c.pairs.length :=
  Nat.lt_of_lt_of_le (by norm_num) c.length_ge_2

/-- Cyclic successor index: `(i + 1) mod r`. -/
def nextFin {r : ℕ} (i : Fin r) (hr : 0 < r) : Fin r :=
  ⟨(i.val + 1) % r, Nat.mod_lt _ hr⟩

/-- Irving rotation on reduced preference lists.
    `qᵢ = second(pᵢ)` and `p_{i+1 mod r} = last(qᵢ)`. -/
def IsRotation (c : RotationCycle α) (reduced : α → List α) : Prop :=
  ∀ i : Fin c.pairs.length,
    let p_i := (c.pairs.get i).1
    let q_i := (c.pairs.get i).2
    let p_next := (c.pairs.get (nextFin i c.length_pos)).1
    (reduced p_i)[1]? = some q_i ∧
    (reduced q_i).getLastD q_i = p_next ∧ (reduced q_i) ≠ [] ∧
    p_i ≠ p_next

/-- Apply rotation elimination. -/
noncomputable def eliminateRotation
    (reduced : α → List α) (c : RotationCycle α) : α → List α :=
  fun a =>
    let removals := (List.finRange c.pairs.length).filterMap fun i =>
      let q_i := (c.pairs.get i).2
      let p_next := (c.pairs.get (nextFin i c.length_pos)).1
      if a = q_i then some p_next
      else if a = p_next then some q_i
      else none
    (reduced a).filter (· ∉ removals)

omit [Fintype α] in
/-- Rotations eliminate less-preferred pairs. -/
theorem rotation_eliminates_less_preferred
    (c : RotationCycle α)
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hrot : IsRotation c reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (i : Fin c.pairs.length) :
    Ranks prof (c.pairs.get i).2
      {(c.pairs.get i).2, (c.pairs.get i).1}
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} := by
  obtain ⟨hsec, hlast, hne, hneq⟩ := hrot i
  have hq_mem : (c.pairs.get i).2 ∈ reduced (c.pairs.get i).1 :=
    List.mem_of_getElem? hsec
  have hp_mem : (c.pairs.get i).1 ∈ reduced (c.pairs.get i).2 :=
    (hsym _ _).mp hq_mem
  obtain ⟨j, hj, hj_eq⟩ := List.mem_iff_getElem.mp hp_mem
  have hlen : 0 < (reduced (c.pairs.get i).2).length := List.length_pos_of_ne_nil hne
  have hk : (reduced (c.pairs.get i).2).length - 1 < (reduced (c.pairs.get i).2).length := by omega
  have hk_eq : (reduced (c.pairs.get i).2)[(reduced (c.pairs.get i).2).length - 1] =
      (c.pairs.get (nextFin i c.length_pos)).1 := by
    conv_lhs => rw [← List.getLast_eq_getElem hne]
    rw [← hlast, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some]
  have hjk : j < (reduced (c.pairs.get i).2).length - 1 := by
    rcases Nat.lt_or_ge j ((reduced (c.pairs.get i).2).length - 1) with h | h
    · exact h
    · exfalso
      have hjeq : j = (reduced (c.pairs.get i).2).length - 1 := by omega
      exact hneq (by rw [← hj_eq, ← hk_eq]; congr 1)
  rw [show (c.pairs.get i).1 = (reduced (c.pairs.get i).2)[j] from hj_eq.symm,
      show (c.pairs.get (nextFin i c.length_pos)).1 =
        (reduced (c.pairs.get i).2)[(reduced (c.pairs.get i).2).length - 1] from hk_eq.symm]
  exact hcompat _ ⟨j, hj⟩ ⟨_, hk⟩ hjk

private lemma filter_indices_ordered {α : Type*} (l : List α) (p : α → Bool)
    {j k : ℕ} (hj : j < (l.filter p).length) (hk : k < (l.filter p).length) (hjk : j < k) :
    ∃ (j' : ℕ) (_ : j' < l.length) (k' : ℕ) (_ : k' < l.length),
      j' < k' ∧ l[j'] = (l.filter p)[j] ∧ l[k'] = (l.filter p)[k] := by
  induction l generalizing j k with
  | nil => simp at hj
  | cons a t ih =>
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha] at hj hk
      simp only [List.length_cons] at hj hk ⊢
      cases j with
      | zero =>
        cases k with
        | zero => omega
        | succ k' =>
          have hk' : k' < (t.filter p).length := by omega
          have := List.filter_sublist (p := p) (l := t) |>.subset (List.getElem_mem hk')
          obtain ⟨k'', hk'', hk''_eq⟩ := List.mem_iff_getElem.mp this
          exact ⟨0, by omega, k'' + 1, by omega, by omega,
                 by simp [List.filter_cons_of_pos ha],
                 by simp [List.getElem_cons_succ, List.filter_cons_of_pos ha, hk''_eq]⟩
      | succ j' =>
        cases k with
        | zero => omega
        | succ k' =>
          have hj' : j' < (t.filter p).length := by omega
          have hk' : k' < (t.filter p).length := by omega
          obtain ⟨j'', hj'', k'', hk'', hjk'', hj''_eq, hk''_eq⟩ := ih hj' hk' (by omega)
          exact ⟨j'' + 1, by omega, k'' + 1, by omega, by omega,
                 by simp [List.getElem_cons_succ, List.filter_cons_of_pos ha, hj''_eq],
                 by simp [List.getElem_cons_succ, List.filter_cons_of_pos ha, hk''_eq]⟩
    · rw [List.filter_cons_of_neg ha] at hj hk
      simp only [List.length_cons] at ⊢
      obtain ⟨j', hj', k', hk', hjk', hj'_eq, hk'_eq⟩ := ih hj hk hjk
      exact ⟨j' + 1, by omega, k' + 1, by omega, by omega,
             by simp [List.getElem_cons_succ, List.filter_cons_of_neg ha, hj'_eq],
             by simp [List.getElem_cons_succ, List.filter_cons_of_neg ha, hk'_eq]⟩

/-- **Rotation elimination preserves reduced-table invariants.** -/
theorem rotation_elimination_preserves_invariants
    (c : RotationCycle α)
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (_hsize : SizeTwo prof)
    (hrot : IsRotation c reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced) :
    let reduced' := eliminateRotation reduced c
    ReducedTableSymmetric reduced' ∧
    ReducedListCompatible reduced' prof := by
  refine ⟨fun a b => ?_, fun a j k hjk => ?_⟩
  · simp only [eliminateRotation, List.mem_filter, decide_eq_true_eq]
    constructor <;> intro ⟨hmem, hnotrem⟩
    · refine ⟨(hsym a b).mp hmem, ?_⟩
      intro habs
      apply hnotrem
      rw [List.mem_filterMap] at habs ⊢
      obtain ⟨idx, hidx, hf⟩ := habs
      exact ⟨idx, hidx, by
        split at hf <;> [split <;> simp_all; split at hf <;> [split <;> simp_all; simp at hf]]⟩
    · refine ⟨(hsym b a).mp hmem, ?_⟩
      intro habs
      apply hnotrem
      rw [List.mem_filterMap] at habs ⊢
      obtain ⟨idx, hidx, hf⟩ := habs
      exact ⟨idx, hidx, by
        split at hf <;> [split <;> simp_all; split at hf <;> [split <;> simp_all; simp at hf]]⟩
  · obtain ⟨j', hj', k', hk', hjk', hj'_eq, hk'_eq⟩ :=
      filter_indices_ordered (reduced a) _ j.isLt k.isLt hjk
    have h := hcompat a ⟨j', hj'⟩ ⟨k', hk'⟩ hjk'
    convert h using 3
    · exact hj'_eq.symm
    · exact hk'_eq.symm

/-! ## Phase 1 — proposal-rejection loop -/

noncomputable section
open Classical

/-- Phase 1 state: reduced preference table + held proposals. -/
structure P1State (α : Type*) [DecidableEq α] where
  table : α → List α
  held : α → Option α

/-- Initialize Phase 1 from a size-2 preference profile. -/
def P1State.init (prof : PreferenceProfile α) (_hsize : SizeTwo prof) : P1State α where
  table := fun a => (prof a).filterMap fun G =>
    if _h : G.card = 2 ∧ a ∈ G then some (pairPartner a G) else none
  held := fun _ => none

/-- Agent `a` is free: unmatched and has remaining candidates. -/
def P1Free (s : P1State α) (a : α) : Prop :=
  s.held a = none ∧ (s.table a) ≠ []

/-- Phase 1 is complete: no free agent remains. -/
def P1Terminated (s : P1State α) : Prop :=
  ¬ ∃ a, P1Free s a

/-- One Phase 1 step: free agent `a` proposes to first on their list. -/
def P1State.stepWith (s : P1State α) (a b : α) : P1State α :=
  match s.held b with
  | none =>
    { table := s.table
      held := fun x => if x = b then some a else s.held x }
  | some bOld =>
    if (s.table b).findIdx (· == a) < (s.table b).findIdx (· == bOld) then
      { table := fun x =>
          if x = b then (s.table b).filter (fun y => y ≠ bOld)
          else if x = bOld then (s.table bOld).filter (fun y => y ≠ b)
          else s.table x
        held := fun x =>
          if x = b then some a
          else if x = bOld then none
          else s.held x }
    else
      { table := fun x =>
          if x = b then (s.table b).filter (fun y => y ≠ a)
          else if x = a then (s.table a).filter (fun y => y ≠ b)
          else s.table x
        held := s.held }

/-- Termination measure for Phase 1. -/
noncomputable def P1State.totalLength (s : P1State α) : ℕ :=
  Finset.univ.sum fun a => (s.table a).length

/-- **Phase 1 output.** Starting from a valid size-2 profile, the
    proposal-rejection loop (followed by the cascade pass) terminates with
    a reduced table that is symmetric, compatible, dual, cascade-closed,
    and either nowhere-empty or the instance has no pairwise-stable
    matching. -/
theorem phase1_produces_reduced_table
    (prof : PreferenceProfile α) (hsize : SizeTwo prof) (hvalid : IsValidProfile prof) :
    ∃ (reduced : α → List α),
      ReducedTableSymmetric reduced ∧
      ReducedListCompatible reduced prof ∧
      Phase1Duality reduced ∧
      CascadeInvariant reduced ∧
      (∀ a : α, (reduced a) ≠ [] ∨
        ∀ μ : Grouping α, ¬ PairwiseStable prof μ) := by
  sorry -- Proof: Run the proposal-rejection loop, then the cascade pass.
         -- Termination: totalLength strictly decreases with each rejection.
         -- Symmetry: each rejection removes both directions.
         -- Compatibility: only tail-truncation, never reordering.
         -- Duality: if first(b) = a, then a holds b, and b is last on a's list.
         -- CascadeInvariant: the cascade pass propagates forced matches —
         -- length-1 lists pair only with length-1 lists.

/-! ## Phase 2 — iterated rotation elimination -/

/-- Rotation elimination strictly decreases total list lengths. Witnessed by
    rotation position 0: `p_next = (c.pairs.get 1).1` is the last element of
    `reduced q_0`, and it is included in the removal list computed for
    agent `q_0`. So `(reduced q_0).filter` is a strict sublist of `reduced q_0`,
    and the sum over all agents drops by at least one. -/
theorem eliminateRotation_decreases_totalLength
    (reduced : α → List α)
    (c : RotationCycle α)
    (hrot : IsRotation c reduced) :
    totalLength (eliminateRotation reduced c) < totalLength reduced := by
  classical
  have h0 : 0 < c.pairs.length := c.length_pos
  obtain ⟨_, hlast, hne, _⟩ := hrot ⟨0, h0⟩
  set q : α := (c.pairs.get ⟨0, h0⟩).2 with hq_def
  set p_next : α :=
    (c.pairs.get (nextFin (⟨0, h0⟩ : Fin c.pairs.length) c.length_pos)).1 with hp_def
  have hp_mem : p_next ∈ reduced q := by
    have h := hlast
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
        Option.getD_some] at h
    rw [← h]
    exact List.getLast_mem hne
  set rem : List α := (List.finRange c.pairs.length).filterMap (fun i =>
      if q = (c.pairs.get i).2 then
        some (c.pairs.get (nextFin i c.length_pos)).1
      else if q = (c.pairs.get (nextFin i c.length_pos)).1 then
        some (c.pairs.get i).2
      else none) with hrem_def
  have hp_in_rem : p_next ∈ rem := by
    rw [hrem_def, List.mem_filterMap]
    refine ⟨⟨0, h0⟩, List.mem_finRange _, ?_⟩
    show (if q = (c.pairs.get (⟨0, h0⟩ : Fin c.pairs.length)).2 then
            some (c.pairs.get (nextFin (⟨0, h0⟩ : Fin c.pairs.length) c.length_pos)).1
          else if q = (c.pairs.get (nextFin (⟨0, h0⟩ : Fin c.pairs.length) c.length_pos)).1 then
            some (c.pairs.get (⟨0, h0⟩ : Fin c.pairs.length)).2
          else none) = some p_next
    rw [if_pos rfl]
  have heq_q : (eliminateRotation reduced c) q =
      (reduced q).filter (fun x => decide (x ∉ rem)) := rfl
  have h_strict : ((eliminateRotation reduced c) q).length < (reduced q).length := by
    rw [heq_q]
    have hsub : List.Sublist
        ((reduced q).filter (fun x => decide (x ∉ rem))) (reduced q) :=
      List.filter_sublist
    rcases lt_or_eq_of_le hsub.length_le with hlt | heq
    · exact hlt
    · exfalso
      have hfilt_eq := List.Sublist.eq_of_length hsub heq
      have hpfilt : p_next ∈ (reduced q).filter (fun x => decide (x ∉ rem)) := by
        rw [hfilt_eq]; exact hp_mem
      rw [List.mem_filter] at hpfilt
      have : p_next ∉ rem := by
        have := hpfilt.2
        simpa using this
      exact this hp_in_rem
  have h_le : ∀ a, ((eliminateRotation reduced c) a).length ≤ (reduced a).length := by
    intro a
    show ((reduced a).filter _).length ≤ _
    exact List.filter_sublist.length_le
  unfold totalLength
  exact Finset.sum_lt_sum (fun a _ => h_le a) ⟨q, Finset.mem_univ _, h_strict⟩

/-! ### Phase 2 iteration step -/

/-- Phase 2 iteration step: from `p`, follow
    `last(reduced (second(reduced p)))`. Self-loop default when
    `(reduced p).length < 2`. -/
noncomputable def phase2Step (reduced : α → List α) (p : α) : α :=
  if h : 2 ≤ (reduced p).length then
    (reduced (reduced p)[1]).getLastD (reduced p)[1]
  else
    p

omit [Fintype α] in
/-- Under `ReducedTableSymmetric + CascadeInvariant`, the Phase 2 step
    preserves `length ≥ 2`. The key well-definedness fact for
    `findRotation`'s iteration. -/
lemma phase2Step_length_ge_two
    {reduced : α → List α}
    (hsym : ReducedTableSymmetric reduced)
    (hcasc : CascadeInvariant reduced)
    {p : α} (hp : 2 ≤ (reduced p).length) :
    2 ≤ (reduced (phase2Step reduced p)).length := by
  have h1 : 1 < (reduced p).length := hp
  set q : α := (reduced p)[1] with hq_def
  have hstep : phase2Step reduced p = (reduced q).getLastD q := by
    unfold phase2Step
    rw [dif_pos hp]
  have hqp : q ∈ reduced p := List.getElem_mem h1
  have hpq : p ∈ reduced q := (hsym p q).mp hqp
  have hqne : reduced q ≠ [] := List.ne_nil_of_mem hpq
  have hqpos : 1 ≤ (reduced q).length := List.length_pos_of_ne_nil hqne
  have hqlen2 : 2 ≤ (reduced q).length := by
    by_contra h
    push_neg at h
    have hqlen1 : (reduced q).length = 1 := by omega
    have : (reduced p).length = 1 := hcasc q p hpq hqlen1
    omega
  set p' : α := (reduced q).getLast hqne with hp'_def
  have hstep_eq : phase2Step reduced p = p' := by
    rw [hstep, hp'_def, List.getLastD_eq_getLast?,
        List.getLast?_eq_some_getLast hqne, Option.getD_some]
  rw [hstep_eq]
  have hp'_mem : p' ∈ reduced q := by rw [hp'_def]; exact List.getLast_mem hqne
  have hqp' : q ∈ reduced p' := (hsym q p').mp hp'_mem
  have hp'ne : reduced p' ≠ [] := List.ne_nil_of_mem hqp'
  have hp'pos : 1 ≤ (reduced p').length := List.length_pos_of_ne_nil hp'ne
  by_contra h
  push_neg at h
  have hp'len1 : (reduced p').length = 1 := by omega
  have : (reduced q).length = 1 := hcasc p' q hqp' hp'len1
  omega

/-- Find a rotation in the reduced table. The return type packages the
    cycle with its `IsRotation` witness — the prior signature returned an
    unconstrained `RotationCycle α`, which is trivially inhabited from any
    element of `α` and so did not bind the result to be a real rotation.

    The construction (left as a sorry) iterates `phase2Step reduced` from
    `p_0 := a`; finiteness of `α` forces a cycle, which is the rotation.
    `phase2Step_length_ge_two` is the supporting lemma: each step stays
    inside `length ≥ 2`, so `(reduced p_i)[1]` is always defined. -/
noncomputable def findRotation (reduced : α → List α)
    (hdual : Phase1Duality reduced)
    (hsym : ReducedTableSymmetric reduced)
    (hcasc : CascadeInvariant reduced)
    (a : α) (ha : 2 ≤ (reduced a).length) :
    { c : RotationCycle α // IsRotation c reduced } := by
  sorry

/-- Phase 2 iteration: eliminate rotations until termination.

    Each iteration re-establishes `CascadeInvariant` after `eliminateRotation`
    by running a cascade pass (mirroring `src/irving.py::_phase2`), so the
    invariant is maintained across the recursion. -/
noncomputable def phase2
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hdual : Phase1Duality reduced)
    (hcasc : CascadeInvariant reduced) :
    (∃ (final : α → List α), AllSingleton final ∧
      ReducedTableSymmetric final ∧ ReducedListCompatible final prof) ∨
    (∃ (a : α), ∃ (final : α → List α),
      final a = [] ∧ ReducedTableSymmetric final ∧
      ReducedListCompatible final prof) := by
  sorry -- Proof: well-founded recursion on totalLength.

/-! ## Endpoint theorems -/

/-- Stable-pair invariant: if μ is pairwise-stable, then at every Phase 2
    stage, each agent's partner in μ remains on their list. -/
def StablePairInvariant (reduced : α → List α) (_prof : PreferenceProfile α)
    (μ : Grouping α) : Prop :=
  ∀ a : α, pairPartner a (μ a) ∈ reduced a

/-- Rotation elimination preserves the stable-pair invariant. -/
theorem eliminateRotation_preserves_stablePair
    (reduced : α → List α) (prof : PreferenceProfile α) (μ : Grouping α)
    (c : RotationCycle α)
    (hsize : SizeTwo prof)
    (hrot : IsRotation c reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hstable : PairwiseStable prof μ)
    (hvalid : IsValidGrouping μ)
    (hsize_μ : ∀ a : α, (μ a).card = 2)
    (hinv : StablePairInvariant reduced prof μ) :
    StablePairInvariant (eliminateRotation reduced c) prof μ := by
  sorry -- Proof: Suppose partner(μ, q_i) = p_{i+1} is eliminated at position i.
         -- Then q_i is matched to p_{i+1} in μ.
         -- The rotation says q_i prefers p_i to p_{i+1}.
         -- Trace around the cycle to derive a blocking pair — contradiction.

/-- **Singleton reduced table → pairwise-stable matching.** -/
theorem reducedTable_singleton_stable
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hsingleton : AllSingleton reduced) :
    PairwiseStable prof (singletonMatching reduced) := by
  sorry -- Proof: Singleton matching is mutual (symmetry + singleton).
         -- Suppose {a, c} blocks. Then c was eliminated from a's list by
         -- some rotation; that rotation's compatibility contradicts the
         -- assumed preference.

/-- **Empty list → no pairwise-stable matching.** -/
theorem reducedTable_empty_no_stable
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (a : α) (hempty : reduced a = []) :
    ∀ μ : Grouping α, ¬ PairwiseStable prof μ := by
  sorry -- Proof by contradiction: Suppose μ is pairwise-stable.
         -- Then StablePairInvariant holds initially and through every step.
         -- But reduced a = [], so partner(μ, a) ∉ reduced a. Contradiction.

/-! ## Main decidability theorem -/

/-- **Irving decides pairwise stability.** -/
theorem irving_decides_stability
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof) :
    (∃ μ : Grouping α, PairwiseStable prof μ) ∨
    (∀ μ : Grouping α, ¬ PairwiseStable prof μ) := by
  sorry -- Proof:
         -- 1. Run Phase 1 → obtain reduced table.
         -- 2. Run Phase 2 → either AllSingleton or some-empty.
         -- 3. AllSingleton → left (reducedTable_singleton_stable).
         -- 4. some-empty → right (reducedTable_empty_no_stable).

end

end HedonicGrouping.Algorithms.Irving
