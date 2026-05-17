import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.SMP

namespace HedonicGrouping.Algorithms.GaleShapley
/-!
# Gale-Shapley algorithm

Deferred acceptance over a bipartite size-2 instance. Produces a
`PairwiseStable` grouping; the `CoreStable` upgrade under size-2 lives
in `Correctness.GS_SMP`.

## Structure
1. Self-contained `GSState`, init, predicates.
2. Max-preferred candidate chooser via `List.idxOf`.
3. `stepWith`, `step`, `run`, termination within `|α|²` steps.
4. Three invariants — `Engagement`, `ProposalDownward`, `ReceiverDominates` —
   preserved by `step`, witnessing pairwise stability at the terminal state.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.SMP

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable section
open Classical

/-- GS state. `proposing a = some b` records the current match; `proposed`
    is the history of advocacies. -/
structure GSState (α : Type*) where
  proposing : α → Option α
  proposed  : α → α → Prop

/-- Initial state: everyone unmatched, no advocacies. -/
def GSState.init : GSState α where
  proposing := fun _ => none
  proposed  := fun _ _ => False

/-! ### Proposal-count termination machinery -/

noncomputable def GSState.proposedSet (s : GSState α) : Finset (α × α) := by
  classical
  exact Finset.univ.filter fun p => s.proposed p.1 p.2

noncomputable def GSState.proposedCount (s : GSState α) : ℕ := s.proposedSet.card

lemma GSState.mem_proposedSet (s : GSState α) (p : α × α) :
    p ∈ s.proposedSet ↔ s.proposed p.1 p.2 := by
  classical
  simp [GSState.proposedSet]

lemma GSState.proposedCount_init : (GSState.init : GSState α).proposedCount = 0 := by
  classical
  simp [GSState.proposedCount, GSState.proposedSet, GSState.init]

lemma GSState.proposedCount_le_card (s : GSState α) :
    s.proposedCount ≤ Fintype.card α * Fintype.card α := by
  classical
  unfold GSState.proposedCount GSState.proposedSet
  calc (Finset.univ.filter fun p : α × α => s.proposed p.1 p.2).card
      ≤ (Finset.univ : Finset (α × α)).card := Finset.card_filter_le _ _
    _ = Fintype.card (α × α) := Finset.card_univ
    _ = Fintype.card α * Fintype.card α := Fintype.card_prod _ _

/-- Monotone-bounded termination meta-lemma. -/
theorem gs_terminates_within
    (step : GSState α → GSState α) (Term : GSState α → Prop)
    (hfix : ∀ s, Term s → step s = s)
    (hgrow : ∀ s, ¬ Term s → (step s).proposedCount > s.proposedCount)
    (init : GSState α) :
    Term ((step^[Fintype.card α * Fintype.card α]) init) := by
  classical
  set N := Fintype.card α * Fintype.card α with hN_def
  by_contra hN
  have allFalse : ∀ k ≤ N, ¬ Term ((step^[k]) init) := by
    intro k hk hT
    have prop : ∀ m, Term ((step^[k + m]) init) := by
      intro m
      induction m with
      | zero => simpa using hT
      | succ m ih =>
        have hiter : (step^[k + (m + 1)]) init = step ((step^[k + m]) init) := by
          rw [show k + (m + 1) = (k + m) + 1 from rfl, Function.iterate_succ_apply']
        rw [hiter, hfix _ ih]
        exact ih
    have hN' := prop (N - k)
    rw [show k + (N - k) = N from by omega] at hN'
    exact hN hN'
  have growChain : ∀ n ≤ N,
      ((step^[n + 1]) init).proposedCount ≥ init.proposedCount + (n + 1) := by
    intro n hn
    induction n with
    | zero =>
      have h0 := hgrow init (allFalse 0 (by omega))
      have hiter : (step^[1]) init = step init := by
        rw [Function.iterate_one]
      rw [hiter]; omega
    | succ n ih =>
      have hn' : n ≤ N := by omega
      have hih := ih hn'
      have hnT : ¬ Term ((step^[n + 1]) init) := allFalse (n + 1) (by omega)
      have hg := hgrow _ hnT
      have hiter : (step^[n + 2]) init = step ((step^[n + 1]) init) := by
        rw [show n + 2 = (n + 1) + 1 from rfl, Function.iterate_succ_apply']
      rw [hiter]; omega
  have h1 := growChain N (le_refl _)
  have h2 := GSState.proposedCount_le_card ((step^[N + 1]) init)
  have h3 : init.proposedCount ≥ 0 := Nat.zero_le _
  omega

/-! ### Free-man predicate and candidates -/

/-- Agent `m` is a free proposer with remaining candidates. -/
def GSFree (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m : α) : Prop :=
  bp.isMen m = true ∧
  s.proposing m = none ∧
  ∃ w, bp.isMen w = false ∧ {m, w} ∈ prof m ∧ ¬ s.proposed m w

/-- No free proposer with remaining candidates. -/
def GSTerminated (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ¬ ∃ m, GSFree bp prof s m

/-- The set of receivers that `m` can still propose to. -/
def candidateReceivers (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m : α) : Finset α :=
  Finset.univ.filter fun w =>
    bp.isMen w = false ∧ {m, w} ∈ prof m ∧ ¬ s.proposed m w

lemma mem_candidateReceivers
    {bp : BipartiteStructure α} {prof : PreferenceProfile α}
    {s : GSState α} {m w : α} :
    w ∈ candidateReceivers bp prof s m ↔
      bp.isMen w = false ∧ {m, w} ∈ prof m ∧ ¬ s.proposed m w := by
  simp [candidateReceivers]

/-! ### Max-preferred candidate -/

/-- Among `cands`, pick the one whose coalition `{m, w}` appears earliest in
    `m`'s preference list. Unranked coalitions score as `(prof m).length`; in
    practice the caller restricts `cands` to listed receivers. -/
noncomputable def chooseMaxCandidate (prof : PreferenceProfile α) (m : α)
    (cands : Finset α) (h : cands.Nonempty) : α :=
  (cands.exists_min_image (fun w => (prof m).idxOf {m, w}) h).choose

lemma chooseMaxCandidate_mem (prof : PreferenceProfile α) (m : α)
    (cands : Finset α) (h : cands.Nonempty) :
    chooseMaxCandidate prof m cands h ∈ cands := by
  unfold chooseMaxCandidate
  exact ((cands.exists_min_image (fun w => (prof m).idxOf {m, w}) h).choose_spec).1

lemma chooseMaxCandidate_min (prof : PreferenceProfile α) (m : α)
    (cands : Finset α) (h : cands.Nonempty) {w : α} (hw : w ∈ cands) :
    (prof m).idxOf {m, chooseMaxCandidate prof m cands h} ≤ (prof m).idxOf {m, w} := by
  unfold chooseMaxCandidate
  exact ((cands.exists_min_image (fun w => (prof m).idxOf {m, w}) h).choose_spec).2 w hw

/-- No candidate is strictly preferred over the chosen one. -/
lemma chooseMaxCandidate_no_better (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof) (m : α) (cands : Finset α) (h : cands.Nonempty) :
    ∀ w' ∈ cands, ¬ PrefersPartner prof m w' (chooseMaxCandidate prof m cands h) := by
  classical
  intro w' hw' hpref
  obtain ⟨i, j, hij, hi, hj⟩ := hpref
  have hnodup := (hvalid m).1
  have hi' : (prof m)[i.val]'i.isLt = {m, w'} := hi
  have hj' : (prof m)[j.val]'j.isLt = {m, chooseMaxCandidate prof m cands h} := hj
  have hi_idx : (prof m).idxOf {m, w'} = i.val := by
    have h1 := List.Nodup.idxOf_getElem hnodup i.val i.isLt
    rw [hi'] at h1
    exact h1
  have hj_idx :
      (prof m).idxOf {m, chooseMaxCandidate prof m cands h} = j.val := by
    have h1 := List.Nodup.idxOf_getElem hnodup j.val j.isLt
    rw [hj'] at h1
    exact h1
  have hmin := chooseMaxCandidate_min prof m cands h hw'
  rw [hj_idx, hi_idx] at hmin
  have hij' : i.val < j.val := hij
  omega

/-! ### Step, run, grouping -/

/-- One proposal: `m` proposes to `w`. -/
def GSState.stepWith (prof : PreferenceProfile α) (s : GSState α) (m w : α) : GSState α :=
  let proposed' := fun m' w' => s.proposed m' w' ∨ (m' = m ∧ w' = w)
  match s.proposing w with
  | none =>
    if {m, w} ∈ prof w then
      { proposing := fun a =>
          if a = m then some w
          else if a = w then some m
          else s.proposing a
        proposed := proposed' }
    else
      { proposing := s.proposing
        proposed := proposed' }
  | some mOld =>
    if ∃ i j : Fin (prof w).length,
        (prof w)[i] = {w, m} ∧ (prof w)[j] = {w, mOld} ∧ i < j then
      { proposing := fun a =>
          if a = m then some w
          else if a = w then some m
          else if a = mOld then none
          else s.proposing a
        proposed := proposed' }
    else
      { proposing := s.proposing
        proposed := proposed' }

/-- Choose a free man and propose to his max-preferred remaining candidate. -/
def GSState.step (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : GSState α :=
  if h : ∃ m, GSFree bp prof s m then
    let m := Classical.choose h
    let candidates := candidateReceivers bp prof s m
    if hc : candidates.Nonempty then
      GSState.stepWith prof s m (chooseMaxCandidate prof m candidates hc)
    else s
  else s

def GSState.run (bp : BipartiteStructure α) (prof : PreferenceProfile α) :
    ℕ → GSState α
  | 0 => GSState.init
  | n + 1 => (GSState.run bp prof n).step bp prof

def gsProposalBound (α : Type*) [Fintype α] : ℕ :=
  Fintype.card α * Fintype.card α

def gsGrouping (s : GSState α) : Grouping α :=
  fun a => match s.proposing a with
    | some b => {a, b}
    | none => {a}

/-! ### Termination -/

lemma stepWith_proposed (prof : PreferenceProfile α) (s : GSState α) (m w : α) :
    (GSState.stepWith prof s m w).proposed =
      fun m' w' => s.proposed m' w' ∨ (m' = m ∧ w' = w) := by
  cases hw : s.proposing w with
  | none => simp [GSState.stepWith, hw]; split_ifs <;> rfl
  | some mOld => simp [GSState.stepWith, hw]; split_ifs <;> rfl

/-! ### stepWith branch computations -/

lemma stepWith_proposing_none_accept
    (prof : PreferenceProfile α) (s : GSState α) (m w : α)
    (hpw : s.proposing w = none) (hwacc : ({m, w} : Finset α) ∈ prof w) :
    (GSState.stepWith prof s m w).proposing =
      fun a => if a = m then some w else if a = w then some m else s.proposing a := by
  show (GSState.stepWith prof s m w).proposing = _
  unfold GSState.stepWith
  rw [hpw]; simp [hwacc]

lemma stepWith_proposing_none_reject
    (prof : PreferenceProfile α) (s : GSState α) (m w : α)
    (hpw : s.proposing w = none) (hwacc : ({m, w} : Finset α) ∉ prof w) :
    (GSState.stepWith prof s m w).proposing = s.proposing := by
  show (GSState.stepWith prof s m w).proposing = _
  unfold GSState.stepWith
  rw [hpw]; simp [hwacc]

lemma stepWith_proposing_some_swap
    (prof : PreferenceProfile α) (s : GSState α) (m w mOld : α)
    (hpw : s.proposing w = some mOld)
    (hpref : ∃ i j : Fin (prof w).length,
        (prof w)[i] = {w, m} ∧ (prof w)[j] = {w, mOld} ∧ i < j) :
    (GSState.stepWith prof s m w).proposing =
      fun a => if a = m then some w
               else if a = w then some m
               else if a = mOld then none
               else s.proposing a := by
  show (GSState.stepWith prof s m w).proposing = _
  unfold GSState.stepWith
  simp only [hpw]
  rw [if_pos hpref]

lemma stepWith_proposing_some_keep
    (prof : PreferenceProfile α) (s : GSState α) (m w mOld : α)
    (hpw : s.proposing w = some mOld)
    (hpref : ¬ ∃ i j : Fin (prof w).length,
        (prof w)[i] = {w, m} ∧ (prof w)[j] = {w, mOld} ∧ i < j) :
    (GSState.stepWith prof s m w).proposing = s.proposing := by
  show (GSState.stepWith prof s m w).proposing = _
  unfold GSState.stepWith
  simp only [hpw]
  rw [if_neg hpref]

lemma proposedSet_stepWith (prof : PreferenceProfile α) (s : GSState α) (m w : α) :
    (GSState.stepWith prof s m w).proposedSet =
      insert (m, w) s.proposedSet := by
  ext ⟨m', w'⟩
  simp [GSState.proposedSet, stepWith_proposed, or_comm]

lemma proposedCount_stepWith (prof : PreferenceProfile α) (s : GSState α) (m w : α)
    (hnew : ¬ s.proposed m w) :
    (GSState.stepWith prof s m w).proposedCount = s.proposedCount + 1 := by
  have hnotmem : (m, w) ∉ s.proposedSet := by
    simp [GSState.proposedSet, hnew]
  simp [GSState.proposedCount, proposedSet_stepWith,
        Finset.card_insert_of_notMem hnotmem]

lemma proposedCount_step_of_free
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (hfree : ∃ m, GSFree bp prof s m) :
    (s.step bp prof).proposedCount = s.proposedCount + 1 := by
  simp only [GSState.step, hfree, dite_true]
  set m := Classical.choose hfree with hm_def
  set candidates := candidateReceivers bp prof s m with hcands_def
  have hcands : candidates.Nonempty := by
    obtain ⟨_, _, w, hw, hacc, hnprop⟩ := Classical.choose_spec hfree
    exact ⟨w, by
      simp only [hcands_def, mem_candidateReceivers]
      exact ⟨hw, hacc, hnprop⟩⟩
  simp only [hcands, dite_true]
  have hnew : ¬ s.proposed m (chooseMaxCandidate prof m candidates hcands) := by
    have hmem := chooseMaxCandidate_mem prof m candidates hcands
    rw [mem_candidateReceivers] at hmem
    exact hmem.2.2
  exact proposedCount_stepWith prof s m _ hnew

lemma step_eq_of_terminated (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (h : GSTerminated bp prof s) :
    s.step bp prof = s := by
  simp only [GSState.step, dif_neg h]

lemma run_eq_iterate (bp : BipartiteStructure α) (prof : PreferenceProfile α) (n : ℕ) :
    GSState.run bp prof n =
      ((fun s => s.step bp prof)^[n]) GSState.init := by
  induction n with
  | zero => simp [GSState.run]
  | succ n ih =>
    rw [GSState.run, ih, Function.iterate_succ_apply']

/-- GS terminates within `|α|²` steps. -/
theorem gs_terminates (bp : BipartiteStructure α) (prof : PreferenceProfile α) :
    GSTerminated bp prof (GSState.run bp prof (gsProposalBound α)) := by
  rw [run_eq_iterate]
  refine gs_terminates_within
    (step := fun s => s.step bp prof)
    (Term := fun s => GSTerminated bp prof s)
    (fun s h => step_eq_of_terminated bp prof s h)
    (fun s h => ?_)
    GSState.init
  show (s.step bp prof).proposedCount > s.proposedCount
  have := proposedCount_step_of_free bp prof s (Classical.not_not.mp h)
  omega

/-! ## Invariants -/

/-- Structural facts about engagements: mutual, bipartite, acceptable, and
    (for the proposer = man side) recorded in the proposed history. -/
def Engagement (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ a b, s.proposing a = some b →
    s.proposing b = some a ∧
    bp.isMen a ≠ bp.isMen b ∧
    {a, b} ∈ prof a ∧
    (bp.isMen a = true → s.proposed a b)

/-- Men propose in preference order: if `m` proposed to `w` then he also
    proposed to every more-preferred receiver (woman). -/
def ProposalDownward (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ m w w', bp.isMen m = true → bp.isMen w' = false → s.proposed m w →
    PrefersPartner prof m w' w → s.proposed m w'

/-- For every past proposer `m` of receiver `w`, `w`'s current state
    dominates `m`: either `m` is unacceptable to `w`, or `w` is engaged
    to someone she weakly prefers. -/
def ReceiverDominates (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ w m, bp.isMen w = false → s.proposed m w →
    {w, m} ∉ prof w ∨
    ∃ mCur, s.proposing w = some mCur ∧
      (mCur = m ∨ PrefersPartner prof w mCur m)

/-- All three invariants. -/
def GSInvariants (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  Engagement bp prof s ∧ ProposalDownward bp prof s ∧ ReceiverDominates bp prof s

/-! ### Initial state -/

lemma initial_engagement (bp : BipartiteStructure α) (prof : PreferenceProfile α) :
    Engagement bp prof (GSState.init : GSState α) := by
  intro a b h
  simp [GSState.init] at h

lemma initial_proposalDownward (bp : BipartiteStructure α) (prof : PreferenceProfile α) :
    ProposalDownward bp prof (GSState.init : GSState α) := by
  intro m w w' _ _ h _
  simp [GSState.init] at h

lemma initial_receiverDominates (bp : BipartiteStructure α) (prof : PreferenceProfile α) :
    ReceiverDominates bp prof (GSState.init : GSState α) := by
  intro w m _ h
  simp [GSState.init] at h

lemma initial_invariants (bp : BipartiteStructure α) (prof : PreferenceProfile α) :
    GSInvariants bp prof (GSState.init : GSState α) :=
  ⟨initial_engagement bp prof, initial_proposalDownward bp prof,
    initial_receiverDominates bp prof⟩

/-! ### stepWith preservation

    The lemmas below are stated for an arbitrary `(m, w)`. The caller
    (`step_preserves_invariants`) supplies the chooser context. -/

lemma stepWith_engagement
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m w : α)
    (hmen : bp.isMen m = true) (hwomen : bp.isMen w = false)
    (hacc : {m, w} ∈ prof m)
    (hmfree : s.proposing m = none)
    (h : Engagement bp prof s) :
    Engagement bp prof (GSState.stepWith prof s m w) := by
  have hmw : m ≠ w := fun heq => by
    rw [heq, hwomen] at hmen; exact absurd hmen (by decide)
  have hMwomen : bp.isMen m ≠ bp.isMen w := by rw [hmen, hwomen]; decide
  have hWmen : bp.isMen w ≠ bp.isMen m := by rw [hmen, hwomen]; decide
  have hpr := stepWith_proposed prof s m w
  have hpwm : ∀ x, ¬ s.proposing x = some m := fun x hx => by
    have := (h x m hx).1; rw [hmfree] at this; simp at this
  intro a b hab
  cases hpw : s.proposing w with
  | none =>
    by_cases hwacc : ({m, w} : Finset α) ∈ prof w
    · -- None + Accept
      have hprop := stepWith_proposing_none_accept prof s m w hpw hwacc
      have hpm : (GSState.stepWith prof s m w).proposing m = some w := by
        rw [hprop]; simp
      have hpw' : (GSState.stepWith prof s m w).proposing w = some m := by
        rw [hprop]; simp [hmw.symm]
      have hpx : ∀ x, x ≠ m → x ≠ w →
          (GSState.stepWith prof s m w).proposing x = s.proposing x := by
        intros x hxm hxw; rw [hprop]; simp [hxm, hxw]
      by_cases ham : a = m
      · subst ham
        rw [hpm] at hab
        have hbw : b = w := (Option.some_inj.mp hab).symm
        subst hbw
        exact ⟨hpw', hMwomen, hacc, fun _ => by rw [hpr]; right; exact ⟨rfl, rfl⟩⟩
      · by_cases haw : a = w
        · subst haw
          rw [hpw'] at hab
          have hbm : b = m := (Option.some_inj.mp hab).symm
          subst hbm
          refine ⟨hpm, hWmen, ?_, fun hwmen => ?_⟩
          · rwa [Finset.pair_comm] at hwacc
          · rw [hwmen] at hwomen; exact absurd hwomen (by decide)
        · rw [hpx a ham haw] at hab
          have hold := h a b hab
          refine ⟨?_, hold.2.1, hold.2.2.1, fun hamen => by rw [hpr]; left; exact hold.2.2.2 hamen⟩
          by_cases hbm : b = m
          · subst hbm; exact absurd hab (hpwm a)
          · by_cases hbw : b = w
            · subst hbw
              have := hold.1; rw [hpw] at this; simp at this
            · rw [hpx b hbm hbw]; exact hold.1
    · -- None + Reject
      have hprop := stepWith_proposing_none_reject prof s m w hpw hwacc
      rw [hprop] at hab
      have hold := h a b hab
      exact ⟨by rw [hprop]; exact hold.1, hold.2.1, hold.2.2.1,
        fun hamen => by rw [hpr]; left; exact hold.2.2.2 hamen⟩
  | some mOld =>
    have hmOld_w : s.proposing mOld = some w := (h w mOld hpw).1
    have hmOld_neq_m : mOld ≠ m := fun heq => by
      rw [heq] at hmOld_w; rw [hmfree] at hmOld_w; simp at hmOld_w
    have hmOld_men_neq_w : bp.isMen mOld ≠ bp.isMen w := (h mOld w hmOld_w).2.1
    have hmOld_neq_w : mOld ≠ w := fun heq => by
      rw [heq] at hmOld_men_neq_w; exact hmOld_men_neq_w rfl
    by_cases hpref : ∃ i j : Fin (prof w).length,
        (prof w)[i] = {w, m} ∧ (prof w)[j] = {w, mOld} ∧ i < j
    · -- Some + Swap
      have hprop := stepWith_proposing_some_swap prof s m w mOld hpw hpref
      have hpm : (GSState.stepWith prof s m w).proposing m = some w := by
        rw [hprop]; simp
      have hpw' : (GSState.stepWith prof s m w).proposing w = some m := by
        rw [hprop]; simp [hmw.symm]
      have hpmOld : (GSState.stepWith prof s m w).proposing mOld = none := by
        rw [hprop]; simp [hmOld_neq_m, hmOld_neq_w]
      have hpx : ∀ x, x ≠ m → x ≠ w → x ≠ mOld →
          (GSState.stepWith prof s m w).proposing x = s.proposing x := by
        intros x hxm hxw hxmOld; rw [hprop]; simp [hxm, hxw, hxmOld]
      by_cases ham : a = m
      · subst ham
        rw [hpm] at hab
        have hbw : b = w := (Option.some_inj.mp hab).symm
        subst hbw
        exact ⟨hpw', hMwomen, hacc, fun _ => by rw [hpr]; right; exact ⟨rfl, rfl⟩⟩
      · by_cases haw : a = w
        · subst haw
          rw [hpw'] at hab
          have hbm : b = m := (Option.some_inj.mp hab).symm
          subst hbm
          refine ⟨hpm, hWmen, ?_, fun hwmen => ?_⟩
          · obtain ⟨i, _, hwm, _, _⟩ := hpref
            rw [← hwm]; exact List.getElem_mem _
          · rw [hwmen] at hwomen; exact absurd hwomen (by decide)
        · by_cases hamOld : a = mOld
          · subst hamOld
            rw [hpmOld] at hab; simp at hab
          · rw [hpx a ham haw hamOld] at hab
            have hold := h a b hab
            refine ⟨?_, hold.2.1, hold.2.2.1, fun hamen => by rw [hpr]; left; exact hold.2.2.2 hamen⟩
            by_cases hbm : b = m
            · subst hbm; exact absurd hab (hpwm a)
            · by_cases hbw : b = w
              · subst hbw
                have := hold.1; rw [hpw] at this
                rw [Option.some_inj] at this; exact absurd this.symm hamOld
              · by_cases hbmOld : b = mOld
                · subst hbmOld
                  have := hold.1; rw [hmOld_w] at this
                  rw [Option.some_inj] at this; exact absurd this.symm haw
                · rw [hpx b hbm hbw hbmOld]; exact hold.1
    · -- Some + Keep
      have hprop := stepWith_proposing_some_keep prof s m w mOld hpw hpref
      rw [hprop] at hab
      have hold := h a b hab
      exact ⟨by rw [hprop]; exact hold.1, hold.2.1, hold.2.2.1,
        fun hamen => by rw [hpr]; left; exact hold.2.2.2 hamen⟩

lemma stepWith_proposalDownward
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m w : α)
    (hmen : bp.isMen m = true)
    (hnobetter : ∀ w' : α, bp.isMen w' = false → {m, w'} ∈ prof m →
      ¬ s.proposed m w' → ¬ PrefersPartner prof m w' w)
    (h : ProposalDownward bp prof s) :
    ProposalDownward bp prof (GSState.stepWith prof s m w) := by
  intro m' w'' w' hm' hwomen' hpr_old hpref
  rw [stepWith_proposed] at hpr_old ⊢
  rcases hpr_old with hs | ⟨rfl, rfl⟩
  · left; exact h m' w'' w' hm' hwomen' hs hpref
  · by_cases h1 : w' = w''
    · right; exact ⟨rfl, h1⟩
    · left
      have hacc'' : {m', w'} ∈ prof m' := by
        obtain ⟨i, _, _, hi, _⟩ := hpref
        rw [← hi]; exact List.getElem_mem _
      by_contra hnp
      exact hnobetter w' hwomen' hacc'' hnp hpref

lemma stepWith_receiverDominates
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof)
    (s : GSState α) (m w : α)
    (hmen : bp.isMen m = true) (hwomen : bp.isMen w = false)
    (hmfree : s.proposing m = none)
    (hE : Engagement bp prof s)
    (h : ReceiverDominates bp prof s) :
    ReceiverDominates bp prof (GSState.stepWith prof s m w) := by
  have hmw : m ≠ w := fun heq => by
    rw [heq, hwomen] at hmen; exact absurd hmen (by decide)
  intro w_q m_q hw_q hpr_new
  rw [stepWith_proposed] at hpr_new
  cases hpw : s.proposing w with
  | none =>
    by_cases hwacc : ({m, w} : Finset α) ∈ prof w
    · -- None + Accept
      have hprop := stepWith_proposing_none_accept prof s m w hpw hwacc
      rcases hpr_new with hs | ⟨hmq, hwq⟩
      · have hold := h w_q m_q hw_q hs
        rcases hold with hno_acc | ⟨mCur, hpw_cur, hcur⟩
        · left; exact hno_acc
        · by_cases hwq_eq_w : w_q = w
          · subst hwq_eq_w
            rw [hpw] at hpw_cur; simp at hpw_cur
          · have hwq_ne_m : w_q ≠ m := fun heq => by
              rw [heq, hmen] at hw_q; simp at hw_q
            right
            refine ⟨mCur, ?_, hcur⟩
            rw [hprop]; simp [hwq_ne_m, hwq_eq_w]; exact hpw_cur
      · right
        refine ⟨m, ?_, Or.inl hmq.symm⟩
        rw [hwq, hprop]; simp [hmw.symm]
    · -- None + Reject
      have hprop := stepWith_proposing_none_reject prof s m w hpw hwacc
      rcases hpr_new with hs | ⟨hmq, hwq⟩
      · have hold := h w_q m_q hw_q hs
        rcases hold with hno_acc | ⟨mCur, hpw_cur, hcur⟩
        · left; exact hno_acc
        · right
          refine ⟨mCur, ?_, hcur⟩
          rw [hprop]; exact hpw_cur
      · left
        intro hmem
        apply hwacc
        rw [hwq, hmq] at hmem
        rwa [Finset.pair_comm] at hmem
  | some mOld =>
    have hmOld_w : s.proposing mOld = some w := (hE w mOld hpw).1
    have hmOld_men_neq_w : bp.isMen mOld ≠ bp.isMen w := (hE mOld w hmOld_w).2.1
    have hmOld_men : bp.isMen mOld = true := by
      cases hb : bp.isMen mOld
      · rw [hb, hwomen] at hmOld_men_neq_w; exact absurd rfl hmOld_men_neq_w
      · rfl
    have hmOld_w_acc : {w, mOld} ∈ prof w := (hE w mOld hpw).2.2.1
    have hmOld_neq_m : mOld ≠ m := fun heq => by
      rw [heq] at hmOld_w; rw [hmfree] at hmOld_w; simp at hmOld_w
    have hmOld_neq_w : mOld ≠ w := fun heq => by
      rw [heq, hwomen] at hmOld_men; simp at hmOld_men
    by_cases hpref : ∃ i j : Fin (prof w).length,
        (prof w)[i] = {w, m} ∧ (prof w)[j] = {w, mOld} ∧ i < j
    · -- Some + Swap
      have hprop := stepWith_proposing_some_swap prof s m w mOld hpw hpref
      rcases hpr_new with hs | ⟨hmq, hwq⟩
      · have hold := h w_q m_q hw_q hs
        rcases hold with hno_acc | ⟨mCur, hpw_cur, hcur⟩
        · left; exact hno_acc
        · have hwq_ne_m : w_q ≠ m := fun heq => by
            rw [heq, hmen] at hw_q; simp at hw_q
          have hwq_ne_mOld : w_q ≠ mOld := fun heq => by
            rw [heq, hmOld_men] at hw_q; simp at hw_q
          by_cases hwq_eq_w : w_q = w
          · subst hwq_eq_w
            rw [hpw] at hpw_cur
            rw [Option.some_inj] at hpw_cur
            subst hpw_cur
            right
            refine ⟨m, ?_, ?_⟩
            · rw [hprop]; simp [hmw.symm]
            · obtain ⟨i_m_w, j_mOld_w, hi_m, hj_mOld, hij⟩ := hpref
              have hpref_m_mOld : PrefersPartner prof w_q m mOld :=
                ⟨i_m_w, j_mOld_w, hij, hi_m, hj_mOld⟩
              rcases hcur with rfl | hp
              · right; exact hpref_m_mOld
              · right; exact Ranks_trans prof hvalid w_q hpref_m_mOld hp
          · right
            refine ⟨mCur, ?_, hcur⟩
            rw [hprop]; simp [hwq_ne_m, hwq_eq_w, hwq_ne_mOld]; exact hpw_cur
      · right
        refine ⟨m, ?_, Or.inl hmq.symm⟩
        rw [hwq, hprop]; simp [hmw.symm]
    · -- Some + Keep
      have hprop := stepWith_proposing_some_keep prof s m w mOld hpw hpref
      rcases hpr_new with hs | ⟨hmq, hwq⟩
      · have hold := h w_q m_q hw_q hs
        rcases hold with hno_acc | ⟨mCur, hpw_cur, hcur⟩
        · left; exact hno_acc
        · right
          refine ⟨mCur, ?_, hcur⟩
          rw [hprop]; exact hpw_cur
      · subst hmq; subst hwq
        by_cases hwm_acc : ({w_q, m_q} : Finset α) ∈ prof w_q
        · right
          refine ⟨mOld, ?_, Or.inr ?_⟩
          · rw [hprop]; exact hpw
          · obtain ⟨i_m_val, hi_m_lt, hi_m⟩ := List.getElem_of_mem hwm_acc
            obtain ⟨i_mOld_val, hi_mOld_lt, hi_mOld⟩ := List.getElem_of_mem hmOld_w_acc
            rcases lt_trichotomy i_mOld_val i_m_val with hlt | heq | hgt
            · exact ⟨⟨i_mOld_val, hi_mOld_lt⟩, ⟨i_m_val, hi_m_lt⟩, hlt, hi_mOld, hi_m⟩
            · exfalso
              have hkey : (prof w_q)[i_mOld_val] = (prof w_q)[i_m_val] := by
                subst heq; rfl
              rw [hi_mOld, hi_m] at hkey
              have hmem_m : m_q ∈ ({w_q, mOld} : Finset α) := by rw [hkey]; simp
              simp at hmem_m
              rcases hmem_m with hmemw | hmemold
              · exact hmw hmemw
              · exact hmOld_neq_m hmemold.symm
            · exact absurd ⟨⟨i_m_val, hi_m_lt⟩, ⟨i_mOld_val, hi_mOld_lt⟩, hi_m, hi_mOld, hgt⟩ hpref
        · left; exact hwm_acc

/-! ### Step + run preservation -/

lemma step_preserves_invariants
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof)
    (s : GSState α) (hI : GSInvariants bp prof s) :
    GSInvariants bp prof (s.step bp prof) := by
  classical
  by_cases hfree : ∃ m, GSFree bp prof s m
  · simp only [GSState.step, hfree, dite_true]
    set m := Classical.choose hfree with hm_def
    set candidates := candidateReceivers bp prof s m with hcands_def
    obtain ⟨hmen, hmfree, w0, hw0_women, hw0_acc, hw0_nprop⟩ := Classical.choose_spec hfree
    have hcands : candidates.Nonempty :=
      ⟨w0, by simp only [hcands_def, mem_candidateReceivers]; exact ⟨hw0_women, hw0_acc, hw0_nprop⟩⟩
    simp only [hcands, dite_true]
    set w := chooseMaxCandidate prof m candidates hcands with hw_def
    have hw_mem := chooseMaxCandidate_mem prof m candidates hcands
    rw [← hw_def] at hw_mem
    rw [mem_candidateReceivers] at hw_mem
    obtain ⟨hwomen, hacc, _hnprop⟩ := hw_mem
    have hnobetter : ∀ w' : α, bp.isMen w' = false → {m, w'} ∈ prof m →
        ¬ s.proposed m w' → ¬ PrefersPartner prof m w' w := by
      intro w' hw' hacc' hnprop'
      have hw'_cand : w' ∈ candidates := by
        simp only [hcands_def, mem_candidateReceivers]
        exact ⟨hw', hacc', hnprop'⟩
      have := chooseMaxCandidate_no_better prof hvalid m candidates hcands w' hw'_cand
      rw [hw_def]; exact this
    refine ⟨?_, ?_, ?_⟩
    · exact stepWith_engagement bp prof s m w hmen hwomen hacc hmfree hI.1
    · exact stepWith_proposalDownward bp prof s m w hmen hnobetter hI.2.1
    · exact stepWith_receiverDominates bp prof hvalid s m w hmen hwomen hmfree hI.1 hI.2.2
  · rw [step_eq_of_terminated bp prof s hfree]
    exact hI

lemma run_invariants
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof) (n : ℕ) :
    GSInvariants bp prof (GSState.run bp prof n) := by
  induction n with
  | zero => exact initial_invariants bp prof
  | succ n ih =>
    show GSInvariants bp prof ((GSState.run bp prof n).step bp prof)
    exact step_preserves_invariants bp prof hvalid _ ih

/-! ## Pairwise stability -/

theorem gs_pairwiseStable (bp : BipartiteStructure α)
    (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof)
    (hbip : BipartitePref bp prof) :
    PairwiseStable prof (gsGrouping (GSState.run bp prof (gsProposalBound α))) := by
  set s := GSState.run bp prof (gsProposalBound α) with hs_def
  obtain ⟨hE, hPD, hRD⟩ := run_invariants bp prof hvalid (gsProposalBound α)
  have hterm : GSTerminated bp prof s := by rw [hs_def]; exact gs_terminates bp prof
  -- Helper: prove False given that x is the man, y is the woman.
  suffices helper : ∀ x y : α, x ≠ y → bp.isMen x = true → bp.isMen y = false →
      Ranks prof x {x, y} (gsGrouping s x) → Ranks prof y {x, y} (gsGrouping s y) →
      ({x, y} : Finset α) ∈ prof x → False by
    intro a b ⟨hab, hra, hrb⟩
    have hab_acc_a : ({a, b} : Finset α) ∈ prof a := by
      obtain ⟨i, _, _, hi, _⟩ := hra
      rw [← hi]; exact List.getElem_mem _
    have hab_acc_b : ({a, b} : Finset α) ∈ prof b := by
      obtain ⟨i, _, _, hi, _⟩ := hrb
      rw [← hi]; exact List.getElem_mem _
    have hsides : bp.isMen a ≠ bp.isMen b :=
      hbip a {a, b} hab_acc_a a (by simp) b (by simp) hab
    cases hxx : bp.isMen a with
    | true =>
      have hb_false : bp.isMen b = false := by
        cases hbb : bp.isMen b
        · rfl
        · rw [hxx, hbb] at hsides; exact absurd rfl hsides
      exact helper a b hab hxx hb_false hra hrb hab_acc_a
    | false =>
      have hb_true : bp.isMen b = true := by
        cases hbb : bp.isMen b
        · rw [hxx, hbb] at hsides; exact absurd rfl hsides
        · rfl
      have hba : ({a, b} : Finset α) = {b, a} := Finset.pair_comm _ _
      have hry' : Ranks prof a {b, a} (gsGrouping s a) := by rw [← hba]; exact hra
      have hrx' : Ranks prof b {b, a} (gsGrouping s b) := by rw [← hba]; exact hrb
      have hab_acc_b' : ({b, a} : Finset α) ∈ prof b := by rw [← hba]; exact hab_acc_b
      exact helper b a (Ne.symm hab) hb_true hxx hrx' hry' hab_acc_b'
  -- Now prove the helper
  intro x y hxy hxmen hywomen hrx hry hxy_acc_x
  -- Step 1: show s.proposed x y
  have hxy_acc_y : ({x, y} : Finset α) ∈ prof y := by
    obtain ⟨i, _, _, hi, _⟩ := hry
    rw [← hi]; exact List.getElem_mem _
  have hpropose : s.proposed x y := by
    cases hpx : s.proposing x with
    | some w_x =>
      have hgs_x : gsGrouping s x = {x, w_x} := by simp [gsGrouping, hpx]
      rw [hgs_x] at hrx
      have hE_x := hE x w_x hpx
      have hpr_x_wx : s.proposed x w_x := hE_x.2.2.2 hxmen
      exact hPD x w_x y hxmen hywomen hpr_x_wx hrx
    | none =>
      by_contra hnp
      exact hterm ⟨x, hxmen, hpx, y, hywomen, hxy_acc_x, hnp⟩
  -- Step 2: apply ReceiverDominates on (y, x)
  have hRD_y := hRD y x hywomen hpropose
  have hyx_acc : ({y, x} : Finset α) ∈ prof y := by
    rwa [Finset.pair_comm] at hxy_acc_y
  rcases hRD_y with hno_acc | ⟨mCur, hpy_cur, hcur⟩
  · exact hno_acc hyx_acc
  · have hpy_cur_s : s.proposing y = some mCur := hpy_cur
    have hgs_y : gsGrouping s y = {y, mCur} := by simp [gsGrouping, hpy_cur_s]
    rw [hgs_y] at hry
    have hpref_y_x_mCur : PrefersPartner prof y x mCur := by
      have hp : ({x, y} : Finset α) = {y, x} := Finset.pair_comm _ _
      rw [hp] at hry; exact hry
    rcases hcur with hmCur_x | hcur'
    · rw [hmCur_x] at hpref_y_x_mCur
      exact Ranks_irrefl prof hvalid y _ hpref_y_x_mCur
    · exact Ranks_irrefl prof hvalid y _
        (Ranks_trans prof hvalid y hcur' hpref_y_x_mCur)

end

end HedonicGrouping.Algorithms.GaleShapley
