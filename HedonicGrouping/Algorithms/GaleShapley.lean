import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.SMP

namespace HedonicGrouping.Algorithms.GaleShapley
/-!
# Gale-Shapley algorithm

Deferred acceptance with pairwise advocacies. Produces a `PairwiseStable`
grouping; the `CoreStable` upgrade is performed in `Correctness.GS_SMP`
via the size-2 bridge.

## Structure
1. State (self-contained `GSState`), step, run.
2. Termination via proposal-count monotonicity (`gs_terminates_within`).
3. Seven invariants, each split into `stepWith_*` / `runSteps_*` lemmas.
4. Terminal-state pairwise-stability theorem.

## Open work in this file
- The `step` chooser is currently arbitrary (`Finset.Nonempty.choose`).
  `ProposalDownward` requires it to be preference-respecting; closing
  `stepWith_proposalDownward` is therefore blocked on switching `step`
  to a max-preferred chooser. Tracked in `stepWith_proposalDownward` below.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.SMP

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable section
open Classical

/-- GS state. Each agent's `proposing` field carries their current matched
    partner (`some w` for engaged, `none` for unmatched); `proposed` is the
    history of past advocacies. Self-contained — HCF, Irving, and GS each
    have their own state type (see `.cril/ideas.md` for the rationale). -/
structure GSState (α : Type*) where
  proposing : α → Option α
  proposed  : α → α → Prop

/-- Initial state: everyone unmatched, no advocacies on record. -/
def GSState.init : GSState α where
  proposing := fun _ => none
  proposed  := fun _ _ => False

/-! ### Proposal-count termination machinery -/

/-- Set of `(proposer, receiver)` pairs in the history. -/
noncomputable def GSState.proposedSet (s : GSState α) : Finset (α × α) := by
  classical
  exact Finset.univ.filter fun p => s.proposed p.1 p.2

/-- Total advocacies made so far. -/
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

/-- Monotone-bounded termination: a step function that strictly grows
    `proposedCount` whenever it's not at a fixpoint must reach a fixpoint
    within `|α|·|α|` iterations. -/
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

/-- Preference ordering on receivers from `m`'s preference list. -/
def menPrefLE (prof : PreferenceProfile α) (m : α) (w1 w2 : α) : Prop :=
  w1 = w2 ∨
  ∃ i j : Fin (prof m).length,
    (prof m)[i] = {m, w2} ∧ (prof m)[j] = {m, w1} ∧ j ≤ i

/-- One GS step: a free man proposes to his best remaining candidate. -/
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

/-- Choose a free man and propose. The current chooser is arbitrary
    (`Classical.choose`), which suffices for termination but blocks
    `ProposalDownward`. Switch to a preference-respecting chooser
    (e.g. via `menPrefLE` and `Finset.exists_maximal`) when attacking
    `stepWith_proposalDownward`. -/
def GSState.step (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : GSState α :=
  if h : ∃ m, GSFree bp prof s m then
    let m := Classical.choose h
    let _hm := Classical.choose_spec h
    let candidates := candidateReceivers bp prof s m
    if hc : candidates.Nonempty then
      GSState.stepWith prof s m hc.choose
    else s
  else s

/-- Run `n` steps from the initial state. -/
def GSState.run (bp : BipartiteStructure α) (prof : PreferenceProfile α) :
    ℕ → GSState α
  | 0 => GSState.init
  | n + 1 => (GSState.run bp prof n).step bp prof

/-- Termination bound: `Fintype.card α * Fintype.card α`, the generic
    `|α|·|β|` from `Common` specialized to GS's `β = α`. The looser
    bipartite bound `|men|·|women|` is *not* used; bipartiteness is
    irrelevant to termination. -/
def gsProposalBound (α : Type*) [Fintype α] : ℕ :=
  Fintype.card α * Fintype.card α

/-- Convert final GS state to a hedonic `Grouping`. -/
def gsGrouping (s : GSState α) : Grouping α :=
  fun a => match s.proposing a with
    | some b => {a, b}
    | none => {a}

/-! ## Invariants -/

/-- `proposing a = some b ↔ proposing b = some a`. -/
def ProposingConsistent (s : GSState α) : Prop :=
  ∀ a b : α, s.proposing a = some b ↔ s.proposing b = some a

/-- Engaged proposers are matched to acceptable partners. -/
def ProposerAcceptable (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ m w, bp.isMen m = true → s.proposing m = some w → {m, w} ∈ prof m

/-- Engaged receivers are matched to acceptable partners. -/
def ReceiverAcceptable (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ w m, bp.isMen w = false → s.proposing w = some m → {w, m} ∈ prof w

/-- Proposals are downward-closed. -/
def ProposalDownward (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ m w w', bp.isMen m = true → s.proposed m w →
    PrefersPartner prof m w' w → s.proposed m w'

/-- Every engaged proposer proposed to his current match. -/
def ProposingProposed (bp : BipartiteStructure α) (s : GSState α) : Prop :=
  ∀ m w, bp.isMen m = true → s.proposing m = some w → s.proposed m w

/-- Unmatched receivers rejected all proposers as unacceptable. -/
def UnmatchedReject (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ w m, bp.isMen w = false → s.proposing w = none →
    s.proposed m w → {w, m} ∉ prof w

/-- A receiver's current match is at least as preferred as any past proposer. -/
def ReceiverBest (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ w m mCur, bp.isMen w = false → s.proposing w = some mCur →
    s.proposed m w → m ≠ mCur →
    PrefersPartner prof w mCur m

/-! ## Invariant initialization -/

omit [Fintype α] [DecidableEq α] in
lemma initial_proposingConsistent : ProposingConsistent (GSState.init : GSState α) := by
  intro a b
  simp [GSState.init]

lemma initial_proposerAcceptable (bp : BipartiteStructure α)
    (prof : PreferenceProfile α) :
    ProposerAcceptable bp prof (GSState.init : GSState α) := by
  intro m w _ hmatch
  simp [GSState.init] at hmatch

lemma initial_receiverAcceptable (bp : BipartiteStructure α)
    (prof : PreferenceProfile α) :
    ReceiverAcceptable bp prof (GSState.init : GSState α) := by
  intro w m _ hmatch
  simp [GSState.init] at hmatch

lemma initial_proposalDownward (bp : BipartiteStructure α)
    (prof : PreferenceProfile α) :
    ProposalDownward bp prof (GSState.init : GSState α) := by
  intro m w w' _ hprop
  simp [GSState.init] at hprop

lemma initial_proposingProposed (bp : BipartiteStructure α) :
    ProposingProposed bp (GSState.init : GSState α) := by
  intro m w _ hmatch
  simp [GSState.init] at hmatch

lemma initial_unmatchedReject (bp : BipartiteStructure α)
    (prof : PreferenceProfile α) :
    UnmatchedReject bp prof (GSState.init : GSState α) := by
  intro w m _ _ hprop
  simp [GSState.init] at hprop

lemma initial_receiverBest (bp : BipartiteStructure α)
    (prof : PreferenceProfile α) :
    ReceiverBest bp prof (GSState.init : GSState α) := by
  intro w m mCur _ hmatch
  simp [GSState.init] at hmatch

/-! ## Termination -/

/-- After `stepWith`, the proposed relation is the old one extended by `(m, w)`. -/
lemma stepWith_proposed (prof : PreferenceProfile α) (s : GSState α) (m w : α) :
    (GSState.stepWith prof s m w).proposed =
      fun m' w' => s.proposed m' w' ∨ (m' = m ∧ w' = w) := by
  cases hw : s.proposing w with
  | none => simp [GSState.stepWith, hw]; split_ifs <;> rfl
  | some mOld => simp [GSState.stepWith, hw]; split_ifs <;> rfl

/-- `stepWith` inserts exactly `(m, w)` into the proposed set. -/
lemma proposedSet_stepWith (prof : PreferenceProfile α) (s : GSState α) (m w : α) :
    (GSState.stepWith prof s m w).proposedSet =
      insert (m, w) s.proposedSet := by
  ext ⟨m', w'⟩
  simp [GSState.proposedSet, stepWith_proposed, or_comm]

/-- If `(m, w)` is new, `stepWith` increases the count by one. -/
lemma proposedCount_stepWith (prof : PreferenceProfile α) (s : GSState α) (m w : α)
    (hnew : ¬ s.proposed m w) :
    (GSState.stepWith prof s m w).proposedCount = s.proposedCount + 1 := by
  have hnotmem : (m, w) ∉ s.proposedSet := by
    simp [GSState.proposedSet, hnew]
  simp [GSState.proposedCount, proposedSet_stepWith,
        Finset.card_insert_of_notMem hnotmem]

/-- If a free man exists, stepping adds exactly one proposal. -/
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
      simp only [hcands_def, candidateReceivers, Finset.mem_filter,
                 Finset.mem_univ, true_and]
      exact ⟨hw, hacc, hnprop⟩⟩
  simp only [hcands, dite_true]
  have hnew : ¬ s.proposed m hcands.choose := by
    have hmem := hcands.choose_spec
    simp only [hcands_def, candidateReceivers, Finset.mem_filter,
               Finset.mem_univ, true_and] at hmem
    exact hmem.2.2
  exact proposedCount_stepWith prof s m hcands.choose hnew

/-- A terminated state is a fixpoint under `step`. -/
lemma step_eq_of_terminated (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (h : GSTerminated bp prof s) :
    s.step bp prof = s := by
  simp only [GSState.step, dif_neg h]

/-- `run n` is the same as iterating `step` `n` times from `init`. -/
lemma run_eq_iterate (bp : BipartiteStructure α) (prof : PreferenceProfile α) (n : ℕ) :
    GSState.run bp prof n =
      ((fun s => s.step bp prof)^[n]) GSState.init := by
  induction n with
  | zero => simp [GSState.run]
  | succ n ih =>
    rw [GSState.run, ih, Function.iterate_succ_apply']

/-- **GS terminates within `|α|²` steps.** Proof: the proposed-set is
    monotone-strictly-growing (one fresh `(m, w)` per non-terminated
    step) and bounded by `gsProposalBound α`. The bipartite structure
    is *not* used here — termination is a property of the proposal-history
    growth, not of the matching structure. -/
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

/-! ## Invariant preservation

    Each invariant `X` is broken into:
    - `stepWith_X` — preservation under one explicit `(m, w)` proposal,
    - `runSteps_X` — preservation under `run`, by induction on `n`.

    The seven `runSteps_X` lemmas combine into `gs_invariants_hold`. -/

lemma stepWith_proposingConsistent
    (prof : PreferenceProfile α) (s : GSState α) (m w : α)
    (h : ProposingConsistent s) :
    ProposingConsistent (GSState.stepWith prof s m w) := by
  sorry -- Proof: case on s.proposing w; the update preserves bidirectional consistency.
         -- Reference: refs/stable-marriage-lean/Lemmas.lean stepWith_consistent (line 357).

lemma stepWith_proposerAcceptable
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m w : α)
    (hmen : bp.isMen m = true) (hwomen : bp.isMen w = false)
    (hacc : {m, w} ∈ prof m)
    (h : ProposerAcceptable bp prof s) :
    ProposerAcceptable bp prof (GSState.stepWith prof s m w) := by
  sorry -- Proof: only m's proposing field changes (to some w); {m, w} ∈ prof m by hypothesis.
         -- Reference: stepWith_menAcceptable (line 170).

lemma stepWith_receiverAcceptable
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m w : α)
    (h : ReceiverAcceptable bp prof s) :
    ReceiverAcceptable bp prof (GSState.stepWith prof s m w) := by
  sorry -- Proof: w's proposing only updates inside the `{m, w} ∈ prof w` branch.
         -- Reference: stepWith_womenAcceptable (line 234).

lemma stepWith_proposalDownward
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m w : α)
    (h : ProposalDownward bp prof s) :
    ProposalDownward bp prof (GSState.stepWith prof s m w) := by
  sorry -- BLOCKED on bug fix: `step` must select a max-preferred candidate (currently
         -- uses arbitrary `Classical.choose`). Once `step` proposes in preference order,
         -- this lemma follows since w's only chosen because every preferred w' had
         -- already been proposed. Reference: step_menProposedDownward (line 467).

lemma stepWith_proposingProposed
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m w : α)
    (h : ProposingProposed bp s) :
    ProposingProposed bp (GSState.stepWith prof s m w) := by
  sorry -- Proof: stepWith adds (m, w) to proposed in every branch; new matches are
         -- only ever m to w. Reference: stepWith_menMatchedProposed (line 520).

lemma stepWith_unmatchedReject
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m w : α)
    (h : UnmatchedReject bp prof s) :
    UnmatchedReject bp prof (GSState.stepWith prof s m w) := by
  sorry -- Proof: a receiver becomes proposing iff she just accepted; otherwise the
         -- field is unchanged. Reference: stepWith_womenUnmatchedReject (line 625).

lemma stepWith_receiverBest
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m w : α)
    (h : ReceiverBest bp prof s) :
    ReceiverBest bp prof (GSState.stepWith prof s m w) := by
  sorry -- Proof: w only swaps to a strictly-preferred proposer; non-w receivers
         -- unchanged. Reference: stepWith_womenBest (line 728).

/-! ### Per-invariant `runSteps` results -/

lemma runSteps_proposingConsistent
    (bp : BipartiteStructure α) (prof : PreferenceProfile α) (n : ℕ) :
    ProposingConsistent (GSState.run bp prof n) := by
  sorry -- Proof: induction on n; base = initial_proposingConsistent;
         -- step uses stepWith_proposingConsistent through GSState.step.

lemma runSteps_proposerAcceptable
    (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (hbip : BipartitePref bp prof) (n : ℕ) :
    ProposerAcceptable bp prof (GSState.run bp prof n) := by
  sorry -- Proof: induction on n; the GSFree witness gives bp.isMen m = true and
         -- {m, w} ∈ prof m, so stepWith_proposerAcceptable applies.

lemma runSteps_receiverAcceptable
    (bp : BipartiteStructure α) (prof : PreferenceProfile α) (n : ℕ) :
    ReceiverAcceptable bp prof (GSState.run bp prof n) := by
  sorry

lemma runSteps_proposalDownward
    (bp : BipartiteStructure α) (prof : PreferenceProfile α) (n : ℕ) :
    ProposalDownward bp prof (GSState.run bp prof n) := by
  sorry -- BLOCKED on stepWith_proposalDownward (which is blocked on the step bug fix).

lemma runSteps_proposingProposed
    (bp : BipartiteStructure α) (prof : PreferenceProfile α) (n : ℕ) :
    ProposingProposed bp (GSState.run bp prof n) := by
  sorry

lemma runSteps_unmatchedReject
    (bp : BipartiteStructure α) (prof : PreferenceProfile α) (n : ℕ) :
    UnmatchedReject bp prof (GSState.run bp prof n) := by
  sorry

lemma runSteps_receiverBest
    (bp : BipartiteStructure α) (prof : PreferenceProfile α) (n : ℕ) :
    ReceiverBest bp prof (GSState.run bp prof n) := by
  sorry

/-- All seven invariants hold after `n` steps. -/
def GSInvariantsHold (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ProposingConsistent s ∧
  ProposerAcceptable bp prof s ∧
  ReceiverAcceptable bp prof s ∧
  ProposalDownward bp prof s ∧
  ProposingProposed bp s ∧
  UnmatchedReject bp prof s ∧
  ReceiverBest bp prof s

theorem gs_invariants_hold (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof) (hsize : SizeTwo prof)
    (hbip : BipartitePref bp prof) (n : ℕ) :
    GSInvariantsHold bp prof (GSState.run bp prof n) :=
  ⟨runSteps_proposingConsistent bp prof n,
   runSteps_proposerAcceptable bp prof hbip n,
   runSteps_receiverAcceptable bp prof n,
   runSteps_proposalDownward bp prof n,
   runSteps_proposingProposed bp prof n,
   runSteps_unmatchedReject bp prof n,
   runSteps_receiverBest bp prof n⟩

/-! ## Pairwise stability -/

/-- **GS produces a pairwise-stable grouping.** The `CoreStable` upgrade
    under size-2 is in `Correctness.GS_SMP`. -/
theorem gs_pairwiseStable (bp : BipartiteStructure α)
    (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof) (hsize : SizeTwo prof)
    (hbip : BipartitePref bp prof) :
    PairwiseStable prof (gsGrouping (GSState.run bp prof (gsProposalBound α))) := by
  sorry -- Proof: Let s = terminal state. Suppose (m, w) is a blocking pair.
         -- m prefers w to his match → m proposed to w (ProposalDownward + termination).
         -- Case w unmatched: UnmatchedReject says w finds m unacceptable → contradiction.
         -- Case w matched to mCur: ReceiverBest says w prefers mCur to m → contradiction.

end

end HedonicGrouping.Algorithms.GaleShapley
