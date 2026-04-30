import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.SMP

namespace HedonicGrouping.Algorithms.GaleShapley
/-!
# Gale-Shapley algorithm

Deferred acceptance on a bipartite size-2 instance. Produces a
`PairwiseStable` grouping; the `CoreStable` upgrade is performed in
`Correctness.GS_SMP` via the size-2 bridge.

## Structure
1. State, step, run, termination bound.
2. Seven invariants (ported from `refs/stable-marriage-lean/`).
3. Terminal-state pairwise-stability theorem.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.SMP

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable section
open Classical

/-- GS algorithm state: current matching + proposal history. -/
structure GSState (α : Type*) where
  matching : α → Option α
  proposed : α → α → Prop

/-- Initial state: everyone unmatched, no proposals. -/
def GSState.init : GSState α where
  matching := fun _ => none
  proposed := fun _ _ => False

/-- Agent `m` is a free proposer with remaining candidates. -/
def GSFree (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m : α) : Prop :=
  bp.isMen m = true ∧
  s.matching m = none ∧
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
def GSState.stepWith (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (m w : α) : GSState α :=
  let proposed' := fun m' w' => s.proposed m' w' ∨ (m' = m ∧ w' = w)
  match s.matching w with
  | none =>
    if {m, w} ∈ prof w then
      { matching := fun a =>
          if a = m then some w
          else if a = w then some m
          else s.matching a
        proposed := proposed' }
    else
      { matching := s.matching
        proposed := proposed' }
  | some mOld =>
    if ∃ i j : Fin (prof w).length,
        (prof w)[i] = {w, m} ∧ (prof w)[j] = {w, mOld} ∧ i < j then
      { matching := fun a =>
          if a = m then some w
          else if a = w then some m
          else if a = mOld then none
          else s.matching a
        proposed := proposed' }
    else
      { matching := s.matching
        proposed := proposed' }

/-- Choose a free man and propose. -/
def GSState.step (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : GSState α :=
  if h : ∃ m, GSFree bp prof s m then
    let m := Classical.choose h
    let _hm := Classical.choose_spec h
    let candidates := candidateReceivers bp prof s m
    if hc : candidates.Nonempty then
      GSState.stepWith bp prof s m hc.choose
    else s
  else s

/-- Run `n` steps from the initial state. -/
def GSState.run (bp : BipartiteStructure α) (prof : PreferenceProfile α) :
    ℕ → GSState α
  | 0 => GSState.init
  | n + 1 => (GSState.run bp prof n).step bp prof

/-- Upper bound on total proposals. -/
def gsProposalBound (bp : BipartiteStructure α) : ℕ :=
  (Finset.univ.filter (fun a => bp.isMen a = true)).card *
  (Finset.univ.filter (fun a => bp.isMen a = false)).card

/-- Convert final GS state to a hedonic `Grouping`. -/
def gsGrouping (s : GSState α) : Grouping α :=
  fun a => match s.matching a with
    | some b => {a, b}
    | none => {a}

/-! ## Invariants -/

/-- `matching a = some b ↔ matching b = some a`. -/
def MatchConsistent (s : GSState α) : Prop :=
  ∀ a b : α, s.matching a = some b ↔ s.matching b = some a

/-- Matched proposers are matched to acceptable partners. -/
def ProposerAcceptable (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ m w, bp.isMen m = true → s.matching m = some w → {m, w} ∈ prof m

/-- Matched receivers are matched to acceptable partners. -/
def ReceiverAcceptable (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ w m, bp.isMen w = false → s.matching w = some m → {w, m} ∈ prof w

/-- Proposals are downward-closed. -/
def ProposalDownward (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ m w w', bp.isMen m = true → s.proposed m w →
    PrefersPartner prof m w' w → s.proposed m w'

/-- Every matched proposer proposed to his current match. -/
def MatchedProposed (bp : BipartiteStructure α) (s : GSState α) : Prop :=
  ∀ m w, bp.isMen m = true → s.matching m = some w → s.proposed m w

/-- Unmatched receivers rejected all proposers as unacceptable. -/
def UnmatchedReject (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ w m, bp.isMen w = false → s.matching w = none →
    s.proposed m w → {w, m} ∉ prof w

/-- A receiver's current match is at least as preferred as any past proposer. -/
def ReceiverBest (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  ∀ w m mCur, bp.isMen w = false → s.matching w = some mCur →
    s.proposed m w → m ≠ mCur →
    PrefersPartner prof w mCur m

/-! ## Invariant initialization -/

lemma initial_matchConsistent : MatchConsistent (GSState.init : GSState α) := by
  intro a b
  simp [GSState.init]

lemma initial_proposerAcceptable (bp : BipartiteStructure α)
    (prof : PreferenceProfile α) :
    ProposerAcceptable bp prof GSState.init := by
  intro m w _ hmatch
  simp [GSState.init] at hmatch

lemma initial_receiverAcceptable (bp : BipartiteStructure α)
    (prof : PreferenceProfile α) :
    ReceiverAcceptable bp prof GSState.init := by
  intro w m _ hmatch
  simp [GSState.init] at hmatch

lemma initial_proposalDownward (bp : BipartiteStructure α)
    (prof : PreferenceProfile α) :
    ProposalDownward bp prof GSState.init := by
  intro m w w' _ hprop
  simp [GSState.init] at hprop

lemma initial_matchedProposed (bp : BipartiteStructure α) :
    MatchedProposed bp (GSState.init : GSState α) := by
  intro m w _ hmatch
  simp [GSState.init] at hmatch

lemma initial_unmatchedReject (bp : BipartiteStructure α)
    (prof : PreferenceProfile α) :
    UnmatchedReject bp prof GSState.init := by
  intro w m _ _ hprop
  simp [GSState.init] at hprop

lemma initial_receiverBest (bp : BipartiteStructure α)
    (prof : PreferenceProfile α) :
    ReceiverBest bp prof GSState.init := by
  intro w m mCur _ hmatch
  simp [GSState.init] at hmatch

/-! ## Termination -/

/-- Count of proposals made so far. -/
noncomputable def proposalCount (bp : BipartiteStructure α)
    (s : GSState α) : ℕ :=
  (Finset.univ.filter fun mw : α × α =>
    bp.isMen mw.1 = true ∧ bp.isMen mw.2 = false ∧ s.proposed mw.1 mw.2).card

/-- The algorithm terminates within `gsProposalBound` steps. -/
theorem gs_terminates (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof) (hsize : SizeTwo prof)
    (hbip : BipartitePref bp prof) :
    GSTerminated bp prof (GSState.run bp prof (gsProposalBound bp)) := by
  sorry -- Proof: proposalCount strictly increases per step, bounded by gsProposalBound.
         -- At the bound, no free man can exist (pigeonhole).

/-! ## Invariant preservation -/

/-- All seven invariants hold after `n` steps. -/
def GSInvariantsHold (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) : Prop :=
  MatchConsistent s ∧
  ProposerAcceptable bp prof s ∧
  ReceiverAcceptable bp prof s ∧
  ProposalDownward bp prof s ∧
  MatchedProposed bp s ∧
  UnmatchedReject bp prof s ∧
  ReceiverBest bp prof s

theorem gs_invariants_hold (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof) (hsize : SizeTwo prof)
    (hbip : BipartitePref bp prof) (n : ℕ) :
    GSInvariantsHold bp prof (GSState.run bp prof n) := by
  sorry -- Proof: induction on n.
         -- Base: all initial_* lemmas.
         -- Step: each stepWith preserves each invariant (7 preservation lemmas).

/-! ## Pairwise stability -/

/-- **GS produces a pairwise-stable grouping.** The `CoreStable` upgrade
    under size-2 is in `Correctness.GS_SMP`. -/
theorem gs_pairwiseStable (bp : BipartiteStructure α)
    (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof) (hsize : SizeTwo prof)
    (hbip : BipartitePref bp prof) :
    PairwiseStable prof (gsGrouping (GSState.run bp prof (gsProposalBound bp))) := by
  sorry -- Proof: Let s = terminal state. Suppose (m, w) is a blocking pair.
         -- m prefers w to his match → m proposed to w (ProposalDownward + termination).
         -- Case w unmatched: UnmatchedReject says w finds m unacceptable → contradiction.
         -- Case w matched to mCur: ReceiverBest says w prefers mCur to m → contradiction.

end

end HedonicGrouping.Algorithms.GaleShapley
