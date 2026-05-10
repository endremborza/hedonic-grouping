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
def GSState.stepWith (prof : PreferenceProfile α) (s : GSState α) (m w : α) : GSState α :=
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
def GSState.step (bp : BipartiteStructure α) (prof : PreferenceProfile α) (s : GSState α) : GSState α :=
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

omit [Fintype α] [DecidableEq α] in
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

/-- The set of pairs `(m, w)` that have been proposed so far. -/
def proposedSet (s : GSState α) : Finset (α × α) :=
  Finset.univ.filter fun p => s.proposed p.1 p.2

/-- Number of proposals made so far. -/
def proposedCount (s : GSState α) : ℕ :=
  (proposedSet s).card

lemma mem_proposedSet (s : GSState α) (p : α × α) :
    p ∈ proposedSet s ↔ s.proposed p.1 p.2 := by
  simp [proposedSet]

/-- After `stepWith`, the proposed relation is the old one extended by `(m, w)`. -/
lemma stepWith_proposed (prof : PreferenceProfile α) (s : GSState α) (m w : α) :
    (GSState.stepWith prof s m w).proposed =
      fun m' w' => s.proposed m' w' ∨ (m' = m ∧ w' = w) := by
  cases hw : s.matching w with
  | none => simp [GSState.stepWith, hw]; split_ifs <;> rfl
  | some mOld => simp [GSState.stepWith, hw]; split_ifs <;> rfl

/-- `stepWith` inserts exactly `(m, w)` into the proposed set. -/
lemma proposedSet_stepWith (prof : PreferenceProfile α) (s : GSState α) (m w : α) :
    proposedSet (GSState.stepWith prof s m w) = insert (m, w) (proposedSet s) := by
  ext ⟨m', w'⟩
  simp [proposedSet, stepWith_proposed, or_comm]

/-- If `(m, w)` is new, `stepWith` increases the count by one. -/
lemma proposedCount_stepWith (prof : PreferenceProfile α) (s : GSState α) (m w : α)
    (hnew : ¬ s.proposed m w) :
    proposedCount (GSState.stepWith prof s m w) = proposedCount s + 1 := by
  have hnotmem : (m, w) ∉ proposedSet s := by simp [proposedSet, hnew]
  simp [proposedCount, proposedSet_stepWith, Finset.card_insert_of_notMem hnotmem]

/-- The initial state has zero proposals. -/
lemma proposedCount_initial : proposedCount (GSState.init : GSState α) = 0 := by
  simp [proposedCount, proposedSet, GSState.init]

/-- If a free man exists, stepping adds exactly one proposal. -/
lemma proposedCount_step_of_free (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (hfree : ∃ m, GSFree bp prof s m) :
    proposedCount (s.step bp prof) = proposedCount s + 1 := by
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

/-- All proposals go from men to women; so `proposedSet s` fits inside the men×women grid.
    Proof: induction on the run — `step` only proposes when `GSFree` holds, which
    requires `bp.isMen m = true` and `bp.isMen w = false`. -/
lemma proposedSet_subset_menWomen (bp : BipartiteStructure α) (prof : PreferenceProfile α) (n : ℕ) :
    proposedSet (GSState.run bp prof n) ⊆
      (Finset.univ.filter (fun a => bp.isMen a = true)) ×ˢ
      (Finset.univ.filter (fun a => bp.isMen a = false)) := by
  induction n with
    | zero => simp [GSState.run, proposedSet, GSState.init]
    | succ n ih => 
      simp only [GSState.run]
      unfold GSState.step
      split
      next hFree => 
        dsimp
        split_ifs with hc
        · rw [proposedSet_stepWith]
          rw [Finset.insert_subset_iff]
          constructor
          · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
            have hw := Classical.choose_spec hc
            constructor
            · obtain ⟨ hIsMan, hMatchedToNone, hExistsUnproposedWoman ⟩ := Classical.choose_spec hFree
              exact hIsMan
            · --
              simp only [candidateReceivers, Finset.mem_filter, Finset.mem_univ, true_and] at hw
              obtain ⟨hIsWoman, hValidCoalition, hNotProposed⟩ := hw
              exact hIsWoman
          · exact ih
        · exact ih
      · exact ih


/-- The men×women grid has exactly `gsProposalBound bp` cells. -/
lemma menWomen_card (bp : BipartiteStructure α) :
    ((Finset.univ.filter (fun a => bp.isMen a = true)) ×ˢ
     (Finset.univ.filter (fun a => bp.isMen a = false))).card = gsProposalBound bp := by
  simp [gsProposalBound, Finset.card_product]

/-- If a free man exists, the count is strictly below the proposal bound. -/
lemma proposedCount_lt_bound_of_free (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (n : ℕ) (hfree : ∃ m, GSFree bp prof (GSState.run bp prof n) m) :
    proposedCount (GSState.run bp prof n) < gsProposalBound bp := by
  obtain ⟨m, hismen, _, w, hw, _, hnprop⟩ := hfree
  set s := GSState.run bp prof n with hs_def
  set grid :=
    (Finset.univ.filter (fun a => bp.isMen a = true)) ×ˢ
    (Finset.univ.filter (fun a => bp.isMen a = false)) with hgrid_def
  have hnotmem : (m, w) ∉ proposedSet s := by simp [proposedSet, hnprop]
  have hmwinGrid : (m, w) ∈ grid := by simp [hgrid_def, hismen, hw]
  have hsub : proposedSet s ⊆ grid := by rw [hs_def]; exact proposedSet_subset_menWomen bp prof n
  have hssub : proposedSet s ⊂ grid := by
    constructor
    · exact hsub
    · intro hge; exact hnotmem (hge hmwinGrid)
  calc proposedCount s
      = (proposedSet s).card := rfl
    _ < grid.card := Finset.card_lt_card hssub
    _ = gsProposalBound bp := menWomen_card bp

/-- A terminated state is a fixpoint under `step`. -/
lemma step_eq_of_terminated (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (s : GSState α) (h : GSTerminated bp prof s) :
    s.step bp prof = s := by
  simp only [GSState.step, dif_neg h]

/-- If not terminated at step `n`, exactly `n` proposals have been made. -/
lemma proposedCount_run_of_not_terminated (bp : BipartiteStructure α)
    (prof : PreferenceProfile α) (n : ℕ) :
    ¬ GSTerminated bp prof (GSState.run bp prof n) →
    proposedCount (GSState.run bp prof n) = n := by
  induction n with
  | zero =>
    intro _; simp [GSState.run, proposedCount_initial]
  | succ n ih =>
    intro hnot
    have hnot' : ¬ GSTerminated bp prof (GSState.run bp prof n) := fun hterm =>
      hnot (show GSTerminated bp prof (GSState.run bp prof (n + 1)) by
        simp only [GSState.run]; rwa [step_eq_of_terminated bp prof _ hterm])
    have hfree : ∃ m, GSFree bp prof (GSState.run bp prof n) m :=
      Classical.not_not.mp hnot'
    calc proposedCount (GSState.run bp prof (n + 1))
        = proposedCount ((GSState.run bp prof n).step bp prof) := rfl
      _ = proposedCount (GSState.run bp prof n) + 1 :=
          proposedCount_step_of_free bp prof _ hfree
      _ = n + 1 := by rw [ih hnot']

/-- The algorithm terminates within `gsProposalBound` steps. -/
theorem gs_terminates (bp : BipartiteStructure α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof) (hsize : SizeTwo prof)
    (hbip : BipartitePref bp prof) :
    GSTerminated bp prof (GSState.run bp prof (gsProposalBound bp)) := by
  by_contra h
  have heq := proposedCount_run_of_not_terminated bp prof _ h
  have hfree : ∃ m, GSFree bp prof (GSState.run bp prof (gsProposalBound bp)) m :=
    Classical.not_not.mp h
  linarith [proposedCount_lt_bound_of_free bp prof _ hfree]

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
