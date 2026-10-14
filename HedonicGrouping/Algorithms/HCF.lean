import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.HCP

namespace HedonicGrouping.Algorithms.HCF
/-!
# Hedonic Coalition Formation — iterative form

Iterative reformulation of the recursive HCF: the Python prototype's
recursive call stack becomes an explicit `List HCFFrame`. Each `step`
performs one atomic action. Mirrors `src/hedonic.py::solve_iterative`.

Termination is proved: no lexicographic pairing of `|stack|` with the
remaining-preference budget decreases — a push copies the parent's problem
unchanged, growing the stack at constant budget. What does decrease
(oracle-probed 2026-07-02, machine-checked as `slackMeasure_step_lt`) is a
forced-move-slack measure: every pushed exception is fresh, so
`forcedMoves` strictly grows up the stack, and weighting each frame's
budget by `C^(K − |forcedMoves|)` (`K` bounding distinct coalitions, `C`
bounding budgets) strictly decreases at every step. The invariant-carrying
`HCFState.run` is well-founded on it, and `hcfGrouping` extracts the
Option-valued result.

Correctness against `CoreStable` (`hcf_coreStable`, partial correctness)
is stated but not yet proved.
-/

open HedonicGrouping.Core
open HedonicGrouping.Problems.HCP

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## State types -/

/-- Per-frame problem state. Holds the mutable per-call data: the current
    (possibly trimmed) preferences, the per-agent proposal histories, the
    per-agent in-proposals (coalition → proposers so far), and the set of
    forced moves accumulated along the recursion path. -/
structure HCFProblem (α : Type*) [DecidableEq α] where
  preferences  : α → List (Finset α)
  outProposals : α → List (Finset α)
  inProposals  : α → Finset α → Finset α
  forcedMoves  : Finset (Finset α)

def HCFProblem.init (prof : PreferenceProfile α) : HCFProblem α where
  preferences  := prof
  outProposals := fun _ => []
  inProposals  := fun _ _ => ∅
  forcedMoves  := ∅

/-- What `step` will do next on this frame. -/
inductive Stage
  | init
  | phase1
  | decide
  | awaitingChild
  deriving DecidableEq, Repr

structure HCFFrame (α : Type*) [DecidableEq α] where
  problem          : HCFProblem α
  exception        : Finset α
  stage            : Stage
  pendingRemaining : List (Finset α)

/-- Global iterator state: a stack of frames and the most-recently-popped
    problem (mirrors Python's `last`). -/
structure HCFState (α : Type*) [DecidableEq α] where
  stack : List (HCFFrame α)
  last  : Option (HCFProblem α)

def HCFState.init (prof : PreferenceProfile α) : HCFState α :=
  { stack :=
      [{ problem := HCFProblem.init prof
         exception := ∅
         stage := Stage.init
         pendingRemaining := [] }]
    last := none }

/-! ## Per-frame query helpers -/

def HCFProblem.hasValidProposal (p : HCFProblem α) (a : α) : Bool :=
  (p.outProposals a).any (fun G => decide (G ∉ p.forcedMoves))

def HCFProblem.topUnproposed (p : HCFProblem α) (a : α) : Option (Finset α) :=
  (p.preferences a).find? (fun G => decide (G ∉ p.outProposals a))

def HCFProblem.remainingPrefs (p : HCFProblem α) (a : α) : List (Finset α) :=
  (p.preferences a).filter (fun G => decide (G ∉ p.outProposals a))

/-- Latest out-proposal per agent, if all agents have proposed. -/
def HCFProblem.latestProposals (p : HCFProblem α) : Option (α → Finset α) :=
  if h : ∀ a, (p.outProposals a) ≠ [] then
    some (fun a => (p.outProposals a).getLast (h a))
  else none

/-- Extract a grouping from the latest proposals when they form a valid
    partition: every member of `a`'s coalition has the same coalition. -/
def HCFProblem.solution (p : HCFProblem α) : Option (Grouping α) :=
  match p.latestProposals with
  | none => none
  | some g =>
    if ∀ a : α, ∀ b ∈ g a, g b = g a then some g else none

/-! ## Mutators -/

/-- Filter every per-agent list to drop coalitions in `removal`. -/
def eliminate (p : HCFProblem α) (removal : Finset (Finset α)) :
    HCFProblem α :=
  { p with
    preferences  := fun a => (p.preferences  a).filter (fun G => decide (G ∉ removal))
    outProposals := fun a => (p.outProposals a).filter (fun G => decide (G ∉ removal))
    inProposals  := fun a G => if G ∈ removal then ∅ else p.inProposals a G }

/-- `coalition` is considerable for `receiver`: enough of its members are
    already proposing it (≥ `|coalition| − 1`) and `receiver` ranks it. -/
def isConsiderableB (p : HCFProblem α) (receiver : α) (G : Finset α) : Bool :=
  decide ((p.inProposals receiver G).card ≥ G.card - 1) &&
    decide (G ∈ p.preferences receiver)

/-- Record `proposer` as having proposed `coalition` to `receiver`, then run
    the Considerable-cascade (mirrors Python `_receive_proposal`): once the
    proposal is considerable, either eliminate `coalition` itself if
    `receiver` already holds a strictly-better considerable proposal, or
    else eliminate every option `receiver` ranks below `coalition`. -/
def receiveProposal (p : HCFProblem α) (receiver : α)
    (coalition : Finset α) (proposer : α) : HCFProblem α :=
  let p1 := { p with
    inProposals := fun a G =>
      if a = receiver ∧ G = coalition then insert proposer (p.inProposals a G)
      else p.inProposals a G }
  if isConsiderableB p1 receiver coalition then
    let prefsR := p1.preferences receiver
    let better := prefsR.takeWhile (fun C => decide (C ≠ coalition))
    if better.any (fun C => isConsiderableB p1 receiver C) then
      eliminate p1 {coalition}
    else
      eliminate p1 ((prefsR.dropWhile (fun C => decide (C ≠ coalition))).drop 1).toFinset
  else p1

/-- Broadcast a new proposal `(a, G)`: append to `a`'s out-proposals and
    record `a` as a proposer with each other member of `G`. -/
def broadcastProposal [LinearOrder α] (p : HCFProblem α) (a : α) (G : Finset α) :
    HCFProblem α :=
  let p' := { p with outProposals := fun x =>
                if x = a then p.outProposals x ++ [G] else p.outProposals x }
  ((G.erase a).sort (· ≤ ·)).foldl (fun acc b => receiveProposal acc b G a) p'

/-! ## Step function -/

/-- The first agent for which `pred` holds, if any. -/
def firstAgent [LinearOrder α] (pred : α → Bool) : Option α :=
  ((Finset.univ : Finset α).sort (· ≤ ·)).find? pred

/-- Pop the top frame, setting `last := result`. -/
def popWith (s : HCFState α) (result : Option (HCFProblem α)) : HCFState α :=
  { s with stack := s.stack.tail, last := result }

/-- One atomic step of the iterative HCF. -/
def step [LinearOrder α] (s : HCFState α) : HCFState α :=
  match s.stack with
  | [] => s
  | frame :: rest =>
    match frame.stage with
    | .init =>
      let p' := { frame.problem with
                  forcedMoves := insert frame.exception frame.problem.forcedMoves }
      { s with stack := { frame with problem := p', stage := .phase1 } :: rest }

    | .phase1 =>
      match firstAgent (fun a => !frame.problem.hasValidProposal a) with
      | none =>
        { s with stack := { frame with stage := .decide } :: rest }
      | some a =>
        match frame.problem.topUnproposed a with
        | none => popWith s none
        | some G =>
            let p' := broadcastProposal frame.problem a G
            { s with stack := { frame with problem := p' } :: rest }

    | .decide =>
      match frame.problem.solution with
      | some g =>
        let p' := { frame.problem with
                    preferences := fun a => [g a] }
        popWith s (some p')
      | none =>
        match firstAgent (fun a => !(frame.problem.remainingPrefs a).isEmpty) with
        | none => popWith s (some frame.problem)
        | some a =>
          match (frame.problem.outProposals a).getLast? with
          | none => popWith s none
          | some k =>
            let child : HCFFrame α :=
              { problem := frame.problem
                exception := k
                stage := .init
                pendingRemaining := frame.problem.remainingPrefs a }
            let frame' := { frame with
                            stage := .awaitingChild
                            pendingRemaining := frame.problem.remainingPrefs a }
            { s with stack := child :: frame' :: rest }

    | .awaitingChild =>
      match s.last with
      | none =>
        let removal : Finset (Finset α) := frame.pendingRemaining.toFinset
        let p' := eliminate frame.problem removal
        { s with stack := { frame with problem := p', stage := .phase1 } :: rest
                 last := none }
      | some _ =>
        popWith s s.last

/-- The iterator has finished — no more frames to advance. -/
def Terminated (s : HCFState α) : Prop := s.stack = []

/-! ## Termination measure

The slack-hierarchy measure for the eventual well-founded `run`
(oracle-probed 2026-07-02: strictly decreases at every one of ~5,900 steps
across 376 instances). Lean names for the probe's symbols: `budget` (B),
`coalitionBound` (K), `slack`, `pos`, `Stage.weight` (stageW), `value` (v),
`measureBase` (C), `slackMeasure` (M). -/

/-- Remaining-preference budget `B(p)`: total count of not-yet-proposed
    preference entries across all agents. -/
def HCFProblem.budget (p : HCFProblem α) : Nat :=
  ∑ a, (p.remainingPrefs a).length

/-- The original coalition pool: every coalition some agent ranks in the
    starting profile. Every coalition a run tracks comes from here (the
    root exception `∅` is the one addition). -/
def originalCoalitions (prof : PreferenceProfile α) : Finset (Finset α) :=
  Finset.univ.biUnion fun a => (prof a).toFinset

/-- `K`: one more than the number of distinct coalitions in the original
    profile — a bound on `|forcedMoves|` along a run, since every forced
    move is an original coalition or the root exception `∅`. -/
def coalitionBound (prof : PreferenceProfile α) : Nat :=
  (originalCoalitions prof).card + 1

/-- Forced-move slack of a frame: how far its `forcedMoves` sits below the
    bound `K`. Every pushed exception is fresh, so slack strictly shrinks
    going up the stack — this is what pays for a push. -/
def HCFFrame.slack (prof : PreferenceProfile α) (f : HCFFrame α) : Nat :=
  coalitionBound prof - f.problem.forcedMoves.card

/-- Positional exponent of a frame: `2·slack − [stage = .init]`. The `.init`
    offset makes a fresh child (whose first step inserts its exception,
    dropping its slack) enter strictly below the position its parent
    occupied before the push. -/
def HCFFrame.pos (prof : PreferenceProfile α) (f : HCFFrame α) : Nat :=
  2 * f.slack prof - (if f.stage = .init then 1 else 0)

/-- Stage weight: strictly decreasing along the intra-frame progression
    `init → phase1 → decide → awaitingChild`, so stage-only transitions
    (which leave the budget untouched) still decrease the frame value. -/
def Stage.weight : Stage → Nat
  | .init          => 3
  | .phase1        => 2
  | .decide        => 1
  | .awaitingChild => 0

/-- Frame value `v(f) = 4·B + stageW + 1`: budget-dominated, stage weight
    breaking ties on stage-only transitions, `+1` keeping every frame's
    contribution positive. -/
def HCFFrame.value (f : HCFFrame α) : Nat :=
  4 * f.problem.budget + f.stage.weight + 1

/-- Hierarchy base `C = 4·B_init + 8`: strictly exceeds every reachable
    frame value (per-frame budgets never grow past the initial budget), so
    one unit at position `p` outweighs any single frame's value at a
    position `< p`. -/
def measureBase (prof : PreferenceProfile α) : Nat :=
  4 * (∑ a, (prof a).length) + 8

/-- The slack-hierarchy measure `M(s) = Σ_f v(f)·C^pos(f)` over the stack.
    A push is paid by the parent's stage drop (`decide → awaitingChild`) at
    a strictly higher position than the child's entire contribution. -/
def HCFState.slackMeasure (prof : PreferenceProfile α) (s : HCFState α) : Nat :=
  (s.stack.map fun f => f.value * measureBase prof ^ f.pos prof).sum

/-! ## Run invariants

The six probe-validated invariants (0 violations across ~5,900 steps /
376 instances, 2026-07-02) that the well-founded `run` threads: they are
what makes `slackMeasure` strictly decrease at *arbitrary*
invariant-satisfying states, not merely states reachable from `init`.
Numbering `(i)`–`(vi)` follows the probe. -/

/-- (i) Only an agent's most recent out-proposal can be unforced: every
    earlier entry of its proposal history is already a forced move. An
    agent proposes only while it holds no valid proposal, so at most its
    last proposal escapes `forcedMoves`. -/
def HCFProblem.ProposalsForced (p : HCFProblem α) : Prop :=
  ∀ a : α, ∀ G ∈ (p.outProposals a).dropLast, G ∈ p.forcedMoves

/-- Every coalition the frame tracks — ranked, proposed, forced, or its
    exception — comes from the original pool (forced moves and the
    exception may also be the root `∅`). This is the Lean content of the
    probe's "`pos` stays ≥ 0": it lets `coalitionBound` genuinely bound
    `forcedMoves.card`, so the slack subtractions never truncate. -/
structure HCFFrame.FromPool (prof : PreferenceProfile α) (f : HCFFrame α) :
    Prop where
  preferences : ∀ a : α, ∀ G ∈ f.problem.preferences a, G ∈ originalCoalitions prof
  outProposals : ∀ a : α, ∀ G ∈ f.problem.outProposals a, G ∈ originalCoalitions prof
  forcedMoves : f.problem.forcedMoves ⊆ insert ∅ (originalCoalitions prof)
  exception : f.exception ∈ insert ∅ (originalCoalitions prof)

/-- Per-frame run invariant: the probe-validated facts restricted to one
    stacked frame. -/
structure HCFFrame.Inv (prof : PreferenceProfile α) (f : HCFFrame α) :
    Prop where
  /-- (i) -/
  proposalsForced : f.problem.ProposalsForced
  /-- (ii) At `.decide` every agent holds a valid proposal. Together with
      (i) this makes each pushed exception `getLast (outProposals pivot)`
      fresh — so `forcedMoves` strictly grows up the stack, and a parent
      about to push has slack ≥ 1, paying for the child's position. -/
  decideAllValid : f.stage = .decide → ∀ a : α, f.problem.hasValidProposal a
  /-- (iii) Per-frame budgets never grow past the initial budget — what
      keeps every frame value below the hierarchy base `C`. -/
  budgetBounded : f.problem.budget ≤ ∑ a, (prof a).length
  /-- (iv, "stays ≥ 0" half) -/
  fromPool : f.FromPool prof
  /-- (v) An `.init` frame's exception is never already forced — its first
      step strictly grows `forcedMoves`, dropping its slack. -/
  initFresh : f.stage = .init → f.exception ∉ f.problem.forcedMoves
  /-- (vi) An `.awaitingChild` frame's `pendingRemaining` is the (frozen,
      nonempty) remaining prefs of its pivot agent — so the eliminate on a
      child's `none` return strictly shrinks the budget. The equality is
      exact because only the head frame is ever rebuilt. -/
  awaitingPending : f.stage = .awaitingChild →
    ∃ a : α, f.pendingRemaining = f.problem.remainingPrefs a ∧
      f.pendingRemaining ≠ []

/-- The bundled run invariant the well-founded `run` threads: every
    stacked frame satisfies `HCFFrame.Inv`, and (iv, descent half)
    positions strictly decrease from the bottom of the stack to the top —
    the head is the top, so positions strictly increase along the list. -/
structure HCFInv (prof : PreferenceProfile α) (s : HCFState α) : Prop where
  frames : ∀ f ∈ s.stack, f.Inv prof
  posDescending : s.stack.IsChain fun c p => c.pos prof < p.pos prof

/-- The initial state satisfies the run invariant: every per-frame conjunct
    is vacuous at stage `.init` or trivial on the empty histories, the budget
    bound is the filter length bound, and the singleton stack settles the
    position chain. -/
theorem hcfInv_init (prof : PreferenceProfile α) :
    HCFInv prof (HCFState.init prof) := by
  constructor
  · intro f hf
    simp only [HCFState.init, List.mem_singleton] at hf
    subst hf
    refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro a G hG
      simp [HCFProblem.init] at hG
    · intro h
      simp at h
    · simp only [HCFProblem.budget, HCFProblem.remainingPrefs, HCFProblem.init]
      refine Finset.sum_le_sum fun a _ => ?_
      apply List.length_filter_le
    · intro a G hG
      simp only [HCFProblem.init] at hG
      simp only [originalCoalitions, Finset.mem_biUnion]
      exact ⟨a, Finset.mem_univ a, List.mem_toFinset.mpr hG⟩
    · intro a G hG
      simp [HCFProblem.init] at hG
    · simp [HCFProblem.init]
    · exact Finset.mem_insert_self _ _
    · intro _
      simp [HCFProblem.init]
    · intro h
      simp at h
  · simp only [HCFState.init]
    constructor

/-! ## Bundle preservation

Campaign brick 4 (complete): `HCFInv` is preserved across each of `step`'s
transitions — the five `popWith` pops (one lemma; the invariant never
inspects `last`), the stage-only `.phase1` → `.decide` move, the `.init` →
`.phase1` exception-forcing move, the `phase1` broadcast (via `TrimsTo`),
the `.decide` push, and the `awaitingChild`-`none` eliminate — assembled
into `hcfInv_step`. -/

/-- A `firstAgent` miss is a universal `false`: the sorted universe is
    exhaustive, so `find?` returning `none` refutes the predicate at every
    agent. Converts `step`'s guards into the pointwise facts the
    preservation lemmas consume. -/
theorem firstAgent_eq_none [LinearOrder α] {pred : α → Bool}
    (h : firstAgent pred = none) (a : α) : pred a = false := by
  simp only [firstAgent, List.find?_eq_none] at h
  simpa using h a (by simp)

/-- Popping the top frame preserves the run invariant: the surviving frames
    were already stacked, and a chain restricted to its tail is still a
    chain. One lemma covers all five `popWith` transitions of `step`. -/
theorem hcfInv_popWith {prof : PreferenceProfile α} {s : HCFState α}
    (h : HCFInv prof s) (result : Option (HCFProblem α)) :
    HCFInv prof (popWith s result) :=
  ⟨fun f hf => h.frames f (List.mem_of_mem_tail hf), h.posDescending.tail⟩


/-- Bundle preservation across the stage-only `.phase1` → `.decide` move.
    The transition guard — every agent holds a valid proposal, taken
    pointwise rather than in `firstAgent` form — is exactly the newly-live
    `decideAllValid` conjunct; the remaining conjuncts transport along the
    unchanged problem, and the position chain is untouched because `pos`
    ignores non-`.init` stages. -/
theorem hcfInv_phase1_decide {prof : PreferenceProfile α} {s : HCFState α}
    {frame : HCFFrame α} {rest : List (HCFFrame α)}
    (h : HCFInv prof s) (hstack : s.stack = frame :: rest)
    (hstage : frame.stage = .phase1)
    (hall : ∀ a : α, frame.problem.hasValidProposal a) :
    HCFInv prof { s with stack := { frame with stage := .decide } :: rest } := by
  have hframe : frame.Inv prof := h.frames frame (by simp [hstack])
  constructor
  · intro f hf
    rcases List.mem_cons.mp hf with hf | hf
    · subst hf
      exact ⟨hframe.proposalsForced, fun _ => hall, hframe.budgetBounded,
        ⟨hframe.fromPool.preferences, hframe.fromPool.outProposals,
         hframe.fromPool.forcedMoves, hframe.fromPool.exception⟩,
        fun hc => by simp at hc, fun hc => by simp at hc⟩
    · exact h.frames f (by rw [hstack]; exact List.mem_cons_of_mem _ hf)
  · have hpos : ({ frame with stage := .decide } : HCFFrame α).pos prof
        = frame.pos prof := by
      simp [HCFFrame.pos, HCFFrame.slack, hstage]
    have hchain := h.posDescending
    rw [hstack, List.isChain_cons] at hchain
    exact List.isChain_cons.mpr
      ⟨fun b hb => hpos ▸ hchain.1 b hb, hchain.2⟩

/-- Bundle preservation across the `.init` → `.phase1` move: the frame
    forces its own exception. Freshness ((v), live at `.init`) makes the
    insert grow `forcedMoves` by exactly one, so the frame's slack drops by
    one and its position falls from `2σ − 1` to `2σ − 2` — still below the
    frame beneath it (only `≤` on the old position is needed here; the
    strict measure drop is brick 5's business). The pool absorbs the new
    forced move because the exception was already pool-listed; every other
    conjunct transports along the unchanged preferences and proposal
    histories or is vacuous at `.phase1`. -/
theorem hcfInv_init_phase1 {prof : PreferenceProfile α} {s : HCFState α}
    {frame : HCFFrame α} {rest : List (HCFFrame α)}
    (h : HCFInv prof s) (hstack : s.stack = frame :: rest)
    (hstage : frame.stage = .init) :
    HCFInv prof { s with stack :=
      { frame with
        problem := { frame.problem with
          forcedMoves := insert frame.exception frame.problem.forcedMoves }
        stage := .phase1 } :: rest } := by
  have hframe : frame.Inv prof := h.frames frame (by simp [hstack])
  constructor
  · intro f hf
    rcases List.mem_cons.mp hf with hf | hf
    · subst hf
      exact ⟨fun a G hG => Finset.mem_insert_of_mem (hframe.proposalsForced a G hG),
        fun hc => by simp at hc, hframe.budgetBounded,
        ⟨hframe.fromPool.preferences, hframe.fromPool.outProposals,
         Finset.insert_subset_iff.mpr
           ⟨hframe.fromPool.exception, hframe.fromPool.forcedMoves⟩,
         hframe.fromPool.exception⟩,
        fun hc => by simp at hc, fun hc => by simp at hc⟩
    · exact h.frames f (by rw [hstack]; exact List.mem_cons_of_mem _ hf)
  · have hcard : (insert frame.exception frame.problem.forcedMoves).card
        = frame.problem.forcedMoves.card + 1 :=
      Finset.card_insert_of_notMem (hframe.initFresh hstage)
    have hchain := h.posDescending
    rw [hstack, List.isChain_cons] at hchain
    refine List.isChain_cons.mpr
      ⟨fun b hb => lt_of_le_of_lt ?_ (hchain.1 b hb), hchain.2⟩
    simp [HCFFrame.pos, HCFFrame.slack, hstage, hcard]
    omega

/-- An element of a filtered list's `dropLast` sits at a non-final position
    of the filtered list, hence has a later element in the base list, hence
    sits at a non-final position there too. What makes invariant (i) survive
    `eliminate`: filtering a proposal history never promotes an old entry
    past the position of the (possibly removed) newest one. -/
private theorem mem_dropLast_of_mem_filter_dropLast {β : Type*} {q : β → Bool}
    {y : β} : ∀ {l : List β}, y ∈ (l.filter q).dropLast → y ∈ l.dropLast := by
  intro l
  induction l with
  | nil => simp
  | cons x t ih =>
    intro h
    have hcons : t ≠ [] → (x :: t).dropLast = x :: t.dropLast := fun ht => by
      cases t with
      | nil => exact absurd rfl ht
      | cons z t' => rfl
    by_cases hq : q x
    · rw [List.filter_cons_of_pos hq] at h
      cases hf : t.filter q with
      | nil => rw [hf] at h; simp at h
      | cons z f' =>
        rw [hf] at h
        have ht : t ≠ [] := fun ht => by rw [ht] at hf; simp at hf
        rw [hcons ht]
        rcases List.mem_cons.mp (by simpa using h) with hy | hy
        · exact hy ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih (hf ▸ hy))
    · rw [List.filter_cons_of_neg hq] at h
      have hy := ih h
      have ht : t ≠ [] := fun ht => by rw [ht] at hy; simp at hy
      rw [hcons ht]
      exact List.mem_cons_of_mem _ hy

/-- One problem *trims to* another: preferences and proposal histories only
    lose entries (and non-final proposal entries stay non-final), forced
    moves are untouched, and no agent's remaining-preference count grows.
    Every action `receiveProposal` takes — recording an in-proposal,
    eliminating the proposed coalition, eliminating a dominated tail — is a
    trim, and trims compose, so this is the foldl invariant that carries the
    frame bundle across `broadcastProposal`'s cascade. -/
structure HCFProblem.TrimsTo (p q : HCFProblem α) : Prop where
  preferences : ∀ x : α, ∀ G ∈ q.preferences x, G ∈ p.preferences x
  outProposals : ∀ x : α, ∀ G ∈ q.outProposals x, G ∈ p.outProposals x
  outDropLast : ∀ x : α, ∀ G ∈ (q.outProposals x).dropLast,
    G ∈ (p.outProposals x).dropLast
  forcedMoves : q.forcedMoves = p.forcedMoves
  remaining : ∀ x : α, (q.remainingPrefs x).length ≤ (p.remainingPrefs x).length

theorem HCFProblem.TrimsTo.rfl (p : HCFProblem α) : p.TrimsTo p :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, Eq.refl _, fun _ => le_rfl⟩

theorem HCFProblem.TrimsTo.trans {p q r : HCFProblem α}
    (hpq : p.TrimsTo q) (hqr : q.TrimsTo r) : p.TrimsTo r :=
  ⟨fun x G h => hpq.preferences x G (hqr.preferences x G h),
   fun x G h => hpq.outProposals x G (hqr.outProposals x G h),
   fun x G h => hpq.outDropLast x G (hqr.outDropLast x G h),
   hqr.forcedMoves.trans hpq.forcedMoves,
   fun x => (hqr.remaining x).trans (hpq.remaining x)⟩

/-- `eliminate` is a trim: both per-agent lists are filtered by the same
    removal set, so a coalition surviving in the filtered proposal history
    still shadows its preference entry — nothing is ever un-shadowed. -/
theorem eliminate_trimsTo (p : HCFProblem α) (removal : Finset (Finset α)) :
    p.TrimsTo (eliminate p removal) := by
  refine ⟨?_, ?_, ?_, Eq.refl _, ?_⟩
  · exact fun x G hG => (List.mem_filter.mp hG).1
  · exact fun x G hG => (List.mem_filter.mp hG).1
  · exact fun x G hG => mem_dropLast_of_mem_filter_dropLast hG
  · intro x
    simp only [HCFProblem.remainingPrefs, eliminate, List.filter_filter]
    refine List.Sublist.length_le (List.monotone_filter_right _ ?_)
    intro C hC
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hC
    simp only [decide_eq_true_eq]
    intro hmem
    exact hC.1 (List.mem_filter.mpr ⟨hmem, by simpa using hC.2⟩)

/-- `receiveProposal` is a trim: recording the in-proposal touches only
    `inProposals`, and both cascade branches are `eliminate`s. -/
theorem receiveProposal_trimsTo (p : HCFProblem α) (r : α) (G : Finset α)
    (proposer : α) : p.TrimsTo (receiveProposal p r G proposer) := by
  have hp1 : ∀ ip, p.TrimsTo { p with inProposals := ip } := fun ip =>
    ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, Eq.refl _, fun _ => le_rfl⟩
  simp only [receiveProposal]
  split
  · split
    · exact (hp1 _).trans (eliminate_trimsTo _ _)
    · exact (hp1 _).trans (eliminate_trimsTo _ _)
  · exact hp1 _

/-- The broadcast cascade is a trim of the post-append problem: each
    receiver's `receiveProposal` trims, and trims compose. -/
theorem foldl_receiveProposal_trimsTo (G : Finset α) (a : α) :
    ∀ (l : List α) (p : HCFProblem α),
      p.TrimsTo (l.foldl (fun acc b => receiveProposal acc b G a) p)
  | [], p => HCFProblem.TrimsTo.rfl p
  | b :: l, p =>
    (receiveProposal_trimsTo p b G a).trans
      (foldl_receiveProposal_trimsTo G a l _)

/-- Bundle preservation across the `phase1` broadcast: agent `a` (holding
    no valid proposal) proposes its top unproposed coalition `G`. The
    append keeps (i) because the transition guard forces `a`'s *entire*
    history — everything but the fresh `G` — into `forcedMoves`; `G` comes
    from `a`'s preference list, so the pool absorbs it; and the cascade is
    a trim, so every conjunct transports. `forcedMoves` is untouched
    throughout, so positions are unchanged and the chain carries over. -/
theorem hcfInv_phase1_broadcast [LinearOrder α] {prof : PreferenceProfile α}
    {s : HCFState α} {frame : HCFFrame α} {rest : List (HCFFrame α)}
    {a : α} {G : Finset α}
    (h : HCFInv prof s) (hstack : s.stack = frame :: rest)
    (hstage : frame.stage = .phase1)
    (hnovalid : frame.problem.hasValidProposal a = false)
    (hG : frame.problem.topUnproposed a = some G) :
    HCFInv prof { s with stack :=
      { frame with problem := broadcastProposal frame.problem a G } :: rest } := by
  have hframe : frame.Inv prof := h.frames frame (by simp [hstack])
  simp only [HCFProblem.hasValidProposal, List.any_eq_false, decide_eq_true_eq,
    not_not] at hnovalid
  simp only [HCFProblem.topUnproposed] at hG
  have hGpref : G ∈ frame.problem.preferences a := List.mem_of_find?_eq_some hG
  set p' : HCFProblem α := { frame.problem with outProposals :=
      fun x => if x = a then (frame.problem.outProposals x ++ [G]) else frame.problem.outProposals x }
    with hp'
  have hT : p'.TrimsTo (broadcastProposal frame.problem a G) :=
    foldl_receiveProposal_trimsTo G a _ p'
  have hprefs_eq : ∀ x : α, p'.preferences x = frame.problem.preferences x := by
    intro x; simp [hp']
  have hforced_eq : p'.forcedMoves = frame.problem.forcedMoves := by
    simp [hp']
  have houts_a : ∀ x : α, x = a →
      p'.outProposals x = frame.problem.outProposals x ++ [G] := by
    intro x hx; simp [hp', hx]
  have houts_ne : ∀ x : α, x ≠ a →
      p'.outProposals x = frame.problem.outProposals x := by
    intro x hx; simp [hp', hx]
  have houts' : ∀ x : α, ∀ P ∈ p'.outProposals x,
      P ∈ frame.problem.outProposals x ∨ P = G := by
    intro x P hP
    by_cases hx : x = a
    · rw [houts_a x hx] at hP
      rcases List.mem_append.mp hP with hP | hP
      · exact Or.inl hP
      · exact Or.inr (by simpa using hP)
    · rw [houts_ne x hx] at hP
      exact Or.inl hP
  have hbudget' : ∀ x : α,
      (p'.remainingPrefs x).length ≤ (frame.problem.remainingPrefs x).length := by
    intro x
    by_cases hx : x = a
    · simp only [HCFProblem.remainingPrefs, hprefs_eq, houts_a x hx]
      refine List.Sublist.length_le (List.monotone_filter_right _ ?_)
      intro C hC
      simp only [decide_eq_true_eq, List.mem_append] at hC ⊢
      exact fun hmem => hC (Or.inl hmem)
    · simp only [HCFProblem.remainingPrefs, hprefs_eq, houts_ne x hx]
      exact le_rfl
  constructor
  · intro f hf
    rcases List.mem_cons.mp hf with hf | hf
    · subst hf
      refine ⟨?_, fun hc => by simp [hstage] at hc, ?_, ⟨?_, ?_, ?_, ?_⟩,
        fun hc => by simp [hstage] at hc, fun hc => by simp [hstage] at hc⟩
      · intro x P hP
        rw [hT.forcedMoves, hforced_eq]
        have hP' := hT.outDropLast x P hP
        by_cases hx : x = a
        · rw [houts_a x hx] at hP'
          have hdl : (frame.problem.outProposals x ++ [G]).dropLast
              = frame.problem.outProposals x := by simp
          rw [hdl] at hP'
          exact hnovalid P (hx ▸ hP')
        · rw [houts_ne x hx] at hP'
          exact hframe.proposalsForced x P hP'
      · calc (broadcastProposal frame.problem a G).budget
            ≤ p'.budget := Finset.sum_le_sum fun x _ => hT.remaining x
          _ ≤ frame.problem.budget := Finset.sum_le_sum fun x _ => hbudget' x
          _ ≤ ∑ x, (prof x).length := hframe.budgetBounded
      · exact fun x P hP =>
          hframe.fromPool.preferences x P (hT.preferences x P hP)
      · intro x P hP
        rcases houts' x P (hT.outProposals x P hP) with hP' | hP'
        · exact hframe.fromPool.outProposals x P hP'
        · exact hP' ▸ hframe.fromPool.preferences a G hGpref
      · rw [hT.forcedMoves, hforced_eq]
        exact hframe.fromPool.forcedMoves
      · exact hframe.fromPool.exception
    · exact h.frames f (by rw [hstack]; exact List.mem_cons_of_mem _ hf)
  · have hpos : ({ frame with problem := broadcastProposal frame.problem a G }
        : HCFFrame α).pos prof = frame.pos prof := by
      simp [HCFFrame.pos, HCFFrame.slack, hT.forcedMoves, hforced_eq]
    have hchain := h.posDescending
    rw [hstack, List.isChain_cons] at hchain
    exact List.isChain_cons.mpr
      ⟨fun b hb => hpos ▸ hchain.1 b hb, hchain.2⟩

private theorem mem_of_getLast?_eq_some {β : Type*} {l : List β} {b : β}
    (h : l.getLast? = some b) : b ∈ l := by
  obtain ⟨l', rfl⟩ := List.getLast?_eq_some_iff.mp h
  exact List.mem_append_right _ List.mem_cons_self

/-- At `.decide`, the pivot's latest proposal is fresh: invariant (i)
    forces every non-final history entry, so the valid proposal (ii)
    guarantees must be the final entry — the `getLast?` itself. -/
theorem decide_getLast_fresh {prof : PreferenceProfile α} {f : HCFFrame α}
    (hinv : f.Inv prof) (hstage : f.stage = .decide) {a : α} {k : Finset α}
    (hlast : (f.problem.outProposals a).getLast? = some k) :
    k ∉ f.problem.forcedMoves := by
  obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.mp hlast
  have hvalid := hinv.decideAllValid hstage a
  simp only [HCFProblem.hasValidProposal, List.any_eq_true,
    decide_eq_true_eq] at hvalid
  obtain ⟨P, hPmem, hPfree⟩ := hvalid
  rw [hl'] at hPmem
  rcases List.mem_append.mp hPmem with hP | hP
  · exact absurd (hinv.proposalsForced a P (by rw [hl']; simpa using hP)) hPfree
  · have hPk : P = k := by simpa using hP
    exact hPk ▸ hPfree

/-- A fresh pool-listed coalition witnesses `forcedMoves ⊂ insert ∅ pool`,
    bounding `forcedMoves.card` strictly below `coalitionBound` — the
    "slack ≥ 1" fact both the push chain and the measure drop consume. -/
theorem card_forced_lt_of_fresh {prof : PreferenceProfile α}
    {f : HCFFrame α} (hpool : f.FromPool prof) {k : Finset α}
    (hk : k ∈ insert ∅ (originalCoalitions prof))
    (hfresh : k ∉ f.problem.forcedMoves) :
    f.problem.forcedMoves.card < coalitionBound prof := by
  have hss : f.problem.forcedMoves ⊂ insert ∅ (originalCoalitions prof) :=
    (Finset.ssubset_iff_of_subset hpool.forcedMoves).mpr ⟨k, hk, hfresh⟩
  have h1 := Finset.card_lt_card hss
  have h2 := Finset.card_insert_le (∅ : Finset α) (originalCoalitions prof)
  unfold coalitionBound
  omega

/-- Bundle preservation across the `.decide` push: the parent — all-valid
    at `.decide` — pushes a child copying its problem, excepting the pivot's
    latest proposal `k`. Invariant (i) forces every non-final entry of the
    pivot's history, so the valid proposal (ii) guarantees must be the final
    entry — `k` itself — making the child's exception fresh (v) and
    pool-listed. Freshness against the pool bounds `forcedMoves` strictly
    below `coalitionBound`, so the parent's slack is ≥ 1 and the child (at
    `.init`) enters at position `2σ − 1`, strictly below its parent's `2σ`. -/
theorem hcfInv_decide_push {prof : PreferenceProfile α} {s : HCFState α}
    {frame : HCFFrame α} {rest : List (HCFFrame α)} {a : α} {k : Finset α}
    (h : HCFInv prof s) (hstack : s.stack = frame :: rest)
    (hstage : frame.stage = .decide)
    (hrem : frame.problem.remainingPrefs a ≠ [])
    (hlast : (frame.problem.outProposals a).getLast? = some k) :
    HCFInv prof { s with stack :=
      { problem := frame.problem, exception := k, stage := .init,
        pendingRemaining := frame.problem.remainingPrefs a } ::
      { frame with
        stage := .awaitingChild,
        pendingRemaining := frame.problem.remainingPrefs a } :: rest } := by
  have hframe : frame.Inv prof := h.frames frame (by simp [hstack])
  have hkfresh : k ∉ frame.problem.forcedMoves :=
    decide_getLast_fresh hframe hstage hlast
  have hkpool : k ∈ insert ∅ (originalCoalitions prof) :=
    Finset.mem_insert_of_mem
      (hframe.fromPool.outProposals a k (mem_of_getLast?_eq_some hlast))
  have hcard : frame.problem.forcedMoves.card < coalitionBound prof :=
    card_forced_lt_of_fresh hframe.fromPool hkpool hkfresh
  constructor
  · intro f hf
    rcases List.mem_cons.mp hf with hf | hf
    · subst hf
      exact ⟨hframe.proposalsForced, fun hc => by simp at hc,
        hframe.budgetBounded,
        ⟨hframe.fromPool.preferences, hframe.fromPool.outProposals,
         hframe.fromPool.forcedMoves, hkpool⟩,
        fun _ => hkfresh, fun hc => by simp at hc⟩
    · rcases List.mem_cons.mp hf with hf | hf
      · subst hf
        exact ⟨hframe.proposalsForced, fun hc => by simp at hc,
          hframe.budgetBounded,
          ⟨hframe.fromPool.preferences, hframe.fromPool.outProposals,
           hframe.fromPool.forcedMoves, hframe.fromPool.exception⟩,
          fun hc => by simp at hc, fun _ => ⟨a, rfl, hrem⟩⟩
      · exact h.frames f (by rw [hstack]; exact List.mem_cons_of_mem _ hf)
  · have hchain := h.posDescending
    rw [hstack, List.isChain_cons] at hchain
    have hpos_parent : ({ frame with
        stage := .awaitingChild,
        pendingRemaining := frame.problem.remainingPrefs a }
        : HCFFrame α).pos prof = frame.pos prof := by
      simp [HCFFrame.pos, HCFFrame.slack, hstage]
    refine List.isChain_cons.mpr ⟨?_, List.isChain_cons.mpr
      ⟨fun b hb => hpos_parent ▸ hchain.1 b hb, hchain.2⟩⟩
    intro b hb
    simp only [List.head?_cons, Option.mem_some_iff] at hb
    subst hb
    simp only [HCFFrame.pos, HCFFrame.slack]
    simp
    omega

/-- Bundle preservation across the `awaitingChild`-`none` eliminate: the
    child failed, so the parent eliminates its frozen `pendingRemaining`
    and returns to `phase1`. `eliminate` is a trim, so every conjunct
    transports; `forcedMoves` is untouched, so positions are unchanged. -/
theorem hcfInv_awaiting_eliminate {prof : PreferenceProfile α}
    {s : HCFState α} {frame : HCFFrame α} {rest : List (HCFFrame α)}
    (h : HCFInv prof s) (hstack : s.stack = frame :: rest)
    (hstage : frame.stage = .awaitingChild) :
    HCFInv prof
      { stack := { frame with
          problem := eliminate frame.problem frame.pendingRemaining.toFinset,
          stage := .phase1 } :: rest,
        last := none } := by
  have hframe : frame.Inv prof := h.frames frame (by simp [hstack])
  have hE := eliminate_trimsTo frame.problem frame.pendingRemaining.toFinset
  constructor
  · intro f hf
    rcases List.mem_cons.mp hf with hf | hf
    · subst hf
      refine ⟨?_, fun hc => by simp at hc, ?_, ⟨?_, ?_, ?_, ?_⟩,
        fun hc => by simp at hc, fun hc => by simp at hc⟩
      · intro x P hP
        rw [hE.forcedMoves]
        exact hframe.proposalsForced x P (hE.outDropLast x P hP)
      · calc (eliminate frame.problem frame.pendingRemaining.toFinset).budget
            ≤ frame.problem.budget := Finset.sum_le_sum fun x _ => hE.remaining x
          _ ≤ ∑ x, (prof x).length := hframe.budgetBounded
      · exact fun x P hP =>
          hframe.fromPool.preferences x P (hE.preferences x P hP)
      · exact fun x P hP =>
          hframe.fromPool.outProposals x P (hE.outProposals x P hP)
      · rw [hE.forcedMoves]
        exact hframe.fromPool.forcedMoves
      · exact hframe.fromPool.exception
    · exact h.frames f (by rw [hstack]; exact List.mem_cons_of_mem _ hf)
  · have hpos : ({ frame with
        problem := eliminate frame.problem frame.pendingRemaining.toFinset,
        stage := .phase1 } : HCFFrame α).pos prof = frame.pos prof := by
      simp [HCFFrame.pos, HCFFrame.slack, hE.forcedMoves, hstage]
    have hchain := h.posDescending
    rw [hstack, List.isChain_cons] at hchain
    exact List.isChain_cons.mpr
      ⟨fun b hb => hpos ▸ hchain.1 b hb, hchain.2⟩

/-- The assembled brick-4 preservation theorem: one `step` preserves the
    bundled run invariant. Case analysis mirrors `step`'s match tree; each
    branch is one of the per-transition lemmas, with the `firstAgent` /
    `find?` guards converted to the pointwise facts they consume. -/
theorem hcfInv_step [LinearOrder α] {prof : PreferenceProfile α}
    {s : HCFState α} (h : HCFInv prof s) : HCFInv prof (step s) := by
  rcases hstack : s.stack with _ | ⟨frame, rest⟩
  · simpa [step, hstack] using h
  · cases hstage : frame.stage with
    | init =>
      simp only [step, hstack, hstage]
      exact hcfInv_init_phase1 h hstack hstage
    | phase1 =>
      rcases hfa : firstAgent (fun a => !frame.problem.hasValidProposal a)
        with _ | a
      · simp only [step, hstack, hstage, hfa]
        refine hcfInv_phase1_decide h hstack hstage fun x => ?_
        have hx := firstAgent_eq_none hfa x
        simpa using hx
      · rcases htop : frame.problem.topUnproposed a with _ | G
        · simp only [step, hstack, hstage, hfa, htop]
          exact hcfInv_popWith h _
        · simp only [step, hstack, hstage, hfa, htop]
          rw [← hstage]
          refine hcfInv_phase1_broadcast h hstack hstage ?_ htop
          simp only [firstAgent] at hfa
          have hx := List.find?_some hfa
          simpa using hx
    | decide =>
      rcases hsol : frame.problem.solution with _ | g
      · rcases hfa : firstAgent
            (fun a => !(frame.problem.remainingPrefs a).isEmpty) with _ | a
        · simp only [step, hstack, hstage, hsol, hfa]
          exact hcfInv_popWith h _
        · rcases hgl : (frame.problem.outProposals a).getLast? with _ | k
          · simp only [step, hstack, hstage, hsol, hfa, hgl]
            exact hcfInv_popWith h _
          · simp only [step, hstack, hstage, hsol, hfa, hgl]
            refine hcfInv_decide_push h hstack hstage ?_ hgl
            simp only [firstAgent] at hfa
            have hx := List.find?_some hfa
            simpa using hx
      · simp only [step, hstack, hstage, hsol]
        exact hcfInv_popWith h _
    | awaitingChild =>
      rcases hlast : s.last with _ | p
      · simp only [step, hstack, hstage, hlast]
        exact hcfInv_awaiting_eliminate h hstack hstage
      · simp only [step, hstack, hstage, hlast]
        exact hcfInv_popWith h _

/-! ## Strict measure decrease

Campaign brick 5: from any invariant-satisfying, non-terminated state, one
`step` strictly decreases `slackMeasure`. Head-rewriting transitions drop
their head term (value and/or position), a push is paid by the parent's
stage drop at a strictly higher position, and a pop deletes a positive
term. -/

/-- The broadcast cascade never touches `forcedMoves`. -/
theorem broadcastProposal_forcedMoves [LinearOrder α] (p : HCFProblem α)
    (a : α) (G : Finset α) :
    (broadcastProposal p a G).forcedMoves = p.forcedMoves := by
  set p' : HCFProblem α := { p with outProposals :=
      fun x => if x = a then (p.outProposals x ++ [G]) else p.outProposals x }
    with hp'
  have hT : p'.TrimsTo (broadcastProposal p a G) :=
    foldl_receiveProposal_trimsTo G a _ p'
  rw [hT.forcedMoves]

/-- A broadcast strictly shrinks the budget: proposing `G` removes it from
    the pivot's remaining preferences (it was ranked and unproposed), no
    other agent's remaining count grows on the append, and the cascade only
    trims further. This is the payment for every `phase1` proposal step. -/
theorem broadcastProposal_budget_lt [LinearOrder α] (p : HCFProblem α)
    (a : α) (G : Finset α) (hGpref : G ∈ p.preferences a)
    (hGnew : G ∉ p.outProposals a) :
    (broadcastProposal p a G).budget < p.budget := by
  set p' : HCFProblem α := { p with outProposals :=
      fun x => if x = a then (p.outProposals x ++ [G]) else p.outProposals x }
    with hp'
  have hT : p'.TrimsTo (broadcastProposal p a G) :=
    foldl_receiveProposal_trimsTo G a _ p'
  have hprefs : ∀ x : α, p'.preferences x = p.preferences x := by
    intro x; simp [hp']
  have houts_a : p'.outProposals a = p.outProposals a ++ [G] := by
    simp [hp']
  have houts_ne : ∀ x : α, x ≠ a → p'.outProposals x = p.outProposals x := by
    intro x hx; simp [hp', hx]
  have hsub : List.Sublist (p'.remainingPrefs a) (p.remainingPrefs a) := by
    simp only [HCFProblem.remainingPrefs, hprefs, houts_a]
    refine List.monotone_filter_right _ ?_
    intro C hC
    simp only [decide_eq_true_eq, List.mem_append] at hC ⊢
    exact fun hmem => hC (Or.inl hmem)
  have hle : ∀ x : α,
      (p'.remainingPrefs x).length ≤ (p.remainingPrefs x).length := by
    intro x
    by_cases hx : x = a
    · rw [hx]; exact hsub.length_le
    · simp only [HCFProblem.remainingPrefs, hprefs, houts_ne x hx]
      exact le_rfl
  have hstrict : (p'.remainingPrefs a).length < (p.remainingPrefs a).length := by
    refine lt_of_le_of_ne hsub.length_le fun heq => ?_
    have heql : p'.remainingPrefs a = p.remainingPrefs a :=
      hsub.eq_of_length heq
    have hGrem : G ∈ p.remainingPrefs a :=
      List.mem_filter.mpr ⟨hGpref, by simpa using hGnew⟩
    rw [← heql] at hGrem
    have hG2 := (List.mem_filter.mp hGrem).2
    rw [houts_a] at hG2
    simp at hG2
  calc (broadcastProposal p a G).budget
      ≤ p'.budget := Finset.sum_le_sum fun x _ => hT.remaining x
    _ < p.budget := Finset.sum_lt_sum (fun x _ => hle x)
        ⟨a, Finset.mem_univ a, hstrict⟩

/-- Eliminating a pivot's (nonempty) remaining preferences strictly shrinks
    the budget: the pivot's remaining list empties outright — a preference
    entry surviving the removal filter was already shadowed by a proposal,
    and its shadow survives the same filter. This is the payment for the
    `awaitingChild`-`none` eliminate. -/
theorem eliminate_pending_budget_lt (p : HCFProblem α) (a : α)
    (hne : p.remainingPrefs a ≠ []) :
    (eliminate p (p.remainingPrefs a).toFinset).budget < p.budget := by
  have hE := eliminate_trimsTo p (p.remainingPrefs a).toFinset
  have hnil :
      (eliminate p (p.remainingPrefs a).toFinset).remainingPrefs a = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro C hC
    obtain ⟨hCp, hCnot⟩ := List.mem_filter.mp hC
    obtain ⟨hCpp, hCr⟩ := List.mem_filter.mp hCp
    have hCrem : C ∉ p.remainingPrefs a := by
      intro hmem
      have hCr' : C ∉ (p.remainingPrefs a).toFinset := by simpa using hCr
      exact hCr' (List.mem_toFinset.mpr hmem)
    have hCout : C ∈ p.outProposals a := by
      by_contra hno
      exact hCrem (List.mem_filter.mpr ⟨hCpp, by simpa using hno⟩)
    have hCnot' : C ∉ p.outProposals a ∨ C ∈ p.remainingPrefs a := by
      simpa [eliminate] using hCnot
    rcases hCnot' with hno | hyes
    · exact hno hCout
    · exact hCrem hyes
  refine Finset.sum_lt_sum (fun x _ => hE.remaining x)
    ⟨a, Finset.mem_univ a, ?_⟩
  rw [hnil]
  simp only [List.length_nil]
  exact Nat.pos_of_ne_zero fun h0 => hne (List.length_eq_zero_iff.mp h0)

private theorem term_lt_term {C v' v p' p : ℕ} (hC : 0 < C)
    (hv : v' < v) (hp : p' ≤ p) : v' * C ^ p' < v * C ^ p :=
  lt_of_le_of_lt (Nat.mul_le_mul (le_refl v') (Nat.pow_le_pow_right hC hp))
    (mul_lt_mul_of_pos_right hv (pow_pos hC p))

/-- The push arithmetic: a child worth `vc < C` entering one position below
    is dominated by the parent's one-unit value drop at the full position. -/
private theorem push_sum_lt {C vc vp vf pc pf : ℕ} (hC : 0 < C)
    (hvpf : vp + 1 = vf) (hpc : pc + 1 = pf) (hvc : vc < C) :
    vc * C ^ pc + vp * C ^ pf < vf * C ^ pf := by
  have hX : 0 < C ^ pc := pow_pos hC pc
  have h1 : vc * C ^ pc < C ^ pf := by
    rw [← hpc, pow_succ]
    calc vc * C ^ pc < C * C ^ pc := mul_lt_mul_of_pos_right hvc hX
      _ = C ^ pc * C := Nat.mul_comm _ _
  calc vc * C ^ pc + vp * C ^ pf
      < C ^ pf + vp * C ^ pf := Nat.add_lt_add_right h1 _
    _ = vf * C ^ pf := by rw [← hvpf]; ring

/-- Popping the top frame strictly decreases the measure: every frame's
    contribution is positive. Covers all five `popWith` transitions. -/
theorem slackMeasure_tail_lt {prof : PreferenceProfile α} {s : HCFState α}
    {frame : HCFFrame α} {rest : List (HCFFrame α)}
    (hstack : s.stack = frame :: rest) (r : Option (HCFProblem α)) :
    (popWith s r).slackMeasure prof < s.slackMeasure prof := by
  simp only [HCFState.slackMeasure, popWith, hstack, List.tail_cons,
    List.map_cons, List.sum_cons]
  have hterm : 0 < frame.value * measureBase prof ^ frame.pos prof :=
    Nat.mul_pos (by unfold HCFFrame.value; omega)
      (pow_pos (by unfold measureBase; omega) _)
  omega

/-- Brick 5 — the strict-decrease keystone: from any invariant-satisfying,
    non-terminated state, one `step` strictly decreases the slack-hierarchy
    measure. -/
theorem slackMeasure_step_lt [LinearOrder α] {prof : PreferenceProfile α}
    {s : HCFState α} (h : HCFInv prof s) (hne : s.stack ≠ []) :
    (step s).slackMeasure prof < s.slackMeasure prof := by
  rcases hstack : s.stack with _ | ⟨frame, rest⟩
  · exact absurd hstack hne
  have hframe : frame.Inv prof := h.frames frame (by simp [hstack])
  have hC : 0 < measureBase prof := by unfold measureBase; omega
  cases hstage : frame.stage with
  | init =>
    simp only [step, hstack, hstage]
    simp only [HCFState.slackMeasure, hstack, List.map_cons, List.sum_cons]
    refine Nat.add_lt_add_right ?_ _
    have hcard : frame.problem.forcedMoves.card < coalitionBound prof :=
      card_forced_lt_of_fresh hframe.fromPool hframe.fromPool.exception
        (hframe.initFresh hstage)
    have hcins : (insert frame.exception frame.problem.forcedMoves).card
        = frame.problem.forcedMoves.card + 1 :=
      Finset.card_insert_of_notMem (hframe.initFresh hstage)
    have hbudg : ({ frame.problem with forcedMoves := insert frame.exception frame.problem.forcedMoves } : HCFProblem α).budget = frame.problem.budget := rfl
    refine term_lt_term hC ?_ ?_
    · simp only [HCFFrame.value, hbudg, hstage, Stage.weight]
      omega
    · simp [HCFFrame.pos, HCFFrame.slack, hstage, hcins]
      omega
  | phase1 =>
    rcases hfa : firstAgent (fun a => !frame.problem.hasValidProposal a)
      with _ | a
    · simp only [step, hstack, hstage, hfa]
      simp only [HCFState.slackMeasure, hstack, List.map_cons, List.sum_cons]
      refine Nat.add_lt_add_right ?_ _
      refine term_lt_term hC ?_ ?_
      · simp only [HCFFrame.value, hstage, Stage.weight]
        omega
      · exact le_of_eq (by simp [HCFFrame.pos, HCFFrame.slack, hstage])
    · rcases htop : frame.problem.topUnproposed a with _ | G
      · simp only [step, hstack, hstage, hfa, htop]
        exact slackMeasure_tail_lt hstack _
      · simp only [step, hstack, hstage, hfa, htop]
        simp only [HCFState.slackMeasure, hstack, List.map_cons, List.sum_cons]
        refine Nat.add_lt_add_right ?_ _
        have hfind : List.find?
            (fun C => decide (C ∉ frame.problem.outProposals a))
            (frame.problem.preferences a) = some G := by
          simpa [HCFProblem.topUnproposed] using htop
        have hGmem : G ∈ frame.problem.preferences a :=
          List.mem_of_find?_eq_some hfind
        have hGnew : G ∉ frame.problem.outProposals a := by
          have hx := List.find?_some hfind
          simpa using hx
        have hB := broadcastProposal_budget_lt frame.problem a G hGmem hGnew
        have hforced := broadcastProposal_forcedMoves frame.problem a G
        refine term_lt_term hC ?_ ?_
        · simp only [HCFFrame.value, hstage, Stage.weight]
          omega
        · exact le_of_eq
            (by simp [HCFFrame.pos, HCFFrame.slack, hforced, hstage])
  | decide =>
    rcases hsol : frame.problem.solution with _ | g
    · rcases hfa : firstAgent
          (fun a => !(frame.problem.remainingPrefs a).isEmpty) with _ | a
      · simp only [step, hstack, hstage, hsol, hfa]
        exact slackMeasure_tail_lt hstack _
      · rcases hgl : (frame.problem.outProposals a).getLast? with _ | k
        · simp only [step, hstack, hstage, hsol, hfa, hgl]
          exact slackMeasure_tail_lt hstack _
        · simp only [step, hstack, hstage, hsol, hfa, hgl]
          simp only [HCFState.slackMeasure, hstack, List.map_cons,
            List.sum_cons]
          rw [← Nat.add_assoc]
          refine Nat.add_lt_add_right ?_ _
          have hkfresh : k ∉ frame.problem.forcedMoves :=
            decide_getLast_fresh hframe hstage hgl
          have hkpool : k ∈ insert ∅ (originalCoalitions prof) :=
            Finset.mem_insert_of_mem
              (hframe.fromPool.outProposals a k (mem_of_getLast?_eq_some hgl))
          have hcard : frame.problem.forcedMoves.card < coalitionBound prof :=
            card_forced_lt_of_fresh hframe.fromPool hkpool hkfresh
          have hpp : ({ frame with
              stage := .awaitingChild,
              pendingRemaining := frame.problem.remainingPrefs a }
              : HCFFrame α).pos prof = frame.pos prof := by
            simp [HCFFrame.pos, HCFFrame.slack, hstage]
          rw [hpp]
          refine push_sum_lt hC ?_ ?_ ?_
          · simp only [HCFFrame.value, hstage, Stage.weight]
          · simp [HCFFrame.pos, HCFFrame.slack, hstage]
            omega
          · have hbb := hframe.budgetBounded
            simp only [HCFFrame.value, Stage.weight, measureBase]
            omega
    · simp only [step, hstack, hstage, hsol]
      exact slackMeasure_tail_lt hstack _
  | awaitingChild =>
    rcases hlast : s.last with _ | p
    · simp only [step, hstack, hstage, hlast]
      simp only [HCFState.slackMeasure, hstack, List.map_cons, List.sum_cons]
      refine Nat.add_lt_add_right ?_ _
      obtain ⟨a, hpend, hpne⟩ := hframe.awaitingPending hstage
      have hB : (eliminate frame.problem frame.pendingRemaining.toFinset).budget
          < frame.problem.budget := by
        rw [hpend]
        exact eliminate_pending_budget_lt frame.problem a (hpend ▸ hpne)
      have hfe :=
        (eliminate_trimsTo frame.problem frame.pendingRemaining.toFinset).forcedMoves
      refine term_lt_term hC ?_ ?_
      · simp only [HCFFrame.value, hstage, Stage.weight]
        omega
      · exact le_of_eq
          (by simp [HCFFrame.pos, HCFFrame.slack, hfe, hstage])
    · simp only [step, hstack, hstage, hlast]
      exact slackMeasure_tail_lt hstack _

/-- Run `step` until the stack empties or `fuel` is exhausted. Structural
    recursion on `fuel`, so it needs no termination proof; the well-founded
    `run` (for the proven `hcfGrouping`) is its counterpart. -/
def runFuel [LinearOrder α] : Nat → HCFState α → HCFState α
  | 0,     s => s
  | n + 1, s => if s.stack.isEmpty then s else runFuel n (step s)

/-- Execute HCF on `prof` with a fuel budget. `none` = no stable grouping;
    callers must pass a sufficient budget (fuel exhaustion is handled at the
    CLI boundary, not conflated with "no solution" here). -/
def hcfRunFuel [LinearOrder α] (prof : PreferenceProfile α) (fuel : Nat) :
    Option (Grouping α) :=
  ((runFuel fuel (HCFState.init prof)).last).bind HCFProblem.solution

/-! ## Top-level interface -/

/-- Run `step` to termination, threading the run invariant. Well-founded
    on the slack-hierarchy measure: `hcfInv_step` re-establishes the bundle
    after every step and `slackMeasure_step_lt` strictly decreases `M` at
    every non-terminated invariant-satisfying state. -/
def HCFState.run [LinearOrder α] (prof : PreferenceProfile α)
    (s : HCFState α) (hinv : HCFInv prof s) : HCFState α :=
  if hstop : s.stack = [] then s
  else HCFState.run prof (step s) (hcfInv_step hinv)
termination_by s.slackMeasure prof
decreasing_by exact slackMeasure_step_lt hinv hstop

/-- Final grouping after running HCF on `prof`; `none` = no stable
    grouping. Extracted from the terminal state of the invariant-carrying
    well-founded `run`, mirroring the fuel-driven `hcfRunFuel`. -/
def hcfGrouping [LinearOrder α] (prof : PreferenceProfile α) :
    Option (Grouping α) :=
  ((HCFState.run prof (HCFState.init prof) (hcfInv_init prof)).last).bind
    HCFProblem.solution

/-- **Partial correctness: any grouping HCF returns is core-stable.** -/
theorem hcf_coreStable [LinearOrder α] (prof : PreferenceProfile α)
    (_hvalid : IsValidProfile prof) {g : Grouping α}
    (_hsome : hcfGrouping prof = some g) : CoreStable prof g := by
  sorry

end HedonicGrouping.Algorithms.HCF
