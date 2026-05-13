import Mathlib
import HedonicGrouping.Core
import HedonicGrouping.Problems.HCP

namespace HedonicGrouping.Algorithms.HCF
/-!
# Hedonic Coalition Formation — iterative form

Iterative reformulation of the recursive HCF: the Python prototype's
recursive call stack becomes an explicit `List HCFFrame`. Each `step`
performs one atomic action. Mirrors `src/hedonic.py::solve_iterative`.

Termination measure (for the eventual proof): `(|stack|, totalRemainingPrefs)`
decreases lexicographically — `eliminate` strictly shrinks the second
component, pushing a child strictly grows the first while the parent's
budget is preserved, popping shrinks the first.

Correctness against `CoreStable` is stated but not yet proved.
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

/-- Global iterator state: a stack of frames, the most-recently-popped
    problem (mirrors Python's `last`), and the immutable original profile
    used by the stability check inside `decide`. -/
structure HCFState (α : Type*) [DecidableEq α] where
  originalPrefs : PreferenceProfile α
  stack         : List (HCFFrame α)
  last          : Option (HCFProblem α)

def HCFState.init (prof : PreferenceProfile α) : HCFState α :=
  { originalPrefs := prof
    stack :=
      [{ problem := HCFProblem.init prof
         exception := ∅
         stage := Stage.init
         pendingRemaining := [] }]
    last := none }

/-! ## Per-frame query helpers -/

def hasValidProposal (p : HCFProblem α) (a : α) : Bool :=
  (p.outProposals a).any (fun G => decide (G ∉ p.forcedMoves))

noncomputable def topUnproposed (p : HCFProblem α) (a : α) : Option (Finset α) :=
  (p.preferences a).find? (fun G => decide (G ∉ p.outProposals a))

noncomputable def remainingPrefs (p : HCFProblem α) (a : α) : List (Finset α) :=
  (p.preferences a).filter (fun G => decide (G ∉ p.outProposals a))

/-- Latest out-proposal per agent, if all agents have proposed. -/
noncomputable def latestProposals (p : HCFProblem α) : Option (α → Finset α) :=
  if h : ∀ a, (p.outProposals a) ≠ [] then
    some (fun a => (p.outProposals a).getLast (h a))
  else none

/-- Extract a grouping from the latest proposals when they form a valid
    partition: every member of `a`'s coalition has the same coalition. -/
noncomputable def HCFProblem.solution (p : HCFProblem α) : Option (Grouping α) :=
  match latestProposals p with
  | none => none
  | some g =>
    if (Finset.univ : Finset α).toList.all
        (fun a => (g a).toList.all (fun b => decide (g b = g a))) then
      some g
    else none

/-! ## Mutators -/

/-- Filter every per-agent list to drop coalitions in `removal`. -/
noncomputable def eliminate (p : HCFProblem α) (removal : Finset (Finset α)) :
    HCFProblem α :=
  { p with
    preferences  := fun a => (p.preferences  a).filter (fun G => decide (G ∉ removal))
    outProposals := fun a => (p.outProposals a).filter (fun G => decide (G ∉ removal))
    inProposals  := fun a G => if G ∈ removal then ∅ else p.inProposals a G }

/-- Record `proposer` as having proposed `coalition` to `receiver`.

    TODO: the Python `_receive_proposal` also runs a Considerable-cascade
    eliminate (if `coalition` is now considerable, remove worse options for
    `receiver`, or eliminate `coalition` itself if a strictly-better
    considerable proposal is already held). This skeleton only records the
    proposer; the cascade will be added once the surrounding `step`
    structure is settled. -/
noncomputable def receiveProposal (p : HCFProblem α) (receiver : α)
    (coalition : Finset α) (proposer : α) : HCFProblem α :=
  { p with
    inProposals := fun a G =>
      if a = receiver ∧ G = coalition then
        insert proposer (p.inProposals a G)
      else p.inProposals a G }

/-- Broadcast a new proposal `(a, G)`: append to `a`'s out-proposals and
    record `a` as a proposer with each other member of `G`. -/
noncomputable def broadcastProposal (p : HCFProblem α) (a : α) (G : Finset α) :
    HCFProblem α :=
  let p' := { p with outProposals := fun x =>
                if x = a then p.outProposals x ++ [G] else p.outProposals x }
  (G.erase a).toList.foldl (fun acc b => receiveProposal acc b G a) p'

/-! ## Step function -/

/-- The first agent for which `pred` holds, if any. -/
noncomputable def firstAgent (pred : α → Bool) : Option α :=
  (Finset.univ : Finset α).toList.find? pred

/-- Pop the top frame, setting `last := result`. -/
def popWith (s : HCFState α) (result : Option (HCFProblem α)) : HCFState α :=
  { s with stack := s.stack.tail, last := result }

/-- One atomic step of the iterative HCF. -/
noncomputable def step (s : HCFState α) : HCFState α :=
  match s.stack with
  | [] => s
  | frame :: rest =>
    match frame.stage with
    | .init =>
      let p' := { frame.problem with
                  forcedMoves := insert frame.exception frame.problem.forcedMoves }
      { s with stack := { frame with problem := p', stage := .phase1 } :: rest }

    | .phase1 =>
      match firstAgent (fun a => !hasValidProposal frame.problem a) with
      | none =>
        { s with stack := { frame with stage := .decide } :: rest }
      | some a =>
        match topUnproposed frame.problem a with
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
        match firstAgent (fun a => !(remainingPrefs frame.problem a).isEmpty) with
        | none => popWith s (some frame.problem)
        | some a =>
          match (frame.problem.outProposals a).getLast? with
          | none => popWith s none
          | some k =>
            let child : HCFFrame α :=
              { problem := frame.problem
                exception := k
                stage := .init
                pendingRemaining := remainingPrefs frame.problem a }
            let frame' := { frame with
                            stage := .awaitingChild
                            pendingRemaining := remainingPrefs frame.problem a }
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

/-! ## Top-level interface -/

/-- Final grouping after running HCF on `prof`. Stubbed until termination
    of `step` (with an explicit measure) is established. -/
noncomputable def hcfGrouping (prof : PreferenceProfile α) : Grouping α :=
  fun a => {a}  -- TODO: extract from terminal HCFState.

/-- **HCF produces a core-stable grouping for every HCP instance.** -/
theorem hcf_coreStable (prof : PreferenceProfile α) (_hvalid : IsValidProfile prof) :
    CoreStable prof (hcfGrouping prof) := by
  sorry

end HedonicGrouping.Algorithms.HCF
