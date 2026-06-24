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

/-- Final grouping after running HCF on `prof`. Stubbed until termination
    of `step` (with an explicit measure) is established. -/
def hcfGrouping (prof : PreferenceProfile α) : Grouping α :=
  fun a => {a}  -- TODO: extract from terminal HCFState.

/-- **HCF produces a core-stable grouping for every HCP instance.** -/
theorem hcf_coreStable (prof : PreferenceProfile α) (_hvalid : IsValidProfile prof) :
    CoreStable prof (hcfGrouping prof) := by
  sorry

end HedonicGrouping.Algorithms.HCF
