import Mathlib
import HedonicGrouping.Algorithms.HCF
import Lean.Data.Json

namespace HedonicGrouping.Exec
/-!
# Executable CLI glue for HCF

Not a verified object — pure I/O glue around the computable `HCF` core.
Reads a JSON instance on stdin, runs `runFuel`, prints the grouping (or
`null`). The agent ↔ `Fin n` map is positional (index = position in the
input `agents` array), so `Fin n` numeric order matches the Python
oracle's list order.

Schema in:  `{ "agents": ["a1",…], "prefs": { "a1": [["a1","a2"],…], … } }`
Schema out: `{ "a1": ["a1","a2"], … }` (members sorted) or `null`.
-/

open Lean (Json)
open HedonicGrouping.Core
open HedonicGrouping.Algorithms.HCF

/-- Ordered agent names and, per agent (same order), coalitions as name lists. -/
structure RawInstance where
  agents : Array String
  prefs  : Array (Array (Array String))

def parseInstance (j : Json) : Except String RawInstance := do
  let agents ← (← (← j.getObjVal? "agents").getArr?).mapM (·.getStr?)
  let prefsObj ← j.getObjVal? "prefs"
  let prefs ← agents.mapM fun name => do
    let coals ← (← prefsObj.getObjVal? name).getArr?
    coals.mapM fun c => do (← c.getArr?).mapM (·.getStr?)
  pure { agents := agents, prefs := prefs }

/-- Resolve coalition member names to indices into `agents`; error on any
    unknown name (a malformed instance, not a "no solution"). -/
def resolve (inst : RawInstance) : Except String (Array (Array (Array Nat))) :=
  inst.prefs.mapM fun coals =>
    coals.mapM fun c =>
      c.mapM fun name =>
        match inst.agents.findIdx? (· == name) with
        | some k => .ok k
        | none => .error s!"unknown agent in coalition: {name}"

def toProfile (n : Nat) (prefs : Array (Array (Array Nat))) :
    PreferenceProfile (Fin n) :=
  fun i =>
    (prefs.getD i.val #[]).toList.map fun coal =>
      (coal.toList.filterMap fun k =>
        if h : k < n then some (⟨k, h⟩ : Fin n) else none).toFinset

/-- A generous, size-derived fuel bound. Exhaustion is reported as an
    error, never conflated with "no solution", so an under-estimate is a
    loud failure rather than a wrong answer. -/
def fuelBound (prefs : Array (Array (Array Nat))) : Nat :=
  let pairs := prefs.foldl (fun acc a => acc + a.size) 0
  (pairs + prefs.size + 1) ^ 3 + 1024

/-- Run HCF on a parsed instance. `Except` error = fuel exhausted (bug);
    inner `Option` = stable grouping (member-name lists, agent order) or
    none. -/
def runRaw (inst : RawInstance) : Except String (Option (Array (Array String))) := do
  let prefs ← resolve inst
  let n := inst.agents.size
  let final := runFuel (fuelBound prefs) (HCFState.init (toProfile n prefs))
  if !final.stack.isEmpty then
    .error "fuel exhausted before termination"
  else match final.last.bind HCFProblem.solution with
    | none => .ok none
    | some g => .ok (some (Array.ofFn fun i : Fin n =>
        (((g i).sort (· ≤ ·)).map fun j => inst.agents.getD j.val "").toArray))

def toJson (inst : RawInstance) (res : Option (Array (Array String))) : Json :=
  match res with
  | none => Json.null
  | some out =>
    Json.mkObj <| (inst.agents.toList.zip out.toList).map fun (name, members) =>
      (name, Json.arr (members.map Json.str))

def runCli : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input with
  | .error e => IO.eprintln s!"JSON parse error: {e}" *> pure 1
  | .ok j => match parseInstance j with
    | .error e => IO.eprintln s!"instance error: {e}" *> pure 1
    | .ok inst => match runRaw inst with
      | .error e => IO.eprintln s!"run error: {e}" *> pure 1
      | .ok res => IO.println (toJson inst res).compress *> pure 0

end HedonicGrouping.Exec
