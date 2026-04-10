import Mathlib

namespace HedonicGrouping.Defs
/-!
# Hedonic Grouping — Core Definitions (Paper §3)

Formalizes the paper's `⟨A, Ω, M⟩` framework for hedonic coalition formation:

- `A` (agents): the type `α` with `[Fintype α]`.
- `Ω` (preferences): `PreferenceProfile α` — each agent's strict ranking of
  admissible coalitions.
- `M` (matching): `Grouping α` — the assignment of each agent to a coalition.

Additional concepts:

- `Considerable`: the algorithm's acceptance condition for a proposed coalition
  (§4). This is the central mechanism that unifies Gale-Shapley and Irving.
- `BlockingCoalition` / `CoreStable`: the stability criterion — a grouping is
  core-stable iff no coalition can deviate and make all its members better off.
- `SizeTwo`: restricts to classical pairwise matching (marriage, roommates).

Well-formedness conditions (no-duplicate preferences, membership coherence,
partition validity) are stated as separate predicates rather than baked into
the types, keeping the core data lightweight.
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/--
`PreferenceProfile α` — the paper's `Ω`. Each agent maps to a list of
coalitions ordered from most preferred to least preferred (strict ranking,
no ties). Validity (no duplicates, membership) is a separate predicate
`IsValidProfile`.
-/
def PreferenceProfile (α : Type*) := α → List (Finset α)

/--
`Ranks prof a G H` — agent `a` strictly prefers coalition `G` to coalition `H`,
i.e. `G` appears before `H` in the preference list `prof a`.
-/
def Ranks (prof : PreferenceProfile α) (a : α) (G H : Finset α) : Prop :=
  ∃ i j : Fin (prof a).length, i < j ∧ (prof a)[i] = G ∧ (prof a)[j] = H

/--
`Grouping α` — the paper's `M`. Maps each agent to the coalition it belongs to.
Not yet required to be a genuine partition; `IsValidGrouping` enforces that.
-/
def Grouping (α : Type*) := α → Finset α

/--
`Considerable G a prop` — the algorithm's acceptance test (§4).

Under proposal map `prop`, coalition `G` is considerable for agent `a` iff every
other member of `G` is currently proposing `G`. This is the trigger for the
algorithm's processing phase: when a proposal becomes considerable, it is
accepted and may start a cascade of rejections (move-on chain).
-/
def Considerable (G : Finset α) (a : α) (prop : α → Option (Finset α)) : Prop :=
  ∀ b ∈ G, b ≠ a → prop b = some G

/--
`BlockingCoalition prof μ S` — coalition `S` blocks grouping `μ` (§3).

`S` blocks if `|S| ≥ 2` and every member `a ∈ S` strictly prefers `S`
to their current assignment `μ a`. Coalitions in the preference profile
include the agent (i.e. `a ∈ G` for every `G ∈ prof a`), so the comparison
is between `S` and `μ a` directly — both contain `a`.
-/
def BlockingCoalition (prof : PreferenceProfile α) (μ : Grouping α) (S : Finset α) : Prop :=
  S.card ≥ 2 ∧
  ∀ a ∈ S, Ranks prof a S (μ a)

/--
Core stability (= group stability in §3): no coalition can block the grouping.
This is the solution concept the algorithm targets.
-/
def CoreStable (prof : PreferenceProfile α) (μ : Grouping α) : Prop :=
  ∀ S : Finset α, ¬ BlockingCoalition prof μ S

/-! ### Validity predicates -/

/--
`IsAdmissibleCoalition a G` — agent `a` could belong to coalition `G`.
Currently just `a ∈ G`; could be strengthened for quota or capacity constraints.
-/
def IsAdmissibleCoalition (a : α) (G : Finset α) : Prop :=
  a ∈ G

/--
`IsValidProfile prof` — well-formedness of preferences.
Each agent's list has no duplicates and every listed coalition contains the agent.
-/
def IsValidProfile (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, (prof a).Nodup ∧ ∀ G ∈ prof a, IsAdmissibleCoalition a G

/--
`IsValidGrouping μ` — minimal well-formedness: each agent belongs to their
assigned coalition. Full partition validity (coverage, disjointness) can be added.
-/
def IsValidGrouping (μ : Grouping α) : Prop :=
  ∀ a : α, a ∈ μ a

/--
`SizeTwo prof` — all preference coalitions have exactly two members.
This restricts to classical pairwise matching: marriage (bipartite + size-2)
and stable roommates (non-bipartite + size-2). Lemmas 1 and 2 operate in
this setting.
-/
def SizeTwo (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ G ∈ prof a, G.card = 2

/-! ### Algorithm State and Operations (§4)

The algorithm operates on a mutable state tracking proposals and remaining
preferences. These definitions connect to `Considerable` (Lemma 1) and
the reduced preference table (Lemma 2). The complete imperative algorithm
is implemented in Python (`src/grouping.py`) and pseudocode
(`tex/algorithms.tex`); the Lean definitions capture the state, operations,
and cascade dynamics that the formal lemmas reference.
-/

/-- Algorithm state during execution of the Recursive Grouping (Algorithm 4).
    - `prefs`: remaining admissible coalitions per agent (shrinks via elimination)
    - `outProps`: outgoing proposals per agent (grows as agents propose)
    - `forcedMoves`: coalitions from which agents have been forced to move on -/
structure AlgState (α : Type*) [DecidableEq α] where
  prefs       : α → List (Finset α)
  outProps    : α → List (Finset α)
  forcedMoves : Finset (Finset α)

/-- Initialize algorithm state from a preference profile. -/
def AlgState.init (prof : PreferenceProfile α) : AlgState α where
  prefs := prof
  outProps := fun _ => []
  forcedMoves := {}

/-- Proposal map: each agent's currently active outgoing proposal (the most
    recent one not in `forcedMoves`). Connects `AlgState` to the
    `Considerable` predicate — `Considerable G a s.propMap` holds when all
    other members of G are actively proposing G. -/
noncomputable def AlgState.propMap (s : AlgState α) : α → Option (Finset α) :=
  fun a => ((s.outProps a).filter (· ∉ s.forcedMoves)).getLast?

/-- Reduced preference table under size-2 restriction: extracts remaining
    acceptable partners in preference order for each agent. Connects the
    algorithm state to the rotation analysis in Lemma 2. -/
noncomputable def AlgState.reducedTable (s : AlgState α) : α → List α :=
  fun a => (s.prefs a).filterMap fun G =>
    if G.card = 2 then (G.erase a).toList.head? else none

/-- Eliminate coalitions from the algorithm state. -/
noncomputable def AlgState.eliminate (s : AlgState α) (cs : List (Finset α)) :
    AlgState α where
  prefs := fun a => (s.prefs a).filter (· ∉ cs)
  outProps := fun a => (s.outProps a).filter (· ∉ cs)
  forcedMoves := s.forcedMoves

/-- Available coalitions: remaining preferences not yet proposed. -/
noncomputable def AlgState.available (s : AlgState α) (a : α) :
    List (Finset α) :=
  (s.prefs a).filter (· ∉ s.outProps a)

/-- Total remaining preferences — termination measure. Strictly decreases
    with each elimination, bounding the algorithm's computation. -/
noncomputable def AlgState.totalPrefs (s : AlgState α) : ℕ :=
  Finset.univ.sum fun a => (s.prefs a).length

/-- One step of the move-on cascade on reduced preference tables (§4).
    When agent `p` moves on from `first(p)`, they propose `second(p) = q`.
    The pair `{p, q}` is immediately considerable for `q` (size-2), so `q`
    eliminates everything below it — removing `last(q) = p_next`.
    This is the atomic operation underlying both Irving's Phase 2 rotation
    elimination and Algorithm 3's forced move-on mechanism. -/
noncomputable def cascadeStep (reduced : α → List α) (p : α) : α → List α :=
  let q := ((reduced p)[1]?).getD p
  let p_next := (reduced q).getLastD q
  fun a =>
    if a = q then (reduced a).filter (· ≠ p_next)
    else if a = p_next then (reduced a).filter (· ≠ q)
    else reduced a

end HedonicGrouping.Defs
