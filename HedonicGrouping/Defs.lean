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
def PreferenceProfile (β : Type*) := β → List (Finset β)

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

/-! ### Size-2 pair utilities

Under `SizeTwo` restrictions, coalitions are pairs `{a, b}`. These utilities
extract the partner and define partner-level preferences, avoiding repeated
`Finset.card_eq_two` deconstructions throughout the GS and Irving proofs.
-/

/-- Extract the other member of a size-2 coalition containing `a`. -/
noncomputable def pairPartner (a : α) (G : Finset α) : α :=
  ((G.erase a).toList.head?.getD a)

private lemma erase_nonempty_of_card_two {a : α} {G : Finset α}
    (ha : a ∈ G) (hcard : G.card = 2) : (G.erase a).Nonempty :=
  Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha, hcard]; omega)

private lemma erase_toList_ne_nil {a : α} {G : Finset α}
    (ha : a ∈ G) (hcard : G.card = 2) : (G.erase a).toList ≠ [] :=
  Finset.Nonempty.toList_ne_nil (erase_nonempty_of_card_two ha hcard)

lemma pairPartner_mem {a : α} {G : Finset α} (ha : a ∈ G) (hcard : G.card = 2) :
    pairPartner a G ∈ G := by
  unfold pairPartner
  have hne := erase_toList_ne_nil ha hcard
  rw [List.head?_eq_some_head hne, Option.getD_some]
  have := List.head_mem hne
  exact Finset.mem_of_mem_erase (Finset.mem_toList.mp this)

lemma pairPartner_ne {a : α} {G : Finset α} (ha : a ∈ G) (hcard : G.card = 2) :
    pairPartner a G ≠ a := by
  unfold pairPartner
  have hne := erase_toList_ne_nil ha hcard
  rw [List.head?_eq_some_head hne, Option.getD_some]
  intro heq
  have := List.head_mem hne
  have hmem := Finset.mem_toList.mp this
  rw [Finset.mem_erase] at hmem
  exact hmem.1 heq

/-- Agent `a` prefers partner `b` to partner `c`:
    `{a, b}` appears before `{a, c}` in `a`'s preference list. -/
def PrefersPartner (prof : PreferenceProfile α) (a b c : α) : Prop :=
  Ranks prof a {a, b} {a, c}

/-! ### Bipartite structure

A partition of agents into two sides (proposers/receivers in GS). Defined here
rather than in GaleShapley.lean so that Stability.lean can reference it without
duplication.
-/

/-- A bipartite partition of agents into two sides. -/
structure BipartiteStructure (α : Type*) where
  isMen : α → Bool

def BipartiteStructure.isWomen (bp : BipartiteStructure α) (a : α) : Bool :=
  !bp.isMen a

/-- Every preferred coalition is cross-partition: in any size-2 pair,
    one member is from each side. -/
def BipartitePref (bp : BipartiteStructure α) (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ G ∈ prof a, ∀ b ∈ G, ∀ c ∈ G, b ≠ c → bp.isMen b ≠ bp.isMen c

/-! ### Irving reduced table definitions

Definitions for Irving's Phase 1 output and Phase 2 analysis. Moved here from
Stability.lean so that Irving.lean can reference them directly.
-/

/-- Phase 1 duality: `first(b) = a → last(a) = b` in the reduced table.

    After Simplified Reduction, if `a` is the first entry on `b`'s reduced
    list (meaning `b` is currently proposing to `a`), then `b` is the last
    entry on `a`'s list (the least-preferred remaining option for `a`). -/
def Phase1Duality (reduced : α → List α) : Prop :=
  ∀ a b : α, (reduced a).head? = some b →
    (reduced b).length > 0 ∧ (reduced b).getLastD b = a

/-- All reduced lists have length 1: each agent has exactly one remaining
    partner. Termination condition for Irving's Phase 2. -/
def AllSingleton (reduced : α → List α) : Prop :=
  ∀ a : α, (reduced a).length = 1

/-- Extract the matching implied by a singleton reduced table. -/
noncomputable def singletonMatching (reduced : α → List α) : Grouping α :=
  fun a => {a, ((reduced a).head?.getD a)}

/-- Total list lengths — termination measure for Phase 2. -/
noncomputable def totalLength [Fintype α] (reduced : α → List α) : ℕ :=
  Finset.univ.sum fun a => (reduced a).length

/-- Blocking pair: both agents strictly prefer being together
    to their current assignment. Under size-2 preferences, this is the
    only form of blocking coalition. -/
def BlockingPair (prof : PreferenceProfile α) (μ : Grouping α) (a b : α) : Prop :=
  a ≠ b ∧ Ranks prof a {a, b} (μ a) ∧ Ranks prof b {a, b} (μ b)

/-- Pairwise stability: no blocking pair exists. -/
def PairwiseStable (prof : PreferenceProfile α) (μ : Grouping α) : Prop :=
  ∀ a b : α, ¬ BlockingPair prof μ a b

/-! ### Core stability ↔ Pairwise stability (size-2)

Under size-2 preferences, every blocking coalition is a pair, so core
stability and pairwise stability coincide. This bridge is used by both
the GS and Irving proofs. -/

/-- Under size-2 preferences, any blocking coalition has exactly 2 members. -/
lemma blocking_coalition_sizeTwo
    (prof : PreferenceProfile α) (μ : Grouping α) (S : Finset α)
    (hsize : SizeTwo prof)
    (hblock : BlockingCoalition prof μ S) :
    S.card = 2 := by
  obtain ⟨_, hpref⟩ := hblock
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨i, _, _, hi, _⟩ := hpref a ha
  exact hsize a S (hi ▸ List.getElem_mem (by exact i.isLt))

/-- **Core stability equals pairwise stability under size-2 preferences.** -/
theorem coreStable_iff_pairwiseStable
    (prof : PreferenceProfile α) (μ : Grouping α)
    (hsize : SizeTwo prof) :
    CoreStable prof μ ↔ PairwiseStable prof μ := by
  constructor
  · intro hcore a b hbp
    obtain ⟨hab, ha_ranks, hb_ranks⟩ := hbp
    apply hcore {a, b}
    refine ⟨by simp [Finset.card_pair hab], fun x hx => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    cases hx with
    | inl h => subst h; exact ha_ranks
    | inr h => subst h; exact hb_ranks
  · intro hpair S hblock
    have hcard := blocking_coalition_sizeTwo prof μ S hsize hblock
    obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hcard
    subst hS
    exact hpair a b ⟨hab, hblock.2 a (Finset.mem_insert_self a {b}),
      hblock.2 b (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))⟩

/-! ### College Admissions — Factored / Responsive Preferences (Roth 1985)

Students rank colleges; colleges rank individual students. Coalition
preferences are *derived*: a student is indifferent between coalitions
sharing the same college, and a college's preference over student groups
is responsive to its ranking of individual students.
-/

/-- College admissions instance. -/
structure CollegeAdmissions (α : Type*) [DecidableEq α] where
  isCollege : α → Bool
  quota : α → ℕ
  studentRanking : α → List α  -- students rank colleges
  collegeRanking : α → List α  -- colleges rank individual students

/-- A student's preference class: the college in the coalition (if any). -/
noncomputable def CollegeAdmissions.studentClass (ca : CollegeAdmissions α) (_a : α)
    (G : Finset α) : Option α :=
  (G.filter (fun x => ca.isCollege x = true)).toList.head?

/-- Responsive preference: college `c` prefers group `G` to group `H` if the
    *worst* student in `G` (according to `collegeRanking c`) is better than the
    worst student in `H`, breaking ties by group size. This captures the standard
    responsive extension from individual rankings to subset rankings. -/
def ResponsivePreference (ca : CollegeAdmissions α) (c : α) (G H : Finset α) : Prop :=
  let studentsG := G.filter (fun x => ca.isCollege x = false)
  let studentsH := H.filter (fun x => ca.isCollege x = false)
  studentsG.card ≥ studentsH.card ∧
  ∀ s ∈ studentsG, ∃ t ∈ studentsH,
    let ranking := ca.collegeRanking c
    ∃ (i : ℕ) (j : ℕ), ranking[i]? = some s ∧ ranking[j]? = some t ∧ i ≤ j

end HedonicGrouping.Defs
