import Mathlib

/-!
# Hedonic Grouping — Core Definitions

Formalizes the grouping problem: agents, preference profiles, the "considerable"
condition, core stability, and one step of the Simplified Reduction algorithm.
-/
variable {α : Type*} [DecidableEq α] [Fintype α]

-- A preference profile for agent `a`: a strict linear order on Finset α \ {a}.
-- We represent it as a list of groups in decreasing preference order.
-- `prefs a` is the ordered list of groups that `a` could belong to (excluding `a` itself).
def PreferenceProfile (α : Type*) := α → List (Finset α)

-- `ranks prof a G H` means agent `a` strictly prefers group `G` to group `H`
-- (i.e., `G` appears before `H` in `prof a`).
def ranks (prof : PreferenceProfile α) (a : α) (G H : Finset α) : Prop :=
  ∃ i j : Fin (prof a).length, i < j ∧ (prof a)[i] = G ∧ (prof a)[j] = H

-- A grouping (partition) is represented as a function assigning each agent to their group.
-- We use `Finset α` as the group type; a valid partition requires disjointness + coverage,
-- but for stability we only need the assignment function.
def Grouping (α : Type*) := α → Finset α

-- `Considerable`: group `G` is considerable for agent `a` under proposal map `prop`
-- iff every other member of `G` is currently proposing `G`.
-- `prop b` = the group that agent `b` is currently proposing (None if not proposing).
def Considerable (G : Finset α) (a : α) (prop : α → Option (Finset α)) : Prop :=
  ∀ b ∈ G, b ≠ a → prop b = some G

-- `BlockingCoalition`: a set `S` blocks grouping `μ` under preference profile `prof`
-- iff every member of `S` strictly prefers `S` (minus themselves) to their current group.
def BlockingCoalition (prof : PreferenceProfile α) (μ : Grouping α) (S : Finset α) : Prop :=
  S.card ≥ 2 ∧
  ∀ a ∈ S, ranks prof a (S.erase a) (μ a)

-- `CoreStable`: a grouping is core-stable iff no blocking coalition exists.
def CoreStable (prof : PreferenceProfile α) (μ : Grouping α) : Prop :=
  ∀ S : Finset α, ¬ BlockingCoalition prof μ S
