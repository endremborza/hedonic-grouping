import Mathlib

/-!
# Hedonic Grouping — Core Definitions

This file introduces the basic objects used throughout the formalization:
agents, preference profiles, coalition comparison, proposal states, blocking
coalitions, and core stability.

The definitions here are intentionally lightweight. In particular:
- a preference profile is represented by an ordered list of candidate groups,
- a grouping is represented as a map from each agent to its assigned group,
- additional well-formedness conditions can be introduced separately later.
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A preference profile assigns to each agent a list of candidate groups,
ordered from most preferred to least preferred. -/
def PreferenceProfile (α : Type*) := α → List (Finset α)

/--
`Ranks prof a G H` means that agent `a` strictly prefers group `G` to group `H`.

This is encoded by saying that `G` appears earlier than `H` in the preference list
`prof a`.
-/
def Ranks (prof : PreferenceProfile α) (a : α) (G H : Finset α) : Prop :=
  ∃ i j : Fin (prof a).length, i < j ∧ (prof a)[i] = G ∧ (prof a)[j] = H

/--
A grouping assigns to each agent the group they belong to.

This is only the raw assignment map. It does not yet enforce that the groups form
a genuine partition. Those conditions should be packaged separately.
-/
def Grouping (α : Type*) := α → Finset α

/--
`Considerable G a prop` means that, under the current proposal map `prop`,
every member of `G` other than `a` is currently proposing `G`.

This is the basic "mutual support" condition used by the reduction algorithm.
-/
def Considerable (G : Finset α) (a : α) (prop : α → Option (Finset α)) : Prop :=
  ∀ b ∈ G, b ≠ a → prop b = some G

/--
`BlockingCoalition prof μ S` means that the coalition `S` blocks grouping `μ`.

The coalition must have at least two members, and every member must strictly prefer
the coalition obtained by removing themselves from `S` to their current assigned group.
-/
def BlockingCoalition (prof : PreferenceProfile α) (μ : Grouping α) (S : Finset α) : Prop :=
  S.card ≥ 2 ∧ ∀ a ∈ S, Ranks prof a (S.erase a) (μ a)

/--
A grouping is core-stable if no blocking coalition exists.
-/
def CoreStable (prof : PreferenceProfile α) (μ : Grouping α) : Prop :=
  ∀ S : Finset α, ¬ BlockingCoalition prof μ S
