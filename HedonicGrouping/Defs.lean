import Mathlib

namespace HedonicGrouping.Defs
/-!
# Hedonic Grouping — Core Definitions

This file introduces the basic objects for the thesis formalization:

- agents,
- preference profiles as strict orderings of admissible coalitions,
- proposal state,
- blocking coalitions,
- core stability,
- and a raw grouping map.

The raw data here is intentionally lightweight.
Well-formedness conditions, such as "the preference list contains exactly the
admissible coalitions for each agent" and "the grouping is a genuine partition",
are stated separately as predicates.
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/--
`PreferenceProfile α` assigns to each agent a list of coalitions, ordered from
most preferred to least preferred.

The intended interpretation is that this list is a strict ranking with no
duplicates; validity is expressed separately.
-/
def PreferenceProfile (α : Type*) := α → List (Finset α)

/--
`Ranks prof a G H` means that agent `a` strictly prefers coalition `G` to
coalition `H`, i.e. `G` appears before `H` in the preference list `prof a`.
-/
def Ranks (prof : PreferenceProfile α) (a : α) (G H : Finset α) : Prop :=
  ∃ i j : Fin (prof a).length, i < j ∧ (prof a)[i] = G ∧ (prof a)[j] = H

/--
A raw grouping assigns to each agent the coalition it belongs to.

This is not yet required to be a genuine partition. In particular, additional
validity conditions will later enforce:
- every agent is assigned,
- coalition membership is coherent,
- coalitions are disjoint.
-/
def Grouping (α : Type*) := α → Finset α

/--
`Considerable G a prop` means that, under the current proposal map `prop`,
every member of coalition `G` other than `a` is currently proposing `G`.

Here `prop b = none` means that agent `b` is not currently proposing anything.
-/
def Considerable (G : Finset α) (a : α) (prop : α → Option (Finset α)) : Prop :=
  ∀ b ∈ G, b ≠ a → prop b = some G

/--
`BlockingCoalition prof μ S` means that coalition `S` blocks the grouping `μ`.

The coalition must have at least two members, and every member `a ∈ S`
strictly prefers the coalition obtained by removing `a` from `S`
to their current assigned coalition `μ a`.
-/
def BlockingCoalition (prof : PreferenceProfile α) (μ : Grouping α) (S : Finset α) : Prop :=
  S.card ≥ 2 ∧
  ∀ a ∈ S, Ranks prof a (S.erase a) (μ a)

/--
A grouping is core-stable if no blocking coalition exists.
-/
def CoreStable (prof : PreferenceProfile α) (μ : Grouping α) : Prop :=
  ∀ S : Finset α, ¬ BlockingCoalition prof μ S

/-
Validity predicates
-/

/--
`IsAdmissibleCoalition a G` means that coalition `G` is one that agent `a`
could actually belong to.
For the current formalization, that simply means `a ∈ G`.
-/
def IsAdmissibleCoalition (a : α) (G : Finset α) : Prop :=
  a ∈ G

/--
`IsValidProfile prof` means that for every agent `a`:

- the list `prof a` contains no duplicates,
- every listed coalition contains `a`,
- and the list is intended to represent the complete strict ranking of all
  admissible coalitions.

The "complete ranking" part will usually be made precise later, depending on the
exact coalition domain you choose.
-/
def IsValidProfile (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, (prof a).Nodup ∧ ∀ G ∈ prof a, IsAdmissibleCoalition a G

/--
`IsValidGrouping μ` means that `μ` is a genuine partition of the agent set.

This will later be expanded to require:
- coverage,
- disjointness,
- and coherence of the map `μ`.
-/
def IsValidGrouping (μ : Grouping α) : Prop :=
  ∀ a : α, a ∈ μ a

/--
`SizeTwo prof` means every coalition in every agent's preference list has exactly
two members — the setting for classical matching problems.
-/
def SizeTwo (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ G ∈ prof a, G.card = 2

end HedonicGrouping.Defs
