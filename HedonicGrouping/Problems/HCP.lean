import Mathlib
import HedonicGrouping.Core

namespace HedonicGrouping.Problems.HCP
/-!
# Hedonic Coalition Formation Problem

Agents rank admissible coalitions; a grouping is core-stable iff no
coalition blocks. Solved (in the novel algorithm's regime) by HCF.

`Considerable` — the acceptance test used by HCF — is defined here
because it is the definitional glue that any HCF-style proposal mechanism
plugs into. Under size-2 preferences it collapses to GS's proposal
acceptance; that bridge lives in `Unification`.
-/

open HedonicGrouping.Core

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `Considerable G a prop` — under proposal map `prop`, coalition `G` is
    considerable for `a` iff every other member of `G` is currently
    proposing `G`. -/
def Considerable (G : Finset α) (a : α) (prop : α → Option (Finset α)) : Prop :=
  ∀ b ∈ G, b ≠ a → prop b = some G

/-- Coalition `S` blocks `μ`: |S| ≥ 2 and every member strictly prefers
    `S` to their current assignment. -/
def BlockingCoalition (prof : PreferenceProfile α) (μ : Grouping α) (S : Finset α) : Prop :=
  S.card ≥ 2 ∧ ∀ a ∈ S, Ranks prof a S (μ a)

/-- Core stability: no coalition blocks. -/
def CoreStable (prof : PreferenceProfile α) (μ : Grouping α) : Prop :=
  ∀ S : Finset α, ¬ BlockingCoalition prof μ S

/-- HCP instance: a valid preference profile. Everything that validates is
    an HCP instance — the general case. -/
def IsHCP (prof : PreferenceProfile α) : Prop :=
  IsValidProfile prof

end HedonicGrouping.Problems.HCP
