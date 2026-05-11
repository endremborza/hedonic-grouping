import Mathlib
import HedonicGrouping.Core

namespace HedonicGrouping.Algorithms.Common
/-!
# Common — proposal-driven algorithm substrate

The shape every proposal-driven algorithm in this development shares:
each agent has a current advocacy (`proposing`) and a history of past
advocacies (`proposed`). Both `Gale-Shapley` (β = α — pairwise) and
`Hedonic Coalition Formation` (β = Finset α — coalitions) are instances.

The only generic theorem here is `terminates_within`: monotone strict
growth of `proposedCount` against the finite cap `|α|·|β|` forces a
fixpoint within that many iterations. Algorithms supply their own step
and termination predicate; this module supplies the bound.
-/

open HedonicGrouping.Core

variable {α β : Type*}

/-- HCF-shaped proposal state.

    `proposing a` — the entity `a` is currently advocating, if any.
    `proposed a b` — agent `a` has at some past point advocated `b`.

    Algorithms instantiate `β`:
    - GS / Irving phase 1: `β = α` (advocacy is a partner).
    - HCF: `β = Finset α` (advocacy is a coalition). -/
structure State (α β : Type*) where
  proposing : α → Option β
  proposed  : α → β → Prop

/-- Initial state — nobody advocating, empty history. -/
def State.init : State α β where
  proposing := fun _ => none
  proposed  := fun _ _ => False

variable [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]

/-- Set of `(agent, advocacy)` pairs in the history. -/
noncomputable def proposedSet (s : State α β) : Finset (α × β) := by
  classical
  exact Finset.univ.filter fun p => s.proposed p.1 p.2

/-- Total advocacies made so far. -/
noncomputable def proposedCount (s : State α β) : ℕ := (proposedSet s).card

lemma mem_proposedSet (s : State α β) (p : α × β) :
    p ∈ proposedSet s ↔ s.proposed p.1 p.2 := by
  classical
  simp [proposedSet]

lemma proposedCount_init : proposedCount (State.init : State α β) = 0 := by
  classical
  simp [proposedCount, proposedSet, State.init]

lemma proposedCount_le_card (s : State α β) :
    proposedCount s ≤ Fintype.card α * Fintype.card β := by
  classical
  unfold proposedCount proposedSet
  calc (Finset.univ.filter fun p : α × β => s.proposed p.1 p.2).card
      ≤ (Finset.univ : Finset (α × β)).card := Finset.card_filter_le _ _
    _ = Fintype.card (α × β) := Finset.card_univ
    _ = Fintype.card α * Fintype.card β := Fintype.card_prod _ _

/-- **Generic monotone-bounded termination.**

    For any state space `S` projecting into `State α β`, a step function
    that strictly grows `proposedCount` whenever it is not at a fixpoint
    must reach a fixpoint within `|α|·|β|` iterations. The proof requires
    nothing about the algorithm-specific predicate — only the strict
    growth + finite cap. -/
theorem terminates_within {S : Type*}
    (toState : S → State α β)
    (step : S → S) (Term : S → Prop)
    (hfix : ∀ s, Term s → step s = s)
    (hgrow : ∀ s, ¬ Term s →
       proposedCount (toState (step s)) > proposedCount (toState s))
    (init : S) :
    Term ((step^[Fintype.card α * Fintype.card β]) init) := by
  classical
  set N := Fintype.card α * Fintype.card β with hN_def
  by_contra hN
  -- Term-at-step-N is the sticky downward closure: if Term were ever
  -- reached at some k ≤ N, by `hfix` every later index would also be
  -- Term, contradicting `hN`. So `¬ Term` at every k ∈ [0, N].
  have allFalse : ∀ k ≤ N, ¬ Term ((step^[k]) init) := by
    intro k hk hT
    have prop : ∀ m, Term ((step^[k + m]) init) := by
      intro m
      induction m with
      | zero => simpa using hT
      | succ m ih =>
        have hiter : (step^[k + (m + 1)]) init = step ((step^[k + m]) init) := by
          rw [show k + (m + 1) = (k + m) + 1 from rfl, Function.iterate_succ_apply']
        rw [hiter, hfix _ ih]
        exact ih
    have hN' := prop (N - k)
    rw [show k + (N - k) = N from by omega] at hN'
    exact hN hN'
  -- Strict growth, with `¬ Term` at every step in the prefix, forces
  -- `proposedCount` to grow by at least 1 per iteration.
  have growChain : ∀ n ≤ N,
      proposedCount (toState ((step^[n + 1]) init))
        ≥ proposedCount (toState init) + (n + 1) := by
    intro n hn
    induction n with
    | zero =>
      have h0 := hgrow init (allFalse 0 (by omega))
      have hiter : (step^[1]) init = step init := by
        rw [Function.iterate_one]
      rw [hiter]; omega
    | succ n ih =>
      have hn' : n ≤ N := by omega
      have hih := ih hn'
      have hnT : ¬ Term ((step^[n + 1]) init) := allFalse (n + 1) (by omega)
      have hg := hgrow _ hnT
      have hiter : (step^[n + 2]) init = step ((step^[n + 1]) init) := by
        rw [show n + 2 = (n + 1) + 1 from rfl, Function.iterate_succ_apply']
      rw [hiter]; omega
  -- After N+1 strict-growth iterations the count exceeds the finite cap.
  have h1 := growChain N (le_refl _)
  have h2 := proposedCount_le_card (toState ((step^[N + 1]) init))
  have h3 : proposedCount (toState init) ≥ 0 := Nat.zero_le _
  omega

end HedonicGrouping.Algorithms.Common
