import Mathlib
import HedonicGrouping.Defs

open HedonicGrouping.Defs

/-!
# Lemma 2 — Irving Correspondence (Paper §5)

**Claim:** In the size-2 non-bipartite case, the hedonic grouping algorithm's
move-on chains correspond structurally to Irving's Phase 2 rotations. Both
identify cycles in the preference structure and eliminate the same pairs.

## Formalization

We define `RotationCycle` as the shared cycle structure used by both algorithms:
a list of (proposer, partner) pairs `(p₀, q₀), …, (p_{r−1}, q_{r−1})` with `r ≥ 2`.

- **Irving's interpretation** (`IsIrvingRotation`): `pᵢ` currently holds `{pᵢ, qᵢ}`
  and `qᵢ` prefers `pᵢ` over `p_{i+1 mod r}` — i.e., `qᵢ`'s current match is
  better than the next proposer in the cycle.

- **Hedonic grouping interpretation** (`IsMoveOnChain`): no `pᵢ` is currently
  proposing `{pᵢ, qᵢ}` (each has moved on), but `q₀`'s proposal to `p₀` is
  considerable, triggering a rejection cascade.

- **Shared elimination** (`eliminatedPair`): at position `i`, both algorithms
  remove `{pᵢ, q_{i+1 mod r}}` from consideration. This single definition
  serving both interpretations IS the structural correspondence.

## What is proven

- `irving_eliminates_less_preferred`: Irving rotations eliminate pairs where
  `qᵢ` ranks the eliminated partner strictly below their current match.
  This is the key invariant justifying the elimination: no stability violation
  is introduced because each affected agent loses only a less-preferred option.

## What remains open

The full computational correspondence (move-on chain detection ↔ Irving rotation
detection) requires formalizing `AlgState`: reduced preference lists, loop
invariants connecting `prop` to the reduced lists, and monotonicity of the
reduction. Note that `IsMoveOnChain` and `IsIrvingRotation` describe different
proposal states (post-cascade vs. pre-cascade), so the equivalence must mediate
between two `prop` maps — not assert both hold under the same one.
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A rotation cycle: the shared data structure for Irving's Phase 2 rotations
    and the hedonic grouping algorithm's move-on chains.

    Each entry `(pᵢ, qᵢ)` pairs a proposer with a partner. The cycle has
    length `r ≥ 2`, and indices wrap around mod `r`.

    This structure being shared by both algorithms is intentional — it embodies
    the claim that both algorithms identify the same cyclic pattern in the
    preference structure. -/
structure RotationCycle (α : Type*) where
  pairs       : List (α × α)
  nonempty    : pairs ≠ []
  length_ge_2 : 2 ≤ pairs.length

omit [DecidableEq α] [Fintype α] in
lemma RotationCycle.length_pos (c : RotationCycle α) : 0 < c.pairs.length :=
  Nat.lt_of_lt_of_le (by norm_num) c.length_ge_2

/-- Cyclic successor index: `(i + 1) mod r`. -/
def nextFin {r : ℕ} (i : Fin r) (hr : 0 < r) : Fin r :=
  ⟨(i.val + 1) % r, Nat.mod_lt _ hr⟩

/-- Irving rotation condition (Phase 2 of Irving 1985).

    For each position `i` in the cycle:
    - `pᵢ` currently holds proposal `{pᵢ, qᵢ}`, and
    - `qᵢ` strictly prefers `{qᵢ, pᵢ}` to `{qᵢ, p_{i+1 mod r}}` —
      i.e., the current match is ranked above the next proposer.

    This is the condition under which eliminating `{pᵢ, q_{i+1 mod r}}`
    is safe: each affected agent loses only a less-preferred option. -/
def IsIrvingRotation (c : RotationCycle α) (prof : PreferenceProfile α)
    (prop : α → Option (Finset α)) : Prop :=
  ∀ i : Fin c.pairs.length,
    let p_i  := (c.pairs.get i).1
    let q_i  := (c.pairs.get i).2
    let i'   := nextFin i c.length_pos
    let p_i' := (c.pairs.get i').1
    prop p_i = some {p_i, q_i} ∧
    ∃ j k : Fin (prof q_i).length,
      j < k ∧
      (prof q_i)[j] = {q_i, p_i} ∧
      (prof q_i)[k] = {q_i, p_i'}

/-- Move-on chain condition in the hedonic grouping algorithm (§4).

    The chain represents a rejection cascade:
    - No proposer `pᵢ` currently holds `{pᵢ, qᵢ}` — they have each moved on
      past their chain partner to a more-preferred option.
    - `q₀` finds the pair `{p₀, q₀}` considerable (i.e., `q₀` is proposing it),
      triggering the cascade: `q₀`'s new match displaces someone, who moves on,
      who displaces someone else, cycling back around.

    Note: this describes the proposal state *during/after* the cascade, not
    before. Compare with `IsIrvingRotation`, which describes the state *before*
    processing (everyone holds their current second-choice). The two conditions
    use different `prop` maps for the same cycle. -/
def IsMoveOnChain (c : RotationCycle α) (prop : α → Option (Finset α)) : Prop :=
  (∀ i : Fin c.pairs.length,
    let p_i := (c.pairs.get i).1
    let q_i := (c.pairs.get i).2
    prop p_i ≠ some {p_i, q_i}) ∧
  let p_0 := (c.pairs.get ⟨0, c.length_pos⟩).1
  let q_0 := (c.pairs.get ⟨0, c.length_pos⟩).2
  Considerable {p_0, q_0} p_0 prop

/-- The pair eliminated at cycle position `i`: `{pᵢ, q_{(i+1) mod r}}`.

    This is the structural heart of Lemma 2. Both algorithms — Irving's Phase 2
    and the hedonic grouping algorithm's processing phase — eliminate exactly
    this pair at each cycle position. The function is defined once because the
    elimination rule is identical; only the detection mechanism differs.

    Intuitively: `qᵢ` currently prefers `pᵢ` but is "last on `pᵢ`'s list",
    so when the cycle resolves, `pᵢ` drops `q_{i+1}` (the next partner in
    the cycle) and `q_{i+1}` drops `pᵢ` — removing the pair from consideration. -/
def RotationCycle.eliminatedPair (c : RotationCycle α) (i : Fin c.pairs.length) : Finset α :=
  {(c.pairs.get i).1, (c.pairs.get (nextFin i c.length_pos)).2}

omit [Fintype α] in
/-- **Irving rotations eliminate less-preferred pairs.**

    At each cycle position `i`, agent `qᵢ` strictly prefers their current
    partner `pᵢ` to the next proposer `p_{i+1 mod r}` in the cycle. Formally:
    `Ranks prof qᵢ {qᵢ, pᵢ} {qᵢ, p_{i+1 mod r}}`.

    This is the key invariant that makes Irving's Phase 2 (and, by the structural
    correspondence, the hedonic grouping algorithm's processing phase) correct:
    eliminating `{pᵢ, q_{i+1 mod r}}` cannot create a blocking pair, because
    `qᵢ` would never prefer `p_{i+1}` — they already have the strictly better `pᵢ`. -/
theorem irving_eliminates_less_preferred
    (c : RotationCycle α)
    (prof : PreferenceProfile α)
    (prop : α → Option (Finset α))
    (hrot : IsIrvingRotation c prof prop)
    (i : Fin c.pairs.length) :
    Ranks prof (c.pairs.get i).2
      {(c.pairs.get i).2, (c.pairs.get i).1}
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} := by
  obtain ⟨_, j, k, hjk, hj, hk⟩ := hrot i
  exact ⟨j, k, hjk, hj, hk⟩
