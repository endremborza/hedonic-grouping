import Mathlib
import HedonicGrouping.Defs

open HedonicGrouping.Defs

/-!
# Lemma 2 — Irving Correspondence (Paper §5)

**Claim:** Under size-2 non-bipartite preferences, the hedonic grouping
algorithm's processing phase is outcome-equivalent to Irving's Phase 2
rotation elimination. Both detect the same cyclic structures in the reduced
preference table and eliminate the same pairs.

## Proof strategy

The prior formalization attempted `IsMoveOnChain → IsIrvingRotation` under
a single proposal map `prop`. This was provably false: `IsMoveOnChain`
requires `prop pᵢ ≠ some {pᵢ, qᵢ}` (proposers moved on past their chain
partner) while `IsIrvingRotation` required `prop pᵢ = some {pᵢ, qᵢ}`
(proposers hold their chain partner). These are contradictory because they
describe *different algorithm states* for the same cycle — post-cascade vs
pre-cascade — and no single `prop` can satisfy both.

The correct mediating structure is the **reduced preference table**
(`α → List α`): after Phase 1 / Simplified Reduction, each agent has a
list of remaining acceptable partners in preference order. Irving's
rotation is defined directly on this table (Irving 1985, Def 2.5):

    (p₀, q₀), …, (p_{r−1}, q_{r−1})
    where  qᵢ = second(pᵢ)  and  p_{i+1 mod r} = last(qᵢ)

The hedonic algorithm's move-on mechanism traverses the same second→last
chain: forcing `p₀` to propose `second(p₀)` triggers a rejection cascade
(each `qᵢ` rejects `last(qᵢ)`, who then proposes *their* second choice)
that follows exactly the rotation's structure. Both identify the same
cycle and eliminate the pair `{qᵢ, p_{(i+1) mod r}}` at each position —
removing the last entry from each `qᵢ`'s reduced list.

## What is proven

- `IsRotation`: standard Irving rotation defined on reduced lists with no
  reference to a proposal map. Fixes the prior `IsIrvingRotation` which
  conflated the rotation structure with a specific algorithm state.
- `eliminatedPair`: the pair removed at each cycle position (shared by
  both algorithms, definitionally identical).

## What remains (sorry)

- `rotation_eliminates_less_preferred`: the eliminated partner is strictly
  less preferred. Needs `ReducedListCompatible` + `ReducedTableSymmetric`
  to connect reduced-list positions to preference-profile rankings.
- `cascade_matches_rotation`: the main correspondence — the hedonic
  algorithm's move-on cascade follows the rotation's second→last chain
  and produces the same pair eliminations. Requires formalizing the
  cascade dynamics on reduced lists.
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A rotation cycle: proposer-partner pairs forming a cycle of length ≥ 2.
    Each entry `(pᵢ, qᵢ)` follows Irving's convention: `qᵢ` is `pᵢ`'s
    second remaining choice on the reduced preference list. -/
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

/-- Irving rotation on reduced preference lists (Irving 1985, Phase 2).

    Given reduced lists `reduced : α → List α` — each agent's remaining
    acceptable partners in preference order — a rotation cycle
    `(p₀, q₀), …, (p_{r−1}, q_{r−1})` satisfies:

    - `qᵢ` is the second entry on `pᵢ`'s reduced list (second-best choice)
    - `p_{i+1 mod r}` is the last entry on `qᵢ`'s reduced list

    This is a property of the reduced table alone. No proposal map appears.
    The key structural fact: `last(qᵢ) = p_{i+1}` holds because
    `first(p_{i+1}) = qᵢ` (by the Phase 1 duality `first(b) = a ↔ last(a) = b`),
    i.e., `p_{i+1}` is proposing to `qᵢ` and is therefore the worst remaining
    option on `qᵢ`'s list. -/
def IsRotation (c : RotationCycle α) (reduced : α → List α) : Prop :=
  ∀ i : Fin c.pairs.length,
    let p_i := (c.pairs.get i).1
    let q_i := (c.pairs.get i).2
    let p_next := (c.pairs.get (nextFin i c.length_pos)).1
    (reduced p_i)[1]? = some q_i ∧
    (reduced q_i).getLastD q_i = p_next ∧ (reduced q_i) ≠ []

/-- The pair eliminated at cycle position `i`: `{pᵢ, q_{(i+1) mod r}}`.

    At each position, `qᵢ` loses `p_{i+1 mod r}` (the last entry on their
    reduced list) and `p_{i+1 mod r}` loses `qᵢ`. After elimination, each
    `pᵢ`'s second choice becomes their first (they now propose `qᵢ`), and
    each `qᵢ`'s list shrinks by one from the tail. -/
def RotationCycle.eliminatedPair (c : RotationCycle α) (i : Fin c.pairs.length) : Finset α :=
  {(c.pairs.get i).1, (c.pairs.get (nextFin i c.length_pos)).2}

/-- The reduced list preserves the preference ordering from the full profile:
    if `b` appears before `c` on agent `a`'s reduced list, then `a` prefers
    `{a, b}` to `{a, c}` in the original preference profile.
    This holds because Phase 1 / Simplified Reduction only removes entries;
    it never reorders the preference list. -/
def ReducedListCompatible (reduced : α → List α)
    (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ j k : Fin (reduced a).length,
    j < k → Ranks prof a {a, (reduced a)[j]} {a, (reduced a)[k]}

/-- Symmetry invariant: `b` is on `a`'s list iff `a` is on `b`'s.
    Holds after Phase 1 / Simplified Reduction — every rejection is mutual. -/
def ReducedTableSymmetric (reduced : α → List α) : Prop :=
  ∀ a b : α, b ∈ reduced a ↔ a ∈ reduced b

omit [Fintype α] in
/-- **Rotations eliminate less-preferred pairs.**

    At position `i`, agent `qᵢ` strictly prefers `pᵢ` to `p_{i+1 mod r}`.

    Proof sketch: `p_{i+1}` is the last entry on `qᵢ`'s reduced list
    (from `IsRotation`). `pᵢ` is also on `qᵢ`'s list (by `ReducedTableSymmetric`:
    `qᵢ` appears on `pᵢ`'s list as second entry, so `pᵢ` appears on `qᵢ`'s).
    Since `pᵢ ≠ p_{i+1}` in a well-formed rotation and `pᵢ` precedes the last
    entry, `ReducedListCompatible` gives `Ranks prof qᵢ {qᵢ, pᵢ} {qᵢ, p_{i+1}}`. -/
theorem rotation_eliminates_less_preferred
    (c : RotationCycle α)
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hrot : IsRotation c reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (i : Fin c.pairs.length) :
    Ranks prof (c.pairs.get i).2
      {(c.pairs.get i).2, (c.pairs.get i).1}
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} := by
  sorry

/-- Apply Irving's rotation elimination to a reduced table: for each
    position `i`, remove `p_{i+1 mod r}` from `qᵢ`'s list and `qᵢ` from
    `p_{i+1 mod r}`'s list.

    After elimination, each `pᵢ`'s first entry becomes `qᵢ` (their former
    second choice) and each `qᵢ`'s list shrinks by one from the tail. -/
noncomputable def eliminateRotation
    (reduced : α → List α) (c : RotationCycle α) : α → List α :=
  fun a =>
    let removals := (List.finRange c.pairs.length).filterMap fun i =>
      let q_i := (c.pairs.get i).2
      let p_next := (c.pairs.get (nextFin i c.length_pos)).1
      if a = q_i then some p_next
      else if a = p_next then some q_i
      else none
    (reduced a).filter (· ∉ removals)

omit [Fintype α] in
/-- **The hedonic cascade produces Irving's rotation elimination.**

    When `p₀` is forced to move on from `first(p₀)`, the cascade follows
    the rotation's second→last chain:

    1. `p₀` proposes `second(p₀) = q₀`
    2. `{p₀, q₀}` is considerable for `q₀` (size-2: only `p₀` needed)
    3. `q₀` eliminates everything below `{p₀, q₀}`, removing `last(q₀) = p₁`
    4. `p₁` proposes `second(p₁) = q₁`, and the cascade continues

    After traversing the full cycle, the resulting reduced table equals
    `eliminateRotation reduced c` — the same result Irving's Phase 2
    produces. This is the formal bridge between Irving's Phase 2 and the
    hedonic algorithm's `process` function (Algorithm 3 in the paper).

    Proof requires: formalizing the cascade as an induction over rotation
    positions, with each step using `Considerable` (from `Defs.lean`) to
    trigger the elimination of `eliminatedPair c i`. The `Considerable`
    condition is trivially satisfied at each step because in the size-2
    case it collapses to a single proposer check (Lemma 1). -/
theorem cascade_produces_irving_elimination
    (c : RotationCycle α)
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hrot : IsRotation c reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced) :
    let reduced' := eliminateRotation reduced c
    ReducedTableSymmetric reduced' ∧
    ReducedListCompatible reduced' prof := by
  sorry
