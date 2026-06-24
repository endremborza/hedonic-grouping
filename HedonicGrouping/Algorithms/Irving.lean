import Mathlib
import HedonicGrouping.Core

namespace HedonicGrouping.Algorithms.Irving
/-!
# Irving's stable roommates algorithm

Phase 1: proposal-rejection loop producing a reduced preference table.
Phase 2: iterated rotation elimination.

Internal reasoning is pairwise: theorems conclude `PairwiseStable`
(or negation thereof). The `CoreStable` upgrade under size-2 is performed
in `Correctness.IRV_RMP` via the `Unification` bridge.
-/

open HedonicGrouping.Core

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Reduced-table invariants -/

/-- Phase-1 duality (the stable-table invariant `_reduce` maintains):
    `b` is the head of `a`'s reduced list **iff** `a` is the last entry of
    `b`'s list (`first(a) = b ⟺ last(b) = a`). Equivalently each agent's
    first choice ranks that agent last, and conversely. Both directions
    matter: the forward one (`phase1Duality_getLast`) feeds the `IsRotation`
    `last(q_i) = p_{i+1}` shape, while the converse (`phase1Duality_head`)
    is what rules out length-1 self-loop rotations
    (`isRotation_no_selfLoop`), keeping every Phase-2 rotation chain among
    length-≥-2 lists. -/
def Phase1Duality (reduced : α → List α) : Prop :=
  ∀ a b : α, (reduced a).head? = some b ↔ (reduced b).getLast? = some a

omit [DecidableEq α] [Fintype α] in
/-- Forward direction of `Phase1Duality` in canonical `getLast?` form: an
    agent's head-partner holds it in the last position. The shape Phase-2
    rotation reasoning consumes (`p_{i+1} = last(q_i)` in `IsRotation`). -/
lemma phase1Duality_getLast
    (reduced : α → List α) (hdual : Phase1Duality reduced)
    {a b : α} (hb : (reduced a).head? = some b) :
    (reduced b).getLast? = some a :=
  (hdual a b).mp hb

omit [DecidableEq α] [Fintype α] in
/-- Converse direction of `Phase1Duality`: an agent that sits last on `b`'s
    list has `b` as its own first choice (`last(b) = a → first(a) = b`). The
    direction `isRotation_no_selfLoop` reads off: `last(q_i) = p_i` forces
    `first(p_i) = q_i`, colliding with `q_i = second(p_i)`. -/
lemma phase1Duality_head
    (reduced : α → List α) (hdual : Phase1Duality reduced)
    {a b : α} (hb : (reduced b).getLast? = some a) :
    (reduced a).head? = some b :=
  (hdual a b).mpr hb

/-- All reduced lists have length 1: each agent has exactly one remaining
    partner. -/
def AllSingleton (reduced : α → List α) : Prop :=
  ∀ a : α, (reduced a).length = 1

/-- Extract the matching implied by a singleton reduced table. -/
noncomputable def singletonMatching (reduced : α → List α) : Grouping α :=
  fun a => {a, ((reduced a).head?.getD a)}

/-- Total list lengths — termination measure for Phase 2. -/
noncomputable def totalLength [Fintype α] (reduced : α → List α) : ℕ :=
  Finset.univ.sum fun a => (reduced a).length

/-- Reduced list preserves original preference ordering. -/
def ReducedListCompatible (reduced : α → List α)
    (prof : PreferenceProfile α) : Prop :=
  ∀ a : α, ∀ j k : Fin (reduced a).length,
    j < k → Ranks prof a {a, (reduced a)[j]} {a, (reduced a)[k]}

/-- `b ∈ reduced a ↔ a ∈ reduced b`. -/
def ReducedTableSymmetric (reduced : α → List α) : Prop :=
  ∀ a b : α, b ∈ reduced a ↔ a ∈ reduced b

/-- Each agent's reduced list is duplicate-free. Preserved by `reduceStep`
    (`reduceStep_preserves_nodup`); needed so that truncating a list at an
    agent's first-choice position cleanly partitions it into a kept prefix and
    a deleted tail, which is what `reduceStep_preserves_symmetric` relies on. -/
def ReducedTableNodup (reduced : α → List α) : Prop :=
  ∀ a : α, (reduced a).Nodup

/-- Cascade invariant: agents with singleton lists have matched partners.
    Re-established by the reduce pass after Phase 1 and after each
    rotation elimination: if `b ∈ reduced a` and `reduced a`
    has length 1, then `reduced b` also has length 1.

    This is what guarantees Phase 2's rotation-finding iteration
    `p ↦ last(reduced (second(reduced p)))` stays inside the length-≥-2
    agents and therefore terminates with a true rotation. -/
def CascadeInvariant (reduced : α → List α) : Prop :=
  ∀ a b : α, b ∈ reduced a → (reduced a).length = 1 → (reduced b).length = 1

/-- Stable-pair invariant: each agent's partner in `μ` remains on their
    reduced list. Established by Phase 1 for every stable matching and
    preserved through Phase 2. -/
def StablePairInvariant (reduced : α → List α) (_prof : PreferenceProfile α)
    (μ : Grouping α) : Prop :=
  ∀ a : α, pairPartner a (μ a) ∈ reduced a

/-- Every genuine stable matching survives in the reduced table — the
    `StablePairInvariant` form of Irving's "no stable pair is ever deleted".
    **True for the Phase-1 output only.**

    ⚠ FALSE for Phase 2 (found 2026-06-23): rotation elimination *does* delete
    stable pairs (it navigates the rotation poset, discarding stable matchings),
    so universal survival cannot be preserved per step. Phase 2 is therefore
    threaded through the existential `SolvableInTable` instead — seeded from this
    (true) Phase-1 invariant via `solvableInTable_of_survive`. See `.cril/ideas.md`. -/
def StableMatchingsSurvive (reduced : α → List α)
    (prof : PreferenceProfile α) : Prop :=
  ∀ μ : Grouping α, IsPairMatching prof μ → PairwiseStable prof μ →
    StablePairInvariant reduced prof μ

/-- **Existential solvability** of a reduced table: it still admits a genuine
    pairwise-stable matching all of whose pairs survive in it. This is the
    *corrected* Phase-2 invariant. `StableMatchingsSurvive` (universal survival)
    is false for Phase 2 — rotation elimination discards stable matchings — but
    existential solvability is preserved by each step (`solvableInTable_step`),
    so an empty list certifies unsolvability (`empty_not_solvableInTable`). -/
def SolvableInTable (reduced : α → List α) (prof : PreferenceProfile α) : Prop :=
  ∃ μ : Grouping α, IsPairMatching prof μ ∧ PairwiseStable prof μ ∧
    StablePairInvariant reduced prof μ

omit [Fintype α] in
/-- Phase-1 → Phase-2 bridge: where universal survival holds (the Phase-1
    output, `StableMatchingsSurvive`), any actual stable pair-matching witnesses
    existential solvability. This seeds Phase 2's `SolvableInTable` thread from
    Phase 1's (true) `StableMatchingsSurvive`. -/
theorem solvableInTable_of_survive
    (reduced : α → List α) (prof : PreferenceProfile α)
    (hsurv : StableMatchingsSurvive reduced prof)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ) (hstable : PairwiseStable prof μ) :
    SolvableInTable reduced prof :=
  ⟨μ, hmatch, hstable, hsurv μ hmatch hstable⟩

omit [Fintype α] in
/-- **Empty list ⇒ not solvable.** An agent with an empty reduced list has
    nowhere to keep its partner, so no stable pair-matching survives in the
    table. The existential-invariant endpoint of Phase 2 (it replaced the
    false-path universal-survival empty-list endpoint, removed 2026-06-23). -/
theorem empty_not_solvableInTable
    (reduced : α → List α) (prof : PreferenceProfile α)
    (a : α) (hempty : reduced a = []) :
    ¬ SolvableInTable reduced prof := by
  rintro ⟨μ, _, _, hinv⟩
  have h := hinv a
  rw [hempty] at h
  simp at h

/-- Removed-pair domination invariant: for every *mutually* ranked pair
    `{a, c}` with `c` deleted from `a`'s reduced list, **at least one side**
    ranks all of its surviving partners strictly above the other — either `a`
    prefers every kept `d` to `c`, or `c` prefers every kept `d` to `a`.

    The disjunction is essential; the one-sided "removed ⇒ less preferred"
    form is **false** (oracle-probed: it fails on 1200/1248 solvable n=4
    profiles, because Irving routinely deletes an agent's *most*-preferred
    mutual partner). Under `Phase1Duality` a rotation deletes `{q_i, p_{i+1}}`,
    and `last(q_i) = p_{i+1}` forces `first(p_{i+1}) = q_i`
    (`phase1Duality_head`) — so `q_i` is `p_{i+1}`'s *top* choice and the
    deletion is justified only from `q_i`'s side (where `p_{i+1}` is its last).
    Every deletion is justified by the *rejecting* side, so the surviving
    invariant is disjunctive.

    The mutuality guard `{a, c} ∈ prof c` is sound and free at the only
    consumer: a blocking `c` ranks `{a, c}` by definition, and the symmetric
    blocking hypothesis supplies the mirror membership. -/
def RemovedDominated (reduced : α → List α) (prof : PreferenceProfile α) : Prop :=
  ∀ a c : α, ({a, c} : Finset α) ∈ prof a → ({a, c} : Finset α) ∈ prof c →
    c ∉ reduced a →
      (∀ d ∈ reduced a, Ranks prof a {a, d} {a, c}) ∨
      (∀ d ∈ reduced c, Ranks prof c {c, d} {c, a})

/-! ## Rotation machinery -/

/-- A rotation cycle: proposer-partner pairs forming a nonempty cycle.
    The field stays `length_pos` (length ≥ 1) by design: rather than
    strengthen it, length-≥-2 is derived on demand from duality via
    `rotationCycle_length_ge_2_of_dual` (a length-1 cycle's sole edge is a
    self-loop, which `isRotation_no_selfLoop` forbids under `Phase1Duality`).
    `Phase1Duality` is now threaded through Phase 2, so `hdual` is in scope
    wherever the ≥-2 fact is needed; the earlier "self-loops are genuine"
    reading was an artifact of the superseded buggy `_cascade` model. -/
structure RotationCycle (α : Type*) where
  pairs      : List (α × α)
  length_pos : 0 < pairs.length

/-- Cyclic successor index: `(i + 1) mod r`. -/
def nextFin {r : ℕ} (i : Fin r) (hr : 0 < r) : Fin r :=
  ⟨(i.val + 1) % r, Nat.mod_lt _ hr⟩

/-- `nextFin` is surjective: every index has a cyclic predecessor
    (`j` with `nextFin j = i`). The index-stepping primitive of the
    rotation-cycle trace — it produces the `i-1` the descent `i → i-1`
    walks to. -/
lemma nextFin_surjective {r : ℕ} (hr : 0 < r) (i : Fin r) :
    ∃ j : Fin r, nextFin j hr = i := by
  refine ⟨⟨(i.val + r - 1) % r, Nat.mod_lt _ hr⟩, Fin.ext ?_⟩
  show ((i.val + r - 1) % r + 1) % r = i.val
  have hmod : ((i.val + r - 1) % r + 1) % r = (i.val + r - 1 + 1) % r :=
    Nat.ModEq.add_right 1 (Nat.mod_modEq _ _)
  have he : i.val + r - 1 + 1 = i.val + r := by omega
  rw [hmod, he, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt i.isLt

/-- `nextFin` is injective: distinct indices have distinct cyclic successors.
    The cyclic shift `i ↦ (i+1) mod r` is a bijection on `Fin r`, so injectivity
    follows from `nextFin_surjective` on the finite index type. Consumed by
    `isRotation_partners_distinct` to step `nextFin i = nextFin j` back to
    `i = j`. -/
lemma nextFin_injective {r : ℕ} (hr : 0 < r) {i j : Fin r}
    (h : nextFin i hr = nextFin j hr) : i = j := by
  have hsurj : Function.Surjective (fun k : Fin r => nextFin k hr) :=
    fun k => nextFin_surjective hr k
  exact Finite.injective_iff_surjective.mpr hsurj h

/-- Irving rotation on reduced preference lists.
    `qᵢ = second(pᵢ)` and `p_{i+1 mod r} = last(qᵢ)`. -/
def IsRotation (c : RotationCycle α) (reduced : α → List α) : Prop :=
  ∀ i : Fin c.pairs.length,
    let p_i := (c.pairs.get i).1
    let q_i := (c.pairs.get i).2
    let p_next := (c.pairs.get (nextFin i c.length_pos)).1
    (reduced p_i)[1]? = some q_i ∧
    (reduced q_i).getLastD q_i = p_next ∧ (reduced q_i) ≠ []

/-- The partners deleted from `a`'s list when rotation `c` is eliminated:
    `p_{i+1}` leaves `q_i`'s list and `q_i` leaves `p_{i+1}`'s. -/
def rotationRemovals (c : RotationCycle α) (a : α) : List α :=
  (List.finRange c.pairs.length).filterMap fun i =>
    let q_i := (c.pairs.get i).2
    let p_next := (c.pairs.get (nextFin i c.length_pos)).1
    if a = q_i then some p_next
    else if a = p_next then some q_i
    else none

omit [Fintype α] in
/-- Removals are mutual: rotation elimination deletes pairs, never single
    directions. -/
lemma rotationRemovals_symm {c : RotationCycle α} {a b : α}
    (h : b ∈ rotationRemovals c a) : a ∈ rotationRemovals c b := by
  simp only [rotationRemovals, List.mem_filterMap] at h ⊢
  obtain ⟨i, hi, hf⟩ := h
  refine ⟨i, hi, ?_⟩
  split at hf <;> [split <;> simp_all; split at hf <;> [split <;> simp_all; simp at hf]]

omit [Fintype α] in
/-- Membership characterization for `rotationRemovals`: `b` is deleted from
    `a`'s list exactly when `(a, b)` is a rotation edge `(q_i, p_{i+1})` in one
    of the two directions. The case-extraction step the stable-pair-preservation
    argument consumes. -/
lemma mem_rotationRemovals {c : RotationCycle α} {a b : α}
    (h : b ∈ rotationRemovals c a) :
    ∃ i : Fin c.pairs.length,
      (a = (c.pairs.get i).2 ∧ b = (c.pairs.get (nextFin i c.length_pos)).1) ∨
      (a = (c.pairs.get (nextFin i c.length_pos)).1 ∧ b = (c.pairs.get i).2) := by
  simp only [rotationRemovals, List.mem_filterMap] at h
  obtain ⟨i, _, hf⟩ := h
  refine ⟨i, ?_⟩
  split at hf
  · next hq =>
      refine Or.inl ⟨hq, ?_⟩
      injection hf with hf'; exact hf'.symm
  · split at hf
    · next hpn =>
        refine Or.inr ⟨hpn, ?_⟩
        injection hf with hf'; exact hf'.symm
    · simp at hf

/-- Apply rotation elimination. -/
noncomputable def eliminateRotation
    (reduced : α → List α) (c : RotationCycle α) : α → List α :=
  fun a => (reduced a).filter (· ∉ rotationRemovals c a)

/-- Partner list for the **rotation-shifted matching** `M/ρ`: re-pair each `q_i`
    with `p_i` (the proposer at its *own* index) and, symmetrically, each `p_i`
    with `q_i`. This is the Gusfield–Irving `M/ρ[x_i] = y_{i-1}` shift under
    `x_i := q_i`, `y_i := p_{i+1}` (so `y_{i-1} = p_i`). Same `finRange.filterMap`
    shape as `rotationRemovals`, so membership reasoning reuses that idiom. -/
def rotationShiftPartner (c : RotationCycle α) (a : α) : List α :=
  (List.finRange c.pairs.length).filterMap fun i =>
    if a = (c.pairs.get i).2 then some (c.pairs.get i).1
    else if a = (c.pairs.get i).1 then some (c.pairs.get i).2
    else none

/-- The rotation-shifted matching `M/ρ`: on a cycle agent, re-pair via
    `rotationShiftPartner` (`q_i ↦ p_i`, `p_i ↦ q_i`); off the cycle, keep the
    original `μ` coalition. Under the all-or-nothing hypothesis (a stable `μ`
    using one removed pair `{q_i, p_{i+1}}` uses all of them) this is the witness
    the upper-matching branch of `solvableInTable_step` feeds to
    `stablePair_eliminate_of_avoids`; probe-validated 2026-06-23. -/
def rotationShift (c : RotationCycle α) (μ : Grouping α) : Grouping α :=
  fun a =>
    match (rotationShiftPartner c a).head? with
    | some b => {a, b}
    | none   => μ a

omit [Fintype α] in
/-- Membership characterization for `rotationShiftPartner`: `b` is a shift
    partner of `a` exactly when `(a, b)` is a rotation edge in one of the two
    re-pairing directions `q_i ↦ p_i` / `p_i ↦ q_i`. The shift analogue of
    `mem_rotationRemovals`. -/
lemma mem_rotationShiftPartner {c : RotationCycle α} {a b : α}
    (h : b ∈ rotationShiftPartner c a) :
    ∃ i : Fin c.pairs.length,
      (a = (c.pairs.get i).2 ∧ b = (c.pairs.get i).1) ∨
      (a = (c.pairs.get i).1 ∧ b = (c.pairs.get i).2) := by
  simp only [rotationShiftPartner, List.mem_filterMap] at h
  obtain ⟨i, _, hf⟩ := h
  refine ⟨i, ?_⟩
  split at hf
  · next hq =>
      refine Or.inl ⟨hq, ?_⟩
      injection hf with hf'; exact hf'.symm
  · split at hf
    · next hp =>
        refine Or.inr ⟨hp, ?_⟩
        injection hf with hf'; exact hf'.symm
    · simp at hf

omit [Fintype α] in
/-- Shift partners are mutual: `rotationShiftPartner` re-pairs `q_i ↔ p_i`
    symmetrically, the shift analogue of `rotationRemovals_symm`. Consumed by the
    matching-consistency half of the `rotationShift` witness — with
    `a ∈ rotationShiftPartner c b` in hand, cycle-agent distinctness pins
    `rotationShiftPartner c b = [a]`, hence `head? = some a` and
    `rotationShift c μ b = {b, a}`. -/
lemma rotationShiftPartner_symm {c : RotationCycle α} {a b : α}
    (h : b ∈ rotationShiftPartner c a) : a ∈ rotationShiftPartner c b := by
  simp only [rotationShiftPartner, List.mem_filterMap] at h ⊢
  obtain ⟨i, hi, hf⟩ := h
  refine ⟨i, hi, ?_⟩
  split at hf <;> [split <;> simp_all; split at hf <;> [split <;> simp_all; simp at hf]]

omit [Fintype α] in
/-- `rotationShiftPartner` and `rotationRemovals` share support: an agent with no
    shift partner has no rotation removal either. The shift re-pairs exactly the
    agents that appear as some `p_i`/`q_i`; the removals delete pairs exactly among
    the agents that appear as some `q_i`/`p_{i+1}` — and `nextFin` ranges over every
    index, so the two supports coincide. The off-cycle half of the upper-matching
    witness's avoids-removed-pairs obligation in `solvableInTable_step`: an off-cycle
    agent (`rotationShiftPartner` empty, so `rotationShift` keeps `μ`'s coalition) is
    untouched by `eliminateRotation` and thus trivially avoids every removed pair.
    Distinctness-independent — it does not pin which index an agent sits at. -/
lemma rotationRemovals_nil_of_rotationShiftPartner_nil {c : RotationCycle α} {a : α}
    (h : rotationShiftPartner c a = []) : rotationRemovals c a = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro b hb
  have hempty : ∀ x, x ∉ rotationShiftPartner c a := by rw [h]; simp
  obtain ⟨i, hcase⟩ := mem_rotationRemovals hb
  rcases hcase with ⟨ha_eq, _⟩ | ⟨ha_eq, _⟩
  · exact hempty (c.pairs.get i).1 (by
      simp only [rotationShiftPartner, List.mem_filterMap]
      exact ⟨i, List.mem_finRange i, if_pos ha_eq⟩)
  · by_cases hq : a = (c.pairs.get (nextFin i c.length_pos)).2
    · exact hempty (c.pairs.get (nextFin i c.length_pos)).1 (by
        simp only [rotationShiftPartner, List.mem_filterMap]
        exact ⟨nextFin i c.length_pos, List.mem_finRange _, if_pos hq⟩)
    · exact hempty (c.pairs.get (nextFin i c.length_pos)).2 (by
        simp only [rotationShiftPartner, List.mem_filterMap]
        exact ⟨nextFin i c.length_pos, List.mem_finRange _, (if_neg hq).trans (if_pos ha_eq)⟩)

omit [Fintype α] in
/-- Off the rotation cycle (`rotationShiftPartner` empty) the shifted matching
    keeps `μ`'s coalition. -/
lemma rotationShift_off (c : RotationCycle α) (μ : Grouping α) (a : α)
    (h : rotationShiftPartner c a = []) :
    rotationShift c μ a = μ a := by
  simp [rotationShift, h]

omit [Fintype α] in
/-- The shifted matching keeps every agent inside its own coalition whenever `μ`
    does: on a cycle agent `rotationShift c μ a = {a, b}` contains `a` by
    construction, off-cycle it is `μ a` which contains `a` by `hμ`. The
    `IsValidGrouping` half of the upper-matching witness of `solvableInTable_step`
    — consumed by its `IsPairMatching` / `coalition_eq_pairPartner` reasoning
    (which reads `a ∈ rotationShift c μ a`), and unconditional in the cycle-agent
    distinctness still open for the rest of that branch. -/
lemma rotationShift_isValidGrouping (c : RotationCycle α) (μ : Grouping α)
    (hμ : IsValidGrouping μ) : IsValidGrouping (rotationShift c μ) := by
  intro a
  unfold rotationShift
  split
  · simp
  · exact hμ a

omit [Fintype α] in
/-- On a cycle agent, the shifted coalition's `pairPartner` is the head shift
    partner. `rotationShift c μ a = {a, b}` for the head shift partner `b`, so
    when `a ≠ b` its `pairPartner` is `b` (`pairPartner_eq_of_card_two`). The
    `pairPartner` side of the upper-matching witness of `solvableInTable_step`:
    both the `IsPairMatching` consistency and the avoids-removed-pairs
    obligations compute `pairPartner a (rotationShift c μ a)` and read it off as
    the shift partner. Distinctness-independent (the cycle-simplicity decision is
    deferred): the caller supplies `a ≠ b`. -/
lemma rotationShift_pairPartner_cycle (c : RotationCycle α) (μ : Grouping α)
    {a b : α} (hhead : (rotationShiftPartner c a).head? = some b) (hne : a ≠ b) :
    pairPartner a (rotationShift c μ a) = b := by
  have hcoal : rotationShift c μ a = {a, b} := by simp [rotationShift, hhead]
  rw [hcoal]
  exact pairPartner_eq_of_card_two (Finset.card_pair hne)
    (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (Ne.symm hne)

omit [Fintype α] in
/-- **A rotation's proposer and partner are distinct** (`p_i ≠ q_i`).
    `q_i = second(p_i)` sits at index 1 of `p_i`'s reduced list with index 0
    before it, so compatibility lists the coalition `{p_i, q_i}` in `prof p_i`;
    `SizeTwo` then forces it to be a genuine two-element set, hence `p_i ≠ q_i`.

    This settles the cycle-simplicity question (flagged as a deferred owner
    decision) in the affirmative: shift-endpoint distinctness is *derivable*
    from the already-threaded invariants (`ReducedListCompatible` + `SizeTwo`),
    so neither `RotationCycle` nor `IsRotation` needs an extra distinctness
    field. Consumed (via `rotationShift_head_ne`) by the upper-matching witness
    of `solvableInTable_step`, which feeds the resulting `a ≠ b` to
    `rotationShift_pairPartner_cycle`. -/
theorem isRotation_proposer_ne_partner
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hrot : IsRotation c reduced)
    (i : Fin c.pairs.length) :
    (c.pairs.get i).1 ≠ (c.pairs.get i).2 := by
  obtain ⟨hsec, _, _⟩ := hrot i
  obtain ⟨h1, hq1⟩ := List.getElem?_eq_some_iff.mp hsec
  have h0 : (0 : ℕ) < (reduced (c.pairs.get i).1).length := by omega
  have hlt : (⟨0, h0⟩ : Fin (reduced (c.pairs.get i).1).length) < ⟨1, h1⟩ :=
    Fin.mk_lt_mk.mpr (by norm_num)
  have hrank := hcompat (c.pairs.get i).1 ⟨0, h0⟩ ⟨1, h1⟩ hlt
  rw [show (reduced (c.pairs.get i).1)[(⟨1, h1⟩ : Fin (reduced (c.pairs.get i).1).length)]
      = (c.pairs.get i).2 from hq1] at hrank
  obtain ⟨_, _, _, _, hH⟩ := hrank
  have hmem : ({(c.pairs.get i).1, (c.pairs.get i).2} : Finset α) ∈ prof (c.pairs.get i).1 := by
    rw [← hH]; exact List.getElem_mem _
  have hcard := hsize (c.pairs.get i).1 _ hmem
  intro heq
  rw [heq] at hcard
  simp at hcard

omit [Fintype α] in
/-- The head shift partner is always a *distinct* agent: if
    `(rotationShiftPartner c a).head? = some b` then `a ≠ b`. The head is a
    member, so `mem_rotationShiftPartner` exhibits it as a rotation edge
    (`q_i ↦ p_i` or `p_i ↦ q_i`), whose endpoints are distinct by
    `isRotation_proposer_ne_partner`. This supplies the `a ≠ b` hypothesis
    `rotationShift_pairPartner_cycle` demands of its caller, closing the
    distinctness obligation of the upper-matching witness without a
    cycle-simplicity field. -/
theorem rotationShift_head_ne
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hrot : IsRotation c reduced)
    {a b : α} (hhead : (rotationShiftPartner c a).head? = some b) :
    a ≠ b := by
  have hb_mem : b ∈ rotationShiftPartner c a :=
    List.mem_of_mem_head? (Option.mem_def.mpr hhead)
  obtain ⟨i, hcase⟩ := mem_rotationShiftPartner hb_mem
  rcases hcase with ⟨ha, hb_eq⟩ | ⟨ha, hb_eq⟩
  · rw [ha, hb_eq]
    exact (isRotation_proposer_ne_partner c reduced prof hsize hcompat hrot i).symm
  · rw [ha, hb_eq]
    exact isRotation_proposer_ne_partner c reduced prof hsize hcompat hrot i

omit [Fintype α] in
/-- Rotations eliminate less-preferred pairs. On a length-1 self-loop
    (`p_i = p_next`) the statement degenerates reflexively, so the
    inequality is an explicit guard hypothesis rather than an `IsRotation`
    conjunct. -/
theorem rotation_eliminates_less_preferred
    (c : RotationCycle α)
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hrot : IsRotation c reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (i : Fin c.pairs.length)
    (hneq : (c.pairs.get i).1 ≠ (c.pairs.get (nextFin i c.length_pos)).1) :
    Ranks prof (c.pairs.get i).2
      {(c.pairs.get i).2, (c.pairs.get i).1}
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} := by
  obtain ⟨hsec, hlast, hne⟩ := hrot i
  have hq_mem : (c.pairs.get i).2 ∈ reduced (c.pairs.get i).1 :=
    List.mem_of_getElem? hsec
  have hp_mem : (c.pairs.get i).1 ∈ reduced (c.pairs.get i).2 :=
    (hsym _ _).mp hq_mem
  obtain ⟨j, hj, hj_eq⟩ := List.mem_iff_getElem.mp hp_mem
  have hlen : 0 < (reduced (c.pairs.get i).2).length := List.length_pos_of_ne_nil hne
  have hk : (reduced (c.pairs.get i).2).length - 1 < (reduced (c.pairs.get i).2).length := by omega
  have hk_eq : (reduced (c.pairs.get i).2)[(reduced (c.pairs.get i).2).length - 1] =
      (c.pairs.get (nextFin i c.length_pos)).1 := by
    conv_lhs => rw [← List.getLast_eq_getElem hne]
    rw [← hlast, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some]
  have hjk : j < (reduced (c.pairs.get i).2).length - 1 := by
    rcases Nat.lt_or_ge j ((reduced (c.pairs.get i).2).length - 1) with h | h
    · exact h
    · exfalso
      have hjeq : j = (reduced (c.pairs.get i).2).length - 1 := by omega
      exact hneq (by rw [← hj_eq, ← hk_eq]; congr 1)
  rw [show (c.pairs.get i).1 = (reduced (c.pairs.get i).2)[j] from hj_eq.symm,
      show (c.pairs.get (nextFin i c.length_pos)).1 =
        (reduced (c.pairs.get i).2)[(reduced (c.pairs.get i).2).length - 1] from hk_eq.symm]
  exact hcompat _ ⟨j, hj⟩ ⟨_, hk⟩ hjk

omit [Fintype α] in
/-- **Rotations on a dual table have no self-loops.** Under `Phase1Duality`,
    a rotation edge cannot satisfy `p_i = p_{i+1}`: the cyclic law
    `last(q_i) = p_{i+1}` would, via duality's converse, force
    `first(p_i) = q_i`, but `q_i = second(p_i)`, so `p_i`'s first and second
    choices coincide — refuted by compatibility + irreflexivity. This is what
    licenses restoring `IsRotation`'s `p_i ≠ p_next` guard once duality is
    threaded through Phase 2. -/
theorem isRotation_no_selfLoop
    (c : RotationCycle α)
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hdual : Phase1Duality reduced)
    (hrot : IsRotation c reduced)
    (i : Fin c.pairs.length) :
    (c.pairs.get i).1 ≠ (c.pairs.get (nextFin i c.length_pos)).1 := by
  intro hself
  obtain ⟨hsec, hlast, hne⟩ := hrot i
  -- `last(q_i) = p_next = p_i`, in canonical `getLast?` form.
  have hglq : (reduced (c.pairs.get i).2).getLast? = some (c.pairs.get i).1 := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
      Option.getD_some] at hlast
    rw [List.getLast?_eq_some_getLast hne, hlast, hself]
  -- Duality's converse: `q_i` is then `p_i`'s first choice.
  have hhead : (reduced (c.pairs.get i).1).head? = some (c.pairs.get i).2 :=
    phase1Duality_head reduced hdual hglq
  rw [List.head?_eq_getElem?] at hhead
  obtain ⟨h0, hq0⟩ := List.getElem?_eq_some_iff.mp hhead
  obtain ⟨h1, hq1⟩ := List.getElem?_eq_some_iff.mp hsec
  -- `first(p_i) = q_i = second(p_i)` collides with strict compatibility.
  have hlt : (⟨0, h0⟩ : Fin (reduced (c.pairs.get i).1).length) < ⟨1, h1⟩ :=
    Fin.mk_lt_mk.mpr (by norm_num)
  have hcontra : Ranks prof (c.pairs.get i).1
      {(c.pairs.get i).1, (reduced (c.pairs.get i).1)[0]'h0}
      {(c.pairs.get i).1, (reduced (c.pairs.get i).1)[1]'h1} :=
    hcompat (c.pairs.get i).1 ⟨0, h0⟩ ⟨1, h1⟩ hlt
  rw [hq0, hq1] at hcontra
  exact Ranks.irrefl hvalid hcontra

omit [Fintype α] in
/-- Under `Phase1Duality`, rotations eliminate strictly-less-preferred pairs
    **unconditionally**: the self-loop guard `p_i ≠ p_next` that
    `rotation_eliminates_less_preferred` carries as an explicit hypothesis is
    discharged by `isRotation_no_selfLoop` (duality forbids the self-loop),
    so duality alone licenses "`qᵢ` ranks `pᵢ` above `p_{i+1}`". This is the
    form the removed-partner / stable-pair threading consumes once Phase 2
    carries `Phase1Duality`; it is the consumer of step 2's
    `isRotation_no_selfLoop` keystone. -/
theorem rotation_eliminates_less_preferred_of_dual
    (c : RotationCycle α)
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof)
    (hrot : IsRotation c reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hdual : Phase1Duality reduced)
    (i : Fin c.pairs.length) :
    Ranks prof (c.pairs.get i).2
      {(c.pairs.get i).2, (c.pairs.get i).1}
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} :=
  rotation_eliminates_less_preferred c reduced prof hrot hcompat hsym i
    (isRotation_no_selfLoop c reduced prof hvalid hcompat hdual hrot i)

omit [Fintype α] in
/-- **Rotations on a dual table have length ≥ 2.** A length-1 cycle's sole
    edge is a self-loop: `nextFin ⟨0,_⟩ = ⟨0,_⟩`, so its rotation edge has
    `p_0 = p_next`, which `isRotation_no_selfLoop` forbids under
    `Phase1Duality`. This derives `2 ≤ length` from duality on demand, so the
    `RotationCycle.length_pos` field need not be strengthened to `length_ge_2`,
    and supplies the period-≥-2 fact `findRotation`'s cycle construction carries. -/
theorem rotationCycle_length_ge_2_of_dual
    (c : RotationCycle α)
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hdual : Phase1Duality reduced)
    (hrot : IsRotation c reduced) :
    2 ≤ c.pairs.length := by
  by_contra h
  push_neg at h
  have h1 : c.pairs.length = 1 := by have := c.length_pos; omega
  have hself :=
    isRotation_no_selfLoop c reduced prof hvalid hcompat hdual hrot ⟨0, c.length_pos⟩
  apply hself
  have e : nextFin (⟨0, c.length_pos⟩ : Fin c.pairs.length) c.length_pos
      = ⟨0, c.length_pos⟩ := by
    apply Fin.ext
    show ((0 : ℕ) + 1) % c.pairs.length = 0
    rw [h1, Nat.mod_one]
  rw [e]

omit [Fintype α] in
/-- **The rotation-shift coalition is ranked.** For a cycle agent `a` whose head
    shift partner is `b`, the shifted coalition `{a, b}` is one of `a`'s ranked
    pairs (`∈ prof a`). The head is a rotation edge `q_i ↦ p_i` / `p_i ↦ q_i`
    (`mem_rotationShiftPartner`): the `q_i` direction reads the membership off
    `rotation_eliminates_less_preferred_of_dual` (which ranks `{q_i, p_i}` for
    `q_i`) via `Ranks.fst_mem`; the `p_i` direction off compatibility at positions
    `0, 1` (`q_i = second(p_i)`). This is the first `IsPairMatching` conjunct
    (`rotationShift c μ a ∈ prof a`) for the upper-matching witness of
    `solvableInTable_step`, restricted to cycle agents (off-cycle it is `μ a`).
    Distinctness-independent: it takes the head as a hypothesis rather than
    pinning `rotationShiftPartner`'s list, so it does not prejudge the open
    cycle-simplicity decision. -/
theorem rotationShift_mem_prof_cycle
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hdual : Phase1Duality reduced)
    (hrot : IsRotation c reduced)
    (μ : Grouping α) {a b : α}
    (hhead : (rotationShiftPartner c a).head? = some b) :
    rotationShift c μ a ∈ prof a := by
  have hcoal : rotationShift c μ a = {a, b} := by simp [rotationShift, hhead]
  rw [hcoal]
  have hb_mem : b ∈ rotationShiftPartner c a :=
    List.mem_of_mem_head? (Option.mem_def.mpr hhead)
  obtain ⟨i, hcase⟩ := mem_rotationShiftPartner hb_mem
  rcases hcase with ⟨ha, hb_eq⟩ | ⟨ha, hb_eq⟩
  · rw [ha, hb_eq]
    exact Ranks.fst_mem
      (rotation_eliminates_less_preferred_of_dual c reduced prof hvalid hrot hcompat hsym hdual i)
  · rw [ha, hb_eq]
    obtain ⟨hsec, _, _⟩ := hrot i
    obtain ⟨h1, hq1⟩ := List.getElem?_eq_some_iff.mp hsec
    have h0 : (0 : ℕ) < (reduced (c.pairs.get i).1).length := by omega
    have hlt : (⟨0, h0⟩ : Fin (reduced (c.pairs.get i).1).length) < ⟨1, h1⟩ :=
      Fin.mk_lt_mk.mpr (by norm_num)
    have hrank := hcompat (c.pairs.get i).1 ⟨0, h0⟩ ⟨1, h1⟩ hlt
    rw [show (reduced (c.pairs.get i).1)[(⟨1, h1⟩ : Fin (reduced (c.pairs.get i).1).length)]
        = (c.pairs.get i).2 from hq1] at hrank
    obtain ⟨_, _, _, _, hH⟩ := hrank
    rw [← hH]; exact List.getElem_mem _

omit [Fintype α] in
/-- **The rotation-shift witness is everywhere a ranked pair** — the first
    `IsPairMatching` conjunct (`rotationShift c μ a ∈ prof a`) for *every* agent,
    lifting the cycle-only `rotationShift_mem_prof_cycle` across the cycle /
    off-cycle split. On a cycle agent (`head? = some b`) it reads off
    `rotationShift_mem_prof_cycle`; off-cycle (`head? = none`, so
    `rotationShift c μ a = μ a`) off the original matching's membership
    `(hmatch a).1`. List-pinning-independent — it consumes whatever head the cycle
    agent has, not the intended `p_i`, so it does not prejudge the open
    list-pinning decision. This is the membership half of the upper-matching
    witness's `IsPairMatching` obligation in `solvableInTable_step`. -/
theorem rotationShift_mem_prof
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hdual : Phase1Duality reduced)
    (hrot : IsRotation c reduced)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ) (a : α) :
    rotationShift c μ a ∈ prof a := by
  cases hh : (rotationShiftPartner c a).head? with
  | some b =>
    exact rotationShift_mem_prof_cycle c reduced prof hvalid hcompat hsym hdual hrot μ hh
  | none =>
    have hoff : rotationShift c μ a = μ a := by simp [rotationShift, hh]
    rw [hoff]; exact (hmatch a).1

omit [Fintype α] in
/-- **The rotation-shift witness is matching-consistent on a cycle agent** — the
    second `IsPairMatching` conjunct (`μ (pairPartner a (μ a)) = μ a`) for the
    upper-matching witness, restricted to a cycle agent `a` with head shift partner
    `b`. The shifted coalition is `{a, b}` (`hhead`), distinct (`rotationShift_head_ne`)
    so its `pairPartner` is `b` (`rotationShift_pairPartner_cycle`); the partner's
    own shifted coalition is `{b, a} = {a, b}` once its head is pinned to `a`. The
    pinning `hpin` is taken as a hypothesis rather than derived, so this stays
    **list-pinning-independent** — it does not prejudge the open cycle-simplicity
    decision (that `rotationShiftPartner c b = [a]`), only consumes it; deriving
    `hpin` from the cycle structure is the remaining gap of the matching-consistency
    obligation in `solvableInTable_step`. -/
lemma rotationShift_consistency_cycle
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hrot : IsRotation c reduced)
    (μ : Grouping α) {a b : α}
    (hhead : (rotationShiftPartner c a).head? = some b)
    (hpin : (rotationShiftPartner c b).head? = some a) :
    rotationShift c μ (pairPartner a (rotationShift c μ a)) = rotationShift c μ a := by
  have hne : a ≠ b := rotationShift_head_ne c reduced prof hsize hcompat hrot hhead
  have hpp : pairPartner a (rotationShift c μ a) = b :=
    rotationShift_pairPartner_cycle c μ hhead hne
  have hcoal_a : rotationShift c μ a = {a, b} := by simp [rotationShift, hhead]
  have hcoal_b : rotationShift c μ b = {b, a} := by simp [rotationShift, hpin]
  rw [hpp, hcoal_b, hcoal_a]
  exact Finset.pair_comm b a

omit [Fintype α] in
/-- **The rotation-shift witness is matching-consistent everywhere** — the second
    `IsPairMatching` conjunct (`μ' (pairPartner a (μ' a)) = μ' a` for `μ' = rotationShift c μ`)
    for *every* agent, lifting the cycle-only `rotationShift_consistency_cycle` across the
    cycle / off-cycle split (the consistency analogue of how `rotationShift_mem_prof` lifts
    `rotationShift_mem_prof_cycle`). On a cycle agent (`head? = some b`) it reads off
    `rotationShift_consistency_cycle`, supplied the head-pinning `hpin`; off the cycle
    (`head? = none`, so `rotationShift c μ a = μ a`) it stays inside `μ` and closes by `μ`'s
    own consistency `(hmatch a).2`, using `hclosed` to keep the μ-partner off the cycle too.
    The two structural hypotheses — `hpin` (head-symmetry on cycle agents) and `hclosed`
    (off-cycle agents have off-cycle μ-partners) — are exactly the list-pinning /
    all-or-nothing content of the upper-matching branch, taken as hypotheses so the lemma
    stays list-pinning-independent. This is the consistency half of the upper-matching
    witness's `IsPairMatching` obligation in `solvableInTable_step`. -/
theorem rotationShift_consistency
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hrot : IsRotation c reduced)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ)
    (hpin : ∀ a b : α, (rotationShiftPartner c a).head? = some b →
      (rotationShiftPartner c b).head? = some a)
    (hclosed : ∀ a : α, (rotationShiftPartner c a).head? = none →
      (rotationShiftPartner c (pairPartner a (μ a))).head? = none)
    (a : α) :
    rotationShift c μ (pairPartner a (rotationShift c μ a)) = rotationShift c μ a := by
  cases hh : (rotationShiftPartner c a).head? with
  | some b =>
    exact rotationShift_consistency_cycle c reduced prof hsize hcompat hrot μ hh (hpin a b hh)
  | none =>
    have hoff_a : rotationShift c μ a = μ a := by simp [rotationShift, hh]
    rw [hoff_a]
    have hoff_p : rotationShift c μ (pairPartner a (μ a)) = μ (pairPartner a (μ a)) := by
      simp [rotationShift, hclosed a hh]
    rw [hoff_p]
    exact (hmatch a).2

omit [Fintype α] in
/-- **The rotation-shift witness is an `IsPairMatching`** — both conjuncts for every agent,
    bundling `rotationShift_mem_prof` (ranked-pair membership) with `rotationShift_consistency`
    (matching-consistency). The `IsPairMatching` half of the upper-matching witness of
    `solvableInTable_step`; the remaining witness halves are `PairwiseStable` and
    avoids-removed-pairs. Carries the same two structural hypotheses (`hpin`, `hclosed`) as
    `rotationShift_consistency`. -/
theorem rotationShift_isPairMatching
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof) (hsize : SizeTwo prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hdual : Phase1Duality reduced)
    (hrot : IsRotation c reduced)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ)
    (hpin : ∀ a b : α, (rotationShiftPartner c a).head? = some b →
      (rotationShiftPartner c b).head? = some a)
    (hclosed : ∀ a : α, (rotationShiftPartner c a).head? = none →
      (rotationShiftPartner c (pairPartner a (μ a))).head? = none) :
    IsPairMatching prof (rotationShift c μ) := by
  intro a
  exact ⟨rotationShift_mem_prof c reduced prof hvalid hcompat hsym hdual hrot μ hmatch a,
    rotationShift_consistency c reduced prof hsize hcompat hrot μ hmatch hpin hclosed a⟩

omit [Fintype α] in
/-- **The rotation-shift witness avoids every removed pair** — the
    avoids-removed-pairs half of the upper-matching witness of
    `solvableInTable_step`, assembled across the cycle / off-cycle split into the
    exact `havoid` shape `stablePair_eliminate_of_avoids` consumes. On a cycle
    agent (`head? = some b`) the shifted `pairPartner` is the head shift partner
    `b` (`rotationShift_pairPartner_cycle`, distinct via `rotationShift_head_ne`),
    so the cycle-avoid hypothesis rules it out of `rotationRemovals`; off the
    cycle (`head? = none`) the shift keeps `μ`'s coalition and the agent has no
    removal at all (`rotationRemovals_nil_of_rotationShiftPartner_nil`). Taking
    the cycle-avoid as a hypothesis keeps the lemma list-pinning-independent — the
    same consume-the-pin discipline as `rotationShift_consistency`'s
    `hpin`/`hclosed`, the structural facts the upper-matching branch discharges
    from all-or-nothing. -/
theorem rotationShift_avoids_removed
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hrot : IsRotation c reduced)
    (μ : Grouping α)
    (hcycle_avoid : ∀ a b : α, (rotationShiftPartner c a).head? = some b →
      b ∉ rotationRemovals c a)
    (a : α) :
    pairPartner a (rotationShift c μ a) ∉ rotationRemovals c a := by
  cases hh : (rotationShiftPartner c a).head? with
  | some b =>
    have hne : a ≠ b := rotationShift_head_ne c reduced prof hsize hcompat hrot hh
    rw [rotationShift_pairPartner_cycle c μ hh hne]
    exact hcycle_avoid a b hh
  | none =>
    have hnil : rotationShiftPartner c a = [] := by
      cases hl : rotationShiftPartner c a with
      | nil => rfl
      | cons hd tl => rw [hl] at hh; simp at hh
    rw [rotationShift_off c μ a hnil, rotationRemovals_nil_of_rotationShiftPartner_nil hnil]
    simp

omit [Fintype α] in
/-- **The rotation-shift witness survives in the reduced table** —
    `StablePairInvariant reduced prof (rotationShift c μ)`: every shifted partner is
    still present in `reduced`. On a cycle agent with head shift partner `b` the
    shifted `pairPartner` is `b` (`rotationShift_pairPartner_cycle`, distinct via
    `rotationShift_head_ne`), a rotation edge `q_i ↦ p_i` / `p_i ↦ q_i`
    (`mem_rotationShiftPartner`): the `p_i ↦ q_i` direction is `IsRotation`'s
    second-choice membership `q_i ∈ reduced p_i` (`List.mem_of_getElem?` on the
    `[1]?` field), and the `q_i ↦ p_i` direction is its symmetric image (`hsym`).
    Off the cycle the shift keeps `μ`'s coalition, present by `hinv`. The
    `StablePairInvariant reduced` half of the upper-matching witness — fed, with the
    avoids-removed half, to `stablePair_eliminate_of_avoids` in
    `solvableInTable_step`. Needs no all-or-nothing — only rotation structure +
    table symmetry. -/
theorem rotationShift_stablePairInvariant
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hrot : IsRotation c reduced)
    (μ : Grouping α) (hinv : StablePairInvariant reduced prof μ) :
    StablePairInvariant reduced prof (rotationShift c μ) := by
  intro a
  cases hh : (rotationShiftPartner c a).head? with
  | some b =>
    rw [rotationShift_pairPartner_cycle c μ hh
      (rotationShift_head_ne c reduced prof hsize hcompat hrot hh)]
    have hb_mem : b ∈ rotationShiftPartner c a :=
      List.mem_of_mem_head? (Option.mem_def.mpr hh)
    obtain ⟨i, hcase⟩ := mem_rotationShiftPartner hb_mem
    obtain ⟨hsec, _, _⟩ := hrot i
    have hq_mem : (c.pairs.get i).2 ∈ reduced (c.pairs.get i).1 :=
      List.mem_of_getElem? hsec
    rcases hcase with ⟨ha, hb_eq⟩ | ⟨ha, hb_eq⟩
    · rw [ha, hb_eq]; exact (hsym _ _).mp hq_mem
    · rw [ha, hb_eq]; exact hq_mem
  | none =>
    have hoff : rotationShift c μ a = μ a := by simp [rotationShift, hh]
    rw [hoff]; exact hinv a

private lemma filter_indices_ordered {α : Type*} (l : List α) (p : α → Bool)
    {j k : ℕ} (hj : j < (l.filter p).length) (hk : k < (l.filter p).length) (hjk : j < k) :
    ∃ (j' : ℕ) (_ : j' < l.length) (k' : ℕ) (_ : k' < l.length),
      j' < k' ∧ l[j'] = (l.filter p)[j] ∧ l[k'] = (l.filter p)[k] := by
  induction l generalizing j k with
  | nil => simp at hj
  | cons a t ih =>
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha] at hj hk
      simp only [List.length_cons] at hj hk ⊢
      cases j with
      | zero =>
        cases k with
        | zero => omega
        | succ k' =>
          have hk' : k' < (t.filter p).length := by omega
          have := List.filter_sublist (p := p) (l := t) |>.subset (List.getElem_mem hk')
          obtain ⟨k'', hk'', hk''_eq⟩ := List.mem_iff_getElem.mp this
          exact ⟨0, by omega, k'' + 1, by omega, by omega,
                 by simp [List.filter_cons_of_pos ha],
                 by simp [List.getElem_cons_succ, List.filter_cons_of_pos ha, hk''_eq]⟩
      | succ j' =>
        cases k with
        | zero => omega
        | succ k' =>
          have hj' : j' < (t.filter p).length := by omega
          have hk' : k' < (t.filter p).length := by omega
          obtain ⟨j'', hj'', k'', hk'', hjk'', hj''_eq, hk''_eq⟩ := ih hj' hk' (by omega)
          exact ⟨j'' + 1, by omega, k'' + 1, by omega, by omega,
                 by simp [List.getElem_cons_succ, List.filter_cons_of_pos ha, hj''_eq],
                 by simp [List.getElem_cons_succ, List.filter_cons_of_pos ha, hk''_eq]⟩
    · rw [List.filter_cons_of_neg ha] at hj hk
      simp only [List.length_cons] at ⊢
      obtain ⟨j', hj', k', hk', hjk', hj'_eq, hk'_eq⟩ := ih hj hk hjk
      exact ⟨j' + 1, by omega, k' + 1, by omega, by omega,
             by simp [List.getElem_cons_succ, List.filter_cons_of_neg ha, hj'_eq],
             by simp [List.getElem_cons_succ, List.filter_cons_of_neg ha, hk'_eq]⟩

omit [Fintype α] in
/-- Compatibility lifts through three list transforms: shrinking to length ≤ 1,
    leaving alone, or filtering. Filtering uses `filter_indices_ordered` to
    convert reduced-list indices back to original ones. -/
private lemma compat_of_three_cases
    {prof : PreferenceProfile α} {x : α} {l l' : List α}
    (compat : ∀ j k : Fin l.length, j < k →
      Ranks prof x {x, l[j]} {x, l[k]})
    (h : l'.length ≤ 1 ∨ l' = l ∨ ∃ p, l' = l.filter p) :
    ∀ j k : Fin l'.length, j < k →
      Ranks prof x {x, l'[j]} {x, l'[k]} := by
  rcases h with hshort | heq | ⟨p, hp⟩
  · intro j k hjk
    exfalso
    have hj1 : j.val < 1 := lt_of_lt_of_le j.isLt hshort
    have hk1 : k.val < 1 := lt_of_lt_of_le k.isLt hshort
    omega
  · subst heq; exact compat
  · subst hp
    intro j k hjk
    obtain ⟨j', hj', k', hk', hjk', hj'_eq, hk'_eq⟩ :=
      filter_indices_ordered l p j.isLt k.isLt hjk
    convert compat ⟨j', hj'⟩ ⟨k', hk'⟩ hjk' using 3
    · exact hj'_eq.symm
    · exact hk'_eq.symm

omit [Fintype α] in
/-- Compatibility lifts through a prefix (`take`): a prefix keeps positional
    indexing (`getElem_take`), so ranked-order comparisons among the kept
    elements transfer directly. The `take`-case companion to
    `compat_of_three_cases`, used by `reduceStep` at the truncated first choice. -/
private lemma compat_of_take
    {prof : PreferenceProfile α} {x : α} {l : List α} {n : ℕ}
    (compat : ∀ j k : Fin l.length, j < k →
      Ranks prof x {x, l[j]} {x, l[k]}) :
    ∀ j k : Fin (l.take n).length, j < k →
      Ranks prof x {x, (l.take n)[j]} {x, (l.take n)[k]} := by
  intro j k hjk
  have hjl : j.val < l.length := lt_of_lt_of_le j.isLt (List.length_take_le' n l)
  have hkl : k.val < l.length := lt_of_lt_of_le k.isLt (List.length_take_le' n l)
  have hj : (l.take n)[j] = l[j.val]'hjl := by simp only [Fin.getElem_fin, List.getElem_take]
  have hk : (l.take n)[k] = l[k.val]'hkl := by simp only [Fin.getElem_fin, List.getElem_take]
  rw [hj, hk]
  exact compat ⟨j.val, hjl⟩ ⟨k.val, hkl⟩ hjk

omit [Fintype α] in
/-- Compatibility lifts through the three transforms `reduceStep` applies: a
    prefix (`take`), leaving alone, or filtering. The equation is taken as a
    hypothesis so the (dependent) subject can be `subst`ed — the reduce-pass
    analogue of `compat_of_three_cases`, with `take` replacing the length-≤-1
    shrink case. -/
private lemma compat_of_reduce_cases
    {prof : PreferenceProfile α} {x : α} {l l' : List α}
    (compat : ∀ j k : Fin l.length, j < k →
      Ranks prof x {x, l[j]} {x, l[k]})
    (h : (∃ n, l' = l.take n) ∨ l' = l ∨ ∃ p, l' = l.filter p) :
    ∀ j k : Fin l'.length, j < k →
      Ranks prof x {x, l'[j]} {x, l'[k]} := by
  rcases h with ⟨n, hn⟩ | heq | ⟨p, hp⟩
  · subst hn; exact compat_of_take compat
  · subst heq; exact compat
  · subst hp
    intro j k hjk
    obtain ⟨j', hj', k', hk', hjk', hj'_eq, hk'_eq⟩ :=
      filter_indices_ordered l p j.isLt k.isLt hjk
    convert compat ⟨j', hj'⟩ ⟨k', hk'⟩ hjk' using 3
    · exact hj'_eq.symm
    · exact hk'_eq.symm

omit [Fintype α] in
/-- **Rotation elimination preserves reduced-table invariants.** -/
theorem rotation_elimination_preserves_invariants
    (c : RotationCycle α)
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (_hsize : SizeTwo prof)
    (hrot : IsRotation c reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced) :
    let reduced' := eliminateRotation reduced c
    ReducedTableSymmetric reduced' ∧
    ReducedListCompatible reduced' prof := by
  refine ⟨fun a b => ?_, fun a j k hjk => ?_⟩
  · simp only [eliminateRotation, List.mem_filter, decide_eq_true_eq]
    constructor <;> intro ⟨hmem, hnotrem⟩
    · exact ⟨(hsym a b).mp hmem, fun habs => hnotrem (rotationRemovals_symm habs)⟩
    · exact ⟨(hsym b a).mp hmem, fun habs => hnotrem (rotationRemovals_symm habs)⟩
  · exact compat_of_three_cases (hcompat a) (Or.inr (Or.inr ⟨_, rfl⟩)) j k hjk

omit [Fintype α] in
/-- **Rotation elimination preserves duplicate-freeness.** Each list is
    filtered (`· ∉ rotationRemovals c a`), and `List.filter` keeps `Nodup`.
    Prerequisite for the phase-2 `cascade → reduceTable` swap: every
    `reduceTable` invariant lemma (`reduceTable_preserves_symmetric`,
    `phase1Duality_reduceTable`, `cascadeInvariant_reduceTable`) requires its
    input to be `ReducedTableNodup`, so nodup must be carried across each
    `eliminateRotation` in the Phase-2 recursion. -/
theorem eliminateRotation_preserves_nodup
    (reduced : α → List α) (c : RotationCycle α)
    (hnodup : ReducedTableNodup reduced) :
    ReducedTableNodup (eliminateRotation reduced c) := by
  intro a
  simp only [eliminateRotation]
  exact List.Nodup.filter _ (hnodup a)

/-! ## Phase 1 — proposal-rejection loop -/

noncomputable section
open Classical

/-! ## Phase 2 — iterated rotation elimination -/

/-- Rotation elimination strictly decreases total list lengths. Witnessed by
    rotation position 0: the successor proposer `p_next = last(reduced q_0)`
    is included in the removal list computed for agent `q_0` (also when the
    cycle is a length-1 self-loop). So `(reduced q_0).filter` is a strict
    sublist of `reduced q_0`, and the sum over all agents drops by at least
    one. -/
theorem eliminateRotation_decreases_totalLength
    (reduced : α → List α)
    (c : RotationCycle α)
    (hrot : IsRotation c reduced) :
    totalLength (eliminateRotation reduced c) < totalLength reduced := by
  classical
  have h0 : 0 < c.pairs.length := c.length_pos
  obtain ⟨_, hlast, hne⟩ := hrot ⟨0, h0⟩
  set q : α := (c.pairs.get ⟨0, h0⟩).2 with hq_def
  set p_next : α :=
    (c.pairs.get (nextFin (⟨0, h0⟩ : Fin c.pairs.length) c.length_pos)).1 with hp_def
  have hp_mem : p_next ∈ reduced q := by
    have h := hlast
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
        Option.getD_some] at h
    rw [← h]
    exact List.getLast_mem hne
  have hp_in_rem : p_next ∈ rotationRemovals c q := by
    simp only [rotationRemovals, List.mem_filterMap]
    refine ⟨⟨0, h0⟩, List.mem_finRange _, ?_⟩
    rw [if_pos rfl]
  have heq_q : (eliminateRotation reduced c) q =
      (reduced q).filter (fun x => decide (x ∉ rotationRemovals c q)) := rfl
  have h_strict : ((eliminateRotation reduced c) q).length < (reduced q).length := by
    rw [heq_q]
    have hsub : List.Sublist
        ((reduced q).filter (fun x => decide (x ∉ rotationRemovals c q))) (reduced q) :=
      List.filter_sublist
    rcases lt_or_eq_of_le hsub.length_le with hlt | heq
    · exact hlt
    · exfalso
      have hfilt_eq := List.Sublist.eq_of_length hsub heq
      have hpfilt :
          p_next ∈ (reduced q).filter (fun x => decide (x ∉ rotationRemovals c q)) := by
        rw [hfilt_eq]; exact hp_mem
      rw [List.mem_filter] at hpfilt
      have : p_next ∉ rotationRemovals c q := by
        have := hpfilt.2
        simpa using this
      exact this hp_in_rem
  have h_le : ∀ a, ((eliminateRotation reduced c) a).length ≤ (reduced a).length := by
    intro a
    show ((reduced a).filter _).length ≤ _
    exact List.filter_sublist.length_le
  unfold totalLength
  exact Finset.sum_lt_sum (fun a _ => h_le a) ⟨q, Finset.mem_univ _, h_strict⟩

/-! ### Phase 2 iteration step -/

/-- Phase 2 iteration step: from `p`, follow
    `last(reduced (second(reduced p)))`. Self-loop default when
    `(reduced p).length < 2`. -/
noncomputable def phase2Step (reduced : α → List α) (p : α) : α :=
  if h : 2 ≤ (reduced p).length then
    (reduced (reduced p)[1]).getLastD (reduced p)[1]
  else
    p

omit [DecidableEq α] [Fintype α] in
/-- Under `ReducedTableSymmetric + CascadeInvariant`, the Phase 2 step
    preserves `length ≥ 2`. The key well-definedness fact for
    `findRotation`'s iteration. -/
lemma phase2Step_length_ge_two
    {reduced : α → List α}
    (hsym : ReducedTableSymmetric reduced)
    (hcasc : CascadeInvariant reduced)
    {p : α} (hp : 2 ≤ (reduced p).length) :
    2 ≤ (reduced (phase2Step reduced p)).length := by
  have h1 : 1 < (reduced p).length := hp
  set q : α := (reduced p)[1] with hq_def
  have hstep : phase2Step reduced p = (reduced q).getLastD q := by
    unfold phase2Step
    rw [dif_pos hp]
  have hqp : q ∈ reduced p := List.getElem_mem h1
  have hpq : p ∈ reduced q := (hsym p q).mp hqp
  have hqne : reduced q ≠ [] := List.ne_nil_of_mem hpq
  have hqpos : 1 ≤ (reduced q).length := List.length_pos_of_ne_nil hqne
  have hqlen2 : 2 ≤ (reduced q).length := by
    by_contra h
    push_neg at h
    have hqlen1 : (reduced q).length = 1 := by omega
    have : (reduced p).length = 1 := hcasc q p hpq hqlen1
    omega
  set p' : α := (reduced q).getLast hqne with hp'_def
  have hstep_eq : phase2Step reduced p = p' := by
    rw [hstep, hp'_def, List.getLastD_eq_getLast?,
        List.getLast?_eq_some_getLast hqne, Option.getD_some]
  rw [hstep_eq]
  have hp'_mem : p' ∈ reduced q := by rw [hp'_def]; exact List.getLast_mem hqne
  have hqp' : q ∈ reduced p' := (hsym q p').mp hp'_mem
  have hp'ne : reduced p' ≠ [] := List.ne_nil_of_mem hqp'
  have hp'pos : 1 ≤ (reduced p').length := List.length_pos_of_ne_nil hp'ne
  by_contra h
  push_neg at h
  have hp'len1 : (reduced p').length = 1 := by omega
  have : (reduced q).length = 1 := hcasc p' q hqp' hp'len1
  omega

omit [DecidableEq α] [Fintype α] in
/-- Every iterate of `phase2Step` from a length-≥-2 agent stays in the
    length-≥-2 region. The well-definedness fact `findRotation`'s cycle
    extraction relies on: along the orbit `a, step a, step² a, …` each
    `(reduced pᵢ)[1]` is defined, so the proposer-partner pairs are
    well-formed at every position. Induction from `phase2Step_length_ge_two`. -/
lemma phase2Step_iterate_length_ge_two
    {reduced : α → List α}
    (hsym : ReducedTableSymmetric reduced)
    (hcasc : CascadeInvariant reduced)
    {a : α} (ha : 2 ≤ (reduced a).length) (n : ℕ) :
    2 ≤ (reduced ((phase2Step reduced)^[n] a)).length := by
  induction n with
  | zero => simpa using ha
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact phase2Step_length_ge_two hsym hcasc ih

omit [DecidableEq α] in
/-- The `phase2Step` orbit from any agent eventually repeats: finiteness of
    `α` forces `(phase2Step reduced)^[i] a = (phase2Step reduced)^[j] a` for
    some `i < j`. With `phase2Step_iterate_length_ge_two` (the orbit stays
    length-≥-2), this is the well-definedness ingredient `findRotation`'s
    cycle extraction consumes: the orbit enters a cycle, possibly a
    length-1 self-loop. -/
lemma phase2Step_orbit_repeats (reduced : α → List α) (a : α) :
    ∃ i j : ℕ, i < j ∧
      (phase2Step reduced)^[i] a = (phase2Step reduced)^[j] a := by
  obtain ⟨i, j, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (phase2Step reduced)^[n] a)
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨i, j, h, heq⟩
  · exact ⟨j, i, h, heq.symm⟩

omit [DecidableEq α] [Fintype α] in
/-- Per-step rotation facts at a length-≥-2 agent `p`. The proposer-partner
    pair `(p, (reduced p)[1])` together with the successor `phase2Step reduced p`
    satisfies the `IsRotation` conjuncts: `q = second(reduced p)` is recorded
    at index 1, `last(reduced q)` is the successor, and `reduced q` is
    nonempty. Instantiated at each cycle position
    `pᵢ = (phase2Step reduced)^[i] a`, it discharges `IsRotation` pointwise
    (the successor `phase2Step reduced pᵢ` is the next orbit element `pᵢ₊₁`). -/
lemma phase2Step_rotation_step
    {reduced : α → List α}
    (hsym : ReducedTableSymmetric reduced)
    {p : α} (hp : 2 ≤ (reduced p).length) :
    (reduced p)[1]? = some ((reduced p)[1]) ∧
      (reduced ((reduced p)[1])).getLastD ((reduced p)[1]) = phase2Step reduced p ∧
      (reduced ((reduced p)[1])) ≠ [] := by
  have h1 : 1 < (reduced p).length := hp
  refine ⟨List.getElem?_eq_getElem h1, ?_, ?_⟩
  · unfold phase2Step; rw [dif_pos hp]
  · have hqp : (reduced p)[1] ∈ reduced p := List.getElem_mem h1
    exact List.ne_nil_of_mem ((hsym p _).mp hqp)

omit [DecidableEq α] in
/-- The `phase2Step` orbit from a length-≥-2 agent reaches a periodic point.
    Combines `phase2Step_orbit_repeats` (finiteness forces a repeat) with
    `phase2Step_iterate_length_ge_two` (the orbit stays length-≥-2). These
    duality-agnostic lemmas admit period 1, so the backbone is stated for
    `r ≥ 1`; under `Phase1Duality` the period is in fact ≥ 2
    (`isRotation_no_selfLoop`). This is the cyclic backbone `findRotation`
    builds its `pairs` list on: `b, step b, …, step^[r-1] b` with
    `step^[r] b = b` closing the cycle. -/
lemma phase2Step_periodic_point
    {reduced : α → List α}
    (hsym : ReducedTableSymmetric reduced)
    (hcasc : CascadeInvariant reduced)
    {a : α} (ha : 2 ≤ (reduced a).length) :
    ∃ (b : α) (r : ℕ), 2 ≤ (reduced b).length ∧ 0 < r ∧
      (phase2Step reduced)^[r] b = b := by
  obtain ⟨i, j, hij, heq⟩ := phase2Step_orbit_repeats reduced a
  refine ⟨(phase2Step reduced)^[i] a, j - i,
    phase2Step_iterate_length_ge_two hsym hcasc ha i, by omega, ?_⟩
  have hadd : j - i + i = j := by omega
  calc (phase2Step reduced)^[j - i] ((phase2Step reduced)^[i] a)
      = (phase2Step reduced)^[j - i + i] a :=
        (Function.iterate_add_apply _ _ _ _).symm
    _ = (phase2Step reduced)^[j] a := by rw [hadd]
    _ = (phase2Step reduced)^[i] a := heq.symm

omit [DecidableEq α] in
/-- **A `phase2Step`-periodic point with a *minimal* period — distinct orbit
    agents.** Strengthens `phase2Step_periodic_point`: that lemma is built on
    the non-minimal `phase2Step_orbit_repeats` (a bare `i < j` collision), so
    its period `r` may revisit agents and the orbit `b, step b, …, step^[r-1] b`
    need not be a *simple* cycle. Choosing `r = Function.minimalPeriod` instead
    makes the orbit agents **pairwise distinct** for indices `< r`
    (`Function.iterate_injOn_Iio_minimalPeriod`), so each cycle agent occurs at a
    *unique* index. This is the cycle-simplicity fact the upper-matching witness
    of `solvableInTable_step` was missing: index-uniqueness pins
    `rotationShiftPartner`'s list to a singleton (the `hpin` / list-pinning
    obligation), and answers the long-deferred "does `RotationCycle` need a
    distinctness field?" question — **derivable, no field**. The witness `b` and
    its length-≥-2 status are inherited unchanged from `phase2_periodic_point`;
    only the period is re-chosen minimal, and `b` is a genuine periodic point
    (`mk_mem_periodicPts`) so the minimal period is positive and is itself a
    period. -/
lemma phase2Step_periodic_point_distinct
    {reduced : α → List α}
    (hsym : ReducedTableSymmetric reduced)
    (hcasc : CascadeInvariant reduced)
    {a : α} (ha : 2 ≤ (reduced a).length) :
    ∃ (b : α) (r : ℕ), 2 ≤ (reduced b).length ∧ 0 < r ∧
      (phase2Step reduced)^[r] b = b ∧
      (∀ k₁ k₂ : ℕ, k₁ < r → k₂ < r →
        (phase2Step reduced)^[k₁] b = (phase2Step reduced)^[k₂] b → k₁ = k₂) := by
  obtain ⟨b, r₀, hb_len, hr₀_pos, hcycle₀⟩ := phase2Step_periodic_point hsym hcasc ha
  have hmem : b ∈ Function.periodicPts (phase2Step reduced) :=
    Function.mk_mem_periodicPts hr₀_pos hcycle₀
  refine ⟨b, Function.minimalPeriod (phase2Step reduced) b, hb_len,
    Function.minimalPeriod_pos_of_mem_periodicPts hmem,
    Function.isPeriodicPt_minimalPeriod (phase2Step reduced) b, ?_⟩
  intro k₁ k₂ hk₁ hk₂ heq
  exact Function.iterate_injOn_Iio_minimalPeriod (Set.mem_Iio.mpr hk₁) (Set.mem_Iio.mpr hk₂) heq

/-- The rotation cycle read off a `phase2Step`-periodic point: the orbit
    `b, step b, …, step^[r-1] b` paired with each second-choice partner
    `(step^[k] b, (reduced (step^[k] b))[1])`. Length `r ≥ 1` is the period. -/
noncomputable def periodicCycle (reduced : α → List α) (b : α) (r : ℕ)
    (hr : 0 < r)
    (hlen : ∀ k, 2 ≤ (reduced ((phase2Step reduced)^[k] b)).length) :
    RotationCycle α where
  pairs := (List.range r).map fun k =>
    ((phase2Step reduced)^[k] b, (reduced ((phase2Step reduced)^[k] b))[1]'(hlen k))
  length_pos := by rw [List.length_map, List.length_range]; exact hr

omit [DecidableEq α] [Fintype α] in
/-- The periodic cycle is a genuine rotation. At each position
    `phase2Step_rotation_step` discharges the `IsRotation` conjuncts for
    the pair `(step^[k] b, (reduced (step^[k] b))[1])` and successor
    `step^[k+1] b`; the wrap-around at the last index closes via the period
    equation `step^[r] b = b` (so `step^[(k+1) mod r] b = step (step^[k] b)`
    throughout). -/
lemma periodicCycle_isRotation {reduced : α → List α}
    {b : α} {r : ℕ} {hr : 0 < r}
    {hlen : ∀ k, 2 ≤ (reduced ((phase2Step reduced)^[k] b)).length}
    (hsym : ReducedTableSymmetric reduced)
    (hcycle : (phase2Step reduced)^[r] b = b) :
    IsRotation (periodicCycle reduced b r hr hlen) reduced := by
  have key : ∀ j : Fin (periodicCycle reduced b r hr hlen).pairs.length,
      (periodicCycle reduced b r hr hlen).pairs.get j
        = ((phase2Step reduced)^[j.val] b,
           (reduced ((phase2Step reduced)^[j.val] b))[1]'(hlen j.val)) := by
    intro j
    simp only [periodicCycle, List.get_eq_getElem, List.getElem_map, List.getElem_range]
  have hcl : (periodicCycle reduced b r hr hlen).pairs.length = r := by
    simp only [periodicCycle, List.length_map, List.length_range]
  intro i
  obtain ⟨m, hm⟩ := i
  have hmr : m < r := hcl ▸ hm
  have rstep := phase2Step_rotation_step hsym (hlen m)
  have hmod : (phase2Step reduced)^[(m + 1) % r] b
      = phase2Step reduced ((phase2Step reduced)^[m] b) := by
    rw [show phase2Step reduced ((phase2Step reduced)^[m] b)
          = (phase2Step reduced)^[m + 1] b from
        (Function.iterate_succ_apply' (phase2Step reduced) m b).symm]
    rcases Nat.lt_or_ge (m + 1) r with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
    · have heq : m + 1 = r := by omega
      rw [heq, Nat.mod_self, Function.iterate_zero_apply, hcycle]
  have hget1 := key ⟨m, hm⟩
  have hnv : (nextFin (⟨m, hm⟩ : Fin (periodicCycle reduced b r hr hlen).pairs.length)
      (periodicCycle reduced b r hr hlen).length_pos).val = (m + 1) % r := by
    show (m + 1) % (periodicCycle reduced b r hr hlen).pairs.length = (m + 1) % r
    rw [hcl]
  have hgetn := key (nextFin ⟨m, hm⟩ (periodicCycle reduced b r hr hlen).length_pos)
  rw [hnv] at hgetn
  refine ⟨?_, ?_, ?_⟩
  · rw [hget1]; exact rstep.1
  · rw [hget1, hgetn]; exact rstep.2.1.trans hmod.symm
  · rw [hget1]; exact rstep.2.2

/-- A rotation cycle's proposer entries are distinct across indices: each agent
    occurs as a proposer `pᵢ` at a *unique* position. The cycle-simplicity fact
    the upper-matching witness of `solvableInTable_step` needs to pin
    `rotationShiftPartner`'s list to a singleton; `findRotation` establishes it
    by building on the minimal-period `phase2Step_periodic_point_distinct`. -/
def ProposersDistinct (c : RotationCycle α) : Prop :=
  ∀ i j : Fin c.pairs.length, (c.pairs.get i).1 = (c.pairs.get j).1 → i = j

omit [DecidableEq α] [Fintype α] in
/-- Reading proposer index-uniqueness off the minimal period: when the orbit
    agents `step^[k] b` are pairwise distinct for `k < r` (as
    `phase2Step_periodic_point_distinct` guarantees), the `periodicCycle`'s
    proposer entries — which are exactly those orbit agents — are distinct across
    indices. The `ProposersDistinct` half `findRotation` adds to its output by
    building on the distinct period. -/
lemma periodicCycle_proposers_distinct {reduced : α → List α}
    {b : α} {r : ℕ} {hr : 0 < r}
    {hlen : ∀ k, 2 ≤ (reduced ((phase2Step reduced)^[k] b)).length}
    (hdist : ∀ k₁ k₂ : ℕ, k₁ < r → k₂ < r →
      (phase2Step reduced)^[k₁] b = (phase2Step reduced)^[k₂] b → k₁ = k₂) :
    ProposersDistinct (periodicCycle reduced b r hr hlen) := by
  have hcl : (periodicCycle reduced b r hr hlen).pairs.length = r := by
    simp only [periodicCycle, List.length_map, List.length_range]
  have key : ∀ k : Fin (periodicCycle reduced b r hr hlen).pairs.length,
      ((periodicCycle reduced b r hr hlen).pairs.get k).1
        = (phase2Step reduced)^[k.val] b := by
    intro k
    simp only [periodicCycle, List.get_eq_getElem, List.getElem_map, List.getElem_range]
  intro i j h
  rw [key i, key j] at h
  exact Fin.ext (hdist i.val j.val (lt_of_lt_of_eq i.isLt hcl) (lt_of_lt_of_eq j.isLt hcl) h)

/-- Find a rotation in the reduced table. The return type packages the
    cycle with its `IsRotation` witness *and* `ProposersDistinct` (cycle
    simplicity) — the prior signature returned an unconstrained `RotationCycle α`,
    which is trivially inhabited from any element of `α` and so did not bind the
    result to be a real rotation, and the bare `IsRotation` form left the cycle
    free to revisit agents.

    `phase2Step_periodic_point_distinct` supplies the cyclic backbone (a
    minimal-period point `b`, whose orbit agents are pairwise distinct),
    `periodicCycle` reads off the proposer-partner pairs, `periodicCycle_isRotation`
    certifies them, and `periodicCycle_proposers_distinct` reads off index-uniqueness
    of the proposers. -/
noncomputable def findRotation (reduced : α → List α)
    (hsym : ReducedTableSymmetric reduced)
    (hcasc : CascadeInvariant reduced)
    (a : α) (ha : 2 ≤ (reduced a).length) :
    { c : RotationCycle α // IsRotation c reduced ∧ ProposersDistinct c } :=
  -- `phase2Step_periodic_point_distinct` is an existence proof (`Prop`); the
  -- subtype result is data, so the witnesses are read off by `Classical.choose`
  -- rather than `obtain` (large elimination of `Exists` into `Type` is barred).
  let h := phase2Step_periodic_point_distinct hsym hcasc ha
  let b := h.choose
  let r := h.choose_spec.choose
  let hspec := h.choose_spec.choose_spec
  ⟨periodicCycle reduced b r hspec.2.1
      (fun k => phase2Step_iterate_length_ge_two hsym hcasc hspec.1 k),
    periodicCycle_isRotation (hr := hspec.2.1)
      (hlen := fun k => phase2Step_iterate_length_ge_two hsym hcasc hspec.1 k)
      hsym hspec.2.2.1,
    periodicCycle_proposers_distinct hspec.2.2.2⟩

/-! ### Reduce pass (duality-restoring; mirrors `src/irving.py::_reduce`) -/

/-- One reduce step keyed on agent `a`: restore the stable-table (duality)
    invariant at `a`'s first choice `f`. Every entry `f` ranks strictly
    below `a` cannot belong to a stable matching, so `f`'s list is truncated
    to the prefix ending at `a` (`take (idxOf a + 1)`) and `f` is deleted
    from each dropped entry's list. A no-op when `a`'s list is empty or
    `a ∉ reduced f` (then the prefix keeps everything and nothing is
    dropped). Mirrors one inner action of `src/irving.py::_reduce`; it
    preserves `Phase1Duality` (the retired `_cascade` did not). -/
def reduceStep (reduced : α → List α) (a : α) : α → List α :=
  let f := (reduced a).head?.getD a
  let keep := (reduced f).idxOf a + 1
  fun x =>
    if x = f then (reduced f).take keep
    else if x ∈ (reduced f).drop keep then (reduced x).filter (· ≠ f)
    else reduced x

omit [Fintype α] in
/-- Per-element non-increase: at every `x`, `reduceStep` produces a list no
    longer than the original — a prefix at `f`, a filter at dropped entries,
    untouched elsewhere. -/
private lemma reduceStep_length_le
    (reduced : α → List α) (a x : α) :
    (reduceStep reduced a x).length ≤ (reduced x).length := by
  simp only [reduceStep]
  split_ifs with hxf hxd
  · rw [hxf]; simp only [List.length_take]; omega
  · exact List.length_filter_le _ _
  · exact le_refl _

/-- `reduceStep` never increases total list lengths. The reduce-pass
    termination measure. -/
lemma reduceStep_totalLength_le (reduced : α → List α) (a : α) :
    totalLength (reduceStep reduced a) ≤ totalLength reduced :=
  Finset.sum_le_sum fun _ _ => reduceStep_length_le _ _ _

/-- `a`'s first choice `f` ranks something strictly below `a` (i.e. `a` is not
    last in `reduced f`), so the stable-table duality invariant is violated at
    `a` and `reduceStep reduced a` truncates `f`'s list. The `reduceTable`
    fixpoint runs while some agent satisfies this; its negation at every `a` is
    exactly `Phase1Duality`'s defining property (first choice ranks last). -/
def reduceNeededAt (reduced : α → List α) (a : α) : Prop :=
  (reduced ((reduced a).head?.getD a)).idxOf a + 1
    < (reduced ((reduced a).head?.getD a)).length

omit [Fintype α] in
/-- `reduceStep` at `a`'s own first choice `f` truncates `reduced f` to the
    prefix ending at `a`. -/
private lemma reduceStep_at_first (reduced : α → List α) (a : α) :
    reduceStep reduced a ((reduced a).head?.getD a)
      = (reduced ((reduced a).head?.getD a)).take
          ((reduced ((reduced a).head?.getD a)).idxOf a + 1) := by
  simp [reduceStep]

omit [Fintype α] in
/-- Strict decrease at `f` when `reduceNeededAt` holds: `reduceStep` drops the
    tail of `reduced f` below `a`. -/
private lemma reduceStep_length_lt_at_first
    (reduced : α → List α) (a : α) (h : reduceNeededAt reduced a) :
    (reduceStep reduced a ((reduced a).head?.getD a)).length
      < (reduced ((reduced a).head?.getD a)).length := by
  rw [reduceStep_at_first, List.length_take]
  unfold reduceNeededAt at h
  omega

/-- Reduce pass (duality-restoring). Iterates `reduceStep` while some agent's
    first choice still fails to rank it last (`reduceNeededAt`). Mirrors
    `src/irving.py::_reduce`; the textbook replacement for the retired
    `cascade`. On termination no agent satisfies `reduceNeededAt`, i.e. every
    agent's first choice ranks it last — the defining property of
    `Phase1Duality`. -/
def reduceTable (reduced : α → List α) : α → List α :=
  if h : ∃ a : α, reduceNeededAt reduced a then
    reduceTable (reduceStep reduced (Classical.choose h))
  else reduced
termination_by totalLength reduced
decreasing_by
  have hspec := Classical.choose_spec h
  unfold totalLength
  exact Finset.sum_lt_sum
    (fun x _ => reduceStep_length_le _ _ x)
    ⟨(reduced (Classical.choose h)).head?.getD (Classical.choose h),
      Finset.mem_univ _, reduceStep_length_lt_at_first _ _ hspec⟩

/-- `reduceTable` does not increase total list lengths. Each `reduceStep` is
    non-increasing (`reduceStep_totalLength_le`), so the iterated application
    stays bounded by the starting total. -/
theorem reduceTable_totalLength_le (reduced : α → List α) :
    totalLength (reduceTable reduced) ≤ totalLength reduced := by
  induction reduced using reduceTable.induct with
  | case1 reduced h ih =>
    rw [reduceTable]
    simp only [dif_pos h]
    exact ih.trans (reduceStep_totalLength_le _ _)
  | case2 reduced h =>
    rw [reduceTable, dif_neg h]

omit [Fintype α] in
/-- `reduceStep` preserves duplicate-freeness: at the first choice `f` it takes
    a prefix (a sublist), at dropped entries it filters, and elsewhere it leaves
    the list untouched — each keeps `Nodup`. -/
private lemma reduceStep_preserves_nodup (reduced : α → List α) (a : α)
    (hnodup : ReducedTableNodup reduced) :
    ReducedTableNodup (reduceStep reduced a) := by
  intro x
  simp only [reduceStep]
  split_ifs
  · exact List.Sublist.nodup (List.take_sublist _ _) (hnodup _)
  · exact List.Nodup.filter _ (hnodup x)
  · exact hnodup x

omit [Fintype α] in
/-- `reduceStep` preserves table symmetry. Truncating `reduced f` to the kept
    prefix and deleting `f` from each dropped entry are mirror operations:
    `Nodup` makes prefix and tail a clean partition, so membership at one
    endpoint matches the symmetric membership at the other (via `hsym`). -/
private lemma reduceStep_preserves_symmetric (reduced : α → List α) (a : α)
    (hnodup : ReducedTableNodup reduced)
    (hsym : ReducedTableSymmetric reduced) :
    ReducedTableSymmetric (reduceStep reduced a) := by
  intro u v
  simp only [reduceStep]
  set f := (reduced a).head?.getD a with hf
  set keep := (reduced f).idxOf a + 1 with hk
  have hmemf : ∀ w, w ∈ reduced f ↔
      w ∈ (reduced f).take keep ∨ w ∈ (reduced f).drop keep := by
    intro w; rw [← List.mem_append, List.take_append_drop]
  have hdisj : ∀ w, w ∈ (reduced f).take keep → w ∈ (reduced f).drop keep → False := by
    intro w hwt hwd
    have hnd : ((reduced f).take keep ++ (reduced f).drop keep).Nodup := by
      rw [List.take_append_drop]; exact hnodup f
    exact (List.nodup_append.mp hnd).2.2 w hwt w hwd rfl
  have memfilter : ∀ x w : α,
      w ∈ (reduced x).filter (· ≠ f) ↔ w ∈ reduced x ∧ w ≠ f := by
    intro x w; simp [List.mem_filter]
  by_cases huf : u = f
  · by_cases hvf : v = f
    · simp only [huf, hvf]
    · rw [huf, if_pos rfl, if_neg hvf]
      by_cases hvd : v ∈ (reduced f).drop keep
      · rw [if_pos hvd, memfilter v f]
        exact ⟨fun hvt => absurd hvt (fun ht => hdisj v ht hvd),
               fun ⟨_, hne⟩ => absurd rfl hne⟩
      · rw [if_neg hvd, show (f ∈ reduced v) ↔ (v ∈ reduced f) from hsym v f, hmemf v]
        exact ⟨Or.inl, fun h => h.resolve_right hvd⟩
  · by_cases hvf : v = f
    · rw [hvf, if_pos rfl, if_neg huf]
      by_cases hud : u ∈ (reduced f).drop keep
      · rw [if_pos hud, memfilter u f]
        exact ⟨fun ⟨_, hne⟩ => absurd rfl hne,
               fun hut => absurd hut (fun ht => hdisj u ht hud)⟩
      · rw [if_neg hud, show (f ∈ reduced u) ↔ (u ∈ reduced f) from hsym u f, hmemf u]
        exact ⟨fun h => h.resolve_right hud, Or.inl⟩
    · rw [if_neg huf, if_neg hvf]
      by_cases hud : u ∈ (reduced f).drop keep <;> by_cases hvd : v ∈ (reduced f).drop keep
      · rw [if_pos hud, if_pos hvd, memfilter u v, memfilter v u,
            show (v ∈ reduced u) ↔ (u ∈ reduced v) from hsym u v]
        exact ⟨fun ⟨h, _⟩ => ⟨h, huf⟩, fun ⟨h, _⟩ => ⟨h, hvf⟩⟩
      · rw [if_pos hud, if_neg hvd, memfilter u v,
            show (v ∈ reduced u) ↔ (u ∈ reduced v) from hsym u v]
        exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, hvf⟩⟩
      · rw [if_neg hud, if_pos hvd, memfilter v u,
            show (v ∈ reduced u) ↔ (u ∈ reduced v) from hsym u v]
        exact ⟨fun h => ⟨h, huf⟩, fun ⟨h, _⟩ => h⟩
      · rw [if_neg hud, if_neg hvd]
        exact hsym u v

omit [Fintype α] in
/-- `reduceStep` preserves list compatibility. At the first choice `f` the list
    is truncated to a prefix (`compat_of_take`); at each dropped entry `f` is
    filtered out (`compat_of_three_cases`'s filter case); elsewhere the list is
    untouched. -/
private lemma reduceStep_preserves_compatible (reduced : α → List α) (a : α)
    (prof : PreferenceProfile α)
    (hcompat : ReducedListCompatible reduced prof) :
    ReducedListCompatible (reduceStep reduced a) prof := by
  intro x
  refine compat_of_reduce_cases (hcompat x) ?_
  by_cases hxf : x = (reduced a).head?.getD a
  · left
    refine ⟨(reduced ((reduced a).head?.getD a)).idxOf a + 1, ?_⟩
    rw [hxf]; exact reduceStep_at_first reduced a
  · by_cases hxd : x ∈ (reduced ((reduced a).head?.getD a)).drop
        ((reduced ((reduced a).head?.getD a)).idxOf a + 1)
    · right; right
      exact ⟨(· ≠ (reduced a).head?.getD a),
        by simp only [reduceStep, if_neg hxf, if_pos hxd]⟩
    · right; left
      simp only [reduceStep, if_neg hxf, if_neg hxd]

/-- `reduceTable` preserves duplicate-freeness: every iteration is a
    `reduceStep`, which preserves `Nodup` (`reduceStep_preserves_nodup`), so the
    fixpoint carries `Nodup` from the starting table to the terminal one. This is
    the prerequisite `reduceTable_preserves_symmetric` consumes at each step. -/
private lemma reduceTable_preserves_nodup :
    ∀ r : α → List α, ReducedTableNodup r → ReducedTableNodup (reduceTable r) := by
  intro r
  induction r using reduceTable.induct with
  | case1 r h ih =>
    intro hnodup
    rw [reduceTable]; simp only [dif_pos h]
    exact ih (reduceStep_preserves_nodup r _ hnodup)
  | case2 r h =>
    intro hnodup
    rw [reduceTable]; simp only [dif_neg h]
    exact hnodup

/-- `reduceTable` preserves table symmetry. Each `reduceStep` preserves `Nodup`
    (`reduceStep_preserves_nodup`) and, given `Nodup`, symmetry
    (`reduceStep_preserves_symmetric`), so the fixpoint threads both invariants
    to termination. Together with `reduceTable_preserves_nodup` this is the
    reduce-pass symmetry preservation,
    and the carrier the `Phase1Duality` establishment proof will read off the
    terminal (`reduceNeededAt`-free) table. -/
private lemma reduceTable_preserves_symmetric :
    ∀ r : α → List α, ReducedTableNodup r → ReducedTableSymmetric r →
      ReducedTableSymmetric (reduceTable r) := by
  intro r
  induction r using reduceTable.induct with
  | case1 r h ih =>
    intro hnodup hsym
    rw [reduceTable]; simp only [dif_pos h]
    exact ih (reduceStep_preserves_nodup r _ hnodup)
             (reduceStep_preserves_symmetric r _ hnodup hsym)
  | case2 r h =>
    intro hnodup hsym
    rw [reduceTable]; simp only [dif_neg h]
    exact hsym

/-- `reduceTable` preserves list compatibility. Each `reduceStep` preserves it
    (`reduceStep_preserves_compatible`), so the fixpoint carries it from the
    starting table to the terminal one — reduce-pass compatibility
    preservation, the last invariant Phase 2 needs. -/
private lemma reduceTable_preserves_compatible (prof : PreferenceProfile α) :
    ∀ r : α → List α, ReducedListCompatible r prof →
      ReducedListCompatible (reduceTable r) prof := by
  intro r
  induction r using reduceTable.induct with
  | case1 r h ih =>
    intro hcompat
    rw [reduceTable]; simp only [dif_pos h]
    exact ih (reduceStep_preserves_compatible r _ prof hcompat)
  | case2 r h =>
    intro hcompat
    rw [reduceTable]; simp only [dif_neg h]
    exact hcompat

omit [Fintype α] in
/-- If `a` sits at the final index of `l` (its `idxOf` is one short of the
    length), then `a` is the list's last element. The `idxOf`-to-`getLast?`
    bridge the forward duality argument reads off `reduceNeededAt`. -/
private lemma getLast?_eq_of_idxOf_last (l : List α) (a : α)
    (hmem : a ∈ l) (hge : l.length ≤ l.idxOf a + 1) :
    l.getLast? = some a := by
  have hlt : l.idxOf a < l.length := List.idxOf_lt_length_of_mem hmem
  have heq : l.length - 1 = l.idxOf a := by omega
  rw [List.getLast?_eq_getElem?, heq, List.getElem?_idxOf hmem]

omit [Fintype α] in
/-- Forward duality on a `reduceNeededAt`-free table: when no agent still needs
    reduction and the table is symmetric, every agent's first choice ranks it
    last (`first(a) = b → last(b) = a`). The forward half of `Phase1Duality` at
    a terminal reduce table — `¬reduceNeededAt a` says `a` is not strictly
    above the end of `first(a)`'s list, and symmetry puts `a` on that list, so
    `a` lands exactly last. -/
lemma reduceNeeded_free_getLast (reduced : α → List α)
    (hterm : ∀ a, ¬ reduceNeededAt reduced a)
    (hsym : ReducedTableSymmetric reduced)
    {a b : α} (hb : (reduced a).head? = some b) :
    (reduced b).getLast? = some a := by
  have hfb : (reduced a).head?.getD a = b := by simp only [hb, Option.getD_some]
  have hmem_ba : b ∈ reduced a := List.mem_of_head? hb
  have hmem_ab : a ∈ reduced b := (hsym a b).mp hmem_ba
  have hterm_a := hterm a
  unfold reduceNeededAt at hterm_a
  rw [hfb] at hterm_a
  have hge : (reduced b).length ≤ (reduced b).idxOf a + 1 := by omega
  exact getLast?_eq_of_idxOf_last (reduced b) a hmem_ab hge

/-- The reduce-pass fixpoint is terminal: no agent still needs reduction, i.e.
    every agent's first choice ranks it last. The `else`-branch postcondition of
    `reduceTable` lifted to the fixpoint output — the precondition the forward
    half of `Phase1Duality` (`reduceNeeded_free_getLast`) consumes. -/
lemma reduceTable_terminal (r : α → List α) :
    ∀ a, ¬ reduceNeededAt (reduceTable r) a := by
  induction r using reduceTable.induct with
  | case1 r h ih =>
    rw [reduceTable]; simp only [dif_pos h]; exact ih
  | case2 r h =>
    rw [reduceTable]; simp only [dif_neg h]
    exact not_exists.mp h

/-- Forward half of `Phase1Duality` at the reduce-pass fixpoint: on the
    `reduceTable` output every agent's first choice ranks it last
    (`first(a) = b → last(b) = a`). Composes the terminal property
    (`reduceTable_terminal`) with symmetry preservation
    (`reduceTable_preserves_symmetric`) through `reduceNeeded_free_getLast`. The
    converse (`last(b) = a → first(a) = b`) is
    `head?_eq_of_getLast?_of_dualForward`; the two assemble the full
    biconditional `phase1Duality_reduceTable`. -/
lemma reduceTable_head_getLast (r : α → List α)
    (hnodup : ReducedTableNodup r) (hsym : ReducedTableSymmetric r)
    {a b : α} (hb : (reduceTable r a).head? = some b) :
    (reduceTable r b).getLast? = some a :=
  reduceNeeded_free_getLast (reduceTable r) (reduceTable_terminal r)
    (reduceTable_preserves_symmetric r hnodup hsym) hb

omit [DecidableEq α] in
/-- Converse half of stable-table duality, recovered from the forward half on a
    finite agent set. Given symmetry and forward duality
    (`first(x) = y → last(y) = x`), the first-choice map `x ↦ first(x)` is a
    self-map of the nonempty-list agents for which `last` is a left inverse
    (forward duality), hence it is injective; a finite injective self-map is
    surjective, and its inverse direction is exactly the converse
    `last(b) = a → first(a) = b`. This is the left-inverse-is-right-inverse
    argument that, with `reduceTable_head_getLast`, completes
    `Phase1Duality (reduceTable r)`. -/
private lemma head?_eq_of_getLast?_of_dualForward (reduced : α → List α)
    (hsym : ReducedTableSymmetric reduced)
    (hfwd : ∀ x y : α, (reduced x).head? = some y → (reduced y).getLast? = some x)
    {a b : α} (hb : (reduced b).getLast? = some a) :
    (reduced a).head? = some b := by
  have head_some : ∀ x : α, reduced x ≠ [] →
      (reduced x).head? = some ((reduced x).head?.getD x) := by
    intro x hx
    cases hl : reduced x with
    | nil => exact absurd hl hx
    | cons c t => simp
  let F : {x : α // reduced x ≠ []} → {x : α // reduced x ≠ []} :=
    fun x => ⟨(reduced x.1).head?.getD x.1, by
      have hgl := hfwd x.1 _ (head_some x.1 x.2)
      intro hempty
      rw [hempty] at hgl
      simp at hgl⟩
  have hF_inj : Function.Injective F := by
    rintro ⟨x, hx⟩ ⟨x', hx'⟩ hgg
    have e : (reduced x).head?.getD x = (reduced x').head?.getD x' :=
      congrArg Subtype.val hgg
    apply Subtype.ext
    show x = x'
    have hxh := head_some x hx
    have hx'h := head_some x' hx'
    rw [e] at hxh
    have h1 := hfwd x _ hxh
    have h2 := hfwd x' _ hx'h
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  have hb_ne : reduced b ≠ [] := by
    intro h; rw [h] at hb; simp at hb
  obtain ⟨⟨a', ha'⟩, hga'⟩ :=
    (Finite.injective_iff_bijective.mp hF_inj).surjective ⟨b, hb_ne⟩
  have e' : (reduced a').head?.getD a' = b := congrArg Subtype.val hga'
  have ha'h := head_some a' ha'
  rw [e'] at ha'h
  have hfin := hfwd a' b ha'h
  rw [hb] at hfin
  rw [Option.some.inj hfin]
  exact ha'h

/-- Full Phase-1 duality at the reduce-pass fixpoint: on `reduceTable r` an
    agent's first choice ranks it last **and** conversely
    (`first(a) = b ⟺ last(b) = a`). The forward half is
    `reduceTable_head_getLast`; the converse is recovered from it by
    `head?_eq_of_getLast?_of_dualForward` (finite
    left-inverse-is-right-inverse). This is the `Phase1Duality` carrier Phase 2
    will thread to revert the `length_pos → length_ge_2` / `p_i ≠ p_next`
    relaxation, once `cascade` is swapped for `reduceTable`. -/
lemma phase1Duality_reduceTable (r : α → List α)
    (hnodup : ReducedTableNodup r) (hsym : ReducedTableSymmetric r) :
    Phase1Duality (reduceTable r) := by
  intro a b
  refine ⟨reduceTable_head_getLast r hnodup hsym, ?_⟩
  intro hb
  exact head?_eq_of_getLast?_of_dualForward (reduceTable r)
    (reduceTable_preserves_symmetric r hnodup hsym)
    (fun x y hxy => reduceTable_head_getLast r hnodup hsym hxy) hb

omit [DecidableEq α] [Fintype α] in
/-- A duplicate-free list whose first and last entries coincide has length 1:
    the shared value sits at the head and at the last position, so `Nodup`
    forbids a second element. -/
lemma len_one_of_nodup_head_getLast {l : List α} (hnd : l.Nodup)
    {a : α} (hh : l.head? = some a) (hl : l.getLast? = some a) :
    l.length = 1 := by
  cases l with
  | nil => simp at hh
  | cons x t =>
    cases t with
    | nil => rfl
    | cons y t' =>
      exfalso
      rw [List.head?_cons, Option.some_inj] at hh
      subst hh
      have hmem : x ∈ y :: t' :=
        List.mem_of_getLast? (by rwa [List.getLast?_cons_cons] at hl)
      rw [List.nodup_cons] at hnd
      exact hnd.1 hmem

omit [DecidableEq α] in
/-- `Phase1Duality` (the full biconditional) + symmetry + duplicate-freeness
    imply `CascadeInvariant`. If `b ∈ reduced a` and `reduced a = [b]`, then
    `first(a) = b` and `last(a) = b`; converse duality
    (`head?_eq_of_getLast?_of_dualForward`) turns `last(a) = b` into
    `first(b) = a`, while forward duality turns `first(a) = b` into
    `last(b) = a`. So `b`'s list has the same head and last entry `a`, and
    `Nodup` collapses it to length 1.

    This corrects the earlier reading that duality could not yield
    `CascadeInvariant`: that argument used only forward duality, which indeed
    forces just `a` last in `reduced b`. The converse half — supplied by the
    finite first-choice bijection — additionally forces `a` *first* in
    `reduced b`, and the two together pin the length. -/
lemma cascadeInvariant_of_phase1Duality (reduced : α → List α)
    (hdual : Phase1Duality reduced) (hsym : ReducedTableSymmetric reduced)
    (hnodup : ReducedTableNodup reduced) :
    CascadeInvariant reduced := by
  intro a b hmem hlen
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hlen
  rw [hc, List.mem_singleton] at hmem
  rw [← hmem] at hc
  have hhead_a : (reduced a).head? = some b := by simp [hc]
  have hlast_a : (reduced a).getLast? = some b := by simp [hc]
  have hhead_b : (reduced b).head? = some a :=
    head?_eq_of_getLast?_of_dualForward reduced hsym
      (fun x y h => (hdual x y).mp h) hlast_a
  have hlast_b : (reduced b).getLast? = some a := (hdual a b).mp hhead_a
  exact len_one_of_nodup_head_getLast (hnodup b) hhead_b hlast_b

/-- The reduce-pass fixpoint establishes `CascadeInvariant`. Composes
    `phase1Duality_reduceTable` with `cascadeInvariant_of_phase1Duality`,
    using the symmetry/nodup carriers `reduceTable` already threads. It
    establishes `CascadeInvariant` at the fixpoint; it lets
    Phase 2 obtain its length-≥-2 rotation guarantee after the
    `cascade → reduceTable` swap without a separate `CascadeInvariant`
    carrier. -/
theorem cascadeInvariant_reduceTable (r : α → List α)
    (hnodup : ReducedTableNodup r) (hsym : ReducedTableSymmetric r) :
    CascadeInvariant (reduceTable r) :=
  cascadeInvariant_of_phase1Duality (reduceTable r)
    (phase1Duality_reduceTable r hnodup hsym)
    (reduceTable_preserves_symmetric r hnodup hsym)
    (reduceTable_preserves_nodup r hnodup)

omit [Fintype α] in
/-- A two-element coalition is exactly the agent paired with its partner. -/
private lemma coalition_eq_pairPartner {G : Finset α} {x : α}
    (hx : x ∈ G) (hcard : G.card = 2) : G = {x, pairPartner x G} := by
  have hp_mem : pairPartner x G ∈ G := pairPartner_mem hx hcard
  have hp_ne : pairPartner x G ≠ x := pairPartner_ne hx hcard
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    by_cases hyx : y = x
    · subst hyx; exact Finset.mem_insert_self _ _
    · have heq : pairPartner x G = y := pairPartner_eq_of_card_two hcard hx hy hyx
      rw [← heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · rw [hcard]; exact le_of_eq (Finset.card_pair (Ne.symm hp_ne))

/-- **Phase-1 initial table.** Each agent's ranked partner list, restricted to
    *mutual* pairs: `b ∈ initialTable prof a ↔ {a,b} ∈ prof a ∧ {a,b} ∈ prof b`.
    The mutual-pair filter makes the table symmetric **by construction** — the
    RMP model (`IsRMP = IsValidProfile ∧ SizeTwo`) does not assume profile
    cross-symmetry, so an unfiltered `prof a`-partner list need not be symmetric.
    This is the witness `phase1_produces_reduced_table` runs the reduce pass on:
    `reduceTable_establishes_invariants` discharges five of its seven output
    conjuncts from the three structural invariants proved here
    (`initialTable_symmetric`, `initialTable_nodup`, `initialTable_compatible`). -/
noncomputable def initialTable (prof : PreferenceProfile α) : α → List α :=
  fun a => ((prof a).filter (fun G => decide (G ∈ prof (pairPartner a G)))).map
    (fun G => pairPartner a G)

omit [Fintype α] in
/-- Membership in the initial table is exactly mutual rankability of the pair. -/
lemma mem_initialTable {prof : PreferenceProfile α} (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof) (a b : α) :
    b ∈ initialTable prof a ↔ {a, b} ∈ prof a ∧ {a, b} ∈ prof b := by
  simp only [initialTable, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨G, ⟨hGa, hGmut⟩, hpp⟩
    have ha_in : a ∈ G := (hvalid a).2 G hGa
    have hcard : G.card = 2 := hsize a G hGa
    have hG : G = {a, b} := by rw [coalition_eq_pairPartner ha_in hcard, hpp]
    subst hG
    exact ⟨hGa, by rwa [hpp] at hGmut⟩
  · rintro ⟨hab_a, hab_b⟩
    have hcard : ({a, b} : Finset α).card = 2 := hsize a _ hab_a
    have hne : a ≠ b := by
      intro h; subst h
      have : ({a, a} : Finset α) = {a} := by ext x; simp
      rw [this] at hcard; simp at hcard
    have ha_in : a ∈ ({a, b} : Finset α) := Finset.mem_insert_self _ _
    have hb_in : b ∈ ({a, b} : Finset α) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hpp : pairPartner a {a, b} = b :=
      pairPartner_eq_of_card_two hcard ha_in hb_in (Ne.symm hne)
    exact ⟨{a, b}, ⟨hab_a, by rw [hpp]; exact hab_b⟩, hpp⟩

omit [Fintype α] in
/-- The initial table is symmetric: mutual rankability is symmetric in the pair. -/
lemma initialTable_symmetric {prof : PreferenceProfile α} (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof) : ReducedTableSymmetric (initialTable prof) := by
  intro a b
  simp only [mem_initialTable hsize hvalid]
  rw [Finset.pair_comm a b]
  exact and_comm

omit [Fintype α] in
/-- The initial table is duplicate-free: distinct ranked coalitions of `a` yield
    distinct partners (`coalition_eq_pairPartner` makes the partner determine the
    coalition), so the partner map is injective on `prof a`. -/
lemma initialTable_nodup {prof : PreferenceProfile α} (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof) : ReducedTableNodup (initialTable prof) := by
  intro a
  simp only [initialTable]
  refine List.Nodup.map_on ?_ (List.Nodup.filter _ (hvalid a).1)
  intro G hG G' hG' heq
  have hGa : G ∈ prof a := List.mem_of_mem_filter hG
  have hG'a : G' ∈ prof a := List.mem_of_mem_filter hG'
  have hGeq : G = {a, pairPartner a G} :=
    coalition_eq_pairPartner ((hvalid a).2 G hGa) (hsize a G hGa)
  have hG'eq : G' = {a, pairPartner a G'} :=
    coalition_eq_pairPartner ((hvalid a).2 G' hG'a) (hsize a G' hG'a)
  rw [hGeq, hG'eq]
  exact congrArg (fun t => ({a, t} : Finset α)) heq

omit [Fintype α] in
/-- The initial table preserves the profile's ranked order: each list entry is a
    partner whose coalition `{a, ·}` sits at the corresponding position of
    `prof a`, and filtering/mapping keeps relative order (`filter_indices_ordered`). -/
lemma initialTable_compatible {prof : PreferenceProfile α} (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof) : ReducedListCompatible (initialTable prof) prof := by
  intro a j k hjk
  have hlen : (initialTable prof a).length
      = ((prof a).filter (fun G => decide (G ∈ prof (pairPartner a G)))).length := by
    simp only [initialTable, List.length_map]
  have key : ∀ (m : ℕ) (hm : m < (initialTable prof a).length),
      ({a, (initialTable prof a)[m]} : Finset α)
        = ((prof a).filter (fun G => decide (G ∈ prof (pairPartner a G))))[m]'(hlen ▸ hm) := by
    intro m hm
    have hmap : (initialTable prof a)[m]
        = pairPartner a (((prof a).filter
            (fun G => decide (G ∈ prof (pairPartner a G))))[m]'(hlen ▸ hm)) := by
      simp only [initialTable, List.getElem_map]
    rw [hmap]
    have hmemF : ((prof a).filter (fun G => decide (G ∈ prof (pairPartner a G))))[m]'(hlen ▸ hm)
        ∈ prof a := List.mem_of_mem_filter (List.getElem_mem _)
    exact (coalition_eq_pairPartner ((hvalid a).2 _ hmemF) (hsize a _ hmemF)).symm
  obtain ⟨jo, hjo, ko, hko, hjko, hjeq, hkeq⟩ :=
    filter_indices_ordered (prof a) (fun G => decide (G ∈ prof (pairPartner a G)))
      (hlen ▸ j.isLt) (hlen ▸ k.isLt) hjk
  have ej : ({a, (initialTable prof a)[j]} : Finset α) = (prof a)[jo] :=
    (key j.val j.isLt).trans hjeq.symm
  have ek : ({a, (initialTable prof a)[k]} : Finset α) = (prof a)[ko] :=
    (key k.val k.isLt).trans hkeq.symm
  rw [ej, ek]
  exact ⟨⟨jo, hjo⟩, ⟨ko, hko⟩, hjko, rfl, rfl⟩

omit [DecidableEq α] [Fintype α] in
/-- Under `Phase1Duality`, the successor proposer `p_{i+1}` holds `q_i` as its
    *first* choice: the rotation law `last(q_i) = p_{i+1}` reads, through duality's
    converse (`phase1Duality_head`), as `first(p_{i+1}) = q_i`. This is the
    structural engine of the rotation cycle — `q_i` is `p_{i+1}`'s top-ranked
    partner. Retained as a sound duality fact: its original consumer (the
    universal-survival trace for the removed `eliminateRotation_preserves_stablePair`)
    is abandoned, but the same first-choice structure feeds the rotation-shift
    witness of `solvableInTable_step`. -/
theorem isRotation_succ_head
    (c : RotationCycle α) (reduced : α → List α)
    (hdual : Phase1Duality reduced) (hrot : IsRotation c reduced)
    (i : Fin c.pairs.length) :
    (reduced (c.pairs.get (nextFin i c.length_pos)).1).head? = some (c.pairs.get i).2 := by
  obtain ⟨hsec, hlast, hne⟩ := hrot i
  have hglq : (reduced (c.pairs.get i).2).getLast? =
      some (c.pairs.get (nextFin i c.length_pos)).1 := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
      Option.getD_some] at hlast
    rw [List.getLast?_eq_some_getLast hne, hlast]
  exact phase1Duality_head reduced hdual hglq

omit [DecidableEq α] [Fintype α] in
/-- Predecessor companion to `isRotation_succ_head`: under `Phase1Duality`,
    the proposer `p_i` holds `q_{i-1}` (the partner at its cyclic predecessor
    `j`, `nextFin j = i`) as its *first* choice. The rotation law at `j`
    reads `last(q_j) = p_{nextFin j} = p_i`, so duality's converse gives
    `first(p_i) = q_j`. With `isRotation_succ_head` (`first(p_{i+1}) = q_i`)
    these are the two duality facts describing first choices along the rotation
    cycle. Retained sound — their original consumer (the abandoned
    universal-survival trace for the removed `eliminateRotation_preserves_stablePair`)
    is gone; the rotation-shift witness of `solvableInTable_step` reasons about the
    same structure. -/
theorem isRotation_pred_head
    (c : RotationCycle α) (reduced : α → List α)
    (hdual : Phase1Duality reduced) (hrot : IsRotation c reduced)
    (i : Fin c.pairs.length) :
    ∃ j : Fin c.pairs.length, nextFin j c.length_pos = i ∧
      (reduced (c.pairs.get i).1).head? = some (c.pairs.get j).2 := by
  obtain ⟨j, hj⟩ := nextFin_surjective c.length_pos i
  refine ⟨j, hj, ?_⟩
  have h := isRotation_succ_head c reduced hdual hrot j
  rw [hj] at h
  exact h

omit [DecidableEq α] [Fintype α] in
/-- Partner index-uniqueness, the duality-derived companion of `ProposersDistinct`:
    under `Phase1Duality` and proposer index-uniqueness, each agent occurs as a
    partner `q_i` at a *unique* index. If `q_i = q_j`, then `isRotation_succ_head`
    gives both successors `p_{i+1}`, `p_{j+1}` the same first choice `q_i`; forward
    duality (`phase1Duality_getLast`, applied to each) forces
    `last(q_i) = p_{i+1}` and `= p_{j+1}`, so `p_{i+1} = p_{j+1}`, whence
    `ProposersDistinct` gives `nextFin i = nextFin j` and `nextFin_injective`
    gives `i = j`. With `ProposersDistinct` this pins each cycle agent to a single
    index — the singleton list-pinning the rotation-shift witness of
    `solvableInTable_step` consumes (`hpin`). -/
theorem isRotation_partners_distinct
    (c : RotationCycle α) (reduced : α → List α)
    (hdual : Phase1Duality reduced) (hrot : IsRotation c reduced)
    (hprop : ProposersDistinct c)
    {i j : Fin c.pairs.length}
    (h : (c.pairs.get i).2 = (c.pairs.get j).2) : i = j := by
  have hi := isRotation_succ_head c reduced hdual hrot i
  have hj := isRotation_succ_head c reduced hdual hrot j
  rw [h] at hi
  have hli := phase1Duality_getLast reduced hdual hi
  have hlj := phase1Duality_getLast reduced hdual hj
  have hp : (c.pairs.get (nextFin i c.length_pos)).1
      = (c.pairs.get (nextFin j c.length_pos)).1 :=
    Option.some.inj (hli.symm.trans hlj)
  exact nextFin_injective c.length_pos (hprop _ _ hp)

omit [Fintype α] in
/-- **`rotationShiftPartner` is a subsingleton under index-uniqueness +
    disjointness** — every shift partner of a single agent `a` coincides. A member
    is a rotation edge from a unique role/index (`mem_rotationShiftPartner`): two
    partner-role members share `a = q_i = q_{i'}`, pinned to one index by
    `isRotation_partners_distinct`; two proposer-role members share `a = p_i = p_{i'}`,
    pinned by `ProposersDistinct`; a partner-role and a proposer-role member would
    force `q_i = a = p_{i'}`, refuted by the disjointness hypothesis `hdisj`
    (`p_i ≠ q_j`). The disjointness is taken as a hypothesis — it is FALSE as a
    standalone rotation fact (2026-06-24 probe) and holds only under the
    upper-matching all-or-nothing — so the lemma stays list-pinning-independent. The
    structural kernel of the head-pinning `rotationShift_hpin` below. -/
theorem rotationShiftPartner_subsingleton
    (c : RotationCycle α) (reduced : α → List α)
    (hdual : Phase1Duality reduced) (hrot : IsRotation c reduced)
    (hprop : ProposersDistinct c)
    (hdisj : ∀ i j : Fin c.pairs.length, (c.pairs.get i).1 ≠ (c.pairs.get j).2)
    {a b b' : α} (hb : b ∈ rotationShiftPartner c a)
    (hb' : b' ∈ rotationShiftPartner c a) :
    b = b' := by
  obtain ⟨i, hci⟩ := mem_rotationShiftPartner hb
  obtain ⟨i', hci'⟩ := mem_rotationShiftPartner hb'
  rcases hci with ⟨ha, hbeq⟩ | ⟨ha, hbeq⟩ <;>
    rcases hci' with ⟨ha', hb'eq⟩ | ⟨ha', hb'eq⟩
  · have hii : i = i' :=
      isRotation_partners_distinct c reduced hdual hrot hprop (ha.symm.trans ha')
    rw [hbeq, hb'eq, hii]
  · exact absurd (ha'.symm.trans ha) (hdisj i' i)
  · exact absurd (ha.symm.trans ha') (hdisj i i')
  · have hii : i = i' := hprop i i' (ha.symm.trans ha')
    rw [hbeq, hb'eq, hii]

omit [Fintype α] in
/-- **Head-symmetry (`hpin`) discharged modulo proposer/partner disjointness** — if
    `a`'s head shift partner is `b`, then `b`'s head shift partner is `a`. By
    `rotationShiftPartner_symm`, `a ∈ rotationShiftPartner c b`, so that list is
    nonempty; its head is some member, which `rotationShiftPartner_subsingleton`
    forces to be `a`. This is the exact `hpin` hypothesis of
    `rotationShift_consistency` / `rotationShift_isPairMatching`, assembled modulo
    the conditional disjointness `hdisj` — now the only remaining all-or-nothing
    content of the upper-matching branch of `solvableInTable_step`. -/
theorem rotationShift_hpin
    (c : RotationCycle α) (reduced : α → List α)
    (hdual : Phase1Duality reduced) (hrot : IsRotation c reduced)
    (hprop : ProposersDistinct c)
    (hdisj : ∀ i j : Fin c.pairs.length, (c.pairs.get i).1 ≠ (c.pairs.get j).2)
    {a b : α} (hhead : (rotationShiftPartner c a).head? = some b) :
    (rotationShiftPartner c b).head? = some a := by
  have hb_mem : b ∈ rotationShiftPartner c a :=
    List.mem_of_mem_head? (Option.mem_def.mpr hhead)
  have ha_mem : a ∈ rotationShiftPartner c b := rotationShiftPartner_symm hb_mem
  cases hl : rotationShiftPartner c b with
  | nil => rw [hl] at ha_mem; simp at ha_mem
  | cons hd tl =>
    have hhd_mem : hd ∈ rotationShiftPartner c b := by rw [hl]; simp
    have hx : hd = a :=
      rotationShiftPartner_subsingleton c reduced hdual hrot hprop hdisj hhd_mem ha_mem
    rw [List.head?_cons, hx]

omit [Fintype α] in
/-- **Cycle-avoid (`hcycle_avoid`) discharged modulo proposer/partner
    disjointness** — a shift-edge partner of `a` is never one of `a`'s removed
    partners. The shift re-pairs along edges `{q_i, p_i}` while elimination
    deletes edges `{q_j, p_{j+1}}`, and the two supports are disjoint: matching a
    shift role against a removal role, like-roles (`a = q_i = q_j` /
    `b = q_i = q_j`) collapse the index (`isRotation_partners_distinct`) and then
    collide a proposer with its own cyclic successor `p_i = p_{i+1}`, refuted by
    `isRotation_no_selfLoop`; cross-roles force a proposer to equal a partner
    (`p_i = q_j`), refuted by the disjointness hypothesis `hdisj`. The
    `hcycle_avoid` companion of `rotationShift_hpin`: both discharge a structural
    hypothesis of the upper-matching witness modulo the same conditional
    disjointness (FALSE standalone — 2026-06-24 probe — true only under the
    upper-matching all-or-nothing). Feeds `rotationShift_avoids_removed`'s
    `hcycle_avoid` argument (its `head? = some b` gives `b ∈ rotationShiftPartner`
    via `List.mem_of_mem_head?`). -/
theorem rotationShift_cycle_avoid
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hdual : Phase1Duality reduced) (hrot : IsRotation c reduced)
    (hprop : ProposersDistinct c)
    (hdisj : ∀ i j : Fin c.pairs.length, (c.pairs.get i).1 ≠ (c.pairs.get j).2)
    {a b : α} (hb : b ∈ rotationShiftPartner c a) :
    b ∉ rotationRemovals c a := by
  intro hrem
  obtain ⟨i, hshift⟩ := mem_rotationShiftPartner hb
  obtain ⟨j, hrm⟩ := mem_rotationRemovals hrem
  rcases hshift with ⟨ha_s, hb_s⟩ | ⟨ha_s, hb_s⟩ <;>
    rcases hrm with ⟨ha_r, hb_r⟩ | ⟨ha_r, hb_r⟩
  · have hij : i = j :=
      isRotation_partners_distinct c reduced hdual hrot hprop (ha_s.symm.trans ha_r)
    exact isRotation_no_selfLoop c reduced prof hvalid hcompat hdual hrot i
      (by rw [← hb_s, hb_r, hij])
  · exact hdisj i j (hb_s.symm.trans hb_r)
  · exact hdisj i j (ha_s.symm.trans ha_r)
  · have hij : i = j :=
      isRotation_partners_distinct c reduced hdual hrot hprop (hb_s.symm.trans hb_r)
    exact isRotation_no_selfLoop c reduced prof hvalid hcompat hdual hrot i
      (by rw [← ha_s, ha_r, hij])

omit [Fintype α] in
/-- **Avoid branch of the Phase-2 crux.** A stable pair-matching that already
    survives in `reduced` (`StablePairInvariant`) and uses *no* removed pair
    survives the rotation elimination unchanged: each partner stays on the list
    (`hinv`) and is not removed (`havoid`), so it remains in the filtered list
    `eliminateRotation reduced c = fun a => (reduced a).filter (· ∉ rotationRemovals c a)`.
    This is the easy disjunct of `solvableInTable_step` — when the surviving
    matching `μ` is *not* the eliminated ("upper") matching it avoids every
    removed pair and is its own post-elimination witness; composing with
    `solvableInTable_of_eliminate_survivor` then discharges that branch. -/
theorem stablePair_eliminate_of_avoids
    (reduced : α → List α) (prof : PreferenceProfile α) (c : RotationCycle α)
    (μ : Grouping α)
    (hinv : StablePairInvariant reduced prof μ)
    (havoid : ∀ a : α, pairPartner a (μ a) ∉ rotationRemovals c a) :
    StablePairInvariant (eliminateRotation reduced c) prof μ := by
  intro a
  simp only [eliminateRotation, List.mem_filter, decide_eq_true_eq]
  exact ⟨hinv a, havoid a⟩

omit [Fintype α] in
/-- The stability heart of the reduce pass: keyed on `a`, a `reduceStep` never
    deletes a stable pair. Writing `f = first(a)`, no stable matching `μ` pairs
    `f` with anyone `f` ranks strictly below `a` — such a partner `c` would make
    `{a, f}` a blocking pair (`a` prefers its first choice `f` to `μ a`, and `f`
    prefers `a` to `c = μ f`). So `f`'s μ-partner stays in the kept prefix
    `take (idxOf a + 1)`, i.e. outside the dropped tail. The single fact both
    `reduceStep` cases consume to preserve `StablePairInvariant`. -/
private lemma reduceStep_mu_partner_not_dropped
    (reduced : α → List α) (prof : PreferenceProfile α) (μ : Grouping α) (a : α)
    (hsize : SizeTwo prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hnodup : ReducedTableNodup reduced)
    (hsym : ReducedTableSymmetric reduced)
    (hstable : PairwiseStable prof μ)
    (hvalidμ : IsValidGrouping μ)
    (hsizeμ : ∀ a : α, (μ a).card = 2)
    (hconsistent : ∀ a : α, μ (pairPartner a (μ a)) = μ a)
    (hinv : StablePairInvariant reduced prof μ) :
    pairPartner ((reduced a).head?.getD a) (μ ((reduced a).head?.getD a)) ∉
      (reduced ((reduced a).head?.getD a)).drop
        ((reduced ((reduced a).head?.getD a)).idxOf a + 1) := by
  by_cases hane : reduced a = []
  · simp [hane]
  · have hhead : (reduced a).head? = some ((reduced a).head?.getD a) := by
      cases hl : reduced a with
      | nil => exact absurd hl hane
      | cons hd tl => simp
    set f := (reduced a).head?.getD a with hf
    set c := pairPartner f (μ f) with hc
    intro hcontra
    have hf_mem_a : f ∈ reduced a := List.mem_of_head? hhead
    have ha_in_f : a ∈ reduced f := (hsym a f).mp hf_mem_a
    have hia_lt : (reduced f).idxOf a < (reduced f).length :=
      List.idxOf_lt_length_of_mem ha_in_f
    have ha_at : (reduced f)[(reduced f).idxOf a]'hia_lt = a := List.getElem_idxOf hia_lt
    obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hcontra
    rw [List.length_drop] at hi
    have hicb : (reduced f).idxOf a + 1 + i < (reduced f).length := by omega
    have hc_at : (reduced f)[(reduced f).idxOf a + 1 + i]'hicb = c := by
      rw [← hci, List.getElem_drop]
    have hac_ne : a ≠ c := by
      intro h
      have heq : (reduced f)[(reduced f).idxOf a]'hia_lt
               = (reduced f)[(reduced f).idxOf a + 1 + i]'hicb := by rw [ha_at, hc_at, h]
      have hii := (List.Nodup.getElem_inj_iff (hnodup f)).mp heq
      omega
    have hfac : Ranks prof f {f, a} {f, c} := by
      have hlt : (⟨(reduced f).idxOf a, hia_lt⟩ : Fin (reduced f).length)
               < ⟨(reduced f).idxOf a + 1 + i, hicb⟩ := Fin.mk_lt_mk.mpr (by omega)
      have hr := hcompat f ⟨(reduced f).idxOf a, hia_lt⟩
        ⟨(reduced f).idxOf a + 1 + i, hicb⟩ hlt
      rwa [show (reduced f)[(⟨(reduced f).idxOf a, hia_lt⟩ : Fin (reduced f).length)] = a
             from ha_at,
           show (reduced f)[(⟨(reduced f).idxOf a + 1 + i, hicb⟩ : Fin (reduced f).length)] = c
             from hc_at] at hr
    have hfa_ne : f ≠ a := by
      intro hfa
      have hmem : ({f, a} : Finset α) ∈ prof f := Ranks.fst_mem hfac
      have hc2 : ({f, a} : Finset α).card = 2 := hsize f _ hmem
      rw [hfa] at hc2; simp at hc2
    have hμf_eq : μ f = {f, c} := by
      have h := coalition_eq_pairPartner (hvalidμ f) (hsizeμ f)
      rw [← hc] at h; exact h
    set pa := pairPartner a (μ a) with hpa
    have hpa_mem : pa ∈ reduced a := by rw [hpa]; exact hinv a
    have hμa_eq : μ a = {a, pa} := by
      have h := coalition_eq_pairPartner (hvalidμ a) (hsizeμ a)
      rw [← hpa] at h; exact h
    have hpa_ne_f : pa ≠ f := by
      intro hpaf
      have hμfa : μ f = μ a := by
        have hco := hconsistent a; rw [← hpa] at hco; rw [hpaf] at hco; exact hco
      have hca : c = a := by
        rw [hc, hμfa]
        apply pairPartner_eq_of_card_two (hsizeμ a)
        · rw [hμa_eq, hpaf]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f)
        · exact hvalidμ a
        · exact hfa_ne.symm
      exact hac_ne hca.symm
    rw [List.head?_eq_getElem?] at hhead
    obtain ⟨h0, hf0⟩ := List.getElem?_eq_some_iff.mp hhead
    obtain ⟨ipa, hipa_lt, hpa_at⟩ := List.mem_iff_getElem.mp hpa_mem
    have hipa_pos : 0 < ipa := by
      rcases Nat.eq_zero_or_pos ipa with h0' | h0'
      · subst h0'; exact absurd (hpa_at.symm.trans hf0) hpa_ne_f
      · exact h0'
    have hra : Ranks prof a {a, f} (μ a) := by
      rw [hμa_eq]
      have hlt : (⟨0, h0⟩ : Fin (reduced a).length) < ⟨ipa, hipa_lt⟩ :=
        Fin.mk_lt_mk.mpr hipa_pos
      have hr := hcompat a ⟨0, h0⟩ ⟨ipa, hipa_lt⟩ hlt
      rwa [show (reduced a)[(⟨0, h0⟩ : Fin (reduced a).length)] = f from hf0,
           show (reduced a)[(⟨ipa, hipa_lt⟩ : Fin (reduced a).length)] = pa from hpa_at] at hr
    have hrf : Ranks prof f {a, f} (μ f) := by
      rw [hμf_eq, Finset.pair_comm a f]; exact hfac
    exact hstable a f ⟨hfa_ne.symm, hra, hrf⟩

omit [Fintype α] in
/-- One reduce step preserves the stable-pair invariant: the only pairs it
    deletes are stable-pair-free (`reduceStep_mu_partner_not_dropped`). At the
    first choice `f` the μ-partner stays in the kept prefix; at a dropped entry
    `x` the deleted partner `f` is not `x`'s μ-partner; elsewhere the list is
    untouched. -/
private lemma reduceStep_preserves_stablePair
    (reduced : α → List α) (prof : PreferenceProfile α) (μ : Grouping α) (a : α)
    (hsize : SizeTwo prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hnodup : ReducedTableNodup reduced)
    (hsym : ReducedTableSymmetric reduced)
    (hstable : PairwiseStable prof μ)
    (hvalidμ : IsValidGrouping μ)
    (hsizeμ : ∀ a : α, (μ a).card = 2)
    (hconsistent : ∀ a : α, μ (pairPartner a (μ a)) = μ a)
    (hinv : StablePairInvariant reduced prof μ) :
    StablePairInvariant (reduceStep reduced a) prof μ := by
  have hkey := reduceStep_mu_partner_not_dropped reduced prof μ a hsize hcompat hnodup hsym
    hstable hvalidμ hsizeμ hconsistent hinv
  intro x
  simp only [reduceStep]
  set f := (reduced a).head?.getD a with hf
  set keep := (reduced f).idxOf a + 1 with hkeep
  split_ifs with hxf hxd
  · rw [hxf]
    have hsplit : pairPartner f (μ f) ∈ (reduced f).take keep ++ (reduced f).drop keep := by
      rw [List.take_append_drop]; exact hinv f
    rcases List.mem_append.mp hsplit with h | h
    · exact h
    · exact absurd h hkey
  · simp only [List.mem_filter, decide_eq_true_eq]
    refine ⟨hinv x, ?_⟩
    intro hpf
    apply hkey
    have hpartner : pairPartner f (μ f) = x := by
      have hμ : μ f = μ x := by
        have hco := hconsistent x; rw [hpf] at hco; exact hco
      rw [hμ]
      apply pairPartner_eq_of_card_two (hsizeμ x)
      · rw [← hpf]; exact pairPartner_mem (hvalidμ x) (hsizeμ x)
      · exact hvalidμ x
      · exact hxf
    rw [hpartner]; exact hxd
  · exact hinv x

/-- A reduce pass preserves the stable-pair invariant: each `reduceStep` deletes
    only stable-pair-free pairs (`reduceStep_preserves_stablePair`), and the
    fixpoint threads symmetry, compatibility and nodup forward so the hypothesis
    bundle is re-established at every step. The reduce-pass stable-pair carrier:
    it feeds the rotation-shift witness of the Phase-2 crux `solvableInTable_step`. -/
theorem reduceTable_preserves_stablePair
    (reduced : α → List α) (prof : PreferenceProfile α) (μ : Grouping α)
    (hsize : SizeTwo prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hnodup : ReducedTableNodup reduced)
    (hsym : ReducedTableSymmetric reduced)
    (hstable : PairwiseStable prof μ)
    (hvalidμ : IsValidGrouping μ)
    (hsizeμ : ∀ a : α, (μ a).card = 2)
    (hconsistent : ∀ a : α, μ (pairPartner a (μ a)) = μ a)
    (hinv : StablePairInvariant reduced prof μ) :
    StablePairInvariant (reduceTable reduced) prof μ := by
  suffices hmain : ∀ r, ReducedTableSymmetric r → ReducedListCompatible r prof →
      ReducedTableNodup r → StablePairInvariant r prof μ →
      StablePairInvariant (reduceTable r) prof μ by
    exact hmain reduced hsym hcompat hnodup hinv
  intro r
  induction r using reduceTable.induct with
  | case1 r h ih =>
    intro hsymr hcompatr hnodupr hinvr
    rw [reduceTable]
    simp only [dif_pos h]
    exact ih (reduceStep_preserves_symmetric r _ hnodupr hsymr)
             (reduceStep_preserves_compatible r _ prof hcompatr)
             (reduceStep_preserves_nodup r _ hnodupr)
             (reduceStep_preserves_stablePair r prof μ _ hsize hcompatr hnodupr hsymr
               hstable hvalidμ hsizeμ hconsistent hinvr)
  | case2 r h =>
    intro hsymr hcompatr hnodupr hinvr
    rw [reduceTable]
    simp only [dif_neg h]
    exact hinvr

/-- **Reduce-pass + packaging half of the Phase-2 crux.** A stable pair-matching
    that survives the rotation elimination alone (`StablePairInvariant
    (eliminateRotation reduced c)`) already witnesses `SolvableInTable` of the full
    Phase-2 successor `reduceTable (eliminateRotation reduced c)`: rotation
    elimination preserves symmetry / compatibility / nodup
    (`rotation_elimination_preserves_invariants`, `eliminateRotation_preserves_nodup`),
    so `reduceTable_preserves_stablePair` carries the survivor across the reduce pass,
    and the `IsPairMatching` hypotheses (validity, size-2, consistency) are read off
    `hmatch`/`hvalid`/`hsize`. This factors all the reduce-pass plumbing out of
    `solvableInTable_step`, shrinking its open obligation to constructing the
    rotation-shifted matching and showing it is pairwise stable and survives the
    *rotation elimination* — the reduce pass and `SolvableInTable` packaging are
    discharged here. -/
theorem solvableInTable_of_eliminate_survivor
    (reduced : α → List α) (prof : PreferenceProfile α) (c : RotationCycle α)
    (hsize : SizeTwo prof)
    (hrot : IsRotation c reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hnodup : ReducedTableNodup reduced)
    (hvalid : IsValidProfile prof)
    (μ : Grouping α)
    (hmatch : IsPairMatching prof μ)
    (hstable : PairwiseStable prof μ)
    (hinv : StablePairInvariant (eliminateRotation reduced c) prof μ) :
    SolvableInTable (reduceTable (eliminateRotation reduced c)) prof := by
  obtain ⟨hsym', hcompat'⟩ :=
    rotation_elimination_preserves_invariants c reduced prof hsize hrot hcompat hsym
  have hnodup' : ReducedTableNodup (eliminateRotation reduced c) :=
    eliminateRotation_preserves_nodup reduced c hnodup
  exact ⟨μ, hmatch, hstable,
    reduceTable_preserves_stablePair (eliminateRotation reduced c) prof μ hsize
      hcompat' hnodup' hsym' hstable
      (fun a => (hvalid a).2 (μ a) (hmatch a).1)
      (fun a => hsize a (μ a) (hmatch a).1)
      (fun a => (hmatch a).2)
      hinv⟩

omit [Fintype α] in
/-- **Upper-matching index extraction.** When agent `a`'s μ-partner is one it
    must give up under rotation elimination (`pairPartner a (μ a) ∈
    rotationRemovals c a`), `a` is matched in `μ` to one of the rotation's
    removal pairs `{q_i, p_{i+1}}`, and the disjunct records whether `a` is the
    `q_i` (proposer-partner) or `p_{i+1}` (successor proposer) endpoint — which
    determines which side the `q_i ↦ p_i` shift re-pairs it to. The entry point
    of the upper-matching branch of `solvableInTable_step`: from one agent using a
    removed pair it produces the cycle index and pins `μ a` to the unordered
    removal pair via `mem_rotationRemovals` + `coalition_eq_pairPartner`. -/
theorem musesRemovedPair_index
    (prof : PreferenceProfile α) (c : RotationCycle α)
    (hsize : SizeTwo prof) (hvalid : IsValidProfile prof)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ)
    (a : α) (ha : pairPartner a (μ a) ∈ rotationRemovals c a) :
    ∃ i : Fin c.pairs.length,
      (a = (c.pairs.get i).2 ∨ a = (c.pairs.get (nextFin i c.length_pos)).1) ∧
      μ a = {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} := by
  have ha_in : a ∈ μ a := (hvalid a).2 (μ a) (hmatch a).1
  have hcard : (μ a).card = 2 := hsize a (μ a) (hmatch a).1
  have hμa : μ a = {a, pairPartner a (μ a)} := coalition_eq_pairPartner ha_in hcard
  obtain ⟨i, hcase⟩ := mem_rotationRemovals ha
  refine ⟨i, ?_⟩
  rcases hcase with ⟨ha_eq, hb_eq⟩ | ⟨ha_eq, hb_eq⟩
  · exact ⟨Or.inl ha_eq, by rw [hμa, hb_eq, ha_eq]⟩
  · refine ⟨Or.inr ha_eq, ?_⟩
    rw [hμa, hb_eq, ha_eq]
    exact Finset.pair_comm _ _

omit [Fintype α] in
/-- **All-or-nothing, backward step.** In a stable pair-matching `μ`, if `q_i` is
    matched to its removed-pair partner `p_{i+1}` (`μ q_i = {q_i, p_{i+1}}`), then
    so is the cyclic predecessor: `μ q_{i-1} = {q_{i-1}, p_i}`, where `i-1 = j` is
    the index with `nextFin j = i`. The combinatorial heart of the upper-matching
    all-or-nothing fact (a stable matching using one removed pair uses *every*
    removed pair). Stability of `{q_i, p_i}` forces `p_i`'s μ-partner to rank
    at-or-above `q_i = second(p_i)` on `p_i`'s reduced list — so it is
    `first(p_i) = q_{i-1}` or `q_i`; the `q_i` case collides with
    `μ q_i = {q_i, p_{i+1}}` (`p_i ≠ p_{i+1}` by `isRotation_no_selfLoop`),
    leaving `μ p_i = {p_i, q_{i-1}}`, whence consistency gives the claim. Note it
    avoids the standalone proposer/partner disjointness `p_i ≠ q_j` (probe-refuted
    unconditionally): `p_i ≠ q_{i-1}` is read off `(μ p_i).card = 2`, not asserted.
    Iterated around the finite cycle this yields the all-or-nothing fact the upper
    branch of `solvableInTable_step` consumes. -/
theorem musesRemovedPair_pred
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof) (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hdual : Phase1Duality reduced)
    (hrot : IsRotation c reduced)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ)
    (hstable : PairwiseStable prof μ) (hinv : StablePairInvariant reduced prof μ)
    (i : Fin c.pairs.length)
    (hi : μ (c.pairs.get i).2 =
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1})
    (j : Fin c.pairs.length) (hj : nextFin j c.length_pos = i) :
    μ (c.pairs.get j).2 = {(c.pairs.get j).2, (c.pairs.get i).1} := by
  obtain ⟨hsec, _, _⟩ := hrot i
  obtain ⟨h1, hq1⟩ := List.getElem?_eq_some_iff.mp hsec
  -- `first(p_i) = q_{i-1} = q_j`, at index 0 of `reduced p_i`.
  obtain ⟨j', hj', hhead⟩ := isRotation_pred_head c reduced hdual hrot i
  have hjj' : j' = j := nextFin_injective c.length_pos (hj'.trans hj.symm)
  subst j'
  rw [List.head?_eq_getElem?] at hhead
  obtain ⟨h0, hq0⟩ := List.getElem?_eq_some_iff.mp hhead
  have hpi_ne_qi : (c.pairs.get i).1 ≠ (c.pairs.get i).2 :=
    isRotation_proposer_ne_partner c reduced prof hsize hcompat hrot i
  have hpi_ne_pnext : (c.pairs.get i).1 ≠ (c.pairs.get (nextFin i c.length_pos)).1 :=
    isRotation_no_selfLoop c reduced prof hvalid hcompat hdual hrot i
  -- `q_i` ranks `p_i` strictly above `p_{i+1}`.
  have hpref : Ranks prof (c.pairs.get i).2
      {(c.pairs.get i).2, (c.pairs.get i).1}
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} :=
    rotation_eliminates_less_preferred_of_dual c reduced prof hvalid hrot hcompat hsym hdual i
  -- `μ p_i = {p_i, m}` with `m = pairPartner p_i (μ p_i) ∈ reduced p_i`.
  have hpi_in : (c.pairs.get i).1 ∈ μ (c.pairs.get i).1 :=
    (hvalid (c.pairs.get i).1).2 (μ (c.pairs.get i).1) (hmatch (c.pairs.get i).1).1
  have hcard_pi : (μ (c.pairs.get i).1).card = 2 :=
    hsize (c.pairs.get i).1 (μ (c.pairs.get i).1) (hmatch (c.pairs.get i).1).1
  have hμpi : μ (c.pairs.get i).1 =
      {(c.pairs.get i).1, pairPartner (c.pairs.get i).1 (μ (c.pairs.get i).1)} :=
    coalition_eq_pairPartner hpi_in hcard_pi
  set m := pairPartner (c.pairs.get i).1 (μ (c.pairs.get i).1) with hm_def
  have hm_mem : m ∈ reduced (c.pairs.get i).1 := hinv (c.pairs.get i).1
  obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_getElem.mp hm_mem
  -- `{q_i, p_i}` is not blocking ⇒ `p_i` does not prefer `q_i` to its match.
  have hnotblock : ¬ Ranks prof (c.pairs.get i).1
      {(c.pairs.get i).1, (c.pairs.get i).2}
      {(c.pairs.get i).1, m} := by
    intro hr
    apply hstable (c.pairs.get i).2 (c.pairs.get i).1
    refine ⟨hpi_ne_qi.symm, ?_, ?_⟩
    · rw [hi]; exact hpref
    · rw [hμpi, Finset.pair_comm (c.pairs.get i).2 (c.pairs.get i).1]; exact hr
  -- so `m` sits at index ≤ 1 of `reduced p_i`.
  have hk_le : k ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    apply hnotblock
    have hlt : (⟨1, h1⟩ : Fin (reduced (c.pairs.get i).1).length) < ⟨k, hk_lt⟩ :=
      Fin.mk_lt_mk.mpr hgt
    have hr := hcompat (c.pairs.get i).1 ⟨1, h1⟩ ⟨k, hk_lt⟩ hlt
    rwa [show (reduced (c.pairs.get i).1)[(⟨1, h1⟩ : Fin (reduced (c.pairs.get i).1).length)]
          = (c.pairs.get i).2 from hq1,
         show (reduced (c.pairs.get i).1)[(⟨k, hk_lt⟩ : Fin (reduced (c.pairs.get i).1).length)]
          = m from hk_eq] at hr
  -- `m = q_{i-1}` (index 0); rule out `m = q_i` (index 1).
  have hm_qj : m = (c.pairs.get j).2 := by
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with hk0 | hk1
    · subst hk0; rw [← hk_eq]; exact hq0
    · subst hk1
      exfalso
      have hm_qi : m = (c.pairs.get i).2 := by rw [← hk_eq]; exact hq1
      have hcons : μ (c.pairs.get i).2 = μ (c.pairs.get i).1 := by
        have h2 := (hmatch (c.pairs.get i).1).2
        rw [← hm_def, hm_qi] at h2
        exact h2
      rw [hi, hμpi, hm_qi] at hcons
      have hpi_in_rhs : (c.pairs.get i).1 ∈
          ({(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} : Finset α) := by
        rw [hcons]; exact Finset.mem_insert_self _ _
      rw [Finset.mem_insert, Finset.mem_singleton] at hpi_in_rhs
      rcases hpi_in_rhs with h | h
      · exact hpi_ne_qi h
      · exact hpi_ne_pnext h
  -- consistency: `μ p_i = {p_i, q_{i-1}}` ⇒ `μ q_{i-1} = {q_{i-1}, p_i}`.
  have hcons2 : μ (c.pairs.get j).2 = μ (c.pairs.get i).1 := by
    have h2 := (hmatch (c.pairs.get i).1).2
    rw [← hm_def, hm_qj] at h2
    exact h2
  rw [hcons2, hμpi, hm_qj]
  exact Finset.pair_comm _ _

omit [Fintype α] in
/-- **All-or-nothing.** A stable pair-matching `μ` that uses *one* removed pair
    (`μ q_{i₀} = {q_{i₀}, p_{i₀+1}}` at some index `i₀`) uses *every* removed pair:
    `μ q_i = {q_i, p_{i+1}}` for all `i`. Obtained by iterating the backward step
    `musesRemovedPair_pred` around the finite cycle. The cyclic successor `nextFin`
    is a bijection on `Fin r`, so taking predecessors from `i₀` reaches every index
    (`(i.val + k) % r = i₀.val` for `k = i₀ + r - i`), and the predicate is closed
    under predecessors by `musesRemovedPair_pred`. This is the load-bearing
    hypothesis the upper-matching branch of `solvableInTable_step` builds the
    `q_i ↦ p_i` rotation-shift witness on; it also discharges the
    `hpin`/`hclosed` list-pinning facts the witness's `IsPairMatching` needs. -/
theorem musesRemovedPair_all
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof) (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hdual : Phase1Duality reduced)
    (hrot : IsRotation c reduced)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ)
    (hstable : PairwiseStable prof μ) (hinv : StablePairInvariant reduced prof μ)
    (i₀ : Fin c.pairs.length)
    (hi₀ : μ (c.pairs.get i₀).2 =
      {(c.pairs.get i₀).2, (c.pairs.get (nextFin i₀ c.length_pos)).1}) :
    ∀ i : Fin c.pairs.length, μ (c.pairs.get i).2 =
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} := by
  -- Backward step around the cycle: holds at the successor ⇒ holds here.
  have hback : ∀ j : Fin c.pairs.length,
      μ (c.pairs.get (nextFin j c.length_pos)).2 =
        {(c.pairs.get (nextFin j c.length_pos)).2,
         (c.pairs.get (nextFin (nextFin j c.length_pos) c.length_pos)).1} →
      μ (c.pairs.get j).2 =
        {(c.pairs.get j).2, (c.pairs.get (nextFin j c.length_pos)).1} := by
    intro j hPnext
    exact musesRemovedPair_pred c reduced prof hsize hvalid hcompat hsym hdual hrot
      μ hmatch hstable hinv (nextFin j c.length_pos) hPnext j rfl
  -- Every index is reached from `i₀` by `k` backward steps.
  have key : ∀ k : ℕ, ∀ i : Fin c.pairs.length,
      (i.val + k) % c.pairs.length = i₀.val →
      μ (c.pairs.get i).2 =
        {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} := by
    intro k
    induction k with
    | zero =>
      intro i hik
      rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt] at hik
      rw [Fin.ext hik]; exact hi₀
    | succ k ih =>
      intro i hik
      refine hback i (ih (nextFin i c.length_pos) ?_)
      show ((i.val + 1) % c.pairs.length + k) % c.pairs.length = i₀.val
      rw [Nat.mod_add_mod, show i.val + 1 + k = i.val + (k + 1) from by omega]
      exact hik
  intro i
  refine key (i₀.val + c.pairs.length - i.val) i ?_
  rw [show i.val + (i₀.val + c.pairs.length - i.val) = i₀.val + c.pairs.length from by
        have := i.isLt; omega,
     Nat.add_mod_right, Nat.mod_eq_of_lt i₀.isLt]

omit [Fintype α] in
/-- **All-or-nothing, proposer side.** Companion to `musesRemovedPair_all`: once a
    stable matching `μ` is the *upper* matching (uses every removed pair,
    `μ q_i = {q_i, p_{i+1}}` for all `i`), each proposer is matched to the partner
    at its predecessor index — `μ p_i = {p_i, q_{i-1}}`, where `i-1 = j` is the
    index with `nextFin j = i`. Read off `μ q_j = {q_j, p_i}` (all-or-nothing at the
    predecessor `j`, via `nextFin_surjective`) by matching-consistency, with
    `q_j ≠ p_i` falling out of `(μ q_j).card = 2` — no standalone proposer/partner
    disjointness needed (that is probe-refuted unconditionally). Together with
    `musesRemovedPair_all` this shows the rotation's agent set `{q_i} ∪ {p_i}` is
    closed under `μ`-partnering: every cycle agent's partner is again a cycle agent
    (`q_i ↦ p_{i+1}` from `musesRemovedPair_all`, `p_i ↦ q_{i-1}` from here). That
    closure is what discharges the `hclosed` hypothesis (off-cycle agents keep
    off-cycle partners) of the upper-matching witness in `solvableInTable_step`. -/
theorem musesRemovedPair_all_proposer
    (c : RotationCycle α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ)
    (hall : ∀ i : Fin c.pairs.length, μ (c.pairs.get i).2 =
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1}) :
    ∀ i : Fin c.pairs.length, ∃ j : Fin c.pairs.length,
      nextFin j c.length_pos = i ∧
      μ (c.pairs.get i).1 = {(c.pairs.get i).1, (c.pairs.get j).2} := by
  intro i
  obtain ⟨j, hj⟩ := nextFin_surjective c.length_pos i
  refine ⟨j, hj, ?_⟩
  have hqj : μ (c.pairs.get j).2 = {(c.pairs.get j).2, (c.pairs.get i).1} := by
    rw [hall j, hj]
  have hcard : (μ (c.pairs.get j).2).card = 2 :=
    hsize (c.pairs.get j).2 (μ (c.pairs.get j).2) (hmatch (c.pairs.get j).2).1
  have hne : (c.pairs.get i).1 ≠ (c.pairs.get j).2 := by
    intro h
    rw [hqj, h] at hcard
    simp at hcard
  have hpp : pairPartner (c.pairs.get j).2 (μ (c.pairs.get j).2) = (c.pairs.get i).1 :=
    pairPartner_eq_of_card_two hcard
      (by rw [hqj]; exact Finset.mem_insert_self _ _)
      (by rw [hqj]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      hne
  have h2 := (hmatch (c.pairs.get j).2).2
  rw [hpp] at h2
  rw [h2, hqj]
  exact Finset.pair_comm _ _

omit [Fintype α] in
/-- **All-or-nothing from existence** — the entry point of the upper-matching branch
    of `solvableInTable_step`. From the post-`push_neg` branch hypothesis that *some*
    agent is matched in the stable `μ` to a partner it must give up under rotation
    elimination (`∃ a, pairPartner a (μ a) ∈ rotationRemovals c a`), derive the full
    all-or-nothing fact `μ q_i = {q_i, p_{i+1}}` for *every* index. `musesRemovedPair_index`
    pins `μ a` to one removal pair `{q_i, p_{i+1}}` and tags `a`'s role (`q_i` or
    `p_{i+1}`); in the `q_i` role this is the seed directly, and in the `p_{i+1}` role it
    transports across the pair via matching-consistency (`pairPartner p_{i+1} (μ p_{i+1}) =
    q_i`, distinct by `(μ p_{i+1}).card = 2`, so `(hmatch _).2` gives `μ q_i = μ p_{i+1} =
    {q_i, p_{i+1}}`). `musesRemovedPair_all` then iterates the seed around the cycle. This
    is the single load-bearing fact the `q_i ↦ p_i` rotation-shift witness's
    `hpin`/`hclosed`/cycle-avoid hypotheses are discharged from. -/
theorem musesRemovedPair_all_of_exists
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof) (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hdual : Phase1Duality reduced)
    (hrot : IsRotation c reduced)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ)
    (hstable : PairwiseStable prof μ) (hinv : StablePairInvariant reduced prof μ)
    (hex : ∃ a : α, pairPartner a (μ a) ∈ rotationRemovals c a) :
    ∀ i : Fin c.pairs.length, μ (c.pairs.get i).2 =
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} := by
  obtain ⟨a, ha⟩ := hex
  obtain ⟨i, hrole, hμa⟩ := musesRemovedPair_index prof c hsize hvalid μ hmatch a ha
  have hseed : μ (c.pairs.get i).2 =
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} := by
    rcases hrole with hq | hp
    · rw [hq] at hμa; exact hμa
    · rw [hp] at hμa
      have hcard : (μ (c.pairs.get (nextFin i c.length_pos)).1).card = 2 :=
        hsize _ _ (hmatch (c.pairs.get (nextFin i c.length_pos)).1).1
      have hp_in : (c.pairs.get (nextFin i c.length_pos)).1 ∈
          μ (c.pairs.get (nextFin i c.length_pos)).1 :=
        (hvalid (c.pairs.get (nextFin i c.length_pos)).1).2 _
          (hmatch (c.pairs.get (nextFin i c.length_pos)).1).1
      have hq_in : (c.pairs.get i).2 ∈ μ (c.pairs.get (nextFin i c.length_pos)).1 := by
        rw [hμa]; exact Finset.mem_insert_self _ _
      have hne : (c.pairs.get i).2 ≠ (c.pairs.get (nextFin i c.length_pos)).1 := by
        intro h; rw [hμa, h] at hcard; simp at hcard
      have hpp : pairPartner (c.pairs.get (nextFin i c.length_pos)).1
          (μ (c.pairs.get (nextFin i c.length_pos)).1) = (c.pairs.get i).2 :=
        pairPartner_eq_of_card_two hcard hp_in hq_in hne
      have h2 := (hmatch (c.pairs.get (nextFin i c.length_pos)).1).2
      rw [hpp, hμa] at h2
      exact h2
  exact musesRemovedPair_all c reduced prof hsize hvalid hcompat hsym hdual hrot
    μ hmatch hstable hinv i hseed

omit [Fintype α] in
/-- **Proposer/partner disjointness under the upper matching** (`hdisj`) — when
    the surviving stable matching `μ` is the *upper* matching (uses every removed
    pair, `μ q_i = {q_i, p_{i+1}}` for all `i`), the rotation's proposer set
    `{p_i}` and partner set `{q_j}` are disjoint: `p_i ≠ q_j` for all `i, j`. This
    is the conditional disjointness hypothesis the structural witness lemmas
    (`rotationShiftPartner_subsingleton`, `rotationShift_hpin`,
    `rotationShift_cycle_avoid`) all take — FALSE as a standalone rotation fact
    (2026-06-24 probe), discharged here from the all-or-nothing `hall`.

    **Structural, not stability-entangled** (the doc earlier conjectured this
    needed `PairwiseStable`; it does not). A collision `p_a = q_b` makes that one
    agent's `μ`-partner simultaneously its proposer-side partner `q_j`
    (`nextFin j = a`, `musesRemovedPair_all_proposer`) and its partner-side
    partner `p_{b+1}` (`hall b`), so `q_j = p_{b+1}`. But duality puts `q_j` at the
    *head* of `reduced p_a` (`isRotation_succ_head`: `first(p_a) = q_j`) while
    `p_{b+1}` is the *last* of `reduced q_b = reduced p_a` (`IsRotation`'s
    `last(q_b) = p_{b+1}`). The same agent at index `0` and index `len-1` of a
    length-≥-2 duplicate-free list contradicts `hnodup`. -/
theorem rotation_proposer_partner_disjoint_of_upper
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hnodup : ReducedTableNodup reduced)
    (hdual : Phase1Duality reduced)
    (hrot : IsRotation c reduced)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ)
    (hall : ∀ i : Fin c.pairs.length, μ (c.pairs.get i).2 =
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1}) :
    ∀ i j : Fin c.pairs.length, (c.pairs.get i).1 ≠ (c.pairs.get j).2 := by
  intro a b hpq
  -- proposer-side partner of `p_a`: `q_j` with `nextFin j = a`.
  obtain ⟨j, hjnext, hμpa⟩ :=
    musesRemovedPair_all_proposer c prof hsize μ hmatch hall a
  -- partner-side partner of `q_b` (= `p_a`): `p_{b+1}`.
  have hμqb := hall b
  have hcarda : (μ (c.pairs.get a).1).card = 2 :=
    hsize _ _ (hmatch (c.pairs.get a).1).1
  have hcardb : (μ (c.pairs.get b).2).card = 2 :=
    hsize _ _ (hmatch (c.pairs.get b).2).1
  have hne_qj : (c.pairs.get a).1 ≠ (c.pairs.get j).2 := by
    intro h; rw [hμpa, h] at hcarda; simp at hcarda
  have hne_pb : (c.pairs.get b).2 ≠ (c.pairs.get (nextFin b c.length_pos)).1 := by
    intro h; rw [hμqb, h] at hcardb; simp at hcardb
  -- the two readings of the same `μ`-partner agree: `q_j = p_{b+1}`.
  have hpp1 : pairPartner (c.pairs.get a).1 (μ (c.pairs.get a).1) = (c.pairs.get j).2 := by
    rw [hμpa]
    exact pairPartner_eq_of_card_two (Finset.card_pair hne_qj)
      (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (Ne.symm hne_qj)
  have hpp2 : pairPartner (c.pairs.get b).2 (μ (c.pairs.get b).2) =
      (c.pairs.get (nextFin b c.length_pos)).1 := by
    rw [hμqb]
    exact pairPartner_eq_of_card_two (Finset.card_pair hne_pb)
      (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (Ne.symm hne_pb)
  have hy : (c.pairs.get j).2 = (c.pairs.get (nextFin b c.length_pos)).1 := by
    rw [← hpp1, ← hpp2, hpq]
  -- duality: `q_j = first(reduced p_a)`.
  have hhead : (reduced (c.pairs.get a).1).head? = some (c.pairs.get j).2 := by
    have h := isRotation_succ_head c reduced hdual hrot j
    rwa [hjnext] at h
  -- `p_{b+1} = last(reduced q_b)`.
  obtain ⟨_, hlast, hne_nil⟩ := hrot b
  have hglast : (reduced (c.pairs.get b).2).getLast? =
      some (c.pairs.get (nextFin b c.length_pos)).1 := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne_nil,
      Option.getD_some] at hlast
    rw [List.getLast?_eq_some_getLast hne_nil, hlast]
  -- length ≥ 2, from `q_a = (reduced p_a)[1]`.
  obtain ⟨hsec, _, _⟩ := hrot a
  have hlen2 : 2 ≤ (reduced (c.pairs.get a).1).length := by
    obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.mp hsec
    omega
  -- transport onto the shared list `reduced q_b = reduced p_a` and clash head/last.
  rw [hpq] at hhead hlen2
  rw [← hy] at hglast
  rw [List.head?_eq_getElem?] at hhead
  rw [List.getLast?_eq_getElem?] at hglast
  obtain ⟨_, he0⟩ := List.getElem?_eq_some_iff.mp hhead
  obtain ⟨_, heL⟩ := List.getElem?_eq_some_iff.mp hglast
  have hidx : (0 : ℕ) = (reduced (c.pairs.get b).2).length - 1 :=
    (List.Nodup.getElem_inj_iff (hnodup (c.pairs.get b).2)).mp (he0.trans heL.symm)
  omega

omit [Fintype α] in
/-- **`hclosed` discharged from all-or-nothing** — under the upper-matching
    hypothesis (`μ` uses every removed pair, `μ q_i = {q_i, p_{i+1}}` for all
    `i`), the rotation's agent set is closed under `μ`-partnering, so an
    off-cycle agent's `μ`-partner is again off-cycle. This is exactly the
    `hclosed` structural hypothesis of `rotationShift_consistency` /
    `rotationShift_isPairMatching`, discharged in-branch: the partner-side
    closure `q_i ↦ p_{i+1}` is `hall`, the proposer-side closure `p_i ↦ q_{i-1}`
    is `musesRemovedPair_all_proposer`. Proof by case-analysis on the partner's
    shift head: if `pairPartner a (μ a)` is a cycle agent (`= q_i` or `= p_i`),
    matching-consistency + the size-2 matching pin `a` to the cycle
    (`a = p_{i+1}` resp. `a = q_{i-1}`), so `a`'s own shift list is nonempty —
    contradicting its off-cycle hypothesis `(rotationShiftPartner c a).head? =
    none`. -/
theorem rotationShift_hclosed
    (c : RotationCycle α) (reduced : α → List α) (prof : PreferenceProfile α)
    (hsize : SizeTwo prof) (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hrot : IsRotation c reduced)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ)
    (hall : ∀ i : Fin c.pairs.length, μ (c.pairs.get i).2 =
      {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1}) :
    ∀ a : α, (rotationShiftPartner c a).head? = none →
      (rotationShiftPartner c (pairPartner a (μ a))).head? = none := by
  intro a ha
  have ha_mem : a ∈ μ a := (hvalid a).2 (μ a) (hmatch a).1
  have hcardμa : (μ a).card = 2 := hsize a (μ a) (hmatch a).1
  have hp_ne_a : pairPartner a (μ a) ≠ a := pairPartner_ne ha_mem hcardμa
  have hcons : μ (pairPartner a (μ a)) = μ a := (hmatch a).2
  -- `a` is off-cycle: its shift list is empty.
  have ha_nil : rotationShiftPartner c a = [] := by
    cases hl : rotationShiftPartner c a with
    | nil => rfl
    | cons hd tl => rw [hl] at ha; simp at ha
  cases hb : (rotationShiftPartner c (pairPartner a (μ a))).head? with
  | none => rfl
  | some b =>
    exfalso
    have hbmem : b ∈ rotationShiftPartner c (pairPartner a (μ a)) :=
      List.mem_of_mem_head? (Option.mem_def.mpr hb)
    obtain ⟨i, hcase⟩ := mem_rotationShiftPartner hbmem
    rcases hcase with ⟨hp_eq, _⟩ | ⟨hp_eq, _⟩
    · -- `pairPartner a (μ a) = q_i`, so `μ a = {q_i, p_{i+1}}` and `a = p_{i+1}`.
      have hμa : μ a = {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} :=
        hcons.symm.trans ((congrArg μ hp_eq).trans (hall i))
      have hain : a ∈ ({(c.pairs.get i).2,
          (c.pairs.get (nextFin i c.length_pos)).1} : Finset α) := by
        rw [← hμa]; exact ha_mem
      have hane_qi : a ≠ (c.pairs.get i).2 := fun h => hp_ne_a (hp_eq.trans h.symm)
      have haeq : a = (c.pairs.get (nextFin i c.length_pos)).1 :=
        Finset.mem_singleton.mp ((Finset.mem_insert.mp hain).resolve_left hane_qi)
      have hane_qnext : a ≠ (c.pairs.get (nextFin i c.length_pos)).2 := by
        rw [haeq]
        exact isRotation_proposer_ne_partner c reduced prof hsize hcompat hrot
          (nextFin i c.length_pos)
      have hmem_shift :
          (c.pairs.get (nextFin i c.length_pos)).2 ∈ rotationShiftPartner c a := by
        simp only [rotationShiftPartner, List.mem_filterMap]
        exact ⟨nextFin i c.length_pos, List.mem_finRange _,
          (if_neg hane_qnext).trans (if_pos haeq)⟩
      rw [ha_nil] at hmem_shift; simp at hmem_shift
    · -- `pairPartner a (μ a) = p_i`, so `μ a = {p_i, q_{i-1}}` and `a = q_{i-1}`.
      obtain ⟨j, _, hμpi⟩ := musesRemovedPair_all_proposer c prof hsize μ hmatch hall i
      have hμa : μ a = {(c.pairs.get i).1, (c.pairs.get j).2} :=
        hcons.symm.trans ((congrArg μ hp_eq).trans hμpi)
      have hain : a ∈ ({(c.pairs.get i).1, (c.pairs.get j).2} : Finset α) := by
        rw [← hμa]; exact ha_mem
      have hane_pi : a ≠ (c.pairs.get i).1 := fun h => hp_ne_a (hp_eq.trans h.symm)
      have haeq : a = (c.pairs.get j).2 :=
        Finset.mem_singleton.mp ((Finset.mem_insert.mp hain).resolve_left hane_pi)
      have hmem_shift : (c.pairs.get j).1 ∈ rotationShiftPartner c a := by
        simp only [rotationShiftPartner, List.mem_filterMap]
        exact ⟨j, List.mem_finRange _, if_pos haeq⟩
      rw [ha_nil] at hmem_shift; simp at hmem_shift

/-- **Existential solvability is preserved by a Phase-2 step** — the corrected
    Phase-2 crux, replacing the false universal-survival
    `eliminateRotation_preserves_stablePair` (removed 2026-06-23). If the table
    admits a stable pair-matching surviving in it, so does its successor after
    eliminating an exposed rotation and restoring duality
    (`reduceTable ∘ eliminateRotation`).

    The witness (corrected 2026-06-23 after a Python-oracle probe refuted the
    earlier `q_i ↦ p_{i+1}` reading — that map never produces a survivor and is
    often not even a matching): take the surviving stable matching `μ` from
    `hsolv`. If `μ` is the *eliminated* ("upper") matching — i.e. it uses every
    removed pair, `μ q_i = {q_i, p_{i+1}}` for all `i` (rotations are
    all-or-nothing in a stable matching, so one removed pair forces all) — the
    witness is `μ` rotation-shifted by `q_i ↦ p_i` (each `q_i` re-paired with the
    proposer at its *own* rotation index; off-cycle agents unchanged). Otherwise
    `μ` already avoids every removed pair and is itself the witness. Both branches
    yield a pairwise-stable matching surviving `reduceTable (eliminateRotation …)`
    — probe-validated 6278/6278 Phase-2 steps over exhaustive n=4 + random
    n=6/8/10. The avoid branch is discharged; the upper-matching witness is the
    single remaining `sorry`. See `.cril/ideas.md`. -/
theorem solvableInTable_step
    (reduced : α → List α) (prof : PreferenceProfile α) (c : RotationCycle α)
    (hsize : SizeTwo prof)
    (hrot : IsRotation c reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hnodup : ReducedTableNodup reduced)
    (hvalid : IsValidProfile prof)
    (hdual : Phase1Duality reduced)
    (hsolv : SolvableInTable reduced prof) :
    SolvableInTable (reduceTable (eliminateRotation reduced c)) prof := by
  obtain ⟨μ, hmatch, hstable, hinv⟩ := hsolv
  by_cases hall : ∀ a : α, pairPartner a (μ a) ∉ rotationRemovals c a
  · -- **Avoid branch (discharged).** `μ` uses no removed pair, so it survives the
    -- rotation elimination unchanged (`stablePair_eliminate_of_avoids`) and already
    -- witnesses the successor's solvability — `solvableInTable_of_eliminate_survivor`
    -- discharges the reduce pass + `SolvableInTable` packaging.
    exact solvableInTable_of_eliminate_survivor reduced prof c hsize hrot hcompat hsym
      hnodup hvalid μ hmatch hstable
      (stablePair_eliminate_of_avoids reduced prof c μ hinv hall)
  · -- **Upper-matching branch (open).** `μ` uses *some* removed pair; rotations being
    -- all-or-nothing in a stable matching (`hdual` + `hcompat`) it then uses *every*
    -- removed pair `{q_i, p_{i+1}}` (μ q_i = p_{i+1} ∀i). Witness (probe-validated
    -- 2026-06-23; the old q_i↦p_{i+1} reading is FALSE): `μ` rotation-shifted by
    -- q_i ↦ p_i along the cycle (off-cycle agents unchanged). Show it is
    -- IsPairMatching + PairwiseStable and avoids every removed pair, then it feeds
    -- `stablePair_eliminate_of_avoids` + `solvableInTable_of_eliminate_survivor`
    -- exactly as the avoid branch above does.
    push_neg at hall
    -- All-or-nothing now in hand: `μ` is the upper matching, using every removed pair.
    -- This is the load-bearing fact the shift witness's `hpin`/`hclosed`/cycle-avoid
    -- hypotheses are discharged from (next units).
    have hall_pairs : ∀ i : Fin c.pairs.length, μ (c.pairs.get i).2 =
        {(c.pairs.get i).2, (c.pairs.get (nextFin i c.length_pos)).1} :=
      musesRemovedPair_all_of_exists c reduced prof hsize hvalid hcompat hsym hdual hrot
        μ hmatch hstable hinv hall
    sorry

/-- The reduce pass establishes the five structural reduced-table invariants
    from a symmetric, duplicate-free, compatible starting table: it carries
    symmetry, compatibility, and duplicate-freeness forward and additionally
    establishes `CascadeInvariant` and `Phase1Duality`. The shared reduce-pass
    brick of Phase 1's reduce tail (`phase1_produces_reduced_table` will run it
    on the initial full table) and each Phase 2 step
    (`phase2_reduceTable_step_preserves_invariants` runs it after
    `eliminateRotation`). Pure composition of `reduceTable_preserves_symmetric`,
    `reduceTable_preserves_compatible`, `cascadeInvariant_reduceTable`,
    `phase1Duality_reduceTable`, and `reduceTable_preserves_nodup`. -/
theorem reduceTable_establishes_invariants
    (reduced : α → List α) (prof : PreferenceProfile α)
    (hsym : ReducedTableSymmetric reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hnodup : ReducedTableNodup reduced) :
    ReducedTableSymmetric (reduceTable reduced) ∧
    ReducedListCompatible (reduceTable reduced) prof ∧
    CascadeInvariant (reduceTable reduced) ∧
    Phase1Duality (reduceTable reduced) ∧
    ReducedTableNodup (reduceTable reduced) :=
  ⟨reduceTable_preserves_symmetric reduced hnodup hsym,
   reduceTable_preserves_compatible prof reduced hcompat,
   cascadeInvariant_reduceTable reduced hnodup hsym,
   phase1Duality_reduceTable reduced hnodup hsym,
   reduceTable_preserves_nodup reduced hnodup⟩

omit [Fintype α] in
/-- **Phase-1 seed of `StableMatchingsSurvive`.** Every genuine stable
    pair-matching's partners are listed in the *initial* table: `μ a` is a
    size-2 ranked coalition `{a, pairPartner a (μ a)}` (validity + `SizeTwo`),
    and consistency (`μ (pairPartner a (μ a)) = μ a`) makes the same pair appear
    in the partner's profile, so the pair is *mutual* and `mem_initialTable`
    places the partner on `initialTable prof a`. The reduce pass then carries it
    forward (`reduceTable_preserves_stablePair`). -/
lemma initialTable_stablePair {prof : PreferenceProfile α}
    (hsize : SizeTwo prof) (hvalid : IsValidProfile prof)
    (μ : Grouping α) (hmatch : IsPairMatching prof μ) :
    StablePairInvariant (initialTable prof) prof μ := by
  intro a
  rw [mem_initialTable hsize hvalid]
  have ha_in : a ∈ μ a := (hvalid a).2 (μ a) (hmatch a).1
  have hcard : (μ a).card = 2 := hsize a (μ a) (hmatch a).1
  have hμa : μ a = {a, pairPartner a (μ a)} := coalition_eq_pairPartner ha_in hcard
  refine ⟨by rw [← hμa]; exact (hmatch a).1, ?_⟩
  have hb_mem : μ (pairPartner a (μ a)) ∈ prof (pairPartner a (μ a)) :=
    (hmatch (pairPartner a (μ a))).1
  rw [(hmatch a).2] at hb_mem
  rw [← hμa]
  exact hb_mem

/-- **`StableMatchingsSurvive` for the Phase-1 witness.** Running the reduce
    pass on the initial table preserves every genuine stable matching:
    `initialTable_stablePair` seeds `StablePairInvariant` and
    `reduceTable_preserves_stablePair` carries it across the fixpoint (the
    `IsPairMatching` hypotheses — validity, size-2, consistency — are read off
    `hmatch`/`hvalid`/`hsize`). This is the sixth output conjunct of
    `phase1_produces_reduced_table` for the witness `reduceTable (initialTable
    prof)`. -/
theorem initialTable_stableMatchingsSurvive {prof : PreferenceProfile α}
    (hsize : SizeTwo prof) (hvalid : IsValidProfile prof) :
    StableMatchingsSurvive (reduceTable (initialTable prof)) prof := by
  intro μ hmatch hstable
  exact reduceTable_preserves_stablePair (initialTable prof) prof μ hsize
    (initialTable_compatible hsize hvalid)
    (initialTable_nodup hsize hvalid)
    (initialTable_symmetric hsize hvalid)
    hstable
    (fun a => (hvalid a).2 (μ a) (hmatch a).1)
    (fun a => hsize a (μ a) (hmatch a).1)
    (fun a => (hmatch a).2)
    (initialTable_stablePair hsize hvalid μ hmatch)

omit [Fintype α] in
/-- **Nonempty-or-unsolvable, the seventh Phase-1 conjunct.** From universal
    survival, each agent's reduced list is nonempty unless the instance admits
    no stable pair-matching at all: if some genuine `μ` is stable, survival
    keeps `pairPartner a (μ a)` on `reduced a`, so it is nonempty; otherwise the
    right disjunct holds outright. Pure consequence of `StableMatchingsSurvive`,
    independent of the table's construction. -/
lemma nonempty_or_unsolvable_of_survive {reduced : α → List α}
    {prof : PreferenceProfile α} (hsurv : StableMatchingsSurvive reduced prof) (a : α) :
    reduced a ≠ [] ∨
      ∀ μ : Grouping α, IsPairMatching prof μ → ¬ PairwiseStable prof μ := by
  by_cases h : ∃ μ : Grouping α, IsPairMatching prof μ ∧ PairwiseStable prof μ
  · obtain ⟨μ, hmatch, hstable⟩ := h
    exact Or.inl (List.ne_nil_of_mem (hsurv μ hmatch hstable a))
  · exact Or.inr (fun μ hmatch hstable => h ⟨μ, hmatch, hstable⟩)

omit [Fintype α] in
/-- **Base case of the `RemovedDominated` thread.** The initial table contains
    *every* mutually-ranked pair (`mem_initialTable`), so no mutual pair is ever
    deleted in it: `RemovedDominated`'s premise (`c ∉ reduced a` for a mutual
    `{a, c}`) is never met, and the invariant holds vacuously. This seeds the
    Phase-1 ∘ Phase-2 threading that `reducedTable_singleton_stable` consumes. -/
theorem initialTable_removedDominated (prof : PreferenceProfile α)
    (hsize : SizeTwo prof) (hvalid : IsValidProfile prof) :
    RemovedDominated (initialTable prof) prof := by
  intro a c hac_a hac_c hc_notin
  exact absurd ((mem_initialTable hsize hvalid a c).mpr ⟨hac_a, hac_c⟩) hc_notin

omit [Fintype α] in
/-- **Monotone transfer of a domination disjunct under list-shrinking.** A pair
    `{a, c}` dominated relative to `reduced` stays dominated relative to any
    pointwise sublist `reduced'` (both `a`'s and `c`'s lists only lose entries):
    each `∀ d ∈ reduced …` disjunct survives restriction of its quantifier. This
    is the carry-forward step for *already-removed* pairs when threading
    `RemovedDominated` across a Phase-1 / Phase-2 deletion — only the freshly
    removed pairs need a fresh justification. -/
theorem removedDominated_disjunct_mono
    {reduced reduced' : α → List α} {prof : PreferenceProfile α} {a c : α}
    (hsuba : ∀ d, d ∈ reduced' a → d ∈ reduced a)
    (hsubc : ∀ d, d ∈ reduced' c → d ∈ reduced c)
    (hdisj : (∀ d ∈ reduced a, Ranks prof a {a, d} {a, c}) ∨
             (∀ d ∈ reduced c, Ranks prof c {c, d} {c, a})) :
    (∀ d ∈ reduced' a, Ranks prof a {a, d} {a, c}) ∨
    (∀ d ∈ reduced' c, Ranks prof c {c, d} {c, a}) := by
  rcases hdisj with h | h
  · exact Or.inl fun d hd => h d (hsuba d hd)
  · exact Or.inr fun d hd => h d (hsubc d hd)

omit [Fintype α] in
/-- **The last entry of a compatible reduced list is least-preferred.** If `e`
    is the last element of `reduced a`, then `a` ranks every *other* entry `d` of
    its list strictly above `e`. The fresh-removal brick of the
    `RemovedDominated` thread: a rotation deletes `q_i`'s last choice `p_{i+1}`
    (`last(q_i) = p_{i+1}`), so every partner `q_i` keeps strictly outranks it —
    the `q_i`-side disjunct that justifies both directions of the removal. -/
theorem reducedList_getLast_dominated
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hcompat : ReducedListCompatible reduced prof)
    (a e d : α)
    (he : (reduced a).getLast? = some e)
    (hd : d ∈ reduced a) (hde : d ≠ e) :
    Ranks prof a {a, d} {a, e} := by
  have hne : reduced a ≠ [] := by intro h; rw [h] at he; simp at he
  obtain ⟨j, hj, hj_eq⟩ := List.mem_iff_getElem.mp hd
  have hlen : 0 < (reduced a).length := List.length_pos_of_ne_nil hne
  have hk : (reduced a).length - 1 < (reduced a).length := by omega
  have hk_eq : (reduced a)[(reduced a).length - 1] = e := by
    conv_lhs => rw [← List.getLast_eq_getElem hne]
    rw [List.getLast?_eq_some_getLast hne] at he
    exact Option.some.inj he
  have hjk : j < (reduced a).length - 1 := by
    rcases Nat.lt_or_ge j ((reduced a).length - 1) with h | h
    · exact h
    · exfalso
      have hjeq : j = (reduced a).length - 1 := by omega
      exact hde (by rw [← hj_eq, ← hk_eq]; congr 1)
  rw [show d = (reduced a)[j] from hj_eq.symm,
      show e = (reduced a)[(reduced a).length - 1] from hk_eq.symm]
  exact hcompat _ ⟨j, hj⟩ ⟨_, hk⟩ hjk

omit [Fintype α] in
/-- **Take/drop positional domination.** Under compatibility, every entry `d` of
    a kept prefix `(reduced a).take n` is ranked strictly above every entry `x`
    of the dropped tail `(reduced a).drop n` (a prefix entry sits at a strictly
    lower index than any suffix entry). The reduce-truncation fresh-removal brick
    of the `RemovedDominated` thread: `reduceStep` truncates a first choice's list
    to `take (idxOf · + 1)`, so any partner dropped past that index is outranked
    by every kept one — the rejector-side disjunct that justifies the deletion.
    Generalises `reducedList_getLast_dominated` (whose `getLast` is the sole entry
    of the dropped tail of `take (length - 1)`). -/
theorem reducedList_take_drop_dominated
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hcompat : ReducedListCompatible reduced prof)
    (a d x : α) (n : ℕ)
    (hd : d ∈ (reduced a).take n) (hx : x ∈ (reduced a).drop n) :
    Ranks prof a {a, d} {a, x} := by
  obtain ⟨j, hj, hj_eq⟩ := List.mem_iff_getElem.mp hd
  obtain ⟨i, hi, hi_eq⟩ := List.mem_iff_getElem.mp hx
  have hjm : j < min n (reduced a).length := by rwa [List.length_take] at hj
  have him : i < (reduced a).length - n := by rwa [List.length_drop] at hi
  have hjl : j < (reduced a).length := lt_of_lt_of_le hjm (min_le_right _ _)
  have hil : n + i < (reduced a).length := by omega
  have hd_at : (reduced a)[j]'hjl = d := by
    have hcast : ((reduced a).take n)[j] = (reduced a)[j]'hjl := by
      simp only [List.getElem_take]
    rw [← hcast]; exact hj_eq
  have hx_at : (reduced a)[n + i]'hil = x := by rw [← hi_eq, List.getElem_drop]
  have hlt : j < n + i := by omega
  rw [show d = (reduced a)[j]'hjl from hd_at.symm,
      show x = (reduced a)[n + i]'hil from hx_at.symm]
  exact hcompat a ⟨j, hjl⟩ ⟨n + i, hil⟩ hlt

omit [Fintype α] in
/-- **Rotation-pass preservation of `RemovedDominated`.** Eliminating an exposed
    rotation `c` from a compatible table preserves the removed-pair domination
    invariant. A freshly removed pair is a rotation edge `{q_i, p_{i+1}}` with
    `p_{i+1} = last(q_i)` (`IsRotation`), so `reducedList_getLast_dominated`
    supplies the `q_i`-side disjunct (`q_i` outranks `p_{i+1}` over every kept
    partner), which justifies the deletion in *both* edge directions; an
    already-removed pair carries forward by `removedDominated_disjunct_mono`
    (`eliminateRotation` only shrinks lists). The Phase-2 fresh-removal step of
    the `RemovedDominated` thread that `reducedTable_singleton_stable` needs. -/
theorem eliminateRotation_preserves_removedDominated
    (reduced : α → List α) (prof : PreferenceProfile α) (c : RotationCycle α)
    (hcompat : ReducedListCompatible reduced prof)
    (hrot : IsRotation c reduced)
    (hrd : RemovedDominated reduced prof) :
    RemovedDominated (eliminateRotation reduced c) prof := by
  intro a c' hac_a hac_c hc_notin
  by_cases hin : c' ∈ reduced a
  · -- Fresh removal: `c'` survived in `reduced a` but is filtered out, so `(a, c')`
    -- is a rotation edge.
    have hrem : c' ∈ rotationRemovals c a := by
      by_contra hcon
      exact hc_notin
        (by simp only [eliminateRotation, List.mem_filter, decide_eq_true_eq]
            exact ⟨hin, hcon⟩)
    obtain ⟨i, hcase⟩ := mem_rotationRemovals hrem
    obtain ⟨_, hlast, hne⟩ := hrot i
    have hgl : (reduced (c.pairs.get i).2).getLast?
        = some (c.pairs.get (nextFin i c.length_pos)).1 := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
        Option.getD_some] at hlast
      rw [List.getLast?_eq_some_getLast hne, hlast]
    rcases hcase with ⟨ha, hc'⟩ | ⟨ha, hc'⟩
    · -- `a = q_i`, `c' = p_{i+1}`: the `a`-side (= `q_i`-side) disjunct.
      subst ha hc'
      refine Or.inl fun d hd => ?_
      simp only [eliminateRotation, List.mem_filter, decide_eq_true_eq] at hd
      have hdne : d ≠ (c.pairs.get (nextFin i c.length_pos)).1 := by
        intro heq; rw [heq] at hd; exact hd.2 hrem
      exact reducedList_getLast_dominated reduced prof hcompat (c.pairs.get i).2
        (c.pairs.get (nextFin i c.length_pos)).1 d hgl hd.1 hdne
    · -- `a = p_{i+1}`, `c' = q_i`: the `c'`-side (= `q_i`-side) disjunct.
      subst ha hc'
      refine Or.inr fun d hd => ?_
      simp only [eliminateRotation, List.mem_filter, decide_eq_true_eq] at hd
      have hpr : (c.pairs.get (nextFin i c.length_pos)).1
          ∈ rotationRemovals c (c.pairs.get i).2 := rotationRemovals_symm hrem
      have hdne : d ≠ (c.pairs.get (nextFin i c.length_pos)).1 := by
        intro heq; rw [heq] at hd; exact hd.2 hpr
      exact reducedList_getLast_dominated reduced prof hcompat (c.pairs.get i).2
        (c.pairs.get (nextFin i c.length_pos)).1 d hgl hd.1 hdne
  · -- Already removed before this rotation: the disjunct transfers down the
    -- (shorter) filtered lists.
    refine removedDominated_disjunct_mono ?_ ?_ (hrd a c' hac_a hac_c hin)
    · intro d hd
      simp only [eliminateRotation, List.mem_filter, decide_eq_true_eq] at hd
      exact hd.1
    · intro d hd
      simp only [eliminateRotation, List.mem_filter, decide_eq_true_eq] at hd
      exact hd.1

omit [Fintype α] in
/-- `reduceStep` only shrinks lists: every entry of `reduceStep reduced s x` was
    already in `reduced x` (a prefix at the first choice, a filter at dropped
    entries, untouched elsewhere). The sublist fact
    `removedDominated_disjunct_mono` consumes for already-removed pairs. -/
private lemma reduceStep_subset (reduced : α → List α) (s x : α) :
    ∀ d, d ∈ reduceStep reduced s x → d ∈ reduced x := by
  intro d hd
  simp only [reduceStep] at hd
  split_ifs at hd with h1 h2
  · rw [h1]; exact List.take_subset _ _ hd
  · exact List.mem_of_mem_filter hd
  · exact hd

omit [Fintype α] in
/-- **Reduce-step preservation of `RemovedDominated`.** One `reduceStep` of a
    compatible table preserves the removed-pair domination invariant — the
    reduce-pass analogue of `eliminateRotation_preserves_removedDominated`. A
    freshly removed pair is the truncation at the step's first choice `f`: either
    `a = f`, so `c` falls in the dropped tail of `reduced a` and every kept prefix
    entry outranks it (`reducedList_take_drop_dominated`, the `a`-side disjunct),
    or `a` is a dropped entry of `reduced f` whose deleted partner is `c = f`, and
    `f`'s own truncation puts `a` in its dropped tail so every kept `d` of
    `reduced f` outranks `a` (the `c`-side disjunct). An already-removed pair
    carries forward by `removedDominated_disjunct_mono` (`reduceStep` only shrinks
    lists, `reduceStep_subset`). -/
private lemma reduceStep_preserves_removedDominated (reduced : α → List α) (s : α)
    (prof : PreferenceProfile α)
    (hcompat : ReducedListCompatible reduced prof)
    (hrd : RemovedDominated reduced prof) :
    RemovedDominated (reduceStep reduced s) prof := by
  intro a c hac_a hac_c hc_notin
  by_cases hin : c ∈ reduced a
  · -- Fresh removal at this step: `c` survived in `reduced a` but `reduceStep` drops it.
    by_cases haf : a = (reduced s).head?.getD s
    · -- `a` is the step's first choice `f`: its list is truncated, so `c` sits in
      -- the dropped tail and every kept prefix entry outranks it (`a`-side).
      have hstep_eq : reduceStep reduced s a
          = (reduced a).take ((reduced a).idxOf s + 1) := by
        rw [haf]; exact reduceStep_at_first reduced s
      left
      intro d hd
      rw [hstep_eq] at hd
      rw [hstep_eq] at hc_notin
      have hc_drop : c ∈ (reduced a).drop ((reduced a).idxOf s + 1) := by
        have hsplit : c ∈ (reduced a).take ((reduced a).idxOf s + 1)
            ++ (reduced a).drop ((reduced a).idxOf s + 1) := by
          rw [List.take_append_drop]; exact hin
        exact (List.mem_append.mp hsplit).resolve_left hc_notin
      exact reducedList_take_drop_dominated reduced prof hcompat a d c
        ((reduced a).idxOf s + 1) hd hc_drop
    · by_cases had : a ∈ (reduced ((reduced s).head?.getD s)).drop
          ((reduced ((reduced s).head?.getD s)).idxOf s + 1)
      · -- `a` is a dropped entry of `f`'s list: `reduceStep` filters `f = c` out of
        -- `a`'s list, and `f`'s truncation puts `a` in its dropped tail (`c`-side).
        have hstep_eq : reduceStep reduced s a
            = (reduced a).filter (· ≠ (reduced s).head?.getD s) := by
          simp only [reduceStep, if_neg haf, if_pos had]
        rw [hstep_eq] at hc_notin
        have hcf : c = (reduced s).head?.getD s := by
          by_contra hne
          apply hc_notin
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hin, hne⟩
        right
        intro d hd
        have hstepc : reduceStep reduced s c
            = (reduced c).take ((reduced c).idxOf s + 1) := by
          rw [hcf]; exact reduceStep_at_first reduced s
        rw [hstepc] at hd
        have ha_drop : a ∈ (reduced c).drop ((reduced c).idxOf s + 1) := by
          rw [hcf]; exact had
        exact reducedList_take_drop_dominated reduced prof hcompat c d a
          ((reduced c).idxOf s + 1) hd ha_drop
      · -- Untouched at `a`: `reduceStep reduced s a = reduced a`, contradicting the
        -- fresh-removal assumption.
        have hstep_eq : reduceStep reduced s a = reduced a := by
          simp only [reduceStep, if_neg haf, if_neg had]
        rw [hstep_eq] at hc_notin
        exact absurd hin hc_notin
  · -- Already removed before this step: the disjunct transfers down the shrunk lists.
    refine removedDominated_disjunct_mono ?_ ?_ (hrd a c hac_a hac_c hin)
    · exact reduceStep_subset reduced s a
    · exact reduceStep_subset reduced s c

/-- **Reduce-pass preservation of `RemovedDominated`.** The `reduceTable` fixpoint
    carries the removed-pair domination invariant from the starting table to the
    terminal one: each iteration is a `reduceStep`, preserving it
    (`reduceStep_preserves_removedDominated`) and compatibility
    (`reduceStep_preserves_compatible`). The reduce-pass companion of
    `eliminateRotation_preserves_removedDominated`; together they thread
    `RemovedDominated` through one full Phase-2 step. -/
theorem reduceTable_preserves_removedDominated (prof : PreferenceProfile α) :
    ∀ r : α → List α, ReducedListCompatible r prof → RemovedDominated r prof →
      RemovedDominated (reduceTable r) prof := by
  intro r
  induction r using reduceTable.induct with
  | case1 r h ih =>
    intro hcompat hrd
    rw [reduceTable]; simp only [dif_pos h]
    exact ih (reduceStep_preserves_compatible r _ prof hcompat)
             (reduceStep_preserves_removedDominated r _ prof hcompat hrd)
  | case2 r h =>
    intro hcompat hrd
    rw [reduceTable]; simp only [dif_neg h]
    exact hrd

/-- **Phase 1 output.** Starting from a valid size-2 profile, the reduce pass on
    the mutual-pair-restricted initial table — `reduceTable (initialTable prof)`,
    the Lean realization of the proposal-rejection loop — yields a reduced table
    that is symmetric, compatible, cascade-closed, duplicate-free,
    duality-restored, removed-pair-dominated, stable-matching-preserving, and
    either nowhere-empty or the instance has no stable matching. The five
    structural conjuncts come from `reduceTable_establishes_invariants` applied to
    the `initialTable_*` invariants; `RemovedDominated` from the vacuous base
    `initialTable_removedDominated` carried through `reduceTable_preserves_removedDominated`;
    `StableMatchingsSurvive` from `initialTable_stableMatchingsSurvive`;
    the final disjunct from `nonempty_or_unsolvable_of_survive`. The
    `ReducedTableNodup` conjunct is what the swapped Phase 2 (`reduceTable`)
    recursion threads; the `Phase1Duality` conjunct is the one Phase 2 carries
    forward so `hdual` is in scope at the rotation call sites; the
    `RemovedDominated` conjunct is threaded through Phase 2 and consumed by
    `reducedTable_singleton_stable`. -/
theorem phase1_produces_reduced_table
    (prof : PreferenceProfile α) (hsize : SizeTwo prof) (hvalid : IsValidProfile prof) :
    ∃ (reduced : α → List α),
      ReducedTableSymmetric reduced ∧
      ReducedListCompatible reduced prof ∧
      CascadeInvariant reduced ∧
      ReducedTableNodup reduced ∧
      Phase1Duality reduced ∧
      RemovedDominated reduced prof ∧
      StableMatchingsSurvive reduced prof ∧
      (∀ a : α, (reduced a) ≠ [] ∨
        ∀ μ : Grouping α, IsPairMatching prof μ → ¬ PairwiseStable prof μ) := by
  obtain ⟨hsym, hcompat, hcasc, hdual, hnodup⟩ :=
    reduceTable_establishes_invariants (initialTable prof) prof
      (initialTable_symmetric hsize hvalid)
      (initialTable_compatible hsize hvalid)
      (initialTable_nodup hsize hvalid)
  have hsurvive : StableMatchingsSurvive (reduceTable (initialTable prof)) prof :=
    initialTable_stableMatchingsSurvive hsize hvalid
  have hrd : RemovedDominated (reduceTable (initialTable prof)) prof :=
    reduceTable_preserves_removedDominated prof (initialTable prof)
      (initialTable_compatible hsize hvalid)
      (initialTable_removedDominated prof hsize hvalid)
  exact ⟨reduceTable (initialTable prof), hsym, hcompat, hcasc, hnodup, hdual, hrd, hsurvive,
    fun a => nonempty_or_unsolvable_of_survive hsurvive a⟩

/-- One Phase 2 iteration via the **reduce pass** — `eliminateRotation` followed
    by `reduceTable` (mirroring `src/irving.py::_reduce`, used in both phases) —
    re-establishes every invariant the swapped Phase 2 recursion threads
    *and* `Phase1Duality`, while strictly decreasing `totalLength`.

    Pure
    composition of proven lemmas: `eliminateRotation` preserves symmetry,
    compatibility (`rotation_elimination_preserves_invariants`) and nodup
    (`eliminateRotation_preserves_nodup`), then `reduceTable` carries all three
    forward (`reduceTable_preserves_{symmetric,compatible,nodup}`), establishes
    `CascadeInvariant` (`cascadeInvariant_reduceTable`) and `Phase1Duality`
    (`phase1Duality_reduceTable`), and does not increase length
    (`reduceTable_totalLength_le`). This is the per-step invariant bundle the
    existential-solvability `phase2` consumes at each rotation step; with
    `Phase1Duality` in scope, `rotationCycle_length_ge_2_of_dual` and
    `rotation_eliminates_less_preferred_of_dual` are available on demand (the
    `RotationCycle.length_pos` field need not be strengthened). Phase 2's
    solvability thread is the separate existential `SolvableInTable`, carried by
    `solvableInTable_step` — not part of this invariant bundle. -/
theorem phase2_reduceTable_step_preserves_invariants
    (reduced : α → List α) (prof : PreferenceProfile α) (c : RotationCycle α)
    (hsize : SizeTwo prof) (hrot : IsRotation c reduced)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hnodup : ReducedTableNodup reduced)
    (hrd : RemovedDominated reduced prof) :
    ReducedTableSymmetric (reduceTable (eliminateRotation reduced c)) ∧
    ReducedListCompatible (reduceTable (eliminateRotation reduced c)) prof ∧
    CascadeInvariant (reduceTable (eliminateRotation reduced c)) ∧
    Phase1Duality (reduceTable (eliminateRotation reduced c)) ∧
    ReducedTableNodup (reduceTable (eliminateRotation reduced c)) ∧
    RemovedDominated (reduceTable (eliminateRotation reduced c)) prof ∧
    totalLength (reduceTable (eliminateRotation reduced c)) < totalLength reduced := by
  obtain ⟨hsymE, hcompatE⟩ :=
    rotation_elimination_preserves_invariants c reduced prof hsize hrot hcompat hsym
  have hnodupE : ReducedTableNodup (eliminateRotation reduced c) :=
    eliminateRotation_preserves_nodup reduced c hnodup
  have hrdE : RemovedDominated (eliminateRotation reduced c) prof :=
    eliminateRotation_preserves_removedDominated reduced prof c hcompat hrot hrd
  obtain ⟨hsym', hcompat', hcasc', hdual', hnodup'⟩ :=
    reduceTable_establishes_invariants (eliminateRotation reduced c) prof hsymE hcompatE hnodupE
  have hrd' : RemovedDominated (reduceTable (eliminateRotation reduced c)) prof :=
    reduceTable_preserves_removedDominated prof (eliminateRotation reduced c) hcompatE hrdE
  exact ⟨hsym', hcompat', hcasc', hdual', hnodup', hrd',
    lt_of_le_of_lt (reduceTable_totalLength_le _)
      (eliminateRotation_decreases_totalLength reduced c hrot)⟩

/-- Phase 2 iteration: eliminate rotations until termination, deciding
    solvability **existentially**.

    Each iteration re-establishes `CascadeInvariant` after `eliminateRotation`
    by running a `reduceTable` pass (mirroring the corrected
    `src/irving.py::_reduce`, used in both phases), so the invariant is
    maintained across the recursion. The `ReducedTableNodup` hypothesis is what
    the `reduceTable` invariant lemmas demand; the reduce pass also establishes
    `Phase1Duality` of each successor table
    (`phase2_reduceTable_step_preserves_invariants`).

    The conclusion is the corrected existential disjunction (the false
    universal-survival thread was removed 2026-06-23): either the table reduces
    to an all-singleton table (yielding a stable matching), or it is **not
    solvable** (`¬ SolvableInTable`). The negative case lifts across the
    recursion by the contrapositive of `solvableInTable_step`. -/
noncomputable def phase2
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hcasc : CascadeInvariant reduced)
    (hnodup : ReducedTableNodup reduced)
    (hdual : Phase1Duality reduced)
    (hrd : RemovedDominated reduced prof) :
    (∃ (final : α → List α), AllSingleton final ∧
      ReducedTableSymmetric final ∧ ReducedListCompatible final prof ∧
      RemovedDominated final prof) ∨
    ¬ SolvableInTable reduced prof := by
  by_cases hempty : ∃ a, reduced a = []
  · obtain ⟨a, ha⟩ := hempty
    exact Or.inr (empty_not_solvableInTable reduced prof a ha)
  · push_neg at hempty
    by_cases hsing : AllSingleton reduced
    · exact Or.inl ⟨reduced, hsing, hsym, hcompat, hrd⟩
    · obtain ⟨a, ha_ne⟩ : ∃ a, (reduced a).length ≠ 1 := by
        by_contra hcon; push_neg at hcon; exact hsing hcon
      have ha : 2 ≤ (reduced a).length := by
        have hpos : 0 < (reduced a).length :=
          List.length_pos_of_ne_nil (hempty a)
        omega
      obtain ⟨c, hrot, _⟩ := findRotation reduced hsym hcasc a ha
      obtain ⟨hsym', hcompat', hcasc', hdual', hnodup', hrd', hlt⟩ :=
        phase2_reduceTable_step_preserves_invariants reduced prof c hsize hrot hcompat hsym hnodup hrd
      rcases phase2 (reduceTable (eliminateRotation reduced c)) prof hsize hvalid
          hcompat' hsym' hcasc' hnodup' hdual' hrd' with
        hpos | hneg
      · exact Or.inl hpos
      · exact Or.inr (mt (solvableInTable_step reduced prof c hsize hrot hcompat hsym
          hnodup hvalid hdual) hneg)
termination_by totalLength reduced
decreasing_by
  exact hlt

/-! ## Endpoint theorems -/

omit [DecidableEq α] [Fintype α] in
/-- In an all-singleton symmetric reduced table the partner relation is
    mutual: if `a`'s sole remaining partner is `b`, then `b`'s sole
    remaining partner is `a`. This is the well-formedness fact that lets
    `reducedTable_singleton_stable` read `singletonMatching` as a genuine
    (symmetric) matching — the analogue of `Core.pairPartner_mem`/`_ne`
    for the singleton-table representation. -/
private lemma singleton_partner_mutual
    (reduced : α → List α)
    (hsym : ReducedTableSymmetric reduced)
    (hsingleton : AllSingleton reduced)
    {a b : α} (hb : (reduced a).head? = some b) :
    (reduced b).head? = some a := by
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp (hsingleton a)
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp (hsingleton b)
  rw [hx, List.head?_cons, Option.some.injEq] at hb
  have hbmem : b ∈ reduced a := by rw [hx, ← hb]; simp
  have hamem : a ∈ reduced b := (hsym a b).mp hbmem
  rw [hy, List.mem_singleton] at hamem
  rw [hy, List.head?_cons, hamem]

omit [Fintype α] in
/-- The substantive half of `reducedTable_singleton_stable`: given the
    removed-pair domination invariant, the singleton matching has no blocking
    pair. A candidate `b` is either `a`'s sole remaining partner `x` (blocking
    contradicts `Ranks.irrefl`) or was deleted — then `RemovedDominated`
    supplies, on one side, that every kept partner outranks the other: either
    `a` ranks `x` above `b` (contradicting `a`'s blocking preference) or `b`
    ranks its partner `y` above `a` (contradicting `b`'s), each closed by
    `Ranks.trans` + `Ranks.irrefl`. -/
theorem singletonMatching_pairwiseStable_of_removed
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hvalid : IsValidProfile prof)
    (hsingleton : AllSingleton reduced)
    (hremoved : RemovedDominated reduced prof) :
    PairwiseStable prof (singletonMatching reduced) := by
  intro a b
  rintro ⟨-, hRa, hRb⟩
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp (hsingleton a)
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp (hsingleton b)
  have hμa : singletonMatching reduced a = {a, x} := by
    simp only [singletonMatching, hx, List.head?_cons, Option.getD_some]
  have hμb : singletonMatching reduced b = {b, y} := by
    simp only [singletonMatching, hy, List.head?_cons, Option.getD_some]
  rw [hμa] at hRa
  rw [hμb] at hRb
  by_cases hbx : b = x
  · subst hbx
    exact Ranks.irrefl hvalid hRa
  · have hmem : ({a, b} : Finset α) ∈ prof a := Ranks.fst_mem hRa
    have hmemc : ({a, b} : Finset α) ∈ prof b := Ranks.fst_mem hRb
    have hbnotin : b ∉ reduced a := by rw [hx]; simpa using hbx
    rcases hremoved a b hmem hmemc hbnotin with hleft | hright
    · have hxmem : x ∈ reduced a := by rw [hx]; simp
      have hpref : Ranks prof a {a, x} {a, b} := hleft x hxmem
      exact Ranks.irrefl hvalid (Ranks.trans hvalid hRa hpref)
    · have hymem : y ∈ reduced b := by rw [hy]; simp
      have hpref : Ranks prof b {b, y} {b, a} := hright y hymem
      rw [Finset.pair_comm a b] at hRb
      exact Ranks.irrefl hvalid (Ranks.trans hvalid hRb hpref)

omit [Fintype α] in
/-- **Singleton reduced table → pairwise-stable matching.** Given the removed-pair
    domination invariant `RemovedDominated` — established vacuously on
    `initialTable` and threaded through phase 1/2 (`phase1_produces_reduced_table`
    outputs it, `phase2` carries it forward) — the no-blocking argument is
    discharged by `singletonMatching_pairwiseStable_of_removed`. -/
theorem reducedTable_singleton_stable
    (reduced : α → List α)
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof)
    (hcompat : ReducedListCompatible reduced prof)
    (hsym : ReducedTableSymmetric reduced)
    (hsingleton : AllSingleton reduced)
    (hremoved : RemovedDominated reduced prof) :
    PairwiseStable prof (singletonMatching reduced) :=
  singletonMatching_pairwiseStable_of_removed reduced prof hvalid hsingleton hremoved

/-! ## Main decidability theorem -/

/-- **Irving decides pairwise stability.** The negative branch quantifies
    over genuine matchings (`IsPairMatching`) — bare `PairwiseStable` is
    vacuously satisfiable, e.g. by all-singleton groupings. -/
theorem irving_decides_stability
    (prof : PreferenceProfile α)
    (hsize : SizeTwo prof)
    (hvalid : IsValidProfile prof) :
    (∃ μ : Grouping α, PairwiseStable prof μ) ∨
    (∀ μ : Grouping α, IsPairMatching prof μ → ¬ PairwiseStable prof μ) := by
  obtain ⟨reduced, hsym, hcompat, hcasc, hnodup, hdual, hrd, hsurv, _hphase1⟩ :=
    phase1_produces_reduced_table prof hsize hvalid
  rcases phase2 reduced prof hsize hvalid hcompat hsym hcasc hnodup hdual hrd with
    ⟨final, hsing, hsym', hcompat', hrd'⟩ | hnsolv
  · exact Or.inl ⟨singletonMatching final,
      reducedTable_singleton_stable final prof hsize hvalid hcompat' hsym' hsing hrd'⟩
  · -- `hnsolv : ¬ SolvableInTable reduced prof`; combined with the (true)
    -- Phase-1 `StableMatchingsSurvive`, no stable pair-matching can exist.
    refine Or.inr fun μ hmatch hstable => ?_
    exact hnsolv (solvableInTable_of_survive reduced prof hsurv μ hmatch hstable)

end

end HedonicGrouping.Algorithms.Irving
