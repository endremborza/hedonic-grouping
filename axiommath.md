# AxiomMath AXLE Integration Plan

## What AXLE Is

AXLE (https://axle.axiommath.ai) is a Lean 4 proof toolkit with an API offering:
- `verify_proof` — validate a proof against a formal statement
- `repair_proofs` — attempt to repair broken/incomplete proofs
- `sorry2lemma` — extract `sorry` placeholders into standalone lemmas
- `have2lemma` — extract `have` steps into standalone lemmas
- `disprove` — attempt to disprove a theorem
- `simplify_theorems` — simplify completed proofs
- `check` — check Lean code for errors
- `extract_theorems` — split a Lean file into theorems with dependencies

Access: Python SDK (`pip install axiom-axle`), CLI (`axle verify-proof`), HTTP REST.

---

## Why This Matters for the Paper

The paper's single critical bottleneck is **Phase 2**: the proofs for Lemma 1 (algorithm → Gale-Shapley) and Lemma 2 (algorithm → Irving) are currently proof sketches with hand-wavy treatment of the "considerable" condition. The unification claim lives or dies on these lemmas.

Lean formalization via AXLE addresses this directly:
- Forces full precision on the "considerable" → GS/Irving mapping — no hand-waving survives type-checking
- `disprove` can actively stress-test the claim; if AXLE cannot refute the lemmas, confidence in correctness increases significantly
- Machine-verified proofs are a meaningful signal of correctness for workshop reviewers at MATCH-UP/COMSOC

---

## Formalization Scope

Formalize only what is needed to state and prove Lemma 1 and Lemma 2. Do not formalize the full algorithm or all corollaries yet.

### Core definitions to encode in Lean 4

```lean
-- Agents and preference profiles
structure Agent where
  id : Nat

-- A group is a Finset of agents
-- A preference profile M maps each agent to an ordered list of groups
-- "Considerable" condition: a group G is considerable for agent α
--   if every other member of G currently lists G in their M
-- Core stability: a partition π is core-stable if no subset of agents
--   all prefer some coalition to their current one
```

### Lemma 1 (→ Gale-Shapley) formal statement target

Under bipartite constraint (two disjoint groups, all coalitions of size 2):
the algorithm's "considerable" condition on pair {α_i, α_j} reduces to:
α_j's current best proposal is α_i (i.e., α_j holds α_i).
Therefore simplified_reduction ≡ Gale-Shapley deferred-acceptance on the bipartite graph.

### Lemma 2 (→ Irving) formal statement target

Under non-bipartite size-2 constraint:
a "move-on" chain α_1 → α_2 → ... → α_k → α_1 in the algorithm
corresponds exactly to Irving's rotation (q_0, q_1, ..., q_{r-1});
the algorithm's elimination step is the rotation elimination step.

---

## AXLE Workflow

### Step 1 — Scaffold with sorries
Write a Lean file with definitions + lemma statements, using `sorry` for all proofs.
Use `check` to confirm the file is syntactically valid and types are correct.

### Step 2 — Extract subgoals
Run `sorry2lemma` on the scaffolded file. This decomposes each lemma into the atomic
subgoals that need proving — making the proof obligations explicit and addressable one by one.

For Lemma 1, expected subgoals:
- "considerable" on size-2 bipartite pair ↔ one agent holds the other
- simplified_reduction step on such a pair ↔ GS proposal/hold step
- termination correspondence

For Lemma 2, expected subgoals:
- move-on chain of length k forms a cycle
- that cycle structure matches Irving rotation definition
- elimination actions are identical

### Step 3 — Prove subgoals iteratively
Fill in proofs for each extracted subgoal. After each attempt, run `verify_proof`
to confirm it holds.

If a proof attempt is close but broken, run `repair_proofs` before rewriting from scratch.

### Step 4 — Stress-test with disprove
Before finalizing, run `disprove` on each lemma statement. If AXLE finds a counterexample,
the unification claim needs revision — better to discover this now than at review.

If `disprove` fails to find a counterexample, note this in the paper as additional evidence.

### Step 5 — Simplify and extract
Once all subgoals are verified, run `simplify_theorems` to clean up the proofs.
Run `extract_theorems` to get a clean file per lemma with full dependency tracking.

### Step 6 — Integrate into paper
- Add a remark after Lemma 1 and Lemma 2 noting that the proofs are machine-verified in Lean 4
- Publish the Lean formalization as a supplementary artifact (or GitHub repo)
- Reference it in the paper's abstract or related work as a verification artifact

---

## File Structure

```
hedonic-grouping/
  lean/
    Defs.lean          -- agents, preferences, considerable, core stability
    Algorithm.lean     -- simplified_reduction, process, grouping
    Lemma1.lean        -- GS unification lemma + proof
    Lemma2.lean        -- Irving unification lemma + proof
    lakefile.lean      -- Mathlib dependency
```

---

## Priority and Sequencing

This is Phase 2 work — it directly addresses the paper's critical bottleneck.

1. Set up Lean 4 + Mathlib + AXLE SDK
2. Write `Defs.lean` — definitions only, verify with `check`
3. Scaffold `Lemma1.lean` with sorry, run `sorry2lemma`
4. Work through Lemma 1 subgoals with `verify_proof` / `repair_proofs`
5. Run `disprove` on Lemma 1
6. Repeat steps 3–5 for `Lemma2.lean`
7. Simplify, extract, and integrate references into paper

---

## Open Questions

- Does AXLE require Lean 4 or Lean 4 + Mathlib? The considerable condition and Finset reasoning will likely need Mathlib.
- API authentication: check https://axle.axiommath.ai/v1/docs/ for key requirements before starting.
- Is `disprove` bounded by timeout? For lemmas of this complexity, may need to set limits.

---

## Working Checklist

### Setup
- [ ] Install Lean 4 (`elan` toolchain manager)
- [ ] Create `lean/lakefile.lean` with Mathlib dependency
- [ ] Run `lake update` and confirm Mathlib builds
- [ ] Install AXLE SDK: `uv pip install axiom-axle` (use `/mnt/data/pytools` env)
- [ ] Check API key requirements at https://axle.axiommath.ai/v1/docs/
- [ ] Run a smoke-test `axle check` on a trivial Lean snippet to confirm end-to-end connectivity

### Defs.lean
- [ ] Define `Agent`, `Group` (as `Finset Agent`), `PreferenceProfile`
- [ ] Define `Considerable`: group G is considerable for α iff every other member of G lists G currently
- [ ] Define `CoreStable`: no subset of agents all prefer some coalition to their current assignment
- [ ] Define `SimplifiedReduction`: one step of the algorithm (prefer + considerable → assign)
- [ ] Run `axle check lean/Defs.lean` — fix all errors before proceeding

### Lemma 1 — GS Unification
- [ ] Write `lean/Lemma1.lean`: import Defs, state lemma with `sorry` body
  - Statement: bipartite + size-2 constraint → considerable on {α_i, α_j} ↔ α_j holds α_i → reduction step ≡ GS deferred-acceptance step
- [ ] Run `axle check lean/Lemma1.lean` to confirm statement typechecks
- [ ] Run `axle sorry2lemma lean/Lemma1.lean` — record extracted subgoals
- [ ] Subgoal: prove `considerable` on size-2 bipartite pair ↔ "holds" relation
- [ ] Subgoal: prove reduction step on such a pair ↔ GS proposal/hold step
- [ ] Subgoal: prove termination correspondence (both terminate in same round)
- [ ] Run `axle verify_proof` on each subgoal after filling it in
- [ ] If a proof is close but broken, run `axle repair_proofs` before rewriting
- [ ] Run `axle disprove lean/Lemma1.lean` — if counterexample found, revise claim
- [ ] Run `axle simplify_theorems lean/Lemma1.lean`
- [ ] Run `axle extract_theorems lean/Lemma1.lean` — clean dependency-tracked output

### Lemma 2 — Irving Unification
- [ ] Write `lean/Lemma2.lean`: import Defs, state lemma with `sorry` body
  - Statement: size-2 non-bipartite → move-on chain of length k forms a cycle ≡ Irving rotation; elimination step ≡ rotation elimination
- [ ] Run `axle check lean/Lemma2.lean`
- [ ] Run `axle sorry2lemma lean/Lemma2.lean` — record extracted subgoals
- [ ] Subgoal: prove move-on chain of length k forms a cycle
- [ ] Subgoal: prove cycle structure matches Irving rotation definition
- [ ] Subgoal: prove elimination actions are identical
- [ ] Run `axle verify_proof` on each subgoal
- [ ] Run `axle repair_proofs` where needed
- [ ] Run `axle disprove lean/Lemma2.lean`
- [ ] Run `axle simplify_theorems` + `axle extract_theorems`

### Paper Integration
- [ ] Add remark after Lemma 1: proof machine-verified in Lean 4 via AXLE
- [ ] Add remark after Lemma 2: same
- [ ] Publish Lean files as supplementary artifact (GitHub repo or appendix)
- [ ] Reference the formalization artifact in abstract or related work section
- [ ] Re-render paper with `tectonic` and check proofs read correctly in context
