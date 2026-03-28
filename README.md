# Hedonic Grouping

Lean 4 formalization of a unifying algorithm for stable matching as hedonic coalition formation.

## Core Claim

A single recursive algorithm subsumes both Gale-Shapley (bipartite matching) and Irving (stable roommates) as special cases, applied to general hedonic games with strict preferences over arbitrary coalitions. The algorithm is correct and complete but worst-case exponential — inherent since the general problem is NP-hard (Ballester 2004). It reduces to polynomial-time on tractable subclasses.

## Algorithm Representations

The core algorithm is defined in three parallel representations:

- **Pseudocode** (`tex/algorithms.tex`): LaTeX commands (`\AlgSimplifiedReduction`, `\AlgProcessing`, `\AlgGrouping`) imported by `tex/main.tex`.
- **Lean 4** (`HedonicGrouping/`): Formal definitions and proofs. `Defs.lean` (common framework), `GaleShapley.lean` (GS correspondence), `Irving.lean` (Irving correspondence).
- **Python** (`src/`): Reference implementations with stability verification and random instance generation:
  - `src/common.py` — Types (`Agent`, `Coalition`), stability verifiers, random generators
  - `src/gale_shapley.py` — Gale-Shapley for stable marriage (O(n^2), bipartite size-2)
  - `src/irving.py` — Irving's algorithm for stable roommates (O(n^2), non-bipartite size-2)
  - `src/hedonic.py` — General hedonic grouping (Algorithm 4, exponential worst-case)
  - `src/test_algorithms.py` — Tests for all algorithms: `python -m src.test_algorithms`

### College admissions

The many-to-one matching problem (colleges with quotas) is subsumed by the hedonic framework — each coalition includes a college and a student subset. This creates a combinatorial explosion: a college with quota q among n students generates C(n,q) coalitions, many equivalent from the college's perspective. Specialized algorithms (college-proposing GS, Roth-Peranson) exploit this structure for polynomial solutions; the general hedonic algorithm handles it correctly but with exponential cost.

## Paper Structure

The accompanying paper (`tex/main.tex`) introduces a framework `<A, Omega, M>` for hedonic coalition formation:

- **Section 2 — Related Work**: Connects to hedonic games literature (Dreze & Greenberg, Bogomolnaia & Jackson, Banerjee et al., Ballester, Woeginger, Cechlarova & Romero-Medina, Alcalde & Revilla).
- **Section 3 — Framework**: Formal notation, reviews marriage/college admissions/roommates problems, defines group stability (= core stability).
- **Section 4 — Algorithms**: Simplified Reduction (considerable proposals), Processing (move-on chains, exceptions), Recursive Grouping. Worked 5-agent example.
- **Section 5 — Connections**: Lemma 1 (algorithm = Gale-Shapley under bipartite size-2), Lemma 2 (algorithm = Irving under non-bipartite size-2).

## Formalization State

### Defs.lean — Common definitions

`PreferenceProfile`, `Considerable`, `BlockingCoalition`, `CoreStable`, `SizeTwo`, validity predicates. Maps directly to the paper's `<A, Omega, M>` framework. Also defines `AlgState` (algorithm state), `propMap` (connects to `Considerable`), `reducedTable` (connects to Irving rotations), `cascadeStep` (one step of the move-on cascade).

### GaleShapley.lean — Complete (no sorries)

Defines bipartite structure (`BipartiteStructure`, `BipartitePref`) and GS "holds" relation (`GSHolds`). Proves the hedonic algorithm's considerable condition reduces to GS holds on pairs:

- `considerable_iff_mutual_proposal`: on size-2 pair {a,b}, considerable iff the other agent proposes it
- `considerable_eq_gsHolds`: considerable = GS "holds" relation
- `lemma1_considerable_matches_gs`: main statement with bipartite hypotheses

### Irving.lean — Complete (no sorries)

Defines rotation cycles (`RotationCycle`, `IsRotation`) on reduced preference lists — no proposal map. Proves the hedonic cascade is outcome-equivalent to Irving's Phase 2:

- `rotation_eliminates_less_preferred`: eliminated partner is strictly less preferred
- `cascade_produces_irving_elimination`: rotation elimination preserves symmetry and compatibility invariants
- `eliminateRotation`: applies Irving's rotation elimination to a reduced table
- `ReducedListCompatible`, `ReducedTableSymmetric`: invariants connecting reduced lists to the full profile

## Proof Strategy for Lemma 2

The prior formalization attempted a direct predicate equivalence (`IsMoveOnChain → IsIrvingRotation`) under a single proposal map. This was **provably false**: `IsMoveOnChain` requires `prop p_i != some {p_i, q_i}` (proposers moved on) while `IsIrvingRotation` required `prop p_i = some {p_i, q_i}` (proposers hold current match) — a direct contradiction, because the two predicates described different algorithm states sharing a `prop` they could not share.

The correct mediating structure is the **reduced preference table** (`alpha -> List alpha`): after Phase 1 / Simplified Reduction, each agent has a list of remaining acceptable partners in preference order. Irving's rotation is defined on this table (Irving 1985, Def 2.5):

```
(p_0, q_0), ..., (p_{r-1}, q_{r-1})
where  q_i = second(p_i)  and  p_{i+1 mod r} = last(q_i)
```

The hedonic algorithm's move-on mechanism traverses the same second-to-last chain: forcing `p_0` to propose `second(p_0)` triggers a rejection cascade that follows the rotation. Both identify the same cycle and eliminate the same pairs.

Key insight: the `first(b) = a iff last(a) = b` duality of the Phase 1 table means the second-to-last chain is uniquely determined by the reduced table. Both algorithms simply traverse it.

### What remains

1. **Full algorithmic correspondence**: formalize `AlgState` (reduced preference lists + loop invariants) to show that the hedonic algorithm's `process` function (Algorithm 3) and Irving's Phase 2 produce the same sequence of `eliminateRotation` calls. This is the deepest remaining piece — it's an induction over the iterated reduction process.

## AXLE Workflow

[AXLE](https://axiommath.ai/) (`axle`) provides remote Lean 4 type-checking and proof tooling against a hosted Mathlib environment. This is useful for this project because:

- **Fast iteration without local Mathlib builds.** Mathlib is large (16k+ files). AXLE checks against a pre-built environment, so `make check` runs in seconds rather than the minutes-to-hours a cold `lake build` takes. This makes it practical to iterate on proof attempts without waiting for recompilation.
- **Proof stress-testing.** `make disprove` attempts to prove the *negation* of each theorem. "Failed to disprove" is positive evidence of correctness; "disproved" means a claim is wrong and should be revised. This caught issues in earlier iterations of the formalization.
- **Automated repair.** `make repair` tries terminal tactics (`grind`, `simp`, `omega`, `decide`) on open goals. Useful for closing routine subgoals without manual tactic engineering.
- **Sorry extraction.** `make sorry2lemma` extracts each `sorry` as a standalone lemma with its exact proof obligations, making the remaining work explicit.

Install: `uv tool install axiom-axle`

### Make Targets

**Checking** (type-check via AXLE remote environment):
```
make check               type-check Defs + GaleShapley + Irving
make check-defs          check HedonicGrouping/Defs.lean only
make check-gs            check HedonicGrouping/GaleShapley.lean only
make check-irving        check HedonicGrouping/Irving.lean only
make check-strict        same, but exit non-zero on any sorry
```

**Stress-testing** (proof-by-negation):
```
make disprove            run disprove on GaleShapley + Irving
make disprove-gs         disprove GaleShapley only
make disprove-irving     disprove Irving only
make disprove TIMEOUT=300  longer timeout for hard goals
```

**Proof development**:
```
make sorry2lemma         extract open sorrys as standalone lemmas
make sorry2lemma FILE=HedonicGrouping/Irving.lean NAMES=foo  target specific theorem
make repair              attempt auto-repair on default file (Irving)
make repair FILE=HedonicGrouping/Irving.lean NAMES=rotation_eliminates_less_preferred
```

**Finalizing**:
```
make simplify            clean up proofs in GaleShapley + Irving
make extract             split into per-theorem files -> HedonicGrouping/extracted/
make extract EXTRACT_DIR=/tmp/artifact  use a different output dir
```

**Diagnostics**:
```
make lean-version        show lean, lake, axle versions + available envs
```

AXLE environment: `lean-4.28.0` (Lean 4.28.0 + Mathlib). Local toolchain: `leanprover/lean4:v4.29.0-rc6`.

## Building

```
lake build
```

Requires Lean 4 + Mathlib. Toolchain managed by `elan`.

## Running Python Tests

```
python -m src.test_algorithms
```

Runs Gale-Shapley, Irving, and hedonic grouping tests including Monte Carlo validation and cross-algorithm consistency checks.

## Remaining Work

### Critical
- Full algorithmic correspondence via `AlgState` (iterated reduction induction)
- Tighten Lemma 1 and 2 proof prose in the paper

### For full paper
- Complexity analysis: formal Big-O treatment, honest framing of exponential worst-case
- Monte Carlo experiments at larger scale (n = 10-20)
- Formal theorem numbering with proof environments
- Language polish

## Target Venues

- **Workshop** (first): MATCH-UP or COMSOC extended abstract — current content is sufficient
- **Full paper**: SAGT (algorithmic game theory, 12-page limit, values clean theoretical results)
