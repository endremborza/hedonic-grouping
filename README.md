# Hedonic Grouping

Lean 4 formalization of a unifying algorithm for stable matching as hedonic coalition formation.

## Core Claim

A single recursive algorithm subsumes both Gale-Shapley (bipartite matching) and Irving (stable roommates) as special cases, applied to general hedonic games with strict preferences over arbitrary coalitions. The algorithm is correct and complete but worst-case exponential — inherent since the general problem is NP-hard (Ballester 2004). It reduces to polynomial-time on tractable subclasses.

## Paper Structure

The accompanying paper (`tex/main.tex`) introduces a framework `<A, Omega, M>` for hedonic coalition formation:

- **Section 2 — Related Work**: Connects to hedonic games literature (Dreze & Greenberg, Bogomolnaia & Jackson, Banerjee et al., Ballester, Woeginger, Cechlarova & Romero-Medina, Alcalde & Revilla).
- **Section 3 — Framework**: Formal notation, reviews marriage/college admissions/roommates problems, defines group stability (= core stability).
- **Section 4 — Algorithms**: Simplified Reduction (considerable proposals), Processing (move-on chains, exceptions), Recursive Grouping. Worked 5-agent example.
- **Section 5 — Connections**: Lemma 1 (algorithm = Gale-Shapley under bipartite size-2), Lemma 2 (algorithm = Irving under non-bipartite size-2).

## Formalization State

### Defs.lean — Complete

`PreferenceProfile`, `Considerable`, `BlockingCoalition`, `CoreStable`, `SizeTwo`, validity predicates. Maps directly to the paper's `<A, Omega, M>` framework.

### Lemma1.lean — Complete (no sorries)

- `considerable_iff_mutual_proposal`: on size-2 pair {a,b}, considerable iff the other agent proposes it
- `considerable_eq_gsHolds`: considerable = GS "holds" relation
- `lemma1_considerable_matches_gs`: main statement with bipartite hypotheses

### Lemma2.lean — Two open sorries

- `RotationCycle`: cycle structure for Irving rotations (pairs of proposer + second-choice partner)
- `IsRotation`: standard Irving rotation defined on **reduced preference lists** — `q_i = second(p_i)`, `p_{i+1} = last(q_i)`. No proposal map; this is a property of the reduced table alone.
- `eliminatedPair`: pair eliminated at each cycle position (definitionally shared by both algorithms)
- `eliminateRotation`: applies Irving's rotation elimination to a reduced table
- `ReducedListCompatible`, `ReducedTableSymmetric`: invariants connecting reduced lists to the full preference profile
- **Sorry 1**: `rotation_eliminates_less_preferred` — each eliminated partner is strictly less preferred. Proof sketch is documented; requires connecting reduced-list positions to preference-profile rankings.
- **Sorry 2**: `cascade_produces_irving_elimination` — the hedonic cascade preserves the reduced-table invariants after rotation elimination. This is the main open result.

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

1. **Close sorry 1** (`rotation_eliminates_less_preferred`): straightforward once `ReducedListCompatible` + `ReducedTableSymmetric` are combined to locate `p_i` on `q_i`'s list before `p_{i+1}`.
2. **Close sorry 2** (`cascade_produces_irving_elimination`): show `eliminateRotation` preserves symmetry and compatibility. The symmetry preservation is the harder part — it requires showing that removing `{q_i, p_{i+1}}` doesn't break the `b in reduced(a) iff a in reduced(b)` invariant.
3. **Full algorithmic correspondence**: formalize `AlgState` (reduced preference lists + loop invariants) to show that the hedonic algorithm's `process` function (Algorithm 3) and Irving's Phase 2 produce the same sequence of `eliminateRotation` calls. This is the deepest remaining piece — it's an induction over the iterated reduction process.

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
make check               type-check Defs + Lemma1 + Lemma2
make check-defs          check HedonicGrouping/Defs.lean only
make check-lemma1        check HedonicGrouping/Lemma1.lean only
make check-lemma2        check HedonicGrouping/Lemma2.lean only
make check-strict        same, but exit non-zero on any sorry
```

**Stress-testing** (proof-by-negation):
```
make disprove            run disprove on Lemma1 + Lemma2
make disprove-lemma1     disprove Lemma1 only
make disprove-lemma2     disprove Lemma2 only
make disprove TIMEOUT=300  longer timeout for hard goals
```

**Proof development**:
```
make sorry2lemma         extract open sorrys as standalone lemmas
make sorry2lemma FILE=HedonicGrouping/Lemma2.lean NAMES=foo  target specific theorem
make repair              attempt auto-repair on default file (Lemma2)
make repair FILE=HedonicGrouping/Lemma2.lean NAMES=rotation_eliminates_less_preferred
```

**Finalizing**:
```
make simplify            clean up proofs in Lemma1 + Lemma2
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

## Remaining Work

### Critical
- Close the two sorries in Lemma 2 (see proof strategy above)
- Full algorithmic correspondence via `AlgState` (iterated reduction induction)
- Tighten Lemma 1 and 2 proof prose in the paper

### For full paper
- Complexity analysis: formal Big-O treatment, honest framing of exponential worst-case
- Python 3 implementation + Monte Carlo experiments (p = 5-20)
- Formal theorem numbering with proof environments
- Language polish

## Target Venues

- **Workshop** (first): MATCH-UP or COMSOC extended abstract — current content is sufficient
- **Full paper**: SAGT (algorithmic game theory, 12-page limit, values clean theoretical results)
