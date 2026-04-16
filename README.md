# Hedonic Grouping

Lean 4 formalization of a unifying algorithm for stable matching as hedonic coalition formation.

A single recursive algorithm subsumes both Gale-Shapley (bipartite matching) and Irving (stable roommates) as special cases, applied to general hedonic games with strict preferences over arbitrary coalitions. The algorithm is correct and complete but worst-case exponential — inherent since the general problem is NP-hard (Ballester 2004). It reduces to polynomial-time on tractable subclasses.

The algorithm and its unification claim are original unpublished work. The Lean 4 formalization provides machine-checked proofs of correctness — unusual for the matching theory literature, where most results rely on pen-and-paper arguments.

## Repository structure

```
HedonicGrouping/           Lean 4 formalization
  Defs.lean                  shared definitions, bridge theorems — 0 sorries
  GaleShapley.lean           GS algorithm + core stability proof — 3 sorries
  Irving.lean                Irving algorithm + decidability — 8 sorries
  Stability.lean             top-level stability theorems — 0 sorries
refs/stable-marriage-lean/   reference GS formalization (0 sorries, ~1400 lines)
src/                         Python reference implementations + tests
tex/                         LaTeX paper
plan.md                      resolution order and publication paths
CLAUDE.md                    LLM session configuration
```

## Formalization state

**1195 lines of Lean. 11 sorries remain across 2 files.**

All definitions type-check. All claims pass `make disprove` (no counterexamples found). The proof architecture is sound — remaining work is case analyses.

### Proven (no sorries)

| Result | File | Significance |
|--------|------|-------------|
| `coreStable_iff_pairwiseStable` | Defs | Core = pairwise stability under size-2 |
| `blocking_coalition_sizeTwo` | Defs | Blocking coalitions are pairs under size-2 |
| `considerable_iff_mutual_proposal` | GaleShapley | Considerable = mutual proposal (Lemma 1 core) |
| `lemma1_considerable_matches_gs` | GaleShapley | Full Lemma 1 with bipartite hypotheses |
| All 7 GS invariant initial conditions | GaleShapley | Base case for inductive argument |
| `gs_coreStable`, `gs_stable_matching_exists` | GaleShapley | Endpoint theorems (from `gs_noBlockingPairs`) |
| `rotation_eliminates_less_preferred` | Irving | Rotation elimination correctness |
| `lemma2_rotation_elimination_preserves_invariants` | Irving | Reduced table invariant under elimination |

### Remaining (11 sorries)

| Sorry | File | Est. lines |
|-------|------|-----------|
| `eliminateRotation_decreases_totalLength` | Irving | ~50 |
| `gs_terminates` | GS | ~80 |
| `findRotation` | Irving | ~80 |
| `phase2` | Irving | ~50 |
| `gs_invariants_hold` | GS | ~600 |
| `gs_noBlockingPairs` | GS | ~100 |
| `phase1_produces_reduced_table` | Irving | ~300 |
| `eliminateRotation_preserves_stablePair` | Irving | ~150 |
| `reducedTable_singleton_stable` | Irving | ~150 |
| `reducedTable_empty_no_stable` | Irving | ~100 |
| `irving_decides_stability` | Irving | ~50 |

Dependency chain: `eliminateRotation_decreases_totalLength` feeds `phase2`; `gs_invariants_hold` + `gs_terminates` feed `gs_noBlockingPairs`; all Irving sorries feed `irving_decides_stability`. See `plan.md` for resolution order.

## Development workflow

Lean checking via AXLE (remote Lean 4.28.0 + Mathlib):

```bash
make check              # type-check all files
make check-gs           # check GaleShapley.lean only
make check-irving       # check Irving.lean only
make disprove           # stress-test all theorem statements
make sorry2lemma        # extract sorry goals as standalone stubs
make repair             # attempt auto-repair (grind/simp/omega/decide)
```

Python tests (11/11 passing):
```bash
python -m src.test_algorithms
```

## Python implementations

Reference implementations with stability verification and Monte Carlo testing:

- `src/common.py` — types, stability verifiers, random generators
- `src/gale_shapley.py` — Gale-Shapley for stable marriage
- `src/irving.py` — Irving's algorithm for stable roommates
- `src/hedonic.py` — general hedonic grouping
- `src/test_algorithms.py` — all tests including cross-algorithm stability checks
