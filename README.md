# Hedonic Grouping

Lean 4 formalization of a unifying algorithm for stable matching as hedonic coalition formation.

A single recursive algorithm subsumes both Gale-Shapley (bipartite matching) and Irving (stable roommates) as special cases, applied to general hedonic games with strict preferences over arbitrary coalitions. The algorithm is correct and complete but worst-case exponential — inherent since the general problem is NP-hard (Ballester 2004). It reduces to polynomial-time on tractable subclasses.

The algorithm and its unification claim are original unpublished work. The Lean 4 formalization provides machine-checked proofs of correctness — unusual for the matching theory literature, where most results rely on pen-and-paper arguments.

## Problems and algorithms

Three problems: **SMP** (stable marriage), **RMP** (stable roommates), **HCP** (hedonic coalition formation). CAP (college admissions) is deferred to a later phase.

Three algorithms: **GS** (Gale-Shapley), **IRV** (Irving), **HCF** (hedonic coalition formation — the novel algorithm). GS and IRV are proved correct directly on SMP and RMP. The unification (HCF subsumes GS/IRV; SMP/RMP embed in HCP) is a separate later layer — algorithms do not depend on that layer.

## Repository structure

```
HedonicGrouping/           Lean 4 formalization
  Core.lean                  shared types and pair utilities
  Problems/
    Pairwise.lean              BlockingPair, PairwiseStable (shared SMP/RMP)
    SMP.lean                   BipartiteStructure, IsSMP
    RMP.lean                   IsRMP
    HCP.lean                   Considerable, CoreStable, IsHCP
  Algorithms/
    GaleShapley.lean           GS state, step, run, invariants — 3 sorries
    Irving.lean                IRV phase 1, phase 2, rotations — 8 sorries
  Correctness/
    GS_SMP.lean                gs_solves_smp
    IRV_RMP.lean               irving_decides_rmp
  Unification.lean           size-2 and Considerable↔GS bridges
  Summary.lean               top-level re-exports
refs/stable-marriage-lean/ reference GS formalization (0 sorries, ~1400 lines)
src/                       Python reference implementations + tests
scripts/concat_imports.py  topo-sort deps for AXLE
tex/                       LaTeX paper
```

## Formalization state

**11 sorries remain, all in `Algorithms/GaleShapley.lean` and
`Algorithms/Irving.lean`.** Everything else is proven or trivially
delegates. All claims pass `make disprove`.

### Remaining sorries

| Sorry | File | Est. lines |
|-------|------|-----------|
| `eliminateRotation_decreases_totalLength` | Algorithms/Irving | ~50 |
| `gs_terminates` | Algorithms/GaleShapley | ~80 |
| `findRotation` | Algorithms/Irving | ~80 |
| `phase2` | Algorithms/Irving | ~50 |
| `gs_invariants_hold` | Algorithms/GaleShapley | ~600 |
| `gs_pairwiseStable` | Algorithms/GaleShapley | ~100 |
| `phase1_produces_reduced_table` | Algorithms/Irving | ~300 |
| `eliminateRotation_preserves_stablePair` | Algorithms/Irving | ~150 |
| `reducedTable_singleton_stable` | Algorithms/Irving | ~150 |
| `reducedTable_empty_no_stable` | Algorithms/Irving | ~100 |
| `irving_decides_stability` | Algorithms/Irving | ~50 |

## Roadmap

Phases are cumulative; each builds on the last.

2. **GS on SMP — 0 sorries.** Close `gs_terminates`, `gs_invariants_hold`, `gs_pairwiseStable`. Reference: `refs/stable-marriage-lean/`.
3. **IRV on RMP — 0 sorries.** Order: `eliminateRotation_decreases_totalLength`, `findRotation`, `phase2`, then `phase1_produces_reduced_table`, `eliminateRotation_preserves_stablePair`, `reducedTable_singleton_stable`, `reducedTable_empty_no_stable`, `irving_decides_stability`.
4. **SMP ⊂ HCP, RMP ⊂ HCP.** Embedding lemmas plus `coreStable_iff_pairwiseStable`. Reframes GS/IRV correctness as HCP-level corollaries.
5. **HCF on HCP.** Define and prove correct. Mirrors `src/hedonic.py`.
6. **Trajectory bridges.** `HCF-on-SMP-instance ≡ GS`, `HCF-on-RMP-instance ≡ IRV`. The paper's punchline.
7. **CAP.** Restore college-admissions infrastructure, define `IsCAP`, bridge.

## Development workflow

Lean checking via AXLE (remote Lean 4.28.0 + Mathlib). Per-file checks
concatenate each target with its dependencies via
`scripts/concat_imports.py` — AXLE only accepts `import Mathlib`.

```bash
make check                                  # type-check every leaf file
make check-one FILE=HedonicGrouping/...     # check one file and its deps
make disprove                               # stress-test theorem statements
make sorry2lemma FILE=... NAMES=...         # extract sorry goals as stubs
make repair FILE=... NAMES=...              # auto-repair attempts
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
