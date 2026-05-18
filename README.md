# Hedonic Grouping

Lean 4 formalization of a unifying algorithm for stable matching as
hedonic coalition formation.

A single recursive algorithm (Hedonic Coalition Formation, HCF) subsumes
both Gale-Shapley (bipartite matching) and Irving (stable roommates) as
special cases, applied to general hedonic games with strict preferences
over arbitrary coalitions. The algorithm is correct and complete but
worst-case exponential — inherent since the general problem is NP-hard
(Ballester 2004). It reduces to polynomial time on tractable subclasses.

The algorithm and its unification claim are original unpublished work.
The Lean 4 formalization provides machine-checked proofs of correctness
— unusual for the matching theory literature, where most results rely
on pen-and-paper arguments.

## Problems and algorithms

Three problems: **SMP** (stable marriage), **RMP** (stable roommates),
**HCP** (hedonic coalition formation). CAP (college admissions) is
deferred.

Three algorithms: **GS** (Gale-Shapley), **IRV** (Irving), **HCF**. GS
and IRV are proved correct on SMP and RMP directly. The unification
(HCF subsumes GS/IRV; SMP/RMP embed in HCP) is a separate layer in
`Correctness/` — algorithms do not depend on it.

## Repository structure

```
HedonicGrouping/
  Core.lean                          shared types and pair utilities
  Problems/
    SMP.lean                         BipartiteStructure, IsSMP
    RMP.lean                         IsRMP
    HCP.lean                         Considerable, CoreStable, IsHCP
  Algorithms/
    GaleShapley.lean                 GS state, step, run, invariants
    Irving.lean                      IRV phase 1, phase 2, rotations
    HCF.lean                         HCF iterative form, frames, step
  Correctness/
    GS_SMP.lean                      gs_solves_smp (via size-2 bridge)
    IRV_RMP.lean                     irving_decides_rmp (via size-2 bridge)
    HCF_HCP.lean                     hcf_solves_{hcp,smp,rmp}
    HCF_subsumes_GS.lean             trajectory-equivalence stub
    HCF_subsumes_IRV.lean            trajectory-equivalence stub
  Unification.lean                   size-2 bridges, isSMP/RMP_to_isHCP
  Summary.lean                       top-level re-exports
refs/stable-marriage-lean/           reference GS formalization (0 sorries)
src/                                 Python reference implementations + tests
tex/                                 LaTeX paper
```

## Formalization state

**10 sorries across 4 files.** All claims pass `make disprove` (no
counterexamples found within the timeout).

| File | Sorries | Notes |
|---|---:|---|
| `Algorithms/Irving.lean` | 7 | Phase 1, Phase 2, endpoint theorems |
| `Algorithms/HCF.lean` | 1 | `hcf_coreStable`; blocked on HCF definitions |
| `Correctness/HCF_subsumes_GS.lean` | 1 | Optional trajectory-equivalence claim |
| `Correctness/HCF_subsumes_IRV.lean` | 1 | Optional trajectory-equivalence claim |

## Development workflow

Lean checking goes through AXLE (axiommath.ai, remote Lean 4.28.0 +
Mathlib). Per-file checks concatenate each target with its
`HedonicGrouping.*` dependencies via `scripts/concat_imports.py` —
AXLE only accepts `import Mathlib`.

```bash
make check                                  # type-check every leaf file
make check-one FILE=HedonicGrouping/...     # check one file and its deps
make disprove                               # stress-test theorem statements
make sorry2lemma FILE=... NAMES=...         # extract sorry goals as stubs
make repair FILE=... NAMES=...              # auto-repair attempts
```

Python tests (pytest, `.venv` managed by `uv`):

```bash
.venv/bin/pytest         # or `make python-check`
```

## Python implementations

Reference implementations exercised by a pytest suite. The
preference generator drives most of the coverage — exhaustive at
small n, random samples above.

- `src/common.py` — types and stability verifiers
- `src/generators.py` — SMP/RMP/HCP preference generators
  (`random_*`, `enumerate_*`, cap-aware `profiles_*`)
- `src/gale_shapley.py` — Gale-Shapley for stable marriage
- `src/irving.py` — Irving's algorithm for stable roommates
- `src/hedonic.py` — general hedonic grouping (recursive + iterative)
- `src/tests/` — pytest suite: edge-case fixtures plus generated
  coverage per algorithm and cross-algorithm checks
