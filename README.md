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
is proved correct on SMP directly; IRV's correctness on RMP is in
progress (see Formalization state). The unification
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
  Exec.lean                          executable CLI glue (JSON ↔ Fin n, runFuel driver)
Main.lean                            CLI entry point: lake exe hedonic-grouping
refs/stable-marriage-lean/           reference GS formalization (0 sorries)
src/                                 Python reference implementations + tests
tex/                                 LaTeX paper
```

The HCF algorithm is computable: `make build` compiles a `hedonic-grouping`
executable that reads a JSON instance on stdin
(`{"agents":[…],"prefs":{…}}`) and prints the resulting grouping (or
`null`), enabling direct comparison against the Python reference.

## Formalization state

**4 sorries across 4 files.** AXLE `disprove` finds no counterexample to the
open statements within the timeout, but that is only weak evidence where the
goal shape defeats `grind`: `hcf_coreStable` is in fact unprovable while
`hcfGrouping` remains the `fun a => {a}` stub (below).

**Irving Phase 2 — existential solvability (corrected 2026-06-23).** Phase 2's
correctness was originally staked on `StableMatchingsSurvive` — that rotation
elimination never deletes a pair of *any* pairwise-stable matching. That claim
is **false**: on the canonical two-stable-matching instance
(`p0:[q1,q0] p1:[q0,q1] q0:[p0,p1] q1:[p1,p0]`), Phase 1 yields the dual table
and eliminating the exposed rotation `[(p0,q0),(p1,q1)]` deletes exactly the
pairs `{p0,q1}`/`{p1,q0}` — *precisely* the pairs of the other stable matching
(verified against the Python oracle). Rotation elimination is *meant* to discard
stable matchings, so per-step universal survival cannot hold. Phase 2 is
therefore threaded through the **existential** invariant `SolvableInTable` (the
table still admits *some* surviving stable matching) rather than universal
survival: `phase2` now concludes "reduces to an all-singleton stable matching,
or the table is not solvable", and the negative branch of
`irving_decides_stability` is sound — it consumes the true existential crux,
seeded from Phase 1's (still true) `StableMatchingsSurvive` via
`solvableInTable_of_survive`. The single open Phase-2 `sorry` is now the
standard, provable crux `solvableInTable_step` (existential solvability is
preserved by a step; witness: the rotation-shifted matching). The duality
machinery (`Phase1Duality`, the `_reduce`/`reduceTable` mirror,
`isRotation_no_selfLoop`, `rotationCycle_length_ge_2_of_dual`) is sound and
reused.

Negative stability conclusions quantify over genuine pair matchings
(`Core.IsPairMatching`: every coalition is a ranked pair, partners
agree). Bare `PairwiseStable`/`CoreStable` are vacuously satisfiable —
`Ranks` only compares ranked coalitions, so groupings built from
unranked coalitions (e.g. all-singletons under a size-2 profile) admit
no blocking pair.

| File | Sorries | Notes |
|---|---:|---|
| `Algorithms/Irving.lean` | 1 | Existential-solvability step (`solvableInTable_step`) |
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

Executable + differential check (local Lean build, not AXLE):

```bash
make build               # compile the hedonic-grouping CLI
make diff                # build, then assert Lean output == Python oracle
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
  coverage per algorithm, cross-algorithm checks, and a Lean-vs-Python
  executable parity check (skipped without a `make build`)
