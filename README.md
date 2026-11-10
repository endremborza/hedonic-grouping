# Hedonic Grouping

HCF (hedonic coalition formation) is an algorithm for core-stable partitions when every agent ranks an explicit list of coalitions. The problem is also studied as stable hypergraph matching. Deciding whether a core-stable partition exists is NP-complete for this representation (Ballester 2004), so HCF is exponential in the worst case.

This repository has two parts:

- **The project** aims at one result: HCF decides core stability for explicit coalition lists; it is verified in Lean 4 to terminate and to be sound and complete; and it specialises to Irving's algorithm on stable roommates and to Gale–Shapley on stable marriage. The Lean formalization lives in `HedonicGrouping/`, the Python oracle in `src/`, and the paper in `tex/`.
- **The journal** in `journal/` records how that work is divided between the author and AI agents: who proposed each step, who did it, what checked it, and what the author read. It begins with a retrospective of seven months in which agents wrote most of the Lean, and two of its three open headline theorems turned out to be false.

## Current state

**3 sorries across 3 files.**

| Statement | File | Status |
| --- | --- | --- |
| HCF's `step` is computable; `hcfGrouping` iterates it to termination along a well-founded measure (`slackMeasure_step_lt`) | `Algorithms/HCF.lean` | proved |
| the CLI's fuel-bounded iteration of `step` (`runFuel`) agrees with `hcfGrouping` | `Algorithms/HCF.lean` | not stated |
| GS's output is pairwise stable (`gs_pairwiseStable`) | `Algorithms/GaleShapley.lean` | proved |
| `hcf_coreStable`: a returned grouping is core-stable | `Algorithms/HCF.lean` | sorry |
| completeness: `none` only when no core-stable partition exists | – | not stated |
| `hcf_subsumes_gs` | `Correctness/HCF_subsumes_GS.lean` | sorry; false as stated (counterexample in `journal/log.md`, J1) |
| `hcf_subsumes_irv` | `Correctness/HCF_subsumes_IRV.lean` | sorry; false as stated (counterexample in J1) |
| `gs_solves_smp`, `irving_decides_rmp` | `Correctness/GS_SMP.lean`, `Correctness/IRV_RMP.lean` | proved, but trivial: `CoreStable` holds for the all-singletons grouping on every size-2 profile |
| eliminating a rotation preserves solvability (`solvableInTable_step`) | `Algorithms/Irving.lean` | proved; this Irving is noncomputable, and its headline theorem is trivial for the reason above |

The Python oracle agrees with brute-force enumeration of all partitions on every tested domain in which each listed coalition is listed by all of its members (J1).

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
    HCF.lean                         HCF state machine, well-founded run, termination
  Correctness/
    GS_SMP.lean                      gs_solves_smp (via size-2 bridge)
    IRV_RMP.lean                     irving_decides_rmp (via size-2 bridge)
    HCF_HCP.lean                     hcf_solves_{hcp,smp,rmp}, soundness compositions over hcf_coreStable
    HCF_subsumes_GS.lean             hcf_subsumes_gs
    HCF_subsumes_IRV.lean            hcf_subsumes_irv
  Unification.lean                   size-2 bridges, isSMP/RMP_to_isHCP
  Summary.lean                       top-level re-exports
  Exec.lean                          executable CLI glue (JSON ↔ Fin n, runFuel driver)
Main.lean                            CLI entry point: lake exe hedonic-grouping
journal/                             how the work is done: protocol, log, retrospective, patterns, evidence
src/                                 Python reference implementations + tests
tex/                                 LaTeX paper
```

HCF is computable. `make build` compiles a `hedonic-grouping` executable that reads a JSON instance on stdin (`{"agents":[…],"prefs":{…}}`) and prints the resulting grouping, or `null`, so its output can be compared directly with the Python oracle.

## Development workflow

Lean checking goes through AXLE (axiommath.ai, remote Lean 4.28.0 + Mathlib). AXLE only accepts `import Mathlib`, so per-file checks concatenate each target with its `HedonicGrouping.*` dependencies via `scripts/concat_imports.py`.

```bash
make check                                  # type-check every leaf file
make check-one FILE=HedonicGrouping/...     # check one file and its deps
make disprove                               # stress-test theorem statements
make sorry2lemma FILE=... NAMES=...         # extract sorry goals as stubs
make repair FILE=... NAMES=...              # auto-repair attempts
```

`disprove` cannot evaluate HCF's well-founded run, so it says nothing about statements involving `hcfGrouping`.

Python tests (pytest, `.venv` managed by `uv`):

```bash
.venv/bin/pytest         # or `make python-check`
```

Executable and differential check (local Lean build, not AXLE):

```bash
make build               # compile the hedonic-grouping CLI
make diff                # build, then assert Lean output == Python oracle
```

## Python implementations

Reference implementations exercised by a pytest suite. The preference generators drive most of the coverage: exhaustive at small n, random samples above.

- `src/common.py`: types and stability verifiers
- `src/generators.py`: SMP/RMP/HCP preference generators (`random_*`, `enumerate_*`, cap-aware `profiles_*`)
- `src/gale_shapley.py`: Gale–Shapley for stable marriage
- `src/irving.py`: Irving's algorithm for stable roommates
- `src/hedonic.py`: general hedonic grouping (recursive and iterative)
- `src/tests/`: pytest suite with edge-case fixtures, generated coverage per algorithm, cross-algorithm checks, and a Lean-vs-Python executable parity check (skipped without a `make build`)
