# DECISIONS -- control panel

Read by the cadence (`make progress` / `make compact`). Holds the goals, the decisions (one line each) and the Current focus. The how -- proof plans, method -- lives in `ideas.md`; current state (sorry table, structure) in `README.md`.

## Goals (owner)

- Executable Lean GS, IRV and HCF (HCF done; GS/IRV: D7).
- Prove, of these executables: (1) what the GS and Irving papers establish (done); (2) the thesis -- on the same setup, HCF carries every guarantee GS has on SMP and Irving has on RMP (D1); (3) the general HCP properties of HCF: soundness + completeness.
- Deferred: CAP, referenced in the paper; GS-on-CAP proofs later (D5).

## Decisions

- D1 "subsumes" = guarantee subsumption: every guarantee the repo proves for GS/IRV holds of HCF's own output on the embedded instance. Not bare existence (satisfiable without HCF), not trajectory equivalence (optional, unscheduled). The guarantee set tracks what the repo proves: a stronger GS/IRV guarantee landing later (e.g. proposer-optimality) makes an HCF analogue owed or explicitly scoped out.
- D2 statement shape: `hcfGrouping : Option (Grouping α)` from the WF `run`; `hcf_coreStable` is partial correctness; subsumption in always-succeeds (SMP) / decides (RMP) shapes.
- D5 CAP: finish the three-problem unification first.
- D7 **open (owner)** -- executable GS/IRV too? Only HCF is computable (GS is Prop-based, Irving iterates `Classical.choose`). HCF-only (status quo) vs. computable GS/IRV (revert the Prop choices, computable search). Does not block the critical path.
- D9 **open (owner)** -- item 11's predicate: the HCP analogue of `IsPairMatching` ("genuine ranked grouping") that `hcf_complete` and `hcf_subsumes_irv`'s negative branch quantify over; or scope item 11 to size-2 profiles over `IsPairMatching`. Formalizing item 11 waits on it.

## Critical path

```
hcfGrouping : Option (Grouping α)         WF HCFState.run, in tree
|- 10 hcf_coreStable    some g -> CoreStable prof g      sorry, FOCUS
|- 11 hcf_complete      solvable -> some                  not stated yet, needs D9
|- 12 hcf_subsumes_gs   always succeeds on SMP            sorry, needs 10 + 11
`- 12 hcf_subsumes_irv  decides on RMP                    sorry, needs 10 + 11
```

## Current focus  <- the cadence reads this

FOCUS: item 10, `hcf_coreStable` soundness. The probe is done and the proof architecture fixed: execute the five-brick plan in `ideas.md` "Item 10". Item 11 waits on D9; item 12 composes after 10 + 11. Keep the README sorry table in sync per unit.
