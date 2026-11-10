# Retrospective: March to October 2026

This account was reconstructed in October 2026, after the fact, from three sources: this repository's git history (64 commits, 2026-03-15 to 2026-10-14), the history of the owner's planning notes (kept in a private repository, cited by date), and the snapshots in `evidence/`. The session transcripts from the period no longer exist, because Claude Code deletes transcripts after 30 days by default.

Attribution is known only roughly. By the owner's account, the thesis (`tex/`, written before this repository) and the Python oracle are theirs, and "a lot of LLM work went on here". Agents wrote most of the Lean and all of the planning notes. The owner made every commit, so commit authorship says nothing about who wrote a change. Where this matters, an item says "author unknown".

## Timeline

Lean lines count every tracked `.lean` file. Sorries count `sorry` tokens outside comments.

| Period | Commits | What changed | Lean lines | Sorries |
| --- | --- | --- | --: | --: |
| 03-15 – 03-22 | 232c8c0 – 061502c | Thesis imported. First Lean definitions (898577f), Python oracle added. | 0 → 556 | 0 |
| 03-27 – 04-30 | 35948e3 – f30dc7d | Three-algorithm layout: `Irving.lean` and `GaleShapley.lean` appear (1d87516). | 556 → 1,021 | 0 → 11 |
| 05-10 – 05-15 | caaf3d8 – 2c4049a | `HCF.lean` appears, with `hcf_coreStable` stated about a placeholder grouping (387103e). The oracle gains `solve_iterative` to mirror the Lean state machine. | 1,021 → 1,642 | 10 → 26 |
| 05-17 – 06-25 | 287d989 – f2bc509 | Repeated agent runs on the sorries, driven by the `progress-with-sorries` skill (directory dated 05-19); the planning notes' progress log starts 05-31. One commit, f2bc509, takes `Irving.lean` from 630 to 3,411 lines. | 1,642 → 5,104 | 26 → 4 |
| 06-26 – 10-14 | 1192b56 | HCF termination (`HCFState.run`, `slackMeasure_step_lt`). The subsumption theorems are restated. Everything lands in one checkpoint commit on 10-14. The planning notes add the decision index (D1 on 07-02, D9 on 09-01) and the hourly unattended schedule (09-02). | 5,104 → 6,153 | 4 → 3 |

## Failures

**F1 Vacuous stability.** `Ranks` (`Core.lean`) compares only coalitions on the agent's own list. `BlockingCoalition` (`Problems/HCP.lean`) requires `S.card ≥ 2`. Both date from the first Lean commits (898577f and 5be092e, 2026-03-21; author unknown).
- **Effect:** an agent assigned a coalition it does not list can never block, so the all-singletons grouping is `CoreStable` on every size-2 profile. `gs_solves_smp` and `irving_decides_rmp` therefore hold with no algorithm at all.
- **Response:** the definitions were never changed. Three patches appeared downstream instead:
  - `IsPairMatching` (f2bc509);
  - an open decision, D9, on a "genuine grouping" predicate (planning notes, 2026-09-01);
  - an open hole named "vacuous positive statements" (`evidence/ideas.md`).
- **Caught:** diagnosed as a single definition in J1.

**F2 False headline statements.** `hcf_subsumes_gs` and `hcf_subsumes_irv` are false in their committed form (1192b56). `IsSMP` and `IsRMP` admit empty, incomplete and asymmetric lists. On such lists HCF returns `none` even though a stable matching exists (counterexamples in J1). Three checks passed them:
- **The oracle tests:** the generators produce only complete, mutually listed profiles, and the tests check only that a returned grouping is stable.
- **AXLE `disprove`:** it cannot evaluate the well-founded `HCFState.run`, so it finds no counterexample.
- **The per-file kernel check:** a sorry is not an error.

They were caught in J1 by brute force over the statements' own hypothesis class.

**F3 Invariants formalized before they were true.**
- **`StableMatchingsSurvive`:** rotation elimination never deletes a pair of any stable matching. It carried Irving's phase 2 until a 2×2 instance refuted it. The README at f2bc509 records the rebuild around an existential invariant ("corrected 2026-06-23").
- **Further cases:** the agents' memory notes (outside git, self-reported) record further false claims of the same kind, among them a rotation witness `q_i ↦ p_{i+1}` (the correct one is `q_i ↦ p_i`) and a disjunctive invariant `RemovedLessPreferred`.
- **Why:** the thesis's correctness argument is a sketch (F6), so each Lean unit had to invent its own invariant.

**F4 Growth off the critical path.**
- **The growth:** f2bc509 grows `Irving.lean` from 630 to 3,411 lines. At 1192b56 it is 3,539 of 6,153 Lean lines.
- **What it holds:** its headline theorem `irving_decides_stability` is trivial by F1. Its real content is `solvableInTable_step`: eliminating a rotation preserves solvability.
- **The redefinition:** on 2026-07-02 the planning notes replaced the paper's outcome equivalence with "guarantee subsumption" (D1, `evidence/decisions.md`). Under D1, HCF's guarantees on SMP and RMP follow from HCF's own soundness and completeness, so the headline needs no Irving formalization.
- **The center:** the central soundness statement `hcf_coreStable`, stated on 2026-05-11, is still open.

**F5 Self-reports that became evidence.**
- **The oracle comment:** f2bc509 adds a comment to the oracle where a complete phase-1 partition is accepted. It says the partition "is already core-stable ... (confirmed against the Lean formalization)". In the same commit, Lean's `hcfGrouping` is the placeholder `fun a => {a}` and `hcf_coreStable` is a sorry.
- **The README:** it carried dated narratives of corrections instead of the current state.

**F6 Thesis gaps that nobody tested.** Brute force in J1 found four gaps in the thesis:
- **Staying alone:** a singleton proposal is never received, so it never cuts anything. On full lists with singletons at n=4, 1,152 of 2,000 outputs violate the paper's group stability.
- **Inconsistent lists:** where a coalition is listed by only some of its members, HCF misses existing solutions, on 197 of 3,000 profiles at n=4.
- **`lem:gs` is false as stated:** with men ordered first, HCF returns the woman-optimal matching. That differs from the claimed man-optimal one on 12,576 of the 46,656 profiles at n=3.
- **Correctness:** the correctness argument is a sketch.

For seven months agents formalized the thesis's claims as stated. None was tested against brute force until J1, where testing took minutes.

**F7 The loop's incentives.**
- **The prompt:** the progress prompt (`evidence/progress-prompt.md`) ran hourly and unattended from 2026-09-02. It asked for "one verified unit per run", forbade asking the owner anything, and gated each run on a per-file AXLE check plus `disprove`.
- **What went unchecked:** nothing in the loop checked that a top-level statement was true, or that the owner could review the output.
- **Guardrails:** they accumulated as prose (anti-bloat rules, a focus pointer, a ban on new files) rather than as checks.
- **The skill's own count:** "~73 additive-brick runs on a side-quest" (`evidence/progress-with-sorries-skill.md`).

**F8 Output outran review.** The owner: "A lot of LLM work went on here that I wanted to review but just really couldn't."
- **Scale:** each checkpoint commit carried thousands of agent-written Lean lines. f2bc509 has 3,433 insertions and 527 deletions in Lean files; 1192b56 has 1,200 and 151.
- **What went unmarked:** nothing set apart the small part that needed the owner's eyes, namely the definitions and the statements. F1 and F2 both lived there.
