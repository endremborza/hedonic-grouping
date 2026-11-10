# Log

Format and rules: `README.md` in this directory. J1 to J3 predate the journal; they were written up on 2026-10-21 from the session they happened in, Claude Code session 2647b6ab.

## J1 Reassessment

- Date: 2026-10-14
- Proposed by: owner ("Let's have an honest reassessment of it")
- Done by: agent (Claude Opus 5.5, Claude Code, interactive). It read `tex/main.tex`, `src/`, the Lean tree and the planning notes, and wrote brute-force probes in the session scratchpad. The probes were not kept; the instances and counts below reproduce them.
- Checks:
  - Brute force: every partition enumerated and compared with the oracle's `solve`, counting outputs that are unstable and `none` answers where a stable partition exists (– means not recorded):

    | Domain | Instances | Unsound | Missed a solution |
    | --- | --: | --: | --: |
    | full lists, n=3 exhaustive | 216 | 0 | 0 |
    | full lists, random n=4/5/6 | 3000/1500/300 | 0 | 0 |
    | coalitions globally feasible or not (symmetric), n=4/5/6 | 3000/1500/300 | 0 | 0 |
    | own truncation, then mutually normalized, n=4/5 | 3000/1500 | 0 | 0 |
    | individually rational lists (singletons included, normalized), n=4/5 | 3000/1500 | 0 | 0 |
    | full lists with singletons, n=4 | 2000 | 1152 | – |
    | the same with the singleton fix, n=4/5/6 | – | 0 | 0 |
    | coalitions listed by only some members, n=4 | 3000 | – | 197 |

  - `hcf_subsumes_gs` counterexamples, as an `IsSMP` profile. In one, a single agent has `prof m1 = []`. The other is `m1:[m1w1] m2:[m2w1] w1:[w1m1,w1m2]`. The Lean executable (`.lake/build/bin/hedonic-grouping`) prints `null` on both.
  - `hcf_subsumes_irv` counterexample (`13` is the coalition {a1, a3}): `a1:[13,14] a2:[12,24] a3:[23,13] a4:[24,14]`. `{13, 24}` is a core-stable pair matching, yet the Lean executable prints `null`. Random asymmetric profiles at n=4 and n=6 fail the same way on 817 of 6,000.
  - Side-first orders, SMP: the n=3 exhaustive set in both orders, and 1,600 random profiles at each of n=6, 9, 12. HCF returned the later side's optimum on every one. Interleaved orders returned intermediate stable matchings on 188 of 46,656 profiles at n=3 and on 213 of 1,500 at n=9.
  - Irving: HCF's matching equals the oracle's `irving` on 1,116 of 1,116 solvable random instances at n=4, 6, 8.
  - AXLE `make check`: 0 errors. The 3 sorries are `hcf_coreStable`, `hcf_subsumes_gs` and `hcf_subsumes_irv`.
- Owner read:
- Outcome: the oracle is sound and complete wherever every listed coalition is listed by all of its members. Two of the three open Lean statements are false (F2). `CoreStable` is vacuous (F1). The thesis has four gaps (F6). The side-first theorem replaces `lem:gs`: with one side ordered first, HCF returns the other side's optimal stable matching.
- Failures and surprises:
  - Agent: it framed its first report as a list of "Decisions I need". The owner rejected that framing ("no, not 'decisions I need' yes, just a conversation").
  - Agent: it proposed deleting `Irving.lean` as dead weight before J2 showed that the file holds the only machine-checked piece of Irving's correctness argument found anywhere.
  - Surprise: the thesis itself had gaps (F6), which no agent run had flagged in seven months.

## J2 Related work

- Date: 2026-10-14
- Proposed by: owner ("since I started this, others might have progressed")
- Done by: agent (a general-purpose subagent of the J1 session), tagging each item as read from the source or taken from an abstract or inference
- Checks: read from the source: Biró–Csáji–Schlotter (ICALP 2025) on stable hypergraph matching being essentially core stability in hedonic games; `hwatheod/galeshapley-lean`; `mmaaz-git/stable-marriage-lean`. Everything else comes from abstracts. The lead agent spot-checked only items it already knew.
- Owner read:
- Outcome:
  - The problem is studied as stable hypergraph matching.
  - Existence is NP-complete for explicit coalition lists (Ballester 2004).
  - "One algorithm solving marriage and roommates" is not new, because Irving's algorithm already solves marriage instances.
  - The closest prior work is Cechlárová and Hajduková (2004), whose preferences are derived from rankings of individuals.
  - No proof assistant has a formalization of Irving's algorithm or of stable roommates.
  - Neither the thesis nor any earlier planning note cites stable hypergraph matching or Cechlárová and Hajduková.
- Failures and surprises: this was the first literature check in the project. It changed the novelty claim (J3).

## J3 Target claim

- Date: 2026-10-14
- Proposed by: owner, as a draft: "An algorithm extending and subsuming Irving (and therefore GS), proven to be correct and executable in Lean 4"
- Done by: the agent pointed out three problems with the draft. "Therefore GS" does not follow. "Subsuming" needs a precise sense. "Correct" must include completeness, because a returned grouping's stability can be checked in time linear in the total list length. It then laid out three candidate claims (algorithmic, formal, both) and judged each on impact, publishability and achievability. The owner chose the combined one: "HCF decides core stability for explicit coalition lists, is verified in Lean 4 to terminate and to be sound and complete, and specialises to Irving on roommates and to Gale–Shapley on marriage."
- Checks: HCF recursion on random complete roommates instances, 200 per size at n=8 to 30 and 100 per size at n=50 and 80. HCF's solvability agreed with the oracle's `irving` on every instance. On solvable instances, child frames still failed: on average 0.1 (n=8) to 1.1 (n=80) times per instance, at most 4. No instance needed more than 10 recursive calls.
- Owner read:
- Outcome: the target claim above.
- Failures and surprises:
  - Agent: in J2's discussion it had named "step-for-step" specialisation as the defensible novelty. Its own probe then showed HCF matches Irving in outcome only. HCF forces the pivot itself off its proposal, while Irving eliminates the rotation the pivot leads to.
  - The agent's suggestion that completeness is a backtracking argument is not yet written out.
  - Whether HCF runs in polynomial time on roommates is open.

## J4 Journal and planning reset

- Date: 2026-10-21
- Proposed by: owner (the repository as a project plus a journal). The agent proposed the layout: a committed `journal/`, with planning kept in the private notes.
- Done by: agent (Claude Opus 5.5, Claude Code, interactive, the J1 session).
  - Wrote `journal/` and copied the retired agent instructions into `evidence/`.
  - Rewrote `README.md` and the local-only `AGENTS.md`.
  - Replaced the planning notes with a plan for the target claim and an ordered step list.
  - Removed the `progress`/`compact` make targets.
  - Raised Claude Code's transcript retention (`cleanupPeriodDays`).
  - Its deletion of the retired files was declined at the permission prompt, and is left to the owner: the progress and cleanup prompts, the `progress-with-sorries` skill, the decision index, the empty progress log, and the J1 reassessment notes, whose content now lives in this journal and the plan.
- Checks:
  - The retrospective's timeline numbers come from a script that runs `git ls-tree` and `git show` on every commit (session scratchpad).
  - Dates of symbols come from `git log -S`.
  - `make -n python-check build check-one FILE=x` parses.
  - A grep of `README.md`, `journal/`, `AGENTS.md` and the planning notes finds no remaining reference to the decision index, the progress log or `make progress`, apart from this entry.
- Owner read:
- Outcome: the repository is now a project aimed at the J3 claim, plus this journal. The next step is the first in the step list: testing that the Python version finds a solution whenever one exists.
- Failures and surprises:
  - The transcripts of the earlier agent runs are gone, so the retrospective rests on git, the planning notes' history and `evidence/`.
  - The scheduler that read the progress prompt's `every: 1h` header was not found: no crontab entry or systemd timer runs `make progress`. Until the prompt files are deleted, an unknown trigger could still run them.
  - The owner did not read J1 to J4 before committing them, citing their length and not yet knowing where the journal leads. That is F8 again, at the scale of this journal, so entries now have a length rule.
  - Agent correction to J1: the "Lean executable" there is the CLI. It iterates the same `step` under a fuel bound (`runFuel`), not `hcfGrouping` itself. That the two agree is not proved, and `README.md` now lists this as unstated.
