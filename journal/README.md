# Journal

This repository pursues one result, stated in the top-level `README.md`, and records how it gets produced. The journal is that record: who proposed each step, who did it, what checked it, and what the owner actually read. Its subject is how algorithm and proof work gets done when AI agents write most of the text.

## Files

- `retrospective.md`: the period before the journal existed (March to October 2026), reconstructed from git history and the snapshots in `evidence/`. It catalogues failures F1, F2, and so on.
- `log.md`: entries J1, J2, and so on, one per closed step, written when the step closes.
- `patterns.md`: interpretations. Each pattern cites the failures and entries that support it, and changes only when an entry does.
- `evidence/`: verbatim copies of the agent instructions and planning notes that drove the retrospective period, frozen on 2026-10-21 when they were retired. They are the hourly progress prompt, the cleanup prompt, the `progress-with-sorries` skill, the decision index, the planning notes, and the previous `AGENTS.md`. None of them was in git before.

## Roles

- **Owner:** Endre Borza, author of the thesis and the Python oracle. Decides what the project claims, reads definitions, theorem statements and paper proofs, and makes every commit.
- **Agents:** LLM sessions, with model and harness named in each entry. They draft code, proofs, probes and prose. They never commit and never run unattended.

## How a step runs

A step is one change with one purpose. It lands as one commit together with its journal entry.

Every mathematical claim climbs the same ladder:

1. **Statement.** Written in Lean, or in the paper for a claim that stays on paper. The owner reads it in full.
2. **Probe.** The Python oracle tests the statement over its own hypothesis class against brute-force enumeration of all partitions. The probe includes the edge cases: empty, incomplete and asymmetric lists, singletons, unequal sides. It checks `none` answers as well as returned groupings. The probe becomes a pytest test.
3. **Paper proof.** Written before any Lean proof. The owner reads it.
4. **Lean proof.** Accepted when AXLE `make check` reports no errors and `#print axioms` shows only the standard axioms. Nobody needs to read it.

The owner's review surface is therefore the definitions, the statements and the paper proofs. Lean proofs are trusted on the kernel. Nothing is trusted on an agent's word.

## Entry format

```
## J<n> <title>
- Date: <YYYY-MM-DD>
- Proposed by: <owner | agent (model, harness)>
- Done by: <who wrote what>
- Checks: <each check, the exact command or method, and its result>
- Owner read: <what the owner actually read; written by the owner>
- Outcome: <what changed, in one or two sentences>
- Failures and surprises: <what went wrong or was unexpected, the agent's own errors included; "none" if none>
```

An agent drafting an entry fills every field except "Owner read". It lists only checks it actually ran, and it quotes their results instead of calling them "verified". The owner writes "Owner read" before committing; left empty, it records that the owner did not read the entry. An entry is short enough to read in a minute; detail belongs in the diff, a test, or the retrospective, not in the entry. An entry's commit is the commit that adds it: `git log -- journal/log.md` maps entries to commits. Once committed, an entry is not edited. A correction goes into a later entry.

## Evidence standard

An agent's account of its own work is not evidence that the work is right. Such accounts include planning notes, progress logs, commit messages, and comments like "confirmed against the Lean formalization". Evidence is a diff, a command with its output, a counterexample, or a kernel check. The retrospective holds itself to the same standard and labels the owner's recollection as such.
