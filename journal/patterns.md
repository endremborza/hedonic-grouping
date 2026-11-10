# Patterns

These are interpretations. Each one rests on failures (F) in `retrospective.md` and entries (J) in `log.md`, and it changes only when an entry supports or contradicts it.

**P1 The check that passed was not the check that mattered.** Every false or empty result passed a real check: a per-file kernel check, a sorry count, soundness-only tests, and `disprove` finding no counterexample to a function it cannot evaluate. The missing check was always about the statement, not about its proof. Brute force over a statement's own hypothesis class found both false theorems in minutes. (F2, F3, F7; J1)

**P2 A wrong definition gets patched downstream.** One vacuous definition produced three patches over four months, and none of them touched the definition itself. Patching a consumer looks like a unit of progress. Changing a definition is a decision, and the loop forbade asking for one. (F1, F7)

**P3 Formalizing ahead of a paper proof means inventing the invariants in Lean.** With only a sketch to formalize, each unit had to discover its invariant and engineer its proof at the same time. A false invariant then cost a rebuild instead of a counterexample on paper. (F3, F6)

**P4 An unattended loop grows what it can verify locally.** The largest growth happened off the critical path while the central statement stayed open. The guardrails were written as prose, and prose did not stop it. (F4, F7)

**P5 Written agent claims turn into evidence.** A comment claimed confirmation by a Lean proof that did not exist, and dated narratives replaced the current state in the README. The interactive agent of J1 to J3 also made claims it later had to revise. (F5; J1, J3)

**P6 Everyone trusted the thesis, including the agents.** The agents formalized and patched the thesis's claims but never tested them, although testing took minutes once someone tried. (F6; J1)

**P7 Output outran review.** Each checkpoint commit carried thousands of agent-written lines, and nothing marked the few that needed human judgement. (F8)

**P8 Executability made falsity cheap to show.** Because HCF's Lean `step` is computable, the counterexamples to the false theorems were run through the formalized transition function itself, via the fuel-bounded CLI, and not only through the Python oracle. (J1)
