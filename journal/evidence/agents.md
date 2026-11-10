# AGENTS.md — Hedonic Grouping

Lean 4 formalization of a novel HCF algorithm that unifies Gale-Shapley
and Irving. Python in `src/` is the testing oracle. The owner is Endre
Borza; agents are collaborators on proofs, definitions, and tooling.

`CLAUDE.md` is a symlink to this file. Local-only — neither file is
committed to git.

## Files and their roles

**Strict rule: no duplication between files.** Every fact lives in
exactly one place. Duplication is what got this project into stale-doc
fragmentation; do not reintroduce it.

- **`README.md`** — public, committed. Single source for current
  factual state: what the project is, repo structure, sorry counts,
  development workflow commands, Python implementation descriptions.
  May not reference `.cril/` or `AGENTS.md` (they don't ship with the
  repo).
- **`.cril/ideas.md`** — local-only, not in this repo's git (symlinked
  from a separate cross-repo intelligence layer). Single source for
  planning, decisions, strategy, TODOs, ideas, edited in place:
  architecture decisions, open holes, sorry resolution order, LLM
  session approach, publication paths, paper-side TODOs. A dated
  deadline block's checklist is the one exception: `.cril/todo.md`.
- **`AGENTS.md`** (and `CLAUDE.md` symlink) — local-only, not
  committed. Agent-facing operating rules: file roles, update
  protocol, Lean coding rules, project-wide "do not" list.
- **`.cril/DECISIONS.md`** — local-only. Thin owner-facing *control
  surface*: the critical-path graph, the open critical decisions
  (D1, D2, …), and the **Current focus** pointer that the `make
  progress` cadence reads. It is an index, **not** a second planning
  log — it links *into* `.cril/ideas.md` rather than copying. Detailed
  notes still live in `ideas.md`; once a decision is made, record the
  *why* in `ideas.md` and update the focus pointer here.

If you find yourself writing the same fact in two of these files,
stop. Pick the right home and delete the other copy.

## Where each kind of fact lives

| Kind of content | Home |
|---|---|
| What the project is, what it claims | `README.md` |
| Repo structure (file tree + descriptions) | `README.md` |
| Sorry counts and per-file totals | `README.md` |
| `make` targets and AXLE usage | `README.md` |
| Python file descriptions | `README.md` |
| Why a design choice was made | `.cril/ideas.md` |
| Open TODOs / specific things to fix | `.cril/ideas.md` |
| Sorry resolution order / dependencies (by name) | `.cril/ideas.md` |
| LLM session strategy, failure modes | `.cril/ideas.md` |
| Publication strategy and venue notes | `.cril/ideas.md` |
| Paper-side TODOs | `.cril/ideas.md` |
| Dated deadline block (release checklist) | `.cril/todo.md` |
| Agent operating rules, update protocol | `AGENTS.md` |
| Lean coding/style rules | `AGENTS.md` |
| Project-wide "do not" rules | `AGENTS.md` |

## Documentation update protocol

When you change code, update the relevant doc in the SAME response —
not in a follow-up turn, not in a separate commit. Use parallel tool
calls in one message so the doc and code are always coherent at any
point in git history.

Route updates by what changed:

- **Add or remove a `.lean` file.** Update the repo structure block in
  `README.md` AND add/remove the entry in `LEAF_FILES` in `Makefile`.
  If the change reflects an architecture decision, also note it in
  `.cril/ideas.md` (the *why*, not the *what*).
- **Add or close a `sorry`.** Update the sorry table in `README.md`
  (the count and per-file total). If the sorry is part of the
  resolution order, update `.cril/ideas.md` to remove the line
  entirely — don't strike it through, don't comment it out, don't add
  "DONE" markers.
- **Rename or remove a referenced symbol.** Grep both `README.md` and
  `.cril/ideas.md` for the old name; update or remove every mention
  in whichever file references it.
- **Architecture change.** Edit the "Architecture decisions" section
  of `.cril/ideas.md` in place: state the decision as it now stands and
  replace any decision it invalidates. No dated entries; git holds the
  history. Reflect
  in `README.md` only if it changes a fact the public sees (repo
  structure, what's proved, what's optional).
- **New TODO / open question / idea.** Goes to `.cril/ideas.md` (a
  deadline block's checklist item: `.cril/todo.md`). Never to `README.md`.

Don't:

- Leave a code change with stale doc as "I'll fix the doc next turn".
- Add aspirational TODOs to `README.md`. Public README states current
  facts only.
- Keep a planning log. `.cril/ideas.md` is the current plan, edited in
  place; the only log is `.cril/writeups/progress-log.md`, written by
  the `make progress` cadence and capped at its 10 newest entries.
  (`.cril/DECISIONS.md` is the thin decision/focus index described
  above — it points into `ideas.md`, never duplicates it.)
- Copy the same paragraph into two `.md` files "for convenience".

## Rules for Lean code

- **Naming (Mathlib style):** `snake_case` for theorems and lemmas;
  `camelCase` for defs, fields, and locals; `PascalCase` for
  predicates, structures, classes, and inductives. Predicate names
  inside freestanding theorem names are lowerCamelCased
  (`coreStable_iff_pairwiseStable`).
- **Layering:** algorithms depend only on `Core` and `Problems/`,
  never on `Problems/HCP` directly. `CoreStable` conclusions belong in
  `Correctness/`. **Exception:** `Algorithms/HCF.lean` operates on HCP
  natively and is allowed to import `Problems.HCP` and state
  `hcf_coreStable` in-place.
- Keep proofs close to the sorry they resolve — don't create new
  files for them.
- When a sorry needs helper lemmas, define them immediately above the
  sorry, in the same file.
- Preserve existing proof comments — they document intended strategy.
- If stuck after 3 attempts on a tactic, stop and explain the proof
  state. Don't keep stacking plausible-but-wrong tactic sequences.

## Do not

- Add docstrings, comments, or type annotations to code you didn't
  change.
- Create new files without asking.
- Modify the paper (`tex/`) without being asked.
- Commit (the owner handles git).
- Steer thesis-level decisions toward whichever claim is easiest to
  prove. When a fork concerns what the project *claims*, lay out the
  options neutrally — including the one that is hard to reach — and
  stop; reachability informs the owner's decision, it does not make it.
