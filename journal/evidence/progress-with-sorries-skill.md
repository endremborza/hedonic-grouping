---
name: progress-with-sorries
description: Make ONE autonomous, verified unit of progress on the next open sorry in this Lean 4 hedonic-grouping repo. Reads `.cril/ideas.md` for the resolution order, picks the highest-priority actionable item, makes the change, verifies via AXLE (`make check-one` + `make disprove-one`), and updates docs. Never commits, never asks the user.
---

# /progress-with-sorries

You are running **autonomously**. Do not ask the user anything. Pick a target by rule, make the change, verify, update docs, stop.

## Workflow

### 1. Orient (parallel reads)

- `.cril/DECISIONS.md` — **Current focus** pointer (the authority on what to work on) and the open owner decisions.
- `README.md` — current sorry table.
- `.cril/ideas.md` — resolution order, open issues, decisions.
- `AGENTS.md` (or `CLAUDE.md`, same file) — operating rules.

### 2. Pick the target (focus-driven, not list-driven)

The target is whatever **Current focus** in `.cril/DECISIONS.md` names — *not*
"the next sorry in the resolution order". Mechanically grabbing the next
actionable sorry is what produced ~73 additive-brick runs on a side-quest.

- **If the focus is owner-blocked** (it points at an unanswered decision, e.g.
  D1/D2): **stop.** Do not start new machinery on some other sorry to manufacture
  progress. Write a short report naming the blocking decision and exit. That is
  the correct outcome, not a failure.
- **If the focus is actionable**: that is your target. Use the resolution order
  in `ideas.md` only to find the named sorry and its dependencies *within* the
  focus.

If the focused target is large (~150+ lines of expected proof), prefer one of these smaller units instead, in this order:

1. Define a missing helper function / type the sorry depends on, closing its termination obligations.
2. Extract named sub-lemmas above the sorry to shrink the obligation.
3. Close a single helper lemma that the sorry will consume.

Even then, prefer **consuming** the sorry over **adding** a helper beside it; an
additive helper is justified only when it strictly enables the focused target.

### 3. Inspect the goal

```
make sorry2lemma FILE=<file> NAMES=<sorry-name>
```

### 4. Attempt auto-repair

```
make repair FILE=<file> NAMES=<sorry-name>
```

If it closes the sorry and step 5 is clean, accept and ship.

### 5. Make manual progress

Edit the target `.lean` file. Constraints:

- Preserve existing proof comments (they document intended strategy).
- Naming follows Mathlib style: `snake_case` theorems, `camelCase` defs, `PascalCase` predicates / structures.
- Algorithms depend only on `Core` and `Problems/`, never on `Problems/HCP` directly (exception: `Algorithms/HCF.lean`).
- Keep helpers in the same file as the sorry they support.

**Stuck rule**: if 3 attempts at closing a single tactic goal fail, stop trying. Instead, factor the unresolved subgoal into a named lemma with its own `sorry` and a one-line proof outline. A smaller, named obligation is still clean progress.

### 6. Verify (hard gate)

```
make check-one FILE=<file>
```

Parse the JSON result; require `okay: true` and `lean_messages.errors == []`
(schema observed 2026-07-13: these fields are **top-level**, not under a
`result` key). `failed_declarations` may legitimately list known
sorry-carrying declarations — inspect it, don't hard-fail on it. The gate
must **fail closed**: missing or empty output (e.g. `make`/`axle` not on
PATH) is a FAIL, never a pass. Use this snippet:

```bash
make check-one FILE=<file> 2>&1 | python3 -c "
import sys, json, re
out = sys.stdin.read()
m = re.search(r'\{.*\}', out, re.DOTALL)
if not m:
    print('FAIL: no JSON in output (toolchain missing or crashed)')
    print(out[:400]); sys.exit(1)
res = json.loads(m.group())
res = res.get('result', res)  # tolerate either nesting
okay = res.get('okay')
errs = (res.get('lean_messages') or {}).get('errors', [])
print('OK' if okay is True and not errs else f'FAIL: okay={okay}, {len(errs)} errors')
for e in errs[:3]: print(str(e)[:400])
print('failed_declarations:', res.get('failed_declarations'))
"
```

If the toolchain is unavailable in the running environment, the unit is
**unverified**: do not claim verification in docs (mark the dated entry
"AXLE verification PENDING"), report the limitation, and stop.

Then stress-test any new claim:

```
make disprove-one FILE=<file>
```

Require 0 counterexamples on any theorem you introduced or modified.

If either gate fails, revert your edits (manually — do NOT `git restore` or `git checkout`) and either retry a smaller scope or stop and report.

### 7. Update docs (same turn, parallel tool calls)

Route by what changed:

- **Sorry count changed.** Edit the table in `README.md` — both the per-file row for the touched file and the total at the top. The total appears as `**N sorries across M files.**`.
- **Sorry closed.** Remove its line from the resolution order in `.cril/ideas.md` entirely. No strike-through, no "DONE" markers, no commented lines.
- **New sorry introduced as helper infrastructure.** Add it to the resolution order with a one-line description and which existing sorry it shrinks.
- **Architectural change.** Append a dated bullet to "Architecture decisions" in `.cril/ideas.md` (use the date in `currentDate` if available; otherwise today's date).

Never duplicate facts between `README.md` and `.cril/ideas.md`. The split is documented in `AGENTS.md` — respect it.

### 8. Report and stop

Write a terse summary (≤5 lines):

- Target sorry name and file.
- What changed (close / shrink / add infrastructure).
- New sorry totals (per-file + total).
- Suggested next target for the following invocation.

## Hard rules

- **Never commit, push, tag, force-push, reset, rebase, branch, or stash.** The repo owner handles all git mutations.
- **Never run `git restore`, `git checkout --`, `git clean`, or `rm` on tracked files.** If a change is bad, undo it via Edit/Write.
- **Never run the full `make check`** (slow, 14 files). Always `make check-one FILE=<one file>`.
- **Never ask the user a question.** Zero user intervention is the contract. If genuinely stuck, write a short report and exit.
- **Never modify `tex/`** (the paper).
- **One verified unit per invocation.** Don't chain sorry closures. Don't optimistically attempt more after the first verified change lands.
- **Net sorry budget**: the file you touched must end with `≤` the sorries it started with, UNLESS you introduced a new sorry that strictly enables shrinking an existing one (e.g., a named helper). In that case the *total* may go up by at most 1, but a corresponding entry must be added to the resolution order.
- **No new files without strong cause.** If creating a new `.lean` file feels needed, instead put the helper in the file with the consuming sorry.

## File roles (single source of truth)

- `README.md` — current factual state (sorry counts, repo structure, commands). Public, committed.
- `.cril/ideas.md` — planning, decisions, resolution order, dated notes. Local-only.
- `AGENTS.md` / `CLAUDE.md` (symlinked) — agent operating rules. Local-only.

If you find the same fact in two of these, fix the duplication.
