---
mode: repeat
unattended: true
profiles: opux
priority: 3
need: 35
every: 1h
target: the Current focus in .cril/DECISIONS.md
---
You are running autonomously on this Lean 4 + Python repo. The goal of the whole project is one thing: **show, in peer-review-quality Lean, that HCF subsumes Gale-Shapley and Irving.** Score everything against that, not against the raw sorry count.

# 1. Read

`.cril/DECISIONS.md` -- goals, decisions, and the **Current focus**, which names the ONE thing this run may advance. `.cril/ideas.md` -- the plan for the focus, open holes, method. `README.md` (sorry table) and `AGENTS.md` (operating rules).

# 2. Staleness pass first (always)

Gate on AXLE, not grep: run `make check-one` on any file you touch (never the full `make check`) and trust the README sorry table only after confirming it against the filesystem. Fix any genuinely stale doc in the same run. A hidden hard error can hide behind an intact sorry count: `okay:true` + zero non-sorry `lean_messages` errors is the bar.

# 3. Act on the focus, and ONLY the focus

- **Owner-blocked focus** (it names an open decision in DECISIONS.md): do not start new machinery on another sorry to "make progress". Do at most a staleness fix or a bounded cleanup from `compact.md`'s remit, then report the block and stop. Surfacing the blocking decision crisply is the valuable output.
- **Actionable focus**: make **one** verified unit of progress on it. Prefer consuming an open sorry over adding a helper next to it. A helper sorry is allowed only when it strictly enables the target, and it goes into the focus's plan in `ideas.md`.

# 4. Anti-bloat guardrails

- **No new `.lean` files** without explicit owner sign-off. Helpers go in the file with the sorry they serve.
- **Prefer consume / refactor / delete over add.** Factoring or deleting dead machinery in a large tangled file (`Irving.lean` is the example) beats one more lemma. Dead subtrees are removed, not preserved.
- **One verified unit per run.** Do not chain closures.
- Verify every new or edited claim with `make disprove-one` before trusting it; probe a load-bearing invariant or witness against the Python oracle *before* formalizing it.

# 5. Never

Commit, push, branch, reset, `git restore/checkout/clean`, `rm` tracked files, modify `tex/`, or ask the user a question. The owner handles all git and all decisions. If genuinely stuck or blocked, write the report and exit.

# 6. Record (keep the planning layer lean)

- `.cril/ideas.md`: edit the focus's plan in place -- delete what the unit fulfilled, tighten what it changed, add a new obligation where it belongs. Never append dated or narrative entries; a fact about the current tree goes to `README.md` (if public) or nowhere.
- `.cril/DECISIONS.md`: if the run changed what should happen next, rewrite the Current focus (a few lines). A newly surfaced owner question becomes a one-line open decision; nothing else goes there.
- `.cril/writeups/progress-log.md`: append one entry -- `## <datetime> -- <title>` plus one short paragraph: the question, decision or progress point of the run, and whether the sorry count moved or the run was additive / cleanup / blocked. Skip the entry when the run changed nothing and the newest entry already reports the same block. Then delete the oldest entries beyond the 10 newest (git keeps them).
