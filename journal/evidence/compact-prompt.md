You are running autonomously on this Lean 4 + Python repo. This is the **cleanup** pass, scored against the project goal (peer-review-quality Lean showing HCF subsumes GS and Irving). Read `.cril/DECISIONS.md` and `AGENTS.md` first.

Make the codebase more elegant, cleaner and better-abstracted, under one overriding constraint: **this pass must not grow the codebase**.

- **Net non-increasing.** End with the same or fewer lines than you started with. Deleting dead machinery, consolidating duplicated lemmas and tightening proofs are the goal; adding abstraction layers is not.
- **Prefer deletion.** Dead subtrees, superseded helpers and orphaned definitions first. `Irving.lean` (~3500 lines of accumulated bricks) is where this matters most: look for machinery no live theorem consumes.
- **No behavior or statement change.** Do not weaken or restate any theorem, do not touch sorry sites' meaning, do not add or remove sorries.
- **No new `.lean` files.** No new public API.

Verify every file you touch with `make check-one` (`okay:true`, zero non-sorry errors); if a cleanup can't be verified clean, revert it via Edit. Never commit, push, run git mutations, modify `tex/`, or ask the user anything.

Then compact the planning layer the same way:

- `.cril/ideas.md`: delete plan text for anything the tree now has (its as-built lives in `README.md` or the code) and any dated or narrative entry. Open holes, the focus's plan and method notes stay, tightened.
- `.cril/writeups/progress-log.md`: keep only the 10 newest entries.

Finally append one short dated entry to `.cril/writeups/progress-log.md`: what was removed or tightened and the net line change.
