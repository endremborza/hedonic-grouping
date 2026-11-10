# hedonic-grouping -- ideas

Working plan for the open proofs, plus method and publication notes. Decisions and the Current focus: `DECISIONS.md`. Current state (structure, sorry table, commands): `README.md`. Edit in place: when a brick lands, delete the plan text it fulfilled; no dated entries, no run narratives (those go to `writeups/progress-log.md`).

## Architecture decisions

- Unification is at the conclusion level, not the state level: each algorithm keeps its own state type; subsumption composes problem containment (`Unification.lean`) with per-algorithm theorems.
- Lean-vs-Python parity: if it breaks, within-coalition set iteration is the one legitimate divergence axis.
- `.decide` accepts the first complete partition, with no explicit core-stability gate: the Considerable-cascade alone yields stability (empirical until item 10 closes; Python oracle has the same gate-free structure).

## Item 10 -- `hcf_coreStable` (focus)

Soundness is local. Oracle probe: exhaustive n=3 (216) + `random_hedonic(4, seed<300)` + `random_hedonic(5, seed<150)` = 666 instances, 0 violations on every claim below. The feared soundness/completeness entanglement does not exist: blockers killed only by child-failure eliminations (77) are all refuted by the pivot, so item 10 needs no exploration-soundness.

Validated invariants (probe names; state them against the Lean forms -- `receiveProposal`/`inProposals` use `Finset` bookkeeping, not Python's proposal list; the parity suite pins the two together):

- INV-BC (after every receive): every currently-considerable in-proposal coalition is the last element of the receiver's current preference list.
- OSP: surviving out-proposals are still listed (both lists are filtered by the same removals).
- PBU: every surviving proposed entry outranks every unproposed one.
- P0/P3 (acceptance): each agent still lists its assigned coalition, and its list ends there.
- P1 (acceptance): everything listed above `g a` was proposed.
- The cascade's `self` branch is unreachable under INV-BC: a held better considerable `B` is the list's last element, so a worse received `C` is no longer listed, hence not considerable.

Proof architecture (`BlockingCoalition` requires every member to `Ranks` both `S` and its assignment, which matches the probe):

- Auxiliary run invariants, a second bundle next to `HCFInv` or an extension of it: `PrefsSublist` (`preferences a` is a sublist of `prof a`, transferring rank comparisons to `Ranks`), OSP, PBU, INV-BC, and in-proposal completeness (proposers of a listed coalition accumulate and are never reset; `eliminate` clears only removed coalitions' in-proposals).
- `Dead z C := C not in prefs z and forall D in prefs z, D >_z C`. BlockerBarrier: for every coalition `C` ranked by all its members, either every member still lists `C`, or some `z in C` has `Dead z C`.
- Events: cascade-tail establishes `Dead receiver C` (after elimination the receiver's list ends at or above the held `B`, which it prefers to `C`). Child-failure establishes `Dead pivot C`: the pivot `z` is in `C` (`IsValidProfile`: lists hold only own coalitions, and `C` came from `z`'s list); the eliminated set is `z`'s unproposed remainder, strictly below its latest proposal `k` by PBU, so afterwards `z` lists only proposed entries `>= k`, and `g z >=_z k >_z C`. `self` is unreachable. `Dead` persists: lists only shrink, nothing re-enters.
- Acceptance endgame: `solution = some g` gives a partition with `g a` last (P3). For a blocker `C`: the Dead disjunct gives refuter `z` (`g z` listed by P0, `Dead z C` gives `g z >_z C`, contradicting `Ranks z C (g z)`); the all-listed disjunct (empirically empty, must still be proved): blocking -> each member lists `C` above its last -> P1 -> all members proposed `C` -> in-proposal completeness makes `C` considerable for a member `m` -> INV-BC -> `C` is `m`'s last = `g m`, contradicting strict preference.

Bricks, one AXLE-verified unit each:

1. `PrefsSublist`/OSP/PBU predicates + per-transition preservation (`TrimsTo` covers the eliminate cases; broadcast needs "topUnproposed is the best remaining").
2. INV-BC + in-proposal bookkeeping.
3. `Dead`/`BlockerBarrier` + the two event lemmas + `self` unreachability.
4. Acceptance endgame.
5. Run-level threading (`HCFState.run` carries the extended bundle as it carries `HCFInv`) + `hcf_coreStable`.

Optional: `run` agrees with `runFuel` at sufficient fuel (bridges the proofs to the parity evidence).

Probe recipe, if a claim needs re-checking: instrument `solve_iterative` with elimination-cause tags (`tail` cascade worse-tail, `self` cascade self-elimination, `(child, pivot)` pending_remaining elimination) plus per-receive and per-acceptance invariant checks.

## Item 11 -- `hcf_complete` (waits on D9)

If the instance admits a genuine core-stable outcome (D9 predicate), `hcfGrouping` returns `some`. Probe against the oracle before formalizing; the parity suite's zero solvability disagreements are the existing evidence.

## Item 12 -- subsumption theorems

- `hcf_subsumes_gs`: `hcfGrouping != none` on SMP from completeness applied to GS's own output (`gs_coreStable`, plus that output meeting the D9 predicate; `gs_solves_smp`'s bare exists cannot feed it); core-stability from item 10.
- `hcf_subsumes_irv`: both directions route through items 10-11 plus the size-2 bridges; the negative branch quantifies over `IsPairMatching`.

## Other open holes

- Vacuous positive statements: `irving_decides_stability`/`irving_decides_rmp` conclude a bare `exists mu, PairwiseStable/CoreStable`, and `gs_solves_smp` a bare `exists mu, CoreStable` -- all trivially witnessed by all-singletons under `SizeTwo`, so `irving_decides_rmp` is provable without Irving. Fix: `exists mu, IsPairMatching prof mu and ...`, which needs a listedness invariant (every remaining list entry is a ranked pair) threaded through phase 1/2 like `RemovedDominated`; or cite `gs_coreStable` and state the Irving result exactly. `gs_coreStable` (about GS's actual output) is not affected. Item 12's statements name HCF's output, so they are not affected either.
- `src/hedonic.py`: the "this never actually should happen" comment sits on the `tail` branch (fires constantly); it belongs on the `self` branch above it.
- Trajectory equivalence (HCF's run equals GS's/Irving's): unscheduled, only if a reviewer asks; what "equivalence" should mean (output equality? step simulation?) is itself open.
- CAP via HCF (deferred, D5): change `_is_considerable` so a college's class becomes considerable once all its members propose individually, and a student considers a college once in a coalition the college proposes. Open: preference encoding blows up (listing all classmate combinations), and whether the above/below elimination still holds.

## Method

- Probe before formalizing: test any load-bearing invariant or witness on Python-oracle trajectories (exhaustive small n + random larger n) before writing Lean. AXLE `disprove` passing is weak evidence; probes have caught several false claims it passed.
- Batch sorries that share an upstream definitional choice (fix the definition, close the cluster); take independent case analyses one at a time with the goal state in hand.
- `make sorry2lemma FILE=... NAMES=...` for the exact goal; split big lemmas into small named helpers; `make check-one` after each change.
- AXLE: full-file `disprove` on `Irving.lean` (and `IRV_RMP.lean`, which concatenates it) aborts at the `isDefEq` heartbeat ceiling -- use `axle disprove --names` with fully-qualified names (short names return "not found"). `disprove` strips proof bodies before negating, so its warnings say nothing about the proofs. `check-one` JSON fields `okay`/`lean_messages`/`failed_declarations` are top-level.
- Lean/Mathlib gotchas in this environment: `List.Chain'` is hard-deprecated (use `List.IsChain`, `List.isChain_cons`); `not_mem` lemmas are renamed `notMem`; structure-instance continuation fields must be column-aligned with the first field, and an application-valued field followed by another needs a comma; `simp only` does not reduce `Stage` constructor-equality `ite`s (full `simp` before `omega`); `<+` does not parse (spell `List.Sublist`); `simp [f, h]` renormalizes `List.get` to `getElem` in the goal but not in `h` (use `simp only`); `omega` treats `Fin.val` casts as opaque atoms (supply the Nat form); `subst hx` with `hx : x = a` eliminates `a`; a multi-line `if` inside `set` fails to parse; an applied `(by simpa ...)` term needs a `have` name.
- `refs/stable-marriage-lean` suggests strategies only: its separate `Men/Women` types do not port to the unified `α + BipartiteStructure` form.

## Publication

- Two contributions: the unifying algorithm, and its machine-checked Lean proofs; strongest combined.
- Route: workshop first (MATCH-UP at AAMAS, COMSOC; 2-4 page extended abstract; establishes priority), then the algorithm paper at a game-theory venue (SAGT 12 pages, GEB, SCW) with the Lean as artifact. An ITP/CPP formalization paper only at 0 sorries.
- Paper work, not blocked by Lean: rewrite Corollaries 3-6 as proper proofs with explicit induction; complexity section (exponential general bound, O(n^2) for the GS/Irving reductions, relation to Ballester 2004 NP-hardness); sharpen what the algorithm adds on core computation vs Bogomolnaia & Jackson 2002 and Banerjee et al. 2001.
