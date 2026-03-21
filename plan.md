# Publication Plan

## Status: Phase 2 substantially complete

### Phase 1: Literature & Terminology — DONE
- [x] Related Work section added connecting to hedonic games / core stability literature
- [x] 8 new bib entries (Drèze & Greenberg 1980, Bogomolnaia & Jackson 2002, Banerjee et al. 2001, Ballester 2004, Alcalde & Revilla 2004, Woeginger 2013, Cechlárová & Romero-Medina 2002)
- [x] Abstract rewritten to position contribution clearly
- [x] Keywords added
- [x] Bibliography command fixed (was broken)
- [ ] Body text still uses "grouping problem" / "group stability" — intentional, but consider adding explicit parenthetical "(core stability)" at key points in Sections 3-4

### Phase 2: Unifying Framework Proofs — SUBSTANTIALLY COMPLETE

#### Paper-level proofs (tex/main.tex)
- [x] Section 5 "Connections to Classical Matching Algorithms" added
- [x] Lemma 1 (→ Gale-Shapley) with proof sketch
- [x] Lemma 2 (→ Irving) with proof sketch
- [ ] **Tighten Lemma 1 proof text**: unpack the "considerable" condition more carefully.
  Under bipartite GS, the proposer side always proposes first; the responder holds
  the best proposal received. The considerable condition on {α_i, α_j} under size-2
  reduces to: α_j holds α_i's proposal (= α_j's current best). This subtlety is now
  machine-verified in lean/Lemma1.lean but needs explicit prose treatment in the paper.
- [ ] **Tighten Lemma 2 proof text**: make the cycle structure explicit. When α_1 moves
  on from α_2, α_2 from α_3, ..., α_k from α_1, the `RotationCycle` closes. Map this
  explicitly to Irving's rotation (q_0, ..., q_{r-1}) and show eliminations are identical.
  The structural correspondence is machine-verified; the semantic proof is open (see below).

#### Lean 4 formalization (lean/)

All files use AXLE (lean-4.28.0 environment, Mathlib included) for checking.

**lean/Defs.lean** — DONE, no sorrys
- [x] `PreferenceProfile`, `ranks`, `Considerable`, `BlockingCoalition`, `CoreStable`

**lean/Lemma1.lean** — DONE, fully proved, no sorrys
- [x] `considerable_iff_mutual_proposal`: on size-2 pair {a,b}, considerable ↔ prop b = some {a,b}
- [x] `considerable_eq_gsHolds`: considerable condition = GS "holds" relation (definitional)
- [x] `lemma1_considerable_matches_gs`: main Lemma 1 statement with BipartiteStructure hypotheses
- [x] `axle disprove` found no counterexample for any claim

**lean/Lemma2.lean** — MOSTLY DONE, one open sorry
- [x] `RotationCycle α`: unified structure for both Irving rotations and move-on chains.
  `IrvingRotation` and `MoveOnChain` are both `abbrev`s for `RotationCycle`, making
  structural correspondence definitional rather than existential.
- [x] `IsIrvingRotation`: validity predicate (p_i proposes to q_i; q_i's list orders them correctly)
- [x] `IsMoveOnChain`: algorithmic predicate (p_i moved on from q_i; cycle closes via considerable)
- [x] `moveon_cycle_is_irving_rotation`: structural correspondence is `⟨chain, rfl⟩` — trivial by design
- [x] `elimination_matches_irving`: pair {p_i, q_{i+1 mod r}} removed by both, proved by `rfl`
- [x] `axle disprove` found no counterexample for any claim
- [ ] **Open sorry**: `moveon_satisfies_irving_conditions` — a cycle from the move-on mechanism
  satisfies `IsIrvingRotation`. This requires reasoning about the algorithm's execution state
  (what proposals were made and held, what was eliminated from M). Needs the algorithm semantics
  formalized (relations between `prop`, the preference lists, and M-reductions).

**Next step to close the sorry**:
Formalize the algorithm state as a record `AlgState` (current `prop` map + reduced M) and define
`SimplifiedReduction` as a relation on `AlgState`. Then show that if `AlgState` satisfies
the loop invariants of Algorithm 2, and the move-on step produces a cycle, the cycle satisfies
`IsIrvingRotation`. This is ~50–80 lines of Lean.

### Phase 3: Complexity Analysis — NOT STARTED
- [ ] Define input size: $N = \sum_{i=1}^{p} |\Omega_i|$ (total preference entries). Under unrestricted preferences, $|\Omega_i| = 2^{p-1} - 1$, so $N = p(2^{p-1} - 1)$.
- [ ] **Simplified Reduction (Algorithm 2)**: each proposal is made at most once, each reduction removes at least one entry from some $M(\alpha_i)$. Cost per round: $O(p \cdot g_{\max})$ where $g_{\max}$ is max group size. Total rounds $\leq N$. Overall: $O(N \cdot p \cdot g_{\max})$.
- [ ] **Recursive Grouping (Algorithm 4)**: each recursive call forces at least one "move on", consuming one group from some $M(\alpha_i)$. Max recursion depth $\leq N$. Each call runs Simplified Reduction ($O(N \cdot p \cdot g_{\max})$). Branching factor $\leq p$. Worst case: $O(p^N \cdot N \cdot p \cdot g_{\max})$.
- [ ] Discuss: under bipartite size-2 constraints, this collapses to $O(n^2)$ (Gale-Shapley). Under non-bipartite size-2, $O(n^2)$ (Irving). The exponential blowup is inherent to the general hedonic game, which is NP-hard (Ballester 2004). Frame the algorithm as complete (always correct) rather than efficient.
- [ ] Add a Theorem or Proposition summarizing complexity in the paper.

### Phase 4: Empirical Validation — NOT STARTED
- [ ] Rewrite the Python 2.7 implementation in Python 3
  - Data structures: agents as integers, preference profiles as lists of frozensets, M as a dict of sorted preference lists
  - Core functions: `simplified_reduction(A, M)`, `process(A, M, omega, J)`, `grouping(A, M, omega, J)`
- [ ] Test against known instances: the 5-agent example from the paper, standard GS/Irving instances
- [ ] Monte Carlo: generate random strict preference profiles for $p = 5, 8, 10, 12, 15$
  - Measure: runtime (wall clock), recursion depth, number of reductions, existence frequency
  - Repeat 1000 times per $p$ value
- [ ] Generate figures (programmatically, per CLAUDE.md):
  - Fig 1: Mean runtime vs. $p$ (log scale y-axis)
  - Fig 2: Fraction of instances with stable grouping vs. $p$
  - Fig 3: Mean recursion depth vs. $p$
- [ ] Add `\section{Computational Experiments}` between Connections and Conclusion

### Phase 5: Final Polish — NOT STARTED
- [ ] Convert Corollaries 1-5 to Propositions with proper `\begin{proof}` environments
- [ ] Convert remaining first-person "I" to "we" in Sections 3-4
- [ ] Tighten informal passages for CS theory audience
- [ ] Remove `cusack95` from bib (unrelated — phase-unwrapping optics paper)
- [ ] Uncomment and update author affiliation
- [ ] Add remark after Lemma 1: proof machine-verified in Lean 4 via AXLE
- [ ] Add remark after Lemma 2: structural correspondence machine-verified; semantic proof open
- [ ] Publish lean/ directory as supplementary artifact
- [ ] Final compilation check, page count, format compliance for target venue
