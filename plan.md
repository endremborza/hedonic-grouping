# Publication Plan

## Status: Phase 2 partially complete

### Phase 1: Literature & Terminology — DONE
- [x] Related Work section added connecting to hedonic games / core stability literature
- [x] 8 new bib entries (Drèze & Greenberg 1980, Bogomolnaia & Jackson 2002, Banerjee et al. 2001, Ballester 2004, Alcalde & Revilla 2004, Woeginger 2013, Cechlárová & Romero-Medina 2002)
- [x] Abstract rewritten to position contribution clearly
- [x] Keywords added
- [x] Bibliography command fixed (was broken)
- [ ] Body text still uses "grouping problem" / "group stability" — intentional, but consider adding explicit parenthetical "(core stability)" at key points in Sections 3-4

### Phase 2: Unifying Framework Proofs — IN PROGRESS
- [x] Section 5 "Connections to Classical Matching Algorithms" added
- [x] Lemma 1 (→ Gale-Shapley) with proof sketch
- [x] Lemma 2 (→ Irving) with proof sketch
- [ ] **Tighten Lemma 1**: the "considerable" condition under bipartite size-2 must be unpacked more carefully. Currently claims α_j proposes {α_i} makes it considerable — but considerable means all other members propose it, which for a pair means the *other* agent proposes it. Under bipartite GS, the proposer side always proposes first, so the responder never proposes — the "considerable" condition is satisfied when the responder holds exactly one proposal (the best so far). This subtlety needs explicit treatment.
- [ ] **Tighten Lemma 2**: show the cycle structure. When α_1 moves on from α_2, and α_2 moves on from α_3, ... , and α_k moves on from α_1, a rotation is detected. Map this explicitly to Irving's rotation (q_0, q_1, ..., q_{r-1}) and show the eliminations are identical.

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
- [ ] Final compilation check, page count, format compliance for target venue
