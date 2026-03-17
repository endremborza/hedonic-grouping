# Generalized Stable Matching as Hedonic Coalition Formation

## Current Paper Structure (as of 2026-03-15)

### Section 1: Introduction
Motivates the grouping problem via applications (hospital-resident, kidney exchange, school assignment, team formation). Establishes the combinatorial explosion: $2^p - 1$ possible coalitions per agent. Uses kindergarten field-trip example to motivate different stability definitions. Ends with roadmap to remaining sections.

### Section 2: Related Work *(new)*
Connects the paper to hedonic games literature. Establishes that "group stability" = core stability. Cites Drèze & Greenberg (1980), Bogomolnaia & Jackson (2002), Banerjee et al. (2001), Ballester (2004), Woeginger (2013), Cechlárová & Romero-Medina (2002), Alcalde & Revilla (2004). Positions the contribution: no prior single algorithm subsumes both Gale-Shapley and Irving.

### Section 3: Framework
Formal notation: $\langle A, \mathbf{\Omega}, M \rangle$. Reviews marriage problem, college admissions, roommates problem. Defines group stability (Definition 1).

### Section 4: Algorithms
- **4.1 Simple Reduction**: Basic Reduction (Algorithm 1) and Simplified Reduction (Algorithm 2). Introduces *considerable* proposals (Definition 2). Corollaries 1 and 2.
- **4.2 Processing of Reduced Problem**: Processing Function (Algorithm 3). Introduces *moving on* and *exceptions*. Corollary 3.
- **4.3 Recursion**: Recursive Grouping Function (Algorithm 4). Corollaries 4 (solution found) and 5 (halting).
- Worked example: 5-agent case (Tables 1-2) traced through all phases.

### Section 5: Connections to Classical Matching Algorithms *(new)*
- Lemma 1: under bipartite size-2 restrictions, Algorithm 2 = Gale-Shapley. Moving-on never triggers.
- Lemma 2: under non-bipartite size-2 restrictions, Algorithms 2+4 = Irving. Moving-on = rotation elimination.

### Section 6: Conclusion
Summarizes contribution. Open directions: weak preferences, complexity analysis, existence conditions, optimality within the core.

---

## Remaining Work

### Must-have for submission
1. **Complexity analysis** — worst-case Big-O for Algorithm 4. The recursion tree has branching factor $\leq p$ and depth $\leq N = \sum_i |M(\alpha_i)|$. Each node runs Simplified Reduction costing at most $O(N^2)$. Worst case is therefore $O(p^N \cdot N^2)$, but expected behavior on structured instances should be much better. This needs formal treatment and honest discussion of the overhead vs. specialized algorithms.
2. **Tighten Lemma 1 proof** — the "considerable" condition under bipartite size-2 is not simply "α_j also proposes {α_i}"; it's that α_j's current best held proposal is from α_i. The proof needs to walk through the GS invariant more carefully.
3. **Tighten Lemma 2 proof** — the correspondence between "moving on" and Irving rotations needs to show the cycle structure explicitly, not just assert analogy.

### Should-have for competitive submission
4. **Empirical validation** — Python 3 implementation + Monte Carlo for $p = 5, 10, 15, 20$. Runtime graphs vs. $p$. Existence frequency of stable groupings vs. $p$.
5. **Formal theorem numbering** — Corollaries 1-5 should be Propositions or Theorems. The proofs are currently inline prose; they need `\begin{proof}...\end{proof}` environments.
6. **Language polish** — remaining first-person "I" usages in Sections 3-4 should become "we". Some informal passages ("It's not just that...", "Take a simple example") could be tightened for a CS theory audience.

### Nice-to-have
7. **Existence characterization** — analogue of Tan's condition for groupings.
8. **Weak preferences extension** — at least a formal conjecture about what changes.
