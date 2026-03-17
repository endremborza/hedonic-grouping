# Publication Path

## Honest assessment

The paper has a genuinely interesting core result: a single recursive algorithm that subsumes Gale-Shapley and Irving as special cases, applied to the most general hedonic coalition formation game with strict preferences over arbitrary subsets. This is a clean contribution if the proofs hold up.

The obstacle is that the general problem is NP-hard (Ballester 2004 shows this for hedonic games). The algorithm is correct and complete but inherently exponential in the worst case. This is not a disqualifier — many important algorithms are exponential — but it shapes the framing. The paper cannot claim efficiency; it claims *universality and correctness*.

The current state of the paper (Related Work done, Lemma proofs sketched, no complexity analysis, no experiments) puts it roughly halfway to a submittable draft.

---

## Recommended path: two-stage submission

### Stage 1: Workshop or short paper (target: late 2026)

**Why workshop first**: The unification claim is novel enough to generate discussion, but the proofs need stress-testing by the community. A workshop paper lets you present the core result, get feedback on the Lemma proofs and complexity framing, and refine before committing to a full venue.

**Target venues** (ordered by fit):

1. **MATCH-UP** (Workshop on Matching Under Preferences, next edition likely 2027)
   - *Perfect* topical fit. The audience literally studies GS and Irving.
   - Accepts extended abstracts (4-8 pages). The current paper, trimmed, would work.
   - Informal peer review, presentation-focused.

2. **COMSOC** (Workshop on Computational Social Choice, biennial, next ~2027)
   - Strong hedonic games track. Core stability in coalition formation is a recurring topic.
   - Extended abstracts accepted.

3. **AAMAS extended abstract** (deadline typically ~October for May conference)
   - 2-page extended abstracts accepted alongside full papers.
   - Large multi-agent systems community interested in hedonic games.
   - Would need: abstract + core algorithm + Lemma statements (no proofs). Feasible now.

**What you need for a workshop submission**:
- Current paper content is sufficient for an extended abstract
- Tighten the two Lemma proofs to be airtight (Phase 2)
- A paragraph acknowledging the exponential complexity and positioning it honestly

### Stage 2: Full paper (target: 2027)

After workshop feedback, expand to a full paper with complexity analysis and experiments.

**Target venues** (ordered by recommendation):

| Venue | Type | Fit | Needs | Typical deadline |
|-------|------|-----|-------|-----------------|
| **SAGT** | Conference | Best fit | Complexity analysis, tight proofs | ~June |
| **WINE** | Conference | Strong | Complexity, some experiments | ~June |
| **Games and Economic Behavior** | Journal | Strong | Thorough proofs, no page limit | Rolling |
| **Journal of Mechanism and Institution Design** | Journal (OA) | Good | Mechanism focus, less CS rigor needed | Rolling |
| **ACM EC** | Conference | Stretch | Needs experiments + tight complexity | ~February |
| **Theoretical Computer Science** | Journal | Good if complexity is strong | Full complexity treatment | Rolling |

**Recommendation: SAGT** as the primary full-paper target. Reasons:
- Algorithmic game theory is the exact intersection
- They value clean theoretical results over massive experiments
- The unification result (GS + Irving as special cases) would be appreciated there
- 12-page limit forces conciseness, which suits this paper

**What you need for a full SAGT submission**:
- Everything in Phases 2-5 of plan.md
- The complexity analysis framed honestly: "the algorithm is worst-case exponential, which is inherent since the general problem is NP-hard, but it is the first algorithm that is (a) correct and complete for the full hedonic game and (b) reduces to polynomial-time algorithms on tractable subclasses"
- At least a small experimental section showing the algorithm works in practice for $p \leq 15$

---

## What NOT to target

- **EC (ACM Economics and Computation)**: Very competitive (15-20% acceptance). The paper would need a stronger novelty angle — either a surprising complexity result or an impossibility theorem — beyond "here is an algorithm that works."
- **AAAI / IJCAI**: Wrong audience. These are broad AI conferences where the matching theory community is small.
- **Pure economics journals (AER, Econometrica, JPE)**: The contribution is algorithmic, not economic. The result doesn't change how economists think about markets.

---

## Critical path to first submission

```
Now ──────────── Phase 2 (tighten Lemmas) ──── Workshop abstract ──── Submit
                                                     │
                          ┌──────────────────────────┘
                          ▼
                  Phase 3 (complexity) ── Phase 4 (code + experiments)
                          │                         │
                          ▼                         ▼
                  Phase 5 (polish) ──────── Full paper ──── Submit SAGT
```

The bottleneck is Phase 2. If the Lemma proofs hold up under scrutiny, the rest is execution. If they don't — if the "considerable" condition doesn't map as cleanly to GS/Irving as claimed — the paper's main selling point weakens and you'd need to reframe.
