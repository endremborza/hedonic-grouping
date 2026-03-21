# Hedonic Grouping

Lean 4 formalization of a unifying algorithm for stable matching as hedonic coalition formation.

## Core Claim

A single recursive algorithm subsumes both Gale-Shapley (bipartite matching) and Irving (stable roommates) as special cases, applied to general hedonic games with strict preferences over arbitrary coalitions. The algorithm is correct and complete but worst-case exponential — inherent since the general problem is NP-hard (Ballester 2004). It reduces to polynomial-time on tractable subclasses.

## Paper Structure

The accompanying paper introduces a framework `<A, Omega, M>` for hedonic coalition formation:

- **Section 2 — Related Work**: Connects to hedonic games literature (Dreze & Greenberg, Bogomolnaia & Jackson, Banerjee et al., Ballester, Woeginger, Cechlarova & Romero-Medina, Alcalde & Revilla).
- **Section 3 — Framework**: Formal notation, reviews marriage/college admissions/roommates problems, defines group stability (= core stability).
- **Section 4 — Algorithms**: Simplified Reduction (considerable proposals), Processing (move-on chains, exceptions), Recursive Grouping. Worked 5-agent example.
- **Section 5 — Connections**: Lemma 1 (algorithm = Gale-Shapley under bipartite size-2), Lemma 2 (algorithm = Irving under non-bipartite size-2).

## Formalization State

### Defs.lean — Complete
`PreferenceProfile`, `Considerable`, `BlockingCoalition`, `CoreStable`, `SizeTwo`, validity predicates.

### Lemma1.lean — Complete (no sorries)
- `considerable_iff_mutual_proposal`: on size-2 pair {a,b}, considerable <-> prop b = some {a,b}
- `considerable_eq_gsHolds`: considerable = GS "holds" relation
- `lemma1_considerable_matches_gs`: main statement with bipartite hypotheses

### Lemma2.lean — One open sorry
- `RotationCycle`: shared structure for Irving rotations and move-on chains
- `IsIrvingRotation`, `IsMoveOnChain`: validity predicates
- `eliminatedPair`: pair eliminated at each cycle position (definitionally shared by both algorithms)
- **Open**: `moveon_satisfies_irving_conditions` — needs algorithm state formalized as `AlgState` with loop invariants relating `prop`, preference lists, and M-reductions (~50-80 lines)

## Remaining Work

### Critical
- Close the sorry in Lemma 2 (formalize `AlgState` + loop invariants)
- Tighten Lemma 1 and 2 proof prose in the paper (unpack "considerable" condition carefully)
- Complexity analysis: formal Big-O treatment, honest framing of exponential worst-case

### For full paper
- Python 3 implementation + Monte Carlo experiments (p = 5-20)
- Formal theorem numbering with proof environments
- Language polish (first-person, informal passages)

## Target Venues
- **Workshop** (first): MATCH-UP or COMSOC extended abstract — current content is sufficient
- **Full paper**: SAGT (algorithmic game theory, 12-page limit, values clean theoretical results)

## Building

```
lake build
```

Requires Lean 4 + Mathlib. Toolchain managed by `elan`. AXLE (`axle`) used for remote proof checking/repair — see `make help`.
