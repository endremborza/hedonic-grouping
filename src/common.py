"""Common types and utilities for stable matching algorithms.

Shared type aliases, stability verification, and random instance generation
used across the Gale-Shapley, Irving, and hedonic grouping implementations.

Note on college admissions: The many-to-one matching problem (colleges with
quotas) is subsumed by the hedonic framework — each coalition includes a
college and a student subset. This creates a combinatorial explosion: a
college with quota q among n students generates C(n,q) coalitions, many
equivalent from the college's perspective. Specialized algorithms
(college-proposing GS, Roth-Peranson) exploit this structure for polynomial
solutions; the general hedonic algorithm handles it correctly but with
exponential cost.
"""

import random
from itertools import combinations
from typing import TypeAlias

Agent: TypeAlias = str
Coalition: TypeAlias = frozenset[str]


# --- Stability verification ---


def is_stable_marriage(
    men_prefs: dict[Agent, list[Agent]],
    women_prefs: dict[Agent, list[Agent]],
    matching: dict[Agent, Agent],
) -> bool:
    """Verify stability of a marriage matching: no blocking pair exists."""
    for m, m_pref in men_prefs.items():
        w_m = matching[m]
        for w in m_pref:
            if w == w_m:
                break
            m_w = matching[w]
            if women_prefs[w].index(m) < women_prefs[w].index(m_w):
                return False
    return True


def is_stable_roommates(
    prefs: dict[Agent, list[Agent]],
    matching: dict[Agent, Agent],
) -> bool:
    """Verify stability of a roommate matching: no blocking pair exists."""
    for a, a_pref in prefs.items():
        partner = matching[a]
        rank_partner = a_pref.index(partner)
        for b in a_pref[:rank_partner]:
            if a in prefs[b] and prefs[b].index(a) < prefs[b].index(matching[b]):
                return False
    return True


def is_stable_hedonic(
    prefs: dict[Agent, list[Coalition]],
    solution: dict[Agent, Coalition],
) -> bool:
    """Verify core stability: no blocking coalition exists."""
    for a, a_pref in prefs.items():
        assigned = solution[a]
        if assigned not in a_pref:
            return False
        rank = a_pref.index(assigned)
        for better in a_pref[:rank]:
            if all(
                better in prefs[b]
                and solution[b] in prefs[b]
                and prefs[b].index(better) < prefs[b].index(solution[b])
                for b in better
                if b != a
            ):
                return False
    return True


# --- Instance generation ---


def generate_marriage(
    n: int, seed: int | None = None
) -> tuple[
    list[Agent], list[Agent], dict[Agent, list[Agent]], dict[Agent, list[Agent]]
]:
    """Random stable marriage instance with n men and n women."""
    rng = random.Random(seed)
    men = [f"m{i + 1}" for i in range(n)]
    women = [f"w{i + 1}" for i in range(n)]
    men_prefs = {m: rng.sample(women, n) for m in men}
    women_prefs = {w: rng.sample(men, n) for w in women}
    return men, women, men_prefs, women_prefs


def generate_roommates(
    n: int, seed: int | None = None
) -> tuple[list[Agent], dict[Agent, list[Agent]]]:
    """Random stable roommates instance with n agents (n must be even)."""
    rng = random.Random(seed)
    agents = [f"a{i + 1}" for i in range(n)]
    prefs = {a: rng.sample([b for b in agents if b != a], n - 1) for a in agents}
    return agents, prefs


def generate_hedonic(
    n: int, seed: int | None = None
) -> tuple[list[Agent], dict[Agent, list[Coalition]]]:
    """Random hedonic grouping instance with n agents."""
    rng = random.Random(seed)
    agents = [f"a{i + 1}" for i in range(n)]
    all_coalitions = [
        frozenset(c) for r in range(2, n + 1) for c in combinations(agents, r)
    ]
    prefs: dict[Agent, list[Coalition]] = {}
    for a in agents:
        possible = [c for c in all_coalitions if a in c]
        rng.shuffle(possible)
        prefs[a] = possible
    return agents, prefs
