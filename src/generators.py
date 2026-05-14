"""Preference generators for SMP, RMP, and HCP testing.

Centerpiece of the test suite. For each problem type three entries:

  enumerate_*(n)        yield every strict-preference profile of size n
  random_*(n, seed)     one profile sampled from a seeded RNG
  profiles_*(n, ...)    cap-aware mix: exhaustive at small n, random above

SMP profiles also fit college admissions: the many-to-one structure
lives in the quota constraint, not in the preferences themselves.

Exhaustive counts grow fast; the caps below were picked so the
default `profiles_*` call stays under ~50k profiles.

  n=2 SMP: 16          n=3 SMP: 46_656     n=4 SMP: ~1.1e11
  n=3 RMP: 8           n=4 RMP: 1_296      n=5 RMP: ~7.9e6
  n=2 HCP: 6           n=3 HCP: 216        n=4 HCP: ~6e14
"""

import random
from collections.abc import Iterator
from itertools import combinations, permutations, product
from typing import TypeAlias

from .common import Agent, Coalition

SmpProfile: TypeAlias = tuple[dict[Agent, list[Agent]], dict[Agent, list[Agent]]]
RmpProfile: TypeAlias = dict[Agent, list[Agent]]
HedonicProfile: TypeAlias = dict[Agent, list[Coalition]]

EXHAUSTIVE_CAP: dict[str, int] = {"smp": 3, "rmp": 4, "hedonic": 3}


def smp_agents(n: int) -> tuple[list[Agent], list[Agent]]:
    return [f"m{i + 1}" for i in range(n)], [f"w{i + 1}" for i in range(n)]


def rmp_agents(n: int) -> list[Agent]:
    return [f"a{i + 1}" for i in range(n)]


def _coalitions(agents: list[Agent]) -> list[Coalition]:
    return [
        frozenset(c)
        for r in range(2, len(agents) + 1)
        for c in combinations(agents, r)
    ]


# --- Random ---


def random_smp(n: int, seed: int = 0) -> SmpProfile:
    rng = random.Random(seed)
    men, women = smp_agents(n)
    return (
        {m: rng.sample(women, n) for m in men},
        {w: rng.sample(men, n) for w in women},
    )


def random_rmp(n: int, seed: int = 0) -> RmpProfile:
    rng = random.Random(seed)
    agents = rmp_agents(n)
    return {a: rng.sample([b for b in agents if b != a], n - 1) for a in agents}


def random_hedonic(n: int, seed: int = 0) -> HedonicProfile:
    rng = random.Random(seed)
    agents = rmp_agents(n)
    coalitions = _coalitions(agents)
    prefs: dict[Agent, list[Coalition]] = {}
    for a in agents:
        possible = [c for c in coalitions if a in c]
        rng.shuffle(possible)
        prefs[a] = possible
    return prefs


# --- Exhaustive ---


def enumerate_smp(n: int) -> Iterator[SmpProfile]:
    men, women = smp_agents(n)
    m_orderings = list(permutations(women))
    w_orderings = list(permutations(men))
    for m_choice in product(m_orderings, repeat=n):
        for w_choice in product(w_orderings, repeat=n):
            yield (
                {m: list(o) for m, o in zip(men, m_choice)},
                {w: list(o) for w, o in zip(women, w_choice)},
            )


def enumerate_rmp(n: int) -> Iterator[RmpProfile]:
    agents = rmp_agents(n)
    per_agent = [list(permutations([b for b in agents if b != a])) for a in agents]
    for choice in product(*per_agent):
        yield {a: list(o) for a, o in zip(agents, choice)}


def enumerate_hedonic(n: int) -> Iterator[HedonicProfile]:
    agents = rmp_agents(n)
    coalitions = _coalitions(agents)
    per_agent = [
        list(permutations([c for c in coalitions if a in c])) for a in agents
    ]
    for choice in product(*per_agent):
        yield {a: list(o) for a, o in zip(agents, choice)}


# --- Cap-aware unified entry points ---


def profiles_smp(n: int, samples: int = 100) -> Iterator[SmpProfile]:
    if n <= EXHAUSTIVE_CAP["smp"]:
        yield from enumerate_smp(n)
    else:
        for s in range(samples):
            yield random_smp(n, s)


def profiles_rmp(n: int, samples: int = 100) -> Iterator[RmpProfile]:
    if n <= EXHAUSTIVE_CAP["rmp"]:
        yield from enumerate_rmp(n)
    else:
        for s in range(samples):
            yield random_rmp(n, s)


def profiles_hedonic(n: int, samples: int = 50) -> Iterator[HedonicProfile]:
    if n <= EXHAUSTIVE_CAP["hedonic"]:
        yield from enumerate_hedonic(n)
    else:
        for s in range(samples):
            yield random_hedonic(n, s)
