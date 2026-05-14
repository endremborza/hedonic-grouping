"""Irving tests: two edge cases + exhaustive/random coverage."""

import pytest

from ..common import is_stable_roommates
from ..generators import RmpProfile, profiles_rmp, random_rmp
from ..irving import irving


def test_irving_no_solution(irving_no_solution: RmpProfile) -> None:
    assert irving(irving_no_solution) is None


def test_irving_6_agents(irving_6_agents: RmpProfile) -> None:
    matching = irving(irving_6_agents)
    assert matching is not None
    assert is_stable_roommates(irving_6_agents, matching)


@pytest.mark.parametrize("n", [4])
def test_irving_exhaustive(n: int) -> None:
    for prefs in profiles_rmp(n):
        matching = irving(prefs)
        if matching is not None:
            assert is_stable_roommates(prefs, matching), (prefs, matching)


@pytest.mark.parametrize("n,seed", [(n, s) for n in (6, 8) for s in range(50)])
def test_irving_random(n: int, seed: int) -> None:
    prefs = random_rmp(n, seed)
    matching = irving(prefs)
    if matching is not None:
        assert is_stable_roommates(prefs, matching)
