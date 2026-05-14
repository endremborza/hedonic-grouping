"""Gale-Shapley tests: one edge case + exhaustive/random coverage."""

import pytest

from ..common import is_stable_marriage
from ..gale_shapley import gale_shapley
from ..generators import SmpProfile, profiles_smp, random_smp


def test_gs_3x3_proposer_optimal(gs_3x3: SmpProfile) -> None:
    mp, wp = gs_3x3
    matching = gale_shapley(mp, wp)
    assert is_stable_marriage(mp, wp, matching)
    assert matching["m1"] == "w3"
    assert matching["m2"] == "w1"
    assert matching["m3"] == "w2"


@pytest.mark.parametrize("n", [2, 3])
def test_gs_exhaustive(n: int) -> None:
    for mp, wp in profiles_smp(n):
        matching = gale_shapley(mp, wp)
        assert is_stable_marriage(mp, wp, matching), (mp, wp, matching)


@pytest.mark.parametrize("n,seed", [(n, s) for n in (5, 8) for s in range(50)])
def test_gs_random(n: int, seed: int) -> None:
    mp, wp = random_smp(n, seed)
    matching = gale_shapley(mp, wp)
    assert is_stable_marriage(mp, wp, matching)
