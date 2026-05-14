"""Hedonic tests: Example 5 + exhaustive/random correctness and iter parity."""

import pytest

from ..common import is_stable_hedonic
from ..generators import HedonicProfile, profiles_hedonic, random_hedonic
from ..hedonic import solve, solve_iterative


def test_hedonic_example5(hedonic_example5: HedonicProfile) -> None:
    sol = solve(hedonic_example5)
    assert sol is not None
    assert is_stable_hedonic(hedonic_example5, sol)


def test_hedonic_iter_example5(hedonic_example5: HedonicProfile) -> None:
    sol = solve_iterative(hedonic_example5)
    assert sol is not None
    assert is_stable_hedonic(hedonic_example5, sol)


@pytest.mark.parametrize("n", [3])
def test_hedonic_exhaustive(n: int) -> None:
    for prefs in profiles_hedonic(n):
        sol = solve(prefs)
        if sol is not None:
            assert is_stable_hedonic(prefs, sol), (prefs, sol)


@pytest.mark.parametrize("n,seed", [(n, s) for n in (4, 5) for s in range(30)])
def test_hedonic_random(n: int, seed: int) -> None:
    prefs = random_hedonic(n, seed)
    sol = solve(prefs)
    if sol is not None:
        assert is_stable_hedonic(prefs, sol)


@pytest.mark.parametrize("n", [3])
def test_iter_parity_exhaustive(n: int) -> None:
    for prefs in profiles_hedonic(n):
        rec = solve(prefs)
        itr = solve_iterative(prefs)
        assert (rec is None) == (itr is None), prefs
        if itr is not None:
            assert is_stable_hedonic(prefs, itr), (prefs, itr)


@pytest.mark.parametrize("n,seed", [(n, s) for n in (4, 5) for s in range(30)])
def test_iter_parity_random(n: int, seed: int) -> None:
    prefs = random_hedonic(n, seed)
    rec = solve(prefs)
    itr = solve_iterative(prefs)
    assert (rec is None) == (itr is None)
    if itr is not None:
        assert is_stable_hedonic(prefs, itr)
