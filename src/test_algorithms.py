"""Tests for all stable matching algorithms.

Run: python -m src.test_algorithms
"""

import sys

from .common import (
    Coalition,
    generate_hedonic,
    generate_marriage,
    generate_roommates,
    is_stable_hedonic,
    is_stable_marriage,
    is_stable_roommates,
)
from .gale_shapley import gale_shapley
from .hedonic import solve as hedonic_solve
from .irving import irving


# --- Gale-Shapley ---


def test_gs_known() -> None:
    """3x3 example with rejection cascade."""
    mp = {
        "m1": ["w1", "w2", "w3"],
        "m2": ["w1", "w3", "w2"],
        "m3": ["w2", "w1", "w3"],
    }
    wp = {
        "w1": ["m2", "m1", "m3"],
        "w2": ["m3", "m1", "m2"],
        "w3": ["m1", "m2", "m3"],
    }
    matching = gale_shapley(mp, wp)
    assert is_stable_marriage(mp, wp, matching)
    assert matching["m1"] == "w3"
    assert matching["m2"] == "w1"
    assert matching["m3"] == "w2"


def test_gs_monte_carlo() -> None:
    """All random marriage instances produce stable matchings."""
    n, samples = 5, 500
    for seed in range(samples):
        _, _, mp, wp = generate_marriage(n, seed)
        matching = gale_shapley(mp, wp)
        assert is_stable_marriage(mp, wp, matching), f"unstable at seed {seed}"


# --- Irving ---


def test_irving_no_solution() -> None:
    """Classic 4-agent instance with no stable matching."""
    prefs = {
        "a1": ["a2", "a3", "a4"],
        "a2": ["a3", "a1", "a4"],
        "a3": ["a1", "a2", "a4"],
        "a4": ["a1", "a2", "a3"],
    }
    assert irving(prefs) is None


def test_irving_simple() -> None:
    """4-agent instance solved entirely in Phase 1."""
    prefs = {
        "a1": ["a2", "a3", "a4"],
        "a2": ["a1", "a3", "a4"],
        "a3": ["a4", "a1", "a2"],
        "a4": ["a3", "a1", "a2"],
    }
    matching = irving(prefs)
    assert matching is not None
    assert is_stable_roommates(prefs, matching)


def test_irving_6_agents() -> None:
    """6-agent instance requiring Phase 2 rotation elimination (Irving 1985)."""
    prefs = {
        "1": ["3", "4", "2", "6", "5"],
        "2": ["6", "5", "4", "1", "3"],
        "3": ["2", "4", "5", "1", "6"],
        "4": ["5", "2", "3", "6", "1"],
        "5": ["3", "2", "1", "6", "4"],
        "6": ["5", "1", "3", "4", "2"],
    }
    matching = irving(prefs)
    assert matching is not None
    assert is_stable_roommates(prefs, matching)


def test_irving_monte_carlo() -> None:
    """Verify any found roommate matching is stable."""
    n, samples = 6, 500
    found = 0
    for seed in range(samples):
        _, prefs = generate_roommates(n, seed)
        matching = irving(prefs)
        if matching is not None:
            found += 1
            assert is_stable_roommates(prefs, matching), f"unstable at seed {seed}"
    print(f"  Irving MC: {found}/{samples} solvable")


# --- Hedonic ---


def test_hedonic_example5() -> None:
    """Example 5 from the paper (5 agents, mixed coalition sizes)."""
    prefs: dict[str, list[Coalition]] = {
        "a1": [
            frozenset({"a1", "a4"}),
            frozenset({"a1", "a2", "a4"}),
            frozenset({"a1", "a3"}),
            frozenset({"a1", "a2", "a5"}),
            frozenset({"a1", "a2"}),
        ],
        "a2": [
            frozenset({"a2", "a1", "a5"}),
            frozenset({"a2", "a1", "a4"}),
            frozenset({"a2", "a1"}),
            frozenset({"a2", "a3"}),
        ],
        "a3": [
            frozenset({"a3", "a5"}),
            frozenset({"a3", "a1"}),
            frozenset({"a3", "a2"}),
            frozenset({"a3", "a4"}),
        ],
        "a4": [
            frozenset({"a4", "a3"}),
            frozenset({"a4", "a1", "a2"}),
            frozenset({"a4", "a1"}),
            frozenset({"a4", "a5"}),
        ],
        "a5": [
            frozenset({"a5", "a4"}),
            frozenset({"a5", "a1", "a2"}),
            frozenset({"a5", "a3"}),
        ],
    }
    solution = hedonic_solve(prefs)
    assert solution is not None
    assert is_stable_hedonic(prefs, solution)


def test_hedonic_monte_carlo() -> None:
    """Verify any found hedonic solution is core-stable."""
    n, samples = 6, 200
    failures = 0
    for seed in range(samples):
        _, prefs = generate_hedonic(n, seed)
        solution = hedonic_solve(prefs)
        if solution is not None and not is_stable_hedonic(prefs, solution):
            failures += 1
            print(f"  FAILURE at seed {seed}")
    print(f"  Hedonic MC: {samples - failures}/{samples} stable")
    assert failures == 0


# --- Cross-validation ---


def test_cross_marriage_hedonic() -> None:
    """Marriage instances: both GS and hedonic should produce stable solutions."""
    n, samples = 4, 200
    for seed in range(samples):
        _, _, mp, wp = generate_marriage(n, seed)
        gs_matching = gale_shapley(mp, wp)
        assert is_stable_marriage(mp, wp, gs_matching)

        hedonic_prefs: dict[str, list[Coalition]] = {}
        for m, plist in mp.items():
            hedonic_prefs[m] = [frozenset({m, w}) for w in plist]
        for w, plist in wp.items():
            hedonic_prefs[w] = [frozenset({w, m}) for m in plist]

        h_sol = hedonic_solve(hedonic_prefs)
        assert h_sol is not None, f"hedonic found no solution at seed {seed}"
        assert is_stable_hedonic(hedonic_prefs, h_sol)


def test_cross_roommates_hedonic() -> None:
    """Roommate instances: Irving and hedonic should agree on solvability."""
    n, samples = 4, 200
    for seed in range(samples):
        _, prefs = generate_roommates(n, seed)
        irving_result = irving(prefs)

        hedonic_prefs: dict[str, list[Coalition]] = {}
        for a, p in prefs.items():
            hedonic_prefs[a] = [frozenset({a, b}) for b in p]

        h_sol = hedonic_solve(hedonic_prefs)

        if irving_result is not None:
            assert is_stable_roommates(prefs, irving_result)
        if h_sol is not None:
            assert is_stable_hedonic(hedonic_prefs, h_sol)

        irv = irving_result is not None
        hed = h_sol is not None
        assert irv == hed, (
            f"disagreement at seed {seed}: "
            f"Irving={'yes' if irv else 'no'}, Hedonic={'yes' if hed else 'no'}"
        )


# --- Runner ---

ALL_TESTS = [
    test_gs_known,
    test_gs_monte_carlo,
    test_irving_no_solution,
    test_irving_simple,
    test_irving_6_agents,
    test_irving_monte_carlo,
    test_hedonic_example5,
    test_hedonic_monte_carlo,
    test_cross_marriage_hedonic,
    test_cross_roommates_hedonic,
]

if __name__ == "__main__":
    passed = failed = 0
    for test in ALL_TESTS:
        try:
            test()
            print(f"  PASS: {test.__name__}")
            passed += 1
        except Exception as e:
            print(f"  FAIL: {test.__name__}: {e}")
            failed += 1

    print(f"\n{passed} passed, {failed} failed")
    sys.exit(1 if failed else 0)
