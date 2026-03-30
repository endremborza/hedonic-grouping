"""Tests for all stable matching algorithms.

Run: python -m src.test_algorithms
"""

import sys
from itertools import combinations

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
    """Marriage instances: both GS and hedonic should produce the SAME stable solutions."""
    n, samples = 4, 100
    for seed in range(samples):
        men, women, mp, wp = generate_marriage(n, seed)
        gs_matching = gale_shapley(mp, wp)

        # Hedonic prefs: men first to match GS proposer-optimality
        hedonic_prefs: dict[str, list[Coalition]] = {}
        for m in men:
            hedonic_prefs[m] = [frozenset({m, w}) for w in mp[m]]
        for w in women:
            hedonic_prefs[w] = [frozenset({w, m}) for m in wp[w]]

        h_sol = hedonic_solve(hedonic_prefs)
        assert h_sol is not None, f"hedonic found no solution at seed {seed}"

        # Compare results
        for m in men:
            h_partner = h_sol[m] - {m}
            assert len(h_partner) == 1
            w = list(h_partner)[0]
            assert gs_matching[m] == w, f"Mismatch at seed {seed}: GS={gs_matching[m]}, Hedonic={w}"


def test_cross_roommates_hedonic() -> None:
    """Roommate instances: Irving and hedonic should agree on solvability and solutions."""
    n, samples = 4, 100
    for seed in range(samples):
        agents, prefs = generate_roommates(n, seed)
        irving_result = irving(prefs)

        hedonic_prefs: dict[str, list[Coalition]] = {}
        for a in agents:
            hedonic_prefs[a] = [frozenset({a, b}) for b in prefs[a]]

        h_sol = hedonic_solve(hedonic_prefs)

        if irving_result is not None:
            assert h_sol is not None, f"Irving found solution, Hedonic did not at seed {seed}"
            for a in agents:
                h_partner = h_sol[a] - {a}
                assert len(h_partner) == 1
                b = list(h_partner)[0]
                assert irving_result[a] == b, f"Mismatch at seed {seed}: Irving={irving_result[a]}, Hedonic={b}"
        else:
            assert h_sol is None, f"Irving found no solution, Hedonic found {h_sol} at seed {seed}"


def test_college_admissions() -> None:
    """College admissions (many-to-one) represented as a hedonic problem.

    NOTE: This is computationally expensive due to combinatorial explosion.
    A college with quota q and n students generates sum(C(n, k) for k in 1..q) coalitions.
    """
    colleges = {"C1": 2, "C2": 1}
    students = ["S1", "S2", "S3"]

    # Student prefs: order of colleges
    s_prefs = {
        "S1": ["C1", "C2"],
        "S2": ["C2", "C1"],
        "S3": ["C1", "C2"],
    }

    # College prefs: order of individual students
    # (Assuming responsive preferences for the hedonic translation)
    c_prefs = {
        "C1": ["S1", "S2", "S3"],
        "C2": ["S1", "S2", "S3"],
    }

    hedonic_prefs: dict[str, list[Coalition]] = {}

    # Translate student prefs
    for s, pref in s_prefs.items():
        # Students care only about which college they are in, not who else is there
        # In this limited implementation, we must enumerate ALL possible coalitions
        # that include this student and the preferred college.
        h_pref = []
        for c_name in pref:
            quota = colleges[c_name]
            other_students = [other for other in students if other != s]
            # All combinations of other students that fit in the quota
            for r in range(quota):
                for combo in combinations(other_students, r):
                    h_pref.append(frozenset({s, c_name} | set(combo)))
        hedonic_prefs[s] = h_pref

    # Translate college prefs (using responsive preferences over sets)
    for c, pref in c_prefs.items():
        quota = colleges[c]
        h_pref = []
        # Simplified: college prefers larger groups of better students
        for r in range(quota, 0, -1):
            for combo in combinations(pref, r):
                h_pref.append(frozenset({c} | set(combo)))
        hedonic_prefs[c] = h_pref

    solution = hedonic_solve(hedonic_prefs)
    assert solution is not None
    assert is_stable_hedonic(hedonic_prefs, solution)
    print(f"  College admissions solution: {solution}")


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
    test_college_admissions,
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
