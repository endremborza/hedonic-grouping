"""Shared fixtures: hand-crafted edge-case instances."""

import pytest

from ..generators import HedonicProfile, RmpProfile, SmpProfile


@pytest.fixture
def gs_3x3() -> SmpProfile:
    """3x3 SMP whose proposer-optimal matching is m1->w3, m2->w1, m3->w2."""
    return (
        {
            "m1": ["w1", "w2", "w3"],
            "m2": ["w1", "w3", "w2"],
            "m3": ["w2", "w1", "w3"],
        },
        {
            "w1": ["m2", "m1", "m3"],
            "w2": ["m3", "m1", "m2"],
            "w3": ["m1", "m2", "m3"],
        },
    )


@pytest.fixture
def irving_no_solution() -> RmpProfile:
    """Classic 4-agent RMP with no stable matching."""
    return {
        "a1": ["a2", "a3", "a4"],
        "a2": ["a3", "a1", "a4"],
        "a3": ["a1", "a2", "a4"],
        "a4": ["a1", "a2", "a3"],
    }


@pytest.fixture
def irving_6_agents() -> RmpProfile:
    """6-agent RMP requiring Phase 2 rotation elimination (Irving 1985)."""
    return {
        "1": ["3", "4", "2", "6", "5"],
        "2": ["6", "5", "4", "1", "3"],
        "3": ["2", "4", "5", "1", "6"],
        "4": ["5", "2", "3", "6", "1"],
        "5": ["3", "2", "1", "6", "4"],
        "6": ["5", "1", "3", "4", "2"],
    }


@pytest.fixture
def hedonic_example5() -> HedonicProfile:
    """Example 5 from the paper: 5 agents, mixed coalition sizes."""
    return {
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
