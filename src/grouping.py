"""Hedonic Grouping Algorithm — stable coalition formation.

Reference implementation of the recursive two-phase algorithm:
  Phase 1 (Simplified Reduction): propose-hold with considerable test
  Phase 2 (Recursive Processing): forced move-on with recursion

Finds a group-stable partition or certifies that none exists.
Corresponds to Algorithm 4 in the paper, with Algorithms 2-3 as subroutines.
"""

from copy import deepcopy
from dataclasses import dataclass, field
from itertools import combinations
from typing import TypeAlias
from functools import reduce
import random

Agent: TypeAlias = str
Coalition: TypeAlias = frozenset[str]


@dataclass
class Proposal:
    """Tracked incoming proposal: which coalition, proposed by whom so far."""

    coalition: Coalition
    proposers: set[Agent]


@dataclass
class Problem:
    """Algorithm state: agents, preferences, and proposal tracking."""

    agents: list[Agent]
    preferences: dict[Agent, list[Coalition]]
    out_proposals: dict[Agent, list[Coalition]] = field(default_factory=dict)
    in_proposals: dict[Agent, list[Proposal]] = field(default_factory=dict)
    forced_moves: set[Coalition] = field(default_factory=set)

    @staticmethod
    def create(agents: list[Agent], prefs: dict[Agent, list[Coalition]]) -> "Problem":
        return Problem(
            agents=agents,
            preferences=prefs,
            out_proposals={a: [] for a in agents},
            in_proposals={a: [] for a in agents},
        )

    def solution(self) -> dict[Agent, Coalition] | None:
        """Extract grouping if solved (each agent has exactly one remaining pref)."""
        result: dict[Agent, Coalition] = {}
        for a in self.agents:
            if len(self.preferences[a]) != 1:
                return None
            result[a] = self.preferences[a][0]
        return result

    def does_agent_have_valid_outgoing_proposal(self, a: Agent) -> bool:
        for g in self.out_proposals[a]:
            if g not in self.forced_moves:
                return True
        return False

    def get_agent_top_unproposed_preference(self, a: Agent) -> Coalition | None:
        for g in self.preferences[a]:
            if g not in self.out_proposals[a]:
                return g

    def get_agent_remaining_preferences(self, a: Agent) -> list[Coalition]:
        return [g for g in self.preferences[a] if g not in self.out_proposals[a]]


def eliminate(problem: Problem, coalitions: list[Coalition]) -> None:
    """Remove coalitions from all preferences and proposal tracking (in-place)."""
    removal = set(coalitions)
    affected: frozenset[Agent] = reduce(frozenset.union, removal)
    for a in affected:
        problem.preferences[a] = [g for g in problem.preferences[a] if g not in removal]
        problem.out_proposals[a] = [
            g for g in problem.out_proposals[a] if g not in removal
        ]
        problem.in_proposals[a] = [
            p for p in problem.in_proposals[a] if p.coalition not in removal
        ]


def _receive_proposal(
    problem: Problem, receiver: Agent, coalition: Coalition, proposer: Agent
) -> None:
    """Process incoming proposal. Triggers elimination if it becomes considerable.

    A proposal is considerable (Definition 2) when all other members of the
    coalition have proposed it.
    """
    existing = None
    for p in problem.in_proposals[receiver]:
        if p.coalition == coalition:
            existing = p
            break

    if existing is None:
        existing = Proposal(coalition=coalition, proposers={proposer})
        problem.in_proposals[receiver].append(existing)
    else:
        existing.proposers.add(proposer)

    became_considerable = len(existing.proposers) >= len(coalition) - 1

    if became_considerable and coalition in problem.preferences[receiver]:
        rank = problem.preferences[receiver].index(coalition)
        worse = problem.preferences[receiver][rank + 1 :]
        if worse:
            eliminate(problem, worse)


def grouping(problem: Problem, exception: Coalition) -> Problem | None:
    """Recursive Grouping (Algorithm 4).

    Forces agents to move on from `exception`, then alternates:
      Phase 1: Simplified Reduction — propose best available, hold, eliminate
      Phase 2: Recursive Processing — force move-on, recurse

    Returns reduced Problem if stable solution found, None if unstable.
    """
    problem.forced_moves.add(exception)

    while True:
        # Phase 1: Simplified Reduction (Algorithm 2)
        progress = True
        while progress:
            progress = False
            for a in problem.agents:
                if problem.does_agent_have_valid_outgoing_proposal(a):
                    continue
                progress = True
                top_preference = problem.get_agent_top_unproposed_preference(a)
                if top_preference is None:
                    return None
                problem.out_proposals[a].append(top_preference)
                for b in top_preference - {a}:
                    _receive_proposal(problem, b, top_preference, a)

        # Phase 2: Recursive Processing (Algorithms 3-4)
        moved = False
        for a in problem.agents:
            remaining = problem.get_agent_remaining_preferences(a)
            if not remaining:
                continue
            moved = True
            k = problem.out_proposals[a][-1]
            result = grouping(deepcopy(problem), k)
            if result is None:
                eliminate(problem, remaining)
            else:
                return result
            break

        if not moved:
            return problem


def solve(
    agents: list[Agent], prefs: dict[Agent, list[Coalition]]
) -> dict[Agent, Coalition] | None:
    """Solve a hedonic grouping problem.

    Returns dict mapping each agent to their assigned coalition,
    or None if no stable grouping exists.
    """
    problem = Problem.create(agents, prefs)
    result = grouping(problem, frozenset())
    return result.solution() if result is not None else None


# --- Verification ---


def is_stable(
    agents: list[Agent],
    original_prefs: dict[Agent, list[Coalition]],
    solution: dict[Agent, Coalition] | None,
) -> bool:
    """Verify core stability: no blocking coalition exists."""
    if solution is None:
        return True
    for a in agents:
        assigned = solution[a]
        if assigned not in original_prefs[a]:
            return False
        rank = original_prefs[a].index(assigned)
        for better in original_prefs[a][:rank]:
            blocks = True
            for b in better:
                if b == a:
                    continue
                if (
                    better not in original_prefs[b]
                    or solution[b] not in original_prefs[b]
                ):
                    blocks = False
                    break
                if original_prefs[b].index(better) >= original_prefs[b].index(
                    solution[b]
                ):
                    blocks = False
                    break
            if blocks:
                return False
    return True


# --- Instance generation ---


def generate_random(
    n: int, seed: int | None = None
) -> tuple[list[Agent], dict[Agent, list[Coalition]]]:
    """Generate a random problem instance with n agents."""
    if seed is not None:
        random.seed(seed)
    agents = [f"a{i + 1}" for i in range(n)]
    all_coalitions = [
        frozenset(c) for r in range(2, n + 1) for c in combinations(agents, r)
    ]
    prefs: dict[Agent, list[Coalition]] = {}
    for a in agents:
        possible = [c for c in all_coalitions if a in c]
        random.shuffle(possible)
        prefs[a] = possible
    return agents, prefs


if __name__ == "__main__":
    # Example 5 from the paper
    agents = ["a1", "a2", "a3", "a4", "a5"]
    prefs: dict[str, list[frozenset[str]]] = {
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

    result = solve(agents, prefs)
    if result is None:
        print("No stable grouping exists")
    else:
        print("Stable grouping:")
        for a in agents:
            print(f"  {a} -> {sorted(result[a])}")
        print(f"Verified stable: {is_stable(agents, prefs, result)}")

    # Monte Carlo validation
    n = 6
    samps = 1000
    print(f"\nMonte Carlo (n={n}, {samps} random instances):")
    failures = 0
    for i in range(samps):
        a, p = generate_random(n)
        sol = solve(a, p)
        if sol is not None and not is_stable(a, p, sol):
            failures += 1
            print(f"  FAILURE at {i}")
    print(f"  {samps - failures}/{samps} stable")
