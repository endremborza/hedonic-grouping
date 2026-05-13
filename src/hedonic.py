"""Hedonic grouping algorithm — stable coalition formation.

Reference implementation of the recursive two-phase algorithm (Algorithm 4):
  Phase 1 (Simplified Reduction): propose-hold with considerable test
  Phase 2 (Recursive Processing): forced move-on with recursion

Finds a group-stable partition or certifies that none exists.
This is the general case; Gale-Shapley (bipartite size-2) and Irving
(non-bipartite size-2) are special cases proven equivalent in the paper.

Note on college admissions: The many-to-one matching problem (colleges with
quotas) is subsumed by this framework — each coalition includes a college and
a student subset. The exponential blowup in equivalent coalitions (C(n,q) per
college with quota q) makes the general algorithm impractical for this case.
Specialized algorithms (college-proposing GS, Roth-Peranson) exploit the
structure for polynomial solutions.
"""

from copy import deepcopy
from dataclasses import dataclass, field
from enum import Enum
from functools import reduce

from .common import Agent, Coalition, is_stable_hedonic


class _Stage(Enum):
    INIT = 0
    PHASE1 = 1
    AWAITING_CHILD = 2


@dataclass
class _Proposal:
    coalition: Coalition
    proposers: set[Agent]


@dataclass
class _Problem:
    agents: list[Agent]
    preferences: dict[Agent, list[Coalition]]
    out_proposals: dict[Agent, list[Coalition]] = field(default_factory=dict)
    in_proposals: dict[Agent, list[_Proposal]] = field(default_factory=dict)
    forced_moves: set[Coalition] = field(default_factory=set)

    @staticmethod
    def create(agents: list[Agent], prefs: dict[Agent, list[Coalition]]) -> "_Problem":
        return _Problem(
            agents=agents,
            preferences=deepcopy(prefs),
            out_proposals={a: [] for a in agents},
            in_proposals={a: [] for a in agents},
        )

    def solution(self) -> dict[Agent, Coalition] | None:
        result: dict[Agent, Coalition] = {}
        for a in self.agents:
            if not self.out_proposals[a]:
                return None
            result[a] = self.out_proposals[a][-1]
        for a, g in result.items():
            for member in g:
                if result.get(member) != g:
                    return None
        return result

    def has_valid_proposal(self, a: Agent) -> bool:
        return any(g not in self.forced_moves for g in self.out_proposals[a])

    def top_unproposed(self, a: Agent) -> Coalition | None:
        for g in self.preferences[a]:
            if g not in self.out_proposals[a]:
                return g
        return None

    def remaining_prefs(self, a: Agent) -> list[Coalition]:
        return [g for g in self.preferences[a] if g not in self.out_proposals[a]]


@dataclass
class _Frame:
    problem: _Problem
    exception: Coalition
    stage: _Stage = _Stage.INIT
    pending_remaining: list[Coalition] = field(default_factory=list)


def _eliminate(problem: _Problem, coalitions: list[Coalition]) -> None:
    removal = set(coalitions)
    if not removal:
        return
    affected: frozenset[Agent] = reduce(frozenset.union, removal)

    def _filter_list(li: list):
        return [e for e in li if e not in removal]

    for a in affected:
        problem.preferences[a] = _filter_list(problem.preferences[a])
        problem.out_proposals[a] = _filter_list(problem.out_proposals[a])
        problem.in_proposals[a] = [
            p for p in problem.in_proposals[a] if p.coalition not in removal
        ]


def _is_considerable(proposal: _Proposal, receiver: Agent, problem: _Problem):
    return (
        len(proposal.proposers) >= len(proposal.coalition) - 1
        and proposal.coalition in problem.preferences[receiver]
    )


def _receive_proposal(
    problem: _Problem, receiver: Agent, coalition: Coalition, proposer: Agent
) -> None:
    existing = next(
        (p for p in problem.in_proposals[receiver] if p.coalition == coalition), None
    )
    if existing is None:
        existing = _Proposal(coalition=coalition, proposers={proposer})
        problem.in_proposals[receiver].append(existing)
    else:
        existing.proposers.add(proposer)

    # If this proposal is considerable, eliminate worse options for the receiver
    if _is_considerable(existing, receiver, problem):
        # 1. If we (the receiver) already hold something BETTER that is also considerable,
        # then this new one should be eliminated immediately.
        rank = problem.preferences[receiver].index(coalition)
        for p in problem.in_proposals[receiver]:
            if p.coalition == coalition:
                continue
            if _is_considerable(p, receiver, problem):
                if problem.preferences[receiver].index(p.coalition) < rank:
                    _eliminate(problem, [coalition])
                    return

        # 2. Otherwise, eliminate everything worse than this new considerable proposal.
        # this never actually should happen
        worse = problem.preferences[receiver][rank + 1 :]
        if worse:
            _eliminate(problem, worse)


def _grouping(
    problem: _Problem,
    exception: Coalition,
    original_prefs: dict[Agent, list[Coalition]],
) -> _Problem | None:
    problem.forced_moves.add(exception)

    while True:
        # Phase 1: Simplified Reduction
        progress = True
        while progress:
            progress = False
            for a in problem.agents:
                if problem.has_valid_proposal(a):
                    continue
                progress = True
                top = problem.top_unproposed(a)
                if top is None:
                    return None
                problem.out_proposals[a].append(top)
                for b in top - {a}:
                    _receive_proposal(problem, b, top, a)

        # Check if current state is already a stable solution
        sol = problem.solution()
        from .common import is_stable_hedonic

        if sol and is_stable_hedonic(original_prefs, sol):
            # Finalize preferences to match solution
            for a in problem.agents:
                problem.preferences[a] = [sol[a]]
            return problem

        # Phase 2: Recursive Processing
        moved = False
        for a in problem.agents:
            remaining = problem.remaining_prefs(a)
            if not remaining:
                continue
            moved = True
            k = problem.out_proposals[a][-1]
            result = _grouping(deepcopy(problem), k, original_prefs)
            if result is None:
                _eliminate(problem, remaining)
            else:
                return result
            break

        if not moved:
            return problem


def _phase1(problem: _Problem) -> bool:
    """Run proposal-rejection to quiescence. Returns False iff exhausted."""
    progress = True
    while progress:
        progress = False
        for a in problem.agents:
            if problem.has_valid_proposal(a):
                continue
            progress = True
            top = problem.top_unproposed(a)
            if top is None:
                return False
            problem.out_proposals[a].append(top)
            for b in top - {a}:
                _receive_proposal(problem, b, top, a)
    return True


def solve(prefs: dict[Agent, list[Coalition]]) -> dict[Agent, Coalition] | None:
    """Solve a hedonic grouping problem.

    Returns dict mapping each agent to their assigned coalition,
    or None if no stable grouping exists.
    """
    agents = list(prefs)
    problem = _Problem.create(agents, prefs)
    result = _grouping(problem, frozenset(), prefs)
    return result.solution() if result is not None else None


def solve_iterative(
    prefs: dict[Agent, list[Coalition]],
) -> dict[Agent, Coalition] | None:
    agents = list(prefs)
    initial = _Problem.create(agents, prefs)
    stack: list[_Frame] = [_Frame(problem=initial, exception=frozenset())]
    last: _Problem | None = None

    while stack:
        frame = stack[-1]

        if frame.stage is _Stage.INIT:
            frame.problem.forced_moves.add(frame.exception)
            frame.stage = _Stage.PHASE1

        if frame.stage is _Stage.PHASE1:
            if not _phase1(frame.problem):
                stack.pop()
                last = None
                continue

            sol = frame.problem.solution()
            if sol is not None and is_stable_hedonic(prefs, sol):
                for a in frame.problem.agents:
                    frame.problem.preferences[a] = [sol[a]]
                stack.pop()
                last = frame.problem
                continue

            pivot: Agent | None = None
            for a in frame.problem.agents:
                if frame.problem.remaining_prefs(a):
                    pivot = a
                    break

            if pivot is None:
                stack.pop()
                last = frame.problem
                continue

            frame.pending_remaining = frame.problem.remaining_prefs(pivot)
            k = frame.problem.out_proposals[pivot][-1]
            stack.append(_Frame(problem=deepcopy(frame.problem), exception=k))
            frame.stage = _Stage.AWAITING_CHILD
            continue

        if frame.stage is _Stage.AWAITING_CHILD:
            if last is None:
                _eliminate(frame.problem, frame.pending_remaining)
                frame.stage = _Stage.PHASE1
                continue
            stack.pop()

    return last.solution() if last is not None else None
