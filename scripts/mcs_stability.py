#!/usr/bin/env python3
"""Search for graphs G and edge sets F with MCS(G) and MCS(G xor F) disjoint.

MCS(G) is the set of all MCS orderings of G under arbitrary tie-breaking
(the set-valued semantics of `IsMCSOrderingAny` in the Lean development).

Modes:
  exhaustive  every graph on n vertices, every embedding of the pattern
  sample      random graphs on n vertices, random embeddings of the pattern

Update direction:
  ins    F is inserted into G (F disjoint from E(G))
  del    F is deleted from G (F contained in E(G))
  mixed  F is a matching flipped with at least one insertion and one deletion
"""

from __future__ import annotations

import argparse
import itertools
import random
import sys
from functools import lru_cache

PATTERNS: dict[str, list[tuple[int, int]]] = {
    "K2": [(0, 1)],
    "2K2": [(0, 1), (2, 3)],
    "3K2": [(0, 1), (2, 3), (4, 5)],
    "P3": [(0, 1), (1, 2)],
    "K1,3": [(0, 1), (0, 2), (0, 3)],
    "K1,4": [(0, 1), (0, 2), (0, 3), (0, 4)],
    "P3+K2": [(0, 1), (1, 2), (3, 4)],
    "K1,3+K2": [(0, 1), (0, 2), (0, 3), (4, 5)],
    "P3+2K2": [(0, 1), (1, 2), (3, 4), (5, 6)],
    "K3": [(0, 1), (1, 2), (0, 2)],
    "P4": [(0, 1), (1, 2), (2, 3)],
    "2P3": [(0, 1), (1, 2), (3, 4), (4, 5)],
    "C4": [(0, 1), (1, 2), (2, 3), (3, 0)],
    "P5": [(0, 1), (1, 2), (2, 3), (3, 4)],
    "S211": [(0, 1), (1, 2), (0, 3), (0, 4)],
    "K3+K2": [(0, 1), (1, 2), (0, 2), (3, 4)],
}
SAMPLE_EDGE_DENSITIES = (0.2, 0.35, 0.5, 0.65)
DEFAULT_SEED = 1


def adjacency(n: int, edges: frozenset[tuple[int, int]]) -> tuple[int, ...]:
    rows = [0] * n
    for x, y in edges:
        rows[x] |= 1 << y
        rows[y] |= 1 << x
    return tuple(rows)


@lru_cache(maxsize=None)
def mcs_orders(n: int, rows: tuple[int, ...]) -> frozenset[tuple[int, ...]]:
    """All MCS orderings (any tie-break) of the graph with bitmask rows."""
    found: set[tuple[int, ...]] = set()
    full = (1 << n) - 1

    def extend(chosen: int, prefix: list[int]) -> None:
        if chosen == full:
            found.add(tuple(prefix))
            return
        counts = [(bin(rows[w] & chosen).count("1"), w) for w in range(n) if not chosen >> w & 1]
        best = max(c for c, _ in counts)
        for c, w in counts:
            if c == best:
                prefix.append(w)
                extend(chosen | 1 << w, prefix)
                prefix.pop()

    extend(0, [])
    return frozenset(found)


def is_matching(edges: frozenset[tuple[int, int]]) -> bool:
    ends = [v for e in edges for v in e]
    return len(ends) == len(set(ends))


def embeddings(n: int, pattern: list[tuple[int, int]]) -> set[frozenset[tuple[int, int]]]:
    k = max(max(e) for e in pattern) + 1
    return {
        frozenset(tuple(sorted((perm[x], perm[y]))) for x, y in pattern)
        for perm in itertools.permutations(range(n), k)
    }


def update_pair(g: frozenset, f: frozenset, mode: str) -> tuple[frozenset, frozenset] | None:
    """Return (before, after) edge sets, or None if f does not fit the mode."""
    inside = f & g
    if mode == "ins":
        return (g, g | f) if not inside else None
    if mode == "del":
        return (g, g - f) if inside == f else None
    if mode == "mixed":
        if not is_matching(f) or not inside or inside == f:
            return None
        return (g, g ^ f)
    raise ValueError(f"unknown mode {mode!r}")


def disjoint(n: int, before: frozenset, after: frozenset) -> bool:
    return not (mcs_orders(n, adjacency(n, before)) & mcs_orders(n, adjacency(n, after)))


def run_exhaustive(n: int, pattern: list[tuple[int, int]], mode: str):
    all_pairs = list(itertools.combinations(range(n), 2))
    fs = embeddings(n, pattern)
    tested = failures = 0
    witness = None
    for mask in range(1 << len(all_pairs)):
        g = frozenset(p for i, p in enumerate(all_pairs) if mask >> i & 1)
        for f in fs:
            pair = update_pair(g, f, mode)
            if pair is None:
                continue
            tested += 1
            if disjoint(n, *pair):
                failures += 1
                witness = witness or (sorted(g), sorted(f))
    return tested, failures, witness


def run_sample(n: int, pattern: list[tuple[int, int]], mode: str, trials: int, rng: random.Random):
    all_pairs = list(itertools.combinations(range(n), 2))
    fs = sorted(embeddings(n, pattern), key=sorted)
    tested = failures = 0
    witness = None
    while tested < trials:
        f = rng.choice(fs)
        density = rng.choice(SAMPLE_EDGE_DENSITIES)
        g = frozenset(p for p in all_pairs if rng.random() < density)
        pair = update_pair(g, f, mode)
        if pair is None:
            continue
        tested += 1
        if disjoint(n, *pair):
            failures += 1
            witness = witness or (sorted(g), sorted(f))
    return tested, failures, witness


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--n", type=int, required=True, help="number of vertices")
    parser.add_argument("--pattern", choices=sorted(PATTERNS), required=True)
    parser.add_argument("--mode", choices=("ins", "del", "mixed"), required=True)
    parser.add_argument("--sample", type=int, default=0, help="number of random trials (0 = exhaustive)")
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    args = parser.parse_args(argv)

    pattern = PATTERNS[args.pattern]
    if max(max(e) for e in pattern) + 1 > args.n:
        parser.error(f"pattern {args.pattern} needs more than n={args.n} vertices")

    if args.sample > 0:
        tested, failures, witness = run_sample(args.n, pattern, args.mode, args.sample, random.Random(args.seed))
        kind = f"sample({args.sample}, seed={args.seed})"
    else:
        tested, failures, witness = run_exhaustive(args.n, pattern, args.mode)
        kind = "exhaustive"
    print(f"n={args.n} pattern={args.pattern} mode={args.mode} {kind}: "
          f"{failures}/{tested} disjoint; witness G,F = {witness}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
