#!/usr/bin/env python3
"""Incomparability witness for MCS and LexBFS (all tie-breaks).

Enumerates the complete families of Maximum-Cardinality-Search (MCS) and
lexicographic-BFS (LexBFS) vertex orderings of a fixed chordal 7-vertex
witness graph, over *all* tie-break choices, and reports the two family sizes
and their symmetric difference.

The witness (chordal, 7 vertices) is a 5-clique on {1,2,3,4,5}, plus a vertex
`u` joined only to `1`, plus a vertex `v` joined only to `2` and `3`.  This is
the graph cited in the paper's related-work section: it shows the MCS and
LexBFS ordering families are incomparable (neither contains the other) even on
chordal graphs -- a fact consistent with Corneil--Krueger (2008), that both
searches are restrictions of maximal neighborhood search.

Expected output: 204 MCS orderings, 204 LexBFS orderings, symmetric difference
40 on each side (|MCS \\ LexBFS| = |LexBFS \\ MCS| = 40).

Exits non-zero if the counts do not match, so it can be used as a regression
check.

Standard library only.
"""

from __future__ import annotations

import sys

# Vertices are 0-indexed here; the paper's prose is 1-indexed.
# 5-clique on {0,1,2,3,4}; u=5 joined to 0; v=6 joined to 1 and 2.
N = 7
EDGES = (
    [(i, j) for i in range(5) for j in range(i + 1, 5)]  # clique on 0..4
    + [(5, 0)]            # u joined to vertex 1
    + [(6, 1), (6, 2)]    # v joined to vertices 2 and 3
)


def adjacency(n: int, edges: list[tuple[int, int]]) -> list[set[int]]:
    adj: list[set[int]] = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def all_mcs_orderings(n: int, adj: list[set[int]]) -> set[tuple[int, ...]]:
    """Every MCS ordering, exploring all maximal-cardinality tie-breaks."""
    results: set[tuple[int, ...]] = set()

    def rec(chosen: tuple[int, ...], card: list[int]) -> None:
        if len(chosen) == n:
            results.add(chosen)
            return
        remaining = [w for w in range(n) if w not in chosen]
        best = max(card[w] for w in remaining)
        for w in remaining:
            if card[w] != best:
                continue
            nxt = card[:]
            for x in adj[w]:
                if x not in chosen:
                    nxt[x] += 1
            rec(chosen + (w,), nxt)

    rec((), [0] * n)
    return results


def all_lexbfs_orderings(n: int, adj: list[set[int]]) -> set[tuple[int, ...]]:
    """Every LexBFS ordering, exploring all lexicographic tie-breaks.

    Labels are tuples of position indices, prepended each step; the next vertex
    is one with the lexicographically maximum label.
    """
    results: set[tuple[int, ...]] = set()

    def rec(chosen: tuple[int, ...], labels: list[tuple[int, ...]]) -> None:
        if len(chosen) == n:
            results.add(chosen)
            return
        remaining = [w for w in range(n) if w not in chosen]
        best = max(labels[w] for w in remaining)
        pos = len(chosen)
        for w in remaining:
            if labels[w] != best:
                continue
            nxt = labels[:]
            for x in adj[w]:
                if x not in chosen:
                    nxt[x] = (pos,) + nxt[x]
            rec(chosen + (w,), nxt)

    rec((), [() for _ in range(n)])
    return results


def main() -> int:
    adj = adjacency(N, EDGES)
    mcs = all_mcs_orderings(N, adj)
    lexbfs = all_lexbfs_orderings(N, adj)
    only_mcs = mcs - lexbfs
    only_lexbfs = lexbfs - mcs

    print(f"witness: n={N}, chordal, edges={sorted(EDGES)}")
    print(f"  MCS orderings   : {len(mcs)}")
    print(f"  LexBFS orderings: {len(lexbfs)}")
    print(f"  symmetric difference: {len(only_mcs)} (MCS-only), "
          f"{len(only_lexbfs)} (LexBFS-only)")

    ok = (len(mcs) == 204 and len(lexbfs) == 204
          and len(only_mcs) == 40 and len(only_lexbfs) == 40)
    if not ok:
        print("FAIL: counts do not match the documented 204/204/40 witness")
        return 1
    print("PASS: 204/204 with symmetric difference 40 on each side")
    return 0


if __name__ == "__main__":
    sys.exit(main())
