#!/usr/bin/env python3
"""High-n cross-check for the proven dynamic-MCS candidate.

The search's bounded verifier only tests graphs of size n=2..5
(verifier.py bound_n_max=5). The Lean proof covers all n but proves the
Lean *encoding*, not that the encoding equals this Python candidate.

This script closes that gap empirically: it runs the ACTUAL candidate
module on large random graphs (n up to --nmax, default 200), and after
every edge flip independently checks two things:

  1. VALID: the candidate's ordering is a legal MCS ordering of the
     current graph (each pick has maximal chosen-neighbor count). This
     re-derives cardinalities from the graph, independent of the
     candidate's own logic.
  2. EXACT: the ordering equals a from-scratch offline MCS (deterministic
     tie-break by lowest id). This catches any drift between the dynamic
     update and the formalization's assumption of the greedy rule.

A single failure prints the counterexample and exits non-zero.
"""

from __future__ import annotations

import argparse
import importlib.util
import random
import sys
from pathlib import Path

import numpy as np


def load_candidate(path: Path):
    spec = importlib.util.spec_from_file_location("candidate", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    for fn in ("init", "insert_edge", "delete_edge"):
        if not hasattr(mod, fn):
            raise AttributeError(f"candidate missing {fn}")
    return mod


def candidate_order(state):
    """The maintained ordering, under either documented state key.

    Candidates expose their ordering as ``order`` (the adopted bitmask
    candidate, gen003_c02) or ``ordering`` (the earlier list-based candidates,
    gen001_c01).
    """
    if "order" in state:
        return state["order"]
    return candidate_order(state)


def offline_mcs(graph: np.ndarray) -> list[int]:
    """From-scratch deterministic MCS (the oracle)."""
    n = graph.shape[0]
    chosen: set[int] = set()
    card = [0] * n
    order: list[int] = []
    for _ in range(n):
        unchosen = [u for u in range(n) if u not in chosen]
        if not unchosen:
            break
        max_card = max(card[u] for u in unchosen)
        v = min(u for u in unchosen if card[u] == max_card)
        order.append(v)
        chosen.add(v)
        for u in range(n):
            if graph[v, u] == 1 and u not in chosen:
                card[u] += 1
    return order


def is_valid_mcs(graph: np.ndarray, order: list[int]) -> bool:
    """Independent validity check: each pick is a maximal-cardinality vertex."""
    n = graph.shape[0]
    if len(order) != n or set(order) != set(range(n)):
        return False
    chosen: set[int] = set()
    card = [0] * n
    for v in order:
        unchosen = [u for u in range(n) if u not in chosen]
        if not unchosen:
            return False
        max_card = max(card[u] for u in unchosen)
        if card[v] != max_card:
            return False
        chosen.add(v)
        for u in range(n):
            if graph[v, u] == 1 and u not in chosen:
                card[u] += 1
    return True


def graph_to_matrix(graph: list[list[int]]) -> np.ndarray:
    return np.array(graph, dtype=np.int8)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--candidate",
                    default=str(Path(__file__).resolve().parent / "candidates" / "gen003_c02.py"))
    ap.add_argument("--nmax", type=int, default=200)
    ap.add_argument("--nmin", type=int, default=6)
    ap.add_argument("--graphs-per-n", type=int, default=8)
    ap.add_argument("--flips-per-graph", type=int, default=40)
    ap.add_argument("--edge-prob", type=float, default=0.3)
    ap.add_argument("--seed", type=int, default=20260919)
    args = ap.parse_args()

    cand_path = Path(args.candidate)
    if not cand_path.exists():
        print(f"candidate not found: {cand_path}", file=sys.stderr)
        return 2
    cand = load_candidate(cand_path)
    rng = random.Random(args.seed)

    total_checks = 0
    total_flips = 0
    ns = list(range(args.nmin, args.nmax + 1, max(1, (args.nmax - args.nmin) // 12)))
    if args.nmax not in ns:
        ns.append(args.nmax)

    for n in ns:
        for g in range(args.graphs_per_n):
            # random undirected graph as adjacency matrix
            adj = np.zeros((n, n), dtype=np.int8)
            for i in range(n):
                for j in range(i + 1, n):
                    if rng.random() < args.edge_prob:
                        adj[i, j] = adj[j, i] = 1
            init_graph = adj.tolist()

            state = cand.init(init_graph)
            if not is_valid_mcs(adj, candidate_order(state)):
                print(f"FAIL init: n={n} graph#{g} produced invalid MCS ordering")
                return 1
            if candidate_order(state) != offline_mcs(adj):
                print(f"FAIL init exact: n={n} graph#{g} != from-scratch MCS")
                return 1
            total_checks += 1

            for f in range(args.flips_per_graph):
                u = rng.randrange(n)
                v = rng.randrange(n)
                if u == v:
                    continue
                op = "insert" if rng.random() < 0.5 else "delete"
                if op == "insert":
                    adj[u, v] = adj[v, u] = 1
                    state = cand.insert_edge(graph_to_matrix(adj).tolist(), (u, v), state)
                else:
                    adj[u, v] = adj[v, u] = 0
                    state = cand.delete_edge(graph_to_matrix(adj).tolist(), (u, v), state)
                total_flips += 1

                if not is_valid_mcs(adj, candidate_order(state)):
                    print(f"FAIL: n={n} graph#{g} flip#{f} {op} ({u},{v}) -> invalid MCS")
                    print(f"  ordering={state['ordering']}")
                    return 1
                if candidate_order(state) != offline_mcs(adj):
                    print(f"FAIL exact: n={n} graph#{g} flip#{f} {op} ({u},{v}) != from-scratch MCS")
                    print(f"  dynamic ={state['ordering']}")
                    print(f"  offline ={offline_mcs(adj)}")
                    return 1
                total_checks += 1

        print(f"  n<= {n:>3}: {total_checks} checks, {total_flips} flips, all valid + exact")

    print(f"\nPASS: {total_checks} invariant checks, {total_flips} edge flips, "
          f"n up to {args.nmax}. Candidate matches from-scratch MCS exactly.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
