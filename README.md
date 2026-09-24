# Dynamic MCS Ordering Maintenance

A machine-checked (Lean 4 / Mathlib) formalization of maintaining a
**Maximum-Cardinality-Search (MCS)** vertex ordering under single-edge
insertions and deletions, with a verified executable implementation, a
locality analysis, a unit-cost complexity model, and a stability-boundary
result with certified counterexamples.

**Authors:** Md Thoriqul Islam Thonmay, Gregory Morse (ELTE).
**License:** Apache-2.0.

---

## What is MCS?

Maximum Cardinality Search is a graph traversal introduced by Tarjan and
Yannakakis (1984). It numbers vertices from 1 to *n* by repeatedly selecting
the unnumbered vertex with the most already-numbered neighbours, breaking ties
by lowest index. On a chordal graph, the reverse of any MCS ordering is a
perfect elimination ordering, which gives a linear-time chordality test. MCS
is simpler and faster than the lexicographic breadth-first search (LexBFS) of
Rose, Tarjan and Lueker (1976), though it produces a superset of LexBFS
orderings.

This formalization studies the *dynamic* problem: given an MCS ordering of a
graph, can we update it efficiently after a single edge insertion or deletion,
rather than recomputing from scratch?

## Result

On a loop-free undirected graph, the update proceeds by a **probe-then-repair**
strategy: scan the window between the two endpoints for the first step whose
old choice is no longer a legal MCS pick, and only then re-greedy the suffix.
The formalization proves, for every graph size `n`:

- **Correctness.** Every order produced is a valid MCS ordering of the updated
  graph, and equals the from-scratch canonical ordering (which is unique).
- **Locality.** Inside an insertion window the old choice breaks exactly when
  the later endpoint now beats it; outside the window positions stay legal. For
  deletions, positions on either side of the endpoints remain legal. The
  update is the identity exactly when the order is already canonical for the
  new graph.
- **Verified executable.** A boolean-adjacency implementation
  (`execInsertUpdate` / `execDeleteUpdate`) is proved to refine the abstract
  update.
- **Unit cost.** Instrumented versions count legality checks and pick steps
  along the real control flow: at most `n` for an insertion and `n + 1` for a
  deletion. The worst case therefore **matches static recomputation** — no
  asymptotic separation over recomputing from scratch is claimed.
- **Stability boundary.** If the neighbour count of every vertex in one graph
  exceeds that in the other by at most one along every chosen prefix, the two
  graphs share an MCS ordering. In particular, inserting or deleting a
  *matching*, or flipping a single edge, always preserves a common MCS
  ordering. This hypothesis is tight: inserting a triangle, inserting a
  `P_4`, or a mixed matching update (one insert + one delete) can each destroy
  every common ordering — certified by kernel `decide` on explicit small
  instances.

## Theorem map

The Palomar comparator contract is the 34-name list in
[`comparator.json`](comparator.json). Each name is a real theorem in
[`Solution.lean`](Solution.lean) with a matching `sorry` statement in
[`Challenge.lean`](Challenge.lean). Both files are generated from a single
source of truth ([`scripts/gen_comparator_wrappers.py`](scripts/gen_comparator_wrappers.py))
so the posed and proved types stay textually identical.

| Category | Theorems |
|---|---|
| Correctness | `init_valid`, `insert_update_valid`, `delete_update_valid`, `greedySuffix_full`, `update_from_prefix` |
| Uniqueness / update = recompute | `IsMCSOrdering_unique`, `insert_update_eq_initOrder`, `delete_update_eq_initOrder` |
| Locality | `legal_upto_earlierPos`, `legal_after_laterPos`, `delete_legal_between`, `insert_break_iff`, `insert_update_eq_self_iff`, `delete_update_eq_self_iff` |
| Executable refinement | `exec_insert_update_eq`, `exec_delete_update_eq` |
| Unit cost | `exec_insert_cost_le`, `exec_delete_cost_le`, `exec_insert_cost_of_no_break`, `exec_delete_cost_of_no_break`, `exec_insert_cost_of_break`, `exec_delete_cost_of_break` |
| Executable bridge | `setEdge_preserves_symm`, `setEdge_preserves_loopless`, `mcsOrder_eq_greedySuffix`, `exec_insert_valid`, `exec_delete_valid` |
| Stability | `exists_common_ordering`, `insert_matching_common_order`, `delete_matching_common_order`, `flip_common_order` |
| Stability obstructions | `triangle_no_common_order`, `p4_no_common_order`, `mixed_matching_no_common_order` |

All 34 theorems audit to only the three standard Lean axioms:
`propext`, `Quot.sound`, `Classical.choice` (no `sorry`, no `native_decide`).

## Repository layout

```
Challenge.lean            Posed statements (sorry bodies) + canonical definitions
Solution.lean             Proved versions of every comparator theorem
AxiomAudit.lean           #print axioms for each comparator theorem
ThesisLean/
  ChallengeDefs.lean      Canonical definitions (byte-identical to Challenge.lean DEFS block)
  Correctness.lean        Uniqueness, locality, update = recompute
  ExecUpdate.lean         Executable updates, refinement proofs, unit-cost model
  Stability.lean          Common-ordering theorem, matching corollaries, obstructions
  Exec.lean, ExecFlip.lean, ExecBridge.lean, McsInvariant.lean,
  CardBridge.lean, BridgeSteps.lean, BridgeParts{A,B,C}.lean,
  BridgeAssembly.lean, SolutionBridge.lean
                          Executable layer and transport lemmas to the abstract model
  Formal_gen001c01_*.lean, Formal_gen003c01_*.lean
                          Core DynamicMCS development (graph searches, updates, validity)
scripts/
  check_challenge_defs.sh  Verify Challenge.lean DEFS block matches ChallengeDefs.lean
  check_axioms.sh          Axiom audit for all comparator theorems
  gen_comparator_wrappers.py  Single-source generator for comparator blocks
  mcs_stability.py         Exhaustive stability harness (cross-check for counterexamples)
```

## Build and verify

Requires Lean `v4.35.0-rc2` (see [`lean-toolchain`](lean-toolchain)) and Mathlib.

```bash
lake exe cache get && lake build          # build everything (8975 jobs)
bash scripts/check_challenge_defs.sh      # Challenge.lean defs match ChallengeDefs.lean
bash scripts/check_axioms.sh              # all theorems use only propext/Quot.sound/Classical.choice
```

The CI workflow (`.github/workflows/lean_action_ci.yml`) runs the build, both
checks above, and an independent kernel re-validation with
[leanchecker](https://github.com/digama0/lean4lean).

The stability obstructions are cross-checked against
[`scripts/mcs_stability.py`](scripts/mcs_stability.py), an independent Python
harness that exhaustively enumerates all MCS orderings on small instances:

```bash
python3 scripts/mcs_stability.py --n 5 --pattern K3  --mode ins
python3 scripts/mcs_stability.py --n 6 --pattern P4  --mode ins
python3 scripts/mcs_stability.py --n 4 --pattern 2K2 --mode mixed
```

## Provenance

| Reference | Contribution |
|---|---|
| D. J. Rose, R. E. Tarjan, G. S. Lueker. *Algorithmic Aspects of Vertex Elimination on Graphs.* SIAM J. Comput. 5(2):266-283, 1976. [doi:10.1137/0205021](https://doi.org/10.1137/0205021) | Introduced LexBFS and linear-time chordal graph recognition via lexicographic search. |
| R. E. Tarjan, M. Yannakakis. *Simple Linear-Time Algorithms to Test Chordality of Graphs, Test Acyclicity of Hypergraphs, and Selectively Reduce Acyclic Hypergraphs.* SIAM J. Comput. 13(3):566-579, 1984. [doi:10.1137/0213035](https://doi.org/10.1137/0213035) | Introduced Maximum Cardinality Search (MCS) as a simplified alternative to LexBFS. |
| J. Holm, K. de Lichtenberg, M. Thorup. *Poly-logarithmic Deterministic Fully-Dynamic Algorithms for Connectivity, Minimum Spanning Tree, 2-Edge, and Biconnectivity.* J. ACM 48(4):723-760, 2001. [doi:10.1145/502090.502095](https://doi.org/10.1145/502090.502095) | Foundational fully-dynamic graph algorithm techniques (context for the dynamic setting). |

The re-greedy in this formalization is a naive greedy recomputation, not a
bucket implementation. To our knowledge, no prior formalization of dynamic MCS
ordering maintenance exists in any proof assistant. See
[`formalization.yaml`](formalization.yaml) for the full provenance, cost-model
fidelity notes, and AI-assistance disclosure.
