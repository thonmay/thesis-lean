# Dynamic MCS Ordering Maintenance

A machine-checked (Lean 4 / Mathlib) study of maintaining a **Maximum-Cardinality-Search (MCS)** vertex ordering under single-edge insertions and deletions, with a verified executable implementation, a locality analysis, a unit-cost model, and a stability-boundary result.

**Authors:** Md Thoriqul Islam Thonmay, Gregory Morse.
**License:** Apache-2.0.

## Result

On a loop-free undirected graph, an MCS ordering is built greedily: repeatedly pick the unchosen vertex with the most already-chosen neighbours (ties broken by lowest index). This formalization maintains such an ordering under a single-edge update by a **probe-then-repair** strategy — scan the window between the two endpoints for the first step whose old choice is no longer a legal MCS pick, and only then regreedy the suffix — and proves, for every graph size `n`:

- **Correctness.** Every order produced is a valid MCS ordering of the updated graph, and in fact equals the from-scratch canonical ordering (which is unique).
- **Locality.** Inside an insertion window the old choice breaks exactly when the later endpoint now beats it; outside the window (and, for deletions, on either side of the endpoints) positions stay legal. The update is the identity exactly when the order is already canonical for the new graph.
- **Verified executable.** A boolean-adjacency implementation (`execInsertUpdate` / `execDeleteUpdate`) is proved to refine the abstract update.
- **Unit cost.** Instrumented versions count legality checks and pick steps along the real control flow: at most `n` for an insertion and `n + 1` for a deletion. The worst case therefore **matches static recomputation** — no asymptotic separation over recomputing from scratch is claimed.
- **Stability boundary.** If the neighbour count of every vertex in one graph exceeds that in the other by at most one along every chosen prefix, the two graphs share an MCS ordering; in particular inserting/deleting a *matching*, or flipping a single edge, always preserves a common MCS ordering. This matching hypothesis is tight: inserting a triangle, inserting a `P4`, or a mixed matching update (one insert + one delete) can destroy every common ordering (certified by kernel `decide`).

## Theorem map

The comparator (Palomar) contract is the list in [`comparator.json`](comparator.json); each name is a real theorem in [`Solution.lean`](Solution.lean) with a matching `sorry` statement in [`Challenge.lean`](Challenge.lean). Both are generated from one source of truth (`scripts/gen_comparator_wrappers.py`) so the posed and proved types stay textually identical.

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

## Repository layout

- `Challenge.lean` — the posed statements (`sorry` bodies) and the canonical definitions (the `BEGIN DEFS` / `END DEFS` block, Mathlib-only).
- `Solution.lean` — the proved versions of every comparator theorem.
- `AxiomAudit.lean` — prints the axioms each comparator theorem depends on.
- `ThesisLean/` — the development:
  - `ChallengeDefs.lean` — canonical definitions (byte-identical to the `Challenge.lean` DEFS block).
  - `Correctness.lean` — uniqueness, locality, update = recompute.
  - `ExecUpdate.lean` — executable updates, refinement proofs, unit-cost model.
  - `Stability.lean` — common-ordering theorem, matching corollaries, certified obstructions.
  - `Exec.lean`, `ExecFlip.lean`, `ExecBridge.lean`, `McsInvariant.lean`, `CardBridge.lean`, `BridgeSteps.lean`, `BridgeParts{A,B,C}.lean`, `BridgeAssembly.lean`, `SolutionBridge.lean` — the executable layer and the transport lemmas connecting it to the abstract model.
  - `Formal_gen001c01_3939115c.lean`, `Formal_gen003c01_eea71821.lean` — the core `DynamicMCS` development (graph searches, updates, validity).
- `scripts/` — `check_challenge_defs.sh` (definitions byte-match), `check_axioms.sh` (axiom audit), `mcs_stability.py` (exhaustive stability harness), `gen_comparator_wrappers.py` (single-source generator for the comparator blocks).

## Build and verify

Requires Lean `v4.35.0-rc2` (see [`lean-toolchain`](lean-toolchain)) and Mathlib.

```bash
lake exe cache get && lake build          # build everything
bash scripts/check_challenge_defs.sh      # Challenge.lean defs match ChallengeDefs.lean
bash scripts/check_axioms.sh              # all comparator theorems use only propext/Quot.sound/Classical.choice
```

The CI workflow (`.github/workflows/lean_action_ci.yml`) runs the build, both checks above, and an independent kernel re-validation with [leanchecker](https://github.com/digama0/lean4lean). The stability obstructions are cross-checked against `scripts/mcs_stability.py`:

```bash
python3 scripts/mcs_stability.py --n 5 --pattern K3  --mode ins
python3 scripts/mcs_stability.py --n 6 --pattern P4  --mode ins
python3 scripts/mcs_stability.py --n 4 --pattern 2K2 --mode mixed
```

## Provenance

The MCS ordering is due to Rose, Tarjan and Lueker (J. ACM 23(1):244-253, 1976); see also Tarjan and Yannakakis, *Maximum cardinality search: a general-purpose heuristic* (SIAM J. Comput. 13(3):566-579, 1984). The regreedy here is a naive greedy recomputation, not a bucket implementation. We are not aware of a prior formalization of dynamic MCS ordering maintenance in any proof assistant. See [`formalization.yaml`](formalization.yaml) for the full provenance, cost-model fidelity notes, and AI-assistance disclosure.
