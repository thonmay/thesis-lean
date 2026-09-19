import Mathlib

/-!
# ThesisLean

Lean formalization of the dynamic graph algorithm correctness proofs.

The target is the dynamic Maximum Cardinality Search (MCS) ordering
algorithm discovered by the evolutionary search (see `runs/mcs_dsv4f_dryrun/`).
-/

-- Sanity: mathlib is importable and working.
example : 2 + 2 = 4 := by norm_num

def hello := "world"