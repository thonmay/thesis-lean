import Solution

/-!
# Axiom audit of the comparator theorems

Prints the axioms each theorem listed in `comparator.json` depends on, as
proved in `Solution.lean`.  Run with `lake env lean AxiomAudit.lean`;
`scripts/check_axioms.sh` fails unless every line lists only `propext`,
`Classical.choice` and `Quot.sound`, and unless the names below are exactly
the comparator list.
-/

-- BEGIN AUDIT
#print axioms Challenge.init_valid
#print axioms Challenge.insert_update_valid
#print axioms Challenge.delete_update_valid
#print axioms Challenge.greedySuffix_full
#print axioms Challenge.update_from_prefix
#print axioms Challenge.setEdge_preserves_symm
#print axioms Challenge.setEdge_preserves_loopless
#print axioms Challenge.mcsOrder_eq_greedySuffix
#print axioms Challenge.exec_insert_recompute_valid
#print axioms Challenge.exec_delete_recompute_valid
#print axioms Challenge.IsMCSOrdering_unique
#print axioms Challenge.insert_update_eq_initOrder
#print axioms Challenge.delete_update_eq_initOrder
#print axioms Challenge.legal_upto_earlierPos
#print axioms Challenge.legal_after_laterPos
#print axioms Challenge.delete_legal_between
#print axioms Challenge.insert_break_iff
#print axioms Challenge.insert_update_eq_self_iff
#print axioms Challenge.delete_update_eq_self_iff
#print axioms Challenge.exec_insert_update_eq
#print axioms Challenge.exec_delete_update_eq
#print axioms Challenge.exec_insert_cost_le
#print axioms Challenge.exec_delete_cost_le
#print axioms Challenge.exec_insert_cost_of_no_break
#print axioms Challenge.exec_delete_cost_of_no_break
#print axioms Challenge.exec_insert_cost_of_break
#print axioms Challenge.exec_delete_cost_of_break
#print axioms Challenge.exists_common_ordering
#print axioms Challenge.insert_matching_common_order
#print axioms Challenge.delete_matching_common_order
#print axioms Challenge.flip_common_order
#print axioms Challenge.triangle_no_common_order
#print axioms Challenge.p4_no_common_order
#print axioms Challenge.mixed_matching_no_common_order
-- END AUDIT
