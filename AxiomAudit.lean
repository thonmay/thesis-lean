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
#print axioms Challenge.exec_insert_valid
#print axioms Challenge.exec_delete_valid
-- END AUDIT
