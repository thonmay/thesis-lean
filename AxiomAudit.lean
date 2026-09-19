import ThesisLean

/-!
# Headline theorem axiom audit

Compiled so the trusted assumptions of the dynamic-MCS correctness results are
printed in one reviewable place. Run with:

    lake env lean AxiomAudit.lean

Each result must depend only on `propext`, `Classical.choice`, `Quot.sound`
(mathlib's standard axioms). Any `sorryAx` or project axiom means the proof is
not honest.
-/

#print axioms DynamicMCS.UGraph.mcsLoop_valid
#print axioms DynamicMCS.UGraph.greedySuffix_valid
#print axioms DynamicMCS.UGraph.mcsUpdate_preserves_invariant
#print axioms DynamicMCS.UGraph.insert_edge_valid
#print axioms DynamicMCS.UGraph.delete_edge_valid
#print axioms DynamicMCS.UGraph.init_valid
