#!/usr/bin/env python3
"""Generate the comparator wrapper blocks for Solution.lean (real proofs) and
Challenge.lean (sorry statements) from one source of truth, so the two files
carry textually identical signatures for each new theorem."""

# (name, full_forall_type)  -- types copied verbatim from `#check @Proofs.<name>`
# with the leading `@Proofs.<name> : ` stripped and the ∀-prefix kept.
THEOREMS = [
    ("IsMCSOrdering_unique", """∀ {n : ℕ} {G : UGraph n} {o₁ o₂ : List (Vert n)},
    G.IsMCSOrdering o₁ → G.IsMCSOrdering o₂ → o₁ = o₂"""),
    ("insert_update_eq_initOrder", """∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.IsMCSOrdering order → G'.insertUpdate order u v = G'.initOrder"""),
    ("delete_update_eq_initOrder", """∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.adj u v → ¬ G'.adj u v → G.IsMCSOrdering order →
        G'.deleteUpdate order u v = G'.initOrder"""),
    ("legal_upto_earlierPos", """∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.IsMCSOrdering order → ∀ (i : ℕ) (hi : i < order.length),
        i ≤ UGraph.earlierPos order u v →
          G'.IsMCSNext (List.take i order).toFinset (order.get ⟨i, hi⟩)"""),
    ("legal_after_laterPos", """∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.IsMCSOrdering order → ∀ (i : ℕ) (hi : i < order.length),
        UGraph.laterPos order u v < i →
          G'.IsMCSNext (List.take i order).toFinset (order.get ⟨i, hi⟩)"""),
    ("delete_legal_between", """∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.adj u v → ¬ G'.adj u v → G.IsMCSOrdering order →
        ∀ (i : ℕ) (hi : i < order.length),
          UGraph.earlierPos order u v < i → i < UGraph.laterPos order u v →
            G'.IsMCSNext (List.take i order).toFinset (order.get ⟨i, hi⟩)"""),
    ("insert_break_iff", """∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → ¬ G.adj u v → G'.adj u v → G.IsMCSOrdering order →
        ∀ (k : ℕ) (hk : k < order.length),
          UGraph.earlierPos order u v < k → k ≤ UGraph.laterPos order u v →
            (¬ G'.IsMCSNext (List.take k order).toFinset (order.get ⟨k, hk⟩) ↔
              G'.neigh (List.take k order).toFinset (UGraph.laterVert order u v) >
                  G'.neigh (List.take k order).toFinset (order.get ⟨k, hk⟩) ∨
                G'.neigh (List.take k order).toFinset (UGraph.laterVert order u v) =
                    G'.neigh (List.take k order).toFinset (order.get ⟨k, hk⟩) ∧
                  UGraph.laterVert order u v < order.get ⟨k, hk⟩)"""),
    ("insert_update_eq_self_iff", """∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.IsMCSOrdering order →
        (G'.insertUpdate order u v = order ↔ G'.IsMCSOrdering order)"""),
    ("delete_update_eq_self_iff", """∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.adj u v → ¬ G'.adj u v → G.IsMCSOrdering order →
        (G'.deleteUpdate order u v = order ↔ G'.IsMCSOrdering order)"""),
    ("exec_insert_update_eq", """∀ {n : ℕ} (a a' : Adj n) (hsymm : ∀ (u v : ℕ), getAdj a u v = getAdj a v u)
      (hloop : ∀ (u : ℕ), getAdj a u u = false)
      (hsymm' : ∀ (u v : ℕ), getAdj a' u v = getAdj a' v u)
      (hloop' : ∀ (u : ℕ), getAdj a' u u = false),
      List.length a' = n → ∀ (u v : Fin n) (ord : List (Fin n)),
        (toUGraph a hsymm hloop).FlipOf (toUGraph a' hsymm' hloop') u v →
          (toUGraph a hsymm hloop).IsMCSOrdering ord →
            execInsertUpdate a' (List.map Fin.val ord) ↑u ↑v =
              List.map Fin.val ((toUGraph a' hsymm' hloop').insertUpdate ord u v)"""),
    ("exec_delete_update_eq", """∀ {n : ℕ} (a a' : Adj n) (hsymm : ∀ (u v : ℕ), getAdj a u v = getAdj a v u)
      (hloop : ∀ (u : ℕ), getAdj a u u = false)
      (hsymm' : ∀ (u v : ℕ), getAdj a' u v = getAdj a' v u)
      (hloop' : ∀ (u : ℕ), getAdj a' u u = false),
      List.length a' = n → ∀ (u v : Fin n) (ord : List (Fin n)),
        (toUGraph a hsymm hloop).FlipOf (toUGraph a' hsymm' hloop') u v →
          getAdj a ↑u ↑v = true → getAdj a' ↑u ↑v = false →
            (toUGraph a hsymm hloop).IsMCSOrdering ord →
              execDeleteUpdate a' (List.map Fin.val ord) ↑u ↑v =
                List.map Fin.val ((toUGraph a' hsymm' hloop').deleteUpdate ord u v)"""),
    ("exec_insert_cost_le", """∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      o.length = List.length a → (execInsertUpdateC a o u v).2 ≤ List.length a"""),
    ("exec_delete_cost_le", """∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      (execDeleteUpdateC a o u v).2 ≤ List.length a + 1"""),
    ("exec_insert_cost_of_no_break", """∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      insertProbe a o u v = none →
        (execInsertUpdateC a o u v).2 ≤ execLaterPos o u v - execEarlierPos o u v"""),
    ("exec_delete_cost_of_no_break", """∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      pickAt a (List.take (execLaterPos o u v) o) = execLaterVert o u v →
        (execDeleteUpdateC a o u v).2 = 1"""),
    ("exec_insert_cost_of_break", """∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v k : ℕ),
      insertProbe a o u v = some k →
        (execInsertUpdateC a o u v).2 ≤ k - execEarlierPos o u v + (List.length a - k)"""),
    ("exec_delete_cost_of_break", """∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      pickAt a (List.take (execLaterPos o u v) o) ≠ execLaterVert o u v →
        (execDeleteUpdateC a o u v).2 ≤ 1 + (List.length a - execLaterPos o u v)"""),
    ("exists_common_ordering", """∀ {n : ℕ} (G G' : UGraph n),
      (∀ (S : Finset (Vert n)) (x : Vert n), G.neigh S x ≤ G'.neigh S x) →
        (∀ (S : Finset (Vert n)) (x : Vert n), G'.neigh S x ≤ G.neigh S x + 1) →
          ∃ ord, G.IsMCSOrderingAny ord ∧ G'.IsMCSOrderingAny ord"""),
    ("insert_matching_common_order", """∀ {n : ℕ} {G F G' : UGraph n},
      G.AddsEdges F G' → F.IsMatching → ∃ ord, G.IsMCSOrderingAny ord ∧ G'.IsMCSOrderingAny ord"""),
    ("delete_matching_common_order", """∀ {n : ℕ} {G F G' : UGraph n},
      G'.AddsEdges F G → F.IsMatching → ∃ ord, G.IsMCSOrderingAny ord ∧ G'.IsMCSOrderingAny ord"""),
    ("flip_common_order", """∀ {n : ℕ} {G G' : UGraph n} {u v : Vert n},
      G.FlipOf G' u v → ∃ ord, G.IsMCSOrderingAny ord ∧ G'.IsMCSOrderingAny ord"""),
]

DOCS = {
    "IsMCSOrdering_unique": "The canonical MCS ordering of a graph is unique (the lowest-index tie-break fixes every step).",
    "insert_update_eq_initOrder": "The insertion update returns exactly the from-scratch canonical ordering of the new graph.",
    "delete_update_eq_initOrder": "The deletion update returns exactly the from-scratch canonical ordering of the new graph.",
    "legal_upto_earlierPos": "Locality: positions up to the earlier endpoint stay legal after any flip.",
    "legal_after_laterPos": "Locality: positions after the later endpoint stay legal after any flip.",
    "delete_legal_between": "Locality: after a deletion, positions strictly between the endpoints stay legal.",
    "insert_break_iff": "Inside the insertion window, the old choice breaks exactly when the later endpoint now beats it.",
    "insert_update_eq_self_iff": "The insertion update is the identity exactly when the order is still canonical for the new graph.",
    "delete_update_eq_self_iff": "The deletion update is the identity exactly when the order is still canonical for the new graph.",
    "exec_insert_update_eq": "Refinement: the executable insertion update equals the abstract insertion update mapped to vertex values.",
    "exec_delete_update_eq": "Refinement: the executable deletion update equals the abstract deletion update mapped to vertex values.",
    "exec_insert_cost_le": "Cost: an insertion costs at most n units in the unit-cost query model.",
    "exec_delete_cost_le": "Cost: a deletion costs at most n + 1 units in the unit-cost query model.",
    "exec_insert_cost_of_no_break": "Cost: an insertion whose probe finds no break costs at most the window size.",
    "exec_delete_cost_of_no_break": "Cost: a deletion whose probe does not fire costs exactly one check.",
    "exec_insert_cost_of_break": "Cost: an insertion that breaks at k costs the probe checks plus at most n - k regreedy steps.",
    "exec_delete_cost_of_break": "Cost: a deletion that fires costs one check plus at most n - laterPos regreedy steps.",
    "exists_common_ordering": "Stability: if G' neighbour counts exceed G's by at most one along every chosen set, the two graphs share an MCS ordering.",
    "insert_matching_common_order": "Stability: inserting a matching leaves a common MCS ordering.",
    "delete_matching_common_order": "Stability: deleting a matching leaves a common MCS ordering.",
    "flip_common_order": "Stability: flipping a single edge leaves a common MCS ordering.",
}


def block(kind):
    out = []
    for name, ty in THEOREMS:
        doc = DOCS[name]
        out.append(f"/-- {doc} -/")
        if kind == "solution":
            out.append(f"theorem {name} : {ty} :=\n  Proofs.{name}\n")
        else:
            out.append(f"theorem {name} : {ty} := by\n  sorry\n")
    return "\n".join(out)


if __name__ == "__main__":
    import sys
    print(block(sys.argv[1]))
