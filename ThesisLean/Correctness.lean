import Mathlib
import ThesisLean.SolutionBridge

/-!
# Correctness and locality of the dynamic updates (on the `Challenge` definitions)

* correctness of `initOrder`, `insertUpdate`, `deleteUpdate`, `greedySuffix`;
* uniqueness of the canonical MCS ordering, hence: each update returns exactly
  the from-scratch canonical ordering of the new graph;
* locality: after a flip of `{u, v}`, positions up to `earlierPos` and after
  `laterPos` stay legal; after a deletion, positions strictly between the
  endpoints stay legal too, so only `laterPos` can break;
* null updates: the ordering is returned unchanged exactly when it is still
  the canonical ordering of the new graph.
-/

noncomputable section
open Classical

namespace Challenge
namespace Proofs

open UGraph Transport

variable {n : ℕ} {G G' : UGraph n}

/-! ## Uniqueness of the canonical ordering -/

theorem IsMCSNext_unique {S : Finset (Vert n)} {w w' : Vert n}
    (h : IsMCSNext G S w) (h' : IsMCSNext G S w') : w = w' := by
  have heq : G.neigh S w' = G.neigh S w := le_antisymm (h.2.1 w' h'.1) (h'.2.1 w h.1)
  exact le_antisymm (h.2.2 w' h'.1 heq) (h'.2.2 w h.1 heq.symm)

theorem IsMCSOrdering_unique {o₁ o₂ : List (Vert n)}
    (h₁ : IsMCSOrdering G o₁) (h₂ : IsMCSOrdering G o₂) : o₁ = o₂ := by
  have key : ∀ i, o₁.take i = o₂.take i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        rw [List.take_succ, List.take_succ, ih]
        congr 1
        by_cases hi : i < n
        · have hi₁ : i < o₁.length := h₁.2.1 ▸ hi
          have hi₂ : i < o₂.length := h₂.2.1 ▸ hi
          have s₁ := h₁.2.2 i hi₁
          have s₂ := h₂.2.2 i hi₂
          rw [ih] at s₁
          have hsame := IsMCSNext_unique s₁ s₂
          simp only [List.get_eq_getElem] at hsame
          rw [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂, hsame]
        · rw [List.getElem?_eq_none (by rw [h₁.2.1]; omega),
            List.getElem?_eq_none (by rw [h₂.2.1]; omega)]
  have := key n
  rwa [List.take_of_length_le (le_of_eq h₁.2.1),
    List.take_of_length_le (le_of_eq h₂.2.1)] at this

theorem IsMCSNext.toAny {S : Finset (Vert n)} {w : Vert n} (h : IsMCSNext G S w) :
    IsMCSNextAny G S w :=
  ⟨h.1, h.2.1⟩

theorem IsMCSOrdering.toAny {order : List (Vert n)} (h : IsMCSOrdering G order) :
    IsMCSOrderingAny G order :=
  ⟨h.1, h.2.1, fun i hi => (h.2.2 i hi).toAny⟩

/-! ## Correctness -/

theorem init_valid (G : UGraph n) : IsMCSOrdering G (initOrder G) := by
  rw [initOrder, Transport.greedySuffix_eq, IsMCSOrdering_toDyn]
  exact DynamicMCS.UGraph.init_valid (Transport.toDyn G)

theorem order_toFinset_univ {order : List (Vert n)} (h : IsMCSOrdering G order) :
    order.toFinset = (Finset.univ : Finset (Vert n)) :=
  DynamicMCS.Eea71821.order_toFinset_univ order ((IsMCSOrdering_toDyn G order).1 h)

theorem greedySuffix_full (H : UGraph n) (order : List (Vert n))
    (h : order.toFinset = (Finset.univ : Finset (Vert n))) :
    greedySuffix H order = order := by
  rw [Transport.greedySuffix_eq]
  exact DynamicMCS.Eea71821.greedySuffix_full (Transport.toDyn H) order h

theorem update_from_prefix (order : List (Vert n)) (k : ℕ)
    (hvalid : IsMCSOrdering G order)
    (hsteps : ∀ i (hi : i < order.length), i < k →
      IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩)) :
    IsMCSOrdering G' (greedySuffix G' (order.take k)) := by
  rw [Transport.greedySuffix_eq, IsMCSOrdering_toDyn]
  exact DynamicMCS.Eea71821.update_from_prefix (G := Transport.toDyn G) order k
    ((IsMCSOrdering_toDyn G order).1 hvalid)
    (fun i hi hlt => (IsMCSNext_toDyn G' _ _).1 (hsteps i hi hlt))

lemma insertUpdate_eq_dyn (H : UGraph n) (order : List (Vert n)) (u v : Vert n) :
    insertUpdate H order u v = DynamicMCS.Eea71821.insertUpdate (Transport.toDyn H) order u v := by
  unfold insertUpdate DynamicMCS.Eea71821.insertUpdate
  rw [earlierPos_eq, laterPos_eq, firstBreakWindow_eq, greedySuffix_eq]

lemma deleteUpdate_eq_dyn (H : UGraph n) (order : List (Vert n)) (u v : Vert n) :
    deleteUpdate H order u v = DynamicMCS.Eea71821.deleteUpdate (Transport.toDyn H) order u v := by
  unfold deleteUpdate DynamicMCS.Eea71821.deleteUpdate
  rw [deletionBreaks_eq, laterPos_eq, greedySuffix_eq]

/-- The insertion update is correct for every flip of `{u, v}` (the proof does
not need the edge to be absent before). -/
theorem insert_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (insertUpdate G' order u v) := by
  rw [insertUpdate_eq_dyn, IsMCSOrdering_toDyn]
  exact DynamicMCS.Eea71821.insert_update_valid u v order
    ((FlipOf_toDyn G G' u v).1 hflip) ((IsMCSOrdering_toDyn G order).1 hvalid)

theorem delete_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (deleteUpdate G' order u v) := by
  rw [deleteUpdate_eq_dyn, IsMCSOrdering_toDyn]
  exact DynamicMCS.Eea71821.delete_update_valid (G := Transport.toDyn G) u v order
    ((FlipOf_toDyn G G' u v).1 hflip) hdel hdel' ((IsMCSOrdering_toDyn G order).1 hvalid)

/-! ## Each update returns exactly the from-scratch canonical ordering -/

theorem insert_update_eq_initOrder (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    insertUpdate G' order u v = initOrder G' :=
  IsMCSOrdering_unique (insert_update_valid u v order hflip hvalid) (init_valid G')

theorem delete_update_eq_initOrder (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    deleteUpdate G' order u v = initOrder G' :=
  IsMCSOrdering_unique (delete_update_valid u v order hflip hdel hdel' hvalid) (init_valid G')

/-! ## Locality -/

/-- Positions up to the earlier endpoint stay legal after any flip. -/
theorem legal_upto_earlierPos (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi : i < order.length) (hle : i ≤ earlierPos order u v) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) :=
  (IsMCSNext_toDyn G' _ _).2 (DynamicMCS.UGraph.prefix_preserved order u v
    ((FlipOf_toDyn G G' u v).1 hflip) ((IsMCSOrdering_toDyn G order).1 hvalid) i
    (by rwa [earlierPos_eq] at hle) hi)

/-- Positions after the later endpoint stay legal after any flip. -/
theorem legal_after_laterPos (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi : i < order.length) (hgt : laterPos order u v < i) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) :=
  (IsMCSNext_toDyn G' _ _).2 (DynamicMCS.Eea71821.legal_after_laterPos order u v
    ((FlipOf_toDyn G G' u v).1 hflip) ((IsMCSOrdering_toDyn G order).1 hvalid) i hi
    (by rwa [laterPos_eq] at hgt))

/-- After a deletion, positions strictly between the endpoints stay legal. -/
theorem delete_legal_between (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi : i < order.length)
    (hgt : earlierPos order u v < i) (hlt : i < laterPos order u v) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) :=
  (IsMCSNext_toDyn G' _ _).2 (DynamicMCS.Eea71821.legal_middle_delete (G := Transport.toDyn G)
    order u v ((FlipOf_toDyn G G' u v).1 hflip) hdel hdel'
    ((IsMCSOrdering_toDyn G order).1 hvalid) i hi
    (by rwa [earlierPos_eq] at hgt) (by rwa [laterPos_eq] at hlt))

/-- Inside the insertion window, the old choice breaks exactly when the later
endpoint now beats it: strictly larger cardinality, or equal cardinality and a
smaller index. -/
theorem insert_break_iff (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hins : ¬ G.adj u v) (hins' : G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (k : ℕ) (hk : k < order.length)
    (hgt : earlierPos order u v < k) (hle : k ≤ laterPos order u v) :
    ¬ IsMCSNext G' (order.take k).toFinset (order.get ⟨k, hk⟩) ↔
      G'.neigh (order.take k).toFinset (laterVert order u v) >
          G'.neigh (order.take k).toFinset (order.get ⟨k, hk⟩) ∨
        (G'.neigh (order.take k).toFinset (laterVert order u v) =
            G'.neigh (order.take k).toFinset (order.get ⟨k, hk⟩) ∧
          laterVert order u v < order.get ⟨k, hk⟩) := by
  rw [IsMCSNext_toDyn, laterVert_eq]
  exact DynamicMCS.Eea71821.insert_break_iff (G := Transport.toDyn G) order u v
    ((FlipOf_toDyn G G' u v).1 hflip) hins hins' ((IsMCSOrdering_toDyn G order).1 hvalid) k hk
    (by rwa [earlierPos_eq] at hgt) (by rwa [laterPos_eq] at hle)

/-! ## Null updates -/

/-- The insertion update returns `order` unchanged exactly when `order` is
still the canonical MCS ordering of the new graph. -/
theorem insert_update_eq_self_iff (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    insertUpdate G' order u v = order ↔ IsMCSOrdering G' order := by
  constructor
  · intro h
    rw [← h]
    exact insert_update_valid u v order hflip hvalid
  · intro h'
    exact IsMCSOrdering_unique (insert_update_valid u v order hflip hvalid) h'

/-- The deletion update returns `order` unchanged exactly when `order` is
still the canonical MCS ordering of the new graph. -/
theorem delete_update_eq_self_iff (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    deleteUpdate G' order u v = order ↔ IsMCSOrdering G' order := by
  constructor
  · intro h
    rw [← h]
    exact delete_update_valid u v order hflip hdel hdel' hvalid
  · intro h'
    exact IsMCSOrdering_unique (delete_update_valid u v order hflip hdel hdel' hvalid) h'

/-- If the window probe finds no break, the insertion update returns `order`
itself (no regreedy). -/
theorem insert_update_of_no_break (u v : Vert n) (order : List (Vert n))
    (hvalid : IsMCSOrdering G order)
    (h : firstBreakWindow G' order (earlierPos order u v + 1) (laterPos order u v) = none) :
    insertUpdate G' order u v = order := by
  unfold insertUpdate
  rw [h, Option.getD_none, List.take_length]
  exact greedySuffix_full G' order (order_toFinset_univ hvalid)

/-- If the deletion probe does not fire, the deletion update returns `order`
itself (no regreedy). -/
theorem delete_update_of_no_break (u v : Vert n) (order : List (Vert n))
    (h : deletionBreaks G' order u v = false) :
    deleteUpdate G' order u v = order := by
  unfold deleteUpdate
  rw [h]
  rfl

end Proofs
end Challenge
