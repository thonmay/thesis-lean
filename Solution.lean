import Mathlib
import ThesisLean.Formal_gen001c01_3939115c
import ThesisLean.Formal_gen003c01_eea71821
import ThesisLean.Exec
import ThesisLean.ExecFlip
import ThesisLean.BridgeAssembly
import ThesisLean.SolutionBridge

/-!
# Solution: proved headline theorems for Dynamic MCS ordering maintenance

This module supplies real proofs (no `sorry`) of the headline theorems that
`Challenge.lean` states with `sorry`-bodies under the same namespace
`Challenge`.  It imports `ThesisLean.ChallengeDefs` (the definitions block of
`Challenge.lean`, byte-identical) and the project development, but not
`Challenge.lean` itself.

Each headline theorem is transported to its proved project counterpart
through the `Challenge.Transport` lemmas in `SolutionBridge`: the graph
types are connected by `Transport.toDyn`, the greedy recomputation by
`Transport.greedySuffix_eq`, and the pure definitions by their `_eq` lemmas.
-/

noncomputable section
open Classical
open scoped BigOperators

open DynamicMCS
open Challenge
open Challenge.UGraph
open Challenge.Transport

namespace Challenge

/-! ## Correctness headline theorems -/

/-- `init` produces a valid MCS ordering of the given graph. -/
theorem init_valid (G : UGraph n) : IsMCSOrdering G (initOrder G) := by
  classical
  rw [initOrder, Transport.greedySuffix_eq]
  change DynamicMCS.UGraph.IsMCSOrdering (Transport.toDyn G)
    (DynamicMCS.UGraph.greedySuffix (Transport.toDyn G) [])
  exact DynamicMCS.UGraph.init_valid (Transport.toDyn G)

/-- After inserting an edge, the updated ordering computed by `insertUpdate`
is a valid MCS ordering of the new graph. -/
theorem insert_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hinsert : ¬ G.adj u v) (hinsert' : G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (insertUpdate G' order u v) := by
  classical
  have hflipD := (Transport.FlipOf_toDyn G G' u v).1 hflip
  have hvalidD := (Transport.IsMCSOrdering_toDyn G order).1 hvalid
  -- the project theorem is over implicit {n} {G G'}; supply them via @
  have hproj := @DynamicMCS.Eea71821.insert_update_valid n
    (Transport.toDyn G) (Transport.toDyn G') u v order hflipD hvalidD
  have hval : insertUpdate G' order u v
      = DynamicMCS.Eea71821.insertUpdate (Transport.toDyn G') order u v := by
    unfold insertUpdate DynamicMCS.Eea71821.insertUpdate
    rw [Transport.earlierPos_eq, Transport.laterPos_eq, Transport.firstBreakWindow_eq]
    rw [Transport.greedySuffix_eq]
  have hres : IsMCSOrdering G' (insertUpdate G' order u v) := by
    rw [hval]
    exact (Transport.IsMCSOrdering_toDyn G' (DynamicMCS.Eea71821.insertUpdate
      (Transport.toDyn G') order u v)).2 hproj
  exact hres

/-- After deleting an edge, the updated ordering computed by `deleteUpdate`
is a valid MCS ordering of the new graph. -/
theorem delete_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (deleteUpdate G' order u v) := by
  classical
  have hflipD := (Transport.FlipOf_toDyn G G' u v).1 hflip
  have hvalidD := (Transport.IsMCSOrdering_toDyn G order).1 hvalid
  have hdelD : (Transport.toDyn G).adj u v := by
    simpa [Transport.toDyn] using hdel
  have hdel'D : ¬ (Transport.toDyn G').adj u v := by
    intro h; exact hdel' (by simpa [Transport.toDyn] using h)
  have hproj := @DynamicMCS.Eea71821.delete_update_valid n
    (Transport.toDyn G) (Transport.toDyn G') u v order hflipD hdelD hdel'D hvalidD
  have hval : deleteUpdate G' order u v
      = DynamicMCS.Eea71821.deleteUpdate (Transport.toDyn G') order u v := by
    unfold deleteUpdate DynamicMCS.Eea71821.deleteUpdate
    rw [Transport.deletionBreaks_eq]
    rw [Transport.laterPos_eq]
    congr 1
    rw [Transport.greedySuffix_eq]
  have hres : IsMCSOrdering G' (deleteUpdate G' order u v) := by
    rw [hval]
    exact (Transport.IsMCSOrdering_toDyn G' (DynamicMCS.Eea71821.deleteUpdate
      (Transport.toDyn G') order u v)).2 hproj
  exact hres

/-- Regreeding from a full prefix is the identity. -/
theorem greedySuffix_full (H : UGraph n) (order : List (Vert n))
    (h : order.toFinset = (Finset.univ : Finset (Vert n))) :
    greedySuffix H order = order := by
  rw [Transport.greedySuffix_eq]
  exact DynamicMCS.Eea71821.greedySuffix_full (Transport.toDyn H) order
    (by simpa [Transport.toDyn] using h)

/-- Regreeding from a legal prefix yields a valid MCS ordering. -/
theorem update_from_prefix (order : List (Vert n)) (k : ℕ)
    (hvalid : IsMCSOrdering G order)
    (hsteps : ∀ i (hi : i < order.length), i < k →
      IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩)) :
    IsMCSOrdering G' (greedySuffix G' (order.take k)) := by
  classical
  have hvalidD := (Transport.IsMCSOrdering_toDyn G order).1 hvalid
  have hstepsD : ∀ i (hi : i < order.length), i < k →
      DynamicMCS.UGraph.IsMCSNext (Transport.toDyn G') (order.take i).toFinset
        (order.get ⟨i, hi⟩) := by
    intro i hi hlt
    exact (Transport.IsMCSNext_toDyn G' (order.take i).toFinset
      (order.get ⟨i, hi⟩)).1 (hsteps i hi hlt)
  have hproj := @DynamicMCS.Eea71821.update_from_prefix n
    (Transport.toDyn G) (Transport.toDyn G') order k hvalidD hstepsD
  have hres : IsMCSOrdering G' (greedySuffix G' (order.take k)) := by
    rw [Transport.greedySuffix_eq]
    rw [Transport.IsMCSOrdering_toDyn]
    exact hproj
  exact hres

/-! ## Executable setEdge preservation & bridge headline theorems -/

/-- `setEdge` preserves the symmetry of the adjacency matrix, provided the
matrix is well-shaped. -/
theorem setEdge_preserves_symm (n : ℕ) (a : Adj n) (u v : ℕ) (present : Bool)
    (hshape : WellShaped n a)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i) :
    ∀ x y : ℕ,
      getAdj (setEdge n a u v present) x y =
        getAdj (setEdge n a u v present) y x := by
  have hshapeE : ExecFlip.WellShaped n a := by
    unfold WellShaped ExecFlip.WellShaped at *
    exact hshape
  have hsymmE : ∀ i j : ℕ, (@Exec.getAdj n a i j) = (@Exec.getAdj n a j i) := by
    intro i j
    rw [← getAdj_eq n, ← getAdj_eq n, hsymm]
  intro x y
  have h := ExecFlip.setEdge_preserves_symm n a u v present hshapeE hsymmE x y
  calc
    getAdj (setEdge n a u v present) x y
        = Exec.getAdj (Exec.setEdge n a u v present) x y := by
            rw [setEdge_eq, getAdj_eq n]
    _ = Exec.getAdj (Exec.setEdge n a u v present) y x := h
    _ = getAdj (setEdge n a u v present) y x := by
            rw [← setEdge_eq, ← getAdj_eq n]

/-- `setEdge` preserves loop-freeness of the matrix, provided the two flipped
indices are distinct. -/
theorem setEdge_preserves_loopless (n : ℕ) (a : Adj n) (u v : ℕ) (present : Bool)
    (hshape : WellShaped n a)
    (hloop : ∀ i : ℕ, getAdj a i i = false) (huv : u ≠ v) :
    ∀ x : ℕ, getAdj (setEdge n a u v present) x x = false := by
  have hshapeE : ExecFlip.WellShaped n a := by
    unfold WellShaped ExecFlip.WellShaped at *
    exact hshape
  have hloopE : ∀ i : ℕ, (@Exec.getAdj n a i i) = false := by
    intro i
    rw [← getAdj_eq n]
    exact hloop i
  intro x
  have h := ExecFlip.setEdge_preserves_loopless n a u v present hshapeE hloopE huv x
  calc
    getAdj (setEdge n a u v present) x x
        = Exec.getAdj (Exec.setEdge n a u v present) x x := by
            rw [setEdge_eq, getAdj_eq n]
    _ = false := h

/-- The executable recomputation of the MCS ordering from a concrete boolean
adjacency matrix yields a list of vertices that is a valid MCS ordering of
the abstract graph the matrix denotes, and its values equal the executable
output. -/
theorem mcsOrder_eq_greedySuffix
    (a : Adj n)
    (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u)
    (hloop : ∀ u : ℕ, getAdj a u u = false)
    (ha_len : a.length = n) :
    let G := toUGraph a hsymm hloop
    ∃ (ord : List (Vert n)),
      IsMCSOrdering G ord ∧
      ord.map (fun v => v.val) = mcsOrder a := by
  let G : UGraph n := toUGraph a hsymm hloop
  have hsymmE : ∀ u v : ℕ, (@Exec.getAdj n a u v) = (@Exec.getAdj n a v u) := by
    intro u v
    rw [← getAdj_eq n, ← getAdj_eq n, hsymm]
  have hloopE : ∀ u : ℕ, (@Exec.getAdj n a u u) = false := by
    intro u
    rw [← getAdj_eq n]
    exact hloop u
  obtain ⟨ord, hord_dyn, hmap⟩ :=
    ExecBridge.mcsOrder_eq_greedySuffix a hsymmE hloopE ha_len
  refine ⟨ord, ?_, ?_⟩
  · have hG : Transport.toDyn G = Exec.toUGraph a hsymmE hloopE := by
      simpa [G, hsymmE, hloopE] using (Transport.toUGraph_toDyn a hsymm hloop)
    have hv : DynamicMCS.UGraph.IsMCSOrdering (Transport.toDyn G) ord := by
      rw [hG]
      exact hord_dyn
    exact (Transport.IsMCSOrdering_toDyn G ord).2 hv
  · rw [Transport.mcsOrder_eq a]
    exact hmap

/-- After an executable edge insertion, the recomputed `mcsOrder` of the new
matrix is a valid abstract MCS ordering of the new graph, and its values are
exactly the executable output. -/
theorem exec_insert_valid (n : ℕ) (a : Adj n) (u v : Vert n)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i)
    (hloop : ∀ i : ℕ, getAdj a i i = false)
    (hshape : WellShaped n a)
    (huv : u.val ≠ v.val) :
    let a' := insertEdge n a u.val v.val
    let G' := toUGraph a'
      (setEdge_preserves_symm n a u.val v.val true hshape hsymm)
      (setEdge_preserves_loopless n a u.val v.val true hshape hloop huv)
    ∃ (ord : List (Vert n)),
      IsMCSOrdering G' ord ∧
        ord.map (fun w => w.val) = mcsOrder a' := by
  let a' : Adj n := insertEdge n a u.val v.val
  let hs' : ∀ u v : ℕ, getAdj a' u v = getAdj a' v u :=
      setEdge_preserves_symm n a u.val v.val true hshape hsymm
  let hl' : ∀ u : ℕ, getAdj a' u u = false :=
      setEdge_preserves_loopless n a u.val v.val true hshape hloop huv
  let G' : UGraph n := toUGraph a' hs' hl'
  have hsymmE : ∀ i j : ℕ, (@Exec.getAdj n a i j) = (@Exec.getAdj n a j i) := by
    intro i j
    rw [← getAdj_eq n, ← getAdj_eq n, hsymm]
  have hloopE : ∀ i : ℕ, (@Exec.getAdj n a i i) = false := by
    intro i
    rw [← getAdj_eq n]
    exact hloop i
  have hshapeE : ExecFlip.WellShaped n a := by
    unfold WellShaped ExecFlip.WellShaped at *
    exact hshape
  obtain ⟨ord, hord_dyn, hmap⟩ :=
    ExecFlip.exec_insert_valid n a u v hsymmE hloopE hshapeE huv
  refine ⟨ord, ?_, ?_⟩
  · have hUG : Transport.toDyn G' = Exec.toUGraph (Exec.insertEdge n a u.val v.val)
        (ExecFlip.insertEdge_symm a u.val v.val hshapeE hsymmE)
        (ExecFlip.insertEdge_loopless a u.val v.val hshapeE hloopE huv) := by
        simpa [G', a', hs', hl', insertEdge_eq, getAdj_eq n, Exec.insertEdge, Exec.setEdge]
          using (Transport.toUGraph_toDyn a' hs' hl')
    have hv : DynamicMCS.UGraph.IsMCSOrdering (Transport.toDyn G') ord := by
      rw [hUG]
      exact hord_dyn
    exact (Transport.IsMCSOrdering_toDyn G' ord).2 hv
  · simpa [a', insertEdge_eq, Exec.insertEdge, Exec.setEdge, Transport.mcsOrder_eq]
      using hmap

/-- After an executable edge deletion, the recomputed `mcsOrder` of the new
matrix is a valid abstract MCS ordering of the new graph. -/
theorem exec_delete_valid (n : ℕ) (a : Adj n) (u v : Vert n)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i)
    (hloop : ∀ i : ℕ, getAdj a i i = false)
    (hshape : WellShaped n a)
    (huv : u.val ≠ v.val) :
    let a' := deleteEdge n a u.val v.val
    let G' := toUGraph a'
      (setEdge_preserves_symm n a u.val v.val false hshape hsymm)
      (setEdge_preserves_loopless n a u.val v.val false hshape hloop huv)
    ∃ (ord : List (Vert n)),
      IsMCSOrdering G' ord ∧
        ord.map (fun w => w.val) = mcsOrder a' := by
  let a' : Adj n := deleteEdge n a u.val v.val
  let hs' : ∀ u v : ℕ, getAdj a' u v = getAdj a' v u :=
      setEdge_preserves_symm n a u.val v.val false hshape hsymm
  let hl' : ∀ u : ℕ, getAdj a' u u = false :=
      setEdge_preserves_loopless n a u.val v.val false hshape hloop huv
  let G' : UGraph n := toUGraph a' hs' hl'
  have hsymmE : ∀ i j : ℕ, (@Exec.getAdj n a i j) = (@Exec.getAdj n a j i) := by
    intro i j
    rw [← getAdj_eq n, ← getAdj_eq n, hsymm]
  have hloopE : ∀ i : ℕ, (@Exec.getAdj n a i i) = false := by
    intro i
    rw [← getAdj_eq n]
    exact hloop i
  have hshapeE : ExecFlip.WellShaped n a := by
    unfold WellShaped ExecFlip.WellShaped at *
    exact hshape
  obtain ⟨ord, hord_dyn, hmap⟩ :=
    ExecFlip.exec_delete_valid n a u v hsymmE hloopE hshapeE huv
  refine ⟨ord, ?_, ?_⟩
  · have hUG : Transport.toDyn G' = Exec.toUGraph (Exec.deleteEdge n a u.val v.val)
        (ExecFlip.deleteEdge_symm a u.val v.val hshapeE hsymmE)
        (ExecFlip.deleteEdge_loopless a u.val v.val hshapeE hloopE huv) := by
        simpa [G', a', hs', hl', deleteEdge_eq, getAdj_eq n, Exec.deleteEdge, Exec.setEdge]
          using (Transport.toUGraph_toDyn a' hs' hl')
    have hv : DynamicMCS.UGraph.IsMCSOrdering (Transport.toDyn G') ord := by
      rw [hUG]
      exact hord_dyn
    exact (Transport.IsMCSOrdering_toDyn G' ord).2 hv
  · simpa [a', deleteEdge_eq, Exec.deleteEdge, Exec.setEdge, Transport.mcsOrder_eq]
      using hmap

end Challenge