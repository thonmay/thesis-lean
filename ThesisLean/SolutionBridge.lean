import Mathlib
import ThesisLean.ChallengeDefs
import ThesisLean.Formal_gen001c01_3939115c
import ThesisLean.Formal_gen003c01_eea71821
import ThesisLean.Exec
import ThesisLean.ExecFlip
import ThesisLean.BridgeAssembly

/-!
# SolutionBridge: transport from the `Challenge` definitions to the project
development

`ThesisLean.ChallengeDefs` holds the definitions `Challenge.lean` states its
theorems about.  The proofs live in the `DynamicMCS` development, whose
definitions have identical bodies but are distinct constants.  This file
connects the two families with `_eq` / `_toDyn` lemmas.

The recursive greedy definitions (`mcsLoop`, `mcsRemainder`, `greedySuffix`)
are related by induction; `greedyPick` values agree definitionally because
both namespaces use the same explicit `mcsPick` construction.  The bounded
insertion probe `Challenge.UGraph.firstBreakWindow` (which stops at the window
end) is related to the project's filtered full-suffix scan by
`firstBreakWindow_eq_scan`.
-/

noncomputable section
open Classical

namespace Challenge

namespace UGraph

variable {n : ℕ}

/-- The scan's reported position is at least its starting position. -/
lemma firstBreakAux_ge (H : UGraph n) (order : List (Vert n)) :
    ∀ (k j : ℕ) (xs : List (Vert n)), firstBreakAux H order k xs = some j → k ≤ j := by
  intro k j xs
  induction xs generalizing k with
  | nil => simp [firstBreakAux]
  | cons x xs ih =>
      intro h
      by_cases hx : IsMCSNext H (order.take k).toFinset x
      · rw [firstBreakAux, if_pos hx] at h
        have := ih (k + 1) h
        omega
      · rw [firstBreakAux, if_neg hx] at h
        exact le_of_eq (Option.some.inj h)

/-- Scanning only the first `m` elements reports the same first break as the
full scan, provided that break lies among those `m` positions. -/
lemma firstBreakAux_take (H : UGraph n) (order : List (Vert n)) :
    ∀ (k m : ℕ) (xs : List (Vert n)),
      firstBreakAux H order k (xs.take m) =
        (firstBreakAux H order k xs).filter (fun j => decide (j < k + m)) := by
  intro k m xs
  induction xs generalizing k m with
  | nil => simp [firstBreakAux]
  | cons x xs ih =>
      cases m with
      | zero =>
          cases h : firstBreakAux H order k (x :: xs) with
          | none => simp [firstBreakAux]
          | some j =>
              have := firstBreakAux_ge H order k j (x :: xs) h
              simp [firstBreakAux]
              omega
      | succ m =>
          by_cases hx : IsMCSNext H (order.take k).toFinset x
          · rw [List.take_succ_cons, firstBreakAux, if_pos hx, firstBreakAux, if_pos hx, ih,
              show k + (m + 1) = k + 1 + m by omega]
          · rw [List.take_succ_cons, firstBreakAux, if_neg hx, firstBreakAux, if_neg hx]
            simp

/-- The bounded window probe equals the full-suffix scan filtered to the
window: stopping the scan at `k1` loses nothing. -/
theorem firstBreakWindow_eq_scan (H : UGraph n) (order : List (Vert n)) (k0 k1 : ℕ) :
    firstBreakWindow H order k0 k1 =
      (firstBreak H order k0).filter (fun j => decide (j ≤ k1)) := by
  unfold firstBreakWindow firstBreak
  rw [firstBreakAux_take]
  cases h : firstBreakAux H order k0 (order.drop k0) with
  | none => rfl
  | some j =>
      have := firstBreakAux_ge H order k0 j _ h
      simp only [Option.filter_some]
      by_cases hj : j ≤ k1
      · rw [if_pos (by simpa using (by omega : j < k0 + (k1 + 1 - k0))), if_pos (by simpa using hj)]
      · rw [if_neg (by simpa using (by omega : ¬ j < k0 + (k1 + 1 - k0))), if_neg (by simpa using hj)]

end UGraph

namespace Transport

open UGraph

/-- Transport a `Challenge.UGraph` to the project's `DynamicMCS.UGraph`. -/
def toDyn {n : ℕ} (G : UGraph n) : DynamicMCS.UGraph n :=
  { adj := fun x y => G.adj x y
    symm := by intro x y h; exact G.symm h
    loopless := by intro x h; exact G.loopless x h }

/-- `greedyPick` values are definitionally equal across the namespaces. -/
lemma greedyPick_val {n} (G : UGraph n) (chosen : Finset (Vert n))
    (h h' : chosen ≠ (Finset.univ : Finset (Vert n))) :
    (greedyPick G chosen h).1 = (DynamicMCS.UGraph.greedyPick (toDyn G) chosen h').1 := by
  rfl

/-- `mcsLoop` computes equal lists across the namespaces, by induction on
`k`. -/
lemma mcsLoop_eq (n : ℕ) (G : UGraph n) (chosen : Finset (Vert n)) (k : ℕ)
    (hk : chosen.card + k = n) (hk' : chosen.card + k = n) :
    UGraph.mcsLoop G chosen k hk = DynamicMCS.UGraph.mcsLoop (toDyn G) chosen k hk' := by
  revert hk hk'
  induction k generalizing chosen with
  | zero =>
      intro hk hk'
      simp [UGraph.mcsLoop, DynamicMCS.UGraph.mcsLoop]
  | succ km ih =>
      intro hk hk'
      have h1 := UGraph.mcsLoop.eq_2 G chosen km hk
      have h2 := DynamicMCS.UGraph.mcsLoop.eq_2 (toDyn G) chosen km hk'
      rw [h1, h2]
      have hnotu : chosen ≠ (Finset.univ : Finset (Vert n)) := by
        intro hc
        have hcard0 : chosen.card = n := by simp [hc]
        omega
      set p := (greedyPick G chosen hnotu).1
      have hp_notin : p ∉ chosen :=
        (Finset.mem_sdiff.mp (greedyPick G chosen hnotu).2.1).2
      have hcard : (insert p chosen).card = chosen.card + 1 :=
        Finset.card_insert_of_notMem hp_notin
      change p :: UGraph.mcsLoop G (insert p chosen) km (by omega)
        = p :: DynamicMCS.UGraph.mcsLoop (toDyn G) (insert p chosen) km (by omega)
      congr 1
      exact ih (insert p chosen) (by omega) (by omega)

/-- `mcsRemainder` computes equal lists across the namespaces. -/
lemma mcsRemainder_eq (n : ℕ) (G : UGraph n) (chosen : Finset (Vert n)) :
    UGraph.mcsRemainder G chosen = DynamicMCS.UGraph.mcsRemainder (toDyn G) chosen := by
  unfold UGraph.mcsRemainder DynamicMCS.UGraph.mcsRemainder
  exact mcsLoop_eq n G chosen (n - chosen.card) _ _

/-- `greedySuffix` computes equal lists across the namespaces. -/
lemma greedySuffix_eq {n : ℕ} (G : UGraph n) (pref : List (Vert n)) :
    UGraph.greedySuffix G pref = DynamicMCS.UGraph.greedySuffix (toDyn G) pref := by
  unfold UGraph.greedySuffix DynamicMCS.UGraph.greedySuffix
  rw [mcsRemainder_eq]

/-- `IsMCSNext` is invariant under the structure transport `toDyn`. -/
lemma IsMCSNext_toDyn {n} (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) :
    IsMCSNext G chosen w ↔ DynamicMCS.UGraph.IsMCSNext (toDyn G) chosen w := by
  unfold IsMCSNext DynamicMCS.UGraph.IsMCSNext toDyn
  simp [neigh, DynamicMCS.UGraph.neigh]

/-- `IsMCSOrdering` is invariant under `toDyn`. -/
lemma IsMCSOrdering_toDyn {n} (G : UGraph n) (order : List (Vert n)) :
    IsMCSOrdering G order ↔ DynamicMCS.UGraph.IsMCSOrdering (toDyn G) order := by
  unfold IsMCSOrdering DynamicMCS.UGraph.IsMCSOrdering
  constructor
  · intro h
    exact ⟨h.1, h.2.1, by
      intro i hi
      exact (IsMCSNext_toDyn G (order.take i).toFinset (order.get ⟨i, hi⟩)).1 (h.2.2 i hi)⟩
  · intro h
    exact ⟨h.1, h.2.1, by
      intro i hi
      exact (IsMCSNext_toDyn G (order.take i).toFinset (order.get ⟨i, hi⟩)).2 (h.2.2 i hi)⟩

/-- `FlipOf` is invariant under `toDyn`. -/
lemma FlipOf_toDyn {n} (G G' : UGraph n) (u v : Vert n) :
    FlipOf G G' u v ↔ DynamicMCS.UGraph.FlipOf (toDyn G) (toDyn G') u v := by
  unfold FlipOf DynamicMCS.UGraph.FlipOf
  constructor
  · intro h
    rcases h with ⟨huv, hflip⟩
    refine ⟨huv, ?_⟩
    intro x y
    rcases hflip x y with h | h | h
    · left; simpa [toDyn] using h
    · right; left; simpa [toDyn] using h
    · right; right; simpa [toDyn] using h
  · intro h
    rcases h with ⟨huv, hflip⟩
    refine ⟨huv, ?_⟩
    intro x y
    rcases hflip x y with h | h | h
    · left; simpa [toDyn] using h
    · right; left; simpa [toDyn] using h
    · right; right; simpa [toDyn] using h

/-- `earlierPos` is invariant (identical, non-recursive body). -/
lemma earlierPos_eq (order : List (Vert n)) (u v : Vert n) :
    earlierPos order u v = DynamicMCS.UGraph.earlierPos order u v := by
  unfold earlierPos DynamicMCS.UGraph.earlierPos
  rfl

/-- `laterPos` is invariant. -/
lemma laterPos_eq (order : List (Vert n)) (u v : Vert n) :
    laterPos order u v = DynamicMCS.Eea71821.laterPos order u v := by
  unfold laterPos DynamicMCS.Eea71821.laterPos
  rfl

/-- `laterVert` is invariant. -/
lemma laterVert_eq (order : List (Vert n)) (u v : Vert n) :
    laterVert order u v = DynamicMCS.Eea71821.laterVert order u v := by
  unfold laterVert DynamicMCS.Eea71821.laterVert
  rfl

/-- `firstBreakAux` computes equal options across the namespaces. -/
lemma firstBreakAux_eq (H : UGraph n) (order : List (Vert n)) :
    ∀ (k : ℕ) (xs : List (Vert n)),
      firstBreakAux H order k xs = DynamicMCS.Eea71821.firstBreakAux (toDyn H) order k xs := by
  intro k xs
  induction xs generalizing k with
  | nil =>
      rw [firstBreakAux, DynamicMCS.Eea71821.firstBreakAux]
  | cons x xs ih =>
      by_cases hx : IsMCSNext H (order.take k).toFinset x
      · have hxD : DynamicMCS.UGraph.IsMCSNext (toDyn H) (order.take k).toFinset x :=
          (IsMCSNext_toDyn H (order.take k).toFinset x).mpr hx
        rw [firstBreakAux, DynamicMCS.Eea71821.firstBreakAux, if_pos hx, if_pos hxD]
        exact ih (k + 1)
      · have hxD : ¬ DynamicMCS.UGraph.IsMCSNext (toDyn H) (order.take k).toFinset x := by
          intro h
          exact hx ((IsMCSNext_toDyn H (order.take k).toFinset x).mp h)
        rw [firstBreakAux, DynamicMCS.Eea71821.firstBreakAux, if_neg hx, if_neg hxD]

/-- `firstBreak` computes equal options across the namespaces. -/
lemma firstBreak_eq (H : UGraph n) (order : List (Vert n)) (k0 : ℕ) :
    firstBreak H order k0 = DynamicMCS.Eea71821.firstBreak (toDyn H) order k0 := by
  unfold firstBreak DynamicMCS.Eea71821.firstBreak
  exact firstBreakAux_eq H order k0 (order.drop k0)

/-- The deletion probe computes equal booleans across the namespaces. -/
lemma deletionBreaks_eq (H : UGraph n) (order : List (Vert n)) (u v : Vert n) :
    deletionBreaks H order u v = DynamicMCS.Eea71821.deletionBreaks (toDyn H) order u v := by
  unfold deletionBreaks DynamicMCS.Eea71821.deletionBreaks isFalse DynamicMCS.Eea71821.isFalse
  rw [← laterPos_eq, ← laterVert_eq]
  by_cases h : IsMCSNext H (order.take (laterPos order u v)).toFinset (laterVert order u v)
  · rw [if_pos h, if_pos ((IsMCSNext_toDyn _ _ _).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((IsMCSNext_toDyn _ _ _).2 h'))]

/-- The bounded window probe transports to the project's filtered scan. -/
lemma firstBreakWindow_eq (H : UGraph n) (order : List (Vert n)) (k0 k1 : ℕ) :
    firstBreakWindow H order k0 k1 =
      DynamicMCS.Eea71821.firstBreakWindow (toDyn H) order k0 k1 := by
  rw [firstBreakWindow_eq_scan, firstBreak_eq]
  unfold DynamicMCS.Eea71821.firstBreakWindow
  cases DynamicMCS.Eea71821.firstBreak (toDyn H) order k0 with
  | none => rfl
  | some j =>
      by_cases hj : j ≤ k1
      · simp [hj]
      · simp [hj]

/-- `initOrder` computes equal lists across the namespaces. -/
lemma initOrder_eq (G : UGraph n) :
    initOrder G = DynamicMCS.Eea71821.initOrder (toDyn G) := by
  unfold initOrder DynamicMCS.Eea71821.initOrder
  exact greedySuffix_eq G []

/-- Executable row lookup agrees with the project's (identical bodies). -/
lemma atRow_eq (row : List Bool) (v : ℕ) : atRow row v = Exec.atRow row v := by
  induction row generalizing v with
  | nil => rfl
  | cons b t ih =>
      cases v with
      | zero => rfl
      | succ v' => simpa [atRow, Exec.atRow] using ih v'

/-- Executable `getAdj` agrees with the project's (identical bodies). -/
lemma getAdj_eq (n : ℕ) (a : Adj n) (u v : ℕ) : getAdj a u v = @Exec.getAdj n a u v := by
  cases h : a[u]? with
  | none => simp [getAdj, Exec.getAdj, h]
  | some row =>
      have h1 : getAdj a u v = atRow row v := by simp [getAdj, h]
      have h2 : @Exec.getAdj n a u v = Exec.atRow row v := by simp [Exec.getAdj, h]
      rw [h1, h2]
      exact atRow_eq row v

/-- `toDyn` of a `toUGraph` built from a matrix is `Exec.toUGraph` of the same
matrix. -/
lemma toUGraph_toDyn (a : Adj n) (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u)
    (hloop : ∀ u : ℕ, getAdj a u u = false) :
    toDyn (toUGraph a hsymm hloop)
      = @Exec.toUGraph n a
          (fun u v => by rw [← getAdj_eq n, ← getAdj_eq n, hsymm])
          (fun u => by rw [← getAdj_eq n]; exact hloop u) := by
  cases h1 : toDyn (toUGraph a hsymm hloop) with
  | mk adj1 symm1 loop1 =>
      cases h2 : @Exec.toUGraph n a
          (fun u v => by rw [← getAdj_eq n, ← getAdj_eq n, hsymm])
          (fun u => by rw [← getAdj_eq n]; exact hloop u) with
      | mk adj2 symm2 loop2 =>
          have hadj : adj1 = adj2 := by
            calc
              adj1 = (toDyn (toUGraph a hsymm hloop)).adj :=
                    (congrArg DynamicMCS.UGraph.adj h1).symm
              _ = (@Exec.toUGraph n a
                  (fun u v => by rw [← getAdj_eq n, ← getAdj_eq n, hsymm])
                  (fun u => by rw [← getAdj_eq n]; exact hloop u)).adj := by
                    funext x y
                    simp [toDyn, toUGraph, Exec.toUGraph, getAdj_eq n]
              _ = adj2 := congrArg DynamicMCS.UGraph.adj h2
          cases hadj
          simp

/-- Executable `setEdge` agrees with the project's (identical bodies). -/
lemma setEdge_eq (n : ℕ) (a : Adj n) (u v : ℕ) (present : Bool) :
    setEdge n a u v present = @Exec.setEdge n a u v present := by
  unfold setEdge Exec.setEdge
  rfl

/-- Executable `insertEdge` agrees with the project's. -/
lemma insertEdge_eq (n : ℕ) (a : Adj n) (u v : ℕ) :
    insertEdge n a u v = @Exec.insertEdge n a u v := by
  unfold insertEdge Exec.insertEdge setEdge Exec.setEdge
  rfl

/-- Executable `deleteEdge` agrees with the project's. -/
lemma deleteEdge_eq (n : ℕ) (a : Adj n) (u v : ℕ) :
    deleteEdge n a u v = @Exec.deleteEdge n a u v := by
  unfold deleteEdge Exec.deleteEdge setEdge Exec.setEdge
  rfl

/-- Executable `cardC` agrees with the project's (via `getAdj_eq`). -/
lemma cardC_eq (a : Adj n) (chosen : List ℕ) (w : ℕ) :
    cardC a chosen w = @Exec.cardC n a chosen w := by
  unfold cardC Exec.cardC
  congr 1
  congr 1
  funext v
  exact getAdj_eq n a v w

/-- Executable `bestPick` agrees with the project's. -/
lemma bestPick_eq (a : Adj n) (chosen : List ℕ) (rem : List ℕ) :
    bestPick a chosen rem = @Exec.bestPick n a chosen rem := by
  unfold bestPick Exec.bestPick
  induction rem with
  | nil => rfl
  | cons v vs ih =>
      simp [List.foldl, cardC_eq, ih]

/-- Executable `mcsStep` agrees with the project's. -/
lemma mcsStep_eq (a : Adj n) (st : List ℕ × List ℕ) :
    mcsStep a st = @Exec.mcsStep n a st := by
  rcases st with ⟨chosen, rem⟩
  induction rem with
  | nil =>
      simp [mcsStep, Exec.mcsStep]
  | cons v vs ih =>
      simp [mcsStep, Exec.mcsStep, bestPick_eq]

/-- The fold over `mcsStep` agrees across the namespaces, on any state. -/
lemma foldl_mcsStep_eq (a : Adj n) (l : List ℕ) (st : List ℕ × List ℕ) :
    l.foldl (fun s _ => mcsStep a s) st = l.foldl (fun s _ => @Exec.mcsStep n a s) st := by
  induction l generalizing st with
  | nil => rfl
  | cons h t ih =>
      simp [List.foldl, ih, mcsStep_eq]

/-- Executable `mcsOrder` agrees with the project's. -/
lemma mcsOrder_eq (a : Adj n) : mcsOrder a = @Exec.mcsOrder n a := by
  unfold mcsOrder Exec.mcsOrder
  simp [foldl_mcsStep_eq a]

end Transport
end Challenge
