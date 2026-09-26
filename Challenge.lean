import Mathlib

/-!
# Challenge: dynamic MCS ordering maintenance

Statements (with `sorry` bodies) of the headline results; `Solution.lean`
proves each one under the same name and type.

The definitions block below is byte-identical to `ThesisLean/ChallengeDefs.lean`
(checked by `scripts/check_challenge_defs.sh`), which `Solution.lean` imports.
-/

-- BEGIN DEFS
noncomputable section
open Classical

namespace Challenge

/-- Vertices of an `n`-vertex undirected graph. -/
abbrev Vert (n : ℕ) := Fin n

/-- A finite undirected, loop-free graph on the vertices `Fin n`. -/
structure UGraph (n : ℕ) where
  adj : Vert n → Vert n → Prop
  symm : ∀ {x y : Vert n}, adj x y → adj y x
  loopless : ∀ (x : Vert n), ¬ adj x x

namespace UGraph

variable {n : ℕ}

/-- Cardinality of `w` measured against the already-chosen set `chosen`,
i.e. the number of neighbors of `w` lying in `chosen`. -/
def neigh (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : ℕ := by
  classical
  exact chosen.card - (chosen.filter (fun x => ¬ G.adj w x)).card

/-- `w` is the canonical MCS step after `chosen`: `w` is unchosen, its
cardinality is maximal among the unchosen vertices, and it is the least-index
vertex achieving that maximum. -/
def IsMCSNext (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : Prop :=
  w ∈ (Finset.univ : Finset (Vert n)) \ chosen ∧
  (∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x ≤ G.neigh chosen w) ∧
  (∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x = G.neigh chosen w → w ≤ x)

/-- `order` is the canonical MCS ordering of `G`: it lists every vertex once
and each position holds the canonical MCS step after the earlier positions. -/
def IsMCSOrdering (G : UGraph n) (order : List (Vert n)) : Prop :=
  order.Nodup ∧ order.length = n ∧
  ∀ (i : ℕ) (hi : i < order.length),
    IsMCSNext G (order.take i).toFinset (order.get ⟨i, hi⟩)

/-- `w` is *an* MCS step after `chosen` under arbitrary tie-breaking. -/
def IsMCSNextAny (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : Prop :=
  w ∈ (Finset.univ : Finset (Vert n)) \ chosen ∧
  ∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x ≤ G.neigh chosen w

/-- `order` is an MCS ordering of `G` under arbitrary tie-breaking. -/
def IsMCSOrderingAny (G : UGraph n) (order : List (Vert n)) : Prop :=
  order.Nodup ∧ order.length = n ∧
  ∀ (i : ℕ) (hi : i < order.length),
    IsMCSNextAny G (order.take i).toFinset (order.get ⟨i, hi⟩)

/-- `G'` differs from `G` only by flipping the undirected edge `{u, v}`. -/
def FlipOf (G G' : UGraph n) (u v : Vert n) : Prop :=
  u ≠ v ∧
  ∀ (x y : Vert n),
    G'.adj x y = G.adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)

/-- `G'` is `G` with the edges of `F` added. -/
def AddsEdges (G F G' : UGraph n) : Prop :=
  ∀ x y : Vert n, G'.adj x y ↔ G.adj x y ∨ F.adj x y

/-- Every vertex has at most one `F`-neighbor. -/
def IsMatching (F : UGraph n) : Prop :=
  ∀ x y z : Vert n, F.adj x y → F.adj x z → y = z

/-- The unchosen vertices of maximum cardinality exist whenever some vertex is
unchosen. -/
theorem maxUnchosen_nonempty (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) :
    (((Finset.univ : Finset (Vert n)) \ chosen).filter (fun x =>
      G.neigh chosen x = ((Finset.univ : Finset (Vert n)) \ chosen).sup (G.neigh chosen))).Nonempty := by
  have hU : ((Finset.univ : Finset (Vert n)) \ chosen).Nonempty :=
    Finset.sdiff_nonempty.2 (fun hs => h (Finset.univ_subset_iff.1 hs))
  obtain ⟨w, hw, hsup⟩ := Finset.exists_mem_eq_sup _ hU (G.neigh chosen)
  exact ⟨w, Finset.mem_filter.2 ⟨hw, hsup.symm⟩⟩

/-- The canonical MCS pick: the least-index unchosen vertex of maximum
cardinality. -/
def mcsPick (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) : Vert n :=
  (((Finset.univ : Finset (Vert n)) \ chosen).filter (fun x =>
    G.neigh chosen x = ((Finset.univ : Finset (Vert n)) \ chosen).sup (G.neigh chosen))).min'
    (maxUnchosen_nonempty G chosen h)

/-- The canonical pick is a canonical MCS step. -/
theorem mcsPick_isMCSNext (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) :
    IsMCSNext G chosen (mcsPick G chosen h) := by
  have hmem := Finset.min'_mem _ (maxUnchosen_nonempty G chosen h)
  rw [Finset.mem_filter] at hmem
  refine ⟨hmem.1, fun x hx => hmem.2 ▸ Finset.le_sup hx, fun x hx hx' => ?_⟩
  exact Finset.min'_le _ x (Finset.mem_filter.2 ⟨hx, hx'.trans hmem.2⟩)

/-- The canonical pick, carried with its legality proof. -/
def greedyPick (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) : { w : Vert n // IsMCSNext G chosen w } :=
  ⟨mcsPick G chosen h, mcsPick_isMCSNext G chosen h⟩

/-- Repeatedly extend `chosen` with the canonical pick, one step per unit of
`k`; the invariant `chosen.card + k = n` certifies that `k` steps suffice. -/
def mcsLoop (G : UGraph n) (chosen : Finset (Vert n)) (k : ℕ)
    (hk : chosen.card + k = n) : List (Vert n) :=
  match k with
  | 0 => []
  | km + 1 =>
      have hchosen : chosen ≠ (Finset.univ : Finset (Vert n)) := by
        intro hc
        have hcard : chosen.card = n := by simp [hc]
        omega
      let p := (greedyPick G chosen hchosen).1
      have hp : p ∉ chosen := by
        exact (Finset.mem_sdiff.mp (greedyPick G chosen hchosen).2.1).2
      have hins : (insert p chosen).card = chosen.card + 1 := by
        exact Finset.card_insert_of_notMem hp
      p :: mcsLoop G (insert p chosen) km (by omega)
termination_by k
decreasing_by
  all_goals simp_wf

/-- Canonical MCS continuation of the chosen set `chosen`. -/
def mcsRemainder (G : UGraph n) (chosen : Finset (Vert n)) : List (Vert n) :=
  mcsLoop G chosen (n - chosen.card) (by
    have hcard : chosen.card ≤ n := by
      simpa using (Finset.card_le_univ chosen)
    omega)

/-- Keep the prefix `pref` and recompute the rest canonically (regreedy). -/
def greedySuffix (G : UGraph n) (pref : List (Vert n)) : List (Vert n) :=
  pref ++ mcsRemainder G pref.toFinset

/-- Position (in `order`) of the earlier of the endpoints `u` and `v`. -/
def earlierPos (order : List (Vert n)) (u v : Vert n) : ℕ :=
  min (List.idxOf u order) (List.idxOf v order)

/-- Position (in `order`) of the later of the endpoints `u` and `v`. -/
def laterPos (order : List (Vert n)) (u v : Vert n) : ℕ :=
  max (List.idxOf u order) (List.idxOf v order)

/-- The endpoint placed later in `order`. -/
def laterVert (order : List (Vert n)) (u v : Vert n) : Vert n :=
  if List.idxOf u order ≤ List.idxOf v order then v else u

/-- Boolean negation of a proposition (classical). -/
def isFalse (P : Prop) : Bool :=
  if P then false else true

/-- Scan the list `xs` (whose head sits at position `k` of `order`) and return
the first position whose old choice is not the canonical MCS step on `H`. -/
def firstBreakAux (H : UGraph n) (order : List (Vert n)) :
    ℕ → List (Vert n) → Option ℕ
  | _, [] => none
  | k, x :: xs =>
      if IsMCSNext H (order.take k).toFinset x then firstBreakAux H order (k + 1) xs
      else some k

/-- The first breaking position at or after `k0`, scanning to the end. -/
def firstBreak (H : UGraph n) (order : List (Vert n)) (k0 : ℕ) : Option ℕ :=
  firstBreakAux H order k0 (order.drop k0)

/-- The first breaking position inside the window `[k0, k1]`; the scan
examines only the positions `k0, …, k1`. -/
def firstBreakWindow (H : UGraph n) (order : List (Vert n)) (k0 k1 : ℕ) : Option ℕ :=
  firstBreakAux H order k0 ((order.drop k0).take (k1 + 1 - k0))

/-- The deletion probe: the later endpoint is no longer the canonical step at
its own position. -/
def deletionBreaks (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : Bool :=
  isFalse (IsMCSNext H (order.take (laterPos order u v)).toFinset (laterVert order u v))

/-- Initialisation: the canonical MCS ordering from scratch. -/
def initOrder (H : UGraph n) : List (Vert n) :=
  greedySuffix H []

/-- Insertion update: probe the window `[earlierPos + 1, laterPos]` for the
first break and regreedy from it; keep `order` if the window survives. -/
def insertUpdate (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : List (Vert n) :=
  let k := Option.getD (firstBreakWindow H order (earlierPos order u v + 1)
    (laterPos order u v)) order.length
  greedySuffix H (order.take k)

/-- Deletion update: probe the single position `laterPos`; regreedy from it
only if the probe fires. -/
def deleteUpdate (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : List (Vert n) :=
  if deletionBreaks H order u v then
    greedySuffix H (order.take (laterPos order u v))
  else
    order

/-- The graph on `Fin n` whose edges are the listed pairs (both directions,
loops dropped).  Used to state concrete counterexamples. -/
def ofEdges (n : ℕ) (E : List (ℕ × ℕ)) : UGraph n :=
  { adj := fun x y => x ≠ y ∧ ((x.val, y.val) ∈ E ∨ (y.val, x.val) ∈ E)
    symm := by
      intro x y h
      exact ⟨fun hxy => h.1 hxy.symm, h.2.symm⟩
    loopless := by
      intro x h
      exact h.1 rfl }

end UGraph

open UGraph

variable {n : ℕ}

/-! ## Executable model (boolean adjacency matrix, vertex ids in `ℕ`) -/

/-- A concrete adjacency matrix: rows of booleans. -/
abbrev Adj (n : ℕ) := List (List Bool)

/-- Row lookup, `false` out of range. -/
def atRow : List Bool → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: rest, k+1 => atRow rest k

/-- `getAdj a u v`: is the edge `(u, v)` present in `a`? -/
def getAdj (a : Adj n) (u v : ℕ) : Bool :=
  match a[u]? with
  | none => false
  | some row => atRow row v

/-- Number of chosen neighbors of `w`. -/
def cardC (a : Adj n) (chosen : List ℕ) (w : ℕ) : ℕ :=
  (chosen.filter (fun v => getAdj a v w)).length

/-- Canonical MCS pick among `rem`: maximum cardinality, smallest id on ties. -/
def bestPick (a : Adj n) (chosen : List ℕ) (rem : List ℕ) : ℕ :=
  rem.foldl (fun best v =>
    let cb := cardC a chosen best
    let cv := cardC a chosen v
    if cv > cb ∨ (cv = cb ∧ v < best) then v else best)
    (rem.headD 0)

/-- One MCS step on the state `(chosen in reverse, remaining)`. -/
def mcsStep (a : Adj n) (st : List ℕ × List ℕ) : List ℕ × List ℕ :=
  let (chosen, rem) := st
  match rem with
  | [] => st
  | _ => let v := bestPick a chosen rem; (v :: chosen, rem.erase v)

/-- Canonical MCS ordering of `a`, computed from scratch. -/
def mcsOrder (a : Adj n) : List ℕ :=
  let n := a.length
  let st := ((List.range n).foldl (fun s _ => mcsStep a s) ([], List.range n))
  st.1.reverse

/-- Set the undirected entry `(u, v)` to `present`. -/
def setEdge (n : ℕ) (a : Adj n) (u v : ℕ) (present : Bool) : Adj n :=
  List.mapIdx (fun i row =>
    List.mapIdx (fun j b =>
      if i = u ∧ j = v ∨ i = v ∧ j = u then present else b) row) a

/-- Insert the edge `(u, v)`. -/
def insertEdge (n : ℕ) (a : Adj n) (u v : ℕ) : Adj n := setEdge n a u v true

/-- Delete the edge `(u, v)`. -/
def deleteEdge (n : ℕ) (a : Adj n) (u v : ℕ) : Adj n := setEdge n a u v false

/-- The matrix is square of size `n`. -/
def WellShaped (n : ℕ) (a : Adj n) : Prop :=
  a.length = n ∧ ∀ x : ℕ, x < n → ∃ row : List Bool, a[x]? = some row ∧ row.length = n

/-- The abstract graph denoted by a symmetric loop-free matrix. -/
def toUGraph (a : Adj n) (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u)
    (hloop : ∀ u : ℕ, getAdj a u u = false) : UGraph n :=
  { adj := fun x y => getAdj a x.val y.val = true
    symm := by
      intro x y h
      rwa [hsymm x.val y.val] at h
    loopless := by
      intro x h
      have hx : getAdj a x.val x.val = false := hloop x.val
      simp [hx] at h }

/-! ## Executable dynamic updates -/

/-- The unchosen vertex ids, in increasing order. -/
def remOf (n : ℕ) (chosen : List ℕ) : List ℕ :=
  (List.range n).filter (fun v => decide (v ∉ chosen))

/-- The canonical MCS pick after the chosen prefix `chosen`. -/
def pickAt (a : Adj n) (chosen : List ℕ) : ℕ :=
  bestPick a chosen (remOf a.length chosen)

/-- Keep the prefix `pref` and recompute the rest of the canonical ordering. -/
def regreedy (a : Adj n) (pref : List ℕ) : List ℕ :=
  ((List.range (a.length - pref.length)).foldl (fun s _ => mcsStep a s)
    (pref.reverse, remOf a.length pref)).1.reverse

/-- Executable probe: the first position (starting at `k`) whose old choice
differs from the canonical pick after the preceding prefix of `order`. -/
def execFirstBreak (a : Adj n) (order : List ℕ) : ℕ → List ℕ → Option ℕ
  | _, [] => none
  | k, x :: xs => if pickAt a (order.take k) = x then execFirstBreak a order (k + 1) xs else some k

/-- Position of the earlier endpoint in `order`. -/
def execEarlierPos (order : List ℕ) (u v : ℕ) : ℕ :=
  min (order.idxOf u) (order.idxOf v)

/-- Position of the later endpoint in `order`. -/
def execLaterPos (order : List ℕ) (u v : ℕ) : ℕ :=
  max (order.idxOf u) (order.idxOf v)

/-- The endpoint placed later in `order`. -/
def execLaterVert (order : List ℕ) (u v : ℕ) : ℕ :=
  if order.idxOf u ≤ order.idxOf v then v else u

/-- The old choices at the positions `earlierPos + 1, …, laterPos`, which are
the only positions an insertion probe examines. -/
def insertWindow (order : List ℕ) (u v : ℕ) : List ℕ :=
  (order.drop (execEarlierPos order u v + 1)).take (execLaterPos order u v - execEarlierPos order u v)

/-- Insertion probe on the post-insertion matrix `a`. -/
def insertProbe (a : Adj n) (order : List ℕ) (u v : ℕ) : Option ℕ :=
  execFirstBreak a order (execEarlierPos order u v + 1) (insertWindow order u v)

/-- Executable insertion update on the post-insertion matrix `a`: probe the
window, regreedy from the first break, keep `order` if nothing breaks. -/
def execInsertUpdate (a : Adj n) (order : List ℕ) (u v : ℕ) : List ℕ :=
  match insertProbe a order u v with
  | none => order
  | some k => regreedy a (order.take k)

/-- Executable deletion update on the post-deletion matrix `a`: probe the
single position `laterPos`, regreedy from it if the probe fires. -/
def execDeleteUpdate (a : Adj n) (order : List ℕ) (u v : ℕ) : List ℕ :=
  if pickAt a (order.take (execLaterPos order u v)) = execLaterVert order u v then order
  else regreedy a (order.take (execLaterPos order u v))

/-! ## Operational cost (unit-cost query model)

Each call of `pickAt` in a probe and each MCS step of a regreedy costs one
unit.  The instrumented functions below follow the control flow of the
executable updates exactly and additionally return the number of units spent.
-/

/-- One MCS step, returning `1` if a vertex was picked. -/
def mcsStepC (a : Adj n) (st : List ℕ × List ℕ) : (List ℕ × List ℕ) × ℕ :=
  match st.2 with
  | [] => (st, 0)
  | _ => (mcsStep a st, 1)

/-- Instrumented `regreedy`. -/
def regreedyC (a : Adj n) (pref : List ℕ) : List ℕ × ℕ :=
  let r := (List.range (a.length - pref.length)).foldl
    (fun s _ => let t := mcsStepC a s.1; (t.1, s.2 + t.2))
    ((pref.reverse, remOf a.length pref), 0)
  (r.1.1.reverse, r.2)

/-- Instrumented `execFirstBreak`. -/
def execFirstBreakC (a : Adj n) (order : List ℕ) : ℕ → List ℕ → Option ℕ × ℕ
  | _, [] => (none, 0)
  | k, x :: xs =>
      if pickAt a (order.take k) = x then
        let r := execFirstBreakC a order (k + 1) xs
        (r.1, r.2 + 1)
      else (some k, 1)

/-- Instrumented `insertProbe`. -/
def insertProbeC (a : Adj n) (order : List ℕ) (u v : ℕ) : Option ℕ × ℕ :=
  execFirstBreakC a order (execEarlierPos order u v + 1) (insertWindow order u v)

/-- Instrumented `execInsertUpdate`. -/
def execInsertUpdateC (a : Adj n) (order : List ℕ) (u v : ℕ) : List ℕ × ℕ :=
  let p := insertProbeC a order u v
  match p.1 with
  | none => (order, p.2)
  | some k => let r := regreedyC a (order.take k); (r.1, p.2 + r.2)

/-- Instrumented `execDeleteUpdate`. -/
def execDeleteUpdateC (a : Adj n) (order : List ℕ) (u v : ℕ) : List ℕ × ℕ :=
  if pickAt a (order.take (execLaterPos order u v)) = execLaterVert order u v then (order, 1)
  else let r := regreedyC a (order.take (execLaterPos order u v)); (r.1, 1 + r.2)

end Challenge
-- END DEFS

namespace Challenge

open UGraph

variable {n : ℕ} {G G' : UGraph n}

/-- `setEdge` preserves the symmetry of the adjacency matrix, provided the
matrix is well-shaped. -/
theorem setEdge_preserves_symm (n : ℕ) (a : Adj n) (u v : ℕ) (present : Bool)
    (hshape : WellShaped n a)
    (hsymm : ∀ i j : ℕ, getAdj a i j = getAdj a j i) :
    ∀ x y : ℕ,
      getAdj (setEdge n a u v present) x y =
        getAdj (setEdge n a u v present) y x := by
  sorry

/-- `setEdge` preserves loop-freeness of the matrix, provided the two flipped
indices are distinct. -/
theorem setEdge_preserves_loopless (n : ℕ) (a : Adj n) (u v : ℕ) (present : Bool)
    (hshape : WellShaped n a)
    (hloop : ∀ i : ℕ, getAdj a i i = false) (huv : u ≠ v) :
    ∀ x : ℕ, getAdj (setEdge n a u v present) x x = false := by
  sorry

/-- Initialising the data structure on a graph yields a valid MCS ordering. -/
theorem init_valid (G : UGraph n) : IsMCSOrdering G (initOrder G) := by
  sorry

/-- After inserting an edge, the updated ordering computed by `insertUpdate`
is a valid MCS ordering of the new graph. -/
theorem insert_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hinsert : ¬ G.adj u v) (hinsert' : G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (insertUpdate G' order u v) := by
  sorry

/-- After deleting an edge, the updated ordering computed by `deleteUpdate`
is a valid MCS ordering of the new graph. -/
theorem delete_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (deleteUpdate G' order u v) := by
  sorry

/-- Regreeding from a full prefix is the identity: any ordering containing
every vertex, greedily regreedied, is unchanged. -/
theorem greedySuffix_full (H : UGraph n) (order : List (Vert n))
    (h : order.toFinset = (Finset.univ : Finset (Vert n))) :
    greedySuffix H order = order := by
  sorry

/-- Regreeding from a legal prefix yields a valid MCS ordering. -/
theorem update_from_prefix (order : List (Vert n)) (k : ℕ)
    (hvalid : IsMCSOrdering G order)
    (hsteps : ∀ i (hi : i < order.length), i < k →
      IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩)) :
    IsMCSOrdering G' (greedySuffix G' (order.take k)) := by
  sorry

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
  sorry

/-- After an executable edge insertion, the recomputed `mcsOrder` of the new
matrix is a valid abstract MCS ordering of the new graph, and its values are
exactly the executable output. -/
theorem exec_insert_recompute_valid (n : ℕ) (a : Adj n) (u v : Vert n)
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
  sorry

/-- After an executable edge deletion, the recomputed `mcsOrder` of the new
matrix is a valid abstract MCS ordering of the new graph. -/
theorem exec_delete_recompute_valid (n : ℕ) (a : Adj n) (u v : Vert n)
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
  sorry


/-! ## Comparator headline theorems (generated) -/

/-- The canonical MCS ordering of a graph is unique (the lowest-index tie-break fixes every step). -/
theorem IsMCSOrdering_unique : ∀ {n : ℕ} {G : UGraph n} {o₁ o₂ : List (Vert n)},
    G.IsMCSOrdering o₁ → G.IsMCSOrdering o₂ → o₁ = o₂ := by
  sorry

/-- The insertion update returns exactly the from-scratch canonical ordering of the new graph. -/
theorem insert_update_eq_initOrder : ∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.IsMCSOrdering order → G'.insertUpdate order u v = G'.initOrder := by
  sorry

/-- The deletion update returns exactly the from-scratch canonical ordering of the new graph. -/
theorem delete_update_eq_initOrder : ∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.adj u v → ¬ G'.adj u v → G.IsMCSOrdering order →
        G'.deleteUpdate order u v = G'.initOrder := by
  sorry

/-- Locality: positions up to the earlier endpoint stay legal after any flip. -/
theorem legal_upto_earlierPos : ∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.IsMCSOrdering order → ∀ (i : ℕ) (hi : i < order.length),
        i ≤ UGraph.earlierPos order u v →
          G'.IsMCSNext (List.take i order).toFinset (order.get ⟨i, hi⟩) := by
  sorry

/-- Locality: positions after the later endpoint stay legal after any flip. -/
theorem legal_after_laterPos : ∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.IsMCSOrdering order → ∀ (i : ℕ) (hi : i < order.length),
        UGraph.laterPos order u v < i →
          G'.IsMCSNext (List.take i order).toFinset (order.get ⟨i, hi⟩) := by
  sorry

/-- Locality: after a deletion, positions strictly between the endpoints stay legal. -/
theorem delete_legal_between : ∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.adj u v → ¬ G'.adj u v → G.IsMCSOrdering order →
        ∀ (i : ℕ) (hi : i < order.length),
          UGraph.earlierPos order u v < i → i < UGraph.laterPos order u v →
            G'.IsMCSNext (List.take i order).toFinset (order.get ⟨i, hi⟩) := by
  sorry

/-- Inside the insertion window, the old choice breaks exactly when the later endpoint now beats it. -/
theorem insert_break_iff : ∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → ¬ G.adj u v → G'.adj u v → G.IsMCSOrdering order →
        ∀ (k : ℕ) (hk : k < order.length),
          UGraph.earlierPos order u v < k → k ≤ UGraph.laterPos order u v →
            (¬ G'.IsMCSNext (List.take k order).toFinset (order.get ⟨k, hk⟩) ↔
              G'.neigh (List.take k order).toFinset (UGraph.laterVert order u v) >
                  G'.neigh (List.take k order).toFinset (order.get ⟨k, hk⟩) ∨
                G'.neigh (List.take k order).toFinset (UGraph.laterVert order u v) =
                    G'.neigh (List.take k order).toFinset (order.get ⟨k, hk⟩) ∧
                  UGraph.laterVert order u v < order.get ⟨k, hk⟩) := by
  sorry

/-- The insertion update is the identity exactly when the order is still canonical for the new graph. -/
theorem insert_update_eq_self_iff : ∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.IsMCSOrdering order →
        (G'.insertUpdate order u v = order ↔ G'.IsMCSOrdering order) := by
  sorry

/-- The deletion update is the identity exactly when the order is still canonical for the new graph. -/
theorem delete_update_eq_self_iff : ∀ {n : ℕ} {G G' : UGraph n} (u v : Vert n) (order : List (Vert n)),
      G.FlipOf G' u v → G.adj u v → ¬ G'.adj u v → G.IsMCSOrdering order →
        (G'.deleteUpdate order u v = order ↔ G'.IsMCSOrdering order) := by
  sorry

/-- Refinement: the executable insertion update equals the abstract insertion update mapped to vertex values. -/
theorem exec_insert_update_eq : ∀ {n : ℕ} (a a' : Adj n) (hsymm : ∀ (u v : ℕ), getAdj a u v = getAdj a v u)
      (hloop : ∀ (u : ℕ), getAdj a u u = false)
      (hsymm' : ∀ (u v : ℕ), getAdj a' u v = getAdj a' v u)
      (hloop' : ∀ (u : ℕ), getAdj a' u u = false),
      List.length a' = n → ∀ (u v : Fin n) (ord : List (Fin n)),
        (toUGraph a hsymm hloop).FlipOf (toUGraph a' hsymm' hloop') u v →
          (toUGraph a hsymm hloop).IsMCSOrdering ord →
            execInsertUpdate a' (List.map Fin.val ord) ↑u ↑v =
              List.map Fin.val ((toUGraph a' hsymm' hloop').insertUpdate ord u v) := by
  sorry

/-- Refinement: the executable deletion update equals the abstract deletion update mapped to vertex values. -/
theorem exec_delete_update_eq : ∀ {n : ℕ} (a a' : Adj n) (hsymm : ∀ (u v : ℕ), getAdj a u v = getAdj a v u)
      (hloop : ∀ (u : ℕ), getAdj a u u = false)
      (hsymm' : ∀ (u v : ℕ), getAdj a' u v = getAdj a' v u)
      (hloop' : ∀ (u : ℕ), getAdj a' u u = false),
      List.length a' = n → ∀ (u v : Fin n) (ord : List (Fin n)),
        (toUGraph a hsymm hloop).FlipOf (toUGraph a' hsymm' hloop') u v →
          getAdj a ↑u ↑v = true → getAdj a' ↑u ↑v = false →
            (toUGraph a hsymm hloop).IsMCSOrdering ord →
              execDeleteUpdate a' (List.map Fin.val ord) ↑u ↑v =
                List.map Fin.val ((toUGraph a' hsymm' hloop').deleteUpdate ord u v) := by
  sorry

/-- Cost: an insertion costs at most n units in the unit-cost query model. -/
theorem exec_insert_cost_le : ∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      o.length = List.length a → (execInsertUpdateC a o u v).2 ≤ List.length a := by
  sorry

/-- Cost: a deletion costs at most n + 1 units in the unit-cost query model. -/
theorem exec_delete_cost_le : ∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      (execDeleteUpdateC a o u v).2 ≤ List.length a + 1 := by
  sorry

/-- Cost: an insertion whose probe finds no break costs at most the window size. -/
theorem exec_insert_cost_of_no_break : ∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      insertProbe a o u v = none →
        (execInsertUpdateC a o u v).2 ≤ execLaterPos o u v - execEarlierPos o u v := by
  sorry

/-- Cost: a deletion whose probe does not fire costs exactly one check. -/
theorem exec_delete_cost_of_no_break : ∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      pickAt a (List.take (execLaterPos o u v) o) = execLaterVert o u v →
        (execDeleteUpdateC a o u v).2 = 1 := by
  sorry

/-- Cost: an insertion that breaks at k costs the probe checks plus at most n - k regreedy steps. -/
theorem exec_insert_cost_of_break : ∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v k : ℕ),
      insertProbe a o u v = some k →
        (execInsertUpdateC a o u v).2 ≤ k - execEarlierPos o u v + (List.length a - k) := by
  sorry

/-- Cost: a deletion that fires costs one check plus at most n - laterPos regreedy steps. -/
theorem exec_delete_cost_of_break : ∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      pickAt a (List.take (execLaterPos o u v) o) ≠ execLaterVert o u v →
        (execDeleteUpdateC a o u v).2 ≤ 1 + (List.length a - execLaterPos o u v) := by
  sorry

/-- Cost link: the counted insertion update returns the same ordering as the plain executable insertion update. -/
theorem exec_insert_update_c_fst : ∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      (execInsertUpdateC a o u v).1 = execInsertUpdate a o u v := by
  sorry

/-- Cost link: the counted deletion update returns the same ordering as the plain executable deletion update. -/
theorem exec_delete_update_c_fst : ∀ {n : ℕ} (a : Adj n) (o : List ℕ) (u v : ℕ),
      (execDeleteUpdateC a o u v).1 = execDeleteUpdate a o u v := by
  sorry

/-- Stability: if G' neighbour counts exceed G's by at most one along every chosen set, the two graphs share an MCS ordering. -/
theorem exists_common_ordering : ∀ {n : ℕ} (G G' : UGraph n),
      (∀ (S : Finset (Vert n)) (x : Vert n), G.neigh S x ≤ G'.neigh S x) →
        (∀ (S : Finset (Vert n)) (x : Vert n), G'.neigh S x ≤ G.neigh S x + 1) →
          ∃ ord, G.IsMCSOrderingAny ord ∧ G'.IsMCSOrderingAny ord := by
  sorry

/-- Stability: inserting a matching leaves a common MCS ordering. -/
theorem insert_matching_common_order : ∀ {n : ℕ} {G F G' : UGraph n},
      G.AddsEdges F G' → F.IsMatching → ∃ ord, G.IsMCSOrderingAny ord ∧ G'.IsMCSOrderingAny ord := by
  sorry

/-- Stability: deleting a matching leaves a common MCS ordering. -/
theorem delete_matching_common_order : ∀ {n : ℕ} {G F G' : UGraph n},
      G'.AddsEdges F G → F.IsMatching → ∃ ord, G.IsMCSOrderingAny ord ∧ G'.IsMCSOrderingAny ord := by
  sorry

/-- Stability: flipping a single edge leaves a common MCS ordering. -/
theorem flip_common_order : ∀ {n : ℕ} {G G' : UGraph n} {u v : Vert n},
      G.FlipOf G' u v → ∃ ord, G.IsMCSOrderingAny ord ∧ G'.IsMCSOrderingAny ord := by
  sorry

/-- Stability obstruction: inserting a triangle can destroy every common MCS ordering. -/
theorem triangle_no_common_order : ¬ ∃ ord, IsMCSOrderingAny (ofEdges 5 [(0,2),(0,4),(1,2),(1,3)]) ord ∧
      IsMCSOrderingAny (ofEdges 5 ([(0,2),(0,4),(1,2),(1,3)] ++ [(2,3),(2,4),(3,4)])) ord := by
  sorry

/-- Stability obstruction: inserting a P4 path can destroy every common MCS ordering. -/
theorem p4_no_common_order : ¬ ∃ ord, IsMCSOrderingAny (ofEdges 6 [(0,3),(0,5),(1,2),(1,4),(2,3)]) ord ∧
      IsMCSOrderingAny
        (ofEdges 6 ([(0,3),(0,5),(1,2),(1,4),(2,3)] ++ [(2,5),(3,4),(4,5)])) ord := by
  sorry

/-- Stability obstruction: a mixed matching update (one insert, one delete) can destroy every common MCS ordering. -/
theorem mixed_matching_no_common_order : ¬ ∃ ord, IsMCSOrderingAny (ofEdges 4 [(0,1),(0,3),(1,2)]) ord ∧
      IsMCSOrderingAny (ofEdges 4 [(0,3),(1,2),(2,3)]) ord := by
  sorry

end Challenge
