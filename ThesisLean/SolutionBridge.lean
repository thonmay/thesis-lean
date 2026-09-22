import Mathlib
import ThesisLean.Formal_gen001c01_3939115c
import ThesisLean.Formal_gen003c01_eea71821
import ThesisLean.ComplexityHeadlines
import ThesisLean.ProbeCost
import ThesisLean.Exec
import ThesisLean.ExecFlip
import ThesisLean.BridgeAssembly
import ThesisLean.CountBridge

/-!
# SolutionBridge: transport from `Challenge` (independent statements) to the
project development

`Solution.lean` must prove the same headline theorem names/types in namespace
`Challenge` as `Challenge.lean` (which states them with `sorry`).  It imports
only Mathlib + project modules (NOT `Challenge.lean`), so this file redeclares
the `Challenge` namespace definitions (verbatim copies) and provides transport
lemmas that connect them to the project's `DynamicMCS` machinery.

The recursive / well-founded greedy definitions (`mcsLoop`, `mcsRemainder`,
`greedySuffix`) are opaque, so they are NOT defeq across the two namespaces;
the transport lemmas here show, by induction, that the two families compute
equal lists/options/costs.  The pure positional and counting definitions
(`earlierPos`, `edgeCount`, `firstBreak`, `probeCost`, ...) are also distinct
constants whose bodies coincide; they are connected by explicit `_eq` lemmas.

The key observation: `greedyPick` values are definitionally equal across the
namespaces (`rfl`), because both are `Classical.choose (exists_IsMCSNext _ _ _)`
with structurally identical `exists_IsMCSNext` theorems.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace Challenge

/-! Verbatim-copied `Challenge` definitions (same names, same namespace, same
bodies as `Challenge.lean`).  Never co-imported with `Challenge.lean`. -/

/-- Vertices of an `n`-vertex undirected graph. -/
abbrev Vert (n : ℕ) := Fin n

/-- A finite undirected, loop-free graph on the vertices `Fin n`. -/
structure UGraph (n : ℕ) where
  adj : Vert n → Vert n → Prop
  symm : ∀ {x y : Vert n}, adj x y → adj y x
  loopless : ∀ (x : Vert n), ¬ adj x x

namespace UGraph

variable {n : ℕ} {G G' : UGraph n}

/-- Cardinality of `w` measured against the already-chosen set `chosen`. -/
def neigh (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : ℕ := by
  classical
  exact chosen.card - (chosen.filter (fun x => ¬ G.adj w x)).card

/-- `w` is a legal MCS step given `chosen`. -/
def IsMCSNext (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : Prop :=
  w ∈ (Finset.univ : Finset (Vert n)) \ chosen ∧
  (∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x ≤ G.neigh chosen w) ∧
  (∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x = G.neigh chosen w → w ≤ x)

/-- `order` is a valid MCS ordering of `G`. -/
def IsMCSOrdering (G : UGraph n) (order : List (Vert n)) : Prop :=
  order.Nodup ∧ order.length = n ∧
  ∀ (i : ℕ) (hi : i < order.length),
    IsMCSNext G (order.take i).toFinset (order.get ⟨i, hi⟩)

/-- `G'` differs from `G` only by flipping the undirected edge `{u, v}`. -/
def FlipOf (G G' : UGraph n) (u v : Vert n) : Prop :=
  u ≠ v ∧
  ∀ (x y : Vert n),
    G'.adj x y = G.adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)

/-- Existence of a legal MCS pick whenever not every vertex is already
chosen. -/
theorem exists_IsMCSNext (G : UGraph n) (chosen : Finset (Vert n)) :
    chosen ≠ (Finset.univ : Finset (Vert n)) → ∃ w : Vert n, IsMCSNext G chosen w := by
  classical
  intro hneq
  let U : Finset (Vert n) := (Finset.univ : Finset (Vert n)) \ chosen
  have hUnonempty : U.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hUempty
    apply hneq
    apply Finset.ext
    intro x
    constructor
    · intro _; exact Finset.mem_univ x
    · intro _hxuniv
      by_contra hx
      have hxU : x ∈ U := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      have hxempty : x ∈ (∅ : Finset (Vert n)) := by
        simpa [U, hUempty] using hxU
      exact (Finset.notMem_empty x) hxempty
  rcases Finset.exists_max_image U (fun x => G.neigh chosen x) hUnonempty with ⟨w0, hw0U, hw0max⟩
  let M : Finset (Vert n) := U.filter (fun x => G.neigh chosen x = G.neigh chosen w0)
  have hw0M : w0 ∈ M := by
    exact Finset.mem_filter.mpr ⟨hw0U, rfl⟩
  have hMnonempty : M.Nonempty := ⟨w0, hw0M⟩
  let w : Vert n := M.min' hMnonempty
  refine ⟨w, ?_⟩
  have hwM : w ∈ M := Finset.min'_mem M hMnonempty
  have hwU : w ∈ U := (Finset.mem_filter.mp hwM).1
  have hwcard : G.neigh chosen w = G.neigh chosen w0 := (Finset.mem_filter.mp hwM).2
  unfold IsMCSNext
  constructor
  · simpa [U] using hwU
  constructor
  · intro x hx
    have hxmax : G.neigh chosen x ≤ G.neigh chosen w0 := hw0max x hx
    rw [hwcard]
    exact hxmax
  · intro x hx hc
    have hxM : x ∈ M := by
      exact Finset.mem_filter.mpr ⟨hx, by rw [hc, hwcard]⟩
    change M.min' hMnonempty ≤ x
    exact Finset.min'_le M x hxM

/-- The deterministic MCS pick. -/
noncomputable def greedyPick (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) : { w : Vert n // IsMCSNext G chosen w } :=
  ⟨Classical.choose (exists_IsMCSNext G chosen h),
   Classical.choose_spec (exists_IsMCSNext G chosen h)⟩

/-- Repeatedly extend `chosen` with the MCS pick. -/
noncomputable def mcsLoop (G : UGraph n) (chosen : Finset (Vert n)) (k : ℕ)
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

/-- MCS continuation: greedily extend the already-chosen set `chosen`. -/
noncomputable def mcsRemainder (G : UGraph n) (chosen : Finset (Vert n)) : List (Vert n) :=
  mcsLoop G chosen (n - chosen.card) (by
    have hcard : chosen.card ≤ n := by
      simpa using (Finset.card_le_univ chosen)
    omega)

/-- Greedy continuation of an MCS prefix `pref`. -/
noncomputable def greedySuffix (G : UGraph n) (pref : List (Vert n)) : List (Vert n) :=
  pref ++ mcsRemainder G pref.toFinset

/-- Position (in `order`) of the earlier of the endpoints `u` and `v`. -/
def earlierPos (order : List (Vert n)) (u v : Vert n) : ℕ :=
  min (List.idxOf u order) (List.idxOf v order)

/-- The endpoint placed later in `order`. -/
def laterVert (order : List (Vert n)) (u v : Vert n) : Vert n :=
  if List.idxOf u order ≤ List.idxOf v order then v else u

/-- The endpoint placed earlier in `order`. -/
def earlierVert (order : List (Vert n)) (u v : Vert n) : Vert n :=
  if List.idxOf u order ≤ List.idxOf v order then u else v

/-- Position (in `order`) of the later of the endpoints `u` and `v`. -/
def laterPos (order : List (Vert n)) (u v : Vert n) : ℕ :=
  max (List.idxOf u order) (List.idxOf v order)

/-- Boolean negation of a proposition (classical). -/
noncomputable def isFalse (P : Prop) : Bool :=
  if P then false else true

/-- Auxiliary scan: first illegal position at or after `k`. -/
def firstBreakAux (H : UGraph n) (order : List (Vert n)) :
    ℕ → List (Vert n) → Option ℕ
  | _, [] => none
  | k, x :: xs =>
      if IsMCSNext H (order.take k).toFinset x then firstBreakAux H order (k + 1) xs
      else some k

/-- The first step `k ≥ k0` at which the old ordering's choice is illegal. -/
def firstBreak (H : UGraph n) (order : List (Vert n)) (k0 : ℕ) : Option ℕ :=
  firstBreakAux H order k0 (order.drop k0)

/-- The first breaking step inside the window `[k0, k1]`. -/
def firstBreakWindow (H : UGraph n) (order : List (Vert n)) (k0 k1 : ℕ) : Option ℕ :=
  match firstBreak H order k0 with
  | some k => if k ≤ k1 then some k else none
  | none => none

/-- The deletion probe (semantic form). -/
noncomputable def deletionBreaks (H : UGraph n) (order : List (Vert n))
    (u v : Vert n) : Bool :=
  isFalse (IsMCSNext H (order.take (laterPos order u v)).toFinset
    (laterVert order u v))

/-- `init`: full deterministic greedy MCS from the empty prefix. -/
def initOrder (H : UGraph n) : List (Vert n) :=
  greedySuffix H []

/-- `insert_edge`: scan the window `[pu + 1, pv]` for the first broken step
and regreedy from there. -/
def insertUpdate (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : List (Vert n) :=
  let k := Option.getD (firstBreakWindow H order (earlierPos order u v + 1)
    (laterPos order u v)) order.length
  greedySuffix H (order.take k)

/-- `delete_edge`: keep the order unless the probe at step `pv` fires. -/
def deleteUpdate (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : List (Vert n) :=
  if deletionBreaks H order u v then
    greedySuffix H (order.take (laterPos order u v))
  else
    order

end UGraph

open UGraph

/-! ## Complexity measures (explicit cost model) -/

/-- All ordered adjacency pairs `(u, v)` of `G`. -/
noncomputable def adjPairs (G : UGraph n) : Finset (Vert n × Vert n) := by
  classical
  exact (Finset.univ : Finset (Vert n × Vert n)).filter
    (fun uv : Vert n × Vert n => G.adj uv.1 uv.2)

/-- Number of undirected edges in `G`. -/
noncomputable def edgeCount (G : UGraph n) : ℕ :=
  (adjPairs G).card / 2

/-- All ordered adjacency pairs touching `S`. -/
noncomputable def mSuffixPairs (G : UGraph n) (S : Finset (Vert n)) :
    Finset (Vert n × Vert n) := by
  classical
  exact (Finset.univ : Finset (Vert n × Vert n)).filter
    (fun uv : Vert n × Vert n => G.adj uv.1 uv.2 ∧ (uv.1 ∈ S ∨ uv.2 ∈ S))

/-- Number of undirected edges of `G` touching `S`. -/
noncomputable def mSuffix (G : UGraph n) (S : Finset (Vert n)) : ℕ :=
  (mSuffixPairs G S).card / 2

/-- The probe cost: recursion depth of `firstBreakAux`. -/
def probeCost (H : UGraph n) (order : List (Vert n)) : ℕ → List (Vert n) → ℕ
  | _, [] => 0
  | k, x :: xs =>
      if IsMCSNext H (order.take k).toFinset x then
        1 + probeCost H order (k + 1) xs
      else 1

/-- Insertion cost measure. -/
noncomputable def insertCost (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : ℕ :=
  probeCost H order (earlierPos order u v + 1) (order.drop (earlierPos order u v + 1))
  + match firstBreakWindow H order (earlierPos order u v + 1) (laterPos order u v) with
    | none => 0
    | some k0 => (order.drop k0).length + 2 * mSuffix H (order.drop k0).toFinset

/-- Deletion cost measure. -/
noncomputable def deleteCost (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : ℕ :=
  probeCost H order (laterPos order u v) (order.drop (laterPos order u v))
  + match firstBreak H order (laterPos order u v) with
    | none => 0
    | some _ => (order.drop (laterPos order u v)).length
                + 2 * mSuffix H (order.drop (laterPos order u v)).toFinset

/-! ## Executable model (concrete boolean adjacency matrix) -/

/-- A concrete adjacency matrix. -/
abbrev Adj (n : ℕ) := List (List Bool)

/-- Row lookup. -/
def atRow : List Bool → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: rest, k+1 => atRow rest k

/-- `getAdj a u v`: is edge (u,v) present in the undirected adjacency `a`? -/
def getAdj (a : Adj n) (u v : ℕ) : Bool :=
  match a[u]? with
  | none => false
  | some row => atRow row v

/-- Number of chosen neighbors of `w`. -/
def cardC (a : Adj n) (chosen : List ℕ) (w : ℕ) : ℕ :=
  (chosen.filter (fun v => getAdj a v w)).length

/-- MCS pick: among remaining vertices, the one with maximum cardinality,
tie-broken by smallest vertex id. -/
def bestPick (a : Adj n) (chosen : List ℕ) (rem : List ℕ) : ℕ :=
  rem.foldl (fun best v =>
    let cb := cardC a chosen best
    let cv := cardC a chosen v
    if cv > cb ∨ (cv = cb ∧ v < best) then v else best)
    (rem.headD 0)

/-- One MCS step. -/
def mcsStep (a : Adj n) (st : List ℕ × List ℕ) : List ℕ × List ℕ :=
  let (chosen, rem) := st
  match rem with
  | [] => st
  | _ => let v := bestPick a chosen rem; (v :: chosen, rem.erase v)

/-- Computable MCS ordering of `a`. -/
def mcsOrder (a : Adj n) : List ℕ :=
  let n := a.length
  let st := ((List.range n).foldl (fun s _ => mcsStep a s) ([], List.range n))
  st.1.reverse

/-- Flip undirected edge (u,v): set symmetric entries to `present`. -/
def setEdge (n : ℕ) (a : Adj n) (u v : ℕ) (present : Bool) : Adj n :=
  List.mapIdx (fun i row =>
    List.mapIdx (fun j b =>
      if i = u ∧ j = v ∨ i = v ∧ j = u then present else b) row) a

/-- Insert edge. -/
def insertEdge (n : ℕ) (a : Adj n) (u v : ℕ) : Adj n := setEdge n a u v true

/-- Delete edge. -/
def deleteEdge (n : ℕ) (a : Adj n) (u v : ℕ) : Adj n := setEdge n a u v false

/-- A concrete adjacency matrix is *well-shaped* (square). -/
def WellShaped (n : ℕ) (a : Adj n) : Prop :=
  a.length = n ∧ ∀ x : ℕ, x < n → ∃ row : List Bool, a[x]? = some row ∧ row.length = n

/-- Build the abstract UGraph from an executable adjacency matrix. -/
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
        rw [firstBreakAux, DynamicMCS.Eea71821.firstBreakAux]
        rw [if_pos hx]
        rw [if_pos hxD]
        exact ih (k + 1)
      · have hxD : ¬ DynamicMCS.UGraph.IsMCSNext (toDyn H) (order.take k).toFinset x := by
          intro h
          exact hx ((IsMCSNext_toDyn H (order.take k).toFinset x).mp h)
        rw [firstBreakAux, DynamicMCS.Eea71821.firstBreakAux]
        rw [if_neg hx]
        rw [if_neg hxD]

/-- `firstBreak` computes equal options across the namespaces. -/
lemma firstBreak_eq (H : UGraph n) (order : List (Vert n)) (k0 : ℕ) :
    firstBreak H order k0 = DynamicMCS.Eea71821.firstBreak (toDyn H) order k0 := by
  unfold firstBreak DynamicMCS.Eea71821.firstBreak
  exact firstBreakAux_eq H order k0 (order.drop k0)

/-- `firstBreakWindow` computes equal options across the namespaces. -/
lemma deletionBreaks_eq (H : UGraph n) (order : List (Vert n)) (u v : Vert n) :
    deletionBreaks H order u v = DynamicMCS.Eea71821.deletionBreaks (toDyn H) order u v := by
  unfold deletionBreaks DynamicMCS.Eea71821.deletionBreaks
  rw [← laterPos_eq, ← laterVert_eq]
  change isFalse (IsMCSNext H (order.take (laterPos order u v)).toFinset
      (laterVert order u v))
    = isFalse ((toDyn H).IsMCSNext (order.take (laterPos order u v)).toFinset
      (laterVert order u v))
  congr 1

/-- Regreeding from a full prefix is trivial for `initOrder`. -/

lemma firstBreakWindow_eq (H : UGraph n) (order : List (Vert n)) (k0 k1 : ℕ) :
    firstBreakWindow H order k0 k1 = DynamicMCS.Eea71821.firstBreakWindow (toDyn H) order k0 k1 := by
  unfold firstBreakWindow DynamicMCS.Eea71821.firstBreakWindow
  rw [firstBreak_eq]
  rfl

/-- `probeCost` computes equal costs across the namespaces. -/
lemma probeCost_eq (H : UGraph n) (order : List (Vert n)) (k : ℕ) (xs : List (Vert n)) :
    probeCost H order k xs = ProbeCost.probeCost (toDyn H) order k xs := by
  induction xs generalizing k with
  | nil =>
      rw [probeCost, ProbeCost.probeCost]
  | cons x xs ih =>
      by_cases hx : IsMCSNext H (order.take k).toFinset x
      · have hxD : DynamicMCS.UGraph.IsMCSNext (toDyn H) (order.take k).toFinset x :=
          (IsMCSNext_toDyn H (order.take k).toFinset x).mpr hx
        rw [probeCost, ProbeCost.probeCost]
        rw [if_pos hx]
        rw [if_pos hxD]
        congr 1
        exact ih (k + 1)
      · have hxD : ¬ DynamicMCS.UGraph.IsMCSNext (toDyn H) (order.take k).toFinset x := by
          intro h
          exact hx ((IsMCSNext_toDyn H (order.take k).toFinset x).mp h)
        rw [probeCost, ProbeCost.probeCost]
        rw [if_neg hx]
        rw [if_neg hxD]

/-- `edgeCount` computes equal counts across the namespaces. -/
lemma edgeCount_eq (G : UGraph n) :
    edgeCount G = CountBridge.edgeCount (toDyn G) := by
  unfold edgeCount adjPairs CountBridge.edgeCount CountBridge.adjPairs toDyn
  rfl

/-- `mSuffix` computes equal counts across the namespaces. -/
lemma mSuffix_eq (G : UGraph n) (S : Finset (Vert n)) :
    mSuffix G S = CountBridge.mSuffix (toDyn G) S := by
  unfold mSuffix mSuffixPairs CountBridge.mSuffix CountBridge.mSuffixPairs toDyn
  rfl

/-- `initOrder` computes equal lists across the namespaces. -/
lemma initOrder_eq (G : UGraph n) :
    initOrder G = DynamicMCS.Eea71821.initOrder (toDyn G) := by
  unfold initOrder DynamicMCS.Eea71821.initOrder
  exact greedySuffix_eq G []

/-- `insertCost` transports to `ComplexityHeadlines.insertCost`. -/
lemma insertCost_eq (G : UGraph n) (order : List (Vert n)) (u v : Vert n) :
    insertCost G order u v = ComplexityHeadlines.insertCost (toDyn G) order u v := by
  unfold insertCost ComplexityHeadlines.insertCost
  rw [earlierPos_eq, laterPos_eq]
  simp
  congr 1
  · rw [probeCost_eq]
  · rw [firstBreakWindow_eq]
    rfl

/-- `deleteCost` transports to `ComplexityHeadlines.deleteCost`. -/
lemma deleteCost_eq (G : UGraph n) (order : List (Vert n)) (u v : Vert n) :
    deleteCost G order u v = ComplexityHeadlines.deleteCost (toDyn G) order u v := by
  unfold deleteCost ComplexityHeadlines.deleteCost
  rw [laterPos_eq]
  simp
  congr 1
  · rw [probeCost_eq]
  · rw [firstBreak_eq]
    rfl

/-- Executable row lookup agrees with the abstract one (identical bodies). -/
lemma atRow_eq (row : List Bool) (v : ℕ) : atRow row v = Exec.atRow row v := by
  induction row generalizing v with
  | nil => rfl
  | cons b t ih =>
      cases v with
      | zero => rfl
      | succ v' => simpa [atRow, Exec.atRow] using ih v'

/-- Executable `getAdj` agrees with the abstract one (identical bodies). -/
lemma getAdj_eq (n : ℕ) (a : Adj n) (u v : ℕ) : getAdj a u v = @Exec.getAdj n a u v := by
  cases h : a[u]? with
  | none => simp [getAdj, Exec.getAdj, h]
  | some row =>
      have h1 : getAdj a u v = atRow row v := by simp [getAdj, h]
      have h2 : @Exec.getAdj n a u v = Exec.atRow row v := by simp [Exec.getAdj, h]
      rw [h1, h2]
      exact atRow_eq row v

/-- `Transport` (toDyn) of a `toUGraph` built from an executable matrix is
exactly `Exec.toUGraph` on the same matrix (proofs re-typed through
`getAdj_eq`; proof irrelevance makes the carried proofs irrelevant). -/
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

/-- Executable `setEdge` agrees with the abstract one (identical bodies). -/
lemma setEdge_eq (n : ℕ) (a : Adj n) (u v : ℕ) (present : Bool) :
    setEdge n a u v present = @Exec.setEdge n a u v present := by
  unfold setEdge Exec.setEdge
  rfl

/-- Executable `insertEdge` agrees with the abstract one. -/
lemma insertEdge_eq (n : ℕ) (a : Adj n) (u v : ℕ) :
    insertEdge n a u v = @Exec.insertEdge n a u v := by
  unfold insertEdge Exec.insertEdge setEdge Exec.setEdge
  rfl

/-- Executable `deleteEdge` agrees with the abstract one. -/
lemma deleteEdge_eq (n : ℕ) (a : Adj n) (u v : ℕ) :
    deleteEdge n a u v = @Exec.deleteEdge n a u v := by
  unfold deleteEdge Exec.deleteEdge setEdge Exec.setEdge
  rfl

/-- Executable `cardC` agrees with the abstract one (via `getAdj_eq`). -/
lemma cardC_eq (a : Adj n) (chosen : List ℕ) (w : ℕ) :
    cardC a chosen w = @Exec.cardC n a chosen w := by
  unfold cardC Exec.cardC
  congr 1
  congr 1
  funext v
  exact getAdj_eq n a v w

/-- Executable `bestPick` agrees with the abstract one. -/
lemma bestPick_eq (a : Adj n) (chosen : List ℕ) (rem : List ℕ) :
    bestPick a chosen rem = @Exec.bestPick n a chosen rem := by
  unfold bestPick Exec.bestPick
  induction rem with
  | nil => rfl
  | cons v vs ih =>
      simp [List.foldl, cardC_eq, ih]

/-- Executable `mcsStep` agrees with the abstract one. -/
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

/-- Executable `mcsOrder` agrees with the abstract one. -/
lemma mcsOrder_eq (a : Adj n) : mcsOrder a = @Exec.mcsOrder n a := by
  unfold mcsOrder Exec.mcsOrder
  simp [foldl_mcsStep_eq a]

end Transport
end Challenge