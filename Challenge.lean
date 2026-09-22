import Mathlib

/-!
# Challenge: Dynamic MCS ordering maintenance

Independent statement of the headline results of a Lean 4 / Mathlib
formalization of a fully-dynamic Maximum-Cardinality-Search (MCS) ordering
algorithm under single-edge insertions and deletions.

Problem.  MCS on an undirected loop-free graph repeatedly chooses an unchosen
vertex with the maximum number of already-chosen neighbors, ties broken by
the lowest vertex index; the resulting order is a *valid MCS ordering*.

Algorithm.  A *probe-then-repair* update.  Flipping an edge `{u, v}` changes
selection-time cardinalities only for steps in the affected window between the
two endpoints (insertion) or at the later endpoint (deletion).  The candidate
probes that tight window for the first step at which the current ordering's
choice is no longer legal on the post-update graph, and only then regreedies
the suffix from that step (bucket / Rose-Tarjan recomputation).  The same
adjacency structure supports insertion and deletion.

Definitions are restated here **verbatim** from the project development (their
bodies are identical up to the namespace) so that the comparator can check the
Solution (real proofs, same statements) against this Challenge statement.  All
headline theorems below are stated with `sorry`-bodies; the Solution module
proves them.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace Challenge

/-- Vertices of an `n`-vertex undirected graph. -/
abbrev Vert (n : ℕ) := Fin n

/-- A finite undirected, loop-free graph on the vertices `Fin n`. -/
structure UGraph (n : ℕ) where
  adj : Vert n → Vert n → Prop
  symm : ∀ {x y : Vert n}, adj x y → adj y x
  loopless : ∀ (x : Vert n), ¬ adj x x

namespace UGraph

variable {n : ℕ} {G G' : UGraph n}

/-- Cardinality of `w` measured against the already-chosen set `chosen`,
i.e. the number of neighbors of `w` lying in `chosen`. -/
def neigh (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : ℕ := by
  classical
  exact chosen.card - (chosen.filter (fun x => ¬ G.adj w x)).card

/-- `w` is a legal MCS step given `chosen`: `w` is unchosen, its cardinality
is maximal among the unchosen vertices, and it is the least-index vertex
achieving that maximum (the candidate's lowest-index tie-breaking rule). -/
def IsMCSNext (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : Prop :=
  w ∈ (Finset.univ : Finset (Vert n)) \ chosen ∧
  (∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x ≤ G.neigh chosen w) ∧
  (∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x = G.neigh chosen w → w ≤ x)

/-- `order` is a valid MCS ordering of `G`: it lists every vertex exactly
once and, at every position `i`, the vertex `order[i]` is the legal MCS pick
given the vertices chosen before position `i`. -/
def IsMCSOrdering (G : UGraph n) (order : List (Vert n)) : Prop :=
  order.Nodup ∧ order.length = n ∧
  ∀ (i : ℕ) (hi : i < order.length),
    IsMCSNext G (order.take i).toFinset (order.get ⟨i, hi⟩)

/-- `G'` differs from `G` only by flipping the undirected edge `{u, v}`:
outside the two ordered pairs `(u, v)` and `(v, u)` the adjacency is
unchanged, and `u ≠ v`. -/
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

/-- The deterministic MCS pick: the least-index maximum-cardinality unchosen
vertex.  Carried with the proof that it is a legal MCS step. -/
noncomputable def greedyPick (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) : { w : Vert n // IsMCSNext G chosen w } :=
  ⟨Classical.choose (exists_IsMCSNext G chosen h),
   Classical.choose_spec (exists_IsMCSNext G chosen h)⟩

/-- Repeatedly extend `chosen` with the MCS pick until every vertex is
chosen, with one step per unit of the counter `k`.  The invariant
`chosen.card + k = n` certifies that `k` further MCS steps suffice. -/
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

/-- MCS continuation: greedily extend the already-chosen set `chosen` to a
full ordering suffix. -/
noncomputable def mcsRemainder (G : UGraph n) (chosen : Finset (Vert n)) : List (Vert n) :=
  mcsLoop G chosen (n - chosen.card) (by
    have hcard : chosen.card ≤ n := by
      simpa using (Finset.card_le_univ chosen)
    omega)

/-- Greedy continuation of an MCS prefix `pref`: the fixed prefix followed by
the deterministically recomputed suffix. -/
noncomputable def greedySuffix (G : UGraph n) (pref : List (Vert n)) : List (Vert n) :=
  pref ++ mcsRemainder G pref.toFinset

/-- Position (in `order`) of the earlier of the endpoints `u` and `v`. -/
def earlierPos (order : List (Vert n)) (u v : Vert n) : ℕ :=
  min (List.idxOf u order) (List.idxOf v order)

/-- The endpoint placed later in `order` (the candidate's `v` after its
possible swap of the two endpoints). -/
def laterVert (order : List (Vert n)) (u v : Vert n) : Vert n :=
  if List.idxOf u order ≤ List.idxOf v order then v else u

/-- The endpoint placed earlier in `order` (the candidate's `u` after its
possible swap of the two endpoints). -/
def earlierVert (order : List (Vert n)) (u v : Vert n) : Vert n :=
  if List.idxOf u order ≤ List.idxOf v order then u else v

/-- Position (in `order`) of the later of the endpoints `u` and `v`. -/
def laterPos (order : List (Vert n)) (u v : Vert n) : ℕ :=
  max (List.idxOf u order) (List.idxOf v order)

/-- Boolean negation of a proposition (classical): `isFalse P = true`
exactly when `P` is false.  (Makes the deletion probe a `Bool`.) -/
noncomputable def isFalse (P : Prop) : Bool :=
  if P then false else true

/-- Auxiliary scan: the first position at or after `k`, measured against the
prefix `order.take k`, at which the old choice `x` is not a legal MCS pick
on `H`. -/
def firstBreakAux (H : UGraph n) (order : List (Vert n)) :
    ℕ → List (Vert n) → Option ℕ
  | _, [] => none
  | k, x :: xs =>
      if IsMCSNext H (order.take k).toFinset x then firstBreakAux H order (k + 1) xs
      else some k

/-- The first step `k ≥ k0` at which the old ordering's choice is illegal on
`H`, or `none` if every step from `k0` to the end stays legal. -/
def firstBreak (H : UGraph n) (order : List (Vert n)) (k0 : ℕ) : Option ℕ :=
  firstBreakAux H order k0 (order.drop k0)

/-- The first breaking step inside the window `[k0, k1]`, or `none` if the
whole window survives (the candidate's bounded `_first_break` scan). -/
def firstBreakWindow (H : UGraph n) (order : List (Vert n)) (k0 k1 : ℕ) : Option ℕ :=
  match firstBreak H order k0 with
  | some k => if k ≤ k1 then some k else none
  | none => none

/-- The deletion probe (candidate `_deletion_breaks`), in *semantic* form:
at step `pv = laterPos` the later endpoint `w` is *not* a legal MCS pick on
`H`. -/
noncomputable def deletionBreaks (H : UGraph n) (order : List (Vert n))
    (u v : Vert n) : Bool :=
  isFalse (IsMCSNext H (order.take (laterPos order u v)).toFinset
    (laterVert order u v))

/-- `init`: full deterministic greedy MCS from the empty prefix (the
candidate's `_regreedy` from step 0). -/
def initOrder (H : UGraph n) : List (Vert n) :=
  greedySuffix H []

/-- `insert_edge`: scan the window `[pu + 1, pv]` for the first broken step
and regreedy from there; if the window survives, keep the whole order
(`greedySuffix H order` is the identity on a full order). -/
def insertUpdate (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : List (Vert n) :=
  let k := Option.getD (firstBreakWindow H order (earlierPos order u v + 1)
    (laterPos order u v)) order.length
  greedySuffix H (order.take k)

/-- `delete_edge`: keep the order unless the probe at step `pv` fires, in
which case regreedy from `pv`. -/
def deleteUpdate (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : List (Vert n) :=
  if deletionBreaks H order u v then
    greedySuffix H (order.take (laterPos order u v))
  else
    order

end UGraph

open UGraph

/-! ## Complexity measures (explicit cost model) -/

/-- All ordered adjacency pairs `(u, v)` of `G`, i.e. the directed edges. -/
noncomputable def adjPairs (G : UGraph n) : Finset (Vert n × Vert n) := by
  classical
  exact (Finset.univ : Finset (Vert n × Vert n)).filter
    (fun uv : Vert n × Vert n => G.adj uv.1 uv.2)

/-- Number of undirected edges in `G`, i.e. the directed adjacency-pair count
divided by two.  Exact because the count is even (adjacency is symmetric and
loop-free). -/
noncomputable def edgeCount (G : UGraph n) : ℕ :=
  (adjPairs G).card / 2

/-- All ordered adjacency pairs touching `S`, i.e. with at least one endpoint
in `S`. -/
noncomputable def mSuffixPairs (G : UGraph n) (S : Finset (Vert n)) :
    Finset (Vert n × Vert n) := by
  classical
  exact (Finset.univ : Finset (Vert n × Vert n)).filter
    (fun uv : Vert n × Vert n => G.adj uv.1 uv.2 ∧ (uv.1 ∈ S ∨ uv.2 ∈ S))

/-- Number of undirected edges of `G` with at least one endpoint in `S`. -/
noncomputable def mSuffix (G : UGraph n) (S : Finset (Vert n)) : ℕ :=
  (mSuffixPairs G S).card / 2

/-- The probe cost: the recursion depth of `firstBreakAux`, i.e. the number of
list elements the scan examines before it first finds an illegal MCS step
(`1` counts the broken step itself).  For a legal list this equals the full
list length. -/
def probeCost (H : UGraph n) (order : List (Vert n)) : ℕ → List (Vert n) → ℕ
  | _, [] => 0
  | k, x :: xs =>
      if IsMCSNext H (order.take k).toFinset x then
        1 + probeCost H order (k + 1) xs
      else 1

/-- The explicit cost measure for an insertion of edge `{u, v}`: the probe
scan over the window `[earlierPos u v + 1, laterPos u v]` plus, if a break is
found at `k0` inside the window, the regreedy work on the suffix from `k0`
(one vertex-touch per suffix element plus two edge-touches per edge incident
to the suffix).  Mirrors `insertUpdate`. -/
noncomputable def insertCost (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : ℕ :=
  probeCost H order (earlierPos order u v + 1) (order.drop (earlierPos order u v + 1))
  + match firstBreakWindow H order (earlierPos order u v + 1) (laterPos order u v) with
    | none => 0
    | some k0 => (order.drop k0).length + 2 * mSuffix H (order.drop k0).toFinset

/-- The explicit cost measure for a deletion of edge `{u, v}`: the probe check
at `laterPos u v` plus, if a break is found there, the regreedy work on the
suffix from `laterPos u v`.  Mirrors `deleteUpdate`. -/
noncomputable def deleteCost (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : ℕ :=
  probeCost H order (laterPos order u v) (order.drop (laterPos order u v))
  + match firstBreak H order (laterPos order u v) with
    | none => 0
    | some _ => (order.drop (laterPos order u v)).length
                + 2 * mSuffix H (order.drop (laterPos order u v)).toFinset

/-! ## Executable model (concrete boolean adjacency matrix) -/

/-- A concrete adjacency matrix: `n` rows of `n` booleans (the type parameter
`n` is phantom; well-shapedness is a separate hypothesis). -/
abbrev Adj (n : ℕ) := List (List Bool)

/-- Row lookup: `atRow row v` is the v-th entry of the row, `false` if out of
range. -/
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

/-- One MCS step: state is (chosen-in-reverse, remaining). -/
def mcsStep (a : Adj n) (st : List ℕ × List ℕ) : List ℕ × List ℕ :=
  let (chosen, rem) := st
  match rem with
  | [] => st
  | _ => let v := bestPick a chosen rem; (v :: chosen, rem.erase v)

/-- Computable MCS ordering of `a` (ties broken by smallest id). -/
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

/-- A concrete adjacency matrix is *well-shaped* (square with `n` rows and
`n` columns).  This is exactly the precondition for `setEdge` to flip entries
inside the `Fin n` vertex domain. -/
def WellShaped (n : ℕ) (a : Adj n) : Prop :=
  a.length = n ∧ ∀ x : ℕ, x < n → ∃ row : List Bool, a[x]? = some row ∧ row.length = n

/-- Build the abstract UGraph from an executable adjacency matrix, when the
matrix is symmetric, loop-free, and square of size n. -/
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

/-! ## Headline theorems (Proofs supplied by the Solution module) -/

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

/-- The insertion update runs in `O(n + m)` time measured by `insertCost`,
where `n` is the vertex count and `m` the edge count of the current graph. -/
theorem insert_complexity :
    ∃ c : ℕ,
      ∀ (n : ℕ) (G : UGraph n) (order : List (Vert n)) (u v : Vert n),
        order.length ≤ n →
          insertCost G order u v ≤ c * (n + edgeCount G) := by
  sorry

/-- The deletion update runs in `O(n + m)` time measured by `deleteCost`. -/
theorem delete_complexity :
    ∃ c : ℕ,
      ∀ (n : ℕ) (G : UGraph n) (order : List (Vert n)) (u v : Vert n),
        order.length ≤ n →
          deleteCost G order u v ≤ c * (n + edgeCount G) := by
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
  sorry

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
  sorry

end Challenge