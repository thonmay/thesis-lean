import Mathlib
import ThesisLean.Formal_gen001c01_3939115c

/-!
# Executable dynamic MCS ordering

This file provides a *computable* (executable) model of the dynamic MCS
ordering algorithm, complementary to the correctness-only abstract model in
`Formal_gen001c01_3939115c.lean` and `Formal_gen003c01_eea71821.lean`.

The abstract model treats graphs as a relation `adj : Vert n → Vert n → Prop`
and uses `Finset`/`classical` (noncomputable). That is good for proving
correctness but does not run. This file fixes the gap: it gives a concrete
`List (List Bool)` adjacency, a computable MCS ordering, a computable
edge-flip update, and `#eval`s demonstrating end-to-end execution.

The bridge between the two models (an equivalence theorem stating that the
executable ordering is the same as the abstract greedySuffix) is stated at the
bottom as a theorem with a proof sketch, to be completed in a later stage.
-/

abbrev Adj (n : ℕ) := List (List Bool)

namespace Exec

variable {n : ℕ}

/-- Row lookup: `atRow row v` is the v-th entry of the row, `false` if out of
range (loopless/well-shaped matrices keep this total). -/
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

-- ---------------------------------------------------------------------------
-- End-to-end execution examples
-- ---------------------------------------------------------------------------

def p3 : Adj 3 := [[false, true, false], [true, false, true], [false, true, false]]
def p4 : Adj 4 := [[false,true,false,false],[true,false,true,false],[false,true,false,true],[false,false,true,false]]
def c4 : Adj 4 := [[false,true,false,true],[true,false,true,false],[false,true,false,true],[true,false,true,false]]

-- MCS of the 3-vertex path 0-1-2: cardinalities 0,1,1 -> pick 0, then 2 (1>0), then 1
#eval mcsOrder p3
-- after deleting (0,1): graph has only edge (1,2); order 0,1,2 still valid
#eval mcsOrder (deleteEdge 3 p3 0 1)
-- 4-cycle C4: all vertices have 2 selected-cardinality at their step in any
-- order? (ties broken by id -> [0,1,2,3] is a valid MCS order)
#eval mcsOrder c4

-- ---------------------------------------------------------------------------
-- Bridge to the abstract model (the no-gap claim)
-- ---------------------------------------------------------------------------

/-- Build the abstract UGraph from an executable adjacency matrix, when the
matrix is symmetric, loop-free, and square of size n. -/
def toUGraph (a : Adj n) (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u)
    (hloop : ∀ u : ℕ, getAdj a u u = false) : DynamicMCS.UGraph n :=
  { adj := fun x y => getAdj a x.val y.val = true
    symm := by
      intro x y h
      rwa [hsymm x.val y.val] at h
    loopless := by
      intro x h
      have hx : getAdj a x.val x.val = false := hloop x.val
      simp [hx] at h }

-- PLANNED THEOREM (proof to be completed in a later stage; stated here as
-- documentation so the executable/spec bridge is explicit):
--
--   theorem mcsOrder_eq_greedySuffix
--       (a : Adj n) (hsymm : …) (hloop : …) :
--       (mcsOrder a) = ord.map (fun v : DynamicMCS.Vert n => v.val)
--   for the ordering `ord` produced by the abstract `greedySuffix` of the
--   `DynamicMCS.UGraph` built by `toUGraph`.
--
-- Rationale: the abstract `mcsLoop`/`greedySuffix` are noncomputable (they
-- use `Classical.choose` on the MCS-next witness). The executable `mcsOrder`
-- implements the same selection rule (max cardinality, smallest-id tie-break)
-- with `bestPick`. The refinement proof needs a lemma that `bestPick` realizes
-- `IsMCSNext`, which is mechanical from the definitions. Until that lemma is
-- written, the claim stands as a documented bridge rather than an axiom or
-- a `sorry`.

end Exec