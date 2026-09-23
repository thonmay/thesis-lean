import Mathlib
import ThesisLean.Formal_gen001c01_3939115c
import ThesisLean.Formal_gen003c01_eea71821
import ThesisLean.CountBridge
import ThesisLean.ProbeCost
import ThesisLean.McsInvariant

/-!
# Complexity headlines for the dynamic MCS update

This module realizes the informal asymptotic claims "O(n + m) per update" for
the dynamic MCS candidate `gen003_c01` (see the module `Formal_gen003c01`)
as *explicit, finite, division-free* bounds.  We fix two concrete cost measures,
`insertCost` and `deleteCost`, which are combinatorial surrogates for the
noncomputable `greedySuffix` regreedy on an insertion or deletion of a single
edge `{u, v}`:

* **probe cost** `probeCost`: the number of ordering positions the scan
  examines while searching for the first step at which the old greedy choice is
  no longer legal on the post-update graph.  This is `ProbeCost.probeCost`
  (the recursion depth of `firstBreakAux`); for insertion the scan runs over
  the full suffix from `earlierPos u v + 1` (the result is then filtered to
  the window `[earlierPos u v + 1, laterPos u v]`), for deletion over the
  suffix from `laterPos u v`.
* **regreedy work**: when a break is found, the candidate recomputes the
  suffix from the breaking step with a bucket/bitmask MCS, which touches each
  vertex of the suffix once (`(order.drop k0).length`) and each edge incident
  to the suffix twice (once per direction): `2 * mSuffix H (order.drop k0)`,
  where `mSuffix` counts undirected edges touching a vertex set.  When no
  break is found the regreedy is skipped and this contribution is `0`.

The `2 *` counts both directions of an edge touch; `mSuffix` already counts
each undirected edge once, so doubling accounts for the endpoint side that is
scanned.  The constant `2` is not sacred: what is rigorous here is that the
measure is explicit, finite, and bounded by `c * (n + edgeCount H)` for an
integer constant `c`.

**Honesty note.**  The measures define *one* layered realization of the cost
(a probe over the ordering plus, only in the breaking case, a regreedy that is
linear in the touched suffix and incident edges).  They do **not** claim that
the noncomputable abstract `greedySuffix` runs in O(n + m): `greedySuffix`
(and `mcsRemainder`) is a noncomputable, unbounded function whose real cost is
left unformalized.  The bounds below are about the *explicit operational cost
measures* spelled out here, which are the honest breakdown of what the
bucket/bitmask implementation spends.

**Why the statement needs `order.length ≤ n`.**  The stated bound is
`insertCost ≤ c * (n + edgeCount H)` where `c` does not depend on `order`.  A
valid MCS ordering on `n` vertices satisfies `order.length = n`; but the cost
measures are defined for *arbitrary* lists, and for an arbitrary list
`order.drop k0` may have unbounded length, making both `probeCost` and
`(order.drop k0).length` unbounded.  So the honest headline quantifies over
orderings with `order.length ≤ n` (a hypothesis automatically satisfied by
every state the algorithm ever maintains, since those are valid MCS
orderings), and holds with `c = 2`.
-/

open DynamicMCS
open DynamicMCS.UGraph
open DynamicMCS.Eea71821
open ProbeCost
open CountBridge

noncomputable section

namespace ComplexityHeadlines

/-- The explicit cost measure for an insertion of edge `{u, v}`: the probe
scan over the window `[earlierPos u v + 1, laterPos u v]` plus, if a break is
found at `k0` inside the window, the regreedy work on the suffix from `k0`
(one vertex-touch per suffix element plus two edge-touches per edge incident
to the suffix).  Mirrors `Eea71821.insertUpdate`. -/
noncomputable def insertCost (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : ℕ :=
  probeCost H order (earlierPos order u v + 1) (order.drop (earlierPos order u v + 1))
  + match firstBreakWindow H order (earlierPos order u v + 1) (laterPos order u v) with
    | none => 0
    | some k0 => (order.drop k0).length + 2 * CountBridge.mSuffix H (order.drop k0).toFinset

/-- The explicit cost measure for a deletion of edge `{u, v}`: the probe check
at `laterPos u v` plus, if a break is found there, the regreedy work on the
suffix from `laterPos u v`.  Mirrors `Eea71821.deleteUpdate`. -/
noncomputable def deleteCost (H : UGraph n) (order : List (Vert n)) (u v : Vert n) : ℕ :=
  probeCost H order (laterPos order u v) (order.drop (laterPos order u v))
  + match firstBreak H order (laterPos order u v) with
    | none => 0
    | some _ => (order.drop (laterPos order u v)).length
                + 2 * CountBridge.mSuffix H (order.drop (laterPos order u v)).toFinset

/-! ## Incremental complexity headline -/

/-- The incremental complexity headline (witness form, no division): there is
an integer constant `c = 2` such that for every `n`, every `n`-vertex graph
`H`, and every ordering `order` with `order.length ≤ n` (in particular every
valid MCS ordering), the insertion cost on any edge `{u, v}` is at most
`2 * (n + edgeCount H)`.  Non-breaking case: cost is just the probe, at most
`n`.  Breaking case: cost is probe + suffix-touches + incident-edge touches,
each bounded by `n`, `n`, and `2 * edgeCount H`; and
`n + n + 2 * edgeCount ≤ 2 * (n + edgeCount)`. -/
theorem insert_complexity :
    ∃ c : ℕ,
      ∀ (n : ℕ) (H : UGraph n) (order : List (Vert n)) (u v : Vert n),
        order.length ≤ n →
          insertCost H order u v ≤ c * (n + CountBridge.edgeCount H) := by
  refine ⟨2, ?_⟩
  intro n H order u v hord
  have hprob :
      probeCost H order (earlierPos order u v + 1)
        (order.drop (earlierPos order u v + 1)) ≤ n := by
    exact le_trans (probeCost_le_n H order (earlierPos order u v + 1)) hord
  have hm2 : ∀ k : ℕ,
      2 * CountBridge.mSuffix H (order.drop k).toFinset
        ≤ 2 * CountBridge.edgeCount H := by
    intro k
    exact Nat.mul_le_mul_left 2 (CountBridge.mSuffix_le_edgeCount H (order.drop k).toFinset)
  by_cases hwin : firstBreakWindow H order (earlierPos order u v + 1)
      (laterPos order u v) = none
  · -- the whole window survives: cost is just the probe
    rw [insertCost, hwin]
    simp
    omega
  · -- a break is found at some k0 inside the window: regreedy from k0
    rcases Option.ne_none_iff_exists.mp hwin with ⟨k0, hk0⟩
    rw [insertCost]
    rw [← hk0]
    simp
    have hdrop : (order.drop k0).length ≤ n := by
      rw [List.length_drop]
      omega
    have hm2k : 2 * CountBridge.mSuffix H (order.drop k0).toFinset
        ≤ 2 * CountBridge.edgeCount H := hm2 k0
    omega

/-! ## Decremental complexity headline -/

/-- The decremental complexity headline (witness form, no division): the same
`c = 2` bounds the deletion cost on any edge `{u, v}` for any ordering with
`order.length ≤ n`.  The deletion probe scans the suffix from `laterPos u v`
(at most `n` positions); the regreedy (only when the probe fires at
`laterPos u v`) is again suffix-touches `≤ n` plus incident-edge touches
`≤ 2 * edgeCount H`. -/
theorem delete_complexity :
    ∃ c : ℕ,
      ∀ (n : ℕ) (H : UGraph n) (order : List (Vert n)) (u v : Vert n),
        order.length ≤ n →
          deleteCost H order u v ≤ c * (n + CountBridge.edgeCount H) := by
  refine ⟨2, ?_⟩
  intro n H order u v hord
  have hprob :
      probeCost H order (laterPos order u v) (order.drop (laterPos order u v)) ≤ n := by
    exact le_trans (probeCost_le_n H order (laterPos order u v)) hord
  have hdrop : (order.drop (laterPos order u v)).length ≤ n := by
    rw [List.length_drop]
    omega
  have hm2 : 2 * CountBridge.mSuffix H (order.drop (laterPos order u v)).toFinset
      ≤ 2 * CountBridge.edgeCount H := by
    exact Nat.mul_le_mul_left 2 (CountBridge.mSuffix_le_edgeCount H
      (order.drop (laterPos order u v)).toFinset)
  by_cases hdel : firstBreak H order (laterPos order u v) = none
  · -- no break: cost is just the probe
    rw [deleteCost, hdel]
    simp
    omega
  · -- the probe fires at laterPos: regreedy from laterPos
    rw [deleteCost]
    rcases Option.ne_none_iff_exists.mp hdel with ⟨k0, hk0⟩
    rw [← hk0]
    simp
    omega

/-! ## Space headline

The state of the bucket/bitmask implementation holds (i) the adjacency as an
`n × n` boolean matrix = `n * n` cells, and (ii) the current ordering as a
list of length `n` (hence O(n) additional words).  `Exec.Adj n` is
`List (List Bool)` (the type parameter `n` is phantom: it does not constrain
the list structure).  So the honest `n × n` bound additionally requires that
the adjacency really is an `n`-row matrix whose every row has length `n` --
the square, well-shaped representation the bitmask implementation maintains.

Note on the statement: the original ask used `(a.get? x).map List.length =
some n` for each `x < n`, but mathlib v4.34.0 has no `List.get?`.  The
membership form below `∀ r ∈ a, r.length = n` is provably equivalent for a
list of length `n` (each of the `n` rows has length `n`), and it is what the
square-matrix invariant actually checks.  We use it instead and document the
API substitution.
-/

/-- The executable `mcsOrder` of a square `n × n` adjacency produces an
ordering of length exactly `a.length = n`: after `n` foldl steps the chosen
prefix has length `n` (from `McsInvariant.foldl_mcsStep_len_core`), and
`reverse` preserves length.  This is the honest O(n)-space fact for the
ordering component of the state. -/
theorem mcsOrder_length (a : Adj n) (ha_len : a.length = n) :
    (Exec.mcsOrder a).length = a.length := by
  rw [Exec.mcsOrder]
  rw [List.length_reverse]
  have hr : List.range a.length = List.range n := congrArg List.range ha_len
  rw [hr]
  have h := McsInvariant.foldl_mcsStep_len_core a n (le_refl n)
  rw [h.1]
  exact ha_len.symm

/-- If every row of the `n`-row matrix `a` has length `n`, then the adjacency
occupies at most `n * n = n ^ 2` cells: the sum of the row lengths is exactly
`a.length * n = n * n`.  This is the honest O(n^2)-space fact for the matrix
component of the state. -/
theorem adj_space_bound (a : Adj n) (ha_len : a.length = n)
    (hrows : ∀ r ∈ a, r.length = n) :
    (a.map List.length).sum ≤ n * n := by
  have main : ∀ (b : List (List Bool)),
      (∀ r ∈ b, r.length = n) → (b.map List.length).sum = b.length * n := by
    intro b
    induction b with
    | nil =>
        simp
    | cons row rest ih =>
        intro hrows'
        have hrow : row.length = n := hrows' row (by simp)
        have hrest : (∀ r ∈ rest, r.length = n) := by
          intro r hr
          have hr' : r ∈ row :: rest := by simp [hr]
          exact hrows' r hr'
        have hrec : (rest.map List.length).sum = rest.length * n := ih hrest
        rw [List.map_cons, List.sum_cons, hrow, hrec]
        rw [List.length_cons]
        ring
  have hs := main a hrows
  rw [hs, ha_len]

end ComplexityHeadlines
end