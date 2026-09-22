import Mathlib
import ThesisLean.Formal_gen001c01_3939115c
import ThesisLean.Formal_gen003c01_eea71821

open DynamicMCS
open DynamicMCS.UGraph
open DynamicMCS.Eea71821

/-!
# Probe-cost bounds for the dynamic MCS update

The dynamic MCS candidate scans the current ordering with a *probe* to locate
the first step at which the old greedy choice is no longer a legal MCS pick on
the post-update graph.  In the formal model this scan is `firstBreakAux` /
`firstBreak`, and the actual regreedy uses `firstBreakWindow` (insertion) or a
single probe at `laterPos` (deletion).  This module formalizes the *probe
cost*: the number of ordering positions the candidate examines before it stops.

We measure the probe cost as the recursion depth of `firstBreakAux`, i.e. the
number of list elements consumed before the scan halts.  Exactly like the
scan it models, `probeCost` stops as soon as it finds an illegal step:

$$ \mathrm{probeCost}(k, []) = 0, \qquad
   \mathrm{probeCost}(k, x \mathop{::} xs) =
   \begin{cases}
     1 + \mathrm{probeCost}(k+1, xs) & \text{if } x \text{ is legal at } k,\\
     1 & \text{otherwise.}
   \end{cases} $$

The headline bounds follow:

1. `probeCost_le_length`: any scan examines at most as many positions as the
   list it walks, so
2. `firstBreak_cost_bound`: the unbounded scan from `k0` is `O(order.drop k0)`;
3. `insert_probe_cost_bound`: when the insertion window `[earlierPos+1,
   laterPos]` actually fires a break, the scan stops inside the window, so its
   cost is `O(laterPos - earlierPos)` — the window length;
4. `delete_probe_cost_bound`: the deletion probe scans the suffix from
   `laterPos`, `O(order.length)`;
5. `probeCost_le_n`: both updated bounds are at most `order.length`.

The precise ``firstBreak_window`` (the windowed probe used by `insertUpdate`)
is ``firstBreakWindow`` in `Formal_gen003c01`.  The insertion bound is
literally a bound on the cost that `insertUpdate`'s regreedy incurs: when
`insertUpdate` regreedies it has found a break inside the window, and that is
exactly the case covered by theorem 3.
-/

noncomputable section
open Classical

namespace ProbeCost

variable {n : ℕ}

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

/-- Lemma 1: scanning a list examines at most as many positions as the list
has elements.  Structural induction on the scanned list. -/
lemma probeCost_le_length (H : UGraph n) (order : List (Vert n)) :
    ∀ (k : ℕ) (xs : List (Vert n)),
      probeCost H order k xs ≤ xs.length := by
  intro k xs
  induction xs generalizing k with
  | nil =>
      simp [probeCost]
  | cons x xs ih =>
      by_cases hx : IsMCSNext H (order.take k).toFinset x
      · -- x legal: one step into the tail
        rw [probeCost]
        rw [if_pos hx]
        have hrec : probeCost H order (k + 1) xs ≤ xs.length := ih (k + 1)
        simp
        omega
      · -- x illegal: the probe stops right there, examining 1 position
        rw [probeCost]
        rw [if_neg hx]
        simp

/-- Corollary (Lemma 2): the unbounded scan from `k0` over `order.drop k0`
costs at most `(order.drop k0).length`. -/
theorem firstBreak_cost_bound (H : UGraph n) (order : List (Vert n)) (k0 : ℕ) :
    probeCost H order k0 (order.drop k0) ≤ (order.drop k0).length := by
  exact probeCost_le_length H order k0 (order.drop k0)

/-- If the unbounded scan from `k0` stops at `k`, then the probe cost is
exactly the number of positions `k0, …, k`, i.e. `k - k0 + 1`.  The
`+ 1` counts the broken position `k` itself. -/
lemma probeCost_eq_of_firstBreakAux_some {H : UGraph n} {order : List (Vert n)} :
    ∀ (k j : ℕ) (xs : List (Vert n)),
      firstBreakAux H order k xs = some j → probeCost H order k xs = j - k + 1 := by
  intro k j xs
  induction xs generalizing k j with
  | nil =>
      intro h
      simp [firstBreakAux] at h
  | cons x xs ih =>
      intro h
      by_cases hx : IsMCSNext H (order.take k).toFinset x
      · -- x legal: the break (if any) sits inside xs, so positions shift by one
        have heq : firstBreakAux H order k (x :: xs) = firstBreakAux H order (k + 1) xs := by
          simp [firstBreakAux, hx]
        have hh : firstBreakAux H order (k + 1) xs = some j := by simpa [heq] using h
        have hge : k + 1 ≤ j := firstBreakAux_some_ge H order (k + 1) j xs hh
        have hrec : probeCost H order (k + 1) xs = j - (k + 1) + 1 :=
          ih (k + 1) j hh
        rw [probeCost]
        rw [if_pos hx]
        rw [hrec]
        omega
      · -- x illegal: the scan stops immediately at k, so j = k
        have hsk : some k = some j := by simpa [firstBreakAux, hx] using h
        have hj : j = k := (Option.some.inj hsk).symm
        rw [probeCost]
        rw [if_neg hx]
        rw [hj]
        simp

/-- The unbounded scan (`firstBreak`) finds a break at `k` iff the auxiliary
scan does; the probe cost is then the window distance `k - k0 + 1`. -/
lemma probeCost_eq_of_firstBreak_some (H : UGraph n) (order : List (Vert n))
    (k0 k : ℕ) (h : firstBreak H order k0 = some k) :
    probeCost H order k0 (order.drop k0) = k - k0 + 1 := by
  unfold firstBreak at h
  exact probeCost_eq_of_firstBreakAux_some k0 k (order.drop k0) h

/-- The windowed scan reports `some k` only when the unbounded scan stops at
`k` and `k` lies inside the window. -/
lemma firstBreakWindow_some_imp (H : UGraph n) (order : List (Vert n))
    (k0 k1 k : ℕ) (h : firstBreakWindow H order k0 k1 = some k) :
    firstBreak H order k0 = some k ∧ k ≤ k1 := by
  classical
  unfold firstBreakWindow at h
  have hnotnone : firstBreak H order k0 ≠ none := by
    intro hn
    rw [hn] at h
    simp at h
  obtain ⟨j, hj'⟩ := Option.ne_none_iff_exists.mp hnotnone
  have hj : firstBreak H order k0 = some j := hj'.symm
  rw [hj] at h
  simp at h
  by_cases hk1 : j ≤ k1
  · have hjk : j = k := h.2
    exact ⟨by simpa [hjk, hj], by simpa [hjk] using hk1⟩
  · exfalso
    exact hk1 h.1

/-- Theorem 3 (the insertion probe is `O(window)`): when the insertion window
probe `[earlierPos u v + 1, laterPos u v]` fires a break, the cost of the scan
from `earlierPos u v + 1` is at most the window length
`laterPos u v - earlierPos u v`.  This is precisely the case in which
`insertUpdate` regreedies from the discovered break. -/
theorem insert_probe_cost_bound (H : UGraph n) (order : List (Vert n)) (u v : Vert n)
    {k : ℕ}
    (hk : firstBreakWindow H order (earlierPos order u v + 1) (laterPos order u v) = some k) :
    probeCost H order (earlierPos order u v + 1) (order.drop (earlierPos order u v + 1)) ≤
      laterPos order u v - earlierPos order u v := by
  classical
  let k0 : ℕ := earlierPos order u v + 1
  have hwin := firstBreakWindow_some_imp H order k0 (laterPos order u v) k (by
    unfold k0
    exact hk)
  rcases hwin with ⟨hfb, hkle⟩
  have hcost : probeCost H order k0 (order.drop k0) = k - k0 + 1 :=
    probeCost_eq_of_firstBreak_some H order k0 k hfb
  -- the discovered break is at or after the window's start
  have hk0lb : k0 ≤ k := by
    unfold firstBreak at hfb
    exact firstBreakAux_some_ge H order k0 k (order.drop k0) hfb
  rw [hcost]
  -- k0 = earlierPos + 1, so k - k0 + 1 = k - earlierPos
  rw [show k - k0 + 1 = k - earlierPos order u v by
    unfold k0
    omega]
  have hkG : earlierPos order u v ≤ k := by omega
  omega

/-- Theorem 5: both the insertion (`earlierPos + 1`, `≤ laterPos`) and the
deletion (`laterPos`) probes scan at most `order.length` positions. -/
theorem probeCost_le_n (H : UGraph n) (order : List (Vert n)) (k0 : ℕ) :
    probeCost H order k0 (order.drop k0) ≤ order.length := by
  have h1 := probeCost_le_length H order k0 (order.drop k0)
  have hdrop : (order.drop k0).length ≤ order.length := by
    rw [List.length_drop]
    omega
  exact le_trans h1 hdrop

/-- Theorem 4 (the deletion probe is `O(order.length)`): the deletion probe
scans the suffix from `laterPos` (a single probe cost bounded by the whole
suffix length, hence by the whole order length). -/
theorem delete_probe_cost_bound (H : UGraph n) (order : List (Vert n)) (u v : Vert n)
    (_hmem_u : u ∈ order) :
    probeCost H order (laterPos order u v) (order.drop (laterPos order u v)) ≤ order.length :=
  probeCost_le_n H order (laterPos order u v)

end ProbeCost
end