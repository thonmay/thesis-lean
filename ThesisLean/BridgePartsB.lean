import Mathlib
import ThesisLean.Exec
import ThesisLean.McsInvariant
import ThesisLean.CardBridge
import ThesisLean.BridgePartsA
import ThesisLean.Formal_gen001c01_3939115c

open DynamicMCS

namespace ExecBridge

/-- The foldl state at step `j`: the executable MCS foldl over `range j`,
seeded with `([], range a.length)` (matching `Exec.mcsOrder`). -/
def stk (a : Adj n) (j : ℕ) : List ℕ × List ℕ :=
  (List.range j).foldl (fun s _ => Exec.mcsStep a s) ([], List.range a.length)

/-- The chosen-so-far list (in reverse pick order) at step `j`. -/
def chosen_k (a : Adj n) (j : ℕ) : List ℕ := (stk a j).1

/-- The remaining list at step `j`. -/
def rem_k (a : Adj n) (j : ℕ) : List ℕ := (stk a j).2

/-- The final MCS ordering, lifted to `Fin n` (semantically `ord.map ⟨·,·⟩`). -/
def ordFin (a : Adj n) (ha_len : a.length = n) : List (Fin n) :=
  CardBridge.chosenFin n (Exec.mcsOrder a) (mcsOrder_mem_lt a ha_len)

/-- Every picked vertex is `< n` at step `j` (from the foldl invariant). -/
lemma chosen_k_lt (a : Adj n) (ha_len : a.length = n) (j : ℕ) (hj : j ≤ a.length) :
    ∀ v ∈ chosen_k a j, v < n := by
  unfold chosen_k stk
  exact (McsInvariant.foldl_mcsStep_listInv a ha_len j hj).2.2.1

/-- Length bookkeeping at step `j`: chosen has `j` entries, remaining has
`a.length - j`. -/
lemma stk_len (a : Adj n) (ha_len : a.length = n) (j : ℕ) (hj : j ≤ a.length) :
    (stk a j).1.length = j ∧ (stk a j).2.length = a.length - j := by
  unfold stk
  have hr : List.range a.length = List.range n := congrArg List.range ha_len
  have hcore := McsInvariant.foldl_mcsStep_len_core a j (by omega)
  simpa [hr, ha_len] using hcore

/-- If `j < a.length`, the remaining list is nonempty. -/
lemma rem_k_ne_of_lt (a : Adj n) (ha_len : a.length = n) {j : ℕ} (hj : j < a.length) :
    rem_k a j ≠ [] := by
  intro he
  have hlen : (rem_k a j).length = a.length - j := by
    simpa [rem_k] using (stk_len a ha_len j (le_of_lt hj)).2
  rw [he] at hlen
  simp at hlen
  omega

/-- One more foldl step unfolds to exactly one `mcsStep` application. -/
lemma stk_succ (a : Adj n) (j : ℕ) : stk a (j + 1) = Exec.mcsStep a (stk a j) := by
  unfold stk
  rw [List.range_succ, List.foldl_append]
  simp

/-- After `j < a.length` steps, the chosen list is a new pick prepended. -/
lemma stk_succ_chosen (a : Adj n) (ha_len : a.length = n) {j : ℕ} (hj : j < a.length) :
    (stk a (j + 1)).1 = Exec.bestPick a (stk a j).1 (stk a j).2 :: (stk a j).1 := by
  rw [stk_succ]
  change (Exec.mcsStep a ((stk a j).1, (stk a j).2)).1 =
    Exec.bestPick a (stk a j).1 (stk a j).2 :: (stk a j).1
  rw [McsInvariant.mcsStep_eq a (stk a j).1 (stk a j).2 (rem_k_ne_of_lt a ha_len hj)]

/-- Core bookkeeping: dropping `m` from the full chosen list at step `k + m`
recovers the chosen list at step `k`. Later picks prepend, so the first `m`
entries of `(stk a (k+m)).1` are exactly the `m` new picks. -/
lemma stk1_drop_m (a : Adj n) (ha_len : a.length = n) (k m : ℕ)
    (hm : k + m ≤ a.length) :
    (stk a (k + m)).1.drop m = (stk a k).1 := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hkle : k + m ≤ a.length := by omega
      have ih' := ih hkle
      have hEqIndex : k + (m + 1) = (k + m) + 1 := by omega
      have hj_lt : k + m < a.length := by omega
      rw [hEqIndex, stk_succ_chosen a ha_len hj_lt]
      rw [List.drop_succ_cons]
      exact ih'

/-- The terminal chosen list, projected by `drop (a.length - k)`, is the chosen
list at step `k`. -/
lemma stk1_drop (a : Adj n) (ha_len : a.length = n) (k : ℕ) (hk : k ≤ a.length) :
    (stk a a.length).1.drop (a.length - k) = (stk a k).1 := by
  have hm : k + (a.length - k) = a.length := Nat.add_sub_of_le hk
  rw [← hm]
  rw [Nat.add_sub_cancel_left]
  exact stk1_drop_m a ha_len k (a.length - k) (by omega)

/-- `Exec.mcsOrder a = (stk a a.length).1.reverse` (the terminal foldl state,
expressed with `stk`). -/
lemma mcsOrder_eq_stk_reverse (a : Adj n) :
    Exec.mcsOrder a = (stk a a.length).1.reverse := by
  simpa [stk] using (mcsOrder_eq_reverse a)

/-- The first `k` elements of the final ordering equal the chosen-so-far at
step `k`, reversed. -/
lemma mcsOrder_take_eq_chosen_reverse (a : Adj n) (ha_len : a.length = n) (k : ℕ)
    (hk : k ≤ a.length) :
    (Exec.mcsOrder a).take k = (chosen_k a k).reverse := by
  rw [mcsOrder_eq_stk_reverse a]
  unfold chosen_k
  rw [List.take_reverse]
  have hlen : (stk a a.length).1.length = a.length :=
    (stk_len a ha_len a.length (le_refl a.length)).1
  rw [hlen]
  exact congrArg List.reverse (stk1_drop a ha_len k hk)

/-- `take k` commutes with `chosenFin` on membership: `x` lies in the first
`k` lifted elements of `l` iff its value lies in the first `k` of `l`. -/
lemma mem_chosenFin_take (l : List ℕ) (hlt : ∀ v ∈ l, v < n) (k : ℕ) (x : Fin n) :
    x ∈ (CardBridge.chosenFin n l hlt).take k ↔ x.val ∈ l.take k := by
  unfold CardBridge.chosenFin
  induction l generalizing k with
  | nil => simp
  | cons v vs ih =>
      have hlt_vs : ∀ w ∈ vs, w < n := fun w hw => hlt w (by simp [hw])
      rw [List.pmap_cons]
      cases k with
      | zero => simp
      | succ k' =>
          rw [List.take_succ_cons, List.take_succ_cons]
          simp only [List.mem_cons]
          constructor
          · rintro (hxv | hrest)
            · left
              exact congrArg Fin.val hxv
            · right
              exact (ih hlt_vs k').mp hrest
          · rintro (hxv | hrest)
            · left
              apply Fin.ext
              exact hxv
            · right
              exact (ih hlt_vs k').mpr hrest

/-- Membership in the ordering prefix (as `Fin`) equals membership in the
chosen-so-far value set. -/
lemma mem_ordFin_take (a : Adj n) (ha_len : a.length = n) (k : ℕ) (hk : k ≤ a.length)
    (x : Fin n) :
    x ∈ (ordFin a ha_len).take k ↔ x.val ∈ chosen_k a k := by
  unfold ordFin
  rw [mem_chosenFin_take]
  rw [mcsOrder_take_eq_chosen_reverse a ha_len k hk]
  rw [List.mem_reverse]

/-- The bridge's key bookkeeping stated as prefix-Finset equality. -/
lemma ord_take_finset_eq_chosenFin (a : Adj n) (ha_len : a.length = n) (k : ℕ)
    (hk : k ≤ a.length) :
    ((ordFin a ha_len).take k).toFinset =
      (CardBridge.chosenFin n (chosen_k a k) (chosen_k_lt a ha_len k hk)).toFinset := by
  classical
  apply Finset.ext
  intro x
  rw [List.mem_toFinset]
  exact (Iff.trans (mem_ordFin_take a ha_len k hk x)
    (McsInvariant.mem_chosenFin_iff (chosen_k_lt a ha_len k hk) x).symm)

end ExecBridge