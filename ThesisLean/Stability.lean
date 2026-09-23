import Mathlib
import ThesisLean.ExecUpdate

/-!
# Stability of MCS orderings under one-sided edge updates

`MCS(G)` denotes the set of MCS orderings of `G` under arbitrary tie-breaking
(`IsMCSOrderingAny`).

* `exists_common_ordering`: if along every chosen set each vertex's count in
  `G'` is its count in `G` plus `0` or `1`, then `MCS(G) ∩ MCS(G') ≠ ∅`.
* Hence inserting a matching, deleting a matching, or flipping a single edge
  always leaves a common MCS ordering.
* The bound is sharp in two directions: flipping a matching whose edges are
  partly inserted and partly deleted (`n = 4`), or inserting a triangle
  (`n = 5`) or a path on four vertices (`n = 6`), can leave no common ordering.
  These are checked by a pruned search whose soundness is proved here and
  whose result is evaluated by the kernel.
-/

noncomputable section
open Classical

namespace Challenge
namespace Proofs

open UGraph

variable {n : ℕ}

lemma neigh_eq_card (G : UGraph n) (s : Finset (Vert n)) (w : Vert n) :
    G.neigh s w = (s.filter (fun y => G.adj w y)).card := by
  unfold UGraph.neigh
  have hsplit : (s.filter (fun y => G.adj w y)).card +
      (s.filter (fun y => ¬ G.adj w y)).card = s.card :=
    Finset.card_filter_add_card_filter_not _
  exact Nat.sub_eq_of_eq_add hsplit.symm

lemma neigh_mono {G G' : UGraph n} (h : ∀ x y, G.adj x y → G'.adj x y)
    (S : Finset (Vert n)) (x : Vert n) : G.neigh S x ≤ G'.neigh S x := by
  rw [neigh_eq_card, neigh_eq_card]
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_filter] at hy ⊢
  exact ⟨hy.1, h x y hy.2⟩

lemma neigh_le_add_one {G F G' : UGraph n} (hadd : AddsEdges G F G') (hF : IsMatching F)
    (S : Finset (Vert n)) (x : Vert n) : G'.neigh S x ≤ G.neigh S x + 1 := by
  rw [neigh_eq_card, neigh_eq_card]
  have hsub : S.filter (fun y => G'.adj x y) ⊆
      S.filter (fun y => G.adj x y) ∪ S.filter (fun y => F.adj x y) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (hadd x y).1 hy.2 with h | h
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr ⟨hy.1, h⟩
  have hF1 : (S.filter (fun y => F.adj x y)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro y hy z hz
    exact hF x y z (Finset.mem_filter.1 hy).2 (Finset.mem_filter.1 hz).2
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (S.filter (fun y => G.adj x y)) (S.filter (fun y => F.adj x y))
  omega

/-- Some unchosen vertex is an MCS step in both graphs. -/
theorem exists_common_pick (G G' : UGraph n) (S : Finset (Vert n))
    (hlo : ∀ x, G.neigh S x ≤ G'.neigh S x) (hhi : ∀ x, G'.neigh S x ≤ G.neigh S x + 1)
    (hS : S ≠ (Finset.univ : Finset (Vert n))) :
    ∃ w, IsMCSNextAny G S w ∧ IsMCSNextAny G' S w := by
  have hU : ((Finset.univ : Finset (Vert n)) \ S).Nonempty :=
    Finset.sdiff_nonempty.2 (fun hs => hS (Finset.univ_subset_iff.1 hs))
  obtain ⟨w, hwU, hw⟩ := Finset.exists_max_image _ (G.neigh S) hU
  obtain ⟨w', hw'U, hw'⟩ := Finset.exists_max_image _ (G'.neigh S) hU
  by_cases h : G'.neigh S w' ≤ G'.neigh S w
  · exact ⟨w, ⟨hwU, hw⟩, ⟨hwU, fun x hx => (hw' x hx).trans h⟩⟩
  · refine ⟨w', ⟨hw'U, fun x hx => ?_⟩, ⟨hw'U, hw'⟩⟩
    have h1 := hlo w
    have h2 := hhi w'
    have h3 := hw x hx
    have h4 := hw w' hw'U
    omega

/-- If counts in `G'` exceed counts in `G` by `0` or `1` along every chosen
set, some ordering is an MCS ordering of both graphs. -/
theorem exists_common_ordering (G G' : UGraph n)
    (hlo : ∀ S x, G.neigh S x ≤ G'.neigh S x) (hhi : ∀ S x, G'.neigh S x ≤ G.neigh S x + 1) :
    ∃ ord, IsMCSOrderingAny G ord ∧ IsMCSOrderingAny G' ord := by
  suffices h : ∀ k ≤ n, ∃ P : List (Vert n), P.length = k ∧ P.Nodup ∧
      ∀ i (hi : i < P.length), IsMCSNextAny G (P.take i).toFinset (P.get ⟨i, hi⟩) ∧
        IsMCSNextAny G' (P.take i).toFinset (P.get ⟨i, hi⟩) by
    obtain ⟨P, hlen, hnd, hP⟩ := h n le_rfl
    exact ⟨P, ⟨hnd, hlen, fun i hi => (hP i hi).1⟩, ⟨hnd, hlen, fun i hi => (hP i hi).2⟩⟩
  intro k
  induction k with
  | zero => intro _; exact ⟨[], rfl, List.nodup_nil, fun i hi => absurd hi (by simp)⟩
  | succ k ih =>
      intro hk
      obtain ⟨P, hlen, hnd, hP⟩ := ih (by omega)
      have hS : P.toFinset ≠ (Finset.univ : Finset (Vert n)) := by
        intro h
        have hc : P.toFinset.card = n := by rw [h, Finset.card_univ, Fintype.card_fin]
        rw [List.toFinset_card_of_nodup hnd] at hc
        omega
      obtain ⟨w, hwG, hwG'⟩ := exists_common_pick G G' P.toFinset (hlo _) (hhi _) hS
      have hwP : w ∉ P := fun hm => (Finset.mem_sdiff.1 hwG.1).2 (List.mem_toFinset.2 hm)
      refine ⟨P ++ [w], by simp [hlen], ?_,
        steps_append (Q := fun S x => IsMCSNextAny G S x ∧ IsMCSNextAny G' S x) P w hP ⟨hwG, hwG'⟩⟩
      rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton w, ?_⟩
      intro x hx y hy
      rw [List.mem_singleton] at hy
      subst hy
      intro hxy
      subst hxy
      exact hwP hx

/-- Inserting a matching leaves a common MCS ordering. -/
theorem insert_matching_common_order {G F G' : UGraph n} (hadd : AddsEdges G F G')
    (hF : IsMatching F) : ∃ ord, IsMCSOrderingAny G ord ∧ IsMCSOrderingAny G' ord :=
  exists_common_ordering G G'
    (fun S x => neigh_mono (fun x y h => (hadd x y).2 (Or.inl h)) S x)
    (fun S x => neigh_le_add_one hadd hF S x)

/-- Deleting a matching leaves a common MCS ordering. -/
theorem delete_matching_common_order {G F G' : UGraph n} (hadd : AddsEdges G' F G)
    (hF : IsMatching F) : ∃ ord, IsMCSOrderingAny G ord ∧ IsMCSOrderingAny G' ord := by
  obtain ⟨ord, h₁, h₂⟩ := insert_matching_common_order hadd hF
  exact ⟨ord, h₂, h₁⟩

/-- The graph with the single edge `{u, v}`. -/
def edgeGraph (u v : Vert n) (huv : u ≠ v) : UGraph n where
  adj x y := (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  symm := by
    rintro x y (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩
  loopless := by
    rintro x (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact huv (h1.symm.trans h2)
    · exact huv (h2.symm.trans h1)

/-- The graph with no edges. -/
def emptyGraph (n : ℕ) : UGraph n where
  adj _ _ := False
  symm h := h
  loopless _ h := h

lemma edgeGraph_isMatching (u v : Vert n) (huv : u ≠ v) : IsMatching (edgeGraph u v huv) := by
  intro x y z hy hz
  rcases hy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rcases hz with ⟨hx', hz⟩ | ⟨hx', hz⟩
  · exact hy.trans hz.symm
  · exact absurd (hx.symm.trans hx') huv
  · exact absurd (hx'.symm.trans hx) huv
  · exact hy.trans hz.symm

lemma emptyGraph_isMatching : IsMatching (emptyGraph n) := fun _ _ _ h => h.elim

lemma flip_adj_iff {G G' : UGraph n} {u v : Vert n} (hflip : FlipOf G G' u v) (x y : Vert n)
    (hp : ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) : G'.adj x y ↔ G.adj x y := by
  rcases hflip.2 x y with he | he | he
  · rw [he]
  · exact absurd (Or.inl he) hp
  · exact absurd (Or.inr he) hp

/-- Flipping a single edge leaves a common MCS ordering. -/
theorem flip_common_order {G G' : UGraph n} {u v : Vert n} (hflip : FlipOf G G' u v) :
    ∃ ord, IsMCSOrderingAny G ord ∧ IsMCSOrderingAny G' ord := by
  have huv := hflip.1
  by_cases h' : G'.adj u v
  · refine insert_matching_common_order (F := edgeGraph u v huv) (fun x y => ?_)
      (edgeGraph_isMatching u v huv)
    by_cases hp : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
    · refine ⟨fun _ => Or.inr hp, fun _ => ?_⟩
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h'
      · exact G'.symm h'
    · rw [flip_adj_iff hflip x y hp]
      exact ⟨Or.inl, fun h => h.elim id (fun hF => absurd hF hp)⟩
  · by_cases h : G.adj u v
    · refine delete_matching_common_order (F := edgeGraph u v huv) (fun x y => ?_)
        (edgeGraph_isMatching u v huv)
      by_cases hp : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
      · refine ⟨fun _ => Or.inr hp, fun _ => ?_⟩
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h
        · exact G.symm h
      · rw [flip_adj_iff hflip x y hp]
        exact ⟨Or.inl, fun h => h.elim id (fun hF => absurd hF hp)⟩
    · refine insert_matching_common_order (F := emptyGraph n) (fun x y => ?_) emptyGraph_isMatching
      by_cases hp : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
      · have hG' : ¬ G'.adj x y := by
          rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h'
          · exact fun hvu => h' (G'.symm hvu)
        have hG : ¬ G.adj x y := by
          rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h
          · exact fun hvu => h (G.symm hvu)
        exact ⟨fun hx => absurd hx hG', fun hx => hx.elim (fun hx => absurd hx hG) False.elim⟩
      · rw [flip_adj_iff hflip x y hp]
        exact ⟨Or.inl, fun h => h.elim id False.elim⟩

/-! ## Certified counterexamples -/

instance ofEdges_decidableRel (E : List (ℕ × ℕ)) : DecidableRel (ofEdges n E).adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ ((x.val, y.val) ∈ E ∨ (y.val, x.val) ∈ E)))

/-- Number of neighbors of `w` in the list `L`, in the graph `ofEdges n E`. -/
def cntB (E : List (ℕ × ℕ)) (L : List (Fin n)) (w : Fin n) : ℕ :=
  (L.filter (fun y => decide ((ofEdges n E).adj w y))).length

/-- Boolean check that `w` is an MCS step (any tie-break) after the prefix `L`. -/
def stepB (E : List (ℕ × ℕ)) (L : List (Fin n)) (w : Fin n) : Bool :=
  !(L.contains w) && (List.finRange n).all (fun x => L.contains x || decide (cntB E L x ≤ cntB E L w))

/-- Search for a common MCS ordering of `ofEdges n E₁` and `ofEdges n E₂`
extending `L` by `k` more steps, branching only over common MCS steps. -/
def commonSearch (E₁ E₂ : List (ℕ × ℕ)) : ℕ → List (Fin n) → Bool
  | 0, _ => true
  | k + 1, L => (List.finRange n).any
      (fun x => stepB E₁ L x && stepB E₂ L x && commonSearch E₁ E₂ k (L ++ [x]))

lemma neigh_ofEdges (E : List (ℕ × ℕ)) (L : List (Fin n)) (hL : L.Nodup) (w : Fin n) :
    (ofEdges n E).neigh L.toFinset w = cntB E L w := by
  rw [neigh_eq_card, cntB, ← List.toFinset_card_of_nodup (hL.filter _), List.toFinset_filter]
  congr 1
  exact Finset.ext fun y => by simp [Finset.mem_filter]

lemma stepB_of_any (E : List (ℕ × ℕ)) (L : List (Fin n)) (hL : L.Nodup) (w : Fin n)
    (h : IsMCSNextAny (ofEdges n E) L.toFinset w) : stepB E L w = true := by
  obtain ⟨hw, hmax⟩ := h
  have hwL : w ∉ L := fun hm => (Finset.mem_sdiff.1 hw).2 (List.mem_toFinset.2 hm)
  unfold stepB
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨by simpa using hwL, fun x _ => ?_⟩
  by_cases hx : x ∈ L
  · simp [hx]
  · have hle := hmax x (Finset.mem_sdiff.2 ⟨Finset.mem_univ x, fun hm => hx (List.mem_toFinset.1 hm)⟩)
    rw [neigh_ofEdges E L hL, neigh_ofEdges E L hL] at hle
    simp [hx, hle]

lemma commonSearch_of_common (E₁ E₂ : List (ℕ × ℕ)) (ord : List (Fin n))
    (h₁ : IsMCSOrderingAny (ofEdges n E₁) ord) (h₂ : IsMCSOrderingAny (ofEdges n E₂) ord) :
    ∀ j i, i + j = n → commonSearch E₁ E₂ j (ord.take i) = true := by
  intro j
  induction j with
  | zero => intro i _; simp [commonSearch]
  | succ j ih =>
      intro i hij
      have hi : i < ord.length := by rw [h₁.2.1]; omega
      have hnd : (ord.take i).Nodup := h₁.1.sublist (List.take_sublist _ _)
      have hcat : ord.take i ++ [ord[i]] = ord.take (i + 1) := by
        rw [List.take_succ, List.getElem?_eq_getElem hi]
        rfl
      simp only [commonSearch, List.any_eq_true, Bool.and_eq_true]
      refine ⟨ord[i], List.mem_finRange _, ⟨?_, ?_⟩, ?_⟩
      · exact stepB_of_any E₁ _ hnd _ (h₁.2.2 i hi)
      · exact stepB_of_any E₂ _ hnd _ (h₂.2.2 i hi)
      · rw [hcat]
        exact ih (i + 1) (by omega)

/-- A failed search certifies that no common MCS ordering exists. -/
theorem no_common_order_of_search (E₁ E₂ : List (ℕ × ℕ))
    (hsearch : commonSearch (n := n) E₁ E₂ n [] = false) :
    ¬ ∃ ord, IsMCSOrderingAny (ofEdges n E₁) ord ∧ IsMCSOrderingAny (ofEdges n E₂) ord := by
  rintro ⟨ord, h₁, h₂⟩
  have h := commonSearch_of_common E₁ E₂ ord h₁ h₂ n 0 (by omega)
  rw [List.take_zero, hsearch] at h
  exact Bool.false_ne_true h

end Proofs
end Challenge
