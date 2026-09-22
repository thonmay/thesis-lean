import Mathlib
import ThesisLean.Formal_gen001c01_3939115c

/-!
# CountBridge

Complexity-theorem bookkeeping for a dynamic MCS (maximum cardinality search)
algorithm. We count *undirected* edges of the abstract `DynamicMCS.UGraph`
(each edge `{u, v}` counted once) and edges incident to a vertex subset `S`,
and derive the standard complexity bounds:

* `edgeCount` is well-defined: the number of *directed* adjacency pairs
  `(u, v)` with `adj u v` is even, because the swap involution `(u, v) ↦ (v, u)`
  pairs each such pair with its reverse without fixed points (loopless).
  Dividing by two therefore yields the undirected edge count exactly.
* `mSuffix` (edges touching `S`) is likewise even.
* `mSuffix ≤ edgeCount` because the `S`-incident filter is a subset of the
  adjacency filter.
* both counts are bounded by `n * (n - 1) / 2`, the maximum number of undirected
  edges on `n` vertices.

Counts are taken on the finset of directed pairs `Vert n × Vert n` and divided by
two; the evenness lemmas justify that the division is exact.

`UGraph.adj` is an unclassified `Prop`, so the filters that select adjacency pairs
are not automatically decidable. In line with the neighboring `Formal_gen...` file
(which uses `by classical` inside its `def neigh`), the pair-counting finsets below
are `noncomputable def`s built under `classical`; the theorems are stated about
those finsets.
-/

open DynamicMCS

namespace CountBridge

variable {n : ℕ}

/-- All ordered adjacency pairs `(u, v)` of `G`, i.e. the directed edges. -/
noncomputable def adjPairs (G : DynamicMCS.UGraph n) : Finset (Vert n × Vert n) := by
  classical
  exact (Finset.univ : Finset (Vert n × Vert n)).filter
    (fun uv : Vert n × Vert n => G.adj uv.1 uv.2)

/-- Number of undirected edges in `G`, i.e. the directed adjacency-pair count
divided by two. Exact because the count is even (`adjPairs_even`). -/
noncomputable def edgeCount (G : DynamicMCS.UGraph n) : ℕ :=
  (adjPairs G).card / 2

/-! ### Evenness of a swap-invariant finset of pairs

A finset `E ⊆ α × α` that is closed under swapping the two components and
contains no pair `(x, x)` has even cardinality: the swaps `(x, y) ⟷ (y, x)` pair
up its elements. We split `E` by the order of the two components into a
"smaller-first" half `L` and its swap image `U`; these are disjoint, their union
is `E`, and swap bijects `L` onto `U`. -/

/-- If `E ⊆ α × α` is swap-closed and has no diagonal element, then its
cardinality is even. Requires only a linear order on the component type `α`
(not on the product), used to separate each 2-cycle. -/
lemma even_card_pairs {α : Type*} [LinearOrder α] (E : Finset (α × α))
    (hσ : ∀ x, x ∈ E → Prod.swap x ∈ E)
    (hloop : ∀ x, x ∈ E → x.1 ≠ x.2) : 2 ∣ E.card := by
  classical
  let L : Finset (α × α) := E.filter (fun x => x.1 < x.2)
  let U : Finset (α × α) := E.filter (fun x => x.2 < x.1)
  have hsplit : E = L ∪ U := by
    ext x
    constructor
    · intro hx
      rcases lt_or_gt_of_ne (hloop x hx) with hlt | hgt
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx, hlt⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, hgt⟩))
    · intro hx
      rcases Finset.mem_union.mp hx with hL | hU
      · exact (Finset.mem_filter.mp hL).1
      · exact (Finset.mem_filter.mp hU).1
  have hdisj : Disjoint L U := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      have hL : x.1 < x.2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2
      have hU : x.2 < x.1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
      exact False.elim (lt_asymm hL hU)
    · intro hx
      exact False.elim ((by simp : x ∉ (∅ : Finset (α × α))) hx)
  have hcard : L.card = U.card := by
    let σe : (α × α) ≃ (α × α) := ⟨Prod.swap, Prod.swap,
      by intro x; rfl, by intro x; rfl⟩
    exact Finset.card_equiv σe (by
      intro x
      constructor
      · intro hxL
        have hmemE : x ∈ E := (Finset.mem_filter.mp hxL).1
        have hlt : x.1 < x.2 := (Finset.mem_filter.mp hxL).2
        have hswapE : Prod.swap x ∈ E := hσ x hmemE
        have hswap : (Prod.swap x).2 < (Prod.swap x).1 := by
          simpa using hlt
        exact Finset.mem_filter.mpr ⟨hswapE, hswap⟩
      · intro hxU
        have hmemU := Finset.mem_filter.mp hxU
        have hswapE : Prod.swap x ∈ E := by
          simpa [σe] using hmemU.1
        have hxE : x ∈ E := by
          simpa [σe] using hσ (Prod.swap x) hswapE
        have hlt : x.1 < x.2 := by
          simpa [σe] using hmemU.2
        exact Finset.mem_filter.mpr ⟨hxE, hlt⟩)
  refine ⟨L.card, ?_⟩
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hcard]
  rw [two_mul]

/-- The number of directed adjacency pairs is even (swap pairs them, loopless
removes fixed points). -/
lemma adjPairs_even (G : DynamicMCS.UGraph n) : 2 ∣ (adjPairs G).card := by
  classical
  dsimp [adjPairs]
  exact even_card_pairs
    ((Finset.univ : Finset (Vert n × Vert n)).filter
      (fun uv : Vert n × Vert n => G.adj uv.1 uv.2))
    (by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        G.symm (Finset.mem_filter.mp hx).2⟩)
    (by
      intro x hx
      intro heq
      exact G.loopless x.2 (by simpa [heq] using (Finset.mem_filter.mp hx).2))

/-! ### Edges incident to a vertex set `S`. -/

/-- All ordered adjacency pairs touching `S`, i.e. with at least one endpoint in
`S`. -/
noncomputable def mSuffixPairs (G : DynamicMCS.UGraph n) (S : Finset (Vert n)) :
    Finset (Vert n × Vert n) := by
  classical
  exact (Finset.univ : Finset (Vert n × Vert n)).filter
    (fun uv : Vert n × Vert n => G.adj uv.1 uv.2 ∧ (uv.1 ∈ S ∨ uv.2 ∈ S))

/-- Number of undirected edges of `G` with at least one endpoint in `S`. Exact
because the count is even (`mSuffixPairs_even`). -/
noncomputable def mSuffix (G : DynamicMCS.UGraph n) (S : Finset (Vert n)) : ℕ :=
  (mSuffixPairs G S).card / 2

/-- The `S`-incident directed-pair count is even. The membership condition
`u ∈ S ∨ v ∈ S` is symmetric under swap, and looplessness removes fixed points. -/
lemma mSuffixPairs_even (G : DynamicMCS.UGraph n) (S : Finset (Vert n)) :
    2 ∣ (mSuffixPairs G S).card := by
  classical
  dsimp [mSuffixPairs]
  exact even_card_pairs
    ((Finset.univ : Finset (Vert n × Vert n)).filter
      (fun uv : Vert n × Vert n => G.adj uv.1 uv.2 ∧ (uv.1 ∈ S ∨ uv.2 ∈ S)))
    (by
      intro x hx
      have hmem := Finset.mem_filter.mp hx
      rcases hmem.2.2 with h1 | h2
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨G.symm hmem.2.1, Or.inr h1⟩⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨G.symm hmem.2.1, Or.inl h2⟩⟩)
    (by
      intro x hx
      intro heq
      exact G.loopless x.2 (by simpa [heq] using (Finset.mem_filter.mp hx).2.1))

/-! ### Monotonicity and the maximum-edge bound. -/

/-- The `S`-incident adjacency pairs are among all adjacency pairs, so their
count is at most it, preserved by dividing by two. -/
lemma mSuffix_le_edgeCount (G : DynamicMCS.UGraph n) (S : Finset (Vert n)) :
    mSuffix G S ≤ edgeCount G := by
  unfold mSuffix edgeCount
  apply Nat.div_le_div_right
  classical
  dsimp [mSuffixPairs, adjPairs]
  apply Finset.card_le_card
  intro uv huv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp huv).2.1⟩

/-! The maximum number of undirected edges on `n` vertices is `n choose 2 =
n * (n - 1) / 2`. The adjacency pairs all lie in the off-diagonal
`{(u, v) | u ≠ v}`, whose cardinality is `n * (n - 1)`. -/

/-- The adjacency-pair count is at most the off-diagonal pair count `n * (n-1)`,
hence the undirected edge count is at most `n * (n - 1) / 2`. -/
lemma edgeCount_le_choose2 (G : DynamicMCS.UGraph n) :
    edgeCount G ≤ n * (n - 1) / 2 := by
  classical
  dsimp [edgeCount, adjPairs]
  have hsub :
      ((Finset.univ : Finset (Vert n × Vert n)).filter
        (fun uv : Vert n × Vert n => G.adj uv.1 uv.2))
      ⊆ (Finset.offDiag (Finset.univ : Finset (Vert n))) := by
    intro x hx
    have hadj : G.adj x.1 x.2 := (Finset.mem_filter.mp hx).2
    have hn : x.1 ≠ x.2 := by
      intro heq
      exact G.loopless x.2 (by simpa [heq] using hadj)
    exact Finset.mem_offDiag.mpr ⟨Finset.mem_univ x.1, Finset.mem_univ x.2, hn⟩
  have hdiv : ((Finset.univ : Finset (Vert n × Vert n)).filter
        (fun uv : Vert n × Vert n => G.adj uv.1 uv.2)).card / 2
      ≤ (Finset.offDiag (Finset.univ : Finset (Vert n))).card / 2 :=
    Nat.div_le_div_right (Finset.card_le_card hsub)
  have hoff :
      (Finset.offDiag (Finset.univ : Finset (Vert n))).card = n * (n - 1) := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    rw [Nat.mul_sub_left_distrib, mul_one]
  simpa [hoff] using hdiv

/-- Corollary: edges incident to `S` are at most the `n`-vertex maximum. -/
lemma mSuffix_le_choose2 (G : DynamicMCS.UGraph n) (S : Finset (Vert n)) :
    mSuffix G S ≤ n * (n - 1) / 2 :=
  le_trans (mSuffix_le_edgeCount G S) (edgeCount_le_choose2 G)

end CountBridge