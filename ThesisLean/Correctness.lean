module

public import Mathlib
public import ThesisLean.SolutionBridge

set_option backward.proofsInPublic true
@[expose] public section

/-!
# Correctness and locality of the dynamic updates (on the `Challenge` definitions)

* correctness of `initOrder`, `insertUpdate`, `deleteUpdate`, `greedySuffix`;
* uniqueness of the canonical MCS ordering, hence: each update returns exactly
  the from-scratch canonical ordering of the new graph;
* locality: after a flip of `{u, v}`, positions up to `earlierPos` and after
  `laterPos` stay legal; after a deletion, positions strictly between the
  endpoints stay legal too, so only `laterPos` can break;
* null updates: the ordering is returned unchanged exactly when it is still
  the canonical ordering of the new graph.
-/

noncomputable section
open Classical

namespace Challenge
namespace Proofs

open UGraph Transport

variable {n : ℕ} {G G' : UGraph n}

/-! ## Uniqueness of the canonical ordering -/

theorem IsMCSNext_unique {S : Finset (Vert n)} {w w' : Vert n}
    (h : IsMCSNext G S w) (h' : IsMCSNext G S w') : w = w' := by
  have heq : G.neigh S w' = G.neigh S w := le_antisymm (h.2.1 w' h'.1) (h'.2.1 w h.1)
  exact le_antisymm (h.2.2 w' h'.1 heq) (h'.2.2 w h.1 heq.symm)

theorem IsMCSOrdering_unique {o₁ o₂ : List (Vert n)}
    (h₁ : IsMCSOrdering G o₁) (h₂ : IsMCSOrdering G o₂) : o₁ = o₂ := by
  have key : ∀ i, o₁.take i = o₂.take i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        rw [List.take_succ, List.take_succ, ih]
        congr 1
        by_cases hi : i < n
        · have hi₁ : i < o₁.length := by rw [h₁.2.1]; exact hi
          have hi₂ : i < o₂.length := by rw [h₂.2.1]; exact hi
          have s₁ := h₁.2.2 i hi₁
          have s₂ := h₂.2.2 i hi₂
          rw [ih] at s₁
          have hsame := IsMCSNext_unique s₁ s₂
          simp only [List.get_eq_getElem] at hsame
          rw [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂, hsame]
        · rw [List.getElem?_eq_none (by rw [h₁.2.1]; omega),
            List.getElem?_eq_none (by rw [h₂.2.1]; omega)]
  have := key n
  rwa [List.take_of_length_le (le_of_eq h₁.2.1),
    List.take_of_length_le (le_of_eq h₂.2.1)] at this

theorem IsMCSNext.toAny {S : Finset (Vert n)} {w : Vert n} (h : IsMCSNext G S w) :
    IsMCSNextAny G S w :=
  ⟨h.1, h.2.1⟩

theorem IsMCSOrdering.toAny {order : List (Vert n)} (h : IsMCSOrdering G order) :
    IsMCSOrderingAny G order :=
  ⟨h.1, h.2.1, fun i hi => IsMCSNext.toAny (h.2.2 i hi)⟩

/-! ## Correctness -/

theorem init_valid (G : UGraph n) : IsMCSOrdering G (initOrder G) := by
  rw [initOrder, Transport.greedySuffix_eq, IsMCSOrdering_toDyn]
  exact DynamicMCS.UGraph.init_valid (Transport.toDyn G)

theorem order_toFinset_univ {order : List (Vert n)} (h : IsMCSOrdering G order) :
    order.toFinset = (Finset.univ : Finset (Vert n)) :=
  DynamicMCS.Eea71821.order_toFinset_univ order ((IsMCSOrdering_toDyn G order).1 h)

theorem greedySuffix_full (H : UGraph n) (order : List (Vert n))
    (h : order.toFinset = (Finset.univ : Finset (Vert n))) :
    greedySuffix H order = order := by
  rw [Transport.greedySuffix_eq]
  exact DynamicMCS.Eea71821.greedySuffix_full (Transport.toDyn H) order h

theorem update_from_prefix (order : List (Vert n)) (k : ℕ)
    (hvalid : IsMCSOrdering G order)
    (hsteps : ∀ i (hi : i < order.length), i < k →
      IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩)) :
    IsMCSOrdering G' (greedySuffix G' (order.take k)) := by
  rw [Transport.greedySuffix_eq, IsMCSOrdering_toDyn]
  exact DynamicMCS.Eea71821.update_from_prefix (G := Transport.toDyn G) order k
    ((IsMCSOrdering_toDyn G order).1 hvalid)
    (fun i hi hlt => (IsMCSNext_toDyn G' _ _).1 (hsteps i hi hlt))

lemma insertUpdate_eq_dyn (H : UGraph n) (order : List (Vert n)) (u v : Vert n) :
    insertUpdate H order u v = DynamicMCS.Eea71821.insertUpdate (Transport.toDyn H) order u v := by
  unfold insertUpdate DynamicMCS.Eea71821.insertUpdate
  rw [earlierPos_eq, laterPos_eq, firstBreakWindow_eq, greedySuffix_eq]

lemma deleteUpdate_eq_dyn (H : UGraph n) (order : List (Vert n)) (u v : Vert n) :
    deleteUpdate H order u v = DynamicMCS.Eea71821.deleteUpdate (Transport.toDyn H) order u v := by
  unfold deleteUpdate DynamicMCS.Eea71821.deleteUpdate
  rw [deletionBreaks_eq, laterPos_eq, greedySuffix_eq]

/-- The insertion update is correct for every flip of `{u, v}` (the proof does
not need the edge to be absent before). -/
theorem insert_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (insertUpdate G' order u v) := by
  rw [insertUpdate_eq_dyn, IsMCSOrdering_toDyn]
  exact DynamicMCS.Eea71821.insert_update_valid u v order
    ((FlipOf_toDyn G G' u v).1 hflip) ((IsMCSOrdering_toDyn G order).1 hvalid)

theorem delete_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (deleteUpdate G' order u v) := by
  rw [deleteUpdate_eq_dyn, IsMCSOrdering_toDyn]
  exact DynamicMCS.Eea71821.delete_update_valid (G := Transport.toDyn G) u v order
    ((FlipOf_toDyn G G' u v).1 hflip) hdel hdel' ((IsMCSOrdering_toDyn G order).1 hvalid)

/-! ## Each update returns exactly the from-scratch canonical ordering -/

theorem insert_update_eq_initOrder (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    insertUpdate G' order u v = initOrder G' :=
  IsMCSOrdering_unique (insert_update_valid u v order hflip hvalid) (init_valid G')

theorem delete_update_eq_initOrder (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    deleteUpdate G' order u v = initOrder G' :=
  IsMCSOrdering_unique (delete_update_valid u v order hflip hdel hdel' hvalid) (init_valid G')

/-! ## Locality -/

/-- Positions up to the earlier endpoint stay legal after any flip. -/
theorem legal_upto_earlierPos (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi : i < order.length) (hle : i ≤ earlierPos order u v) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) :=
  (IsMCSNext_toDyn G' _ _).2 (DynamicMCS.UGraph.prefix_preserved order u v
    ((FlipOf_toDyn G G' u v).1 hflip) ((IsMCSOrdering_toDyn G order).1 hvalid) i
    (by rwa [earlierPos_eq] at hle) hi)

/-- Positions after the later endpoint stay legal after any flip. -/
theorem legal_after_laterPos (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi : i < order.length) (hgt : laterPos order u v < i) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) :=
  (IsMCSNext_toDyn G' _ _).2 (DynamicMCS.Eea71821.legal_after_laterPos order u v
    ((FlipOf_toDyn G G' u v).1 hflip) ((IsMCSOrdering_toDyn G order).1 hvalid) i hi
    (by rwa [laterPos_eq] at hgt))

/-- After a deletion, positions strictly between the endpoints stay legal. -/
theorem delete_legal_between (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi : i < order.length)
    (hgt : earlierPos order u v < i) (hlt : i < laterPos order u v) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) :=
  (IsMCSNext_toDyn G' _ _).2 (DynamicMCS.Eea71821.legal_middle_delete (G := Transport.toDyn G)
    order u v ((FlipOf_toDyn G G' u v).1 hflip) hdel hdel'
    ((IsMCSOrdering_toDyn G order).1 hvalid) i hi
    (by rwa [earlierPos_eq] at hgt) (by rwa [laterPos_eq] at hlt))

/-- Inside the insertion window, the old choice breaks exactly when the later
endpoint now beats it: strictly larger cardinality, or equal cardinality and a
smaller index. -/
theorem insert_break_iff (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hins : ¬ G.adj u v) (hins' : G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (k : ℕ) (hk : k < order.length)
    (hgt : earlierPos order u v < k) (hle : k ≤ laterPos order u v) :
    ¬ IsMCSNext G' (order.take k).toFinset (order.get ⟨k, hk⟩) ↔
      G'.neigh (order.take k).toFinset (laterVert order u v) >
          G'.neigh (order.take k).toFinset (order.get ⟨k, hk⟩) ∨
        (G'.neigh (order.take k).toFinset (laterVert order u v) =
            G'.neigh (order.take k).toFinset (order.get ⟨k, hk⟩) ∧
          laterVert order u v < order.get ⟨k, hk⟩) := by
  rw [IsMCSNext_toDyn, laterVert_eq]
  exact DynamicMCS.Eea71821.insert_break_iff (G := Transport.toDyn G) order u v
    ((FlipOf_toDyn G G' u v).1 hflip) hins hins' ((IsMCSOrdering_toDyn G order).1 hvalid) k hk
    (by rwa [earlierPos_eq] at hgt) (by rwa [laterPos_eq] at hle)

/-! ## Insertion window: the later endpoint is never a break

For an insertion flip, at the exact position `laterPos` the probe examines the
later endpoint itself as the old choice; that choice is always legal on the
post-insertion graph.  Hence the window can be shrunk by one at the right end,
and strictly inside the open window the break test is the *old-graph* comparison
of the later endpoint against the old choice. -/

/-- A valid MCS ordering contains every vertex (Challenge-level restatement of
the project lemma). -/
lemma mem_of_IsMCSOrdering (order : List (Vert n)) (hvalid : IsMCSOrdering G order) :
    ∀ z : Vert n, z ∈ order :=
  DynamicMCS.UGraph.mem_of_IsMCSOrdering order ((IsMCSOrdering_toDyn G order).1 hvalid)

/-- The vertex at position `laterPos` is exactly `laterVert`. -/
lemma laterVert_get (order : List (Vert n)) (u v : Vert n) (_hmem : u ∈ order)
    (_hmem' : v ∈ order) (h : laterPos order u v < order.length) :
    order.get ⟨laterPos order u v, h⟩ = laterVert order u v := by
  classical
  unfold laterPos laterVert
  by_cases hh : List.idxOf u order ≤ List.idxOf v order
  · simp [hh]
  · have hle : List.idxOf v order ≤ List.idxOf u order := le_of_not_ge hh
    simp [hh, hle]

/-- The earlier position is strictly below the later position. -/
lemma earlierPos_lt_laterPos (order : List (Vert n)) (u v : Vert n)
    (huv : u ≠ v) (hnodup : order.Nodup) (hmu : u ∈ order) (hmv : v ∈ order) :
    earlierPos order u v < laterPos order u v := by
  rw [earlierPos_eq, laterPos_eq]
  exact DynamicMCS.Eea71821.earlierPos_lt_laterPos order u v huv hnodup hmu hmv

/-- Transport of the project's insertion cardinality analysis to the
`Challenge` layer. -/
lemma neigh_flip_insert (hflip : FlipOf G G' u v) (hins : ¬ G.adj u v) (hins' : G'.adj u v)
    (s : Finset (Vert n)) (a w : Vert n) (ha : a ∈ s) (hw : w ∉ s)
    (haw : a ≠ w) (hae : a = u ∨ a = v) (hwe : w = u ∨ w = v) :
    (∀ x ∈ s, G'.neigh s x = G.neigh s x) ∧
      G'.neigh s w = G.neigh s w + 1 ∧
      (∀ y, y ∉ s → y ≠ w → G'.neigh s y = G.neigh s y) :=
  DynamicMCS.Eea71821.neigh_flip_insert (G := Transport.toDyn G) (G' := Transport.toDyn G')
    ((FlipOf_toDyn G G' u v).1 hflip) hins hins' s a w ha hw haw hae hwe

/-- Arithmetic normalization of the insertion break condition, using that the
old choice is a maximum (its cardinality `c` is at least the later endpoint's
`d` on the old graph). -/
lemma neigh_arith (d c : ℕ) (w x : Vert n) (hle : d ≤ c) :
    (d + 1 > c ∨ ((d + 1 = c) ∧ w < x)) ↔
      (d = c ∨ ((d = c - 1) ∧ w < x)) := by
  constructor
  · rintro (h1 | ⟨h2, hp⟩)
    · have : d = c := by omega
      exact Or.inl this
    · have h3 : d = c - 1 := by omega
      exact Or.inr ⟨h3, hp⟩
  · rintro (h1 | ⟨h2, hp⟩)
    · have h3 : d + 1 > c := by omega
      exact Or.inl h3
    · by_cases hc : c = 0
      · have h3 : d + 1 > c := by omega
        exact Or.inl h3
      · have h3 : d + 1 = c := by omega
        exact Or.inr ⟨h3, hp⟩

/-- M5(i): for an insertion flip, the old pick at the exact position `laterPos`
is not a break on `G'`. -/
theorem no_break_at_laterPos (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hins : ¬ G.adj u v) (hins' : G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (hk : laterPos order u v < order.length) :
    IsMCSNext G' (order.take (laterPos order u v)).toFinset
      (order.get ⟨laterPos order u v, hk⟩) := by
  classical
  have hmem : u ∈ order := mem_of_IsMCSOrdering order hvalid u
  have hmv : v ∈ order := mem_of_IsMCSOrdering order hvalid v
  have hget := laterVert_get order u v hmem hmv hk
  have hlt := earlierPos_lt_laterPos order u v hflip.1 hvalid.1 hmem hmv
  have hiff := insert_break_iff u v order hflip hins hins' hvalid (laterPos order u v) hk hlt le_rfl
  rw [hget] at hiff
  simp only [lt_irrefl, and_false, or_false] at hiff
  rw [hget]
  by_contra hn
  exact hiff.mp hn

/-- M5(ii): for an insertion flip, at every position `k` strictly inside the
open window `(earlierPos, laterPos)` the old choice breaks on `G'` exactly when
the later endpoint beats it on the *old* graph: equal old-graph cardinality, or
strictly larger old-graph cardinality by one with a smaller index. -/
theorem insert_break_iff_old (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hins : ¬ G.adj u v) (hins' : G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (k : ℕ) (hk : k < order.length)
    (hgt : earlierPos order u v < k) (hlt : k < laterPos order u v) :
    ¬ IsMCSNext G' (order.take k).toFinset (order.get ⟨k, hk⟩) ↔
      G.neigh (order.take k).toFinset (laterVert order u v) =
          G.neigh (order.take k).toFinset (order.get ⟨k, hk⟩) ∨
        (G.neigh (order.take k).toFinset (laterVert order u v) =
            G.neigh (order.take k).toFinset (order.get ⟨k, hk⟩) - 1 ∧
          laterVert order u v < order.get ⟨k, hk⟩) := by
  classical
  let chosen := (order.take k).toFinset
  let x := order.get ⟨k, hk⟩
  let w := laterVert order u v
  let a := DynamicMCS.Eea71821.earlierVert order u v
  have huv := hflip.1
  have hnodup := hvalid.1
  have hmu : u ∈ order := mem_of_IsMCSOrdering order hvalid u
  have hmv : v ∈ order := mem_of_IsMCSOrdering order hvalid v
  have hwe : w = u ∨ w = v := by
    simp only [w]
    rw [Transport.laterVert_eq]
    exact DynamicMCS.Eea71821.laterVert_eq order u v
  have hae : a = u ∨ a = v := DynamicMCS.Eea71821.earlierVert_eq order u v
  have haw : a ≠ w := by
    have h := DynamicMCS.Eea71821.earlier_ne_later order u v huv hnodup hmu hmv
    simp only [w]
    rw [Transport.laterVert_eq]
    exact h
  have hw_mem : w ∈ order := by
    rcases hwe with h | h
    · rw [h]; exact hmu
    · rw [h]; exact hmv
  have ha_mem : a ∈ order := by
    rcases hae with h | h
    · rw [h]; exact hmu
    · rw [h]; exact hmv
  have hidx_a : List.idxOf a order = earlierPos order u v := by
    rw [DynamicMCS.Eea71821.idxOf_earlierVert, Transport.earlierPos_eq]
  have hidx_w : List.idxOf w order = laterPos order u v := by
    simp only [w]
    rw [Transport.laterVert_eq, DynamicMCS.Eea71821.idxOf_laterVert, Transport.laterPos_eq]
  have haC : a ∈ chosen := by
    have hmem : a ∈ order.take k := by
      rw [List.mem_take_iff_idxOf_lt ha_mem, hidx_a]
      exact hgt
    exact List.mem_toFinset.mpr hmem
  have hwN : w ∉ chosen := by
    rw [List.mem_toFinset]
    intro hwmem
    have hwi : List.idxOf w order < k := (List.mem_take_iff_idxOf_lt hw_mem).mp hwmem
    rw [hidx_w] at hwi
    omega
  have hxN : x ∉ chosen := by
    rw [List.mem_toFinset]
    intro hxmem
    have hxi : List.idxOf x order < k :=
      (List.mem_take_iff_idxOf_lt (List.get_mem order ⟨k, hk⟩)).mp hxmem
    have hxpos : List.idxOf x order = k := List.get_idxOf hnodup ⟨k, hk⟩
    rw [hxpos] at hxi
    omega
  have hxU : x ∈ (Finset.univ : Finset (Vert n)) \ chosen :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxN⟩
  have hwU : w ∈ (Finset.univ : Finset (Vert n)) \ chosen :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwN⟩
  have hxw : x ≠ w := by
    intro hxw
    have hxpos : List.idxOf x order = k := List.get_idxOf hnodup ⟨k, hk⟩
    rw [hxw, hidx_w] at hxpos
    omega
  have hnextG : IsMCSNext G chosen x := hvalid.2.2 k hk
  have hxmax : ∀ y, y ∈ (Finset.univ : Finset (Vert n)) \ chosen →
      G.neigh chosen y ≤ G.neigh chosen x := hnextG.2.1
  have hAw := neigh_flip_insert hflip hins hins' chosen a w haC hwN haw hae hwe
  have hB : G'.neigh chosen w = G.neigh chosen w + 1 := hAw.2.1
  have hC := hAw.2.2
  have hxC_eq : G'.neigh chosen x = G.neigh chosen x := hC x hxN hxw
  have hbridge : ¬ IsMCSNext G' chosen x ↔
      (G'.neigh chosen w > G'.neigh chosen x ∨
        (G'.neigh chosen w = G'.neigh chosen x ∧ w < x)) := by
    have hle : k ≤ laterPos order u v := le_of_lt hlt
    have hiff := insert_break_iff u v order hflip hins hins' hvalid k hk hgt hle
    simpa only [chosen, x, w] using hiff
  rw [hbridge, hB, hxC_eq]
  exact neigh_arith (G.neigh chosen w) (G.neigh chosen x) w x (hxmax w hwU)

/-- The insertion probe can drop the right window bound by one: since the old
pick at the exact position `laterPos` is never a break, stopping the scan one
step earlier loses nothing. -/
theorem insert_window_open (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hins : ¬ G.adj u v) (hins' : G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    firstBreakWindow G' order (earlierPos order u v + 1) (laterPos order u v)
      = firstBreakWindow G' order (earlierPos order u v + 1) (laterPos order u v - 1) := by
  classical
  have hmem : u ∈ order := mem_of_IsMCSOrdering order hvalid u
  have hmv : v ∈ order := mem_of_IsMCSOrdering order hvalid v
  have hk : laterPos order u v < order.length := by
    unfold laterPos
    have h1 := List.idxOf_lt_length_of_mem hmem
    have h2 := List.idxOf_lt_length_of_mem hmv
    omega
  have hlegal_hk : IsMCSNext G' (order.take (laterPos order u v)).toFinset
      (order.get ⟨laterPos order u v, hk⟩) :=
    no_break_at_laterPos u v order hflip hins hins' hvalid hk
  rw [UGraph.firstBreakWindow_eq_scan, UGraph.firstBreakWindow_eq_scan]
  cases hs : firstBreak G' order (earlierPos order u v + 1) with
  | none => rfl
  | some j =>
      have hsome := (DynamicMCS.Eea71821.firstBreak_some (H := Transport.toDyn G')
        order (earlierPos order u v + 1) j)
      have hsdyn : DynamicMCS.Eea71821.firstBreak (Transport.toDyn G') order
          (earlierPos order u v + 1) = some j := by
        rwa [Transport.firstBreak_eq] at hs
      rcases hsome.mp hsdyn with ⟨hjlen, hjge, hbad, hall⟩
      have hjle : j ≤ laterPos order u v := by
        by_contra h
        have hgt : laterPos order u v < j := lt_of_not_ge h
        have hleg : IsMCSNext G' (order.take j).toFinset (order.get ⟨j, hjlen⟩) :=
          legal_after_laterPos u v order hflip hvalid j hjlen hgt
        exact hbad ((IsMCSNext_toDyn G' _ _).1 hleg)
      have hjnlt : j ≠ laterPos order u v := by
        intro hjeq
        subst hjeq
        have hnext : (Transport.toDyn G').IsMCSNext (order.take (laterPos order u v)).toFinset
            (order.get ⟨laterPos order u v, hjlen⟩) := by
          rw [show order.get ⟨laterPos order u v, hjlen⟩
              = order.get ⟨laterPos order u v, hk⟩ from congrArg order.get (Fin.ext rfl)]
          exact (IsMCSNext_toDyn G' _ _).1 hlegal_hk
        exact hbad hnext
      have hiff : (j ≤ laterPos order u v) ↔ (j ≤ laterPos order u v - 1) := by omega
      simp only [Option.filter, decide_eq_true_eq, hiff]

/-! ## Null updates -/

/-- The insertion update returns `order` unchanged exactly when `order` is
still the canonical MCS ordering of the new graph. -/
theorem insert_update_eq_self_iff (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    insertUpdate G' order u v = order ↔ IsMCSOrdering G' order := by
  constructor
  · intro h
    rw [← h]
    exact insert_update_valid u v order hflip hvalid
  · intro h'
    exact IsMCSOrdering_unique (insert_update_valid u v order hflip hvalid) h'

/-- The deletion update returns `order` unchanged exactly when `order` is
still the canonical MCS ordering of the new graph. -/
theorem delete_update_eq_self_iff (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    deleteUpdate G' order u v = order ↔ IsMCSOrdering G' order := by
  constructor
  · intro h
    rw [← h]
    exact delete_update_valid u v order hflip hdel hdel' hvalid
  · intro h'
    exact IsMCSOrdering_unique (delete_update_valid u v order hflip hdel hdel' hvalid) h'

/-- If the window probe finds no break, the insertion update returns `order`
itself (no regreedy). -/
theorem insert_update_of_no_break (u v : Vert n) (order : List (Vert n))
    (hvalid : IsMCSOrdering G order)
    (h : firstBreakWindow G' order (earlierPos order u v + 1) (laterPos order u v) = none) :
    insertUpdate G' order u v = order := by
  simp only [insertUpdate, h, Option.getD_none, List.take_length]
  exact greedySuffix_full G' order (order_toFinset_univ hvalid)

/-- If the deletion probe does not fire, the deletion update returns `order`
itself (no regreedy). -/
theorem delete_update_of_no_break (u v : Vert n) (order : List (Vert n))
    (h : deletionBreaks G' order u v = false) :
    deleteUpdate G' order u v = order := by
  unfold deleteUpdate
  rw [h]
  rfl

end Proofs
end Challenge
