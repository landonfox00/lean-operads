/-
# The trees of the L∞ transfer

For an odd bracket `μ`, linear maps `e` and `h`, parities `p` and inputs `v` on a linear order
`α`, and `2` invertible, the trees of the transfer are defined on finite sets `S` of inputs:
`tree {a} = e (v a)` and `tree S = h (λ S)` for two inputs or more, with
`λ S = ½ ∑_T ± μ (tree T, tree (S ∖ T))` over the splittings of `S` into two nonempty parts,
the sign being the Koszul sign of the unshuffle (`LInfT.tree`, `LInfT.lam`).

* **Relabelling and locality.** Trees are invariant under order embeddings of the inputs
  (`LInfT.tree_map`) and only depend on the inputs in `S` (`LInfT.tree_congr`).
* **Splittings into three parts** (`LInfT.trip`), as iterated splittings
  (`LInfT.sum_splits_splits`, `LInfT.sum_splits_splits_sdiff`), with their three reindexings,
  and **the least input argument** (`LInfT.sum_trip_eq_zero`): a function of three parts,
  symmetric in the first two and summing to zero over the rotations fixing the first part, sums
  to zero. With the Jacobi identity this is what cancels the brackets of brackets of trees.
* **Multilinearity** (`LInfT.tree_update_lin`, `LInfT.lam_update_lin`).
* **Graded symmetry.** Exchanging two adjacent inputs multiplies a tree by their Koszul sign when
  both are inputs of the tree (`LInfT.tree_swap`, `LInfT.lam_swap`), the signs of the unshuffles
  changing exactly when the two inputs are on different sides (`LInfT.ks_swap`).
-/
import Operad.UnshuffleSign
import Operad.HTT

universe u v

namespace Operad

namespace LInfT

open GerBV KS

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {α : Type*} [LinearOrder α]

/-! ## Splittings -/

/-- **The splittings of a set into two nonempty parts**, by the first part. -/
def splits (S : Finset α) : Finset (Finset α) :=
  S.powerset.filter fun T => T.Nonempty ∧ T ≠ S

lemma mem_splits {S T : Finset α} : T ∈ splits S ↔ T ⊆ S ∧ T.Nonempty ∧ T ≠ S := by
  unfold splits
  rw [Finset.mem_filter, Finset.mem_powerset]

lemma card_lt_of_mem_splits {S T : Finset α} (h : T ∈ splits S) : T.card < S.card := by
  obtain ⟨h1, -, h3⟩ := mem_splits.1 h
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨h1, h3⟩)

lemma card_sdiff_lt_of_mem_splits {S T : Finset α} (h : T ∈ splits S) :
    (S \ T).card < S.card := by
  obtain ⟨h1, h2, -⟩ := mem_splits.1 h
  have h4 := Finset.card_sdiff_add_card_eq_card h1
  have h5 := h2.card_pos
  omega

lemma sdiff_mem_splits {S T : Finset α} (h : T ∈ splits S) : S \ T ∈ splits S := by
  obtain ⟨h1, h2, h3⟩ := mem_splits.1 h
  refine mem_splits.2 ⟨Finset.sdiff_subset, ?_, fun e => ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro e
    exact h3 (Finset.Subset.antisymm h1 (Finset.sdiff_eq_empty_iff_subset.1 e))
  · obtain ⟨a, ha⟩ := h2
    have : a ∈ S \ T := by rw [e]; exact h1 ha
    exact (Finset.mem_sdiff.1 this).2 ha

lemma sdiff_sdiff_of_mem_splits {S T : Finset α} (h : T ∈ splits S) : S \ (S \ T) = T :=
  Finset.sdiff_sdiff_eq_self (mem_splits.1 h).1

lemma splits_of_card_le_one {S : Finset α} (h : S.card ≤ 1) : splits S = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro T hT
  have h1 := card_lt_of_mem_splits hT
  have h2 := (mem_splits.1 hT).2.1.card_pos
  omega

/-- Splittings of an embedded set are embedded splittings. -/
lemma splits_map {β : Type*} [LinearOrder β] (ι : α ↪o β) (S : Finset α) :
    splits (S.map ι.toEmbedding) = (splits S).map ⟨fun T => T.map ι.toEmbedding,
      fun _ _ h => Finset.map_injective _ h⟩ := by
  ext T'
  rw [Finset.mem_map, mem_splits]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨T, hT, rfl⟩ := Finset.subset_map_iff.1 h1
    refine ⟨T, mem_splits.2 ⟨hT, ?_, fun e => h3 (by rw [e])⟩, rfl⟩
    exact Finset.map_nonempty.1 h2
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨h1, h2, h3⟩ := mem_splits.1 hT
    exact ⟨Finset.map_subset_map.2 h1, Finset.map_nonempty.2 h2,
      fun e => h3 (Finset.map_injective _ e)⟩

/-! ## Splittings into three parts -/

/-- **The splittings of a set into three nonempty parts**, by the first two. -/
def trip (S : Finset α) : Finset (Finset α × Finset α) :=
  (S.powerset ×ˢ S.powerset).filter fun q =>
    q.1.Nonempty ∧ q.2.Nonempty ∧ Disjoint q.1 q.2 ∧ (S \ (q.1 ∪ q.2)).Nonempty

lemma mem_trip {S : Finset α} {q : Finset α × Finset α} :
    q ∈ trip S ↔ q.1 ⊆ S ∧ q.2 ⊆ S ∧ q.1.Nonempty ∧ q.2.Nonempty ∧ Disjoint q.1 q.2 ∧
      (S \ (q.1 ∪ q.2)).Nonempty := by
  unfold trip
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
  tauto

lemma sdiff_union_sdiff {S X Y : Finset α} (hX : X ⊆ S) (hY : Y ⊆ S) (hXY : Disjoint X Y) :
    S \ (X ∪ (S \ (X ∪ Y))) = Y := by
  ext a
  have h1 := @hX a
  have h2 := @hY a
  have h3 : a ∈ X → a ∉ Y := fun h => Finset.disjoint_left.1 hXY h
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

lemma disjoint_sdiff_union {S X Y : Finset α} : Disjoint X (S \ (X ∪ Y)) :=
  Finset.disjoint_left.2 fun _ ha ha' => (Finset.mem_sdiff.1 ha').2 (Finset.mem_union_left _ ha)

lemma trip_xz {S : Finset α} {q : Finset α × Finset α} (hq : q ∈ trip S) :
    (q.1, S \ (q.1 ∪ q.2)) ∈ trip S ∧ S \ (q.1 ∪ (S \ (q.1 ∪ q.2))) = q.2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_trip.1 hq
  have e := sdiff_union_sdiff h1 h2 h5
  refine ⟨mem_trip.2 ⟨h1, Finset.sdiff_subset, h3, h6, disjoint_sdiff_union, ?_⟩, e⟩
  simp only
  rw [e]
  exact h4

lemma trip_swap {S : Finset α} {q : Finset α × Finset α} (hq : q ∈ trip S) :
    (q.2, q.1) ∈ trip S ∧ S \ (q.2 ∪ q.1) = S \ (q.1 ∪ q.2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_trip.1 hq
  refine ⟨mem_trip.2 ⟨h2, h1, h4, h3, h5.symm, ?_⟩, by rw [Finset.union_comm]⟩
  simp only
  rw [Finset.union_comm]
  exact h6

variable {M : Type*} [AddCommMonoid M]

/-- Three-part splittings as a splitting followed by a splitting of the first part. -/
lemma sum_splits_splits (S : Finset α) (G : Finset α → Finset α → Finset α → M) :
    ∑ A ∈ splits S, ∑ X ∈ splits A, G X (A \ X) (S \ A)
      = ∑ q ∈ trip S, G q.1 q.2 (S \ (q.1 ∪ q.2)) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => (x.2, x.1 \ x.2)) (fun q _ => ⟨q.1 ∪ q.2, q.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨A, X⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hA, hX⟩ := hx
    obtain ⟨hAS, -, -⟩ := mem_splits.1 hA
    obtain ⟨hXA, hXn, -⟩ := mem_splits.1 hX
    refine mem_trip.2 ⟨hXA.trans hAS, Finset.sdiff_subset.trans hAS, hXn, ?_,
      Finset.disjoint_sdiff, ?_⟩
    · exact (sdiff_mem_splits hX |> mem_splits.1).2.1
    · simp only
      rw [Finset.union_sdiff_of_subset hXA]
      exact (sdiff_mem_splits hA |> mem_splits.1).2.1
  · rintro ⟨X, Y⟩ hq
    obtain ⟨hX, hY, hXn, hYn, hXY, hZ⟩ := mem_trip.1 hq
    simp only at hX hY hXn hYn hXY hZ
    rw [Finset.mem_sigma]
    dsimp only
    refine ⟨mem_splits.2 ⟨Finset.union_subset hX hY, hXn.mono Finset.subset_union_left,
      fun e => ?_⟩, mem_splits.2 ⟨Finset.subset_union_left, hXn, fun e => ?_⟩⟩
    · obtain ⟨a, ha⟩ := hZ
      rw [e] at ha
      exact (Finset.mem_sdiff.1 ha).2 (Finset.mem_sdiff.1 ha).1
    · obtain ⟨a, ha⟩ := hYn
      have : a ∈ X := by rw [e]; exact Finset.mem_union_right _ ha
      exact Finset.disjoint_left.1 hXY this ha
  · rintro ⟨A, X⟩ hx
    rw [Finset.mem_sigma] at hx
    simp only
    rw [Finset.union_sdiff_of_subset (mem_splits.1 hx.2).1]
  · rintro ⟨X, Y⟩ hq
    obtain ⟨-, -, -, -, hXY, -⟩ := mem_trip.1 hq
    simp only at hXY
    simp only [Prod.mk.injEq, true_and]
    rw [Finset.union_sdiff_cancel_left hXY]
  · rintro ⟨A, X⟩ hx
    rw [Finset.mem_sigma] at hx
    simp only
    rw [Finset.union_sdiff_of_subset (mem_splits.1 hx.2).1]

/-- Three-part splittings as a splitting followed by a splitting of the second part. -/
lemma sum_splits_splits_sdiff (S : Finset α) (H : Finset α → Finset α → Finset α → M) :
    ∑ A ∈ splits S, ∑ Y ∈ splits (S \ A), H A Y ((S \ A) \ Y)
      = ∑ q ∈ trip S, H (S \ (q.1 ∪ q.2)) q.1 q.2 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => (x.2, (S \ x.1) \ x.2))
    (fun q _ => ⟨S \ (q.1 ∪ q.2), q.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨A, Y⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hA, hY⟩ := hx
    obtain ⟨hAS, hAn, -⟩ := mem_splits.1 hA
    obtain ⟨hYA, hYn, -⟩ := mem_splits.1 hY
    refine mem_trip.2 ⟨hYA.trans Finset.sdiff_subset, Finset.sdiff_subset.trans
      Finset.sdiff_subset, hYn, (sdiff_mem_splits hY |> mem_splits.1).2.1,
      Finset.disjoint_sdiff, ?_⟩
    simp only
    rw [Finset.union_sdiff_of_subset hYA, Finset.sdiff_sdiff_eq_self hAS]
    exact hAn
  · rintro ⟨X, Y⟩ hq
    obtain ⟨hX, hY, hXn, hYn, hXY, hZ⟩ := mem_trip.1 hq
    simp only at hX hY hXn hYn hXY hZ
    rw [Finset.mem_sigma]
    dsimp only
    have hXYS : X ∪ Y ⊆ S := Finset.union_subset hX hY
    refine ⟨mem_splits.2 ⟨Finset.sdiff_subset, hZ, fun e => ?_⟩, ?_⟩
    · obtain ⟨a, ha⟩ := hXn
      have h1 : a ∈ S \ (X ∪ Y) := by rw [e]; exact hX ha
      exact (Finset.mem_sdiff.1 h1).2 (Finset.mem_union_left _ ha)
    · rw [Finset.sdiff_sdiff_eq_self hXYS]
      exact mem_splits.2 ⟨Finset.subset_union_left, hXn, fun e => by
        obtain ⟨a, ha⟩ := hYn
        have : a ∈ X := by rw [e]; exact Finset.mem_union_right _ ha
        exact Finset.disjoint_left.1 hXY this ha⟩
  · rintro ⟨A, Y⟩ hx
    rw [Finset.mem_sigma] at hx
    simp only
    rw [Finset.union_sdiff_of_subset (mem_splits.1 hx.2).1,
      Finset.sdiff_sdiff_eq_self (mem_splits.1 hx.1).1]
  · rintro ⟨X, Y⟩ hq
    obtain ⟨hX, hY, -, -, hXY, -⟩ := mem_trip.1 hq
    simp only at hX hY hXY
    simp only [Prod.mk.injEq, true_and]
    rw [Finset.sdiff_sdiff_eq_self (Finset.union_subset hX hY),
      Finset.union_sdiff_cancel_left hXY]
  · rintro ⟨A, Y⟩ hx
    rw [Finset.mem_sigma] at hx
    simp only
    rw [Finset.union_sdiff_of_subset (mem_splits.1 hx.2).1,
      Finset.sdiff_sdiff_eq_self (mem_splits.1 hx.1).1]

/-- Exchanging the first two parts. -/
lemma sum_trip_swap (S : Finset α) (G : Finset α → Finset α → Finset α → M) :
    ∑ q ∈ trip S, G q.1 q.2 (S \ (q.1 ∪ q.2)) = ∑ q ∈ trip S, G q.2 q.1 (S \ (q.1 ∪ q.2)) := by
  refine Finset.sum_nbij' (fun q => (q.2, q.1)) (fun q => (q.2, q.1))
    (fun q hq => (trip_swap hq).1) (fun q hq => (trip_swap hq).1) (fun q _ => rfl)
    (fun q _ => rfl) fun q hq => ?_
  show G q.1 q.2 (S \ (q.1 ∪ q.2)) = G q.1 q.2 (S \ (q.2 ∪ q.1))
  rw [(trip_swap hq).2]

/-- Exchanging the last two parts. -/
lemma sum_trip_xz (S : Finset α) (G : Finset α → Finset α → Finset α → M) :
    ∑ q ∈ trip S, G q.1 q.2 (S \ (q.1 ∪ q.2)) = ∑ q ∈ trip S, G q.1 (S \ (q.1 ∪ q.2)) q.2 := by
  refine Finset.sum_nbij' (fun q => (q.1, S \ (q.1 ∪ q.2))) (fun q => (q.1, S \ (q.1 ∪ q.2)))
    (fun q hq => (trip_xz hq).1) (fun q hq => (trip_xz hq).1)
    (fun q hq => Prod.ext rfl (trip_xz hq).2) (fun q hq => Prod.ext rfl (trip_xz hq).2)
    fun q hq => ?_
  show G q.1 q.2 (S \ (q.1 ∪ q.2)) = G q.1 (S \ (q.1 ∪ (S \ (q.1 ∪ q.2)))) (S \ (q.1 ∪ q.2))
  rw [(trip_xz hq).2]

/-- Rotating the three parts. -/
lemma sum_trip_cyc (S : Finset α) (G : Finset α → Finset α → Finset α → M) :
    ∑ q ∈ trip S, G q.1 q.2 (S \ (q.1 ∪ q.2)) = ∑ q ∈ trip S, G q.2 (S \ (q.1 ∪ q.2)) q.1 := by
  have hZX : ∀ q ∈ trip S, (S \ (q.1 ∪ q.2), q.1) ∈ trip S ∧
      S \ (S \ (q.1 ∪ q.2) ∪ q.1) = q.2 := fun q hq => by
    obtain ⟨h1, -, -⟩ := mem_trip.1 hq
    have hs := trip_swap (trip_xz hq).1
    simp only at hs
    refine ⟨hs.1, ?_⟩
    rw [hs.2]
    exact (trip_xz hq).2
  have hYZ : ∀ q ∈ trip S, (q.2, S \ (q.1 ∪ q.2)) ∈ trip S ∧
      S \ (q.2 ∪ S \ (q.1 ∪ q.2)) = q.1 := fun q hq => by
    have hs := trip_xz (trip_swap hq).1
    simp only at hs
    rw [(trip_swap hq).2] at hs
    exact hs
  refine Finset.sum_nbij' (fun q => (S \ (q.1 ∪ q.2), q.1)) (fun q => (q.2, S \ (q.1 ∪ q.2)))
    (fun q hq => (hZX q hq).1) (fun q hq => (hYZ q hq).1)
    (fun q hq => Prod.ext rfl (hZX q hq).2) (fun q hq => Prod.ext (hYZ q hq).2 rfl)
    fun q hq => ?_
  show G q.1 q.2 (S \ (q.1 ∪ q.2)) = G q.1 (S \ (S \ (q.1 ∪ q.2) ∪ q.1)) (S \ (q.1 ∪ q.2))
  rw [(hZX q hq).2]

/-- **The least input argument**: a function of three parts, symmetric in the first two and
summing to zero over the three rotations fixing the first part, sums to zero over the
three-part splittings. -/
lemma sum_trip_eq_zero {N : Type*} [AddCommGroup N] (S : Finset α)
    (F : Finset α → Finset α → Finset α → N)
    (hsym : ∀ q ∈ trip S, F q.2 q.1 (S \ (q.1 ∪ q.2)) = F q.1 q.2 (S \ (q.1 ∪ q.2)))
    (hjac : ∀ q ∈ trip S, F q.1 q.2 (S \ (q.1 ∪ q.2)) + F q.1 (S \ (q.1 ∪ q.2)) q.2 +
      F q.2 (S \ (q.1 ∪ q.2)) q.1 = 0) :
    ∑ q ∈ trip S, F q.1 q.2 (S \ (q.1 ∪ q.2)) = 0 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨m, hm⟩
  · refine Finset.sum_eq_zero fun q hq => ?_
    obtain ⟨h1, -, h3, -⟩ := mem_trip.1 hq
    obtain ⟨a, ha⟩ := h3
    exact absurd (h1 ha) (Finset.notMem_empty a)
  have hsplit : ∀ q ∈ trip S, F q.1 q.2 (S \ (q.1 ∪ q.2)) =
      (if m ∈ q.1 then F q.1 q.2 (S \ (q.1 ∪ q.2)) else 0) +
      (if m ∈ q.2 then F q.1 q.2 (S \ (q.1 ∪ q.2)) else 0) +
      (if m ∈ S \ (q.1 ∪ q.2) then F q.1 q.2 (S \ (q.1 ∪ q.2)) else 0) := by
    intro q hq
    obtain ⟨-, -, -, -, h5, -⟩ := mem_trip.1 hq
    by_cases h1 : m ∈ q.1
    · have h2 : m ∉ q.2 := Finset.disjoint_left.1 h5 h1
      have h3 : m ∉ S \ (q.1 ∪ q.2) := fun h' =>
        (Finset.mem_sdiff.1 h').2 (Finset.mem_union_left _ h1)
      rw [if_pos h1, if_neg h2, if_neg h3, add_zero, add_zero]
    · by_cases h2 : m ∈ q.2
      · have h3 : m ∉ S \ (q.1 ∪ q.2) := fun h' =>
          (Finset.mem_sdiff.1 h').2 (Finset.mem_union_right _ h2)
        rw [if_neg h1, if_pos h2, if_neg h3, zero_add, add_zero]
      · have h3 : m ∈ S \ (q.1 ∪ q.2) :=
          Finset.mem_sdiff.2 ⟨hm, fun h' => (Finset.mem_union.1 h').elim h1 h2⟩
        rw [if_neg h1, if_neg h2, if_pos h3, zero_add, zero_add]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e2 := sum_trip_swap S fun A B C => if m ∈ B then F A B C else 0
  have e2' := sum_trip_xz S fun A B C => if m ∈ A then F A B C else 0
  have e3 := sum_trip_cyc S fun A B C => if m ∈ C then F A B C else 0
  simp only at e2 e2' e3
  rw [e2, e3]
  have e4 : ∑ q ∈ trip S, (if m ∈ q.1 then F q.2 q.1 (S \ (q.1 ∪ q.2)) else 0)
      = ∑ q ∈ trip S, (if m ∈ q.1 then F q.1 q.2 (S \ (q.1 ∪ q.2)) else 0) :=
    Finset.sum_congr rfl fun q hq => by rw [hsym q hq]
  rw [e4.trans e2', ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun q hq => ?_
  by_cases h1 : m ∈ q.1
  · rw [if_pos h1, if_pos h1, if_pos h1]
    exact hjac q hq
  · simp only [if_neg h1, add_zero]

/-! ## The trees -/

variable [Invertible (2 : R)] (μ : End R V 2) (e h : V →ₗ[R] V) (p : α → Bool) (v : α → V)

/-- **The trees of the transfer** on a set of inputs `S`: `e` on one input, and
`h (½ ∑ ± μ (tree T, tree (S ∖ T)))` over the splittings of `S`, the sign being the Koszul sign
of the unshuffle. -/
noncomputable def tree (S : Finset α) : V :=
  if S.card ≤ 1 then ∑ a ∈ S, e (v a)
  else h ((⅟2 : R) • ∑ T ∈ (splits S).attach,
    ks R p T.1 (S \ T.1) • μ ![tree T.1, tree (S \ T.1)])
termination_by S.card
decreasing_by
  all_goals first
    | exact card_lt_of_mem_splits T.2
    | exact card_sdiff_lt_of_mem_splits T.2

/-- **The brackets of the trees** over the splittings: `λ S = ½ ∑ ± μ (tree T, tree (S ∖ T))`. -/
noncomputable def lam (S : Finset α) : V :=
  (⅟2 : R) • ∑ T ∈ splits S, ks R p T (S \ T) • μ ![tree μ e h p v T, tree μ e h p v (S \ T)]

lemma tree_eq (S : Finset α) :
    tree μ e h p v S = if S.card ≤ 1 then ∑ a ∈ S, e (v a) else h (lam μ e h p v S) := by
  rw [tree]
  split_ifs with hS
  · rfl
  · unfold lam
    rw [Finset.sum_attach (splits S) fun T =>
      ks R p T (S \ T) • μ ![tree μ e h p v T, tree μ e h p v (S \ T)]]

lemma tree_of_card_le_one {S : Finset α} (hS : S.card ≤ 1) :
    tree μ e h p v S = ∑ a ∈ S, e (v a) := by
  rw [tree_eq, if_pos hS]

lemma tree_of_one_lt {S : Finset α} (hS : 1 < S.card) : tree μ e h p v S = h (lam μ e h p v S) := by
  rw [tree_eq, if_neg (by omega)]

@[simp] lemma tree_singleton (a : α) : tree μ e h p v {a} = e (v a) := by
  rw [tree_of_card_le_one μ e h p v (by simp), Finset.sum_singleton]

@[simp] lemma tree_empty : tree μ e h p v ∅ = 0 := by
  rw [tree_of_card_le_one μ e h p v (by simp), Finset.sum_empty]

lemma lam_of_card_le_one {S : Finset α} (hS : S.card ≤ 1) : lam μ e h p v S = 0 := by
  rw [lam, splits_of_card_le_one hS, Finset.sum_empty, smul_zero]

/-! ## Relabelling and locality -/

/-- **Trees are invariant under order embeddings of the inputs.** -/
theorem tree_map {β : Type*} [LinearOrder β] (ι : α ↪o β) (q : β → Bool) (w : β → V) :
    ∀ (n : ℕ) (S : Finset α), S.card = n →
      tree μ e h (q ∘ ι) (w ∘ ι) S = tree μ e h q w (S.map ι.toEmbedding) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn
    by_cases hS : S.card ≤ 1
    · rw [tree_of_card_le_one μ e h _ _ hS,
        tree_of_card_le_one μ e h _ _ (by rw [Finset.card_map]; exact hS), Finset.sum_map]
      rfl
    · rw [tree_of_one_lt μ e h _ _ (by omega),
        tree_of_one_lt μ e h _ _ (by rw [Finset.card_map]; omega)]
      congr 1
      unfold lam
      congr 1
      rw [splits_map, Finset.sum_map]
      refine Finset.sum_congr rfl fun T hT => ?_
      simp only [Function.Embedding.coeFn_mk]
      rw [← Finset.map_sdiff, ← ks_map, ih _ (hn ▸ card_lt_of_mem_splits hT) T rfl,
        ih _ (hn ▸ card_sdiff_lt_of_mem_splits hT) (S \ T) rfl]

lemma lam_map {β : Type*} [LinearOrder β] (ι : α ↪o β) (q : β → Bool) (w : β → V)
    (S : Finset α) :
    lam μ e h (q ∘ ι) (w ∘ ι) S = lam μ e h q w (S.map ι.toEmbedding) := by
  unfold lam
  congr 1
  rw [splits_map, Finset.sum_map]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [← Finset.map_sdiff, ← ks_map, tree_map μ e h ι q w _ T rfl,
    tree_map μ e h ι q w _ (S \ T) rfl]

/-- **Trees only depend on their inputs.** -/
theorem tree_congr {p' : α → Bool} {v' : α → V} :
    ∀ (n : ℕ) (S : Finset α), S.card = n → (∀ a ∈ S, p a = p' a) → (∀ a ∈ S, v a = v' a) →
      tree μ e h p v S = tree μ e h p' v' S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hp hv
    by_cases hS : S.card ≤ 1
    · rw [tree_of_card_le_one μ e h _ _ hS, tree_of_card_le_one μ e h _ _ hS]
      exact Finset.sum_congr rfl fun a ha => by rw [hv a ha]
    · rw [tree_of_one_lt μ e h _ _ (by omega), tree_of_one_lt μ e h _ _ (by omega)]
      congr 1
      unfold lam
      congr 1
      refine Finset.sum_congr rfl fun T hT => ?_
      have hTS := (mem_splits.1 hT).1
      have hks : ks R p T (S \ T) = ks R p' T (S \ T) := by
        unfold ks
        refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj => ?_
        rw [hp i (hTS hi), hp j (Finset.sdiff_subset (Finset.mem_filter.1 hj).1)]
      rw [hks, ih _ (hn ▸ card_lt_of_mem_splits hT) T rfl (fun a ha => hp a (hTS ha))
          (fun a ha => hv a (hTS ha)),
        ih _ (hn ▸ card_sdiff_lt_of_mem_splits hT) (S \ T) rfl
          (fun a ha => hp a (Finset.sdiff_subset ha)) (fun a ha => hv a (Finset.sdiff_subset ha))]

lemma lam_congr {p' : α → Bool} {v' : α → V} (S : Finset α) (hp : ∀ a ∈ S, p a = p' a)
    (hv : ∀ a ∈ S, v a = v' a) : lam μ e h p v S = lam μ e h p' v' S := by
  unfold lam
  congr 1
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTS := (mem_splits.1 hT).1
  have hks : ks R p T (S \ T) = ks R p' T (S \ T) := by
    unfold ks
    refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj => ?_
    rw [hp i (hTS hi), hp j (Finset.sdiff_subset (Finset.mem_filter.1 hj).1)]
  rw [hks, tree_congr μ e h p v _ T rfl (fun a ha => hp a (hTS ha)) (fun a ha => hv a (hTS ha)),
    tree_congr μ e h p v _ (S \ T) rfl (fun a ha => hp a (Finset.sdiff_subset ha))
      (fun a ha => hv a (Finset.sdiff_subset ha))]

/-! ## Multilinearity -/

section lin

/-- The brackets of a splitting are additive and homogeneous in each input of the splitting,
given that the trees of the parts are. -/
lemma bracket_update_lin {a : α} {S T : Finset α} (haS : a ∈ S)
    (ih : ∀ U ∈ ({T, S \ T} : Finset (Finset α)), a ∈ U → ∀ (x y : V) (c : R),
      tree μ e h p (Function.update v a (x + y)) U = tree μ e h p (Function.update v a x) U +
        tree μ e h p (Function.update v a y) U ∧
      tree μ e h p (Function.update v a (c • x)) U = c • tree μ e h p (Function.update v a x) U)
    (x y : V) (c : R) :
    μ ![tree μ e h p (Function.update v a (x + y)) T,
        tree μ e h p (Function.update v a (x + y)) (S \ T)]
      = μ ![tree μ e h p (Function.update v a x) T, tree μ e h p (Function.update v a x) (S \ T)] +
        μ ![tree μ e h p (Function.update v a y) T, tree μ e h p (Function.update v a y) (S \ T)]
      ∧ μ ![tree μ e h p (Function.update v a (c • x)) T,
          tree μ e h p (Function.update v a (c • x)) (S \ T)]
        = c • μ ![tree μ e h p (Function.update v a x) T,
          tree μ e h p (Function.update v a x) (S \ T)] := by
  have hfree : ∀ (U : Finset α) (w : V), a ∉ U →
      tree μ e h p (Function.update v a w) U = tree μ e h p v U := fun U w haU =>
    tree_congr μ e h p _ _ U rfl (fun _ _ => rfl)
      fun b hb => Function.update_of_ne (fun e' => haU (by rw [← e']; exact hb)) _ _
  by_cases haT : a ∈ T
  · have haT' : a ∉ S \ T := fun h' => (Finset.mem_sdiff.1 h').2 haT
    obtain ⟨h1, h2⟩ := ih T (Finset.mem_insert_self _ _) haT x y c
    rw [hfree _ _ haT', hfree _ _ haT', hfree _ _ haT', hfree _ _ haT', h1, h2,
      HTT.mu_add_left, HTT.mu_smul_left]
    exact ⟨rfl, rfl⟩
  · have haT' : a ∈ S \ T := Finset.mem_sdiff.2 ⟨haS, haT⟩
    obtain ⟨h1, h2⟩ := ih (S \ T) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) haT'
      x y c
    rw [hfree _ _ haT, hfree _ _ haT, hfree _ _ haT, hfree _ _ haT, h1, h2,
      HTT.mu_add_right, HTT.mu_smul_right]
    exact ⟨rfl, rfl⟩

/-- **The trees are additive and homogeneous in each input.** -/
theorem tree_update_lin (a : α) :
    ∀ (n : ℕ) (S : Finset α), S.card = n → a ∈ S → ∀ (x y : V) (c : R),
      tree μ e h p (Function.update v a (x + y)) S = tree μ e h p (Function.update v a x) S +
        tree μ e h p (Function.update v a y) S ∧
      tree μ e h p (Function.update v a (c • x)) S
        = c • tree μ e h p (Function.update v a x) S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn haS x y c
    by_cases hS : S.card ≤ 1
    · have hSa : S = {a} := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hS with h0 | h1
        · rw [Finset.card_eq_zero.1 h0] at haS
          exact absurd haS (Finset.notMem_empty a)
        · obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 h1
          rw [Finset.mem_singleton.1 haS]
      subst hSa
      refine ⟨?_, ?_⟩ <;> simp [tree_singleton, map_add, map_smul]
    · simp only [tree_of_one_lt μ e h p _ (show 1 < S.card by omega)]
      have hlam : ∀ T ∈ splits S, _ := fun T hT => bracket_update_lin μ e h p v (T := T) haS
        (fun U hU haU => by
          rcases Finset.mem_insert.1 hU with rfl | hU
          · exact ih _ (hn ▸ card_lt_of_mem_splits hT) U rfl haU
          · rw [Finset.mem_singleton.1 hU]
            exact ih _ (hn ▸ card_sdiff_lt_of_mem_splits hT) (S \ T) rfl
              (Finset.mem_singleton.1 hU ▸ haU)) x y c
      unfold lam
      constructor
      · rw [← map_add, ← smul_add, ← Finset.sum_add_distrib]
        refine congrArg h (congrArg (fun z : V => (⅟2 : R) • z)
          (Finset.sum_congr rfl fun T hT => ?_))
        rw [(hlam T hT).1, smul_add]
      · rw [← map_smul, smul_comm c (⅟2 : R), Finset.smul_sum (r := c)]
        refine congrArg h (congrArg (fun z : V => (⅟2 : R) • z)
          (Finset.sum_congr rfl fun T hT => ?_))
        rw [(hlam T hT).2, smul_comm]

/-- **The brackets of the trees are additive and homogeneous in each input.** -/
theorem lam_update_lin {a : α} {S : Finset α} (haS : a ∈ S) (x y : V) (c : R) :
    lam μ e h p (Function.update v a (x + y)) S = lam μ e h p (Function.update v a x) S +
        lam μ e h p (Function.update v a y) S ∧
      lam μ e h p (Function.update v a (c • x)) S = c • lam μ e h p (Function.update v a x) S := by
  have hlam : ∀ T ∈ splits S, _ := fun T hT => bracket_update_lin μ e h p v (T := T) haS
    (fun U hU haU => by
      rcases Finset.mem_insert.1 hU with rfl | hU
      · exact tree_update_lin μ e h p v a _ U rfl haU
      · rw [Finset.mem_singleton.1 hU]
        exact tree_update_lin μ e h p v a _ (S \ T) rfl (Finset.mem_singleton.1 hU ▸ haU)) x y c
  unfold lam
  constructor
  · rw [← smul_add, ← Finset.sum_add_distrib]
    refine congrArg (fun z : V => (⅟2 : R) • z) (Finset.sum_congr rfl fun T hT => ?_)
    rw [(hlam T hT).1, smul_add]
  · rw [smul_comm c (⅟2 : R), Finset.smul_sum (r := c)]
    refine congrArg (fun z : V => (⅟2 : R) • z) (Finset.sum_congr rfl fun T hT => ?_)
    rw [(hlam T hT).2, smul_comm]

end lin

/-! ## Exchanging two adjacent inputs -/

section swap

variable {a a' : α}

omit [Invertible (2 : R)] in
/-- **The exchange of two adjacent inputs preserves the order of every other pair.** -/
lemma swap_lt_swap_iff (haa : a < a') (hadj : ∀ z, ¬ (a < z ∧ z < a')) {x y : α}
    (h1 : ¬ (x = a' ∧ y = a)) (h2 : ¬ (x = a ∧ y = a')) :
    Equiv.swap a a' y < Equiv.swap a a' x ↔ y < x := by
  have hne : a ≠ a' := haa.ne
  have key : ∀ z, z ≠ a → z ≠ a' → ((z < a ↔ z < a') ∧ (a < z ↔ a' < z)) := by
    intro z hza hza'
    have := hadj z
    constructor <;> constructor <;> intro h
    · exact h.trans haa
    · rcases lt_trichotomy z a with h' | h' | h'
      · exact h'
      · exact absurd h' hza
      · exact absurd ⟨h', h⟩ this
    · rcases lt_trichotomy z a' with h' | h' | h'
      · exact absurd ⟨h, h'⟩ this
      · exact absurd h' hza'
      · exact h'
    · exact haa.trans h
  by_cases hxa : x = a
  · subst hxa
    have hy : y ≠ a' := fun e => h2 ⟨rfl, e⟩
    rw [Equiv.swap_apply_left]
    by_cases hya : y = x
    · subst hya
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne hya hy]
      exact ((key y hya hy).1).symm
  · by_cases hxa' : x = a'
    · subst hxa'
      have hy : y ≠ a := fun e => h1 ⟨rfl, e⟩
      rw [Equiv.swap_apply_right]
      by_cases hya : y = x
      · subst hya
        simp
      · rw [Equiv.swap_apply_of_ne_of_ne hy hya]
        exact (key y hy hya).1
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxa']
      by_cases hya : y = a
      · subst hya
        rw [Equiv.swap_apply_left]
        exact ((key x hxa hxa').2).symm
      · by_cases hya' : y = a'
        · subst hya'
          rw [Equiv.swap_apply_right]
          exact (key x hxa hxa').2
        · rw [Equiv.swap_apply_of_ne_of_ne hya hya']

omit [Invertible (2 : R)] in
lemma prod_ite_pair {N : Type*} [CommMonoid N] (T U : Finset α) (x₀ y₀ : α) (c : N) :
    ∏ x ∈ T, ∏ y ∈ U, (if x = x₀ ∧ y = y₀ then c else 1)
      = if x₀ ∈ T ∧ y₀ ∈ U then c else 1 := by
  classical
  have h1 : ∀ x, ∏ y ∈ U, (if x = x₀ ∧ y = y₀ then c else 1)
      = if x = x₀ then (if y₀ ∈ U then c else 1) else 1 := by
    intro x
    by_cases hx : x = x₀
    · simp only [hx, true_and, if_true]
      exact Finset.prod_ite_eq' U y₀ fun _ => c
    · simp [hx]
  rw [Finset.prod_congr rfl fun x _ => h1 x, Finset.prod_ite_eq' T x₀ fun _ => _]
  by_cases h₀ : x₀ ∈ T <;> by_cases h₁ : y₀ ∈ U <;> simp [h₀, h₁]

omit [Invertible (2 : R)] in
/-- **Signs of unshuffles after exchanging two adjacent inputs**: they change exactly when the
two inputs are on different sides. -/
lemma ks_swap (haa : a < a') (hadj : ∀ z, ¬ (a < z ∧ z < a')) (p : α → Bool)
    (T U : Finset α) :
    ks R (p ∘ Equiv.swap a a') T U
      = ks R p (T.map (Equiv.swap a a').toEmbedding) (U.map (Equiv.swap a a').toEmbedding) *
        ((if a' ∈ T ∧ a ∈ U then σ R (p a && p a') else 1) *
          (if a ∈ T ∧ a' ∈ U then σ R (p a && p a') else 1)) := by
  unfold ks
  rw [Finset.prod_map]
  simp_rw [Finset.prod_filter, Finset.prod_map]
  rw [← prod_ite_pair T U a' a, ← prod_ite_pair T U a a', ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y hy => ?_
  simp only [Function.comp_apply, Equiv.coe_toEmbedding]
  by_cases h1 : x = a' ∧ y = a
  · obtain ⟨hx1, hy1⟩ := h1
    rw [hx1, hy1, Equiv.swap_apply_left, Equiv.swap_apply_right, if_pos haa,
      if_neg (lt_asymm haa), if_pos ⟨rfl, rfl⟩, if_neg (fun h => haa.ne' h.1)]
    simp only [one_mul, mul_one]
  · by_cases h2 : x = a ∧ y = a'
    · obtain ⟨hx1, hy1⟩ := h2
      rw [hx1, hy1, Equiv.swap_apply_left, Equiv.swap_apply_right, if_neg (lt_asymm haa),
        if_pos haa, if_neg (fun h => haa.ne h.1), if_pos ⟨rfl, rfl⟩, Bool.and_comm (p a')]
      simp only [one_mul]
      rw [LInf.σ_mul_self]
    · have hiff := swap_lt_swap_iff haa hadj h1 h2
      rw [if_neg h1, if_neg h2, mul_one, mul_one]
      by_cases hlt : y < x
      · rw [if_pos hlt, if_pos (hiff.2 hlt)]
      · rw [if_neg hlt, if_neg (mt hiff.1 hlt)]

/-- The sign picked up by a tree on `S` when the inputs `a` and `a'` are exchanged. -/
def cs (p : α → Bool) (a a' : α) (S : Finset α) : R :=
  if a ∈ S ∧ a' ∈ S then σ R (p a && p a') else 1

omit [Invertible (2 : R)] in
lemma cs_split (p : α → Bool) {S T : Finset α} (hTS : T ⊆ S) :
    ((if a' ∈ T ∧ a ∈ S \ T then σ R (p a && p a') else 1) *
        (if a ∈ T ∧ a' ∈ S \ T then σ R (p a && p a') else 1)) *
      (cs p a a' T * cs p a a' (S \ T)) = cs p a a' S := by
  unfold cs
  have h1 := @hTS a
  have h2 := @hTS a'
  by_cases ha : a ∈ T <;> by_cases ha' : a' ∈ T <;> by_cases hb : a ∈ S <;>
    by_cases hb' : a' ∈ S <;> simp_all

omit [Invertible (2 : R)] in
lemma cs_of_card_le_one (p : α → Bool) (hne : a ≠ a') {S : Finset α} (hS : S.card ≤ 1) :
    cs (R := R) p a a' S = 1 := by
  unfold cs
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact hne (Finset.card_le_one.1 hS a h1 a' h2)

omit [Invertible (2 : R)] in
/-- Splittings of the image of a set under an embedding. -/
lemma splits_map_emb {β : Type*} [LinearOrder β] (f : α ↪ β) (S : Finset α) :
    splits (S.map f)
      = (splits S).map ⟨fun T => T.map f, fun _ _ h => Finset.map_injective _ h⟩ := by
  ext T'
  rw [Finset.mem_map, mem_splits]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨T, hT, rfl⟩ := Finset.subset_map_iff.1 h1
    refine ⟨T, mem_splits.2 ⟨hT, ?_, fun e => h3 (by rw [e])⟩, rfl⟩
    exact Finset.map_nonempty.1 h2
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨h1, h2, h3⟩ := mem_splits.1 hT
    exact ⟨Finset.map_subset_map.2 h1, Finset.map_nonempty.2 h2,
      fun e => h3 (Finset.map_injective _ e)⟩

/-- **Exchanging two adjacent inputs multiplies a tree by their Koszul sign**, when both are
inputs of the tree. -/
theorem tree_swap (haa : a < a') (hadj : ∀ z, ¬ (a < z ∧ z < a')) :
    ∀ (n : ℕ) (S : Finset α), S.card = n →
      tree μ e h (p ∘ Equiv.swap a a') (v ∘ Equiv.swap a a') S
        = cs (R := R) p a a' S • tree μ e h p v (S.map (Equiv.swap a a').toEmbedding) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn
    by_cases hS : S.card ≤ 1
    · rw [tree_of_card_le_one μ e h _ _ hS,
        tree_of_card_le_one μ e h _ _ (by rw [Finset.card_map]; exact hS), Finset.sum_map,
        cs_of_card_le_one (R := R) p haa.ne hS, one_smul]
      rfl
    · rw [tree_of_one_lt μ e h _ _ (by omega),
        tree_of_one_lt μ e h _ _ (by rw [Finset.card_map]; omega), ← map_smul]
      congr 1
      unfold lam
      rw [smul_comm (cs (R := R) p a a' S) (⅟2 : R), splits_map_emb, Finset.sum_map]
      congr 1
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hTS := (mem_splits.1 hT).1
      simp only [Function.Embedding.coeFn_mk]
      rw [ks_swap haa hadj, ih _ (hn ▸ card_lt_of_mem_splits hT) T rfl,
        ih _ (hn ▸ card_sdiff_lt_of_mem_splits hT) (S \ T) rfl, HTT.mu_smul_left,
        HTT.mu_smul_right, smul_smul, smul_smul, smul_smul, ← Finset.map_sdiff,
        ← cs_split p hTS]
      congr 1
      ring

/-- **Exchanging two adjacent inputs multiplies the brackets of the trees by their Koszul
sign.** -/
theorem lam_swap (haa : a < a') (hadj : ∀ z, ¬ (a < z ∧ z < a')) (S : Finset α) :
    lam μ e h (p ∘ Equiv.swap a a') (v ∘ Equiv.swap a a') S
      = cs (R := R) p a a' S • lam μ e h p v (S.map (Equiv.swap a a').toEmbedding) := by
  unfold lam
  rw [smul_comm (cs (R := R) p a a' S) (⅟2 : R), splits_map_emb, Finset.sum_map]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTS := (mem_splits.1 hT).1
  simp only [Function.Embedding.coeFn_mk]
  rw [ks_swap haa hadj, tree_swap μ e h p v haa hadj _ T rfl,
    tree_swap μ e h p v haa hadj _ (S \ T) rfl, HTT.mu_smul_left,
    HTT.mu_smul_right, smul_smul, smul_smul, smul_smul, ← Finset.map_sdiff,
    ← cs_split p hTS]
  congr 1
  ring

end swap

end LInfT

end Operad
