/-
# Homotopy transfer of C∞-structures

A dg algebra in the bar convention is a C∞-algebra when its product is commutative,
`μ(x, y) + σ(|x| |y|) μ(y, x) = 0` (`CInf.isCInf_dga_iff`). The transferred A∞-structure of
`HTT.transfer` is then a C∞-structure (`CInfT.isCInf_transfer`).

* **Evaluation at positions.** A family of operations becomes a series (`CInfT.toSer`), evaluated
  on any finite set of positions (`LSer.ev`), and a shuffle sum is a sum over the subsets of a set
  of positions (`ShSplit.shf`).
* **The product of two families at positions** is the sum over the cuts of the positions into an
  initial segment and the rest (`CInfT.ev_BIN`). By `ShSplit.shf_cut`, the shuffle sum of each
  cut is a product of shuffle sums of the two sides.
* **Vanishing on shuffles** (`CInfT.VanAt`) passes from the trees of smaller arities to the
  trees and the transferred operations of the next arity: of the shuffle sums of the two sides,
  only those with all letters of one word survive, and the two surviving terms cancel by
  commutativity (`CInfT.shf_ev_BIN`).
-/
import Operad.ShuffleSplit
import Operad.LInfSeries

universe u v

namespace Operad

namespace CInfT

open GerBV KS ShSplit LSer AInf End

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {α : Type*} [LinearOrder α]

/-! ## Families as series -/

/-- **A family of operations as a series**, with nothing in arity zero. -/
def toSer (X : Fam R V) : Ser R V V
  | 0 => 0
  | n + 1 => X n

lemma range_orderEmbOfFin (k : ℕ) {m : ℕ} (h : (Finset.range k).card = m) (j : Fin m) :
    ((Finset.range k).orderEmbOfFin h j : ℕ) = j := by
  have hm : m = k := by rw [← h, Finset.card_range]
  have := Finset.orderEmbOfFin_unique h (f := fun j : Fin m => (j : ℕ))
    (fun j => Finset.mem_range.2 (hm ▸ j.isLt)) (fun a b hab => hab)
  exact (congrFun this j).symm

/-- **A word read along its positions** is the word itself. -/
lemma ev_rank (F : Ser R V V) (S : Finset α) (q : ℕ → V) :
    ev F (fun t => q (rank S t)) S = ev F q (Finset.range S.card) := by
  rw [ev_eq F q _ (Finset.card_range S.card)]
  unfold ev
  congr 1
  funext j
  simp only [Function.comp_apply]
  rw [rank_orderEmbOfFin, range_orderEmbOfFin]

/-- **An even series takes homogeneous inputs to an element of their total parity.** -/
lemma isPar_ev {ε : V →ₗ[R] V} (F : Ser R V V) {S : Finset α} (hF : IsHomog ε 0 (F S.card))
    {w : α → V} {q : α → Bool} (hw : ∀ t ∈ S, IsPar ε (q t) (w t)) :
    IsPar ε (par q S) (ev F w S) := by
  have h1 : ev F (fun t => ε (w t)) S = ε (ev F w S) := by
    unfold ev
    have := hF (w ∘ S.orderEmbOfFin rfl)
    rw [pow_zero, one_smul] at this
    exact this
  have h2 : ev F (fun t => ε (w t)) S = ev F (fun t => σ R (q t) • w t) S :=
    ev_congr F fun t ht => hw t ht
  unfold IsPar
  rw [← h1, h2, ev_smul, σ_par]

/-! ## Shuffle sums -/

section shf

omit [AddCommGroup V] [Module R V]

variable {W W' : Type*} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']

lemma shf_congr {Φ Ψ : (α → V) → Finset α → W} {M : Finset α} (h : ∀ w, Φ w M = Ψ w M)
    (A : ℕ) (x y : ℕ → V) (px py : ℕ → Bool) :
    shf R Φ M A x y px py = shf R Ψ M A x y px py := by
  unfold shf
  simp only [h]

lemma shf_map (f : W →ₗ[R] W') (Φ : (α → V) → Finset α → W) (M : Finset α) (A : ℕ)
    (x y : ℕ → V) (px py : ℕ → Bool) :
    shf R (fun w S => f (Φ w S)) M A x y px py = f (shf R Φ M A x y px py) := by
  unfold shf
  simp only [map_sum, map_smul]

lemma shf_sum {ι : Type*} (s : Finset ι) (Φ : ι → (α → V) → Finset α → W) (M : Finset α)
    (A : ℕ) (x y : ℕ → V) (px py : ℕ → Bool) :
    shf R (fun w S => ∑ k ∈ s, Φ k w S) M A x y px py
      = ∑ k ∈ s, shf R (Φ k) M A x y px py := by
  unfold shf
  simp only [Finset.smul_sum]
  exact Finset.sum_comm

end shf

/-- **The shuffle sum with no letter of `x`** is the evaluation on `y`. -/
lemma shf_zero (F : Ser R V V) (S : Finset α) (x y : ℕ → V) (px py : ℕ → Bool) :
    shf R (ev F) S 0 x y px py = ev F y (Finset.range S.card) := by
  classical
  unfold shf
  rw [Finset.powersetCard_zero, Finset.sum_singleton, ks_empty_left, one_smul, ← ev_rank]
  refine ev_congr F fun t _ => ?_
  simp [mergeA]

/-- **The shuffle sum with only letters of `x`** is the evaluation on `x`. -/
lemma shf_card (F : Ser R V V) (S : Finset α) (x y : ℕ → V) (px py : ℕ → Bool) :
    shf R (ev F) S S.card x y px py = ev F x (Finset.range S.card) := by
  classical
  unfold shf
  rw [Finset.powersetCard_self, Finset.sum_singleton, Finset.sdiff_self, ks_empty_right, one_smul,
    ← ev_rank]
  refine ev_congr F fun t ht => ?_
  simp [mergeA, ht]

variable (ε : V →ₗ[R] V)

variable (α) in
/-- **Vanishing on shuffles in arity `n`**: the shuffle sums of an evaluation on sets of `n`
positions vanish for homogeneous words, with letters of both words. -/
def VanAt (F : Ser R V V) (n : ℕ) : Prop :=
  ∀ (M : Finset α), M.card = n → ∀ (A : ℕ) (x y : ℕ → V) (px py : ℕ → Bool),
    (∀ k, IsPar ε (px k) (x k)) → (∀ k, IsPar ε (py k) (y k)) → 0 < A → A < n →
    shf R (ev F) M A x y px py = 0

/-- **The shuffle sums of a series vanishing on shuffles**: only the two words themselves. -/
lemma shf_trich {F : Ser R V V} {S : Finset α} (hF : VanAt α ε F S.card) (A : ℕ) (x y : ℕ → V)
    (px py : ℕ → Bool) (hx : ∀ k, IsPar ε (px k) (x k)) (hy : ∀ k, IsPar ε (py k) (y k)) :
    shf R (ev F) S A x y px py = if A = 0 then ev F y (Finset.range S.card)
      else if A = S.card then ev F x (Finset.range S.card) else 0 := by
  split_ifs with h0 h1
  · rw [h0, shf_zero]
  · rw [h1, shf_card]
  · rcases lt_or_gt_of_ne h1 with h | h
    · exact hF S rfl A x y px py hx hy (Nat.pos_of_ne_zero h0) h
    · unfold shf
      rw [Finset.powersetCard_eq_empty.2 h, Finset.sum_empty]

/-! ## Cuts -/

/-- **The first `j` positions of `M`.** -/
def cut (M : Finset α) (j : ℕ) : Finset α := M.filter fun t => rank M t < j

lemma isDown_cut (M : Finset α) (j : ℕ) : IsDown (cut M j) M :=
  ⟨Finset.filter_subset _ _, fun _ ht _ hs hst =>
    Finset.mem_filter.2 ⟨hs, (rank_lt_of_lt hs hst).trans (Finset.mem_filter.1 ht).2⟩⟩

lemma card_cut (M : Finset α) {j : ℕ} (hj : j ≤ M.card) : (cut M j).card = j := by
  suffices (cut M j).card = (Finset.range j).card by rwa [Finset.card_range] at this
  refine Finset.card_bij (fun t _ => rank M t)
    (fun t ht => Finset.mem_range.2 (Finset.mem_filter.1 ht).2) ?_ ?_
  · intro s hs t ht hst
    have hs' := (Finset.mem_filter.1 hs).1
    have ht' := (Finset.mem_filter.1 ht).1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (rank_lt_of_lt hs' h).ne hst
    · exact (rank_lt_of_lt ht' h).ne hst.symm
  · intro n hn
    rw [Finset.mem_range] at hn
    refine ⟨M.orderEmbOfFin rfl ⟨n, by omega⟩,
      Finset.mem_filter.2 ⟨Finset.orderEmbOfFin_mem _ _ _, ?_⟩, ?_⟩
    · rw [rank_orderEmbOfFin]
      exact hn
    · exact rank_orderEmbOfFin M rfl _

lemma cut_emb (M : Finset α) {N j : ℕ} (hN : M.card = N) (hj : j ≤ N) (h : (cut M j).card = j)
    (i : Fin j) : (cut M j).orderEmbOfFin h i = M.orderEmbOfFin hN (Fin.castLE hj i) := by
  have := Finset.orderEmbOfFin_unique h (f := fun i => M.orderEmbOfFin hN (Fin.castLE hj i))
    (fun i => Finset.mem_filter.2 ⟨Finset.orderEmbOfFin_mem _ _ _, by
      rw [rank_orderEmbOfFin]
      exact i.isLt⟩)
    (fun a b hab => (M.orderEmbOfFin hN).strictMono
      (show Fin.castLE hj a < Fin.castLE hj b from hab))
  exact (congrFun this i).symm

lemma rest_emb (M : Finset α) {N j m : ℕ} (hN : M.card = N) (hjm : j + m = N)
    (h : (M \ cut M j).card = m) (i : Fin m) :
    (M \ cut M j).orderEmbOfFin h i = M.orderEmbOfFin hN ⟨j + i, by have := i.isLt; omega⟩ := by
  have := Finset.orderEmbOfFin_unique h
    (f := fun i : Fin m => M.orderEmbOfFin hN ⟨j + i, by have := i.isLt; omega⟩)
    (fun i => Finset.mem_sdiff.2 ⟨Finset.orderEmbOfFin_mem _ _ _, fun hc => by
      have := (Finset.mem_filter.1 hc).2
      rw [rank_orderEmbOfFin] at this
      simp at this⟩)
    (fun a b hab => (M.orderEmbOfFin hN).strictMono (Fin.mk_lt_mk.2 (Nat.add_lt_add_left hab j)))
  exact (congrFun this i).symm

/-- **The product of two families at positions** is the sum over the cuts of the positions. -/
lemma ev_BIN (μ : End R V 2) (X Y : Fam R V) (w : α → V) {M : Finset α} {n : ℕ}
    (hM : M.card = n + 1) :
    ev (toSer (HTT.BIN μ X Y)) w M = ∑ k ∈ Finset.range n,
      μ ![ev (toSer X) w (cut M (k + 1)), ev (toSer Y) w (M \ cut M (k + 1))] := by
  rw [ev_eq _ w M hM]
  change HTT.BIN μ X Y n (w ∘ M.orderEmbOfFin hM) = _
  rw [HTT.BIN_apply, MultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have h1 : k + 1 + (n - 1 - k + 1) = n + 1 := by omega
  rw [acast_of_eq h1, reindex_apply, HTT.bin_apply]
  have hc1 : (cut M (k + 1)).card = k + 1 := card_cut M (by omega)
  have hc2 : (M \ cut M (k + 1)).card = n - 1 - k + 1 := by
    rw [Finset.card_sdiff_of_subset (isDown_cut M _).1, hc1, hM]
    omega
  rw [ev_eq _ w _ hc1, ev_eq _ w _ hc2]
  have e1 : (X k fun i => (w ∘ M.orderEmbOfFin hM) (Fin.cast h1 (Fin.castAdd _ i)))
      = toSer X (k + 1) (w ∘ (cut M (k + 1)).orderEmbOfFin hc1) := by
    change X k _ = X k _
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [cut_emb M hM (by omega) hc1]
    rfl
  have e2 : (Y (n - 1 - k) fun j => (w ∘ M.orderEmbOfFin hM) (Fin.cast h1 (Fin.natAdd _ j)))
      = toSer Y (n - 1 - k + 1) (w ∘ (M \ cut M (k + 1)).orderEmbOfFin hc2) := by
    change Y (n - 1 - k) _ = Y (n - 1 - k) _
    congr 1
    funext j
    simp only [Function.comp_apply]
    rw [rest_emb M hM (by omega) hc2]
    rfl
  rw [e1, e2]

/-! ## The shuffle sums of a product -/

omit [LinearOrder α] in
lemma shift_zero {X : Type*} (x : ℕ → X) : shift x 0 = x :=
  funext fun n => by simp [shift]

omit [LinearOrder α] in
/-- The sum over the number of letters of `x` before the cut, when only the ends survive. -/
lemma sum_ends (μ : End R V 2) {p q A : ℕ} (hp : 0 < p) (hA0 : 0 < A) (hA : A < p + q)
    (s : ℕ → R) (a b : V) (G0 Gq : ℕ → V) :
    ∑ i ∈ Finset.range (A + 1), s i • μ ![if i = 0 then a else if i = p then b else 0,
        if A - i = 0 then G0 i else if A - i = q then Gq i else 0]
      = (if p = A then s p • μ ![b, G0 p] else 0) + (if q = A then s 0 • μ ![a, Gq 0] else 0) := by
  have z1 : ∀ c, μ ![0, c] = 0 := fun c => μ.map_coord_zero (0 : Fin 2) rfl
  have z2 : ∀ c, μ ![c, 0] = 0 := fun c => μ.map_coord_zero (1 : Fin 2) rfl
  have f0 : s 0 • μ ![if (0 : ℕ) = 0 then a else if (0 : ℕ) = p then b else 0,
      if A - 0 = 0 then G0 0 else if A - 0 = q then Gq 0 else 0]
      = if q = A then s 0 • μ ![a, Gq 0] else 0 := by
    rw [if_pos rfl, Nat.sub_zero, if_neg hA0.ne']
    by_cases hq : q = A
    · rw [if_pos hq.symm, if_pos hq]
    · rw [if_neg (Ne.symm hq), if_neg hq, z2, smul_zero]
  have hrest : ∀ i ∈ Finset.range (A + 1), i ≠ 0 ∧ i ≠ p →
      s i • μ ![if i = 0 then a else if i = p then b else 0,
        if A - i = 0 then G0 i else if A - i = q then Gq i else 0] = 0 := by
    intro i _ hi
    rw [if_neg hi.1, if_neg hi.2, z1, smul_zero]
  rcases Nat.lt_or_ge A p with hlt | hge
  · rw [Finset.sum_eq_single 0 (fun i hi hi0 => hrest i hi ⟨hi0, by
      rw [Finset.mem_range] at hi
      omega⟩) (fun h => absurd (Finset.mem_range.2 (by omega)) h), f0, if_neg (show p ≠ A by omega),
      zero_add]
  · rw [Finset.sum_eq_add 0 p hp.ne hrest (fun h => absurd (Finset.mem_range.2 (by omega)) h)
      (fun h => absurd (Finset.mem_range.2 (by omega)) h), f0, add_comm]
    congr 1
    rw [if_neg hp.ne']
    by_cases hpA : p = A
    · rw [if_pos rfl, if_pos (by omega), if_pos hpA]
    · rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg hpA, z2, smul_zero]

/-- **The shuffle sums of a product of two families vanishing on shuffles in lower arities**: of
the cuts, only those with all letters of one word on each side survive. -/
theorem shf_ev_BIN (μ : End R V 2) (X Y : Fam R V) {n : ℕ}
    (hX : ∀ k < n, VanAt α ε (toSer X) (k + 1)) (hY : ∀ k < n, VanAt α ε (toSer Y) (k + 1))
    {M : Finset α} (hM : M.card = n + 1) {A : ℕ} (hA0 : 0 < A) (hA : A < n + 1) (x y : ℕ → V)
    (px py : ℕ → Bool) (hx : ∀ k, IsPar ε (px k) (x k)) (hy : ∀ k, IsPar ε (py k) (y k)) :
    shf R (ev (toSer (HTT.BIN μ X Y))) M A x y px py
      = μ ![ev (toSer X) x (Finset.range A), ev (toSer Y) y (Finset.range (n + 1 - A))]
        + σ R (par px (Finset.range A) && par py (Finset.range (n + 1 - A))) •
          μ ![ev (toSer X) y (Finset.range (n + 1 - A)), ev (toSer Y) x (Finset.range A)] := by
  classical
  rw [shf_congr (Ψ := fun w _ => ∑ k ∈ Finset.range n,
      μ ![ev (toSer X) w (cut M (k + 1)), ev (toSer Y) w (M \ cut M (k + 1))])
    (fun w => ev_BIN μ X Y w hM), shf_sum]
  set C1 := μ ![ev (toSer X) x (Finset.range A), ev (toSer Y) y (Finset.range (n + 1 - A))]
  set C2 := σ R (par px (Finset.range A) && par py (Finset.range (n + 1 - A))) •
    μ ![ev (toSer X) y (Finset.range (n + 1 - A)), ev (toSer Y) x (Finset.range A)]
  have key : ∀ k ∈ Finset.range n,
      shf R (fun w _ => μ ![ev (toSer X) w (cut M (k + 1)), ev (toSer Y) w (M \ cut M (k + 1))])
        M A x y px py = (if k + 1 = A then C1 else 0) + (if n - k = A then C2 else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [shf_cut μ (ev (toSer X)) (ev (toSer Y)) (fun w w' S h => ev_congr _ h)
      (fun w w' S h => ev_congr _ h)
      (isDown_cut M (k + 1))]
    have hP : (cut M (k + 1)).card = k + 1 := card_cut M (by omega)
    have hQ : (M \ cut M (k + 1)).card = n - k := by
      rw [Finset.card_sdiff_of_subset (isDown_cut M _).1, hP, hM]
      omega
    have vP : VanAt α ε (toSer X) (cut M (k + 1)).card := by
      rw [hP]
      exact hX k hk
    have vQ : VanAt α ε (toSer Y) (M \ cut M (k + 1)).card := by
      rw [hQ, show n - k = n - 1 - k + 1 by omega]
      exact hY _ (by omega)
    have tP : ∀ i, shf R (ev (toSer X)) (cut M (k + 1)) i x y px py
        = if i = 0 then ev (toSer X) y (Finset.range (k + 1))
          else if i = k + 1 then ev (toSer X) x (Finset.range (k + 1)) else 0 := fun i => by
      rw [shf_trich ε vP i x y px py hx hy, hP]
    have tQ : ∀ i j B, shf R (ev (toSer Y)) (M \ cut M (k + 1)) B (shift x i) (shift y j)
        (shift px i) (shift py j)
        = if B = 0 then ev (toSer Y) (shift y j) (Finset.range (n - k))
          else if B = n - k then ev (toSer Y) (shift x i) (Finset.range (n - k)) else 0 :=
      fun i j B => by
        rw [shf_trich ε vQ B (shift x i) (shift y j) (shift px i) (shift py j)
          (fun m => hx (i + m)) (fun m => hy (j + m)), hQ]
    simp only [tP, tQ, hP]
    rw [sum_ends μ (q := n - k) (Nat.succ_pos k) hA0 (by omega)]
    congr 1
    · by_cases h1 : k + 1 = A
      · rw [if_pos h1, if_pos h1]
        obtain rfl := h1
        simp only [Nat.sub_self, Finset.range_zero, par_empty, Bool.false_and, σ_false, one_smul,
          shift_zero, C1]
        rw [show n + 1 - (k + 1) = n - k by omega]
      · rw [if_neg h1, if_neg h1]
    · by_cases h2 : n - k = A
      · rw [if_pos h2, if_pos h2]
        obtain rfl := h2
        simp only [Nat.sub_zero, shift_zero, C2]
        rw [show n + 1 - (n - k) = k + 1 by omega]
      · rw [if_neg h2, if_neg h2]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib,
    Finset.sum_eq_single (A - 1) (fun k _ hk => if_neg (by omega))
      (fun h => absurd (Finset.mem_range.2 (by omega)) h),
    Finset.sum_eq_single (n - A) (fun k hk hk' => if_neg (by rw [Finset.mem_range] at hk; omega))
      (fun h => absurd (Finset.mem_range.2 (by omega)) h),
    if_pos (by omega), if_pos (by omega)]

/-! ## The transferred structure of a commutative dg algebra -/

section Transfer

variable {ε} {μ : End R V 2} {e h : V →ₗ[R] V}

omit [LinearOrder α] in
lemma toSer_even {Y : Fam R V} (hY : ∀ k, IsHomog ε 0 (Y k)) (m : ℕ) :
    IsHomog ε 0 (toSer Y m) := by
  rcases m with _ | m
  · intro v
    change (0 : V) = _ • ε 0
    rw [map_zero, smul_zero]
  · exact hY m

/-- **The shuffle sums of the product of an even family with itself vanish**, for a commutative
product, when they vanish in lower arities. -/
lemma shf_BIN_self (hcomm : ∀ (x y : V) (px py : Bool), IsPar ε px x → IsPar ε py y →
      μ ![x, y] + σ R (px && py) • μ ![y, x] = 0)
    {Y : Fam R V} (hYe : ∀ k, IsHomog ε 0 (Y k)) {n : ℕ}
    (hY : ∀ k < n, VanAt α ε (toSer Y) (k + 1)) {M : Finset α} (hM : M.card = n + 1) {A : ℕ}
    (hA0 : 0 < A) (hA : A < n + 1) (x y : ℕ → V) (px py : ℕ → Bool)
    (hx : ∀ k, IsPar ε (px k) (x k)) (hy : ∀ k, IsPar ε (py k) (y k)) :
    shf R (ev (toSer (HTT.BIN μ Y Y))) M A x y px py = 0 := by
  rw [shf_ev_BIN ε μ Y Y hY hY hM hA0 hA x y px py hx hy]
  exact hcomm _ _ _ _ (isPar_ev _ (toSer_even hYe _) fun t _ => hx t)
    (isPar_ev _ (toSer_even hYe _) fun t _ => hy t)

lemma ev_tf_succ (w : α → V) {M : Finset α} {n : ℕ} (hM : M.card = n + 1 + 1) :
    ev (toSer (HTT.tf μ e h)) w M
      = h (ev (toSer (HTT.BIN μ (HTT.tf μ e h) (HTT.tf μ e h))) w M) := by
  rw [ev_eq _ w M hM, ev_eq _ w M hM]
  change HTT.tf μ e h (n + 1) _ = h (HTT.BIN μ _ _ (n + 1) _)
  rw [HTT.tf_succ]
  rfl

lemma ev_transfer_succ (d : V →ₗ[R] V) (w : α → V) {M : Finset α} {n : ℕ}
    (hM : M.card = n + 1 + 1) :
    ev (toSer (HTT.transfer μ e h d)) w M
      = e (ev (toSer (HTT.BIN μ (HTT.tf μ e h) (HTT.tf μ e h))) w M) := by
  rw [ev_eq _ w M hM, ev_eq _ w M hM]
  rfl

variable (hcomm : ∀ (x y : V) (px py : Bool), IsPar ε px x → IsPar ε py y →
  μ ![x, y] + σ R (px && py) • μ ![y, x] = 0) (htf : ∀ k, IsHomog ε 0 (HTT.tf μ e h k))

include hcomm htf in
/-- **The trees vanish on shuffles.** -/
theorem vanAt_tf (n : ℕ) : VanAt α ε (toSer (HTT.tf μ e h)) (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hM A x y px py hx hy hA0 hA
  rcases n with _ | n
  · omega
  · rw [shf_congr (Ψ := fun w S => h (ev (toSer (HTT.BIN μ (HTT.tf μ e h) (HTT.tf μ e h))) w S))
      (fun w => ev_tf_succ w hM), shf_map,
      shf_BIN_self hcomm htf (fun k hk => ih k hk) hM hA0 hA x y px py hx hy, map_zero]

include hcomm htf in
/-- **The transferred operations vanish on shuffles.** -/
theorem vanAt_transfer (d : V →ₗ[R] V) (n : ℕ) :
    VanAt α ε (toSer (HTT.transfer μ e h d)) (n + 1 + 1) := by
  intro M hM A x y px py hx hy hA0 hA
  rw [shf_congr (Ψ := fun w S => e (ev (toSer (HTT.BIN μ (HTT.tf μ e h) (HTT.tf μ e h))) w S))
    (fun w => ev_transfer_succ d w hM), shf_map,
    shf_BIN_self hcomm htf (fun k _ => vanAt_tf hcomm htf k) hM hA0 hA x y px py hx hy, map_zero]

end Transfer

omit [AddCommGroup V] [Module R V] in
lemma usgn_eq_ks {N : ℕ} (p : Fin N → Bool) (S : Finset (Fin N)) :
    (LInf.usgn p S : R) = ks R p S (Finset.univ \ S) := by
  unfold LInf.usgn ks
  rw [Finset.compl_eq_univ_sdiff]

lemma univ_orderEmbOfFin {N m : ℕ} (h : (Finset.univ : Finset (Fin N)).card = m) (j : Fin m) :
    (Finset.univ : Finset (Fin N)).orderEmbOfFin h j = Fin.cast (by simpa using h.symm) j := by
  have := Finset.orderEmbOfFin_unique h (f := Fin.cast (by simpa using h.symm))
    (fun _ => Finset.mem_univ _) (fun a b hab => hab)
  exact (congrFun this j).symm

/-- **Homotopy transfer of C∞-structures**: the transferred A∞-structure of a dg algebra which is
a C∞-algebra, along a retraction, is a C∞-structure. -/
theorem isCInf_transfer {μ : End R V 2} {d e h : V →ₗ[R] V} (hdo : ∀ x, d (ε x) = -ε (d x))
    (hμ : IsHomog ε 1 μ) (hr : HTT.Retract ε d e h) (hC : CInf.IsCInf ε (dga R V (HTT.op1 d) μ)) :
    CInf.IsCInf ε (HTT.transfer μ e h d) := by
  classical
  obtain ⟨hA, hcomm⟩ := (CInf.isCInf_dga_iff ε).1 hC
  have hd1 : IsHomog ε 1 (HTT.op1 d) := fun v => by
    change d (ε (v 0)) = (-1 : R) ^ 1 • ε (d (v 0))
    rw [hdo, pow_one, neg_one_smul]
  obtain ⟨h1, h2, h3⟩ := (isAInf_dga_iff ε hd1 hμ).1 hA
  have hd : HTT.DGA ε d μ := ⟨hdo, hμ, fun x => h1 x, fun x y => h2 x y, h3⟩
  refine ⟨HTT.isAInf_transfer_of_dga hr hdo hμ hA, fun a c x y px py hx hy => ?_⟩
  have hN : (Finset.univ : Finset (Fin (a + 1 + (c + 1)))).card = a + c + 1 + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  have hterm : ∀ (S : Finset (Fin (a + 1 + (c + 1)))) (hS : S.card = a + 1),
      (LInf.usgn (CInf.merge S hS px py) S : R) •
        HTT.transfer μ e h d (a + c + 1) (CInf.merge S hS x y ∘ Fin.cast (by omega))
      = ks R (mergeA S Finset.univ (ext px false) (ext py false)) S (Finset.univ \ S) •
        ev (toSer (HTT.transfer μ e h d)) (mergeA S Finset.univ (ext x 0) (ext y 0))
          Finset.univ := by
    intro S hS
    rw [usgn_eq_ks, merge_eq_mergeA S hS px py false, merge_eq_mergeA S hS x y 0,
      ev_eq _ _ _ hN]
    congr 2
    funext j
    simp only [Function.comp_apply]
    rw [univ_orderEmbOfFin]
  rw [Finset.sum_congr rfl fun S _ => hterm S.1 S.2]
  rw [← Finset.sum_subtype (Finset.univ.powersetCard (a + 1)) (fun S => by
    simp [Finset.mem_powersetCard])
    (fun S => ks R (mergeA S Finset.univ (ext px false) (ext py false)) S (Finset.univ \ S) •
      ev (toSer (HTT.transfer μ e h d)) (mergeA S Finset.univ (ext x 0) (ext y 0)) Finset.univ)]
  have hxe : ∀ k, IsPar ε (ext px false k) (ext x 0 k) := fun k => by
    unfold ext
    split_ifs
    · exact hx _
    · simp [IsPar]
  have hye : ∀ k, IsPar ε (ext py false k) (ext y 0 k) := fun k => by
    unfold ext
    split_ifs
    · exact hy _
    · simp [IsPar]
  exact vanAt_transfer hcomm (HTT.tf_even hd hr) d (a + c) Finset.univ hN (a + 1) _ _ _ _ hxe hye
    (Nat.succ_pos a) (by omega)

end CInfT

end Operad
