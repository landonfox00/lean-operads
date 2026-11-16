/-
# ∞-morphisms of C∞-algebras

An ∞-morphism of C∞-algebras is an ∞-morphism of A∞-algebras (`AInf.IsInfMorph`) whose components
vanish on the signed shuffles of homogeneous words (`CInfM.IsCInfMorph`). The identity is one
(`CInfM.IsCInfMorph.id`), a strict morphism is one exactly when it is an ∞-morphism of
A∞-algebras (`CInfM.isCInfMorph_lin_iff`), and **∞-morphisms of C∞-algebras compose**
(`CInfM.IsCInfMorph.comp`). The trees of the transfer of a dg algebra which is a C∞-algebra
vanish on shuffles (`CInfM.shuffle_tf`).

* **Composites vanish on shuffles** (`CInfM.vanAt_comp`). The composite `g ∘ f` at a set of
  positions is a sum over the compositions of its size (`CInfM.ev_comp`). For each composition,
  the shuffle sum of `g` of the values of `f` on the blocks is a sum over the sets `J` of blocks
  holding only letters of `x`, the other blocks holding only letters of `y` (`CInfM.shf_blocks`,
  by induction on the number of blocks, cutting off the last one with `ShSplit.shf_cut₂`). A
  composition with such a set `J` is a pair of compositions of the two words with a shuffle of
  their blocks (`CInfM.fwd`, `CInfM.bwd`), so the sum is a sum of shuffle sums of `g` on the
  values of `f` on the blocks of the two words, each zero.
* The inner series is even, so the value of `f` on a block has the parity of the block
  (`CInfM.isPar_ev_even`), and the Koszul sign of the letters is that of the blocks
  (`CInfM.par_bpar_compl`).
-/
import Operad.CInfTransfer
import Operad.AInfMorphism

universe u v

namespace Operad

namespace CInfM

open GerBV KS ShSplit LSer CInfT

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {W Z : Type*} [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
  {α : Type*} [LinearOrder α]

/-! ## Cuts of cuts -/

lemma rank_cut (M : Finset α) (a : ℕ) {t : α} (ht : t ∈ cut M a) :
    rank (cut M a) t = rank M t := by
  rw [rank_inter_down (isDown_cut M a) subset_rfl ht,
    Finset.inter_eq_right.2 (isDown_cut M a).1]

lemma cut_cut (M : Finset α) {a b : ℕ} (hab : b ≤ a) : cut (cut M a) b = cut M b := by
  ext t
  constructor
  · intro ht
    have h1 := (Finset.mem_filter.1 ht).1
    have h2 := (Finset.mem_filter.1 ht).2
    rw [rank_cut M a h1] at h2
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, h2⟩
  · intro ht
    obtain ⟨htM, hr⟩ := Finset.mem_filter.1 ht
    have h1 : t ∈ cut M a := Finset.mem_filter.2 ⟨htM, by omega⟩
    exact Finset.mem_filter.2 ⟨h1, by rw [rank_cut M a h1]; exact hr⟩

lemma cut_card_self (M : Finset α) : cut M M.card = M :=
  Finset.filter_true_of_mem fun _ ht => rank_lt_card ht

/-! ## Parities of consecutive letters -/

omit [LinearOrder α] in
lemma par_range_add (q : ℕ → Bool) (a c : ℕ) :
    par q (Finset.range (a + c))
      = xor (par q (Finset.range a)) (par (shift q a) (Finset.range c)) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [← add_assoc, Finset.range_add_one, par_insert q Finset.notMem_range_self, ih,
      Finset.range_add_one, par_insert _ Finset.notMem_range_self]
    simp only [shift]
    cases q (a + c) <;> cases par q (Finset.range a) <;>
      cases par (shift q a) (Finset.range c) <;> rfl

/-! ## Blocks -/

/-- The sum of the first `j` block sizes. -/
def S (b : ℕ → ℕ) (j : ℕ) : ℕ := ∑ k ∈ Finset.range j, b k

/-- **The `j`-th block of `M`** for the block sizes `b`. -/
def blk (M : Finset α) (b : ℕ → ℕ) (j : ℕ) : Finset α := cut M (S b (j + 1)) \ cut M (S b j)

/-- The number of letters of `x` before block `j`: the sizes of the blocks of `J` before `j`. -/
def xb (b : ℕ → ℕ) (J : Finset ℕ) (j : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range j).filter (· ∈ J), b k

/-- The number of letters of `y` before block `j`. -/
def yb (b : ℕ → ℕ) (J : Finset ℕ) (j : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range j).filter (· ∉ J), b k

lemma xb_add_yb (b : ℕ → ℕ) (J : Finset ℕ) (j : ℕ) : xb b J j + yb b J j = S b j :=
  Finset.sum_filter_add_sum_filter_not _ _ _

/-- The value on block `j`: `f` on the letters of `x` if `j ∈ J`, of `y` otherwise. -/
noncomputable def bval (f : Ser R V W) (b : ℕ → ℕ) (x y : ℕ → V) (J : Finset ℕ) (j : ℕ) : W :=
  if j ∈ J then ev f (shift x (xb b J j)) (Finset.range (b j))
  else ev f (shift y (yb b J j)) (Finset.range (b j))

/-- The parity of block `j`. -/
def bpar (b : ℕ → ℕ) (px py : ℕ → Bool) (J : Finset ℕ) (j : ℕ) : Bool :=
  if j ∈ J then par (shift px (xb b J j)) (Finset.range (b j))
  else par (shift py (yb b J j)) (Finset.range (b j))

lemma xb_insert_of_le (b : ℕ → ℕ) (J : Finset ℕ) {ℓ j : ℕ} (hj : j ≤ ℓ) :
    xb b (insert ℓ J) j = xb b J j := by
  unfold xb
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨hk, rfl | h⟩
    · omega
    · exact ⟨hk, h⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, Or.inr h⟩

lemma yb_insert_of_le (b : ℕ → ℕ) (J : Finset ℕ) {ℓ j : ℕ} (hj : j ≤ ℓ) :
    yb b (insert ℓ J) j = yb b J j := by
  unfold yb
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, not_or]
  constructor
  · rintro ⟨hk, -, h⟩
    exact ⟨hk, h⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, by omega, h⟩

lemma xb_of_subset (b : ℕ → ℕ) {J : Finset ℕ} {ℓ : ℕ} (hJ : J ⊆ Finset.range ℓ) :
    xb b J ℓ = ∑ k ∈ J, b k := by
  unfold xb
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.1 (hJ h), h⟩⟩

lemma bval_insert_of_lt (f : Ser R V W) (b : ℕ → ℕ) (x y : ℕ → V) (J : Finset ℕ) {ℓ j : ℕ}
    (hj : j < ℓ) : bval f b x y (insert ℓ J) j = bval f b x y J j := by
  unfold bval
  rw [xb_insert_of_le b J hj.le, yb_insert_of_le b J hj.le]
  simp only [Finset.mem_insert, hj.ne, false_or]

lemma bpar_insert_of_lt (b : ℕ → ℕ) (px py : ℕ → Bool) (J : Finset ℕ) {ℓ j : ℕ} (hj : j < ℓ) :
    bpar b px py (insert ℓ J) j = bpar b px py J j := by
  unfold bpar
  rw [xb_insert_of_le b J hj.le, yb_insert_of_le b J hj.le]
  simp only [Finset.mem_insert, hj.ne, false_or]

/-- **The parity of the blocks of `y` before `m`** is that of the letters of `y` before them. -/
lemma par_bpar_compl (b : ℕ → ℕ) (px py : ℕ → Bool) (J : Finset ℕ) (m : ℕ) :
    par (bpar b px py J) ((Finset.range m).filter (· ∉ J)) = par py (Finset.range (yb b J m)) := by
  induction m with
  | zero => simp [yb]
  | succ m ih =>
    by_cases hm : m ∈ J
    · have e : (Finset.range (m + 1)).filter (· ∉ J) = (Finset.range m).filter (· ∉ J) := by
        rw [Finset.range_add_one, Finset.filter_insert, if_neg (not_not.2 hm)]
      have e' : yb b J (m + 1) = yb b J m := by
        unfold yb
        rw [Finset.range_add_one, Finset.filter_insert, if_neg (not_not.2 hm)]
      rw [e, e', ih]
    · have e : (Finset.range (m + 1)).filter (· ∉ J)
          = insert m ((Finset.range m).filter (· ∉ J)) := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hm]
      have e' : yb b J (m + 1) = yb b J m + b m := by
        unfold yb
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hm, Finset.sum_insert
          (fun h => Finset.notMem_range_self (Finset.mem_filter.1 h).1), add_comm]
      rw [e, par_insert _ (fun h => Finset.notMem_range_self (Finset.mem_filter.1 h).1), ih, e',
        par_range_add]
      unfold bpar
      rw [if_neg hm]
      cases par (shift py (yb b J m)) (Finset.range (b m)) <;>
        cases par py (Finset.range (yb b J m)) <;> rfl

/-! ## Shuffle sums over blocks -/

lemma S_succ (b : ℕ → ℕ) (j : ℕ) : S b (j + 1) = S b j + b j := Finset.sum_range_succ b j

lemma S_mono (b : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : S b i ≤ S b j :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

omit [LinearOrder α] in
/-- Regrouping a sum over sizes and sets of a given size. -/
lemma sum_sizes {X : Type*} [AddCommMonoid X] (s : Finset (Finset ℕ)) (g : Finset ℕ → ℕ)
    (A : ℕ) (F : ℕ → Finset ℕ → X) :
    ∑ i ∈ Finset.range (A + 1), ∑ J ∈ s with g J = i, F i J
      = ∑ J ∈ s, if g J ≤ A then F (g J) J else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_fiberwise_of_maps_to (s := s.filter (g · ≤ A))
    (t := Finset.range (A + 1)) (g := g) (fun J hJ => Finset.mem_range.2
      (Nat.lt_succ_of_le (Finset.mem_filter.1 hJ).2))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Finset.filter_filter]
  refine Finset.sum_congr ?_ fun J hJ => ?_
  · ext J
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by omega, h2⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
  · rw [(Finset.mem_filter.1 hJ).2.2]

variable (εV : V →ₗ[R] V)

/-- **The shuffle sums of a multilinear map of the values of `f` on consecutive blocks**, for `f`
vanishing on shuffles: only the choices of blocks of letters of one word survive. -/
theorem shf_blocks {f : Ser R V W} (hf : ∀ n, VanAt α εV f n) {x y : ℕ → V} {px py : ℕ → Bool}
    (hx : ∀ k, IsPar εV (px k) (x k)) (hy : ∀ k, IsPar εV (py k) (y k)) (b : ℕ → ℕ) (ℓ : ℕ)
    (hb : ∀ j < ℓ, 0 < b j) (G : MultilinearMap R (fun _ : Fin ℓ => W) Z) (M : Finset α)
    (hM : M.card = S b ℓ) (A : ℕ) :
    shf R (fun w _ => G fun j => ev f w (blk M b j)) M A x y px py
      = ∑ J ∈ (Finset.range ℓ).powerset with ∑ j ∈ J, b j = A,
        ks R (bpar b px py J) J (Finset.range ℓ \ J) • G fun j => bval f b x y J j := by
  classical
  induction ℓ generalizing M A with
  | zero =>
    have hM0 : M = ∅ := Finset.card_eq_zero.1 (by simp [hM, S])
    subst hM0
    have hG : ∀ v v' : Fin 0 → W, G v = G v' := fun v v' => by
      congr 1
      funext j
      exact j.elim0
    unfold shf
    rw [Finset.range_zero, Finset.powerset_empty, Finset.sum_filter, Finset.sum_singleton,
      Finset.sum_empty]
    rcases Nat.eq_zero_or_pos A with rfl | hA
    · rw [Finset.powersetCard_zero, Finset.sum_singleton, if_pos rfl, ks_empty_left,
        ks_empty_left, hG]
    · rw [Finset.powersetCard_eq_empty.2 (by simpa using hA), Finset.sum_empty,
        if_neg (by omega)]
  | succ ℓ ih =>
    have hSl : S b ℓ ≤ S b (ℓ + 1) := by rw [S_succ]; omega
    set P := cut M (S b ℓ) with hPdef
    have hPc : P.card = S b ℓ := card_cut M (by omega)
    have hQ : M \ P = blk M b ℓ := by
      unfold blk
      rw [← hM, cut_card_self]
    have hQc : (M \ P).card = b ℓ := by
      rw [Finset.card_sdiff_of_subset (isDown_cut M _).1, hPc, hM, S_succ]
      omega
    have hblk : ∀ j : Fin ℓ, blk M b j = blk P b j := fun j => by
      unfold blk
      rw [hPdef, cut_cut M (S_mono b (by omega : (j : ℕ) + 1 ≤ ℓ)),
        cut_cut M (S_mono b (by omega : (j : ℕ) ≤ ℓ))]
    -- peel off the last block
    have hfun : ∀ w : α → V, (G fun j => ev f w (blk M b j))
        = (LinearMap.id : (W →ₗ[R] Z) →ₗ[R] W →ₗ[R] Z)
          (G.curryRight fun j : Fin ℓ => ev f w (blk P b j)) (ev f w (M \ P)) := by
      intro w
      rw [LinearMap.id_apply, MultilinearMap.curryRight_apply]
      congr 1
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_last, Fin.val_last, hQ]
      · simp only [Fin.snoc_castSucc, Fin.val_castSucc, hblk]
    rw [shf_congr (Ψ := fun w _ => (LinearMap.id : (W →ₗ[R] Z) →ₗ[R] W →ₗ[R] Z)
      (G.curryRight fun j : Fin ℓ => ev f w (blk P b j)) (ev f w (M \ P))) fun w => hfun w]
    rw [shf_cut₂ (LinearMap.id : (W →ₗ[R] Z) →ₗ[R] W →ₗ[R] Z)
      (fun w => G.curryRight fun j : Fin ℓ => ev f w (blk P b j))
      (fun w => ev f w (M \ P)) (isDown_cut M (S b ℓ))
      (fun w w' h => congrArg G.curryRight (funext fun j => ev_congr f fun a ha =>
        h a (Finset.mem_filter.1 (Finset.mem_sdiff.1 ha).1).1))
      (fun w w' h => ev_congr f h) A x y px py]
    rw [← hPdef]
    -- the last block, and the blocks before it
    have hlast : ∀ i, shf R (fun w _ => ev f w (M \ P)) (M \ P) (A - i) (shift x i)
        (shift y (P.card - i)) (shift px i) (shift py (P.card - i))
        = if A - i = 0 then ev f (shift y (S b ℓ - i)) (Finset.range (b ℓ))
          else if A - i = b ℓ then ev f (shift x i) (Finset.range (b ℓ)) else 0 := fun i => by
      change shf R (ev f) (M \ P) _ _ _ _ _ = _
      rw [shf_trich εV (hf _) (A - i) (shift x i) (shift y (P.card - i)) (shift px i)
        (shift py (P.card - i)) (fun k => hx (i + k)) (fun k => hy (P.card - i + k)), hQc, hPc]
    have hpre : ∀ i (v : W), (LinearMap.id : (W →ₗ[R] Z) →ₗ[R] W →ₗ[R] Z) (shf R (fun w _ =>
          G.curryRight fun j : Fin ℓ => ev f w (blk P b j)) P i x y px py) v
        = ∑ J ∈ (Finset.range ℓ).powerset with ∑ j ∈ J, b j = i,
          ks R (bpar b px py J) J (Finset.range ℓ \ J) •
            G (Fin.snoc (fun j : Fin ℓ => bval f b x y J j) v) := fun i v => by
      rw [LinearMap.id_apply]
      have e : (shf R (fun w _ => G.curryRight fun j : Fin ℓ => ev f w (blk P b j)) P i x y px py) v
          = shf R (fun w _ => G (Fin.snoc (fun j : Fin ℓ => ev f w (blk P b j)) v)) P i x y
            px py := by
        unfold shf
        rw [LinearMap.sum_apply]
        simp only [LinearMap.smul_apply, MultilinearMap.curryRight_apply]
      rw [e]
      exact ih (fun j hj => hb j (by omega))
        (((LinearMap.id : (W →ₗ[R] Z) →ₗ[R] W →ₗ[R] Z).flip v).compMultilinearMap
          G.curryRight) P hPc i
    simp only [hlast, hpre, Finset.smul_sum]
    simp only [hPc]
    rw [sum_sizes]
    -- the right side, by whether the last block is in `J`
    rw [Finset.sum_filter, Finset.range_add_one,
      Finset.sum_powerset_insert Finset.notMem_range_self, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun J hJ => ?_
    rw [Finset.mem_powerset] at hJ
    have hℓJ : ℓ ∉ J := fun h => Finset.notMem_range_self (hJ h)
    set s := ∑ j ∈ J, b j with hs
    have hbl := hb ℓ (by omega)
    have hins : ∑ j ∈ insert ℓ J, b j = b ℓ + s := Finset.sum_insert hℓJ
    have hxb : xb b J ℓ = s := xb_of_subset b hJ
    have hyb : yb b J ℓ = S b ℓ - s := by
      have := xb_add_yb b J ℓ
      omega
    have hrest : insert ℓ (Finset.range ℓ) \ insert ℓ J = Finset.range ℓ \ J := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_range, not_or]
      constructor
      · rintro ⟨h1 | h1, h2, h3⟩
        · exact absurd h1 h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨Or.inr h1, by omega, h3⟩
    -- `J` without the last block
    have hG0 : (G fun j : Fin (ℓ + 1) => bval f b x y J j)
        = G (Fin.snoc (fun j : Fin ℓ => bval f b x y J j)
          (ev f (shift y (S b ℓ - s)) (Finset.range (b ℓ)))) := by
      congr 1
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last, Fin.val_last]
        unfold bval
        rw [if_neg hℓJ, hyb]
      · rw [Fin.snoc_castSucc, Fin.val_castSucc]
    have hk0 : ks R (bpar b px py J) J (insert ℓ (Finset.range ℓ) \ J)
        = ks R (bpar b px py J) J (Finset.range ℓ \ J) := by
      have e : insert ℓ (Finset.range ℓ) \ J = {ℓ} ∪ (Finset.range ℓ \ J) := by
        rw [Finset.insert_sdiff_of_notMem _ hℓJ, Finset.insert_eq]
      rw [e, ks_union_right _ _ (Finset.disjoint_singleton_left.2 fun h =>
        Finset.notMem_range_self (Finset.mem_sdiff.1 h).1)]
      have : ks R (bpar b px py J) J {ℓ} = 1 := by
        unfold ks
        refine Finset.prod_eq_one fun t ht => Finset.prod_eq_one fun u hu => ?_
        rw [Finset.mem_filter, Finset.mem_singleton] at hu
        have := Finset.mem_range.1 (hJ ht)
        omega
      rw [this, one_mul]
    -- `J` with the last block
    have hG1 : (G fun j : Fin (ℓ + 1) => bval f b x y (insert ℓ J) j)
        = G (Fin.snoc (fun j : Fin ℓ => bval f b x y J j)
          (ev f (shift x s) (Finset.range (b ℓ)))) := by
      congr 1
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last, Fin.val_last]
        unfold bval
        rw [if_pos (Finset.mem_insert_self ℓ J), xb_insert_of_le b J le_rfl, hxb]
      · rw [Fin.snoc_castSucc, Fin.val_castSucc, bval_insert_of_lt f b x y J j.isLt]
    have hk1 : ks R (bpar b px py (insert ℓ J)) (insert ℓ J)
          (insert ℓ (Finset.range ℓ) \ insert ℓ J)
        = σ R (par (shift px s) (Finset.range (b ℓ)) && par py (Finset.range (S b ℓ - s))) *
          ks R (bpar b px py J) J (Finset.range ℓ \ J) := by
      have e : ks R (bpar b px py (insert ℓ J)) (insert ℓ J) (Finset.range ℓ \ J)
          = ks R (bpar b px py (insert ℓ J)) {ℓ} (Finset.range ℓ \ J) *
            ks R (bpar b px py (insert ℓ J)) J (Finset.range ℓ \ J) := by
        rw [Finset.insert_eq]
        exact ks_union_left _ _ (Finset.disjoint_singleton_left.2 hℓJ)
      rw [hrest, e]
      congr 1
      · have hall : (Finset.range ℓ \ J).filter (· < ℓ) = Finset.range ℓ \ J :=
          Finset.filter_true_of_mem fun k hk =>
            Finset.mem_range.1 (Finset.mem_sdiff.1 hk).1
        have hℓ : bpar b px py (insert ℓ J) ℓ = par (shift px s) (Finset.range (b ℓ)) := by
          unfold bpar
          rw [if_pos (Finset.mem_insert_self ℓ J), xb_insert_of_le b J le_rfl, hxb]
        rw [ks_singleton_left, hall, hℓ, ← hyb, ← par_bpar_compl b px py J ℓ,
          ← Finset.sdiff_eq_filter, σ_and_par]
        refine Finset.prod_congr rfl fun k hk => ?_
        rw [bpar_insert_of_lt b px py J (Finset.mem_range.1 (Finset.mem_sdiff.1 hk).1)]
      · refine ks_congr fun k hk => bpar_insert_of_lt b px py J ?_
        rcases Finset.mem_union.1 hk with h | h
        · exact Finset.mem_range.1 (hJ h)
        · exact Finset.mem_range.1 (Finset.mem_sdiff.1 h).1
    rw [hins, hG0, hG1, hk0, hk1]
    by_cases h1 : s = A
    · rw [if_pos h1.le, if_pos h1, if_neg (show ¬(b ℓ + s = A) by omega), add_zero,
        show A - s = 0 by omega, if_pos rfl, Finset.range_zero, par_empty, Bool.false_and,
        σ_false, one_smul]
    · by_cases h2 : b ℓ + s = A
      · rw [if_pos (show s ≤ A by omega), if_neg h1, if_pos h2, zero_add,
          show A - s = b ℓ by omega, if_neg (show ¬(b ℓ = 0) by omega), if_pos rfl, mul_smul]
      · rw [if_neg h1, if_neg h2, add_zero]
        by_cases h3 : s ≤ A
        · rw [if_pos h3, if_neg (show ¬(A - s = 0) by omega),
            if_neg (show ¬(A - s = b ℓ) by omega),
            MultilinearMap.map_coord_zero _ (Fin.last ℓ) (Fin.snoc_last _ _), smul_zero,
            smul_zero]
        · rw [if_neg h3]

/-! ## Compositions as words of block sizes -/

/-- **The block sizes of a composition**, as a word. -/
def cb {n : ℕ} (c : Composition n) (j : ℕ) : ℕ := c.blocks.getD j 0

lemma cb_of_lt {n : ℕ} (c : Composition n) {j : ℕ} (h : j < c.length) :
    cb c j = c.blocksFun ⟨j, h⟩ := by
  unfold cb Composition.blocksFun
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rwa [Composition.blocks_length])]
  rfl

lemma cb_of_le {n : ℕ} (c : Composition n) {j : ℕ} (h : c.length ≤ j) : cb c j = 0 :=
  by
    unfold cb
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rwa [Composition.blocks_length])]
    rfl

lemma cb_pos {n : ℕ} (c : Composition n) {j : ℕ} (h : j < c.length) : 0 < cb c j := by
  rw [cb_of_lt c h]
  exact c.one_le_blocksFun _

lemma S_cb {n : ℕ} (c : Composition n) (j : ℕ) : S (cb c) j = c.sizeUpTo j := by
  induction j with
  | zero => simp [S, Composition.sizeUpTo_zero]
  | succ j ih =>
    rw [S_succ, ih]
    rcases lt_or_ge j c.length with h | h
    · rw [Composition.sizeUpTo_succ c h, cb_of_lt c h]
      rfl
    · rw [cb_of_le c h, add_zero, Composition.sizeUpTo_ofLength_le c _ h,
        Composition.sizeUpTo_ofLength_le c _ (by omega)]

/-- **A composition from a word of positive block sizes.** -/
def ofWord {n : ℕ} (b : ℕ → ℕ) (m : ℕ) (hpos : ∀ k < m, 0 < b k) (hsum : S b m = n) :
    Composition n where
  blocks := List.ofFn fun k : Fin m => b k
  blocks_pos := by
    intro i hi
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hi
    exact hpos k k.isLt
  blocks_sum := by
    rw [List.sum_ofFn, ← hsum, S, Fin.sum_univ_eq_sum_range]

lemma length_ofWord {n : ℕ} (b : ℕ → ℕ) (m : ℕ) (hpos : ∀ k < m, 0 < b k) (hsum : S b m = n) :
    (ofWord b m hpos hsum).length = m := by
  simp [ofWord, Composition.length]

lemma cb_ofWord {n : ℕ} (b : ℕ → ℕ) (m : ℕ) (hpos : ∀ k < m, 0 < b k) (hsum : S b m = n)
    (k : ℕ) : cb (ofWord b m hpos hsum) k = if k < m then b k else 0 := by
  split_ifs with h
  · rw [cb_of_lt _ (by rwa [length_ofWord])]
    simp [Composition.blocksFun, ofWord]
  · exact cb_of_le _ (by rw [length_ofWord]; omega)

lemma ofWord_cb {n : ℕ} (c : Composition n) :
    ofWord (cb c) c.length (fun _ h => cb_pos c h) (by rw [S_cb, Composition.sizeUpTo_length])
      = c := by
  refine Composition.ext (List.ext_getElem (by simp [ofWord, Composition.length]) ?_)
  intro j h1 h2
  have h3 : j < c.length := by simpa [Composition.length] using h2
  simp only [ofWord, List.getElem_ofFn]
  rw [cb_of_lt c h3]
  rfl

/-! ## Subwords along a set of positions -/

/-- The letters of `w` at the positions of `J`, in order. -/
noncomputable def sub (J : Finset ℕ) (w : ℕ → ℕ) : ℕ → ℕ :=
  fun k => if hk : k < J.card then w (J.orderEmbOfFin rfl ⟨k, hk⟩) else 0

lemma emb_rank (J : Finset ℕ) {t : ℕ} (ht : t ∈ J) :
    J.orderEmbOfFin rfl ⟨rank J t, rank_lt_card ht⟩ = t := by
  have h := orderIsoOfFin_symm_val J rfl ht
  have e : (⟨rank J t, rank_lt_card ht⟩ : Fin J.card) = (J.orderIsoOfFin rfl).symm ⟨t, ht⟩ :=
    Fin.ext h.symm
  rw [e, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

lemma sub_rank (J : Finset ℕ) (w : ℕ → ℕ) {t : ℕ} (ht : t ∈ J) : sub J w (rank J t) = w t := by
  unfold sub
  rw [dif_pos (rank_lt_card ht), emb_rank J ht]

lemma sub_of_le (J : Finset ℕ) (w : ℕ → ℕ) {k : ℕ} (hk : J.card ≤ k) : sub J w k = 0 := by
  unfold sub
  rw [dif_neg (by omega)]

lemma mergeA_emb {X : Type*} (J M : Finset ℕ) (u v : ℕ → X) {k : ℕ} (hk : k < J.card) :
    mergeA J M u v (J.orderEmbOfFin rfl ⟨k, hk⟩) = u k := by
  classical
  unfold mergeA
  rw [if_pos (Finset.orderEmbOfFin_mem _ _ _), rank_orderEmbOfFin]

/-- **Reindexing by ranks.** -/
lemma sum_range_rank {X : Type*} [AddCommMonoid X] (J : Finset ℕ) {m : ℕ} (hm : m ≤ J.card)
    (F : ℕ → X) : ∑ k ∈ Finset.range m, F k = ∑ i ∈ J with rank J i < m, F (rank J i) := by
  refine Finset.sum_nbij' (fun k => if hk : k < J.card then J.orderEmbOfFin rfl ⟨k, hk⟩ else 0)
    (rank J) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_range, Finset.mem_filter] at hk ⊢
    rw [dif_pos (by omega), rank_orderEmbOfFin]
    exact ⟨Finset.orderEmbOfFin_mem _ _ _, hk⟩
  · intro i hi
    simp only [Finset.mem_filter] at hi
    exact Finset.mem_range.2 hi.2
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only
    rw [dif_pos (by omega), rank_orderEmbOfFin]
  · intro i hi
    simp only [Finset.mem_filter] at hi
    simp only
    rw [dif_pos (rank_lt_card hi.1), emb_rank J hi.1]
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only
    rw [dif_pos (by omega), rank_orderEmbOfFin]

lemma sum_rank {X : Type*} [AddCommMonoid X] (J : Finset ℕ) (F : ℕ → X) :
    ∑ i ∈ J, F (rank J i) = ∑ k ∈ Finset.range J.card, F k := by
  rw [sum_range_rank J le_rfl]
  congr 1
  exact (Finset.filter_true_of_mem fun i hi => rank_lt_card hi).symm

lemma S_sub_rank (J : Finset ℕ) (w : ℕ → ℕ) {t : ℕ} (ht : t ∈ J) :
    S (sub J w) (rank J t) = ∑ i ∈ J with i < t, w i := by
  unfold S
  rw [sum_range_rank J (rank_lt_card ht).le]
  refine Finset.sum_congr ?_ fun i hi => sub_rank J w (Finset.mem_filter.1 hi).1
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    by_contra h'
    exact absurd h (not_lt.2 (by
      rcases (not_lt.1 h').lt_or_eq with h'' | rfl
      · exact (rank_lt_of_lt ht h'').le
      · exact le_rfl))
  · rintro ⟨hi, h⟩
    exact ⟨hi, rank_lt_of_lt hi h⟩

/-! ## The composite at positions -/

lemma cut_sizeUpTo_emb {n : ℕ} (c : Composition n) (M : Finset α) (hM : M.card = n)
    (j : Fin c.length) (h : (blk M (cb c) j).card = c.blocksFun j) (i : Fin (c.blocksFun j)) :
    (blk M (cb c) j).orderEmbOfFin h i = M.orderEmbOfFin hM (c.embedding j i) := by
  have hle : c.sizeUpTo (j + 1) ≤ n := c.sizeUpTo_le _
  have hj : c.sizeUpTo j + c.blocksFun j = c.sizeUpTo (j + 1) := (c.sizeUpTo_succ' j).symm
  have hM' : (cut M (c.sizeUpTo (j + 1))).card = c.sizeUpTo (j + 1) := card_cut M (by omega)
  have e : blk M (cb c) j = cut M (c.sizeUpTo (j + 1)) \
      cut (cut M (c.sizeUpTo (j + 1))) (c.sizeUpTo j) := by
    unfold blk
    rw [S_cb, S_cb, cut_cut M (c.monotone_sizeUpTo (Nat.le_succ _))]
  have key : ∀ (B : Finset α), B = cut M (c.sizeUpTo (j + 1)) \
      cut (cut M (c.sizeUpTo (j + 1))) (c.sizeUpTo j) →
      ∀ (hB : B.card = c.blocksFun j),
      B.orderEmbOfFin hB i = M.orderEmbOfFin hM (c.embedding j i) := by
    rintro B rfl hB
    rw [rest_emb _ hM' hj hB i, cut_emb M hM (by omega) hM']
    congr 1
  exact key _ e h

/-- **The composite of two series at positions** is the sum over the compositions of the number
of positions, of the outer series on the values of the inner one on the blocks. -/
lemma ev_comp {X : Type*} [AddCommGroup X] [Module R X] (g : Ser R W X) (f : Ser R V W)
    (w : α → V) {M : Finset α} {n : ℕ} (hM : M.card = n) :
    ev (MSer.comp g f) w M = ∑ c : Composition n,
      g c.length fun j => ev f w (blk M (cb c) j) := by
  rw [ev_eq _ w M hM, MSer.comp_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  funext j
  have hc : (blk M (cb c) j).card = c.blocksFun j := by
    have hsub : cut M (c.sizeUpTo j) ⊆ cut M (c.sizeUpTo (j + 1)) := fun t ht =>
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 ht).1, lt_of_lt_of_le (Finset.mem_filter.1 ht).2
        (c.monotone_sizeUpTo (Nat.le_succ _))⟩
    unfold blk
    rw [S_cb, S_cb, Finset.card_sdiff_of_subset hsub,
      card_cut M (by rw [hM]; exact c.sizeUpTo_le _),
      card_cut M (by rw [hM]; exact c.sizeUpTo_le _), c.sizeUpTo_succ' j]
    omega
  rw [ev_eq f w _ hc]
  unfold MSer.applyComp
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [cut_sizeUpTo_emb c M hM j hc i]

/-! ## Regrouping by the blocks of each word -/

lemma mergeA_of_mem {X : Type*} {J M : Finset ℕ} (u v : ℕ → X) {t : ℕ} (ht : t ∈ J) :
    mergeA J M u v t = u (rank J t) := by
  classical
  unfold mergeA
  rw [if_pos ht]

lemma mergeA_of_not_mem {X : Type*} {J M : Finset ℕ} (u v : ℕ → X) {t : ℕ} (ht : t ∉ J) :
    mergeA J M u v t = v (rank (M \ J) t) := by
  classical
  unfold mergeA
  rw [if_neg ht]

lemma mergeA_emb_compl {X : Type*} (J M : Finset ℕ) (u v : ℕ → X) {k : ℕ}
    (hk : k < (M \ J).card) : mergeA J M u v ((M \ J).orderEmbOfFin rfl ⟨k, hk⟩) = v k := by
  have hm := Finset.orderEmbOfFin_mem (M \ J) rfl ⟨k, hk⟩
  rw [mergeA_of_not_mem u v (Finset.mem_sdiff.1 hm).2, rank_orderEmbOfFin]

lemma sum_sub (J : Finset ℕ) (w : ℕ → ℕ) : S (sub J w) J.card = ∑ i ∈ J, w i := by
  unfold S
  rw [← sum_rank J]
  exact Finset.sum_congr rfl fun i hi => sub_rank J w hi

lemma sub_pos {J : Finset ℕ} {w : ℕ → ℕ} (h : ∀ t ∈ J, 0 < w t) :
    ∀ k < J.card, 0 < sub J w k := fun k hk => by
  unfold sub
  rw [dif_pos hk]
  exact h _ (Finset.orderEmbOfFin_mem _ _ _)

/-- **The composition of the blocks at the positions of `J`.** -/
noncomputable def subComp {m : ℕ} (J : Finset ℕ) (w : ℕ → ℕ) (h : ∀ t ∈ J, 0 < w t)
    (hs : ∑ i ∈ J, w i = m) : Composition m :=
  ofWord (sub J w) J.card (sub_pos h) (by rw [sum_sub, hs])

lemma cb_subComp {m : ℕ} (J : Finset ℕ) (w : ℕ → ℕ) (h : ∀ t ∈ J, 0 < w t)
    (hs : ∑ i ∈ J, w i = m) : cb (subComp J w h hs) = sub J w := by
  funext k
  unfold subComp
  rw [cb_ofWord]
  split_ifs with hk
  · rfl
  · rw [sub_of_le J w (by omega)]

lemma length_subComp {m : ℕ} (J : Finset ℕ) (w : ℕ → ℕ) (h : ∀ t ∈ J, 0 < w t)
    (hs : ∑ i ∈ J, w i = m) : (subComp J w h hs).length = J.card :=
  length_ofWord _ _ _ _

lemma comp_eq_of_cb {m : ℕ} {c c' : Composition m} (h : c.length = c'.length)
    (h' : ∀ k < c.length, cb c k = cb c' k) : c = c' := by
  refine Composition.ext (List.ext_getElem (by simpa [Composition.length] using h) ?_)
  intro k h1 h2
  have hk : k < c.length := by simpa [Composition.length] using h1
  have := h' k hk
  rw [cb_of_lt c hk, cb_of_lt c' (by omega)] at this
  exact this

lemma sum_cb {m : ℕ} (c : Composition m) : ∑ j ∈ Finset.range c.length, cb c j = m := by
  change S (cb c) c.length = m
  rw [S_cb, Composition.sizeUpTo_length]

section bij

variable {n A : ℕ}

variable (n A) in
/-- The compositions of `n` with a set of their blocks holding `A` positions. -/
abbrev LIdx : Finset (Σ _ : Composition n, Finset ℕ) :=
  Finset.univ.sigma fun c => (Finset.range c.length).powerset.filter fun J => ∑ j ∈ J, cb c j = A

variable (n A) in
/-- Pairs of compositions of `A` and `n - A`, with a shuffle of their blocks. -/
abbrev RIdx : Finset (Σ _ : Composition A × Composition (n - A), Finset ℕ) :=
  Finset.univ.sigma fun p => (Finset.range (p.1.length + p.2.length)).powersetCard p.1.length

lemma mem_LIdx {a : Σ _ : Composition n, Finset ℕ} :
    a ∈ LIdx n A ↔ a.2 ⊆ Finset.range a.1.length ∧ ∑ j ∈ a.2, cb a.1 j = A := by
  simp [LIdx, Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset]

lemma mem_RIdx {a : Σ _ : Composition A × Composition (n - A), Finset ℕ} :
    a ∈ RIdx n A ↔ a.2 ⊆ Finset.range (a.1.1.length + a.1.2.length) ∧
      a.2.card = a.1.1.length := by
  simp [RIdx, Finset.mem_powersetCard]

/-- From a composition and a set of its blocks, the compositions of the two words. -/
noncomputable def fwd (a : Σ _ : Composition n, Finset ℕ) (ha : a ∈ LIdx n A) :
    Σ _ : Composition A × Composition (n - A), Finset ℕ :=
  ⟨(subComp a.2 (cb a.1)
      (fun _ ht => cb_pos _ (Finset.mem_range.1 ((mem_LIdx.1 ha).1 ht))) (mem_LIdx.1 ha).2,
    subComp (Finset.range a.1.length \ a.2) (cb a.1)
      (fun _ ht => cb_pos _ (Finset.mem_range.1 (Finset.mem_sdiff.1 ht).1)) (by
        have := Finset.sum_sdiff (f := cb a.1) (mem_LIdx.1 ha).1
        rw [sum_cb, (mem_LIdx.1 ha).2] at this
        omega)), a.2⟩

lemma bwd_pos {a : Σ _ : Composition A × Composition (n - A), Finset ℕ} (ha : a ∈ RIdx n A) :
    ∀ k < a.1.1.length + a.1.2.length, 0 < mergeA a.2
      (Finset.range (a.1.1.length + a.1.2.length)) (cb a.1.1) (cb a.1.2) k := by
  intro k hk
  obtain ⟨hJ, hc⟩ := mem_RIdx.1 ha
  by_cases h : k ∈ a.2
  · rw [mergeA_of_mem _ _ h]
    exact cb_pos _ (hc ▸ rank_lt_card h)
  · rw [mergeA_of_not_mem _ _ h]
    have hm : k ∈ Finset.range (a.1.1.length + a.1.2.length) \ a.2 :=
      Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hk, h⟩
    have := rank_lt_card hm
    rw [Finset.card_sdiff_of_subset hJ, Finset.card_range, hc] at this
    exact cb_pos _ (by omega)

lemma bwd_sum (hA : A ≤ n) {a : Σ _ : Composition A × Composition (n - A), Finset ℕ}
    (ha : a ∈ RIdx n A) :
    S (mergeA a.2 (Finset.range (a.1.1.length + a.1.2.length)) (cb a.1.1) (cb a.1.2))
      (a.1.1.length + a.1.2.length) = n := by
  obtain ⟨hJ, hc⟩ := mem_RIdx.1 ha
  unfold S
  rw [← Finset.sum_sdiff hJ]
  have h1 : ∑ t ∈ a.2, mergeA a.2 (Finset.range (a.1.1.length + a.1.2.length)) (cb a.1.1)
      (cb a.1.2) t = A := by
    rw [Finset.sum_congr rfl fun t ht => mergeA_of_mem _ _ ht, sum_rank, hc, sum_cb]
  have hK : (Finset.range (a.1.1.length + a.1.2.length) \ a.2).card = a.1.2.length := by
    rw [Finset.card_sdiff_of_subset hJ, Finset.card_range, hc]
    omega
  have h2 : ∑ t ∈ Finset.range (a.1.1.length + a.1.2.length) \ a.2,
      mergeA a.2 (Finset.range (a.1.1.length + a.1.2.length)) (cb a.1.1) (cb a.1.2) t
      = n - A := by
    rw [Finset.sum_congr rfl fun t ht => mergeA_of_not_mem _ _ (Finset.mem_sdiff.1 ht).2,
      sum_rank, hK, sum_cb]
  rw [h1, h2]
  omega

/-- From compositions of the two words and a shuffle of their blocks, the composition. -/
noncomputable def bwd (hA : A ≤ n) (a : Σ _ : Composition A × Composition (n - A), Finset ℕ)
    (ha : a ∈ RIdx n A) : Σ _ : Composition n, Finset ℕ :=
  ⟨ofWord (mergeA a.2 (Finset.range (a.1.1.length + a.1.2.length)) (cb a.1.1) (cb a.1.2))
    (a.1.1.length + a.1.2.length) (bwd_pos ha) (bwd_sum hA ha), a.2⟩

lemma fwd_mem {a : Σ _ : Composition n, Finset ℕ} (ha : a ∈ LIdx n A) : fwd a ha ∈ RIdx n A := by
  obtain ⟨hJ, -⟩ := mem_LIdx.1 ha
  rw [mem_RIdx]
  simp only [fwd, length_subComp]
  refine ⟨?_, by trivial⟩
  rw [Finset.card_sdiff_of_subset hJ, Finset.card_range,
    show a.2.card + (a.1.length - a.2.card) = a.1.length by
      have := Finset.card_le_card hJ
      rw [Finset.card_range] at this
      omega]
  exact hJ

lemma bwd_mem (hA : A ≤ n) {a : Σ _ : Composition A × Composition (n - A), Finset ℕ}
    (ha : a ∈ RIdx n A) : bwd hA a ha ∈ LIdx n A := by
  obtain ⟨hJ, hc⟩ := mem_RIdx.1 ha
  rw [mem_LIdx]
  simp only [bwd, length_ofWord]
  refine ⟨hJ, ?_⟩
  rw [Finset.sum_congr rfl fun t ht => by
    rw [cb_ofWord, if_pos (Finset.mem_range.1 (hJ ht)), mergeA_of_mem _ _ ht], sum_rank, hc,
    sum_cb]

lemma bwd_fwd (hA : A ≤ n) {a : Σ _ : Composition n, Finset ℕ} (ha : a ∈ LIdx n A) :
    bwd hA (fwd a ha) (fwd_mem ha) = a := by
  obtain ⟨c, J⟩ := a
  obtain ⟨hJ, -⟩ := mem_LIdx.1 ha
  dsimp only at hJ
  have hL : J.card + (Finset.range c.length \ J).card = c.length := by
    rw [Finset.card_sdiff_of_subset hJ, Finset.card_range]
    have := Finset.card_le_card hJ
    rw [Finset.card_range] at this
    omega
  refine Sigma.ext ?_ HEq.rfl
  simp only [bwd, fwd]
  refine comp_eq_of_cb (by rw [length_ofWord, length_subComp, length_subComp, hL]) ?_
  intro k hk
  rw [length_ofWord, length_subComp, length_subComp, hL] at hk
  rw [cb_ofWord, if_pos (by rw [length_subComp, length_subComp, hL]; exact hk)]
  simp only [length_subComp, hL, cb_subComp]
  by_cases h : k ∈ J
  · rw [mergeA_of_mem _ _ h, sub_rank J _ h]
  · rw [mergeA_of_not_mem _ _ h, sub_rank _ _ (Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hk, h⟩)]

lemma fwd_bwd (hA : A ≤ n) {a : Σ _ : Composition A × Composition (n - A), Finset ℕ}
    (ha : a ∈ RIdx n A) : fwd (bwd hA a ha) (bwd_mem hA ha) = a := by
  obtain ⟨⟨cx, cy⟩, J⟩ := a
  obtain ⟨hJ, hc⟩ := mem_RIdx.1 ha
  dsimp only at hJ hc
  have hK : (Finset.range (cx.length + cy.length) \ J).card = cy.length := by
    rw [Finset.card_sdiff_of_subset hJ, Finset.card_range]
    omega
  refine Sigma.ext ?_ HEq.rfl
  simp only [bwd, fwd, length_ofWord]
  refine Prod.ext ?_ ?_
  · refine comp_eq_of_cb (by rw [length_subComp]; exact hc) fun k hk => ?_
    rw [length_subComp] at hk
    rw [cb_subComp]
    unfold sub
    rw [dif_pos hk, cb_ofWord, if_pos (Finset.mem_range.1 (hJ (Finset.orderEmbOfFin_mem _ _ _))),
      mergeA_emb]
  · refine comp_eq_of_cb (by rw [length_subComp]; exact hK) fun k hk => ?_
    rw [length_subComp] at hk
    rw [cb_subComp]
    unfold sub
    rw [dif_pos hk, cb_ofWord, if_pos (Finset.mem_range.1
      (Finset.mem_sdiff.1 (Finset.orderEmbOfFin_mem _ _ _)).1), mergeA_emb_compl]

end bij

/-! ## Composites vanish on shuffles -/

/-- **An even series takes homogeneous inputs to an element of their total parity.** -/
lemma isPar_ev_even {εV : V →ₗ[R] V} {εW : W →ₗ[R] W} (f : Ser R V W)
    (hf : MSer.IsEven εV εW f) {S : Finset α} {w : α → V} {q : α → Bool}
    (hw : ∀ t ∈ S, IsPar εV (q t) (w t)) : IsPar εW (par q S) (ev f w S) := by
  have h1 : ev f (fun t => εV (w t)) S = εW (ev f w S) := hf _ _
  have h2 : ev f (fun t => εV (w t)) S = ev f (fun t => σ R (q t) • w t) S :=
    ev_congr f fun t ht => hw t ht
  unfold IsPar
  rw [← h1, h2, ev_smul, σ_par]

lemma ev_range (F : Ser R V Z) (w : ℕ → V) (m : ℕ) :
    ev F w (Finset.range m) = F m fun j => w j := by
  rw [ev_eq F w _ (Finset.card_range m)]
  congr 1
  funext j
  simp only [Function.comp_apply]
  rw [range_orderEmbOfFin]

/-- The values of `f` on the blocks of a composition of a word. -/
noncomputable def wv (f : Ser R V W) {m : ℕ} (c : Composition m) (x : ℕ → V) (k : ℕ) : W :=
  ev f (shift x (S (cb c) k)) (Finset.range (cb c k))

/-- The parities of the blocks of a composition of a word. -/
def wq {m : ℕ} (c : Composition m) (px : ℕ → Bool) (k : ℕ) : Bool :=
  par (shift px (S (cb c) k)) (Finset.range (cb c k))

lemma xb_eq (b : ℕ → ℕ) (J : Finset ℕ) (t : ℕ) : xb b J t = ∑ i ∈ J with i < t, b i := by
  unfold xb
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  tauto

lemma yb_eq (b : ℕ → ℕ) (J : Finset ℕ) {ℓ t : ℕ} (ht : t < ℓ) :
    yb b J t = ∑ i ∈ Finset.range ℓ \ J with i < t, b i := by
  unfold yb
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by omega, h2⟩, h1⟩
  · rintro ⟨⟨-, h2⟩, h1⟩
    exact ⟨h1, h2⟩

lemma mergeA_wq {n A : ℕ} {c : Composition n} {J : Finset ℕ}
    (h1 : ∀ t ∈ J, 0 < cb c t) (hs1 : ∑ i ∈ J, cb c i = A)
    (h2 : ∀ t ∈ Finset.range c.length \ J, 0 < cb c t)
    (hs2 : ∑ i ∈ Finset.range c.length \ J, cb c i = n - A) (px py : ℕ → Bool) {t : ℕ}
    (ht : t < c.length) :
    mergeA J (Finset.range c.length) (wq (subComp J (cb c) h1 hs1) px)
      (wq (subComp _ (cb c) h2 hs2) py) t = bpar (cb c) px py J t := by
  unfold wq bpar
  rw [cb_subComp, cb_subComp]
  split_ifs with h
  · rw [mergeA_of_mem _ _ h, S_sub_rank J _ h, sub_rank J _ h, xb_eq]
  · have hK : t ∈ Finset.range c.length \ J := Finset.mem_sdiff.2 ⟨Finset.mem_range.2 ht, h⟩
    rw [mergeA_of_not_mem _ _ h, S_sub_rank _ _ hK, sub_rank _ _ hK, yb_eq _ _ ht]

lemma mergeA_wv (f : Ser R V W) {n A : ℕ} {c : Composition n} {J : Finset ℕ}
    (h1 : ∀ t ∈ J, 0 < cb c t) (hs1 : ∑ i ∈ J, cb c i = A)
    (h2 : ∀ t ∈ Finset.range c.length \ J, 0 < cb c t)
    (hs2 : ∑ i ∈ Finset.range c.length \ J, cb c i = n - A) (x y : ℕ → V) {t : ℕ}
    (ht : t < c.length) :
    mergeA J (Finset.range c.length) (wv f (subComp J (cb c) h1 hs1) x)
      (wv f (subComp _ (cb c) h2 hs2) y) t = bval f (cb c) x y J t := by
  unfold wv bval
  rw [cb_subComp, cb_subComp]
  split_ifs with h
  · rw [mergeA_of_mem _ _ h, S_sub_rank J _ h, sub_rank J _ h, xb_eq]
  · have hK : t ∈ Finset.range c.length \ J := Finset.mem_sdiff.2 ⟨Finset.mem_range.2 ht, h⟩
    rw [mergeA_of_not_mem _ _ h, S_sub_rank _ _ hK, sub_rank _ _ hK, yb_eq _ _ ht]

variable {X : Type*} [AddCommGroup X] [Module R X] (εW : W →ₗ[R] W)

/-- **Composites of series vanishing on shuffles vanish on shuffles**, the inner series even. -/
theorem vanAt_comp {f : Ser R V W} {g : Ser R W X} (hf : ∀ n, VanAt α εV f n)
    (hfe : MSer.IsEven εV εW f) (hg : ∀ n, VanAt ℕ εW g n) (n : ℕ) :
    VanAt α εV (MSer.comp g f) n := by
  classical
  intro M hM A x y px py hx hy hA0 hAn
  rw [shf_congr (Ψ := fun w _ => ∑ c : Composition n,
      g c.length fun j => ev f w (blk M (cb c) j)) (fun w => ev_comp g f w hM), shf_sum]
  rw [Finset.sum_congr rfl fun c _ => shf_blocks εV hf hx hy (cb c) c.length
    (fun j hj => cb_pos c hj) (g c.length) M (by rw [hM, S_cb, Composition.sizeUpTo_length]) A]
  rw [Finset.sum_sigma']
  -- regroup by the compositions of the two words
  have hA : A ≤ n := hAn.le
  rw [Finset.sum_bij' (s := LIdx n A) (t := RIdx n A)
    (g := fun a => ks R (mergeA a.2 (Finset.range (a.1.1.length + a.1.2.length))
        (wq a.1.1 px) (wq a.1.2 py)) a.2 (Finset.range (a.1.1.length + a.1.2.length) \ a.2) •
      ev g (mergeA a.2 (Finset.range (a.1.1.length + a.1.2.length)) (wv f a.1.1 x)
        (wv f a.1.2 y)) (Finset.range (a.1.1.length + a.1.2.length)))
    (fun a ha => fwd a ha) (fun a ha => bwd hA a ha) (fun a ha => fwd_mem ha)
    (fun a ha => bwd_mem hA ha) (fun a ha => bwd_fwd hA ha) (fun a ha => fwd_bwd hA ha) ?_]
  · rw [Finset.sum_sigma, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_eq_zero fun cx _ => Finset.sum_eq_zero fun cy _ => ?_
    have hx0 : 0 < cx.length := Composition.length_pos_of_pos cx hA0
    have hy0 : 0 < cy.length := Composition.length_pos_of_pos cy (by omega)
    have := hg (cx.length + cy.length) (Finset.range (cx.length + cy.length))
      (Finset.card_range _) cx.length (wv f cx x) (wv f cy y) (wq cx px) (wq cy py)
      (fun k => isPar_ev_even f hfe fun t _ => hx _)
      (fun k => isPar_ev_even f hfe fun t _ => hy _) hx0 (by omega)
    unfold shf at this
    exact this
  · rintro ⟨c, J⟩ ha
    obtain ⟨hJ, hs⟩ := mem_LIdx.1 ha
    dsimp only at hJ hs
    have hL : J.card + (Finset.range c.length \ J).card = c.length := by
      rw [Finset.card_sdiff_of_subset hJ, Finset.card_range]
      have := Finset.card_le_card hJ
      rw [Finset.card_range] at this
      omega
    simp only [fwd, length_subComp, hL]
    rw [ev_range]
    congr 1
    · refine ks_congr fun t ht => (mergeA_wq _ _ _ _ px py ?_).symm
      rcases Finset.mem_union.1 ht with h | h
      · exact Finset.mem_range.1 (hJ h)
      · exact Finset.mem_range.1 (Finset.mem_sdiff.1 h).1
    · congr 1
      funext j
      exact (mergeA_wv f _ _ _ _ x y j.isLt).symm

/-! ## ∞-morphisms of C∞-algebras -/

/-- **A series concentrated in arity one vanishes on shuffles.** -/
lemma vanAt_of_arity_one {f : Ser R V Z} (hf : ∀ n, n ≠ 1 → f n = 0) (n : ℕ) :
    VanAt α εV f n := by
  intro M hM A x y px py _ _ hA0 hA
  unfold shf
  refine Finset.sum_eq_zero fun T _ => ?_
  rw [ev_eq f _ M hM, hf n (by omega), MultilinearMap.zero_apply, smul_zero]

/-- **An ∞-morphism of C∞-algebras** `(V, b) ⇝ (W, b')`: an ∞-morphism of A∞-algebras whose
components vanish on the signed shuffles of homogeneous words, at any finite set of positions in
`ℕ` (`CInfT.VanAt`). -/
structure IsCInfMorph (b : AInf.Fam R V) (b' : AInf.Fam R W) (f : MSer R V W) : Prop
    extends AInf.IsInfMorph εV εW b b' f where
  /-- The components vanish on shuffles. -/
  shuffle : ∀ n, VanAt ℕ εV f n

namespace IsCInfMorph

variable {εV} {εW} {εX : X →ₗ[R] X}

variable (εV) in
/-- **The identity is an ∞-morphism of C∞-algebras.** -/
theorem id (b : AInf.Fam R V) : IsCInfMorph εV εV b b (MSer.id R V) where
  toIsInfMorph := AInf.IsInfMorph.id εV b
  shuffle := vanAt_of_arity_one εV fun _ h => MSer.id_of_ne_one h

/-- **∞-morphisms of C∞-algebras compose.** -/
theorem comp {b : AInf.Fam R V} {b' : AInf.Fam R W} {b'' : AInf.Fam R X} {f : MSer R V W}
    {g : MSer R W X} (hf : IsCInfMorph εV εW b b' f) (hg : IsCInfMorph εW εX b' b'' g) :
    IsCInfMorph εV εX b b'' (MSer.comp g f) where
  toIsInfMorph := hf.toIsInfMorph.comp hg.toIsInfMorph
  shuffle := vanAt_comp εV εW hf.shuffle hf.even hg.shuffle

end IsCInfMorph

/-- **A strict morphism is an ∞-morphism of C∞-algebras exactly when it is one of A∞-algebras.** -/
theorem isCInfMorph_lin_iff {εV : V →ₗ[R] V} {εW : W →ₗ[R] W} {b : AInf.Fam R V}
    {b' : AInf.Fam R W} (φ : V →ₗ[R] W) :
    IsCInfMorph εV εW b b' (MSer.lin φ) ↔ AInf.IsInfMorph εV εW b b' (MSer.lin φ) :=
  ⟨fun h => h.toIsInfMorph, fun h =>
    ⟨h, vanAt_of_arity_one εV fun _ hn => MSer.lin_of_ne_one φ hn⟩⟩

/-- **The trees of the transfer vanish on shuffles** in every arity, for a dg algebra which is a
C∞-algebra: the shuffle condition of `IsCInfMorph` for the series `i∞` of the trees. -/
theorem shuffle_tf {μ : End R V 2} {d e h : V →ₗ[R] V} (hdo : ∀ x, d (εV x) = -εV (d x))
    (hμ : End.IsHomog εV 1 μ) (hr : HTT.Retract εV d e h)
    (hC : CInf.IsCInf εV (AInf.dga R V (HTT.op1 d) μ)) (n : ℕ) :
    VanAt α εV (toSer (HTT.tf μ e h)) n := by
  obtain ⟨hd, hcomm⟩ := dga_of_isCInf εV hdo hμ hC
  rcases n with _ | n
  · intro M _ A _ _ _ _ _ _ hA0 hA
    omega
  · exact vanAt_tf hcomm (HTT.tf_even hd hr) n

end CInfM

end Operad
