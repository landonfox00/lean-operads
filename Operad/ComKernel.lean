/-
# The kernel of the signed linear orders onto `Com^¡`: the shuffles

Over a field `K` of characteristic zero, **the morphism `ComDual.rho : OrdCo K → Com^¡` is onto,
and its kernel on `n + 1` inputs is the span of the relabelled standard shuffle elements**
(`ComDual.rho_surjective`, `ComDual.rho_eq_zero_iff`).

* **The standard shuffle element** `ComDual.shStd K n k` is the restriction of the alternating
  sum of the linear orders to the shuffles of the first `k` inputs with the others
  (`ComDual.stdCons`); it lies in the coideal of the shuffles (`ComDual.shStd_mem`).
* **Every order is a combination of shuffles and of orders starting with the first input**
  (`ComDual.single_mem_sup`), by induction on the number `k` of inputs before the first one: the
  shuffle of the first `k` inputs of the order with the others contains the order once, and its
  other terms have fewer inputs before the first input (`ComDual.rank_lt_of_mem_consSet`).
* **The orders starting with a given input embed in `Com^¡`** (`ComDual.rho_injective_first`),
  by induction on the arity, decomposing at the window of the first two inputs.
* Hence the kernel is the span of the shuffles, and `ComDual.rho` is onto by the dimension
  `(n - 1)!` of `Com^¡` (`ComDual.finrank_dual_com`) and the count of the orders starting with
  the first input (`ComDual.firstOrd`). It preserves the coaugmentations (`ComDual.rho_one`).

This is the statement, for the Koszul dual cooperads, that the Lie elements of the free
associative algebra are the elements orthogonal to the shuffles.
-/
import Operad.ComShuffle
import Mathlib.GroupTheory.Perm.Fin

universe u

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace ComDual

open SymPresComLie OrdCo LieDual

variable {K : Type u} [Field K]

/-! ## The standard shuffles -/

/-- **The constraints of the shuffles of the first `k` inputs with the others**: two inputs of
the same side are in their standard order. -/
def stdCons (n k : ℕ) : Fin (n + 1) → Fin (n + 1) → Bool → Prop :=
  fun x y v => ((x : ℕ) < k ↔ (y : ℕ) < k) ∧ (v = true ↔ x < y)

lemma valid_stdCons {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    Valid (fun x : Fin (n + 1) => decide ((x : ℕ) < k)) (stdCons n k) :=
  ⟨⟨0, decide_eq_true hk⟩, ⟨Fin.last n, decide_eq_false (by rw [Fin.val_last]; omega)⟩,
    fun _ _ _ h => by rw [decide_eq_decide]; exact h.1⟩

variable (K) in
/-- **The standard shuffle element**: the signed sum of the shuffles of the first `k` inputs
with the others, the restriction of the alternating sum of the linear orders. -/
noncomputable def shStd (n k : ℕ) : NOrd (Fin (n + 1)) →₀ K :=
  restr (consSet (stdCons n k)) (show NOrd (Fin (n + 1)) →₀ K from alt K n)

/-- The standard order satisfies the standard constraints. -/
lemma sd_mem_consSet (n k : ℕ) : sd n ∈ consSet (stdCons n k) :=
  fun _ _ _ h => h.2.symm

/-- The coefficient of the standard order in a standard shuffle element is one. -/
lemma shStd_sd (n k : ℕ) : shStd K n k (sd n) = 1 := by
  have h := alt_apply (K := K) n 1
  rw [show SetOperad.map (1 : Equiv.Perm (Fin (n + 1))) (sd n) = sd n from
    SetOperad.map_refl _] at h
  rw [shStd, restr_apply, if_pos (sd_mem_consSet n k), h]
  simp

/-- **A shuffle other than the standard order has fewer inputs before the first input of the
second word.** -/
lemma rank_lt_of_mem_consSet {n k : ℕ} (hkn : k ≤ n) {M : NOrd (Fin (n + 1))}
    (hM : M ∈ consSet (stdCons n k)) (hne : M ≠ sd n) : M.1.rank ⟨k, by omega⟩ < k := by
  classical
  have hj : ∀ x : Fin (n + 1), k < (x : ℕ) → M.1.lt ⟨k, by omega⟩ x := fun x hx =>
    (hM ⟨k, by omega⟩ x true ⟨by simp; omega, by simpa using Fin.mk_lt_of_lt_val hx⟩).2 rfl
  have hsub : ∀ x : Fin (n + 1), M.1.lt x ⟨k, by omega⟩ → (x : ℕ) < k := fun x hx => by
    by_contra hlt
    have hxk : (x : ℕ) ≠ k := fun e => M.1.irrefl _ (by
      have : x = ⟨k, by omega⟩ := Fin.ext e
      rw [this] at hx
      exact hx)
    exact M.1.irrefl _ (M.1.trans _ _ _ hx (hj x (by omega)))
  have hcard := AltGen.card_ini (N := n + 1) (l := k) (by omega)
  refine lt_of_lt_of_eq (Finset.card_lt_card
    ⟨fun x hx => AltGen.mem_ini.2 (hsub x (Finset.mem_filter.1 hx).2), fun hss => hne ?_⟩) hcard
  have hall : ∀ x : Fin (n + 1), (x : ℕ) < k → M.1.lt x ⟨k, by omega⟩ := fun x hx =>
    (Finset.mem_filter.1 (hss (AltGen.mem_ini.2 hx))).2
  have hsame : ∀ a b : Fin (n + 1), ((a : ℕ) < k ↔ (b : ℕ) < k) → (M.1.lt a b ↔ a < b) :=
    fun a b hab => (hM a b (decide (a < b)) ⟨hab, by simp⟩).trans (by simp)
  have hcross : ∀ a b : Fin (n + 1), (a : ℕ) < k → k ≤ (b : ℕ) → M.1.lt a b := fun a b ha hb => by
    rcases Nat.eq_or_lt_of_le hb with e | e
    · have : b = ⟨k, by omega⟩ := Fin.ext e.symm
      rw [this]
      exact hall a ha
    · exact M.1.trans _ _ _ (hall a ha) (hj b e)
  refine Subtype.ext (LinOrd.ext fun a b => ?_)
  show M.1.lt a b ↔ a < b
  by_cases ha : (a : ℕ) < k <;> by_cases hb : (b : ℕ) < k
  · exact hsame a b ⟨fun _ => hb, fun _ => ha⟩
  · exact ⟨fun _ => Fin.lt_def.2 (by omega), fun _ => hcross a b ha (by omega)⟩
  · refine ⟨fun h => absurd (M.1.trans _ _ _ h (hcross b a hb (by omega))) (M.1.irrefl _),
      fun h => absurd (Fin.lt_def.1 h) (by omega)⟩
  · exact hsame a b ⟨fun h => absurd h ha, fun h => absurd h hb⟩

/-! ## Every order is a combination of shuffles and of orders starting with the first input -/

variable (K) in
/-- **The span of the relabelled standard shuffle elements.** -/
noncomputable def stdSub (n : ℕ) : Submodule K (NOrd (Fin (n + 1)) →₀ K) :=
  Submodule.span K {y | ∃ k, 0 < k ∧ k ≤ n ∧ ∃ e : Equiv.Perm (Fin (n + 1)),
    y = Lin.mapL K e (shStd K n k)}

variable (K) in
/-- **The span of the orders starting with the first input.** -/
noncomputable def firstSub (n : ℕ) : Submodule K (NOrd (Fin (n + 1)) →₀ K) :=
  Submodule.span K {y | ∃ M : NOrd (Fin (n + 1)), M.1.rank 0 = 0 ∧ y = Finsupp.single M 1}

/-- A combination of orders lies in a submodule containing the orders of its support. -/
lemma mem_of_support {X : Type*} {S : Submodule K (X →₀ K)} (z : X →₀ K)
    (h : ∀ M, z M ≠ 0 → Finsupp.single M (1 : K) ∈ S) : z ∈ S := by
  rw [← Finsupp.sum_single z]
  refine Submodule.sum_mem _ fun M hM => ?_
  rw [← Finsupp.smul_single_one]
  exact S.smul_mem _ (h M (Finsupp.mem_support_iff.1 hM))

/-- **Every order is a combination of shuffles and of orders starting with the first input.** -/
theorem single_mem_sup (n : ℕ) (L : NOrd (Fin (n + 1))) :
    Finsupp.single L (1 : K) ∈ stdSub K n ⊔ firstSub K n := by
  classical
  obtain ⟨r, hr⟩ : ∃ r, L.1.rank 0 = r := ⟨_, rfl⟩
  induction r using Nat.strong_induction_on generalizing L with
  | _ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hpos
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨L, hr, rfl⟩)
    · obtain ⟨e, rfl⟩ := exists_perm L
      have hrk : ((e.symm 0 : Fin (n + 1)) : ℕ) = r := by
        have h1 : (SetOperad.map e (sd n)).1.rank 0 = (LinOrd.std (n + 1)).rank (e.symm 0) :=
          LinOrd.rank_map e _ 0
        rw [hr, LinOrd.rank_std] at h1
        exact h1.symm
      have hrn : r ≤ n := by have := (e.symm 0).2; omega
      have he0 : e.symm 0 = ⟨r, by omega⟩ := Fin.ext hrk
      obtain ⟨y, hy⟩ : ∃ y, y = Lin.mapL K e (shStd K n r) := ⟨_, rfl⟩
      have hymem : y ∈ stdSub K n := Submodule.subset_span ⟨r, hpos, hrn, e, hy⟩
      have hyL : y (SetOperad.map e (sd n)) = 1 := by
        rw [hy, Lin.mapL_apply, SetOperad.map_symm_map, shStd_sd]
      have hz : y - Finsupp.single (SetOperad.map e (sd n)) 1 ∈ stdSub K n ⊔ firstSub K n := by
        refine mem_of_support _ fun M hM => ?_
        have hMne : M ≠ SetOperad.map e (sd n) := fun h => by
          rw [h, Finsupp.sub_apply, hyL, Finsupp.single_eq_same, sub_self] at hM
          exact hM rfl
        rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hMne, sub_zero, hy, Lin.mapL_apply,
          shStd, restr_apply] at hM
        have hmem : SetOperad.map e.symm M ∈ consSet (stdCons n r) := by
          by_contra h
          rw [if_neg h] at hM
          exact hM rfl
        have hne' : SetOperad.map e.symm M ≠ sd n := fun h => hMne (by
          rw [← h, SetOperad.map_map_symm])
        have hlt := rank_lt_of_mem_consSet hrn hmem hne'
        have hrank : M.1.rank 0 = (SetOperad.map e.symm M).1.rank ⟨r, by omega⟩ := by
          have h2 : (SetOperad.map e.symm M).1.rank (e.symm 0)
              = M.1.rank (e.symm.symm (e.symm 0)) :=
            LinOrd.rank_map e.symm _ _
          rw [Equiv.symm_symm, Equiv.apply_symm_apply, he0] at h2
          exact h2.symm
        exact ih _ (hrank ▸ hlt) M rfl
      have hsum : Finsupp.single (SetOperad.map e (sd n)) (1 : K)
          = y - (y - Finsupp.single (SetOperad.map e (sd n)) 1) := by abel
      rw [hsum]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hymem) hz

/-! ## The orders starting with a given input embed in `Com^¡` -/

/-- A pure tensor killed by a tensor of maps, the second factor being detected by a functional. -/
lemma eq_zero_of_map_tmul {M N M' N' : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']
    (F : M →ₗ[K] M') (G : N →ₗ[K] N') (ψ : N' →ₗ[K] K) (x : M) (y : N) (hψ : ψ (G y) = 1)
    {T : M ⊗[K] N} (hT : T = x ⊗ₜ[K] y) (h : TensorProduct.map F G T = 0) : F x = 0 := by
  subst hT
  have h2 := congrArg (fun t => TensorProduct.rid K M' (LinearMap.lTensor M' ψ t)) h
  simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hψ,
    one_smul, map_zero] at h2
  exact h2

variable [CharZero K]

variable (K) in
/-- The value of the generator of an element of `Com^¡` on two inputs, at the identity. -/
noncomputable def psi2 : Koszul.Dual K (ECom K) (rCom K) (Fin 2) →ₗ[K] K where
  toFun z := (show ECom K (Fin 2) from FreeGrL.genCoef K (GrSpecies.Shift (ECom K) K) (Fin 2)
    ((Koszul.dualSub K (ECom K) (rCom K)).incl (Fin 2) z)).1 (Equiv.refl _)
  map_add' z z' := by
    rw [map_add, map_add]
    rfl
  map_smul' a z := by
    rw [map_smul, map_smul]
    rfl

/-- The standard order on two inputs is not killed in `Com^¡`. -/
lemma psi2_rho : psi2 K ((rho K).app (Fin 2) (SgnLin.bas NOrd.sgnD K (sd 1))) = 1 := by
  have h := genCoef_rho K (SgnLin.bas NOrd.sgnD K (sd 1) : OrdCo K (Fin 2))
  refine (congrArg (fun f : ECom K (Fin 2) => f.1 (Equiv.refl _)) h).trans ?_
  rw [jCom_val]
  show (show NOrd (Fin 2) →₀ K from SgnLin.bas NOrd.sgnD K (sd 1)) (OrdCo.ord2 (Equiv.refl _).symm)
    + (show NOrd (Fin 2) →₀ K from SgnLin.bas NOrd.sgnD K (sd 1))
      (OrdCo.ord2 ((Equiv.refl (Fin 2)).trans (Equiv.swap 0 1)).symm) = 1
  have h1 : OrdCo.ord2 (Equiv.refl (Fin 2)).symm = sd 1 := SetOperad.map_refl _
  have h2 : sd 1 ≠ OrdCo.ord2 ((Equiv.refl (Fin 2)).trans (Equiv.swap 0 1)).symm := fun h' => by
    have h3 : LinOrd.map (Equiv.refl (Fin 2)) (LinOrd.std 2)
        = LinOrd.map ((Equiv.refl (Fin 2)).trans (Equiv.swap 0 1)).symm (LinOrd.std 2) :=
      (LinOrd.ext fun a b => Iff.rfl : LinOrd.map (Equiv.refl (Fin 2)) (LinOrd.std 2)
        = LinOrd.std 2).trans (congrArg Subtype.val h')
    have h4 := LinOrd.eq_of_map_eq h3
    exact absurd h4 (by decide)
  rw [h1]
  show Finsupp.single (sd 1) (1 : K) (sd 1) + Finsupp.single (sd 1) (1 : K) _ = 1
  rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne h2.symm, add_zero]

/-- **The orders starting with a given input embed in `Com^¡`.** -/
theorem rho_injective_first : ∀ (n : ℕ) (A : Type) [Fintype A] [DecidableEq A],
    Fintype.card A = n + 1 → ∀ (a₀ : A) (w : OrdCo K A),
      (∀ M, (show NOrd A →₀ K from w) M ≠ 0 → M.1.rank a₀ = 0) → (rho K).app A w = 0 → w = 0 := by
  intro n
  induction n with
  | zero =>
    intro A _ _ hA a₀ w _ hw
    let e₁ : Unit ≃ A := (Equiv.ofUnique Unit (Fin 1)).trans (Fintype.equivFinOfCardEq hA).symm
    haveI : Subsingleton A := e₁.symm.subsingleton
    have hc := LinearMap.congr_fun (rho K).counit_app (SymSpecies.map (R := K) e₁.symm w)
    rw [LinearMap.comp_apply, (rho K).app_map, hw, map_zero, map_zero] at hc
    have h1 : Lin.mapL K e₁.symm w (SetOperad.one : NOrd Unit) = 0 := hc.symm
    rw [Lin.mapL_apply, Equiv.symm_symm] at h1
    refine Finsupp.ext fun M => ?_
    exact (congrArg (show NOrd A →₀ K from w)
      (Subtype.ext (LinOrd.eq_of_subsingleton _ _))).trans h1
  | succ n ih =>
    intro A _ _ hA a₀ w hsupp hw
    refine Finsupp.ext fun M => ?_
    show (show NOrd A →₀ K from w) M = 0
    by_contra hM
    have hr := hsupp M hM
    obtain ⟨τ, hτ⟩ := LinOrd.exists_map_eq (LinOrd.std (n + 1 + 1)) M.1
      ((Fintype.card_fin _).trans hA.symm)
    have ha0 : τ 0 = a₀ := M.1.rank_injective (by
      rw [hr, ← hτ, LinOrd.rank_map, Equiv.symm_apply_apply, LinOrd.rank_std]
      rfl)
    obtain ⟨E, hE⟩ : ∃ E, E = posEquivF (0 : Fin (n + 1)) 2 (n + 1 + 1) rfl := ⟨_, rfl⟩
    have hstd : SetOperad.map E (SetOperad.comp (0 : Fin (n + 1)) (sd n) (sd 1))
        = sd (n + 1) := by
      rw [hE]
      exact Subtype.ext (map_posEquivF (l := 2) (m := n + 1 + 1) 0 rfl)
    have hE0 : E (Sum.inr 0) = 0 := by
      rw [hE]
      exact Fin.ext (by rw [posEquivF_inr]; rfl)
    obtain ⟨e, he⟩ : ∃ e : Without (Fin (n + 1)) 0 ⊕ Fin 2 ≃ A, e = E.trans τ := ⟨_, rfl⟩
    have hMe : M = SetOperad.map e (SetOperad.comp (0 : Fin (n + 1)) (sd n) (sd 1)) := by
      rw [he, SetOperad.map_trans, hstd]
      exact Subtype.ext hτ.symm
    have hea : e.symm a₀ = Sum.inr 0 := by
      rw [he, ← ha0, ← hE0]
      exact Equiv.symm_apply_apply _ _
    obtain ⟨w', hw'⟩ : ∃ w' : NOrd (Without (Fin (n + 1)) 0 ⊕ Fin 2) →₀ K,
      w' = Lin.mapL K e.symm w := ⟨_, rfl⟩
    have hw'app : ∀ X, w' X = (show NOrd A →₀ K from w) (SetOperad.map e X) := fun X => by
      rw [hw', Lin.mapL_apply, Equiv.symm_symm]
    have hrank : ∀ (p : NOrd (Fin (n + 1))) (q : NOrd (Fin 2)),
        w' (SetOperad.comp 0 p q) ≠ 0 → p.1.rank 0 + q.1.rank 0 = 0 := fun p q h => by
      rw [hw'app] at h
      have h2 := hsupp _ h
      have h3 : (SetOperad.map e (SetOperad.comp (0 : Fin (n + 1)) p q)).1.rank a₀
          = (LinOrd.comp (0 : Fin (n + 1)) p.1 q.1).rank (e.symm a₀) := LinOrd.rank_map e _ a₀
      rw [h2, hea, LinOrd.rank_comp_inr] at h3
      exact h3.symm
    have hrho' : (rho K).app _ (show OrdCo K _ from w') = 0 := by
      rw [hw']
      exact ((rho K).app_map e.symm w).trans (by rw [hw, map_zero])
    have h1' := (rho K).decomp_app (B := Fin 2) (0 : Fin (n + 1))
    have h1 := LinearMap.congr_fun h1' (show OrdCo K _ from w')
    obtain ⟨D, hD⟩ : ∃ D, D = SgnLin.decompT K NOrd.sgnD (0 : Fin (n + 1)) w' := ⟨_, rfl⟩
    have hmap : TensorProduct.map ((rho K).app (Fin (n + 1))) ((rho K).app (Fin 2)) D = 0 := by
      rw [hD]
      refine h1.symm.trans ?_
      rw [LinearMap.comp_apply, hrho', map_zero]
    have hinj : Function.Injective fun p : NOrd (Fin (n + 1)) => (p, sd 1) :=
      fun p p' h => congrArg Prod.fst h
    obtain ⟨D₀, hD₀⟩ : ∃ D₀ : NOrd (Fin (n + 1)) →₀ K,
        D₀ = Finsupp.comapDomain _ (tens K (NOrd (Fin (n + 1))) (NOrd (Fin 2)) D)
          hinj.injOn := ⟨_, rfl⟩
    have hD₀app : ∀ p, D₀ p = σ K (SgnData.sgn (0 : Fin (n + 1)) (NOrd.sgnD.app _ p)
        (NOrd.sgnD.app _ (sd 1))) * w' (SetOperad.comp 0 p (sd 1)) := fun p => by
      rw [hD₀, Finsupp.comapDomain_apply, hD, SgnLin.decompT_apply]
    have hq : ∀ (p : NOrd (Fin (n + 1))) (q : NOrd (Fin 2)), q ≠ sd 1 →
        w' (SetOperad.comp 0 p q) = 0 := fun p q hq => by
      by_contra h
      have h2 := hrank p q h
      obtain ⟨π, rfl⟩ := exists_perm q
      have h3 : (SetOperad.map π (sd 1)).1.rank 0 = (LinOrd.std (1 + 1)).rank (π.symm 0) :=
        LinOrd.rank_map π _ 0
      rw [LinOrd.rank_std] at h3
      have h4 : π.symm 0 = 0 := Fin.ext (by rw [← h3]; exact (Nat.add_eq_zero_iff.1 h2).2)
      have h5 : ∀ π : Equiv.Perm (Fin 2), π.symm 0 = 0 → π = 1 := by decide
      rw [h5 π h4] at hq
      exact hq (SetOperad.map_refl _)
    have hDeq : D = D₀ ⊗ₜ[K] (Finsupp.single (sd 1) (1 : K)) := by
      refine (tens K (NOrd (Fin (n + 1))) (NOrd (Fin 2))).injective (Finsupp.ext fun pq => ?_)
      obtain ⟨p, q⟩ := pq
      rw [tens_tmul_apply, hD₀app, hD, SgnLin.decompT_apply]
      by_cases hqq : q = sd 1
      · rw [hqq, Finsupp.single_eq_same, mul_one]
      · rw [hq p q hqq, mul_zero, Finsupp.single_eq_of_ne hqq, mul_zero]
    have hF := eq_zero_of_map_tmul ((rho K).app (Fin (n + 1))) ((rho K).app (Fin 2)) (psi2 K)
      (show OrdCo K (Fin (n + 1)) from D₀) (SgnLin.bas NOrd.sgnD K (sd 1)) psi2_rho hDeq hmap
    have hzero := ih (Fin (n + 1)) (Fintype.card_fin _) 0 (show OrdCo K (Fin (n + 1)) from D₀)
      (fun p hp => by
        have hp' : D₀ p ≠ 0 := hp
        rw [hD₀app] at hp'
        exact (Nat.add_eq_zero_iff.1 (hrank p (sd 1) (right_ne_zero_of_mul hp'))).1) hF
    have h6 := hD₀app (sd n)
    rw [show D₀ = 0 from hzero, hw'app, ← hMe] at h6
    exact hM ((mul_eq_zero.1 h6.symm).resolve_left (OrdCo.σ_ne_zero K _))

/-! ## The kernel and the image -/

/-- The standard shuffle elements lie in the coideal of the shuffles. -/
lemma shStd_mem {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    (shStd K n k : OrdCo K (Fin (n + 1))) ∈ (shCoideal K).sub (Fin (n + 1)) :=
  Submodule.subset_span ⟨nu K n, _, _, valid_stdCons hk hkn,
    (congrArg (fun w : OrdCo K (Fin (n + 1)) => restr (consSet (stdCons n k))
      (show NOrd (Fin (n + 1)) →₀ K from w)) (toOrd_nu n)).symm⟩

/-- **The shuffles are killed in `Com^¡`.** -/
theorem rho_stdSub {n : ℕ} {x : OrdCo K (Fin (n + 1))} (hx : x ∈ stdSub K n) :
    (rho K).app (Fin (n + 1)) x = 0 := by
  refine rho_eq_zero ((Submodule.span_le.2 ?_ : stdSub K n ≤ (shCoideal K).sub (Fin (n + 1))) hx)
  rintro _ ⟨k, hk, hkn, e, rfl⟩
  exact (shCoideal K).map_mem e (shStd_mem hk hkn)

omit [CharZero K] in
/-- A combination of orders starting with the first input is supported on such orders. -/
lemma rank_of_mem_firstSub {n : ℕ} {f : NOrd (Fin (n + 1)) →₀ K} (hf : f ∈ firstSub K n) :
    ∀ M, f M ≠ 0 → M.1.rank 0 = 0 := by
  classical
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨M₀, hM₀, rfl⟩ := hy
    intro M hM
    by_cases h : M = M₀
    · rw [h]
      exact hM₀
    · exact absurd (Finsupp.single_eq_of_ne h) hM
  | zero => exact fun M hM => absurd rfl hM
  | add f g _ _ hf hg =>
    intro M hM
    by_cases h : f M = 0
    · refine hg M fun h' => hM ?_
      rw [Finsupp.add_apply, h, h', add_zero]
    · exact hf M h
  | smul a f _ hf =>
    intro M hM
    refine hf M fun h' => hM ?_
    rw [Finsupp.smul_apply, h', smul_zero]

/-- **The kernel of the signed linear orders onto `Com^¡` is the span of the shuffles.** -/
theorem rho_eq_zero_iff {n : ℕ} (x : OrdCo K (Fin (n + 1))) :
    (rho K).app (Fin (n + 1)) x = 0 ↔ x ∈ stdSub K n := by
  refine ⟨fun hx => ?_, rho_stdSub⟩
  have hmem : (show NOrd (Fin (n + 1)) →₀ K from x) ∈ stdSub K n ⊔ firstSub K n :=
    mem_of_support _ fun M _ => single_mem_sup n M
  obtain ⟨s, hs, f, hf, hsf⟩ := Submodule.mem_sup.1 hmem
  have hf0 : (rho K).app (Fin (n + 1)) (show OrdCo K (Fin (n + 1)) from f) = 0 := by
    have h1 : (show OrdCo K (Fin (n + 1)) from f) = x - (show OrdCo K (Fin (n + 1)) from s) :=
      eq_sub_of_add_eq' hsf
    rw [h1, map_sub, hx, rho_stdSub hs, sub_zero]
  have hzero := rho_injective_first n (Fin (n + 1)) (Fintype.card_fin _) 0
    (show OrdCo K (Fin (n + 1)) from f) (rank_of_mem_firstSub hf) hf0
  have hxs : x = (show OrdCo K (Fin (n + 1)) from s) := by
    rw [← hsf]
    exact (congrArg (fun g : NOrd (Fin (n + 1)) →₀ K => s + g) hzero).trans (add_zero s)
  rw [hxs]
  exact hs

/-- **The signed linear orders are coaugmented over `Com^¡`.** -/
theorem rho_one : (rho K).app Unit (GrCooperad.Coaug.one (R := K) (C := OrdCo K))
    = GrCooperad.Coaug.one (R := K) (C := Koszul.Dual K (ECom K) (rCom K)) := by
  refine Subtype.ext ?_
  show (Koszul.dualSub K (ECom K) (rCom K)).incl Unit
    ((rho K).app Unit (GrCooperad.Coaug.one (R := K) (C := OrdCo K)))
      = GrCooperad.Coaug.one (R := K) (C := Koszul.Cut K (ECom K))
  have hmem := FreeGrL.mem_unitSpan_of_card_le (R := K) (V := GrSpecies.Shift (ECom K) K)
    (hredC K) (A := Unit) (by simp) ((Koszul.dualSub K (ECom K) (rCom K)).incl Unit
      ((rho K).app Unit (GrCooperad.Coaug.one (R := K) (C := OrdCo K))))
  have hle : GrCooperad.unitSpan K (Koszul.Cut K (ECom K)) Unit
      ≤ K ∙ (GrCooperad.Coaug.one (R := K) (C := Koszul.Cut K (ECom K))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨e, rfl⟩
    rw [Subsingleton.elim e (Equiv.refl Unit)]
    show SymSpecies.map (R := K) (Equiv.refl Unit) _ ∈ _
    rw [SymSpecies.map_refl]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hle hmem)
  have hc := LinearMap.congr_fun
    ((Koszul.dualSub K (ECom K) (rCom K)).inclHom.comp (rho K)).counit_app
    (GrCooperad.Coaug.one (R := K) (C := OrdCo K))
  have hc' : GrCooperad.counit (R := K) (C := Koszul.Cut K (ECom K))
      ((Koszul.dualSub K (ECom K) (rCom K)).incl Unit
        ((rho K).app Unit (GrCooperad.Coaug.one (R := K) (C := OrdCo K))))
        = GrCooperad.counit (R := K) (C := OrdCo K) (GrCooperad.Coaug.one (R := K)) := hc
  rw [← ha, map_smul, GrCooperad.Coaug.counit_one, GrCooperad.Coaug.counit_one, smul_eq_mul,
    mul_one] at hc'
  rw [← ha, hc', one_smul]

/-- The orders starting with the first input, indexed by the permutations of the others. -/
noncomputable def firstOrd (n : ℕ) (π : Equiv.Perm (Fin n)) : NOrd (Fin (n + 1)) :=
  SetOperad.map ((Equiv.Perm.decomposeFin (n := n)).symm ((0 : Fin (n + 1)), π)) (sd n)

lemma firstOrd_injective (n : ℕ) : Function.Injective (firstOrd n) := fun _ _ h =>
  congrArg Prod.snd ((Equiv.Perm.decomposeFin (n := n)).symm.injective
    (LinOrd.eq_of_map_eq (congrArg Subtype.val h)))

lemma rank_firstOrd (n : ℕ) (π : Equiv.Perm (Fin n)) : (firstOrd n π).1.rank 0 = 0 := by
  have h0 : ((Equiv.Perm.decomposeFin (n := n)).symm ((0 : Fin (n + 1)), π)).symm 0 = 0 := by
    rw [Equiv.symm_apply_eq]
    exact (Equiv.Perm.decomposeFin_symm_apply_zero 0 π).symm
  have h := LinOrd.rank_map ((Equiv.Perm.decomposeFin (n := n)).symm ((0 : Fin (n + 1)), π))
    (LinOrd.std (n + 1)) 0
  rw [h0, LinOrd.rank_std] at h
  exact h

/-- The signed linear orders map onto `Com^¡`, on the standard input sets. -/
theorem rho_surjective_fin : ∀ n : ℕ, Function.Surjective ((rho K).app (Fin n))
  | 0 => fun y => by
    have hy : y = 0 := (Koszul.dualSub K (ECom K) (rCom K)).incl_injective _
      ((CutCobar.eq_zero_of_isEmpty (fun v => hredC K (Fin 0) (by simp) v) _).trans
        (map_zero _).symm)
    exact ⟨0, (map_zero _).trans hy.symm⟩
  | 1 => fun y => by
    have hmem := FreeGrL.mem_unitSpan_of_card_le (R := K) (V := GrSpecies.Shift (ECom K) K)
      (hredC K) (A := Fin 1) (by simp) ((Koszul.dualSub K (ECom K) (rCom K)).incl (Fin 1) y)
    have hle : GrCooperad.unitSpan K (Koszul.Cut K (ECom K)) (Fin 1)
        ≤ K ∙ SymSpecies.map (R := K) (Equiv.ofUnique Unit (Fin 1))
          (GrCooperad.Coaug.one (R := K) (C := Koszul.Cut K (ECom K))) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨e, rfl⟩
      rw [Subsingleton.elim e (Equiv.ofUnique Unit (Fin 1))]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hle hmem)
    refine ⟨a • SymSpecies.map (R := K) (Equiv.ofUnique Unit (Fin 1))
      (GrCooperad.Coaug.one (R := K) (C := OrdCo K)), ?_⟩
    have h1 : (rho K).app (Fin 1) (a • SymSpecies.map (R := K) (Equiv.ofUnique Unit (Fin 1))
        (GrCooperad.Coaug.one (R := K) (C := OrdCo K)))
          = a • SymSpecies.map (R := K) (Equiv.ofUnique Unit (Fin 1))
            (GrCooperad.Coaug.one (R := K) (C := Koszul.Dual K (ECom K) (rCom K))) := by
      rw [LinearMap.map_smul, (rho K).app_map, rho_one]
    exact (Koszul.dualSub K (ECom K) (rCom K)).incl_injective _ ((congrArg _ h1).trans ha)
  | n + 2 => by
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Equiv.Perm (Fin (n + 1)) →₀ K) →ₗ[K]
        Koszul.Dual K (ECom K) (rCom K) (Fin (n + 2)),
        Φ = (rho K).app (Fin (n + 2)) ∘ₗ Finsupp.lmapDomain K K (firstOrd (n + 1)) := ⟨_, rfl⟩
    have hinj : Function.Injective Φ := by
      refine (injective_iff_map_eq_zero Φ).2 fun c hc => ?_
      have hc' : (rho K).app (Fin (n + 2)) (show OrdCo K (Fin (n + 2)) from
          Finsupp.mapDomain (firstOrd (n + 1)) c) = 0 := by
        rw [hΦ] at hc
        exact hc
      have hz := rho_injective_first (n + 1) (Fin (n + 2)) (Fintype.card_fin _) 0
        (show OrdCo K (Fin (n + 2)) from Finsupp.mapDomain (firstOrd (n + 1)) c) (fun M hM => by
          by_contra hne
          refine hM (Finsupp.mapDomain_notin_range _ _ fun hr => ?_)
          obtain ⟨π, rfl⟩ := hr
          exact hne (rank_firstOrd (n + 1) π)) hc'
      exact Finsupp.mapDomain_injective (firstOrd_injective (n + 1))
        (hz.trans Finsupp.mapDomain_zero.symm)
    have hdim : Module.finrank K (Equiv.Perm (Fin (n + 1)) →₀ K)
        = Module.finrank K (Koszul.Dual K (ECom K) (rCom K) (Fin (n + 2))) := by
      rw [finrank_dual_com K (by omega), Module.finrank_finsupp_self, Fintype.card_perm,
        Fintype.card_fin]
      rfl
    haveI : Module.Finite K (Koszul.Dual K (ECom K) (rCom K) (Fin (n + 2))) :=
      Module.finite_of_finrank_pos (by
        rw [finrank_dual_com K (by omega)]
        exact Nat.factorial_pos _)
    have hsurj : Function.Surjective Φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    intro y
    obtain ⟨c, hc⟩ := hsurj y
    exact ⟨Finsupp.mapDomain (firstOrd (n + 1)) c, by rw [← hc, hΦ]; rfl⟩

/-- **The signed linear orders map onto `Com^¡`.** -/
theorem rho_surjective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Surjective ((rho K).app A) := fun y => by
  obtain ⟨x, hx⟩ := rho_surjective_fin (K := K) (Fintype.card A)
    (SymSpecies.map (R := K) (Fintype.equivFin A) y)
  refine ⟨SymSpecies.map (R := K) (Fintype.equivFin A).symm x, ?_⟩
  rw [(rho K).app_map, hx, SymSpecies.map_symm_map]

end ComDual

end Operad
