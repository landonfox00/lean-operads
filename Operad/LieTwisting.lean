/-
# `Lie^¡` is a cooperad of alternating lines

Over a field `K` of characteristic zero, **the Koszul dual cooperad of `Lie` with the generators
`LieDual.nu` is a cooperad of alternating lines** (`LieDual.altGen`), in the sense of
`Operad/AltFamily.lean`.

* The generators alternate (`LieDual.map_nu`) and span (`LieDual.eq_smul_nu`,
  `LieDual.exists_smul_map`); `Lie^¡` vanishes on no inputs (`LieDual.eq_zero_of_isEmpty`); every
  element has the parity of its number of inputs plus one (`LieDual.par_self`); the generator on
  one input is the coaugmentation (`LieDual.nu_zero`).
* **The decomposition of an element** (`LieDual.decomp_eq`) is the multiple of the tensor of the
  generators given by a coefficient of its image in the signed linear orders: the two factors
  are lines, and `LieDual.toOrd` is a morphism of cooperads.
-/
import Operad.AltFamily

universe u w

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace LieDual

open SymPresComLie OrdCo

variable {K : Type u} [Field K] [CharZero K]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "Λ" => Koszul.Dual K (ELie K) (rLie K)

/-! ## The generators under the relabellings -/

omit [CharZero K] in
lemma exists_perm {n : ℕ} (L : NOrd (Fin (n + 1))) :
    ∃ π : Equiv.Perm (Fin (n + 1)), SetOperad.map π (sd n) = L := by
  obtain ⟨e, he⟩ := LinOrd.exists_map_eq (LinOrd.std (n + 1)) L.1 rfl
  exact ⟨e, Subtype.ext he⟩

omit [CharZero K] in
/-- **The alternating sum is alternating.** -/
lemma map_alt (n : ℕ) (τ : Equiv.Perm (Fin (n + 1))) :
    SymSpecies.map (R := K) τ (alt K n) = ((Equiv.Perm.sign τ : ℤ) : K) • alt K n := by
  refine (Finsupp.ext fun L => ?_ :
    (show NOrd (Fin (n + 1)) →₀ K from SymSpecies.map (R := K) τ (alt K n))
      = (show NOrd (Fin (n + 1)) →₀ K from ((Equiv.Perm.sign τ : ℤ) : K) • alt K n))
  obtain ⟨π, rfl⟩ := exists_perm L
  show Lin.mapL K τ (show NOrd (Fin (n + 1)) →₀ K from alt K n) (SetOperad.map π (sd n))
    = ((Equiv.Perm.sign τ : ℤ) : K)
      * (show NOrd (Fin (n + 1)) →₀ K from alt K n) (SetOperad.map π (sd n))
  rw [Lin.mapL_apply, alt_apply, ← SetOperad.map_trans]
  have h : (show NOrd (Fin (n + 1)) →₀ K from alt K n) (SetOperad.map (π.trans τ.symm) (sd n))
      = ((Equiv.Perm.sign (τ⁻¹ * π) : ℤ) : K) := alt_apply n (τ⁻¹ * π)
  rw [h, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
  push_cast
  ring

/-- **The generators of `Lie^¡` alternate.** -/
lemma map_nu (n : ℕ) (τ : Equiv.Perm (Fin (n + 1))) :
    SymSpecies.map (R := K) τ (nu K n) = ((Equiv.Perm.sign τ : ℤ) : K) • nu K n := by
  refine toOrd_injective K (Fin (n + 1)) ?_
  rw [(toOrd K).app_map, LinearMap.map_smul, toOrd_nu, map_alt]

/-- **`Lie^¡` on `n + 1` inputs is the line of its generator.** -/
lemma eq_smul_nu {n : ℕ} (y : Λ (Fin (n + 1))) : y = coef y (sd n) • nu K n := by
  refine toOrd_injective K (Fin (n + 1)) ?_
  rw [LinearMap.map_smul, toOrd_nu, toOrd_eq]

lemma exists_smul_map {n : ℕ} (e : Fin (n + 1) ≃ A) (y : Λ A) :
    ∃ c : K, y = c • SymSpecies.map (R := K) e (nu K n) := by
  refine ⟨coef (SymSpecies.map (R := K) e.symm y) (sd n), ?_⟩
  have h := congrArg (SymSpecies.map (R := K) e)
    (eq_smul_nu (SymSpecies.map (R := K) e.symm y))
  rw [← SymSpecies.map_trans, Equiv.symm_trans_self, SymSpecies.map_refl,
    LinearMap.map_smul] at h
  exact h

/-- `Lie^¡` vanishes on no inputs. -/
lemma eq_zero_of_isEmpty [IsEmpty A] (y : Λ A) : y = 0 := by
  refine toOrd_injective K A ?_
  rw [LinearMap.map_zero]
  exact (Finsupp.ext fun L => (IsEmpty.false (Classical.choice L.2)).elim :
    (show NOrd A →₀ K from (toOrd K).app A y) = 0)

/-- Every element of `Lie^¡` on a set of inputs has the parity of its number of inputs plus
one. -/
lemma par_self (y : Λ A) : GrSpecies.par (R := K) (Fintype.card A + 1).bodd y = y := by
  refine toOrd_injective K A ?_
  rw [(toOrd K).app_par]
  exact LinearMap.congr_fun (OrdCo.hom_ext
    (f := GrSpecies.par (R := K) (Fintype.card A + 1).bodd) (g := LinearMap.id) fun L => by
      rw [OrdCo.par_bs, if_pos rfl]
      rfl) _

lemma coef_nu_sd (n : ℕ) : coef (nu K n) (sd n) = 1 := by
  have h := alt_apply (K := K) n 1
  rw [show SetOperad.map (1 : Equiv.Perm (Fin (n + 1))) (sd n) = sd n from
    SetOperad.map_refl _] at h
  show (show NOrd (Fin (n + 1)) →₀ K from (toOrd K).app (Fin (n + 1)) (nu K n)) (sd n) = 1
  rw [toOrd_nu, h]
  simp

lemma coef_map_nu {n : ℕ} (e : Fin (n + 1) ≃ A) :
    coef (SymSpecies.map (R := K) e (nu K n)) (SetOperad.map e (sd n)) = 1 := by
  rw [coef_map, SetOperad.map_symm_map, coef_nu_sd]

/-! ## The decomposition of an element, on generators -/

omit [CharZero K] in
/-- A tensor of two lines is a multiple of the tensor of their generators. -/
lemma exists_smul_tmul {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {u : M} {v : N} (hu : ∀ y : M, ∃ a : K, y = a • u) (hv : ∀ y : N, ∃ a : K, y = a • v)
    (t : M ⊗[K] N) : ∃ c : K, t = c • (u ⊗ₜ[K] v) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, (zero_smul _ _).symm⟩
  | tmul x y =>
    obtain ⟨a, rfl⟩ := hu x
    obtain ⟨b, rfl⟩ := hv y
    exact ⟨a * b, by rw [TensorProduct.smul_tmul_smul]⟩
  | add s t hs ht =>
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, (add_smul _ _ _).symm⟩

omit [CharZero K] in
/-- The coefficients of the image of a multiple of a pure tensor. -/
lemma tens_map_smul {M N X Y : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] (f : M →ₗ[K] (X →₀ K)) (g : N →ₗ[K] (Y →₀ K)) (c : K) (u : M) (v : N) (p : X)
    (q : Y) {t : M ⊗[K] N} (ht : t = c • (u ⊗ₜ[K] v)) {T : (X →₀ K) ⊗[K] (Y →₀ K)}
    (hT : T = TensorProduct.map f g t) : tens K X Y T (p, q) = c * (f u p * g v q) := by
  subst ht hT
  rw [LinearMap.map_smul, TensorProduct.map_tmul, LinearEquiv.map_smul, Finsupp.smul_apply,
    tens_tmul_apply, smul_eq_mul]

/-- **The decomposition of an element of `Lie^¡`** is the multiple of the tensor of the generators
given by a coefficient of its image in the signed linear orders. -/
theorem decomp_eq (i : A) (z : Λ (Without A i ⊕ B)) {m l : ℕ} (f : Fin (m + 1) ≃ A)
    (g : Fin (l + 1) ≃ B) :
    GrCooperad.decomp (R := K) (C := Koszul.Dual K (ELie K) (rLie K)) (B := B) i z
      = (σ K (SgnData.sgn i (NOrd.sgnD.app A (SetOperad.map f (sd m)))
            (NOrd.sgnD.app B (SetOperad.map g (sd l))))
          * coef z (SetOperad.comp i (SetOperad.map f (sd m)) (SetOperad.map g (sd l)))) •
        (SymSpecies.map (R := K) f (nu K m) ⊗ₜ[K] SymSpecies.map (R := K) g (nu K l)) := by
  obtain ⟨c, hc⟩ := exists_smul_tmul (K := K) (M := Λ A) (N := Λ B)
    (u := SymSpecies.map (R := K) f (nu K m)) (v := SymSpecies.map (R := K) g (nu K l))
    (exists_smul_map f) (exists_smul_map g)
    (GrCooperad.decomp (R := K) (C := Koszul.Dual K (ELie K) (rLie K)) (B := B) i z)
  refine hc.trans ?_
  congr 1
  have h1' := (toOrd K).decomp_app (B := B) i
  have h1 := LinearMap.congr_fun h1' z
  obtain ⟨w, hw⟩ : ∃ w : NOrd (Without A i ⊕ B) →₀ K, w = (toOrd K).app (Without A i ⊕ B) z :=
    ⟨_, rfl⟩
  have key := tens_map_smul ((toOrd K).app A) ((toOrd K).app B) c
    (SymSpecies.map (R := K) f (nu K m)) (SymSpecies.map (R := K) g (nu K l))
    (SetOperad.map f (sd m)) (SetOperad.map g (sd l))
    hc (T := SgnLin.decompT K NOrd.sgnD i w) (by rw [hw]; exact h1)
  have e1 := SgnLin.decompT_apply (R := K) (δ := NOrd.sgnD) i w
    (SetOperad.map f (sd m), SetOperad.map g (sd l))
  have k2 := key.trans (congrArg₂ (fun a b : K => c * (a * b)) (coef_map_nu f) (coef_map_nu g))
  have k3 : c = σ K (SgnData.sgn i (NOrd.sgnD.app A (SetOperad.map f (sd m)))
      (NOrd.sgnD.app B (SetOperad.map g (sd l))))
        * w (SetOperad.comp i (SetOperad.map f (sd m)) (SetOperad.map g (sd l))) :=
    (by rw [mul_one, mul_one] : c = c * (1 * 1)).trans (k2.symm.trans e1)
  rw [k3, hw]
  rfl

/-! ## `Lie^¡` is a cooperad of alternating lines -/

/-- The image of the coaugmentation of `Lie^¡` is the order on one input. -/
lemma coef_one (L : NOrd Unit) :
    coef (GrCooperad.Coaug.one (R := K) (C := Koszul.Dual K (ELie K) (rLie K))) L = 1 := by
  have h := LinearMap.congr_fun (toOrd K).counit_app
    (GrCooperad.Coaug.one (R := K) (C := Koszul.Dual K (ELie K) (rLie K)))
  have h1 : GrCooperad.counit (R := K) (C := Koszul.Dual K (ELie K) (rLie K))
      (GrCooperad.Coaug.one (R := K)) = 1 := GrCooperad.Coaug.counit_one
  have hL : L = SetOperad.one := Subtype.ext (LinOrd.eq_of_subsingleton _ _)
  rw [hL]
  exact h.trans h1

/-- **The generator of `Lie^¡` on one input is the coaugmentation.** -/
theorem nu_zero : nu K 0 = SymSpecies.map (R := K) (Equiv.ofUnique Unit (Fin 1))
    (GrCooperad.Coaug.one (R := K) (C := Koszul.Dual K (ELie K) (rLie K))) := by
  have h := eq_smul_nu (SymSpecies.map (R := K) (Equiv.ofUnique Unit (Fin 1))
    (GrCooperad.Coaug.one (R := K) (C := Koszul.Dual K (ELie K) (rLie K))))
  have hc : coef (SymSpecies.map (R := K) (Equiv.ofUnique Unit (Fin 1))
      (GrCooperad.Coaug.one (R := K) (C := Koszul.Dual K (ELie K) (rLie K)))) (sd 0) = 1 := by
    rw [coef_map]
    exact coef_one _
  exact (h.trans ((congrArg (fun c : K => c • nu K 0) hc).trans (one_smul K (nu K 0)))).symm

/-- **`Lie^¡` is a cooperad of alternating lines**, with the generators `nu`. -/
theorem altGen : AltGen K (Koszul.Dual K (ELie K) (rLie K)) (nu K) where
  map_nu := map_nu
  par_self := fun _ _ _ y => par_self y
  span := fun _ _ _ _ e y => exists_smul_map e y
  empty := fun _ _ _ _ y => eq_zero_of_isEmpty y
  one := nu_zero
  decomp := fun A B _ _ _ _ i n m l e f g h => by
    have hco : coef (SymSpecies.map (R := K) e (nu K n))
        (SetOperad.comp i (SetOperad.map f (sd m)) (SetOperad.map g (sd l))) = 1 :=
      (congrArg (coef _) h).trans (coef_map_nu e)
    refine (decomp_eq i (SymSpecies.map (R := K) e (nu K n)) f g).trans ?_
    exact congrArg (fun c : K => c • (SymSpecies.map (R := K) f (nu K m)
      ⊗ₜ[K] SymSpecies.map (R := K) g (nu K l))) ((congrArg (_ * ·) hco).trans (mul_one _))

end LieDual

end Operad
