/-
# The linear dual of a non-symmetric operad is a cooperad

For a non-symmetric operad `P` whose components are finite free modules, the duals `P(n)*` form a
non-symmetric cooperad (`NSOperad.dualCooperad`):

* the counit evaluates a functional at the identity operation;
* the decomposition `P(a + n + b)* → P(a + 1 + b)* ⊗ P(n)*` is the transpose of partial
  composition (`NSOperad.decompD`), through the isomorphism `P(a + 1 + b)* ⊗ P(n)* ≅
  (P(a + 1 + b) ⊗ P(n))*` of finite free modules. It is characterized by
  `⟨Δφ, α ⊗ β⟩ = φ(α ∘ β)` (`NSOperad.dualDistrib_decompD`).

Each cooperad axiom is the corresponding operad axiom, read through the pairing of a triple
tensor of functionals with a triple tensor (`pairR`, `pairL`), which is injective on finite free
modules (`pairR_injective`, `pairL_injective`).

Without finiteness the transpose of composition does not land in the tensor product of the
duals, and the statement fails.
-/
import Operad.Cooperad
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FreeModule.Basic

universe u v

namespace Operad

open TensorProduct Module

/-! ## Pairings of tensors of functionals -/

section Pairing

variable {R : Type u} [CommRing R] {A B C M N : Type v}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Evaluating the second factor of a tensor of functionals at a vector. -/
lemma rid_lTensor_eval (z : Dual R M ⊗[R] Dual R N) (n₀ : N) (m : M) :
    (TensorProduct.rid R (Dual R M)) (LinearMap.lTensor (Dual R M) (Dual.eval R N n₀) z) m =
      dualDistrib R M N z (m ⊗ₜ n₀) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, LinearMap.smul_apply, dualDistrib_apply,
      Dual.eval_apply, smul_eq_mul, mul_comm]
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply]

/-- Evaluating the first factor of a tensor of functionals at a vector. -/
lemma lid_rTensor_eval (z : Dual R M ⊗[R] Dual R N) (m₀ : M) (n : N) :
    (TensorProduct.lid R (Dual R N)) (LinearMap.rTensor (Dual R N) (Dual.eval R M m₀) z) n =
      dualDistrib R M N z (m₀ ⊗ₜ n) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, LinearMap.smul_apply, dualDistrib_apply,
      Dual.eval_apply, smul_eq_mul]
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply]

variable (R A B C) in
/-- **The pairing of a right-nested triple tensor of functionals** with a triple tensor. -/
noncomputable def pairR : Dual R A ⊗[R] (Dual R B ⊗[R] Dual R C) →ₗ[R]
    Dual R (A ⊗[R] (B ⊗[R] C)) :=
  dualDistrib R A (B ⊗[R] C) ∘ₗ LinearMap.lTensor (Dual R A) (dualDistrib R B C)

variable (R A B C) in
/-- **The pairing of a left-nested triple tensor of functionals** with a triple tensor. -/
noncomputable def pairL : (Dual R A ⊗[R] Dual R B) ⊗[R] Dual R C →ₗ[R]
    Dual R ((A ⊗[R] B) ⊗[R] C) :=
  dualDistrib R (A ⊗[R] B) C ∘ₗ LinearMap.rTensor (Dual R C) (dualDistrib R A B)

lemma pairR_tmul (f : Dual R A) (w : Dual R B ⊗[R] Dual R C) (α : A) (x : B ⊗[R] C) :
    pairR R A B C (f ⊗ₜ w) (α ⊗ₜ x) = f α * dualDistrib R B C w x := by
  rw [pairR, LinearMap.comp_apply, LinearMap.lTensor_tmul, dualDistrib_apply]

lemma pairL_tmul (w : Dual R A ⊗[R] Dual R B) (h : Dual R C) (x : A ⊗[R] B) (γ : C) :
    pairL R A B C (w ⊗ₜ h) (x ⊗ₜ γ) = dualDistrib R A B w x * h γ := by
  rw [pairL, LinearMap.comp_apply, LinearMap.rTensor_tmul, dualDistrib_apply]

/-- A transposed map in the second factor, under the right-nested pairing. -/
lemma pairR_lTensor (z : Dual R A ⊗[R] Dual R N) (G : Dual R N →ₗ[R] Dual R B ⊗[R] Dual R C)
    (k : B ⊗[R] C →ₗ[R] N) (hG : ∀ ψ x, dualDistrib R B C (G ψ) x = ψ (k x)) (α : A)
    (x : B ⊗[R] C) :
    pairR R A B C (LinearMap.lTensor (Dual R A) G z) (α ⊗ₜ x) =
      dualDistrib R A N z (α ⊗ₜ k x) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f ψ => rw [LinearMap.lTensor_tmul, pairR_tmul, hG, dualDistrib_apply]
  | add z z' hz hz' => rw [map_add, map_add, LinearMap.add_apply, hz, hz', map_add,
      LinearMap.add_apply]

lemma pairR_assoc (w : Dual R A ⊗[R] Dual R B) (h : Dual R C) (α : A) (β : B) (γ : C) :
    pairR R A B C ((TensorProduct.assoc R _ _ _) (w ⊗ₜ h)) (α ⊗ₜ (β ⊗ₜ γ)) =
      dualDistrib R A B w (α ⊗ₜ β) * h γ := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    rw [TensorProduct.assoc_tmul, pairR_tmul, dualDistrib_apply, dualDistrib_apply, mul_assoc]
  | add w w' hw hw' =>
    rw [TensorProduct.add_tmul, map_add, map_add, LinearMap.add_apply, hw, hw', map_add,
      LinearMap.add_apply, add_mul]

/-- A transposed map in the first factor, reassociated, under the right-nested pairing. -/
lemma pairR_assoc_rTensor (z : Dual R M ⊗[R] Dual R C)
    (G : Dual R M →ₗ[R] Dual R A ⊗[R] Dual R B) (k : A ⊗[R] B →ₗ[R] M)
    (hG : ∀ ψ x, dualDistrib R A B (G ψ) x = ψ (k x)) (α : A) (β : B) (γ : C) :
    pairR R A B C ((TensorProduct.assoc R _ _ _) (LinearMap.rTensor (Dual R C) G z))
      (α ⊗ₜ (β ⊗ₜ γ)) = dualDistrib R M C z (k (α ⊗ₜ β) ⊗ₜ γ) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ψ h => rw [LinearMap.rTensor_tmul, pairR_assoc, hG, dualDistrib_apply]
  | add z z' hz hz' => rw [map_add, map_add, map_add, LinearMap.add_apply, hz, hz', map_add,
      LinearMap.add_apply]

/-- A transposed map in the first factor, under the left-nested pairing. -/
lemma pairL_rTensor (z : Dual R M ⊗[R] Dual R C) (G : Dual R M →ₗ[R] Dual R A ⊗[R] Dual R B)
    (k : A ⊗[R] B →ₗ[R] M) (hG : ∀ ψ x, dualDistrib R A B (G ψ) x = ψ (k x)) (x : A ⊗[R] B)
    (γ : C) :
    pairL R A B C (LinearMap.rTensor (Dual R C) G z) (x ⊗ₜ γ) =
      dualDistrib R M C z (k x ⊗ₜ γ) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ψ h => rw [LinearMap.rTensor_tmul, pairL_tmul, hG, dualDistrib_apply]
  | add z z' hz hz' => rw [map_add, map_add, LinearMap.add_apply, hz, hz', map_add,
      LinearMap.add_apply]

lemma swapLast_tmul (R : Type u) [CommRing R] {X Y Z : Type v} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] (x : X) (y : Y) (z : Z) :
    swapLast R X Y Z ((x ⊗ₜ y) ⊗ₜ z) = (x ⊗ₜ z) ⊗ₜ y := by
  simp [swapLast]

/-- Exchanging the last two factors, under the left-nested pairings. -/
lemma pairL_swapLast (w : (Dual R A ⊗[R] Dual R C) ⊗[R] Dual R B) (α : A) (β : B) (γ : C) :
    pairL R A B C (swapLast R _ _ _ w) ((α ⊗ₜ β) ⊗ₜ γ) = pairL R A C B w ((α ⊗ₜ γ) ⊗ₜ β) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul u g =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul f h =>
      rw [swapLast_tmul, pairL_tmul, pairL_tmul, dualDistrib_apply, dualDistrib_apply]
      ring
    | add u u' hu hu' =>
      rw [TensorProduct.add_tmul, map_add, map_add, LinearMap.add_apply, hu, hu', map_add,
        LinearMap.add_apply]
  | add w w' hw hw' => rw [map_add, map_add, LinearMap.add_apply, hw, hw', map_add,
      LinearMap.add_apply]

/-- Two functionals on a right-nested triple tensor product agreeing on pure tensors agree. -/
lemma dual_ext_right {φ ψ : Dual R (A ⊗[R] (B ⊗[R] C))}
    (h : ∀ α β γ, φ (α ⊗ₜ (β ⊗ₜ γ)) = ψ (α ⊗ₜ (β ⊗ₜ γ))) : φ = ψ := by
  refine TensorProduct.ext' fun α x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul β γ => exact h α β γ
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]

/-- Two functionals on a left-nested triple tensor product agreeing on pure tensors agree. -/
lemma dual_ext_left {φ ψ : Dual R ((A ⊗[R] B) ⊗[R] C)}
    (h : ∀ α β γ, φ ((α ⊗ₜ β) ⊗ₜ γ) = ψ ((α ⊗ₜ β) ⊗ₜ γ)) : φ = ψ :=
  TensorProduct.ext_threefold h

section Finite

variable [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B]
  [Module.Finite R C] [Module.Free R C]

lemma pairR_injective : Function.Injective (pairR R A B C) := by
  have h : ⇑(pairR R A B C) = ⇑(dualDistribEquiv R A (B ⊗[R] C)) ∘
      ⇑(LinearEquiv.lTensor (Dual R A) (dualDistribEquiv R B C)) := rfl
  rw [h]
  exact (dualDistribEquiv R A (B ⊗[R] C)).injective.comp (LinearEquiv.injective _)

lemma pairL_injective : Function.Injective (pairL R A B C) := by
  have h : ⇑(pairL R A B C) = ⇑(dualDistribEquiv R (A ⊗[R] B) C) ∘
      ⇑(LinearEquiv.rTensor (Dual R C) (dualDistribEquiv R A B)) := rfl
  rw [h]
  exact (dualDistribEquiv R (A ⊗[R] B) C).injective.comp (LinearEquiv.injective _)

end Finite

end Pairing

/-! ## The dual cooperad -/

namespace NSOperad

variable {R : Type u} [CommRing R] {P : ℕ → Type v} [∀ n, AddCommGroup (P n)]
  [∀ n, Module R (P n)] [NSOperad R P]

/-- **Partial composition on the tensor product.** -/
noncomputable def compT (a b n : ℕ) : P (a + 1 + b) ⊗[R] P n →ₗ[R] P (a + n + b) :=
  TensorProduct.lift (comp (R := R) a b)

@[simp] lemma compT_tmul (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) (β : P n) :
    compT a b n (α ⊗ₜ[R] β) = comp (R := R) a b α β :=
  TensorProduct.lift.tmul _ _

variable (R P) in
/-- **The linear duals** of the components of an operad. -/
abbrev DualFam (n : ℕ) : Type (max u v) := Dual R (P n)

omit [NSOperad R P] in
/-- Reindexing a functional is precomposing with the inverse reindexing. -/
lemma reindex_dual {m n : ℕ} (h : m = n) (φ : Dual R (P m)) (x : P n) :
    reindex R (DualFam R P) h φ x = φ (reindex R P h.symm x) := by
  subst h
  rfl

omit [NSOperad R P] in
/-- Reindexing the first factor of a tensor of functionals, under the pairing. -/
lemma dualDistrib_congr_reindex {m m' : ℕ} (h : m = m') {N : Type v} [AddCommGroup N]
    [Module R N] (w : Dual R (P m) ⊗[R] Dual R N) (x : P m' ⊗[R] N) :
    dualDistrib R (P m') N
        ((TensorProduct.congr (reindex R (DualFam R P) h) (LinearEquiv.refl R (Dual R N))) w) x =
      dualDistrib R (P m) N w
        (LinearMap.rTensor N (reindex R P h.symm : P m' ≃ₗ[R] P m).toLinearMap x) := by
  subst h
  have h1 : (TensorProduct.congr (reindex R (DualFam R P) (rfl : m = m))
      (LinearEquiv.refl R (Dual R N))) w = w := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => rfl
    | add w w' hw hw' => rw [map_add, hw, hw']
  have h2 : LinearMap.rTensor N (reindex R P (rfl : m = m) : P m ≃ₗ[R] P m).toLinearMap x = x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul α y => rfl
    | add x x' hx hx' => rw [map_add, hx, hx']
  rw [h1, h2]

variable [∀ n, Module.Finite R (P n)] [∀ n, Module.Free R (P n)]

/-- **The decomposition of the dual**: the transpose of partial composition. -/
noncomputable def decompD (a b n : ℕ) :
    Dual R (P (a + n + b)) →ₗ[R] Dual R (P (a + 1 + b)) ⊗[R] Dual R (P n) :=
  (dualDistribEquiv R (P (a + 1 + b)) (P n)).symm.toLinearMap ∘ₗ (compT a b n).dualMap

/-- **The decomposition pairs with a tensor as the functional with the composite.** -/
lemma dualDistrib_decompD (a b n : ℕ) (φ : Dual R (P (a + n + b)))
    (x : P (a + 1 + b) ⊗[R] P n) :
    dualDistrib R (P (a + 1 + b)) (P n) (decompD a b n φ) x = φ (compT a b n x) := by
  have h : dualDistrib R (P (a + 1 + b)) (P n) (decompD a b n φ) = (compT a b n).dualMap φ :=
    (dualDistribEquiv R (P (a + 1 + b)) (P n)).apply_symm_apply _
  rw [h, LinearMap.dualMap_apply]

/-- **The linear dual of a non-symmetric operad with finite free components is a cooperad**: the
counit evaluates at the identity, and the decomposition is the transpose of partial
composition. -/
noncomputable instance dualCooperad : NSCooperad R (DualFam R P) where
  counit := Dual.eval R (P 1) (one R)
  decomp a b n := decompD a b n
  rid_counit_decomp a b := by
    refine LinearMap.ext fun φ => LinearMap.ext fun α => ?_
    show (TensorProduct.rid R (Dual R (P (a + 1 + b))))
      (LinearMap.lTensor _ (Dual.eval R (P 1) (one R)) (decompD a b 1 φ)) α = φ α
    rw [rid_lTensor_eval, dualDistrib_decompD, compT_tmul, comp_one_right]
  lid_counit_decomp n := by
    refine LinearMap.ext fun φ => LinearMap.ext fun β => ?_
    show (TensorProduct.lid R (Dual R (P n)))
      (LinearMap.rTensor _ (Dual.eval R (P 1) (one R)) (decompD 0 0 n φ)) β =
      reindex R (DualFam R P) _ φ β
    rw [lid_rTensor_eval]
    refine (dualDistrib_decompD 0 0 n φ (one R ⊗ₜ[R] β)).trans ?_
    rw [compT_tmul, reindex_dual]
    exact congrArg φ (((reindex R P _).eq_symm_apply.2 (comp_one_left (R := R) β)).trans
      (reindex_symm_apply _ _))
  decomp_assoc_seq a b c d p := by
    refine LinearMap.ext fun φ => pairR_injective (dual_ext_right fun α β γ => ?_)
    show pairR R _ _ _ (LinearMap.lTensor _ (decompD c d p) (decompD a b (c + p + d) φ))
        (α ⊗ₜ (β ⊗ₜ γ)) =
      pairR R _ _ _ ((TensorProduct.assoc R _ _ _) (LinearMap.rTensor _
        (decompD a b (c + 1 + d) ∘ₗ (reindex R (DualFam R P)
          (show a + c + 1 + (d + b) = a + (c + 1 + d) + b by omega)).toLinearMap)
        (decompD (a + c) (d + b) p (reindex R (DualFam R P)
          (show a + (c + p + d) + b = a + c + p + (d + b) by omega) φ)))) (α ⊗ₜ (β ⊗ₜ γ))
    rw [pairR_lTensor _ _ (compT c d p) (fun ψ x => dualDistrib_decompD c d p ψ x),
      dualDistrib_decompD, compT_tmul, compT_tmul,
      pairR_assoc_rTensor _ _ ((reindex R P
          (show a + (c + 1 + d) + b = a + c + 1 + (d + b) by omega)).toLinearMap ∘ₗ
        compT a b (c + 1 + d)) (fun ψ x => by
          rw [LinearMap.comp_apply, LinearEquiv.coe_coe, dualDistrib_decompD, reindex_dual]
          rfl),
      dualDistrib_decompD, compT_tmul, reindex_dual, LinearMap.comp_apply, compT_tmul]
    exact congrArg φ (comp_assoc_seq a b c d α β γ).symm
  decomp_assoc_par a b c n p := by
    refine LinearMap.ext fun φ => pairL_injective (dual_ext_left fun α β γ => ?_)
    show pairL R _ _ _ (LinearMap.rTensor _
        (decompD a (b + 1 + c) n ∘ₗ (reindex R (DualFam R P)
          (show a + n + b + 1 + c = a + n + (b + 1 + c) by omega)).toLinearMap)
        (decompD (a + n + b) c p φ)) ((α ⊗ₜ β) ⊗ₜ γ) =
      pairL R _ _ _ (swapLast R _ _ _ (LinearMap.rTensor _
        ((TensorProduct.congr (reindex R (DualFam R P)
            (show a + 1 + b + 1 + c = a + 1 + (b + 1 + c) by omega))
          (LinearEquiv.refl R (Dual R (P p)))).toLinearMap ∘ₗ decompD (a + 1 + b) c p ∘ₗ
          (reindex R (DualFam R P)
            (show a + 1 + (b + p + c) = a + 1 + b + p + c by omega)).toLinearMap)
        (decompD a (b + p + c) n (reindex R (DualFam R P)
          (show a + n + b + p + c = a + n + (b + p + c) by omega) φ)))) ((α ⊗ₜ β) ⊗ₜ γ)
    rw [pairL_rTensor _ _ ((reindex R P
          (show a + n + (b + 1 + c) = a + n + b + 1 + c by omega)).toLinearMap ∘ₗ
        compT a (b + 1 + c) n) (fun ψ x => by
          rw [LinearMap.comp_apply, LinearEquiv.coe_coe, dualDistrib_decompD, reindex_dual]
          rfl),
      dualDistrib_decompD, compT_tmul, LinearMap.comp_apply, compT_tmul, pairL_swapLast,
      pairL_rTensor _ _ ((reindex R P
          (show a + 1 + b + p + c = a + 1 + (b + p + c) by omega)).toLinearMap ∘ₗ
        compT (a + 1 + b) c p ∘ₗ LinearMap.rTensor (P p) (reindex R P
          (show a + 1 + (b + 1 + c) = a + 1 + b + 1 + c by omega)).toLinearMap) (fun ψ x => by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
            dualDistrib_congr_reindex, dualDistrib_decompD, LinearEquiv.coe_coe, reindex_dual]
          rfl),
      dualDistrib_decompD, compT_tmul, reindex_dual, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.rTensor_tmul, compT_tmul]
    have ax := comp_assoc_par (R := R) a b c (reindex R P
      (show a + 1 + (b + 1 + c) = a + 1 + b + 1 + c by omega) α) β γ
    rw [reindex_reindex, reindex_self] at ax
    exact congrArg φ (((reindex R P _).eq_symm_apply.2 ax).trans (reindex_symm_apply _ _))

end NSOperad

end Operad
