/-
# Morphisms of cooperads and transposes of morphisms of operads

* `NSCooperadHom`: morphisms of non-symmetric cooperads, families of linear maps preserving the
  counit and the decompositions.
* **The transpose of a morphism of operads with finite free components is a morphism of the dual
  cooperads**, in the other direction (`NSOperadHom.dual`). The transpose of a surjection is
  injective (`NSOperadHom.dual_injective`), so the dual of a quotient operad is a subcooperad.
-/
import Operad.DualCooperad
import Operad.Constructions

universe u v

namespace Operad

open TensorProduct Module

/-! ## Morphisms of cooperads and transposes -/

/-- A morphism of non-symmetric cooperads: a family of linear maps preserving the counit and all
infinitesimal decompositions. -/
structure NSCooperadHom (R : Type u) [CommRing R]
    (C : ℕ → Type v) [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [NSCooperad R C]
    (D : ℕ → Type v) [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)] [NSCooperad R D] where
  /-- The underlying linear map in each arity. -/
  app (n : ℕ) : C n →ₗ[R] D n
  /-- The counit is preserved. -/
  counit_app : NSCooperad.counit ∘ₗ app 1 = NSCooperad.counit
  /-- Infinitesimal decomposition is preserved. -/
  decomp_app (a b n : ℕ) :
    NSCooperad.decomp a b n ∘ₗ app (a + n + b) =
      TensorProduct.map (app (a + 1 + b)) (app n) ∘ₗ NSCooperad.decomp a b n

section Transpose

variable {R : Type u} [CommRing R] {A B A' B' : Type v}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']

/-- Transposed maps in both factors of a tensor of functionals, under the pairing. -/
lemma dualDistrib_map_dualMap (f : A →ₗ[R] A') (g : B →ₗ[R] B')
    (w : Dual R A' ⊗[R] Dual R B') :
    dualDistrib R A B (TensorProduct.map f.dualMap g.dualMap w) =
      dualDistrib R A' B' w ∘ₗ TensorProduct.map f g := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ψ =>
    refine TensorProduct.ext' fun α β => ?_
    rw [TensorProduct.map_tmul, dualDistrib_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      dualDistrib_apply]
    rfl
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, LinearMap.add_comp]

/-- The pairing of tensors of functionals is injective on finite free modules. -/
lemma dualDistrib_injective [Module.Finite R A] [Module.Free R A] [Module.Finite R B]
    [Module.Free R B] : Function.Injective (dualDistrib R A B) :=
  (dualDistribEquiv R A B).injective

end Transpose

namespace NSOperadHom

variable {R : Type u} [CommRing R]
  {P : ℕ → Type v} [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]
  {Q : ℕ → Type v} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

open NSOperad

/-- A morphism of operads commutes with partial composition on the tensor product. -/
lemma app_compT (f : NSOperadHom R P Q) (a b n : ℕ) (x : P (a + 1 + b) ⊗[R] P n) :
    f.app (a + n + b) (compT a b n x) =
      compT a b n (TensorProduct.map (f.app (a + 1 + b)) (f.app n) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul α β => rw [compT_tmul, TensorProduct.map_tmul, compT_tmul, f.app_comp]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable [∀ n, Module.Finite R (P n)] [∀ n, Module.Free R (P n)]
  [∀ n, Module.Finite R (Q n)] [∀ n, Module.Free R (Q n)]

/-- **The transpose of a morphism of operads** with finite free components is a morphism of the
dual cooperads, in the other direction. -/
noncomputable def dual (f : NSOperadHom R P Q) :
    NSCooperadHom R (DualFam R Q) (DualFam R P) where
  app n := (f.app n).dualMap
  counit_app := by
    refine LinearMap.ext fun φ => ?_
    show φ (f.app 1 (one R)) = φ (one R)
    rw [f.app_one]
  decomp_app a b n := by
    refine LinearMap.ext fun φ => dualDistrib_injective (LinearMap.ext fun x => ?_)
    show dualDistrib R _ _ (decompD a b n ((f.app (a + n + b)).dualMap φ)) x =
      dualDistrib R _ _ (TensorProduct.map (f.app (a + 1 + b)).dualMap (f.app n).dualMap
        (decompD a b n φ)) x
    rw [dualDistrib_decompD, dualDistrib_map_dualMap, LinearMap.comp_apply, dualDistrib_decompD,
      LinearMap.dualMap_apply, f.app_compT]

@[simp] lemma dual_app (f : NSOperadHom R P Q) (n : ℕ) (φ : Dual R (Q n)) (x : P n) :
    f.dual.app n φ x = φ (f.app n x) := rfl

/-- The transpose of a morphism which is surjective in an arity is injective there. -/
lemma dual_injective (f : NSOperadHom R P Q) {n : ℕ} (hf : Function.Surjective (f.app n)) :
    Function.Injective (f.dual.app n) :=
  LinearMap.dualMap_injective_of_surjective hf

end NSOperadHom

end Operad
