/-
# Base change of symmetric operads

For a commutative `R`-algebra `S` and a symmetric operad `P` over `R`, the modules `S ⊗[R] P A`
form a symmetric operad `BaseOp R S P` over `S`, with
`(s ⊗ x) ∘ᵢ (t ⊗ y) = st ⊗ (x ∘ᵢ y)`.

* `TensorProduct.baseChange₂`: the base change of a bilinear map.
* `BaseOp.instSymOperad`: the operad structure; `BaseOp.unit : P → BaseOp R S P`, `x ↦ 1 ⊗ x`,
  a morphism of operads over `R`.
* **The universal property** (`BaseOp.homEquiv`): morphisms of operads over `S` out of
  `BaseOp R S P` are the morphisms of operads over `R` from `P` to the restriction of scalars of
  the target.
* **Polynomials** (`BaseOp.polyIso`): `R[X] ⊗[R] P` is the operad `PolyOp R P` of polynomials with
  coefficients in `P`.
-/
import Operad.ScalarRestriction
import Operad.PolyOperad
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Polynomial.Module.TensorProduct

universe u u' v w

open TensorProduct

namespace TensorProduct

variable {R : Type u} [CommRing R] (S : Type u') [CommRing S] [Algebra R S]
  {M : Type*} {N : Type*} {L : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup L] [Module R L]

/-- **The base change of a bilinear map**: `(s ⊗ m, t ⊗ n) ↦ st ⊗ β m n`. -/
noncomputable def baseChange₂ (β : M →ₗ[R] N →ₗ[R] L) :
    S ⊗[R] M →ₗ[S] S ⊗[R] N →ₗ[S] S ⊗[R] L :=
  LinearMap.liftBaseChange S ((LinearMap.baseChangeHom R S N L).comp β)

@[simp] lemma baseChange₂_tmul (β : M →ₗ[R] N →ₗ[R] L) (s t : S) (m : M) (n : N) :
    baseChange₂ S β (s ⊗ₜ m) (t ⊗ₜ n) = (s * t) ⊗ₜ β m n := by
  rw [baseChange₂, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.baseChangeHom_apply, LinearMap.baseChange_tmul, TensorProduct.smul_tmul',
    smul_eq_mul]

end TensorProduct

namespace Operad

/-- **The base change** of the modules of an operad over `R` to a commutative `R`-algebra `S`. -/
@[nolint unusedArguments]
def BaseOp (R : Type u) (S : Type u') [CommRing R] [CommRing S] [Algebra R S]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type (max u' v) :=
  fun A _ _ => S ⊗[R] P A

variable {R : Type u} [CommRing R] {S : Type u'} [CommRing S] [Algebra R S]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]

namespace BaseOp

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (BaseOp R S P A) :=
  inferInstanceAs (AddCommGroup (S ⊗[R] P A))

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : Module S (BaseOp R S P A) :=
  inferInstanceAs (Module S (S ⊗[R] P A))

/-- **The pure tensor** `s ⊗ x`. -/
noncomputable def tmul {A : Type} [Fintype A] [DecidableEq A] (s : S) (x : P A) :
    BaseOp R S P A :=
  s ⊗ₜ[R] x

/-- **Induction on pure tensors.** -/
theorem induction {A : Type} [Fintype A] [DecidableEq A] {motive : BaseOp R S P A → Prop}
    (z : BaseOp R S P A) (zero : motive 0) (tmul : ∀ s x, motive (tmul s x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z zero tmul add

variable [SymOperad R P]

/-- Relabelling, on the base change. -/
noncomputable def mapB {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) : BaseOp R S P A →ₗ[S] BaseOp R S P B :=
  LinearMap.baseChange S (SymOperad.map (R := R) e)

/-- Composition, on the base change. -/
noncomputable def compB {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) : BaseOp R S P A →ₗ[S] BaseOp R S P B →ₗ[S] BaseOp R S P (Without A i ⊕ B) :=
  TensorProduct.baseChange₂ S (SymOperad.comp (R := R) i)

lemma mapB_tmul {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (s : S) (x : P A) :
    mapB (R := R) e (tmul s x) = tmul (R := R) s (SymOperad.map (R := R) e x) :=
  LinearMap.baseChange_tmul _ s x

lemma compB_tmul {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) (s t : S) (x : P A) (y : P B) :
    compB (R := R) i (tmul s x) (tmul t y) =
      tmul (R := R) (s * t) (SymOperad.comp (R := R) i x y) :=
  TensorProduct.baseChange₂_tmul S _ s t x y

/-- **The base change of an operad**, an operad over `S`. -/
noncomputable instance instSymOperad : SymOperad S (BaseOp R S P) where
  map e := mapB e
  map_refl x := by
    induction x using induction with
    | zero => rw [map_zero]
    | tmul s x => rw [mapB_tmul, SymOperad.map_refl]
    | add x y hx hy => rw [map_add, hx, hy]
  map_trans e f x := by
    induction x using induction with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul s x => rw [mapB_tmul, mapB_tmul, mapB_tmul, SymOperad.map_trans]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  one := tmul 1 (SymOperad.one R)
  comp i := compB i
  map_comp σ τ i x y := by
    induction x using induction with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | tmul s a =>
      induction y using induction with
      | zero => simp only [map_zero]
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | tmul t b =>
        rw [compB_tmul, mapB_tmul, mapB_tmul, mapB_tmul, compB_tmul, SymOperad.map_comp]
  comp_one i x := by
    induction x using induction with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | tmul s a => rw [compB_tmul, mapB_tmul, SymOperad.comp_one, mul_one]
  one_comp y := by
    induction y using induction with
    | zero => simp only [map_zero]
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t b => rw [compB_tmul, mapB_tmul, SymOperad.one_comp, one_mul]
  comp_assoc_seq i j x y z := by
    induction x using induction with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | tmul s a =>
      induction y using induction with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | tmul t b =>
        induction z using induction with
        | zero => simp only [map_zero]
        | add z z' hz hz' => simp only [map_add, hz, hz']
        | tmul r c =>
          rw [compB_tmul, compB_tmul, mapB_tmul, compB_tmul, compB_tmul,
            SymOperad.comp_assoc_seq, mul_assoc]
  comp_assoc_par hik x y z := by
    induction x using induction with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | tmul s a =>
      induction y using induction with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | tmul t b =>
        induction z using induction with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
        | tmul r c =>
          rw [compB_tmul, compB_tmul, mapB_tmul, compB_tmul, compB_tmul,
            SymOperad.comp_assoc_par hik, mul_right_comm]

lemma map_tmul {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (s : S) (x : P A) :
    SymOperad.map (R := S) (P := BaseOp R S P) e (tmul s x) =
      tmul (R := R) s (SymOperad.map (R := R) e x) :=
  mapB_tmul e s x

lemma comp_tmul {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) (s t : S) (x : P A) (y : P B) :
    SymOperad.comp (R := S) (P := BaseOp R S P) i (tmul s x) (tmul t y) =
      tmul (R := R) (s * t) (SymOperad.comp (R := R) i x y) :=
  compB_tmul i s t x y

lemma one_def : (SymOperad.one S : BaseOp R S P Unit) = tmul 1 (SymOperad.one R) := rfl

end BaseOp

/-! ## The universal property -/

namespace BaseOp

variable [SymOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module S (Q A)] [SymOperad S Q]

variable (R S P) in
/-- **The unit of base change**: `x ↦ 1 ⊗ x`, a morphism of operads over `R` from `P` to its
base change. -/
noncomputable def unit : SymOperadHom R P (ResOp R S (BaseOp R S P)) where
  app A _ _ :=
    { toFun := fun x => tmul (R := R) (S := S) 1 x
      map_add' := fun x y => TensorProduct.tmul_add _ _ _
      map_smul' := fun r x => by
        show (1 : S) ⊗ₜ[R] (r • x) = algebraMap R S r • ((1 : S) ⊗ₜ[R] x)
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
          Algebra.algebraMap_eq_smul_one] }
  app_map e x := (map_tmul e 1 x).symm
  app_one := rfl
  app_comp i x y := by
    show tmul (R := R) (S := S) 1 (SymOperad.comp (R := R) i x y) =
      SymOperad.comp (R := S) (P := BaseOp R S P) i (tmul 1 x) (tmul 1 y)
    rw [comp_tmul, mul_one]

lemma unit_app {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    (unit R S P).app A x = tmul (R := R) (S := S) 1 x := rfl

omit [Algebra R S] in
/-- Scalars come out of a composite. -/
lemma smul_comp_smul {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) (s t : S) (u : Q A) (v : Q B) :
    (s * t) • SymOperad.comp (R := S) (P := Q) i u v =
      SymOperad.comp (R := S) (P := Q) i (s • u) (t • v) := by
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, mul_comm]

/-- **The lift** of a morphism of operads over `R` into an operad over `S`: `s ⊗ x ↦ s • f x`. -/
noncomputable def lift (f : SymOperadHom R P (ResOp R S Q)) : SymOperadHom S (BaseOp R S P) Q where
  app A _ _ := (LinearMap.liftBaseChange S (f.app A) : S ⊗[R] P A →ₗ[S] ResOp R S Q A)
  app_map e z := by
    induction z using induction with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s x =>
      rw [map_tmul]
      show s • f.app _ (SymOperad.map (R := R) e x) =
        SymOperad.map (R := S) (P := Q) e (s • f.app _ x)
      exact (congrArg (s • ·) (f.app_map e x)).trans
        (map_smul (SymOperad.map (R := S) (P := Q) e) s _).symm
  app_one := by
    show (1 : S) • f.app Unit (SymOperad.one R) = _
    rw [one_smul, f.app_one]
    rfl
  app_comp i x y := by
    induction x using induction with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | tmul s a =>
      induction y using induction with
      | zero => simp only [map_zero]
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | tmul t b =>
        rw [comp_tmul]
        show (s * t) • f.app _ (SymOperad.comp (R := R) i a b) =
          SymOperad.comp (R := S) (P := Q) i (s • f.app _ a) (t • f.app _ b)
        exact (congrArg ((s * t) • ·) (f.app_comp i a b)).trans
          (smul_comp_smul (Q := Q) i s t _ _)

lemma lift_tmul (f : SymOperadHom R P (ResOp R S Q)) {A : Type} [Fintype A] [DecidableEq A]
    (s : S) (x : P A) : (lift f).app A (tmul s x) = s • f.app A x := rfl

/-- **The universal property of base change**: a morphism of operads over `S` out of the base
change of `P` is a morphism of operads over `R` from `P` to the target with its scalars
restricted. -/
noncomputable def homEquiv :
    SymOperadHom S (BaseOp R S P) Q ≃ SymOperadHom R P (ResOp R S Q) where
  toFun F := (F.res R).comp (unit R S P)
  invFun := lift
  left_inv F := SymOperadHom.ext fun A _ _ z => by
    induction z using induction with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s x =>
      rw [lift_tmul]
      show s • F.app A (tmul 1 x) = F.app A (tmul s x)
      rw [← map_smul]
      exact congrArg _ (by
        show s • ((1 : S) ⊗ₜ[R] x) = s ⊗ₜ[R] x
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one])
  right_inv f := SymOperadHom.ext fun A _ _ x => one_smul S (f.app A x)

lemma homEquiv_apply (F : SymOperadHom S (BaseOp R S P) Q) {A : Type} [Fintype A]
    [DecidableEq A] (x : P A) : (homEquiv F).app A x = F.app A (tmul 1 x) := rfl

lemma homEquiv_symm_tmul (f : SymOperadHom R P (ResOp R S Q)) {A : Type} [Fintype A]
    [DecidableEq A] (s : S) (x : P A) : (homEquiv.symm f).app A (tmul s x) = s • f.app A x := rfl

end BaseOp

/-! ## Polynomials -/

namespace PolyOp

open Polynomial

variable [SymOperad R P]

variable (R P) in
/-- **The constant polynomials**: `x ↦ x ħ⁰`, a morphism of operads over `R`. -/
noncomputable def const : SymOperadHom R P (ResOp R R[X] (PolyOp R P)) where
  app A _ _ :=
    { toFun := fun x => single (R := R) 0 x
      map_add' := fun x y => map_add (PolynomialModule.single R 0) x y
      map_smul' := fun r x => by
        show PolynomialModule.single R 0 (r • x) =
          algebraMap R R[X] r • PolynomialModule.single R 0 x
        rw [← Polynomial.C_eq_algebraMap, ← Polynomial.monomial_zero_left,
          PolynomialModule.monomial_smul_single, zero_add] }
  app_map e x := (map_single e 0 x).symm
  app_one := rfl
  app_comp i x y := by
    show single (R := R) 0 (SymOperad.comp (R := R) i x y) =
      SymOperad.comp (R := R[X]) (P := PolyOp R P) i (single 0 x) (single 0 y)
    rw [comp_single, add_zero]

end PolyOp

namespace BaseOp

open Polynomial

variable [SymOperad R P]

/-- The lift of the constant polynomials is the equivalence of mathlib between
`R[X] ⊗[R] M` and the polynomial module. -/
lemma lift_const_app {A : Type} [Fintype A] [DecidableEq A] (z : BaseOp R R[X] P A) :
    (lift (PolyOp.const R P)).app A z =
      PolynomialModule.polynomialTensorProductLEquivPolynomialModule R (P A) z := by
  induction z using induction with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  | tmul s x => rfl

/-- **The base change to `R[X]` is the operad of polynomials**: `R[X] ⊗[R] P ≅ PolyOp R P`, an
isomorphism of operads over `R[X]`. -/
noncomputable def polyIso : SymOperadIso R[X] (BaseOp R R[X] P) (PolyOp R P) :=
  SymOperadIso.ofBijective (lift (PolyOp.const R P)) fun A _ _ => by
    have h : ⇑((lift (PolyOp.const R P)).app A) =
        ⇑(PolynomialModule.polynomialTensorProductLEquivPolynomialModule R (P A)) :=
      funext lift_const_app
    rw [h]
    exact (PolynomialModule.polynomialTensorProductLEquivPolynomialModule R (P A)).bijective

lemma polyIso_tmul {A : Type} [Fintype A] [DecidableEq A] (s : R[X]) (x : P A) :
    polyIso.hom.app A (tmul s x) = s • PolyOp.single (R := R) 0 x := rfl

end BaseOp

end Operad
