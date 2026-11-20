/-
# Twisting morphisms along an isomorphism of coaugmented cooperads

* **The inverse of a morphism of graded cooperads bijective in every arity** is a morphism of
  graded cooperads (`GrCooperadHom.symmOfBijective`).
* A morphism of graded cooperads preserving the coaugmentations preserves their spans
  (`GrCooperadHom.app_mem_unitSpan`), so **twisting morphisms pull back along it**
  (`Twisting.comap`): the parity, the vanishing on the coaugmentation and the Maurer–Cartan
  equation are preserved, precomposition being a morphism of convolution operads.
* **Twisting morphisms out of isomorphic coaugmented cooperads correspond** (`Twisting.congr`).
-/
import Operad.Twisting
import Operad.GrSubCooperad

universe u v w x

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## The inverse of a bijective morphism of graded cooperads -/

namespace GrCooperadHom

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [GrCooperad R C']

/-- **The inverse of a morphism of graded cooperads bijective in every arity.** -/
noncomputable def symmOfBijective (ψ : GrCooperadHom R C' C)
    (hψ : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (ψ.app A)) :
    GrCooperadHom R C C' where
  app A _ _ := (LinearEquiv.ofBijective (ψ.app A) (hψ A)).symm.toLinearMap
  app_map {A B} _ _ _ _ e x := (hψ B).1 (by
    have h1 : ψ.app B ((LinearEquiv.ofBijective (ψ.app B) (hψ B)).symm
        (SymSpecies.map (R := R) e x)) = SymSpecies.map (R := R) e x :=
      (LinearEquiv.ofBijective (ψ.app B) (hψ B)).apply_symm_apply _
    have h2 : ψ.app A ((LinearEquiv.ofBijective (ψ.app A) (hψ A)).symm x) = x :=
      (LinearEquiv.ofBijective (ψ.app A) (hψ A)).apply_symm_apply _
    exact h1.trans ((congrArg _ h2).symm.trans (ψ.app_map e _).symm))
  app_par {A} _ _ b x := (hψ A).1 (by
    have h1 : ψ.app A ((LinearEquiv.ofBijective (ψ.app A) (hψ A)).symm
        (GrSpecies.par (R := R) b x)) = GrSpecies.par (R := R) b x :=
      (LinearEquiv.ofBijective (ψ.app A) (hψ A)).apply_symm_apply _
    have h2 : ψ.app A ((LinearEquiv.ofBijective (ψ.app A) (hψ A)).symm x) = x :=
      (LinearEquiv.ofBijective (ψ.app A) (hψ A)).apply_symm_apply _
    exact h1.trans ((congrArg _ h2).symm.trans (ψ.app_par b _).symm))
  counit_app := LinearMap.ext fun x => by
    have h2 : ψ.app Unit ((LinearEquiv.ofBijective (ψ.app Unit) (hψ Unit)).symm x) = x :=
      (LinearEquiv.ofBijective (ψ.app Unit) (hψ Unit)).apply_symm_apply _
    have h3 := LinearMap.congr_fun ψ.counit_app
      ((LinearEquiv.ofBijective (ψ.app Unit) (hψ Unit)).symm x)
    exact h3.symm.trans (congrArg _ h2)
  decomp_app {A B} _ _ _ _ i := LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := (hψ (Without A i ⊕ B)).2 x
    have h1 : (LinearEquiv.ofBijective (ψ.app (Without A i ⊕ B)) (hψ _)).symm
        (ψ.app (Without A i ⊕ B) y) = y :=
      (LinearEquiv.ofBijective (ψ.app (Without A i ⊕ B)) (hψ _)).symm_apply_apply y
    have h2 := LinearMap.congr_fun (ψ.decomp_app (B := B) i) y
    have h3 : TensorProduct.map (LinearEquiv.ofBijective (ψ.app A) (hψ A)).symm.toLinearMap
        (LinearEquiv.ofBijective (ψ.app B) (hψ B)).symm.toLinearMap ∘ₗ
        TensorProduct.map (ψ.app A) (ψ.app B) = LinearMap.id := by
      rw [← TensorProduct.map_comp]
      have e1 : (LinearEquiv.ofBijective (ψ.app A) (hψ A)).symm.toLinearMap ∘ₗ ψ.app A
          = LinearMap.id := LinearMap.ext fun z =>
        (LinearEquiv.ofBijective (ψ.app A) (hψ A)).symm_apply_apply z
      have e2 : (LinearEquiv.ofBijective (ψ.app B) (hψ B)).symm.toLinearMap ∘ₗ ψ.app B
          = LinearMap.id := LinearMap.ext fun z =>
        (LinearEquiv.ofBijective (ψ.app B) (hψ B)).symm_apply_apply z
      rw [e1, e2, TensorProduct.map_id]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h2 ⊢
    rw [h1, h2]
    exact (LinearMap.congr_fun h3 _).symm

lemma app_symmOfBijective (ψ : GrCooperadHom R C' C)
    (hψ : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (ψ.app A))
    {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    ψ.app A ((ψ.symmOfBijective hψ).app A x) = x :=
  (LinearEquiv.ofBijective (ψ.app A) (hψ A)).apply_symm_apply x

lemma symmOfBijective_app (ψ : GrCooperadHom R C' C)
    (hψ : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (ψ.app A))
    {A : Type} [Fintype A] [DecidableEq A] (y : C' A) :
    (ψ.symmOfBijective hψ).app A (ψ.app A y) = y :=
  (LinearEquiv.ofBijective (ψ.app A) (hψ A)).symm_apply_apply y

variable [GrCooperad.Coaug R C] [GrCooperad.Coaug R C']

/-- **A morphism of graded cooperads preserving the coaugmentation preserves its span.** -/
lemma app_mem_unitSpan (ψ : GrCooperadHom R C' C)
    (h1 : ψ.app Unit (GrCooperad.Coaug.one (R := R) (C := C')) = GrCooperad.Coaug.one (R := R))
    {A : Type} [Fintype A] [DecidableEq A] {x : C' A} (hx : x ∈ GrCooperad.unitSpan R C' A) :
    ψ.app A x ∈ GrCooperad.unitSpan R C A := by
  refine (Submodule.span_le.2 ?_ : GrCooperad.unitSpan R C' A
    ≤ (GrCooperad.unitSpan R C A).comap (ψ.app A)) hx
  rintro _ ⟨e, rfl⟩
  show ψ.app A (SymSpecies.map (R := R) e (GrCooperad.Coaug.one (R := R)))
    ∈ GrCooperad.unitSpan R C A
  rw [ψ.app_map, h1]
  exact Submodule.subset_span ⟨e, rfl⟩

end GrCooperadHom

/-! ## Twisting morphisms -/

namespace Twisting

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [GrCooperad R C']
  [GrCooperad.Coaug R C']
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]

/-- **A twisting morphism pulled back along a coaugmented morphism of graded cooperads.** -/
noncomputable def comap (ψ : GrCooperadHom R C' C)
    (h1 : ψ.app Unit (GrCooperad.Coaug.one (R := R) (C := C')) = GrCooperad.Coaug.one (R := R))
    (α : Twisting R C P) : Twisting R C' P :=
  ⟨GrOperad.Inv.appHom (ConvOp.preHom ψ) α.1,
    fun A _ _ => ((ConvOp.preHom (P := P) ψ).app_par true _).symm.trans
      (congrArg _ (α.2.1 A)),
    fun A _ _ x hx => α.2.2.1 A (ψ.app A x) (ψ.app_mem_unitSpan h1 hx), by
      have h := congrArg (GrOperad.Inv.appHom (ConvOp.preHom (P := P) ψ)) α.2.2.2
      rw [map_add, GrOperad.Inv.appHom_star, map_zero] at h
      exact h⟩

lemma comap_apply (ψ : GrCooperadHom R C' C)
    (h1 : ψ.app Unit (GrCooperad.Coaug.one (R := R) (C := C')) = GrCooperad.Coaug.one (R := R))
    (α : Twisting R C P) {A : Type} [Fintype A] [DecidableEq A] (y : C' A) :
    ConvOp.toLin ((comap ψ h1 α).1.1 A) y = ConvOp.toLin (α.1.1 A) (ψ.app A y) := rfl

/-- **Twisting morphisms out of isomorphic coaugmented cooperads correspond.** -/
noncomputable def congr (ψ : GrCooperadHom R C' C)
    (hψ : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (ψ.app A))
    (h1 : ψ.app Unit (GrCooperad.Coaug.one (R := R) (C := C')) = GrCooperad.Coaug.one (R := R)) :
    Twisting R C P ≃ Twisting R C' P where
  toFun := comap ψ h1
  invFun := comap (ψ.symmOfBijective hψ) (by
    rw [← h1]
    exact ψ.symmOfBijective_app hψ _)
  left_inv α := Subtype.ext (Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    LinearMap.ext fun x => congrArg (ConvOp.toLin (α.1.1 A)) (ψ.app_symmOfBijective hψ x)))
  right_inv β := Subtype.ext (Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    LinearMap.ext fun y => congrArg (ConvOp.toLin (β.1.1 A)) (ψ.symmOfBijective_app hψ y)))

end Twisting

end Operad
