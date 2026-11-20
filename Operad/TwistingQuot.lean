/-
# Twisting morphisms along a surjection of coaugmented cooperads

Over a field, for a morphism `ψ : C → D` of coaugmented graded cooperads, onto in every arity and
preserving the coaugmentations, **the twisting morphisms out of `D` are the twisting morphisms
out of `C` vanishing on the kernel of `ψ`** (`Twisting.equivOfSurjective`).

* Precomposition with `ψ` is injective (`Twisting.preHom_app_injective`,
  `Twisting.appHom_preHom_injective`).
* An invariant family vanishing on the kernel factors through `ψ` (`Twisting.exists_factor`), by
  a linear section in each arity.
* The parity, the vanishing on the coaugmentation and the Maurer–Cartan equation of the factor
  follow from those of the family (`Twisting.twisting_of_factor`), precomposition being an
  injective morphism of convolution operads.
-/
import Operad.TwistingIso

universe u v w x

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace Twisting

variable {K : Type u} [Field K]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (C A)] [GrCooperad K C]
  [GrCooperad.Coaug K C]
  {D : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (D A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (D A)] [GrCooperad K D]
  [GrCooperad.Coaug K D]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (P A)] [DGOperad K P]
  (ψ : GrCooperadHom K C D)
  (hψ : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Surjective (ψ.app A))

include hψ

omit [GrCooperad.Coaug K C] [GrCooperad.Coaug K D] in
/-- Precomposition with a surjection is injective, arity by arity. -/
lemma preHom_app_injective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective ((ConvOp.preHom (P := P) ψ).app A) := fun f g h =>
  ConvOp.ext fun y => by
    obtain ⟨x, rfl⟩ := hψ A y
    exact congrArg (fun q : ConvOp K C P A => ConvOp.toLin q x) h

omit [GrCooperad.Coaug K C] [GrCooperad.Coaug K D] in
/-- Precomposition with a surjection is injective on the invariant families. -/
lemma appHom_preHom_injective :
    Function.Injective (GrOperad.Inv.appHom (ConvOp.preHom (P := P) ψ)) := fun _ _ h =>
  Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    preHom_app_injective ψ hψ A (congrArg (fun q : GrOperad.Inv K (ConvOp K C P) => q.1 A) h))

omit [GrCooperad.Coaug K C] [GrCooperad.Coaug K D] in
/-- **An invariant family vanishing on the kernel of a surjection factors through it.** -/
theorem exists_factor (α : GrOperad.Inv K (ConvOp K C P))
    (hα : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      ψ.app A x = 0 → ConvOp.toLin (α.1 A) x = 0) :
    ∃ β : GrOperad.Inv K (ConvOp K D P), GrOperad.Inv.appHom (ConvOp.preHom ψ) β = α := by
  have hs : ∀ (A : Type) [Fintype A] [DecidableEq A],
      ∃ s : D A →ₗ[K] C A, ψ.app A ∘ₗ s = LinearMap.id := fun A _ _ =>
    (ψ.app A).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 (hψ A))
  choose s hs using hs
  have key : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      ConvOp.toLin (α.1 A) (s A (ψ.app A x)) = ConvOp.toLin (α.1 A) x := fun A _ _ x => by
    have h0 : ψ.app A (s A (ψ.app A x) - x) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact LinearMap.congr_fun (hs A) (ψ.app A x)
    have h1 := hα A _ h0
    rw [map_sub, sub_eq_zero] at h1
    exact h1
  refine ⟨⟨fun A _ _ => ConvOp.of (ConvOp.toLin (α.1 A) ∘ₗ s A), fun A B _ _ _ _ e => ?_⟩, ?_⟩
  · refine ConvOp.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hψ B y
    show GrOperad.map (R := K) e (ConvOp.toLin (α.1 A)
      (s A (SymSpecies.map (R := K) e.symm (ψ.app B x)))) = ConvOp.toLin (α.1 B) (s B (ψ.app B x))
    rw [← ψ.app_map, key, key, ← GrOperad.Inv.map_apply α e]
    rfl
  · refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun x => ?_)
    exact key A x

variable (h1 : ψ.app Unit (GrCooperad.Coaug.one (R := K) (C := C)) = GrCooperad.Coaug.one (R := K))

include h1

/-- An invariant family whose pull-back along a surjection is a twisting morphism is a twisting
morphism. -/
theorem twisting_of_factor (α : Twisting K C P) (β : GrOperad.Inv K (ConvOp K D P))
    (hβ : GrOperad.Inv.appHom (ConvOp.preHom ψ) β = α.1) :
    GrOperad.Inv.IsPar true β ∧ KillsUnit K D P β ∧
      GrOperad.Inv.appDer (ConvOp.postDer (C := D) (DGOperad.toDer (R := K) (P := P))) β
        + GrOperad.Inv.star K _ β β = 0 := by
  refine ⟨fun A _ _ => ?_, fun A _ _ y hy => ?_, ?_⟩
  · refine preHom_app_injective ψ hψ A (((ConvOp.preHom (P := P) ψ).app_par true _).trans ?_)
    have h2 := congrArg (fun q : GrOperad.Inv K (ConvOp K C P) => q.1 A) hβ
    exact (congrArg (GrOperad.par (R := K) true) h2).trans ((α.2.1 A).trans h2.symm)
  · refine (Submodule.span_le.2 ?_ : GrCooperad.unitSpan K D A
      ≤ LinearMap.ker (ConvOp.toLin (β.1 A))) hy
    rintro _ ⟨e, rfl⟩
    show ConvOp.toLin (β.1 A)
      (SymSpecies.map (R := K) e (GrCooperad.Coaug.one (R := K) (C := D))) = 0
    rw [← h1, ← ψ.app_map]
    have h2 := congrArg (fun q : GrOperad.Inv K (ConvOp K C P) => ConvOp.toLin (q.1 A)
      (SymSpecies.map (R := K) e (GrCooperad.Coaug.one (R := K) (C := C)))) hβ
    exact h2.trans (α.2.2.1 A _ (Submodule.subset_span ⟨e, rfl⟩))
  · refine appHom_preHom_injective ψ hψ ?_
    rw [map_add, GrOperad.Inv.appHom_star, map_zero]
    have h2 := α.2.2.2
    rw [← hβ] at h2
    exact h2

/-- **Twisting morphisms out of a quotient**: along a surjection of coaugmented cooperads, the
twisting morphisms out of the target are the twisting morphisms out of the source vanishing on
the kernel. -/
noncomputable def equivOfSurjective :
    Twisting K D P ≃ {α : Twisting K C P // ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      ψ.app A x = 0 → ConvOp.toLin (α.1.1 A) x = 0} where
  toFun β := ⟨comap ψ h1 β, fun A _ _ x hx => by
    show ConvOp.toLin (β.1.1 A) (ψ.app A x) = 0
    rw [hx, map_zero]⟩
  invFun α := ⟨Classical.choose (exists_factor ψ hψ α.1.1 α.2),
    twisting_of_factor ψ hψ h1 α.1 _ (Classical.choose_spec (exists_factor ψ hψ α.1.1 α.2))⟩
  left_inv β := Subtype.ext (appHom_preHom_injective ψ hψ
    (Classical.choose_spec (exists_factor ψ hψ (comap ψ h1 β).1 fun A _ _ x hx => by
      show ConvOp.toLin (β.1.1 A) (ψ.app A x) = 0
      rw [hx, map_zero])))
  right_inv α := Subtype.ext (Subtype.ext (Classical.choose_spec (exists_factor ψ hψ α.1.1 α.2)))

end Twisting

end Operad
