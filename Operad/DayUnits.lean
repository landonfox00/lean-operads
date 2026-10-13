/-
# The units of Day convolution

For monoidal categories `C` and `V`, the functors `C ⥤ V` with the Day convolution monoidal
structure form `C ⊛⥤ V` (Mathlib's `DayFunctor`), when `V` has the colimits needed for Day
convolution and its tensor product preserves them. The tensor product `F ⊗ G` comes with the unit
`η F G : F x ⊗ G y ⟶ (F ⊗ G)(x ⊗ y)` of the left Kan extension, and the monoidal unit with
`ν : 𝟙_ V ⟶ 𝟙(𝟙_ C)`. Here, the whiskerings, the associator and the unitors on these units
(`η_whiskerRight`, `η_whiskerLeft`, `η_associator`, `ν_leftUnitor`, `ν_rightUnitor`) and their
naturality (`η_naturality_right`, `η_naturality_left`).
-/
import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
import Mathlib.CategoryTheory.Monoidal.DayConvolution.Braided
import Mathlib.CategoryTheory.Monoidal.Mon

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

namespace Operad

namespace DayMonoid

open scoped ExternalProduct CategoryTheory.Prod
open DayFunctor LawfulDayConvolutionMonoidalCategoryStruct

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

/-! ## The units of the Day convolution -/

/-- **The unit of the Day convolution** at `(x, y)`, with its natural type. -/
noncomputable def ηa (F G : C ⊛⥤ V) (x y : C) :
    F.functor.obj x ⊗ G.functor.obj y ⟶ (F ⊗ G).functor.obj (x ⊗ y) :=
  (η F G).app (x, y)

@[reassoc]
lemma η_whiskerRight {F F' : C ⊛⥤ V} (f : F ⟶ F') (G : C ⊛⥤ V) (x y : C) :
    ηa F G x y ≫ (f ▷ G).natTrans.app (x ⊗ y) =
      (f.natTrans.app x ▷ G.functor.obj y) ≫ ηa F' G x y :=
  convolutionExtensionUnit_comp_ι_map_whiskerRight_app C V f G x y

@[reassoc]
lemma η_whiskerLeft (F : C ⊛⥤ V) {G G' : C ⊛⥤ V} (g : G ⟶ G') (x y : C) :
    ηa F G x y ≫ (F ◁ g).natTrans.app (x ⊗ y) =
      (F.functor.obj x ◁ g.natTrans.app y) ≫ ηa F G' x y :=
  convolutionExtensionUnit_comp_ι_map_whiskerLeft_app V F g x y

@[reassoc]
lemma η_tensorHom {F F' G G' : C ⊛⥤ V} (f : F ⟶ F') (g : G ⟶ G') (x y : C) :
    ηa F G x y ≫ (f ⊗ₘ g).natTrans.app (x ⊗ y) =
      (f.natTrans.app x ⊗ₘ g.natTrans.app y) ≫ ηa F' G' x y :=
  convolutionExtensionUnit_comp_ι_map_tensorHom_app C V f g x y

@[reassoc]
lemma η_associator (F G H : C ⊛⥤ V) (x y z : C) :
    ηa F G x y ▷ H.functor.obj z ≫ ηa (F ⊗ G) H (x ⊗ y) z ≫
        (α_ F G H).hom.natTrans.app ((x ⊗ y) ⊗ z) =
      (α_ _ _ _).hom ≫ (F.functor.obj x ◁ ηa G H y z) ≫
        ηa F (G ⊗ H) x (y ⊗ z) ≫ (F ⊗ G ⊗ H).functor.map (α_ x y z).inv :=
  associator_hom_unit_unit V F G H x y z

@[reassoc]
lemma ν_leftUnitor (F : C ⊛⥤ V) (y : C) :
    ν C V ▷ F.functor.obj y ≫ ηa (𝟙_ (C ⊛⥤ V)) F (𝟙_ C) y ≫
        (λ_ F).hom.natTrans.app (𝟙_ C ⊗ y) =
      (λ_ (F.functor.obj y)).hom ≫ F.functor.map (λ_ y).inv :=
  leftUnitor_hom_unit_app V F y

@[reassoc]
lemma ν_rightUnitor (F : C ⊛⥤ V) (y : C) :
    F.functor.obj y ◁ ν C V ≫ ηa F (𝟙_ (C ⊛⥤ V)) y (𝟙_ C) ≫
        (ρ_ F).hom.natTrans.app (y ⊗ 𝟙_ C) =
      (ρ_ (F.functor.obj y)).hom ≫ F.functor.map (ρ_ y).inv :=
  rightUnitor_hom_unit_app V F y

@[reassoc]
lemma η_naturality_right (F G : C ⊛⥤ V) {x x' : C} (f : x ⟶ x') (y : C) :
    F.functor.map f ▷ G.functor.obj y ≫ ηa F G x' y =
      ηa F G x y ≫ (F ⊗ G).functor.map (f ▷ y) := by
  simpa [ηa, tensorHom_def] using (η F G).naturality (f ×ₘ 𝟙 y)

@[reassoc]
lemma η_naturality_left (F G : C ⊛⥤ V) (x : C) {y y' : C} (g : y ⟶ y') :
    F.functor.obj x ◁ G.functor.map g ≫ ηa F G x y' =
      ηa F G x y ≫ (F ⊗ G).functor.map (x ◁ g) := by
  simpa [ηa, tensorHom_def] using (η F G).naturality (𝟙 x ×ₘ g)

/-- Natural transformations `F x ⊗ G y ⟶ H (x ⊗ y)` define maps out of the Day convolution. -/
lemma ηa_tensorDesc {F G H : C ⊛⥤ V} (α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor)
    (x y : C) : ηa F G x y ≫ (tensorDesc α).natTrans.app (x ⊗ y) = α.app (x, y) :=
  η_comp_tensorDesc_app α x y

/-- **Maps out of the Day convolution are determined on its units.** -/
lemma tensor_ext {F G H : C ⊛⥤ V} {α β : F ⊗ G ⟶ H}
    (h : ∀ x y, ηa F G x y ≫ α.natTrans.app (x ⊗ y) = ηa F G x y ≫ β.natTrans.app (x ⊗ y)) :
    α = β :=
  tensor_hom_ext h

end DayMonoid

end Operad
