/-
# Monoids for Day convolution are lax monoidal functors

For monoidal categories `C` and `V`, the functors `C ⥤ V` with the Day convolution monoidal
structure form `C ⊛⥤ V` (Mathlib's `DayFunctor`), when `V` has the colimits defining Day
convolution and its tensor product preserves them. **A monoid for Day convolution is the same as a
lax monoidal functor** (Day): by the universal property of `F ⊗ F` as a left Kan extension, a
multiplication `F ⊗ F ⟶ F` is a natural family `F x ⊗ F y ⟶ F (x ⊗ y)`, and a unit
`𝟙 ⟶ F` is a map `𝟙_ V ⟶ F (𝟙_ C)`.

* `laxMonoidalOfMonObj` — the tensorator `μF` of a monoid is the unit of the Day convolution
  followed by the multiplication, and its unit `εF` is the unit of the Day unit followed by the
  unit of the monoid; the axioms of a lax monoidal functor are those of the monoid read on the
  units (`μF_assoc`, `μF_left_unitality`, `μF_right_unitality`).
* `monObjOfLaxMonoidal` — conversely the multiplication and the unit are induced by the
  tensorator and the unit (`mulL`, `oneL`); maps out of `(F ⊗ G) ⊗ H` are determined on the
  double units (`tensor₂_ext`), the tensor product of `V` preserving the colimits
  (`tensorRight_ext`).
* `monObjEquivLaxMonoidal` — **the two are inverse**, and **morphisms of monoids are the monoidal
  natural transformations** (`isMonHom_iff`).
* For `C` symmetric and `V` braided, **a monoid is commutative for the braiding of the Day
  convolution exactly when its tensorator commutes with the braidings** (`isCommDay_iff`): the
  commutative monoids are the lax braided (symmetric) functors (`laxBraidedOfCommDay`,
  `isCommDay_of_laxBraided`).
-/
import Operad.DayUnits

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

namespace Operad

namespace DayMonoid

open scoped ExternalProduct CategoryTheory.Prod
open DayFunctor LawfulDayConvolutionMonoidalCategoryStruct

section Generic

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]

lemma laxMonoidal_ext {G : C ⥤ V} {L L' : G.LaxMonoidal}
    (hε : @Functor.LaxMonoidal.ε _ _ _ _ _ _ G L = @Functor.LaxMonoidal.ε _ _ _ _ _ _ G L')
    (hμ : ∀ x y, @Functor.LaxMonoidal.μ _ _ _ _ _ _ G L x y =
      @Functor.LaxMonoidal.μ _ _ _ _ _ _ G L' x y) : L = L' := by
  rcases L with ⟨ε, μ, _, _, _, _, _⟩
  rcases L' with ⟨ε', μ', _, _, _, _, _⟩
  obtain rfl : ε = ε' := hε
  obtain rfl : μ = μ' := funext fun x => funext fun y => hμ x y
  rfl

end Generic

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


section Forward

variable (F : C ⊛⥤ V) [MonObj F]

/-- **The tensorator of a Day monoid**. -/
noncomputable def μF (x y : C) : F.functor.obj x ⊗ F.functor.obj y ⟶ F.functor.obj (x ⊗ y) :=
  ηa F F x y ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans.app (x ⊗ y)

/-- **The unit of a Day monoid**. -/
noncomputable def εF : 𝟙_ V ⟶ F.functor.obj (𝟙_ C) :=
  ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ F).natTrans.app (𝟙_ C)

@[reassoc]
lemma mul_naturality {a b : C} (f : a ⟶ b) :
    (F ⊗ F).functor.map f ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans.app b =
      (MonObj.mul : F ⊗ F ⟶ F).natTrans.app a ≫ F.functor.map f :=
  (MonObj.mul : F ⊗ F ⟶ F).natTrans.naturality f

lemma μF_natural_left {x x' : C} (f : x ⟶ x') (y : C) :
    F.functor.map f ▷ F.functor.obj y ≫ μF F x' y = μF F x y ≫ F.functor.map (f ▷ y) := by
  simp only [μF, η_naturality_right_assoc, mul_naturality, Category.assoc]

lemma μF_natural_right (x : C) {y y' : C} (g : y ⟶ y') :
    F.functor.obj x ◁ F.functor.map g ≫ μF F x y' = μF F x y ≫ F.functor.map (x ◁ g) := by
  simp only [μF, η_naturality_left_assoc, mul_naturality, Category.assoc]

lemma μF_assoc (x y z : C) :
    μF F x y ▷ F.functor.obj z ≫ μF F (x ⊗ y) z ≫ F.functor.map (α_ x y z).hom =
      (α_ _ _ _).hom ≫ F.functor.obj x ◁ μF F y z ≫ μF F x (y ⊗ z) := by
  have hassoc := congrArg (fun φ => φ.natTrans.app ((x ⊗ y) ⊗ z)) (MonObj.mul_assoc F)
  simp only [comp_natTrans, NatTrans.comp_app] at hassoc
  have hnat := (((F ◁ (MonObj.mul : F ⊗ F ⟶ F)) ≫ MonObj.mul).natTrans.naturality
    (α_ x y z).inv)
  simp only [comp_natTrans, NatTrans.comp_app] at hnat
  calc μF F x y ▷ F.functor.obj z ≫ μF F (x ⊗ y) z ≫ F.functor.map (α_ x y z).hom
      = ηa F F x y ▷ F.functor.obj z ≫ ηa (F ⊗ F) F (x ⊗ y) z ≫
          ((MonObj.mul : F ⊗ F ⟶ F) ▷ F).natTrans.app ((x ⊗ y) ⊗ z) ≫
          (MonObj.mul : F ⊗ F ⟶ F).natTrans.app ((x ⊗ y) ⊗ z) ≫
          F.functor.map (α_ x y z).hom := by
        rw [η_whiskerRight_assoc]
        simp only [μF, comp_whiskerRight, Category.assoc]
    _ = (α_ _ _ _).hom ≫ F.functor.obj x ◁ ηa F F y z ≫ ηa F (F ⊗ F) x (y ⊗ z) ≫
          (F ⊗ F ⊗ F).functor.map (α_ x y z).inv ≫
          (F ◁ (MonObj.mul : F ⊗ F ⟶ F)).natTrans.app ((x ⊗ y) ⊗ z) ≫
          (MonObj.mul : F ⊗ F ⟶ F).natTrans.app ((x ⊗ y) ⊗ z) ≫
          F.functor.map (α_ x y z).hom := by
        rw [reassoc_of% hassoc, η_associator_assoc]
    _ = (α_ _ _ _).hom ≫ F.functor.obj x ◁ ηa F F y z ≫ ηa F (F ⊗ F) x (y ⊗ z) ≫
          (F ◁ (MonObj.mul : F ⊗ F ⟶ F)).natTrans.app (x ⊗ y ⊗ z) ≫
          (MonObj.mul : F ⊗ F ⟶ F).natTrans.app (x ⊗ y ⊗ z) := by
        rw [reassoc_of% hnat]
        simp only [← F.functor.map_comp, Iso.inv_hom_id, F.functor.map_id, Category.comp_id]
    _ = _ := by
        rw [η_whiskerLeft_assoc]
        simp only [μF, MonoidalCategory.whiskerLeft_comp, Category.assoc]

lemma μF_left_unitality (y : C) :
    (λ_ (F.functor.obj y)).hom = εF F ▷ F.functor.obj y ≫ μF F (𝟙_ C) y ≫
      F.functor.map (λ_ y).hom := by
  have hone := congrArg (fun φ => φ.natTrans.app (𝟙_ C ⊗ y)) (MonObj.one_mul F)
  simp only [comp_natTrans, NatTrans.comp_app] at hone
  calc (λ_ (F.functor.obj y)).hom =
      ((λ_ (F.functor.obj y)).hom ≫ F.functor.map (λ_ y).inv) ≫ F.functor.map (λ_ y).hom := by
        rw [Category.assoc, ← F.functor.map_comp, Iso.inv_hom_id, F.functor.map_id,
          Category.comp_id]
    _ = _ := by
        rw [← ν_leftUnitor, ← hone]
        simp only [εF, μF, comp_whiskerRight, Category.assoc, η_whiskerRight_assoc]

lemma μF_right_unitality (y : C) :
    (ρ_ (F.functor.obj y)).hom = F.functor.obj y ◁ εF F ≫ μF F y (𝟙_ C) ≫
      F.functor.map (ρ_ y).hom := by
  have hone := congrArg (fun φ => φ.natTrans.app (y ⊗ 𝟙_ C)) (MonObj.mul_one F)
  simp only [comp_natTrans, NatTrans.comp_app] at hone
  calc (ρ_ (F.functor.obj y)).hom =
      ((ρ_ (F.functor.obj y)).hom ≫ F.functor.map (ρ_ y).inv) ≫ F.functor.map (ρ_ y).hom := by
        rw [Category.assoc, ← F.functor.map_comp, Iso.inv_hom_id, F.functor.map_id,
          Category.comp_id]
    _ = _ := by
        rw [← ν_rightUnitor, ← hone]
        simp only [εF, μF, MonoidalCategory.whiskerLeft_comp, Category.assoc,
          η_whiskerLeft_assoc]

/-- **The lax monoidal functor of a monoid for Day convolution.** -/
@[implicit_reducible]
noncomputable def laxMonoidalOfMonObj : F.functor.LaxMonoidal where
  ε := εF F
  μ := μF F
  μ_natural_left f y := μF_natural_left F f y
  μ_natural_right x g := μF_natural_right F x g
  associativity x y z := μF_assoc F x y z
  left_unitality y := μF_left_unitality F y
  right_unitality y := μF_right_unitality F y

end Forward

/-- **Maps out of `(F ⊗ G)(a) ⊗ v` are determined on the units**, the tensor product of `V`
preserving the colimits defining the Day convolution. -/
lemma tensorRight_ext {F G : C ⊛⥤ V} (a : C) (v : V) {W : V}
    {g h : (F ⊗ G).functor.obj a ⊗ v ⟶ W}
    (H : ∀ (x y : C) (u : x ⊗ y ⟶ a), (ηa F G x y ≫ (F ⊗ G).functor.map u) ▷ v ≫ g =
      (ηa F G x y ≫ (F ⊗ G).functor.map u) ▷ v ≫ h) :
    g = h := by
  have hP := (isPointwiseLeftKanExtensionConvolutionExtensionUnit (C := C) (V := V) F G) a
  have hQ := Limits.isColimitOfPreserves (tensorRight v) hP
  refine hQ.hom_ext fun j => ?_
  simpa [ηa] using H j.left.1 j.left.2 j.hom

/-- **Maps out of `(F ⊗ G) ⊗ H` are determined on the double units.** -/
lemma tensor₂_ext {F G H K : C ⊛⥤ V} {α β : (F ⊗ G) ⊗ H ⟶ K}
    (h : ∀ x y z, ηa F G x y ▷ H.functor.obj z ≫ ηa (F ⊗ G) H (x ⊗ y) z ≫
        α.natTrans.app ((x ⊗ y) ⊗ z) =
      ηa F G x y ▷ H.functor.obj z ≫ ηa (F ⊗ G) H (x ⊗ y) z ≫
        β.natTrans.app ((x ⊗ y) ⊗ z)) : α = β := by
  refine tensor_ext fun a z => tensorRight_ext a (H.functor.obj z) fun x y u => ?_
  rw [comp_whiskerRight_assoc, comp_whiskerRight_assoc, η_naturality_right_assoc,
    η_naturality_right_assoc, α.natTrans.naturality, β.natTrans.naturality, reassoc_of% (h x y z)]

section Backward

variable (F : C ⊛⥤ V) [F.functor.LaxMonoidal]

/-- The tensorator, as a natural transformation. -/
noncomputable def μNat : F.functor ⊠ F.functor ⟶ tensor C ⋙ F.functor where
  app p := Functor.LaxMonoidal.μ F.functor p.1 p.2
  naturality p q f := by
    simp [tensorHom_def]

/-- The multiplication of the lax monoidal functor. -/
noncomputable def mulL : F ⊗ F ⟶ F := tensorDesc (μNat F)

/-- The unit of the lax monoidal functor. -/
noncomputable def oneL : 𝟙_ (C ⊛⥤ V) ⟶ F := unitDesc (Functor.LaxMonoidal.ε F.functor)

@[reassoc]
lemma ηa_mulL (x y : C) :
    ηa F F x y ≫ (mulL F).natTrans.app (x ⊗ y) = Functor.LaxMonoidal.μ F.functor x y :=
  ηa_tensorDesc _ x y

@[reassoc]
lemma ν_oneL : ν C V ≫ (oneL F).natTrans.app (𝟙_ C) = Functor.LaxMonoidal.ε F.functor :=
  ν_comp_unitDesc _

lemma oneL_mul : oneL F ▷ F ≫ mulL F = (λ_ F).hom := by
  ext y
  simp only [comp_natTrans, NatTrans.comp_app]
  set s := (λ_ (F.functor.obj y)).inv ≫ ν C V ▷ F.functor.obj y ≫
    ηa (𝟙_ (C ⊛⥤ V)) F (𝟙_ C) y ≫ (𝟙_ (C ⊛⥤ V) ⊗ F).functor.map (λ_ y).hom with hsdef
  have hl : (λ_ F).hom.natTrans.app y ≫ (λ_ F).inv.natTrans.app y = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← comp_natTrans, Iso.hom_inv_id]
    rfl
  have hs : s ≫ (λ_ F).hom.natTrans.app y = 𝟙 _ := by
    rw [hsdef]
    simp only [Category.assoc]
    rw [(λ_ F).hom.natTrans.naturality (λ_ y).hom, ν_leftUnitor_assoc, ← F.functor.map_comp,
      Iso.inv_hom_id, F.functor.map_id, Category.comp_id, Iso.inv_hom_id]
  have hs' : s = (λ_ F).inv.natTrans.app y := by
    rw [← Category.comp_id s, ← hl, ← Category.assoc, hs, Category.id_comp]
  have hg : s ≫ (oneL F ▷ F).natTrans.app y ≫ (mulL F).natTrans.app y = 𝟙 _ := by
    have hnat := ((oneL F ▷ F) ≫ mulL F).natTrans.naturality (λ_ y).hom
    simp only [comp_natTrans, NatTrans.comp_app] at hnat
    rw [hsdef]
    simp only [Category.assoc]
    rw [hnat]
    simp only [Category.assoc]
    rw [η_whiskerRight_assoc, ηa_mulL_assoc, ← comp_whiskerRight_assoc, ν_oneL,
      ← Functor.LaxMonoidal.left_unitality, Iso.inv_hom_id]
  calc (oneL F ▷ F).natTrans.app y ≫ (mulL F).natTrans.app y
      = ((λ_ F).hom.natTrans.app y ≫ s) ≫ (oneL F ▷ F).natTrans.app y ≫
          (mulL F).natTrans.app y := by rw [hs', hl, Category.id_comp]
    _ = (λ_ F).hom.natTrans.app y := by rw [Category.assoc, hg, Category.comp_id]

lemma mul_oneL : F ◁ oneL F ≫ mulL F = (ρ_ F).hom := by
  ext y
  simp only [comp_natTrans, NatTrans.comp_app]
  set s := (ρ_ (F.functor.obj y)).inv ≫ F.functor.obj y ◁ ν C V ≫
    ηa F (𝟙_ (C ⊛⥤ V)) y (𝟙_ C) ≫ (F ⊗ 𝟙_ (C ⊛⥤ V)).functor.map (ρ_ y).hom with hsdef
  have hρ : (ρ_ F).hom.natTrans.app y ≫ (ρ_ F).inv.natTrans.app y = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← comp_natTrans, Iso.hom_inv_id]
    rfl
  have hs : s ≫ (ρ_ F).hom.natTrans.app y = 𝟙 _ := by
    rw [hsdef]
    simp only [Category.assoc]
    rw [(ρ_ F).hom.natTrans.naturality (ρ_ y).hom, ν_rightUnitor_assoc, ← F.functor.map_comp,
      Iso.inv_hom_id, F.functor.map_id, Category.comp_id, Iso.inv_hom_id]
  have hs' : s = (ρ_ F).inv.natTrans.app y := by
    rw [← Category.comp_id s, ← hρ, ← Category.assoc, hs, Category.id_comp]
  have hg : s ≫ (F ◁ oneL F).natTrans.app y ≫ (mulL F).natTrans.app y = 𝟙 _ := by
    have hnat := ((F ◁ oneL F) ≫ mulL F).natTrans.naturality (ρ_ y).hom
    simp only [comp_natTrans, NatTrans.comp_app] at hnat
    rw [hsdef]
    simp only [Category.assoc]
    rw [hnat]
    simp only [Category.assoc]
    rw [η_whiskerLeft_assoc, ηa_mulL_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ν_oneL, ← Functor.LaxMonoidal.right_unitality, Iso.inv_hom_id]
  calc (F ◁ oneL F).natTrans.app y ≫ (mulL F).natTrans.app y
      = ((ρ_ F).hom.natTrans.app y ≫ s) ≫ (F ◁ oneL F).natTrans.app y ≫
          (mulL F).natTrans.app y := by rw [hs', hρ, Category.id_comp]
    _ = (ρ_ F).hom.natTrans.app y := by rw [Category.assoc, hg, Category.comp_id]

lemma mulL_assoc : mulL F ▷ F ≫ mulL F = (α_ F F F).hom ≫ F ◁ mulL F ≫ mulL F := by
  refine tensor₂_ext fun x y z => ?_
  have hnat := ((F ◁ mulL F) ≫ mulL F).natTrans.naturality (α_ x y z).inv
  simp only [comp_natTrans, NatTrans.comp_app] at hnat ⊢
  rw [η_whiskerRight_assoc, ← comp_whiskerRight_assoc, ηa_mulL, ηa_mulL, η_associator_assoc,
    hnat]
  simp only [Category.assoc]
  rw [η_whiskerLeft_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ηa_mulL, ηa_mulL_assoc,
    ← Functor.LaxMonoidal.associativity_assoc, ← F.functor.map_comp, Iso.hom_inv_id,
    F.functor.map_id, Category.comp_id]

/-- **The monoid for Day convolution of a lax monoidal functor.** -/
@[implicit_reducible]
noncomputable def monObjOfLaxMonoidal : MonObj F where
  one := oneL F
  mul := mulL F
  one_mul := oneL_mul F
  mul_one := mul_oneL F
  mul_assoc := mulL_assoc F

end Backward

/-! ## The dictionary -/

lemma monObj_ext {F : C ⊛⥤ V} {M M' : MonObj F}
    (hone : @MonObj.one _ _ _ F M = @MonObj.one _ _ _ F M')
    (hmul : @MonObj.mul _ _ _ F M = @MonObj.mul _ _ _ F M') : M = M' := by
  rcases M with ⟨one, mul, _, _, _⟩
  rcases M' with ⟨one', mul', _, _, _⟩
  obtain rfl : one = one' := hone
  obtain rfl : mul = mul' := hmul
  rfl

/-- **Monoids for Day convolution are lax monoidal functors** (Day). -/
noncomputable def monObjEquivLaxMonoidal (F : C ⊛⥤ V) : MonObj F ≃ F.functor.LaxMonoidal where
  toFun M := letI := M; laxMonoidalOfMonObj F
  invFun L := letI := L; monObjOfLaxMonoidal F
  left_inv M := by
    letI := M
    letI : F.functor.LaxMonoidal := laxMonoidalOfMonObj F
    refine monObj_ext ?_ ?_
    · show oneL F = MonObj.one
      exact unit_hom_ext (ν_comp_unitDesc _)
    · show mulL F = MonObj.mul
      exact tensor_ext fun x y => ηa_tensorDesc _ x y
  right_inv L := by
    letI := L
    refine laxMonoidal_ext ?_ fun x y => ?_
    · exact ν_comp_unitDesc _
    · exact ηa_tensorDesc _ x y

/-- **The tensorator of the lax monoidal functor of a monoid** is the multiplication on the
units of the Day convolution. -/
lemma monObjEquivLaxMonoidal_μ (F : C ⊛⥤ V) (M : MonObj F) (x y : C) :
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ F.functor (monObjEquivLaxMonoidal F M) x y =
      ηa F F x y ≫ (@MonObj.mul _ _ _ F M).natTrans.app (x ⊗ y) := rfl

/-- **Its unit** is the unit of the monoid on the unit of the Day unit. -/
lemma monObjEquivLaxMonoidal_ε (F : C ⊛⥤ V) (M : MonObj F) :
    @Functor.LaxMonoidal.ε _ _ _ _ _ _ F.functor (monObjEquivLaxMonoidal F M) =
      ν C V ≫ (@MonObj.one _ _ _ F M).natTrans.app (𝟙_ C) := rfl

/-- **Morphisms of monoids are monoidal natural transformations.** -/
theorem isMonHom_iff {M N : C ⊛⥤ V} [MonObj M] [MonObj N] (f : M ⟶ N) :
    IsMonHom f ↔ @NatTrans.IsMonoidal _ _ _ _ _ _ M.functor N.functor f.natTrans
      (laxMonoidalOfMonObj M) (laxMonoidalOfMonObj N) := by
  letI := laxMonoidalOfMonObj M
  letI := laxMonoidalOfMonObj N
  constructor
  · intro hf
    refine ⟨?_, fun x y => ?_⟩
    · show (ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ M).natTrans.app (𝟙_ C)) ≫
          f.natTrans.app (𝟙_ C) = ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ N).natTrans.app (𝟙_ C)
      rw [Category.assoc, ← NatTrans.comp_app, ← comp_natTrans, IsMonHom.one_hom]
    · show (ηa M M x y ≫ (MonObj.mul : M ⊗ M ⟶ M).natTrans.app (x ⊗ y)) ≫
          f.natTrans.app (x ⊗ y) = (f.natTrans.app x ⊗ₘ f.natTrans.app y) ≫
          ηa N N x y ≫ (MonObj.mul : N ⊗ N ⟶ N).natTrans.app (x ⊗ y)
      rw [Category.assoc, ← NatTrans.comp_app, ← comp_natTrans, IsMonHom.mul_hom,
        comp_natTrans, NatTrans.comp_app, η_tensorHom_assoc]
  · intro hf
    refine ⟨?_, ?_⟩
    · refine unit_hom_ext ?_
      have h := hf.unit
      change (ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ M).natTrans.app (𝟙_ C)) ≫
          f.natTrans.app (𝟙_ C) = ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ N).natTrans.app (𝟙_ C) at h
      simpa only [comp_natTrans, NatTrans.comp_app, Category.assoc] using h
    · refine tensor_ext fun x y => ?_
      have h := hf.tensor x y
      change (ηa M M x y ≫ (MonObj.mul : M ⊗ M ⟶ M).natTrans.app (x ⊗ y)) ≫
          f.natTrans.app (x ⊗ y) = (f.natTrans.app x ⊗ₘ f.natTrans.app y) ≫
          ηa N N x y ≫ (MonObj.mul : N ⊗ N ⟶ N).natTrans.app (x ⊗ y) at h
      simp only [comp_natTrans, NatTrans.comp_app, Category.assoc] at h ⊢
      rw [h, η_tensorHom_assoc]

/-! ## Commutative monoids and lax braided functors -/

section Braided

variable [SymmetricCategory C] [BraidedCategory V]

/-- The Day convolution of the underlying functors. -/
noncomputable abbrev dayConv (F G : C ⊛⥤ V) : DayConvolution F.functor G.functor :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolution C V (C ⊛⥤ V) F G

/-- **The braiding of the Day convolution** of `F` with itself. -/
noncomputable def dayBraiding (F : C ⊛⥤ V) : (F ⊗ F).functor ≅ (F ⊗ F).functor :=
  @DayConvolution.braiding C _ V _ _ _ _ _ F.functor F.functor (dayConv F F) (dayConv F F)

@[reassoc]
lemma ηa_dayBraiding (F : C ⊛⥤ V) (x y : C) :
    ηa F F x y ≫ (dayBraiding F).hom.app (x ⊗ y) =
      (β_ _ _).hom ≫ ηa F F y x ≫ (F ⊗ F).functor.map (β_ y x).hom :=
  @DayConvolution.unit_app_braiding_hom_app C _ V _ _ _ _ _ F.functor F.functor
    (dayConv F F) (dayConv F F) x y

/-- **A commutative monoid for Day convolution**: the multiplication is invariant under the
braiding. -/
def IsCommDay (F : C ⊛⥤ V) [MonObj F] : Prop :=
  (dayBraiding F).hom ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans = (MonObj.mul : F ⊗ F ⟶ F).natTrans

lemma ηa_dayBraiding_mul (F : C ⊛⥤ V) [MonObj F] (x y : C) :
    ηa F F x y ≫ (dayBraiding F).hom.app (x ⊗ y) ≫
        (MonObj.mul : F ⊗ F ⟶ F).natTrans.app (x ⊗ y) =
      (β_ _ _).hom ≫ μF F y x ≫ F.functor.map (β_ y x).hom := by
  rw [ηa_dayBraiding_assoc, mul_naturality, μF]
  simp only [Category.assoc]

/-- **Commutative monoids for Day convolution are lax braided functors**: the multiplication is
commutative exactly when the tensorator commutes with the braidings. -/
theorem isCommDay_iff (F : C ⊛⥤ V) [MonObj F] :
    IsCommDay F ↔ ∀ x y : C,
      μF F x y ≫ F.functor.map (β_ x y).hom = (β_ _ _).hom ≫ μF F y x := by
  constructor
  · intro h x y
    have hxy := congrArg (fun φ => ηa F F x y ≫ φ.app (x ⊗ y)) h
    simp only [NatTrans.comp_app] at hxy
    rw [ηa_dayBraiding_mul] at hxy
    rw [← show ηa F F x y ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans.app (x ⊗ y) = μF F x y from rfl,
      ← hxy]
    simp only [Category.assoc, ← F.functor.map_comp, SymmetricCategory.symmetry,
      F.functor.map_id, Category.comp_id]
  · intro h
    have key : (DayFunctor.Hom.mk ((dayBraiding F).hom ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans) :
        F ⊗ F ⟶ F) = (MonObj.mul : F ⊗ F ⟶ F) := by
      refine tensor_ext fun x y => ?_
      show ηa F F x y ≫ ((dayBraiding F).hom ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans).app (x ⊗ y) =
        _
      rw [NatTrans.comp_app, ηa_dayBraiding_mul, ← Category.assoc, ← h x y, Category.assoc,
        ← F.functor.map_comp, SymmetricCategory.symmetry, F.functor.map_id, Category.comp_id]
      rfl
    exact congrArg DayFunctor.Hom.natTrans key

/-- **The lax braided functor of a commutative monoid for Day convolution.** -/
@[implicit_reducible]
noncomputable def laxBraidedOfCommDay (F : C ⊛⥤ V) [MonObj F] (h : IsCommDay F) :
    F.functor.LaxBraided where
  toLaxMonoidal := laxMonoidalOfMonObj F
  braided x y := (isCommDay_iff F).1 h x y

/-- **A lax braided functor is a commutative monoid for Day convolution.** -/
theorem isCommDay_of_laxBraided (F : C ⊛⥤ V) [L : F.functor.LaxBraided] :
    letI := monObjOfLaxMonoidal F
    IsCommDay F := by
  letI := monObjOfLaxMonoidal F
  refine (isCommDay_iff F).2 fun x y => ?_
  have h1 : μF F x y = Functor.LaxMonoidal.μ F.functor x y := ηa_tensorDesc _ x y
  have h2 : μF F y x = Functor.LaxMonoidal.μ F.functor y x := ηa_tensorDesc _ y x
  rw [h1, h2]
  exact Functor.LaxBraided.braided x y

end Braided

end DayMonoid

end Operad
