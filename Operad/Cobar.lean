/-
# The cobar construction of a coaugmented graded cooperad

The cobar construction `ΩC` of a coaugmented graded cooperad `C` is the free graded operad on the
desuspension `s⁻¹ C̄` of its reduced part (`CobarGen`, `CobarGr`), with the odd derivation
extending `s⁻¹ c̄ ↦ -(ι ⋆ ι)(c)` (`Cobar.d`). Here `ι : C → ΩC`, `c ↦ s⁻¹ c̄`, is **the universal
twisting morphism** (`Cobar.ι`), an odd invariant family of the convolution operad of `C` and
`ΩC`, and `⋆` is the convolution product.

* `ι ⋆ ι` vanishes on the coaugmentation, whose decompositions are tensors of relabellings of `1`
  (`Cobar.star_ι_ι_unit`), so the derivation is well defined, and `d ∘ ι = -(ι ⋆ ι)`
  (`Cobar.d_ι`).
* **The differential squares to zero** (`Cobar.d_d`): `d²` is an even derivation, so it is enough
  to check it on the generators, where `d² ι = (ι ⋆ ι) ⋆ ι - ι ⋆ (ι ⋆ ι)` is the associator of
  an odd family with itself, which vanishes (`GrOperad.Inv.assoc_odd`).
* **The cobar construction is a dg operad** (`CobarOp`, `Cobar.instDGOperad`).
-/
import Operad.ConvOperad

universe u v

namespace Operad

open Sym GerBV
open scoped TensorProduct

variable (R : Type u) [CommRing R] (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]

/-- **The generators of the cobar construction**: the desuspension `s⁻¹ C̄` of the reduced
part. -/
abbrev CobarGen := GrSpecies.Shift (GrCooperad.Red R C) R

/-- The graded operad underlying the cobar construction: the free graded operad on `s⁻¹ C̄`. -/
abbrev CobarGr := FreeGrL R (CobarGen R C)

namespace Cobar

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The universal twisting morphism `C A → ΩC A`, `c ↦ s⁻¹ c̄`. -/
noncomputable def ιL (A : Type) [Fintype A] [DecidableEq A] : C A →ₗ[R] CobarGr R C A :=
  (FreeGrL.ι R (CobarGen R C)).app A ∘ₗ
    (GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R C) A).toLinearMap ∘ₗ
      GrCooperad.Red.proj R C A

lemma ιL_apply (x : C A) :
    ιL R C A x = (FreeGrL.ι R (CobarGen R C)).app A
      (GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R C) A (GrCooperad.Red.proj R C A x)) :=
  rfl

lemma ιL_map (e : A ≃ B) (x : C A) :
    ιL R C B (SymSpecies.map (R := R) e x) = GrOperad.map (R := R) e (ιL R C A x) := by
  rw [ιL_apply, ιL_apply, ← GrCooperad.Red.map_proj, ← GrSpecies.Shift.map_of]
  exact (FreeGrL.ι R (CobarGen R C)).app_map e _

lemma ιL_par (c : Bool) (x : C A) :
    ιL R C A (GrSpecies.par (R := R) c x) = GrOperad.par (R := R) (!c) (ιL R C A x) := by
  rw [ιL_apply, ιL_apply, ← GrCooperad.Red.par_proj]
  have h : GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R C) A
      (GrSpecies.par (R := R) c (GrCooperad.Red.proj R C A x))
      = GrSpecies.par (R := R) (!c) (GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R C) A
          (GrCooperad.Red.proj R C A x)) := by
    rw [GrSpecies.Shift.par_of, Bool.not_not]
  rw [h]
  exact (FreeGrL.ι R (CobarGen R C)).app_par _ _

lemma ιL_unitSpan {x : C A} (hx : x ∈ GrCooperad.unitSpan R C A) : ιL R C A x = 0 := by
  rw [ιL_apply, show GrCooperad.Red.proj R C A x = 0 from
    (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero, map_zero]

/-- **The universal twisting morphism**, an invariant family of the convolution operad. -/
noncomputable def ι : GrOperad.Inv R (ConvOp R C (CobarGr R C)) :=
  ⟨fun A _ _ => ConvOp.of (ιL R C A), fun A B _ _ _ _ e => by
    show ConvOp.mapC e (ConvOp.of (ιL R C A)) = ConvOp.of (ιL R C B)
    ext x
    rw [ConvOp.mapC_apply, ConvOp.toLin_of, ConvOp.toLin_of, ← ιL_map,
      SymSpecies.map_map_symm]⟩

lemma ι_apply (A : Type) [Fintype A] [DecidableEq A] :
    (ι R C).1 A = ConvOp.of (ιL R C A) := rfl

/-- **The universal twisting morphism is odd.** -/
lemma isPar_ι : GrOperad.Inv.IsPar true (ι R C) := by
  intro A _ _
  show ConvOp.parC true (ConvOp.of (ιL R C A)) = ConvOp.of (ιL R C A)
  rw [ConvOp.parC_eq_self_iff]
  intro c x
  rw [ConvOp.toLin_of, ιL_par, Bool.xor_true]

/-- The square `ι ⋆ ι`. -/
noncomputable abbrev ιι : GrOperad.Inv R (ConvOp R C (CobarGr R C)) :=
  GrOperad.Inv.star R _ (ι R C) (ι R C)

lemma isPar_ιι : GrOperad.Inv.IsPar false (ιι R C) := by
  have h := GrOperad.Inv.isPar_star (isPar_ι R C) (isPar_ι R C)
  rwa [Bool.xor_self] at h

/-- A tensor whose second factor is a relabelling of `1` is killed by `ι ⊗ ι`. -/
lemma kap_ι_unit {D : Type} [Fintype D] [DecidableEq D] (f : ConvOp R C (CobarGr R C) D)
    (a : C D) {b : C A} (hb : b ∈ GrCooperad.unitSpan R C A) :
    ConvOp.kap f ((ι R C).1 A) (a ⊗ₜ b) = 0 := by
  simp only [ConvOp.kap, LinearMap.coe_sum, Finset.sum_apply, TensorProduct.map_tmul]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [ConvOp.parC_apply]
  have : ∀ c : Bool, ConvOp.toLin ((ι R C).1 A) (GrSpecies.par (R := R) c b) = 0 := fun c =>
    ιL_unitSpan R C (GrCooperad.unitSpan_le_comap_par c hb)
  simp [this]

/-- **`ι ⋆ ι` vanishes on the coaugmentation.** -/
lemma star_ι_ι_unit {x : C A} (hx : x ∈ GrCooperad.unitSpan R C A) :
    ConvOp.toLin ((ιι R C).1 A) x = 0 := by
  rw [GrOperad.Inv.star_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun S _ => ?_
  show ConvOp.toLin (ConvOp.mapC (splitEquiv S)
    (ConvOp.compC none ((ι R C).1 (SOut S)) ((ι R C).1 (SIn S)))) x = 0
  rw [ConvOp.mapC_apply, ConvOp.toLin_compC, LinearMap.comp_apply, LinearMap.comp_apply]
  have hmem : GrCooperad.decomp (R := R) (C := C) (none : SOut S)
      (SymSpecies.map (R := R) (splitEquiv S).symm x)
      ∈ Submodule.map₂ (TensorProduct.mk R (C (SOut S)) (C (SIn S)))
          (GrCooperad.unitSpan R C (SOut S)) (GrCooperad.unitSpan R C (SIn S)) := by
    have hx' := GrCooperad.unitSpan_le_comap_map (R := R) (C := C) (splitEquiv S).symm hx
    have key : GrCooperad.unitSpan R C (Without (SOut S) none ⊕ SIn S)
        ≤ Submodule.comap (GrCooperad.decomp (R := R) (C := C) (none : SOut S))
          (Submodule.map₂ (TensorProduct.mk R (C (SOut S)) (C (SIn S)))
            (GrCooperad.unitSpan R C (SOut S)) (GrCooperad.unitSpan R C (SIn S))) := by
      rw [GrCooperad.unitSpan, GrCooperad.unitSpanOf, Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      exact GrCooperad.Coaug.decomp_mem none e
    exact key hx'
  have hk : ∀ t ∈ Submodule.map₂ (TensorProduct.mk R (C (SOut S)) (C (SIn S)))
      (GrCooperad.unitSpan R C (SOut S)) (GrCooperad.unitSpan R C (SIn S)),
      ConvOp.kap ((ι R C).1 (SOut S)) ((ι R C).1 (SIn S)) t = 0 := by
    intro t ht
    refine (Submodule.map₂_le.2 ?_ : Submodule.map₂ _ _ _ ≤ LinearMap.ker
      (ConvOp.kap ((ι R C).1 (SOut S)) ((ι R C).1 (SIn S)))) ht
    intro a _ b hb
    exact kap_ι_unit R C _ a hb
  rw [hk _ hmem, map_zero, map_zero]

/-! ### The differential -/

/-- The value of the cobar differential on the generators: `s⁻¹ c̄ ↦ -(ι ⋆ ι)(c)`. -/
noncomputable def genD (A : Type) [Fintype A] [DecidableEq A] :
    CobarGen R C A →ₗ[R] CobarGr R C A :=
  -(Submodule.liftQ (GrCooperad.unitSpan R C A) (ConvOp.toLin ((ιι R C).1 A))
    fun _ hx => star_ι_ι_unit R C hx)

lemma genD_proj (x : C A) :
    genD R C A (GrCooperad.Red.proj R C A x) = -ConvOp.toLin ((ιι R C).1 A) x := by
  simp only [genD]
  rfl

lemma ιι_map (e : A ≃ B) (x : C A) :
    ConvOp.toLin ((ιι R C).1 B) (SymSpecies.map (R := R) e x)
      = GrOperad.map (R := R) e (ConvOp.toLin ((ιι R C).1 A) x) := by
  rw [← GrOperad.Inv.map_apply (ιι R C) e]
  show ConvOp.toLin (ConvOp.mapC e _) _ = _
  rw [ConvOp.mapC_apply, SymSpecies.map_symm_map]

/-- The generator values of the cobar differential, as a morphism of linear species. -/
noncomputable def genDSp : SymSpeciesHom R (CobarGen R C) (CobarGr R C) where
  app A _ _ := genD R C A
  app_map {A B} _ _ _ _ e v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    show genD R C B (GrCooperad.Red.proj R C B (SymSpecies.map (R := R) e x))
      = GrOperad.map (R := R) e (genD R C A (GrCooperad.Red.proj R C A x))
    rw [genD_proj, genD_proj, ιι_map, map_neg]

/-- **The generator values shift parities by one.** -/
lemma isShift_genD : FreeGrL.IsShift (genDSp R C) true := by
  intro A _ _ c v
  obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
  show genD R C A (GrCooperad.Red.proj R C A (GrSpecies.par (R := R) (!c) x))
    = GrOperad.par (R := R) (xor c true) (genD R C A (GrCooperad.Red.proj R C A x))
  have hev := ConvOp.parC_eq_self_iff.1 (isPar_ιι R C A)
  rw [genD_proj, genD_proj, hev, map_neg, Bool.xor_false, Bool.xor_true]

/-- **The cobar differential**: the odd derivation of the free graded operad on `s⁻¹ C̄`
extending `s⁻¹ c̄ ↦ -(ι ⋆ ι)(c)`. -/
noncomputable def d : GrDer (GrOperadHom.id R (CobarGr R C)) true :=
  FreeGrL.derOf (GrOperadHom.id R (CobarGr R C)) (genDSp R C) (isShift_genD R C)

lemma d_ιL (x : C A) : (d R C).app A (ιL R C A x) = -ConvOp.toLin ((ιι R C).1 A) x := by
  rw [ιL_apply, d, FreeGrL.derOf_ι]
  exact genD_proj R C x

/-- **`d ∘ ι = -(ι ⋆ ι)`.** -/
theorem d_ι : GrOperad.Inv.appDer (ConvOp.postDer (C := C) (d R C)) (ι R C) = -ιι R C := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ?_)
  show ConvOp.postL ((d R C).app A) (ConvOp.of (ιL R C A)) = -(ιι R C).1 A
  ext x
  rw [ConvOp.toLin_postL, LinearMap.comp_apply, ConvOp.toLin_of, d_ιL, ConvOp.toLin_neg,
    LinearMap.neg_apply]

/-- **The cobar differential squares to zero.** -/
theorem d_d (y : CobarGr R C A) : (d R C).app A ((d R C).app A y) = 0 := by
  refine FreeGrL.sq_eq_zero (fun A _ _ v => ?_) y
  obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
  have h1 : (d R C).app A ((FreeGrL.ι R (CobarGen R C)).app A (GrCooperad.Red.proj R C A x))
      = -ConvOp.toLin ((ιι R C).1 A) x := d_ιL R C x
  rw [h1, map_neg, neg_eq_zero, ← ConvOp.appDer_postDer_apply,
    GrOperad.Inv.appDer_star_self (isPar_ι R C) _ (d_ι R C)]
  rfl

end Cobar

/-! ## The cobar construction as a dg operad -/

/-- **The cobar construction** of a coaugmented graded cooperad, a dg operad. -/
def CobarOp (A : Type) [Fintype A] [DecidableEq A] : Type (max u v) := CobarGr R C A

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (CobarOp R C A) :=
  inferInstanceAs (AddCommGroup (CobarGr R C A))

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : Module R (CobarOp R C A) :=
  inferInstanceAs (Module R (CobarGr R C A))

namespace Cobar

/-- **The cobar construction is a dg operad.** -/
noncomputable instance instDGOperad : DGOperad R (CobarOp R C) :=
  { (inferInstance : GrOperad R (CobarGr R C)) with
    d := fun {A} _ _ => (d R C).app A
    d_d := fun {A} _ _ y => d_d R C (A := A) y
    d_par := fun {A} _ _ b y => by
      have h := (d R C).app_par b y
      rw [Bool.xor_true] at h
      exact h
    map_d := fun {A B} _ _ _ _ e y => ((d R C).app_map e y).symm
    d_one := (d R C).app_one
    d_comp := fun {A B} _ _ _ _ i y z => by
      have h := (d R C).app_comp i y z
      rw [GrOperadHom.id_app, GrOperadHom.id_app, GrOperad.tw_true] at h
      exact h }

end Cobar

end Operad
