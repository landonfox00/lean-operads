/-
# The twisted composite product `C ∘_ι ΩC` is acyclic

Let `C` be a reduced coaugmented graded cooperad (spanned by the coaugmentation in the arities at
most one) and `ΩC` its cobar construction, with the universal twisting morphism `ι : C → ΩC`. The
twisted composite product `C ∘_ι ΩC` has the contracting homotopy

  `h = (s ∘ 1) ∘ ρ ∘ (ε ∘ 1)`

(`GrComposite.cobarH`): the counit of the outer cooperation, leaving its single inner operation
`x ∈ ΩC` (`GrComposite.cobarE`), the root decomposition of `x` (`FreeGrL.root`), and the
suspension of the root vertex back into `C` (`GrComposite.cobarSusp`).
-/
import Operad.GrTwistedDG
import Operad.ConvUnit
import Operad.Twisting

universe u v

namespace Operad

open Function Sym GerBV ConvOp

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]

namespace GrCooperad

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The span of the coaugmentation vanishes outside the arities of one element. -/
lemma unitSpan_eq_bot (h : IsEmpty (Unit ≃ A)) : unitSpan R C A = ⊥ := by
  rw [unitSpan, unitSpanOf, Submodule.span_eq_bot]
  rintro _ ⟨e, rfl⟩
  exact h.elim e

/-- **The section of the reduced part**: the identity outside the arities of one element. -/
noncomputable def Red.sec (A : Type) [Fintype A] [DecidableEq A] : Red R C A →ₗ[R] C A :=
  @dite _ (IsEmpty (Unit ≃ A)) (Classical.dec _)
    (fun h => (Submodule.quotEquivOfEqBot (unitSpan R C A) (unitSpan_eq_bot h)).toLinearMap)
    (fun _ => 0)

lemma Red.sec_proj (h : IsEmpty (Unit ≃ A)) (x : C A) : Red.sec A (Red.proj R C A x) = x := by
  rw [Red.sec, dif_pos h]
  rfl

lemma Red.sec_of_nonempty (h : Nonempty (Unit ≃ A)) (v : Red R C A) : Red.sec A v = 0 := by
  rw [Red.sec, dif_neg (not_isEmpty_iff.2 h)]
  rfl

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
lemma isEmpty_congr (σ : A ≃ B) : IsEmpty (Unit ≃ A) ↔ IsEmpty (Unit ≃ B) :=
  ⟨fun h => ⟨fun e => h.elim (e.trans σ.symm)⟩, fun h => ⟨fun e => h.elim (e.trans σ)⟩⟩

lemma Red.sec_map (σ : A ≃ B) (v : Red R C A) :
    Red.sec B (SymSpecies.map (R := R) σ v) = SymSpecies.map (R := R) σ (Red.sec A v) := by
  obtain ⟨x, rfl⟩ := Red.proj_surjective (R := R) (C := C) A v
  by_cases h : IsEmpty (Unit ≃ A)
  · rw [Red.map_proj, Red.sec_proj ((isEmpty_congr σ).1 h), Red.sec_proj h]
  · rw [not_isEmpty_iff] at h
    rw [Red.sec_of_nonempty h, Red.sec_of_nonempty (h.map fun e => e.trans σ), map_zero]

lemma Red.sec_par (b : Bool) (v : Red R C A) :
    Red.sec A (GrSpecies.par (R := R) b v) = GrSpecies.par (R := R) b (Red.sec A v) := by
  obtain ⟨x, rfl⟩ := Red.proj_surjective (R := R) (C := C) A v
  by_cases h : IsEmpty (Unit ≃ A)
  · rw [Red.par_proj, Red.sec_proj h, Red.sec_proj h]
  · rw [not_isEmpty_iff] at h
    rw [Red.sec_of_nonempty h, Red.sec_of_nonempty h, map_zero]

/-- **A cooperation in an arity of one element** is a multiple of the relabelled coaugmentation,
for a reduced cooperad. -/
lemma eq_counit_smul (hred : ∀ x : C A, x ∈ unitSpan R C A) (e : Unit ≃ A) (x : C A) :
    x = counit (R := R) (SymSpecies.map (R := R) e.symm x)
      • SymSpecies.map (R := R) e (Coaug.one (R := R) (C := C)) := by
  have hx := hred x
  rw [unitSpan, unitSpanOf, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  haveI : Subsingleton (Unit ≃ A) := ⟨fun e₁ e₂ => Equiv.ext fun u => by
    have : ∀ a a' : A, a = a' := fun a a' => by
      rw [← e.apply_symm_apply a, ← e.apply_symm_apply a']
    exact this _ _⟩
  rw [Fintype.sum_subsingleton _ e] at hc
  subst hc
  rw [map_smul, ← SymSpecies.map_trans, Equiv.self_trans_symm, SymSpecies.map_refl, map_smul,
    Coaug.counit_one, smul_eq_mul, mul_one]

end GrCooperad

namespace GrComposite

open GrCooperad

/-! ## The maps of the homotopy -/

section Maps

variable (R C) in
/-- **The suspension** of the generators of the cobar construction back into `C`: the section of
the reduced part. -/
noncomputable def cobarSusp : SymSpeciesHom R (CobarGen R C) C where
  app A _ _ := Red.sec A ∘ₗ (GrSpecies.Shift.of (R := R) (V := Red R C) A).symm.toLinearMap
  app_map σ v := Red.sec_map σ v

lemma cobarSusp_of {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    (cobarSusp R C).app A (GrSpecies.Shift.of (R := R) (V := Red R C) A (Red.proj R C A x))
      = Red.sec A (Red.proj R C A x) := rfl

variable (R C) in
/-- **The counit**, as a morphism of linear species `C → ΩC` into the units. -/
noncomputable def cobarEps : SymSpeciesHom R C (CobarOp R C) where
  app A _ _ := ∑ e : Unit ≃ A, (LinearMap.smulRight (counit (R := R) (C := C)) (GrOperad.map (R := R)
    (P := CobarOp R C) e (GrOperad.one (R := R)))).comp (SymSpecies.map (R := R) e.symm)
  app_map {A B} _ _ _ _ σ x := by
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
      LinearMap.smulRight_apply, map_sum, map_smul]
    refine Fintype.sum_equiv (Equiv.mk (fun e => e.trans σ.symm) (fun e => e.trans σ)
      (fun e => by ext; simp) (fun e => by ext; simp)) _ _ fun e => ?_
    show _ = _ • GrOperad.map (R := R) σ (GrOperad.map (R := R) (e.trans σ.symm) _)
    rw [← SymSpecies.map_trans, ← GrOperad.map_trans]
    congr 2

lemma cobarEps_apply {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    (cobarEps R C).app A x = ∑ e : Unit ≃ A, counit (R := R) (SymSpecies.map (R := R) e.symm x)
      • GrOperad.map (R := R) (P := CobarOp R C) e (GrOperad.one (R := R)) := by
  simp [cobarEps]

end Maps

end GrComposite

end Operad
