/-
# Merging in the cobar construction of a cut cooperad

Let `C = FreeGrL R V` be the free graded operad on a graded linear species `V`, with its cut
cooperad structure. Its operations without unit component are a complement of the span of the
unit (`FreeGrL.sec`), so the reduced part `C̄` embeds into `C`, and composing in `C` gives **a
merge structure on the generators `s⁻¹ C̄` of the cobar construction `ΩC`** (`cobarMerge`):

  `s⁻¹ x̄ ⊛ᵢ s⁻¹ ȳ = (-1)^{|s⁻¹ x|} s⁻¹ (x ∘ᵢ y)‾`.

Its bar differential `h` on `ΩC` contracts the edges of the outer trees, grafting the inner trees
at their ends (`Cobar.hM`), and its merge-composition `⊛` merges the root of a tree into a vertex
of another (`Cobar.mM`).
-/
import Operad.MergeSp
import Operad.Cobar

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## The reduced part as operations without unit component -/

local notation "𝒞" => FreeGrL R V

lemma coaugOne_eq : GrCooperad.Coaug.one (R := R) (C := 𝒞)
    = GrOperad.one (R := R) (P := FreeGrL R V) := rfl

variable (R V) in
/-- **The reduced part embeds** as the operations without unit component. -/
noncomputable def secR (A : Type) [Fintype A] [DecidableEq A] :
    GrCooperad.Red R 𝒞 A →ₗ[R] FreeGrL R V A :=
  Submodule.liftQ _ (secC R V A) (by
    rw [GrCooperad.unitSpan, GrCooperad.unitSpanOf, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact secC_unit e)

lemma secR_proj (x : FreeGrL R V A) :
    secR R V A (GrCooperad.Red.proj R 𝒞 A x) = secC R V A x := rfl

lemma secR_map (σ' : A ≃ B) (x : GrCooperad.Red R 𝒞 A) :
    secR R V B (SymSpecies.map (R := R) σ' x) = GrOperad.map (R := R) σ' (secR R V A x) := by
  obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective _ x
  exact secC_map σ' x

lemma secR_par (b : Bool) (x : GrCooperad.Red R 𝒞 A) :
    secR R V A (GrSpecies.par (R := R) b x) = GrOperad.par (R := R) b (secR R V A x) := by
  obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective _ x
  exact secC_par b x

lemma proj_secR (x : GrCooperad.Red R 𝒞 A) :
    GrCooperad.Red.proj R 𝒞 A (secR R V A x) = x := by
  obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective _ x
  rw [secR_proj, secC_apply, map_sub, map_smul, sub_eq_self]
  by_cases h : Nonempty (Unit ≃ A)
  · obtain ⟨e⟩ := h
    rw [unitL_eq e]
    exact (smul_eq_zero_of_right _ (GrCooperad.Red.proj_map_one e))
  · have h0 : unitL R V A = 0 := by
      rw [unitL]
      exact Finset.sum_eq_zero fun e _ => absurd ⟨e⟩ h
    rw [h0, map_zero, smul_zero]

end FreeGrL

/-! ## The merge structure on the generators of the cobar construction -/

section CobarMerge

variable (R : Type u) [CommRing R] (V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

local notation "𝒞" => FreeGrL R V

/-- **The value of merging two generators of the cobar construction** of a cut cooperad:
`s⁻¹ x̄ ⊛_q s⁻¹ ȳ = (-1)^{|s⁻¹ x|} s⁻¹ (x ∘_q y)‾`, in the positions of the merged vertex. -/
noncomputable def cobarVal {k l : ℕ} (b : Bool) (x : CobarGen R 𝒞 (Fin k)) (q : Fin k)
    (y : CobarGen R 𝒞 (Fin l)) (m : ℕ) (h : m + 1 = k + l) : CobarGen R 𝒞 (Fin m) :=
  σ R b • (GrCooperad.Red.proj R 𝒞 (Fin m) (GrOperad.map (R := R) (posEquivF q l m h)
    (GrOperad.comp (R := R) q (FreeGrL.secR R V (Fin k) x) (FreeGrL.secR R V (Fin l) y))) :
      GrCooperad.Red R 𝒞 (Fin m))

/-- **The merge structure on the generators of the cobar construction** of a cut cooperad. -/
noncomputable def cobarMerge : MergeSp R (CobarGen R 𝒞) where
  val b x q y m h := cobarVal R V b x q y m h
  add_left {k l} b x x' q y m h := by
    unfold cobarVal
    have e : FreeGrL.secR R V (Fin k) (x + x')
        = FreeGrL.secR R V (Fin k) x + FreeGrL.secR R V (Fin k) x' := map_add _ _ _
    rw [e, map_add, LinearMap.add_apply, map_add, map_add, smul_add]
    rfl
  smul_left {k l} b c x q y m h := by
    unfold cobarVal
    have e : FreeGrL.secR R V (Fin k) (c • x) = c • FreeGrL.secR R V (Fin k) x := map_smul _ _ _
    rw [e, LinearMap.map_smul₂, map_smul, map_smul, smul_comm]
    rfl
  add_right {k l} b x q y y' m h := by
    unfold cobarVal
    have e : FreeGrL.secR R V (Fin l) (y + y')
        = FreeGrL.secR R V (Fin l) y + FreeGrL.secR R V (Fin l) y' := map_add _ _ _
    rw [e, map_add, map_add, map_add, smul_add]
    rfl
  smul_right {k l} b c x q y m h := by
    unfold cobarVal
    have e : FreeGrL.secR R V (Fin l) (c • y) = c • FreeGrL.secR R V (Fin l) y := map_smul _ _ _
    rw [e, map_smul, map_smul, map_smul, smul_comm]
    rfl
  map_right {k l} b x q τ y m h := by
    show σ R b • GrCooperad.Red.proj R 𝒞 (Fin m) (GrOperad.map (R := R) (posEquivF q l m h)
        (GrOperad.comp (R := R) q (FreeGrL.secR R V (Fin k) x)
          (FreeGrL.secR R V (Fin l) (SymSpecies.map (R := R) (V := GrCooperad.Red R 𝒞) τ y))))
      = SymSpecies.map (R := R) (V := GrCooperad.Red R 𝒞) _ (σ R b •
          GrCooperad.Red.proj R 𝒞 (Fin m) (GrOperad.map (R := R) (posEquivF q l m h)
            (GrOperad.comp (R := R) q (FreeGrL.secR R V (Fin k) x)
              (FreeGrL.secR R V (Fin l) y))))
    rw [map_smul, GrCooperad.Red.map_proj]
    congr 2
    have e := GrOperad.map_comp (R := R) (P := FreeGrL R V) (Equiv.refl (Fin k)) τ q
      (FreeGrL.secR R V (Fin k) x) (FreeGrL.secR R V (Fin l) y)
    rw [GrOperad.map_refl] at e
    rw [FreeGrL.secR_map, show (q : Fin k) = (Equiv.refl (Fin k)) q from rfl, ← e,
      ← GrOperad.map_trans]
    show _ = GrOperad.map (R := R) _ (GrOperad.map (R := R) _ _)
    rw [← GrOperad.map_trans]
    congr 2
    ext t
    simp
  map_left {k l} b τ x q y m h := by
    show σ R b • GrCooperad.Red.proj R 𝒞 (Fin m) (GrOperad.map (R := R) (posEquivF (τ q) l m h)
        (GrOperad.comp (R := R) (τ q)
          (FreeGrL.secR R V (Fin k) (SymSpecies.map (R := R) (V := GrCooperad.Red R 𝒞) τ x))
          (FreeGrL.secR R V (Fin l) y)))
      = SymSpecies.map (R := R) (V := GrCooperad.Red R 𝒞) _ (σ R b •
          GrCooperad.Red.proj R 𝒞 (Fin m) (GrOperad.map (R := R) (posEquivF q l m h)
            (GrOperad.comp (R := R) q (FreeGrL.secR R V (Fin k) x)
              (FreeGrL.secR R V (Fin l) y))))
    rw [map_smul, GrCooperad.Red.map_proj]
    congr 2
    have e := GrOperad.map_comp (R := R) (P := FreeGrL R V) τ (Equiv.refl (Fin l)) q
      (FreeGrL.secR R V (Fin k) x) (FreeGrL.secR R V (Fin l) y)
    rw [GrOperad.map_refl] at e
    rw [FreeGrL.secR_map, ← e, ← GrOperad.map_trans]
    show _ = GrOperad.map (R := R) _ (GrOperad.map (R := R) _ _)
    rw [← GrOperad.map_trans]
    congr 2
    ext t
    simp
  par {k l} b b' x q y m h hx hy := by
    unfold cobarVal
    have hx' : GrOperad.par (R := R) (!b) (FreeGrL.secR R V (Fin k) x)
        = FreeGrL.secR R V (Fin k) x := by
      rw [← FreeGrL.secR_par]
      exact congrArg _ hx
    have hy' : GrOperad.par (R := R) (!b') (FreeGrL.secR R V (Fin l) y)
        = FreeGrL.secR R V (Fin l) y := by
      rw [← FreeGrL.secR_par]
      exact congrArg _ hy
    show GrSpecies.par (R := R) (!!(xor b b')) (σ R b • GrCooperad.Red.proj R 𝒞 (Fin m) _) = _
    rw [map_smul, GrCooperad.Red.par_proj]
    show σ R b • GrCooperad.Red.proj R 𝒞 (Fin m) (GrOperad.par (R := R) (!!(xor b b'))
      (GrOperad.map (R := R) (posEquivF q l m h) (GrOperad.comp (R := R) q
        (FreeGrL.secR R V (Fin k) x) (FreeGrL.secR R V (Fin l) y)))) = _
    rw [← GrOperad.map_par, ← hx', ← hy',
      show (!!(xor b b')) = xor (!b) (!b') by cases b <;> cases b' <;> rfl, GrOperad.comp_par]

end CobarMerge

end Operad
