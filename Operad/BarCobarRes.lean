/-
# The bar–cobar resolution

For the cobar construction `ΩC` of the cut cooperad `C = FreeGrL R V`, the bar differential `h` of
the merge structure on its generators (`Cobar.hM`) contracts the edges of the outer trees,
grafting the inner trees at their ends, while the cobar differential `d` cuts the inner trees.
-/
import Operad.CutStar
import Operad.CobarMerge

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

section Generators

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒞" => FreeGrL R V
local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)
local notation "𝒥Ω" => GrOperadIdeal.span R (grLinRel R (CobarGen R 𝒞))

namespace Cobar

variable (R V) in
/-- **The bar differential of the merge structure** on the cobar construction of the cut
cooperad: contracting the edges of the outer trees, grafting the inner trees at their ends. -/
noncomputable abbrev hM (A : Type) [Fintype A] [DecidableEq A] :
    CobarGr R 𝒞 A →ₗ[R] CobarGr R 𝒞 A :=
  (cobarMerge R V).d A

variable (R V) in
/-- **The merge-composition of the merge structure** on the cobar construction. -/
noncomputable abbrev mM (i : A) :
    CobarGr R 𝒞 A →ₗ[R] CobarGr R 𝒞 B →ₗ[R] CobarGr R 𝒞 (Without A i ⊕ B) :=
  (cobarMerge R V).mc i

/-- **The bar differential of the merge vanishes on the generators.** -/
lemma hM_ι (v : CobarGen R 𝒞 A) : hM R V A ((FreeGrL.ι R (CobarGen R 𝒞)).app A v) = 0 := by
  rw [GrSpeciesHom.app_eq_chart (FreeGrL.ι R (CobarGen R 𝒞)) (Fintype.equivFin A).symm,
    FreeGrL.ι_app_fin]
  show (cobarMerge R V).d A (GrOperad.map (R := R) (Fintype.equivFin A).symm
    ((𝒥Ω).proj _ (gen _) + (𝒥Ω).proj _ (gen _))) = 0
  rw [← (cobarMerge R V).map_d, map_add, (cobarMerge R V).d_gen, (cobarMerge R V).d_gen,
    add_zero, map_zero]

lemma hM_ιL (c : 𝒞 A) : hM R V A (Cobar.ιL R 𝒞 A c) = 0 := hM_ι _

/-- **Merging two generators**, at the standard finite types. -/
lemma mM_ι_fin {k l : ℕ} {v : CobarGen R 𝒞 (Fin k)} {b : Bool}
    (hv : GrSpecies.par (R := R) b v = v) (i : Fin k) (w : CobarGen R 𝒞 (Fin l)) (m : ℕ)
    (h : m + 1 = k + l) :
    mM R V i ((FreeGrL.ι R (CobarGen R 𝒞)).app (Fin k) v)
        ((FreeGrL.ι R (CobarGen R 𝒞)).app (Fin l) w)
      = GrOperad.map (R := R) (posEquivF i l m h).symm
          ((FreeGrL.ι R (CobarGen R 𝒞)).app (Fin m) (cobarVal R V b v i w m h)) := by
  have hi : (i : ℕ) < k ∧ m + 1 = k + l := ⟨i.2, h⟩
  have key : ∀ c : Bool, mM R V i ((FreeGrL.ι R (CobarGen R 𝒞)).app (Fin k) v)
      (presGen (grLinRel R (CobarGen R 𝒞)) (GrGen.part c w))
        = GrOperad.map (R := R) (posEquivF i l m h).symm
            ((FreeGrL.ι R (CobarGen R 𝒞)).app (Fin m)
              (cobarVal R V b v i (GrSpecies.par (R := R) c w) m h)) := by
    intro c
    rw [FreeGrL.ι_app_hom (R := R) (V := CobarGen R 𝒞) hv]
    show (cobarMerge R V).mc i ((𝒥Ω).proj _ (gen _)) ((𝒥Ω).proj _ (gen _)) = _
    rw [(cobarMerge R V).mc_gen _ i _ m h]
    congr 1
    have hp : GrSpecies.par (R := R) (!(xor b c)) (cobarVal R V b v i (GrSpecies.par (R := R) c w) m h)
        = cobarVal R V b v i (GrSpecies.par (R := R) c w) m h :=
      (cobarMerge R V).par _ _ _ _ _ _ _ hv (GrSpecies.par_par_self (R := R) c w)
    rw [FreeGrL.ι_app_hom (R := R) (V := CobarGen R 𝒞) hp]
    show (𝒥Ω).proj _ (gen ((cobarMerge R V).fn k l _ i _ m)) = (𝒥Ω).proj _ (gen _)
    congr 2
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact (cobarMerge R V).fn_val _ _ hi
    · exact (cobarMerge R V).fn_par _ _
  have e : cobarVal R V b v i (GrSpecies.par (R := R) false w) m h
      + cobarVal R V b v i (GrSpecies.par (R := R) true w) m h = cobarVal R V b v i w m h :=
    ((cobarMerge R V).add_right b v i _ _ m h).symm.trans
      (congrArg (fun y => cobarVal R V b v i y m h) (GrSpecies.par_add (R := R) w))
  have hw := FreeGrL.ι_app_fin (R := R) (V := CobarGen R 𝒞) w
  have h2 := congrArg (mM R V i ((FreeGrL.ι R (CobarGen R 𝒞)).app (Fin k) v)) hw
  refine h2.trans ?_
  refine ((mM R V i ((FreeGrL.ι R (CobarGen R 𝒞)).app (Fin k) v)).map_add _ _).trans ?_
  refine (congrArg₂ (· + ·) (key false) (key true)).trans ?_
  exact ((GrOperad.map (R := R) (posEquivF i l m h).symm).map_add _ _).symm.trans
    (congrArg (GrOperad.map (R := R) (posEquivF i l m h).symm)
      ((((FreeGrL.ι R (CobarGen R 𝒞)).app (Fin m)).map_add _ _).symm.trans
        (congrArg ((FreeGrL.ι R (CobarGen R 𝒞)).app (Fin m)) e)))

/-- The generator of a merged value. -/
lemma ι_cobarVal {k l : ℕ} (b : Bool) (v : CobarGen R 𝒞 (Fin k)) (i : Fin k)
    (w : CobarGen R 𝒞 (Fin l)) (m : ℕ) (h : m + 1 = k + l) :
    (FreeGrL.ι R (CobarGen R 𝒞)).app (Fin m) (cobarVal R V b v i w m h)
      = σ R b • Cobar.ιL R 𝒞 (Fin m) (GrOperad.map (R := R) (posEquivF i l m h)
          (GrOperad.comp (R := R) i (FreeGrL.secR R V (Fin k) v) (FreeGrL.secR R V (Fin l) w))) :=
  map_smul ((FreeGrL.ι R (CobarGen R 𝒞)).app (Fin m)) (σ R b) _

/-- **Merging two generators** composes them in the cut cooperad, on the parts without unit
component: `ι x ⊛ᵢ ι y = (-1)^{|ι x|} ι (x ∘ᵢ y)`, at the standard finite types. -/
lemma mM_ιL_fin {k l : ℕ} {c : 𝒞 (Fin k)} {pa : Bool} (hc : GrOperad.par (R := R) pa c = c)
    (i : Fin k) (c' : 𝒞 (Fin l)) :
    mM R V i (Cobar.ιL R 𝒞 (Fin k) c) (Cobar.ιL R 𝒞 (Fin l) c')
      = σ R (!pa) • Cobar.ιL R 𝒞 _ (GrOperad.comp (R := R) i (FreeGrL.secC R V (Fin k) c)
          (FreeGrL.secC R V (Fin l) c')) := by
  have hk : 0 < k := Fin.pos i
  have hm : (k + l - 1) + 1 = k + l := by omega
  have hv : GrSpecies.par (R := R) (!pa)
      (GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R 𝒞) (Fin k)
        (GrCooperad.Red.proj R 𝒞 (Fin k) c))
      = GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R 𝒞) (Fin k)
          (GrCooperad.Red.proj R 𝒞 (Fin k) c) := by
    rw [GrSpecies.Shift.par_of, Bool.not_not, GrCooperad.Red.par_proj]
    exact congrArg (fun x => GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R 𝒞) (Fin k)
      (GrCooperad.Red.proj R 𝒞 (Fin k) x)) hc
  have e := mM_ι_fin (R := R) (V := V) hv i (GrSpecies.Shift.of (R := R)
    (V := GrCooperad.Red R 𝒞) (Fin l) (GrCooperad.Red.proj R 𝒞 (Fin l) c')) _ hm
  refine e.trans ?_
  rw [ι_cobarVal, map_smul, ← Cobar.ιL_map]
  show σ R (!pa) • Cobar.ιL R 𝒞 _ (GrOperad.map (R := R) (posEquivF i l (k + l - 1) hm).symm
    (GrOperad.map (R := R) (posEquivF i l (k + l - 1) hm) _)) = _
  rw [map_symm_map]
  rfl

end Cobar

end Generators

end Operad
