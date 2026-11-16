/-
# Morphisms into the bar construction of a dg operad

For a dg operad `P`, an ideal `I` stable under its differential and without operations without
inputs, and a conilpotent dg cooperad `C`, over a `ℚ`-algebra, with the projectivity hypothesis of
`Operad.BarAdjunction`: **a twisting morphism `α : C → P` with values in `I` is `π ∘ f` for a
coaugmented morphism of graded cooperads `f : C → B(P, I)` commuting with the differential of the
bar construction of the dg operad** (`Bar.exists_hom_dg`), `d_B + d_int` (`Bar.dTot`).

* `π ∘ d_int = -∂ ∘ π` (`Bar.piL_dInt`): the internal differential keeps the number of vertices,
  and on a tree with one vertex it is `s a ↦ -s (∂ a)`.
* **A morphism of graded cooperads into the bar construction of a dg operad commutes with the
  differentials as soon as it does after `π`** (`Bar.d_app_eq_app_d_dg`): the argument of
  `Bar.d_app_eq_app_d`, with the dg cooperad `Bar.dgCooperad`.
* The morphism is the one of `Operad.BarAdjunction` with cogenerator part the suspension of `α`;
  with `π ∘ d_B ∘ f = -(π f) ⋆ (π f)` and `π ∘ d_int ∘ f = -∂ (π f)`, the Maurer–Cartan equation
  `∂ α + α ∘ d + α ⋆ α = 0` (`Bar.mc_apply`) is the condition `π ∘ d ∘ f = π ∘ f ∘ d`.
-/
import Operad.BarInternal
import Operad.BarAdjunction

universe u v w

namespace Operad

open Sym GerBV FreeGrL FreeGr
open scoped TensorProduct

namespace Bar

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]
  {I : GrOperadIdeal R P}
  (hI : ∀ {A : Type} [Fintype A] [DecidableEq A] {x : P A}, x ∈ I.sub A →
    DGOperad.d (R := R) x ∈ I.sub A)

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R (BarGen I))
local notation "𝒞" => FreeGrL R (BarGen I)
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R

/-- **The universal twisting morphism after the internal differential**: `π ∘ d_int = -∂ ∘ π`. -/
lemma piL_dInt [Algebra ℚ R] {A : Type} [Fintype A] [DecidableEq A] (z : 𝒞 A) :
    piL I A ((dInt hI).app A z) = -DGOperad.d (R := R) (piL I A z) := by
  obtain ⟨w, rfl⟩ := (𝒥).proj_surjective A z
  refine Lin.induction₁ (S := Reg (TreeOfArity (GrGen R (BarGen I))))
    (piL I A ∘ₗ (dInt hI).app A ∘ₗ (𝒥).proj A)
    (-(DGOperad.d (R := R) (P := P) (A := A)) ∘ₗ piL I A ∘ₗ (𝒥).proj A) (fun t => ?_) w
  show piL I A ((dInt hI).app A ((𝒥).proj A (𝔟 t)))
    = -DGOperad.d (R := R) (piL I A ((𝒥).proj A (𝔟 t)))
  have hmem : (𝒥).proj A (𝔟 t) ∈ vx R (BarGen I) (FreeGr.treeOf t).weight A :=
    mem_eig.2 (by rw [← Cobar.wtD_eq_derSp, FreeGrL.wtD_proj_bas])
  by_cases hw : (FreeGr.treeOf t).weight = 1
  · rw [hw] at hmem
    rw [FreeGrL.eq_ι_genCoef hmem, dInt, FreeGrL.derSp_ι, piL_ι, piL_ι]
    rfl
  · have h2 : (dInt hI).app A ((𝒥).proj A (𝔟 t)) ∈ vx R (BarGen I) (FreeGr.treeOf t).weight A :=
      derSp_mem_vx hmem
    rw [piL_vx hw h2, piL_vx hw hmem, map_zero, neg_zero]


variable {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]

/-- **The differential of the bar construction of a dg operad.** -/
noncomputable def dTot (A : Type) [Fintype A] [DecidableEq A] : 𝒞 A →ₗ[R] 𝒞 A :=
  d I A + (dInt hI).app A

lemma dTot_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (X : 𝒞 A) : dTot hI B (GrOperad.map (R := R) e X) = GrOperad.map (R := R) e (dTot hI A X) := by
  simp only [dTot, LinearMap.add_apply]
  rw [d_map, (dInt hI).app_map, map_add]

/-- **The coderivation rule for the defect**, for the bar construction of a dg operad: when all
the values of `d ∘ f - f ∘ d` have at least `k` vertices, their convolution squares have weight
at least `k + 1`. -/
lemma ιι_dTot_sub_mem [Algebra ℚ R] (f : GrCooperadHom R C 𝒞) {k : ℕ}
    (hk : ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      dTot hI A' (f.app A' x') - f.app A' (DGCooperad.d (R := R) x') ∈ vxGe R (BarGen I) k A')
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) :
    ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) (dTot hI A (f.app A x) - f.app A (DGCooperad.d (R := R) x))
      ∈ Cobar.wtGe (V := BarGen I) (k + 1) A := by
  exact ConvOp.toLin_star_d_sub_mem (D := dgCooperad hI) f (Cobar.isPar_ι R 𝒞)
    (Cobar.wtGe_par_all k) (Cobar.wtGe_par_all 1) (Cobar.wtGe_map_all (k + 1))
    (Cobar.wtGe_comp_all k 1 (k + 1) le_rfl) (Cobar.wtGe_comp_all 1 k (k + 1) (by omega))
    (fun A' _ _ x' => Cobar.ιL_mem_wtGe (hk A' x')) (fun A' _ _ x' => Cobar.ιL_mem_wtGe_one _) A x

/-- **A morphism of graded cooperads from a dg cooperad into the bar construction of a dg operad
commutes with the differentials as soon as it does after the universal twisting morphism**:
`π ∘ d ∘ f = π ∘ f ∘ d` implies `d ∘ f = f ∘ d`, over a `ℚ`-algebra, for an ideal without
operations without inputs. The defect `d ∘ f - f ∘ d` is a coderivation along `f`, and a
coderivation into the cut cooperad is determined by its cogenerator part. -/
theorem d_app_eq_app_d_dg [Algebra ℚ R] (hV0 : ∀ v : BarGen I (Fin 0), v = 0)
    (f : GrCooperadHom R C 𝒞)
    (hπ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      piL I A (dTot hI A (f.app A x)) = piL I A (f.app A (DGCooperad.d (R := R) x)))
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) :
    dTot hI A (f.app A x) = f.app A (DGCooperad.d (R := R) x) := by
  have hu : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      unitCoeffL R (BarGen I) A (dTot hI A (f.app A x) - f.app A (DGCooperad.d (R := R) x))
        = 0 := by
    intro A _ _ x
    by_cases hA : Nonempty (Unit ≃ A)
    · obtain ⟨e⟩ := hA
      have hx : x = SymSpecies.map (R := R) e (SymSpecies.map (R := R) e.symm x) :=
        (SymSpecies.map_map_symm e x).symm
      generalize SymSpecies.map (R := R) e.symm x = y at hx
      subst hx
      have hm : dTot hI A (f.app A (SymSpecies.map (R := R) e y))
          - f.app A (DGCooperad.d (R := R) (SymSpecies.map (R := R) e y))
          = GrOperad.map (R := R) e (dTot hI Unit (f.app Unit y)
            - f.app Unit (DGCooperad.d (R := R) y)) := by
        have e1 : f.app A (SymSpecies.map (R := R) e y)
            = GrOperad.map (R := R) e (f.app Unit y) := f.app_map e y
        have e2 : DGCooperad.d (R := R) (SymSpecies.map (R := R) e y)
            = SymSpecies.map (R := R) e (DGCooperad.d (R := R) y) :=
          (DGCooperad.map_d (R := R) e y).symm
        have e3 : f.app A (SymSpecies.map (R := R) e (DGCooperad.d (R := R) y))
            = GrOperad.map (R := R) e (f.app Unit (DGCooperad.d (R := R) y)) := f.app_map e _
        rw [e1, e2, e3, dTot_map, map_sub]
      have c1 : GrCooperad.counit (R := R) (C := 𝒞) (dTot hI Unit (f.app Unit y)) = 0 :=
        (dgCooperad hI).counit_d _
      have c2 : GrCooperad.counit (R := R) (C := 𝒞)
          (f.app Unit (DGCooperad.d (R := R) y)) = 0 :=
        (LinearMap.congr_fun f.counit_app _).trans (DGCooperad.counit_d (R := R) y)
      rw [hm, unitCoeffL_map, ← counit_eq_unitCoeffL, map_sub, c1, c2, sub_zero]
    · exact unitCoeffL_eq_zero (not_nonempty_iff.1 hA) _
  have hg : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      dTot hI A (f.app A x) - f.app A (DGCooperad.d (R := R) x) ∈ vxGe R (BarGen I) 2 A := by
    intro A _ _ x
    have h2 := sub_ι_genCoef_mem (hu A x)
    have hker : vxGe R (BarGen I) 2 A ≤ LinearMap.ker (piL I A) := iSup_le fun j w hw => by
      rw [LinearMap.mem_ker, piL_vx (by have := j.2; omega) hw]
    have h3 := hker h2
    rw [LinearMap.mem_ker, map_sub, map_sub, hπ, sub_self, zero_sub, neg_eq_zero, piL_ι] at h3
    have hg0 : FreeGrL.genCoef R (BarGen I) A
        (dTot hI A (f.app A x) - f.app A (DGCooperad.d (R := R) x)) = 0 := IdealSp.ext I h3
    rwa [hg0, map_zero, sub_zero] at h2
  have key : ∀ k, 2 ≤ k → ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      dTot hI A' (f.app A' x') - f.app A' (DGCooperad.d (R := R) x') ∈ vxGe R (BarGen I) k A' := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hg
    | succ k hk ih =>
      exact fun A' _ _ x' => Cobar.mem_vxGe_succ hV0 hk (ih A' x') (ιι_dTot_sub_mem hI f ih A' x')
  exact sub_eq_zero.1 (eq_zero_of_forall_mem_vxGe fun p =>
    vxGe_anti (le_max_left p 2) (key _ (le_max_right p 2) A x))

/-! ## Twisting morphisms into the ideal -/

section Exist

variable [GrCooperad.Coaug R C]

/-- **The morphism to the suspended ideal** of an odd family with values in the ideal. -/
noncomputable def genOfDG (α : GrOperad.Inv R (ConvOp R C P)) (hα : GrOperad.Inv.IsPar true α)
    (hIα : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1 A) x : P A) ∈ I.sub A) :
    GrSpeciesHom R C (BarGen I) where
  app A _ _ := LinearMap.codRestrict (I.sub A)
    (show C A →ₗ[R] P A from ConvOp.toLin (α.1 A)) (hIα A)
  app_map {A B} _ _ _ _ e x := IdealSp.ext I (by
    show ConvOp.toLin (α.1 B) (SymSpecies.map (R := R) e x)
      = GrOperad.map (R := R) e (ConvOp.toLin (α.1 A) x)
    have h : ConvOp.mapC e (α.1 A) = α.1 B := α.2 A B e
    rw [← h, ConvOp.mapC_apply, SymSpecies.map_symm_map])
  app_par {A} _ _ c x := IdealSp.ext I (by
    show ConvOp.toLin (α.1 A) (GrSpecies.par (R := R) c x)
      = GrOperad.par (R := R) (!c) (ConvOp.toLin (α.1 A) x)
    have h : ConvOp.IsParC true (α.1 A) := ConvOp.parC_eq_self_iff.1 (hα A)
    rw [h c x, Bool.xor_true])

/-- **The Maurer–Cartan equation of a twisting morphism, at an element**:
`∂ (α x) + α (d x) + (α ⋆ α) x = 0`. -/
lemma mc_apply (α : TwistingDG R C P) {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    DGOperad.d (R := R) (ConvOp.toLin (α.1.1 A) x)
      + ConvOp.toLin (α.1.1 A) (DGCooperad.d (R := R) x)
      + ConvOp.toLin ((GrOperad.Inv.star R _ α.1 α.1).1 A) x = 0 := by
  obtain ⟨α, hα, -, hmc⟩ := α
  have h := congrArg (fun q : GrOperad.Inv R (ConvOp R C P) => ConvOp.toLin (q.1 A) x) hmc
  have htw : GrOperad.tw (R := R) true (α.1 A) = -α.1 A := by
    rw [GrOperad.tw_hom true (hα A), Bool.and_self, σ_true, neg_one_smul]
  have h' : DGOperad.d (R := R) (ConvOp.toLin (α.1 A) x)
      - ConvOp.toLin (GrOperad.tw (R := R) true (α.1 A)) (DGCooperad.d (R := R) x)
      + ConvOp.toLin ((GrOperad.Inv.star R _ α α).1 A) x = 0 := h
  rw [htw, ConvOp.toLin_neg, LinearMap.neg_apply, sub_neg_eq_add] at h'
  exact h'

/-- **A twisting morphism with values in the ideal is `π ∘ f` for a coaugmented morphism of graded
cooperads `f` into the bar construction of the dg operad, commuting with the differentials**: on
a conilpotent dg cooperad, over a `ℚ`-algebra, when in each arity the reduced cooperations or the
operations of the ideal form a projective module. -/
theorem exists_hom_dg [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen I (Fin k)))
    (α : TwistingDG R C P)
    (hIα : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1.1 A) x : P A) ∈ I.sub A) :
    ∃ g : GrCooperadHom R C 𝒞,
      g.app Unit (GrCooperad.Coaug.one (R := R)) = GrCooperad.Coaug.one (R := R) ∧
      (∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        piL I A (g.app A x) = ConvOp.toLin (α.1.1 A) x) ∧
      ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        g.app A (DGCooperad.d (R := R) x) = dTot hI A (g.app A x) := by
  obtain ⟨α, hα, hu, hmc0⟩ := α
  have hφ : ∀ (A : Type) [Fintype A] [DecidableEq A],
      GrCooperad.unitSpan R C A ≤ LinearMap.ker ((genOfDG α hα hIα).app A) :=
    fun A _ _ x hx => LinearMap.mem_ker.2 (IdealSp.ext I (hu A x hx))
  let g : GrCooperadHom R C 𝒞 :=
    FreeGrL.liftConil hC (FreeGrL.redLift (genOfDG α hα hIα) hφ) hproj
  have hg : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      piL I A (g.app A x) = ConvOp.toLin (α.1 A) x := fun A _ _ x => by
    rw [piL_eq_val_genCoef, FreeGrL.genCoef_liftConil]
    rfl
  have hV0 : ∀ v : BarGen I (Fin 0), v = 0 := fun v => IdealSp.ext I (hI0 _ (IdealSp.mem I v))
  refine ⟨g, FreeGrL.liftConil_app_one hC _ hproj, hg, fun A _ _ x =>
    (d_app_eq_app_d_dg hI hV0 g (fun A _ _ x => ?_) A x).symm⟩
  let g' : GrCooperadHom R C (BarCoop I) := g
  have hκ : GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) g') (pi I)
      = (α : GrOperad.Inv R (ConvOp R C (ZeroDG R P))) :=
    Subtype.ext (funext fun A => funext fun _ => funext fun _ => by
      rw [GrOperad.Inv.appHom_apply]
      ext x
      rw [ConvOp.preHom_app, LinearMap.comp_apply, pi_apply]
      exact hg A x)
  have h1 := piL_d_app_eq hI0 g' x
  rw [hκ] at h1
  have h1' : piL I A (d I A (g.app A x))
      = -ConvOp.toLin ((GrOperad.Inv.star R _ α α).1 A) x := h1
  have h4 := mc_apply ⟨α, hα, hu, hmc0⟩ x
  show piL I A ((d I A + (dInt hI).app A) (g.app A x)) = piL I A (g.app A (DGCooperad.d (R := R) x))
  rw [LinearMap.add_apply, map_add, h1', piL_dInt hI, hg, hg]
  rw [← sub_eq_zero, ← neg_eq_zero, ← h4]
  abel

end Exist

end Bar

end Operad
