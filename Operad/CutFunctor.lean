/-
# Functoriality of the cut cooperad

A morphism of graded linear species `f : V → W` relabels the decorations of trees by homogeneous
elements (`FreeGrL.genMap`). On the free graded operads on the homogeneous elements this is a
signed-basis morphism along the relabelling of the vertices, bijective on factorizations, hence a
morphism of decomposition cooperads (`FreeGrL.mapF`). It descends to the free graded operads on
`V` and `W` as the morphism extending `f` (`FreeGrL.proj_mapF`), so **the morphism of free graded
operads extending `f` is a morphism of cut cooperads** (`FreeGrL.mapCoop`).
-/
import Operad.FreeGrDer
import Operad.CofreeGrL
import Operad.BarDescent

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr FreeReg
open scoped TensorProduct

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)
local notation "𝒥'" => GrOperadIdeal.span R (grLinRel R W)

variable (f : GrSpeciesHom R V W)

/-- **The relabelling of the homogeneous generators** along `f`. -/
def genMap (k : ℕ) (g : GrGen R V k) : GrGen R W k :=
  ⟨(f.app (Fin k) g.1.1, g.1.2), by
    show GrSpecies.par (R := R) g.1.2 (f.app (Fin k) g.1.1) = f.app (Fin k) g.1.1
    rw [← f.app_par]
    exact congrArg (f.app (Fin k)) g.2⟩

/-- The signed basis values of the relabelling: the corollas of the relabelled generators. -/
noncomputable def mapVal : SBVal (grGenPar R V) (grGenPar R W) where
  sg _ _ := false
  tree k g := Reg.std (corolla (genMap f k g))
  tot_eq k g := treeSgn_tot (genMap f k g)

/-- **The relabelling on the free graded operads on the homogeneous elements.** -/
noncomputable abbrev mapF : GrOperadHom R (FreeGr R (grGenPar R V)) (FreeGr R (grGenPar R W)) :=
  (mapVal f).hom R

lemma mapF_gen {k : ℕ} (g : GrGen R V k) :
    (mapF f).app (Fin k) (gen g) = gen (genMap f k g) := by
  rw [mapF, SBVal.hom_gen]
  show σ R false • _ = _
  rw [σ_false, one_smul]
  rfl

lemma mapVal_ψ : ((mapVal f).sbm R).ψ = relabel (genMap f) :=
  regHom_ext fun k e => by
    rw [SBVal.sbm_ψ_std, relabel_std]
    rfl

/-- **The relabelling descends to the morphism extending `f`.** -/
lemma proj_mapF (x : FreeGr R (grGenPar R V) A) :
    (𝒥').proj A ((mapF f).app A x) = (mapSp f).app A ((𝒥).proj A x) := by
  have h : (𝒥').projHom.comp (mapF f) = (mapSp f).comp (𝒥).projHom :=
    FreeGr.hom_ext fun k g => by
      obtain ⟨⟨v, b⟩, hv⟩ := g
      show (𝒥').proj (Fin k) ((mapF f).app (Fin k) (gen _))
        = (mapSp f).app (Fin k) ((𝒥).proj (Fin k) (gen _))
      rw [mapF_gen]
      show FreeGr.presGen (grLinRel R W) _ = (mapSp f).app (Fin k) (FreeGr.presGen (grLinRel R V) _)
      rw [← ι_app_hom hv, mapSp_ι]
      exact (ι_app_hom (genMap f k ⟨(v, b), hv⟩).2).symm
  exact congrArg (fun φ : GrOperadHom R (FreeGr R (grGenPar R V)) (FreeGrL R W) => φ.app A x) h

lemma comp_proj_mapF (A : Type) [Fintype A] [DecidableEq A] :
    (𝒥').proj A ∘ₗ (mapF f).app A = (mapSp f).app A ∘ₗ (𝒥).proj A :=
  LinearMap.ext (proj_mapF f)

/-- The relabelling is a morphism of decomposition cooperads. -/
lemma decomp_mapF (i : A) :
    SgnLin.decompT R (treeSgn (grGenPar R W)) (B := B) i ∘ₗ (mapF f).app (Without A i ⊕ B)
      = TensorProduct.map ((mapF f).app A) ((mapF f).app B) ∘ₗ
          SgnLin.decompT R (treeSgn (grGenPar R V)) i :=
  ((mapVal f).sbm R).decomp_app (by rw [mapVal_ψ]; exact relabel_factBij _) i

/-- The relabelling preserves the counits. -/
lemma counit_mapF :
    GrCooperad.counit (R := R) (C := FreeGr R (grGenPar R W)) ∘ₗ (mapF f).app Unit
      = GrCooperad.counit (R := R) (C := FreeGr R (grGenPar R V)) := by
  refine Finsupp.lhom_ext fun t c => ?_
  have h1 : (Finsupp.single t c : FreeGr R (grGenPar R V) Unit)
      = c • SgnLin.bas (treeSgn (grGenPar R V)) R t :=
    (Finsupp.smul_single_one t c).symm
  show GrCooperad.counit (R := R) (C := FreeGr R (grGenPar R W))
      ((mapF f).app Unit (Finsupp.single t c : FreeGr R (grGenPar R V) Unit))
    = GrCooperad.counit (R := R) (C := FreeGr R (grGenPar R V))
      (Finsupp.single t c : FreeGr R (grGenPar R V) Unit)
  rw [h1, map_smul, map_smul, map_smul]
  congr 1
  cases ht : (treeOf t).isLeaf
  · have hne : ∀ {T : ℕ → Type v} (s : Reg (TreeOfArity T) Unit),
        (treeOf s).isLeaf = false → s ≠ SetOperad.one := by
      rintro T s hs rfl
      exact Bool.noConfusion hs
    have hψ : ((mapVal f).sbm R).ψ.app Unit t = relabelR (genMap f) t := by
      rw [mapVal_ψ]
      rfl
    rw [((mapVal f).sbm R).app_bas, hψ, map_smul]
    show σ R _ • (Finsupp.single (relabelR (genMap f) t) (1 : R)) SetOperad.one
      = (Finsupp.single t (1 : R)) SetOperad.one
    rw [Finsupp.single_eq_of_ne (hne t ht).symm, Finsupp.single_eq_of_ne, smul_zero]
    refine (hne _ ?_).symm
    rw [treeOf_relabelR]
    cases h : Tree.relabel (genMap f) (treeOf t) with
    | leaf => exact absurd (Tree.eq_leaf_of_relabel _ h) (by
        intro h'
        rw [h'] at ht
        exact Bool.noConfusion ht)
    | node _ _ => rfl
  · obtain ⟨e, rfl⟩ := eq_map_one_of_isLeaf ht
    rw [← SgnLin.map_bas, GrOperadHom.app_map]
    show GrCooperad.counit (R := R) (C := FreeGr R (grGenPar R W))
        (GrOperad.map (R := R) e ((mapF f).app Unit (GrOperad.one (R := R)))) = _
    obtain rfl : e = Equiv.refl Unit := Subsingleton.elim _ _
    rw [(mapF f).app_one, GrOperad.map_refl, GrOperad.map_refl]
    show (Finsupp.single (SetOperad.one : Reg (TreeOfArity (GrGen R W)) Unit) (1 : R))
        SetOperad.one
      = (Finsupp.single (SetOperad.one : Reg (TreeOfArity (GrGen R V)) Unit) (1 : R))
        SetOperad.one
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same]

/-- **The morphism of free graded operads extending a morphism of graded linear species is a
morphism of cut cooperads.** -/
noncomputable def mapCoop : GrCooperadHom R (FreeGrL R V) (FreeGrL R W) where
  toGrSpeciesHom := (mapSp f).toGrSpeciesHom
  counit_app := LinearMap.ext fun X => by
    obtain ⟨x, rfl⟩ := (𝒥).proj_surjective Unit X
    show GrCooperad.counit (R := R) (C := FreeGrL R W) ((mapSp f).app Unit ((𝒥).proj Unit x))
      = GrCooperad.counit (R := R) (C := FreeGrL R V) ((𝒥).proj Unit x)
    rw [← proj_mapF]
    exact (LinearMap.congr_fun (projHom R W).counit_app _).trans
      ((LinearMap.congr_fun (counit_mapF f) x).trans
        (LinearMap.congr_fun (projHom R V).counit_app x).symm)
  decomp_app {A B} _ _ _ _ i := LinearMap.ext fun X => by
    obtain ⟨x, rfl⟩ := (𝒥).proj_surjective _ X
    have e1 : GrCooperad.decomp (R := R) (C := FreeGrL R V) i ((𝒥).proj _ x)
        = TensorProduct.map ((𝒥).proj A) ((𝒥).proj B)
          (GrCooperad.decomp (R := R) (C := FreeGr R (grGenPar R V)) i x) :=
      LinearMap.congr_fun ((projHom R V).decomp_app (A := A) (B := B) i) x
    have e2 : GrCooperad.decomp (R := R) (C := FreeGrL R W) i ((𝒥').proj _ ((mapF f).app _ x))
        = TensorProduct.map ((𝒥').proj A) ((𝒥').proj B)
          (GrCooperad.decomp (R := R) (C := FreeGr R (grGenPar R W)) i ((mapF f).app _ x)) :=
      LinearMap.congr_fun ((projHom R W).decomp_app (A := A) (B := B) i) _
    have e3 : GrCooperad.decomp (R := R) (C := FreeGr R (grGenPar R W)) i ((mapF f).app _ x)
        = TensorProduct.map ((mapF f).app A) ((mapF f).app B)
          (GrCooperad.decomp (R := R) (C := FreeGr R (grGenPar R V)) i x) :=
      LinearMap.congr_fun (decomp_mapF f (A := A) (B := B) i) x
    show GrCooperad.decomp (R := R) (C := FreeGrL R W) i ((mapSp f).app _ ((𝒥).proj _ x))
      = TensorProduct.map ((mapSp f).app A) ((mapSp f).app B)
          (GrCooperad.decomp (R := R) (C := FreeGrL R V) i ((𝒥).proj _ x))
    rw [← proj_mapF, e1, e2, e3, TensorProduct.map_map, TensorProduct.map_map, comp_proj_mapF,
      comp_proj_mapF]

@[simp] lemma mapCoop_app (x : FreeGrL R V A) : (mapCoop f).app A x = (mapSp f).app A x := rfl

end FreeGrL

end Operad
