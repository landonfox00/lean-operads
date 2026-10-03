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
    have hp : GrSpecies.par (R := R) (!(xor b c))
        (cobarVal R V b v i (GrSpecies.par (R := R) c w) m h)
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

/-! ## The universal twisting morphism on decorated trees -/

variable (R V) in
/-- **The universal twisting morphism on the trees decorated by homogeneous elements.** -/
noncomputable def ιF : GrOperad.Inv R (ConvOp R (FreeGr R (grGenPar R V)) (CobarGr R 𝒞)) :=
  GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) (FreeGrL.projHom R V)) (Cobar.ι R 𝒞)

lemma ιF_apply (y : FreeGr R (grGenPar R V) A) :
    ConvOp.toLin ((ιF R V).1 A) y = Cobar.ιL R 𝒞 A ((𝒥).proj A y) := rfl

lemma isParC_ιF (A : Type) [Fintype A] [DecidableEq A] : ConvOp.IsParC true ((ιF R V).1 A) :=
  ConvOp.parC_eq_self_iff.1
    (((ConvOp.preHom (P := CobarGr R 𝒞) (FreeGrL.projHom R V)).app_par true
      ((Cobar.ι R 𝒞).1 A)).symm.trans
      (congrArg ((ConvOp.preHom (P := CobarGr R 𝒞) (FreeGrL.projHom R V)).app A)
        (Cobar.isPar_ι R 𝒞 A)))

lemma ιF_leaf {x : Reg (TreeOfArity (GrGen R V)) A} (hx : (treeOf x).isLeaf = true) :
    ConvOp.toLin ((ιF R V).1 A) (SgnLin.bas (treeSgn (grGenPar R V)) R x) = 0 := by
  obtain ⟨e, rfl⟩ := eq_map_one_of_isLeaf hx
  rw [ιF_apply, ← SgnLin.map_bas]
  exact Cobar.ιL_unitSpan R 𝒞 (GrCooperad.map_one_mem e)

lemma ιι_proj (y : FreeGr R (grGenPar R V) A) :
    ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) ((𝒥).proj A y)
      = ConvOp.toLin ((GrOperad.Inv.star R _ (ιF R V) (ιF R V)).1 A) y :=
  congrArg (fun q : GrOperad.Inv R (ConvOp R (FreeGr R (grGenPar R V)) (CobarGr R 𝒞)) =>
    ConvOp.toLin (q.1 A) y)
    (GrOperad.Inv.appHom_star (ConvOp.preHom (P := CobarGr R 𝒞) (FreeGrL.projHom R V))
      (Cobar.ι R 𝒞) (Cobar.ι R 𝒞))

/-- **The bar differential of the merge on a composite of two generators** merges them. -/
lemma hM_comp_ιL {k l : ℕ} {c : 𝒞 (Fin k)} {pa : Bool} (hc : GrOperad.par (R := R) pa c = c)
    (i : Fin k) (c' : 𝒞 (Fin l)) :
    hM R V _ (GrOperad.comp (R := R) i (Cobar.ιL R 𝒞 (Fin k) c) (Cobar.ιL R 𝒞 (Fin l) c'))
      = σ R (!pa) • Cobar.ιL R 𝒞 _ (GrOperad.comp (R := R) i (FreeGrL.secC R V (Fin k) c)
          (FreeGrL.secC R V (Fin l) c')) := by
  refine ((cobarMerge R V).d_comp i _ _).trans ?_
  have h1 : (cobarMerge R V).d (Fin k) (Cobar.ιL R 𝒞 (Fin k) c) = 0 := hM_ιL c
  have h2 : (cobarMerge R V).d (Fin l) (Cobar.ιL R 𝒞 (Fin l) c') = 0 := hM_ιL c'
  refine (congrArg₂ (fun a b => GrOperad.comp (R := R) i a (Cobar.ιL R 𝒞 (Fin l) c')
    + GrOperad.comp (R := R) i (GrOperad.tw (R := R) true (Cobar.ιL R 𝒞 (Fin k) c)) b
    + mM R V i (Cobar.ιL R 𝒞 (Fin k) c) (Cobar.ιL R 𝒞 (Fin l) c')) h1 h2).trans ?_
  refine Eq.trans ?_ (mM_ιL_fin hc i c')
  simp only [map_zero, LinearMap.zero_apply, zero_add]

variable {X : Type} [Fintype X] [DecidableEq X]

lemma unitCoeffL_bas {x : Reg (TreeOfArity (GrGen R V)) A} (hx : (treeOf x).isLeaf = false) :
    FreeGrL.unitCoeffL R V A ((𝒥).proj A (SgnLin.bas (treeSgn (grGenPar R V)) R x)) = 0 := by
  rw [FreeGrL.unitCoeffL_proj, unitCoeff_bas, if_neg (by rw [hx]; decide)]

lemma ιL_proj_smul (c : R) (y : FreeGr R (grGenPar R V) A) :
    Cobar.ιL R 𝒞 A ((𝒥).proj A (c • y)) = c • Cobar.ιL R 𝒞 A ((𝒥).proj A y) := by
  rw [map_smul, map_smul]

lemma ιL_proj_map (e : A ≃ B) (y : FreeGr R (grGenPar R V) A) :
    GrOperad.map (R := R) e (Cobar.ιL R 𝒞 A ((𝒥).proj A y))
      = Cobar.ιL R 𝒞 B ((𝒥).proj B (GrOperad.map (R := R) e y)) := by
  rw [← Cobar.ιL_map]
  rfl

/-- **The generators have no unit component.** -/
lemma unitCoeffL_ι (v : CobarGen R 𝒞 A) :
    FreeGrL.unitCoeffL R (CobarGen R 𝒞) A ((FreeGrL.ι R (CobarGen R 𝒞)).app A v) = 0 := by
  rw [GrSpeciesHom.app_eq_chart (FreeGrL.ι R (CobarGen R 𝒞)) (Fintype.equivFin A).symm,
    FreeGrL.ι_app_fin]
  show FreeGrL.unitCoeffL R (CobarGen R 𝒞) A (GrOperad.map (R := R) _
    ((𝒥Ω).proj _ (gen _) + (𝒥Ω).proj _ (gen _))) = 0
  rw [FreeGrL.unitCoeffL_map, map_add, FreeGrL.unitCoeffL_proj, FreeGrL.unitCoeffL_proj,
    unitCoeff_gen, unitCoeff_gen, add_zero]

lemma unitCoeffL_ιL (c : 𝒞 A) :
    FreeGrL.unitCoeffL R (CobarGen R 𝒞) A (Cobar.ιL R 𝒞 A c) = 0 := unitCoeffL_ι _

/-- **The term of a factorization**, as a composite of generators. -/
lemma repW_ιF {k l : ℕ} (i : Fin k) (p : Reg (TreeOfArity (GrGen R V)) (Fin k))
    (q : Reg (TreeOfArity (GrGen R V)) (Fin l)) (e : Without (Fin k) i ⊕ Fin l ≃ X) :
    repW (ιF R V) (ιF R V) e p q
      = GrOperad.map (R := R) e ((σ R (cSgn (grGenPar R V) i p q)
          * σ R (Tree.tpar (grGenPar R V) (treeOf p))) •
          GrOperad.comp (R := R) i
            (Cobar.ιL R 𝒞 (Fin k) ((𝒥).proj (Fin k) (SgnLin.bas (treeSgn (grGenPar R V)) R p)))
            (Cobar.ιL R 𝒞 (Fin l) ((𝒥).proj (Fin l) (SgnLin.bas (treeSgn (grGenPar R V)) R q))))
      := by
  have e1 : ConvOp.toLin ((ιF R V).1 (Fin k))
      (GrSpecies.tw (R := R) true (SgnLin.bas (treeSgn (grGenPar R V)) R p))
      = σ R (Tree.tpar (grGenPar R V) (treeOf p)) •
          Cobar.ιL R 𝒞 (Fin k) ((𝒥).proj (Fin k) (SgnLin.bas (treeSgn (grGenPar R V)) R p)) := by
    rw [ιF_apply, tw_bas, ιL_proj_smul]
  unfold repW
  refine congrArg (GrOperad.map (R := R) e) ?_
  refine (congrArg (fun z => σ R (cSgn (grGenPar R V) i p q) • GrOperad.comp (R := R) i z
    (Cobar.ιL R 𝒞 (Fin l) ((𝒥).proj (Fin l) (SgnLin.bas (treeSgn (grGenPar R V)) R q)))) e1).trans
    ?_
  exact (congrArg (fun z => σ R (cSgn (grGenPar R V) i p q) • z)
    (LinearMap.map_smul₂ _ _ _ _)).trans (smul_smul _ _ _)

/-- **The merge after the cut at a factorization** gives back the tree, with a minus sign. -/
lemma hM_repW {k l : ℕ} (i : Fin k) (p : Reg (TreeOfArity (GrGen R V)) (Fin k))
    (q : Reg (TreeOfArity (GrGen R V)) (Fin l)) (e : Without (Fin k) i ⊕ Fin l ≃ X)
    (hp : (treeOf p).isLeaf = false) (hq : (treeOf q).isLeaf = false) :
    hM R V X (repW (ιF R V) (ιF R V) e p q)
      = -Cobar.ιL R 𝒞 X ((𝒥).proj X (SgnLin.bas (treeSgn (grGenPar R V)) R
          (SetOperad.map e (SetOperad.comp i p q)))) := by
  have hpa : GrOperad.par (R := R) (Tree.tpar (grGenPar R V) (treeOf p))
      ((𝒥).proj (Fin k) (SgnLin.bas (treeSgn (grGenPar R V)) R p))
      = (𝒥).proj (Fin k) (SgnLin.bas (treeSgn (grGenPar R V)) R p) :=
    congrArg ((𝒥).proj (Fin k)) (SgnLin.par_bas p)
  have e2 := hM_comp_ιL (R := R) (V := V) hpa i
    ((𝒥).proj (Fin l) (SgnLin.bas (treeSgn (grGenPar R V)) R q))
  have e3 : FreeGrL.secC R V (Fin k) ((𝒥).proj (Fin k) (SgnLin.bas (treeSgn (grGenPar R V)) R p))
      = (𝒥).proj (Fin k) (SgnLin.bas (treeSgn (grGenPar R V)) R p) :=
    FreeGrL.secC_of_unitCoeff (unitCoeffL_bas hp)
  have e4 : FreeGrL.secC R V (Fin l) ((𝒥).proj (Fin l) (SgnLin.bas (treeSgn (grGenPar R V)) R q))
      = (𝒥).proj (Fin l) (SgnLin.bas (treeSgn (grGenPar R V)) R q) :=
    FreeGrL.secC_of_unitCoeff (unitCoeffL_bas hq)
  have e5 : GrOperad.comp (R := R) i
      ((𝒥).proj (Fin k) (SgnLin.bas (treeSgn (grGenPar R V)) R p))
      ((𝒥).proj (Fin l) (SgnLin.bas (treeSgn (grGenPar R V)) R q))
      = σ R (cSgn (grGenPar R V) i p q) • (𝒥).proj _ (SgnLin.bas (treeSgn (grGenPar R V)) R
          (SetOperad.comp i p q)) := by
    show (𝒥).proj _ (GrOperad.comp (R := R) i _ _) = _
    rw [comp_bas_eq, map_smul]
  have e6 : GrOperad.comp (R := R) i
      (FreeGrL.secC R V (Fin k) ((𝒥).proj (Fin k) (SgnLin.bas (treeSgn (grGenPar R V)) R p)))
      (FreeGrL.secC R V (Fin l) ((𝒥).proj (Fin l) (SgnLin.bas (treeSgn (grGenPar R V)) R q)))
      = σ R (cSgn (grGenPar R V) i p q) • (𝒥).proj _ (SgnLin.bas (treeSgn (grGenPar R V)) R
          (SetOperad.comp i p q)) := by
    rw [e3, e4, e5]
  have e7 := e2.trans (congrArg (fun z => σ R (!(Tree.tpar (grGenPar R V) (treeOf p))) •
    Cobar.ιL R 𝒞 _ z) e6)
  have e8 := ιL_proj_smul (R := R) (V := V) (σ R (cSgn (grGenPar R V) i p q))
    (SgnLin.bas (treeSgn (grGenPar R V)) R (SetOperad.comp i p q))
  have s1 := repW_ιF (R := R) (V := V) i p q e
  have s2 := ((cobarMerge R V).map_d e ((σ R (cSgn (grGenPar R V) i p q)
          * σ R (Tree.tpar (grGenPar R V) (treeOf p))) •
          GrOperad.comp (R := R) i
            (Cobar.ιL R 𝒞 (Fin k) ((𝒥).proj (Fin k) (SgnLin.bas (treeSgn (grGenPar R V)) R p)))
            (Cobar.ιL R 𝒞 (Fin l) ((𝒥).proj (Fin l) (SgnLin.bas (treeSgn (grGenPar R V)) R q)))))
  refine (congrArg (hM R V X) s1).trans (s2.symm.trans ?_)
  refine (congrArg (GrOperad.map (R := R) e) ((map_smul _ _ _).trans
    (congrArg _ (e7.trans (congrArg _ e8))))).trans ?_
  have hsign : σ R (cSgn (grGenPar R V) i p q) * σ R (Tree.tpar (grGenPar R V) (treeOf p))
      * σ R (!(Tree.tpar (grGenPar R V) (treeOf p))) * σ R (cSgn (grGenPar R V) i p q) = -1 := by
    generalize Tree.tpar (grGenPar R V) (treeOf p) = a
    generalize cSgn (grGenPar R V) i p q = c
    cases a <;> cases c <;> simp
  have hW := (ιL_proj_map (R := R) (V := V) e
    (SgnLin.bas (treeSgn (grGenPar R V)) R (SetOperad.comp i p q))).trans
    (congrArg (fun y => Cobar.ιL R 𝒞 X ((𝒥).proj X y)) (SgnLin.map_bas e _))
  rw [smul_smul, smul_smul, hsign, neg_one_smul, map_neg]
  exact congrArg Neg.neg hW

/-- **The merge after the cut at a vertex** gives back the tree, with a minus sign. -/
lemma hM_starV (t : Reg (TreeOfArity (GrGen R V)) X) {v : ℕ}
    (hv : v ∈ Finset.Ico 1 (treeOf t).weight) :
    hM R V X (starV (ιF R V) (ιF R V) t v)
      = -Cobar.ιL R 𝒞 X ((𝒥).proj X (SgnLin.bas (treeSgn (grGenPar R V)) R t)) := by
  rw [Finset.mem_Ico] at hv
  obtain ⟨e, he⟩ := exists_rep t hv.2
  have hst := starV_eq (ιF R V) (ιF R V) he (Tree.isLeaf_cutV _ _ hv.2)
  have hvert : vert ⟨((treeOf t).cutV v).2.2, Tree.lt_arity_cutV _ v hv.2⟩
      (stdT ((treeOf t).cutV v).1) = v := by
    show (treeOf (stdT _)).vb ((stdT _).1.rank _) = v
    rw [treeOf_stdT, rank_stdT]
    exact Tree.vb_cutV _ _ hv.2
  rw [hvert] at hst
  refine (congrArg (hM R V X) hst).trans ((hM_repW _ (stdT ((treeOf t).cutV v).1)
    (stdT ((treeOf t).cutV v).2.1) e
    (Tree.isLeaf_cutV_fst hv.1 hv.2 rfl) (Tree.isLeaf_cutV _ _ hv.2)).trans ?_)
  rw [he]

/-- **The merge after the cobar differential on a generator** counts the edges of its tree:
`h (d (ι t)) = (w - 1) ι t` for a tree `t` with `w` vertices, none of them nullary. -/
theorem hM_d_ιL_bas (t : Reg (TreeOfArity (GrGen R V)) X) (ht : (treeOf t).NoNull) :
    hM R V X ((Cobar.d R 𝒞).app X
        (Cobar.ιL R 𝒞 X ((𝒥).proj X (SgnLin.bas (treeSgn (grGenPar R V)) R t))))
      = ((treeOf t).weight - 1) •
          Cobar.ιL R 𝒞 X ((𝒥).proj X (SgnLin.bas (treeSgn (grGenPar R V)) R t)) := by
  have h1 := Cobar.d_ιL R 𝒞 ((𝒥).proj X (SgnLin.bas (treeSgn (grGenPar R V)) R t))
  rw [ιι_proj, star_bas (ιF R V) (ιF R V) isParC_ιF (fun _ _ _ x hx => ιF_leaf hx)
    (fun _ _ _ x hx => ιF_leaf hx) t] at h1
  have hfilter : (Finset.Ico 1 (treeOf t).weight).filter
      (fun v => 0 < ((treeOf t).cutV v).2.1.arity) = Finset.Ico 1 (treeOf t).weight :=
    Finset.filter_true_of_mem fun v hv =>
      ((ht.cutV (Finset.mem_Ico.1 hv).2).2).arity_pos
  rw [hfilter] at h1
  refine (congrArg (hM R V X) h1).trans ?_
  rw [map_neg, map_sum, Finset.sum_congr rfl fun v hv => hM_starV t hv, Finset.sum_neg_distrib,
    neg_neg, Finset.sum_const, Nat.card_Ico]

end Cobar

end Generators

end Operad
