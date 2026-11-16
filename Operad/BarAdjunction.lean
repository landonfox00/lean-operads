/-
# The bar side of the bar–cobar adjunction

For a graded operad `P`, an ideal `I` of `P` without operations without inputs, and a
conilpotent coaugmented dg cooperad `C`, **the coaugmented morphisms of dg cooperads
`C → B(P, I)` are the twisting morphisms `C → P` with values in `I`**, by composition with the
universal twisting morphism `π` (`Bar.homEquiv`; over a field of characteristic zero,
`Bar.homEquivField`). With the cobar adjunction `CobarDG.homEquiv` this is **the bar–cobar
adjunction** `Hom(ΩC, P) ≅ Tw(C, P) ≅ Hom(C, B(P, I))` (`Bar.barCobarEquiv`).

* **A coderivation into the cut cooperad is determined by its cogenerator part.** For a morphism
  of graded cooperads `f : C → B(P, I)` out of a dg cooperad, the defect `d ∘ f - f ∘ d` is a
  coderivation along `f`: `(ι ⋆ ι) ∘ (d f - f d) = ±(ι (d f - f d)) ⋆ (ι f) ± (ι f) ⋆
  (ι (d f - f d))` (`ConvOp.toLin_star_d_sub_mem`). So if all its values have at least `k ≥ 2`
  vertices they have at least `k + 1` (`Bar.ιι_d_sub_mem`, `Cobar.mem_vxGe_succ`), and
  **`π ∘ d ∘ f = π ∘ f ∘ d` implies `d ∘ f = f ∘ d`** (`Bar.d_app_eq_app_d`). This extends
  `Bar.d_app_eq_zero` to a cooperad with a differential and to ideals with operations of one
  input.
* **The Maurer–Cartan equation.** `π` is the cogenerator part, desuspended
  (`Bar.piL_eq_val_genCoef`), and `π ∘ d ∘ f = -(π f) ⋆ (π f)` (`Bar.piL_d_app_eq`). So a
  morphism of graded cooperads `f` for which `π ∘ f` satisfies the Maurer–Cartan equation
  commutes with the differentials (`Bar.app_d_of_mc`).
* **Existence and uniqueness.** A twisting morphism `α` with values in `I` suspends to a
  morphism of graded linear species `C → sI` (`Bar.genOf`), which lifts to a coaugmented
  morphism of graded cooperads into the cut cooperad `T^c(sI)` by its universal property
  (`FreeGrL.liftConil`); by the previous point it is a morphism of dg cooperads, with
  `π ∘ f = α` (`Bar.exists_dgHom`, `Bar.ofTwisting`, `Bar.twOfHom_ofTwisting`). A morphism of
  dg cooperads into the bar construction is determined by `π ∘ f` (`Bar.dgHom_ext`).
* **Naturality.** In the cooperad, `π ∘ (f ∘ h) = (π ∘ f) ∘ h` (`Bar.twOfHom_comp`). In the
  operad, a morphism `φ : P → P'` sending `I` into `I'` gives a morphism of dg cooperads
  `B(φ) : B(P, I) → B(P', I')` (`Bar.mapHom`) with `π ∘ B(φ) = φ ∘ π` (`Bar.piL_mapHom`).

Hypotheses. The ring is a `ℚ`-algebra. In each arity the reduced cooperations of `C` or the
operations of `I` form a projective module, as over a field: the universal property of the cut
cooperad (`Operad.CutCofreeConil`) needs it. `C` is conilpotent, which that universal property
needs when `I` has operations of one input. `P` carries the zero differential, the bar
construction of `Operad.Bar` being that of a graded operad.
-/
import Operad.BarWeights
import Operad.CutCofreeConil
import Operad.BarMap

universe u v w

namespace Operad

open Sym GerBV FreeGrL FreeGr
open scoped TensorProduct

namespace ConvOp

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DC : DGCooperad R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [D : DGCooperad R C']
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- An odd family precomposed with a morphism of graded cooperads is odd. -/
lemma isPar_appHom_preHom (f : GrCooperadHom R C C') {ι' : GrOperad.Inv R (ConvOp R C' Q)}
    {p : Bool} (hι : GrOperad.Inv.IsPar p ι') :
    GrOperad.Inv.IsPar p (GrOperad.Inv.appHom (preHom (P := Q) f) ι') := fun A _ _ => by
  show GrOperad.par (R := R) p ((preHom (P := Q) f).app A (ι'.1 A)) = _
  rw [← GrOperadHom.app_par, hι A]
  rfl

/-- **The coderivation rule for the square of an odd family**, on the cooperad itself:
`(κ ⋆ κ) ∘ d = (κ d) ⋆ κ - κ ⋆ (κ d)`, with `κ d` carrying the Koszul sign. -/
lemma toLin_star_d_self {κ : GrOperad.Inv R (ConvOp R C Q)} (hκ : GrOperad.Inv.IsPar true κ)
    {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    toLin ((GrOperad.Inv.star R _ κ κ).1 A) (DGCooperad.d (R := R) x)
      = toLin ((GrOperad.Inv.star R _
          (GrOperad.Inv.appDer (preDer (C := C) (P := Q)) κ) κ).1 A) x
        - toLin ((GrOperad.Inv.star R _ κ
          (GrOperad.Inv.appDer (preDer (C := C) (P := Q)) κ)).1 A) x := by
  have h := GrOperad.Inv.appDer_star (preDer (C := C) (P := Q)) hκ κ
  have e := congrArg (fun q : GrOperad.Inv R (ConvOp R C Q) => toLin (q.1 A) x) h
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.neg_apply, Bool.and_self,
    σ_true, neg_one_smul, ← sub_eq_add_neg] at e
  have hκκ : GrOperad.Inv.IsPar false (GrOperad.Inv.star R _ κ κ) := by
    have := GrOperad.Inv.isPar_star hκ hκ
    rwa [Bool.xor_self] at this
  refine Eq.trans ?_ e
  show _ = toLin (GrOperad.tw (R := R) true ((GrOperad.Inv.star R _ κ κ).1 A))
    (DGCooperad.d (R := R) x)
  rw [GrOperad.tw_hom true (hκκ A), Bool.true_and, σ_false, one_smul]

variable (f : GrCooperadHom R C C') {ι' : GrOperad.Inv R (ConvOp R C' Q)}
  (hι : GrOperad.Inv.IsPar true ι')
include hι

/-- **The coderivation rule, filtered, for the defect of a morphism**: if `ι ∘ (d f - f d)` and
`ι ∘ f` take values in `F` and `G`, with `F ∘ G` and `G ∘ F` in `H`, then
`(ι ⋆ ι) ∘ (d f - f d)` takes values in `H`. -/
theorem toLin_star_d_sub_mem
    {F G H : ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (Q A)}
    (hF : ∀ (A : Type) [Fintype A] [DecidableEq A] (b : Bool) (y : Q A), y ∈ F A →
      GrOperad.par (R := R) b y ∈ F A)
    (hG : ∀ (A : Type) [Fintype A] [DecidableEq A] (b : Bool) (y : Q A), y ∈ G A →
      GrOperad.par (R := R) b y ∈ G A)
    (hH : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (y : Q A), y ∈ H A → GrOperad.map (R := R) e y ∈ H B)
    (hFG : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (y : Q A) (z : Q B), y ∈ F A → z ∈ G B → GrOperad.comp (R := R) i y z ∈ H _)
    (hGF : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (y : Q A) (z : Q B), y ∈ G A → z ∈ F B → GrOperad.comp (R := R) i y z ∈ H _)
    (hα : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      toLin (ι'.1 A) (DGCooperad.d (R := R) (f.app A x)
        - f.app A (DGCooperad.d (R := R) x)) ∈ F A)
    (hβ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), toLin (ι'.1 A) (f.app A x) ∈ G A)
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) :
    toLin ((GrOperad.Inv.star R _ ι' ι').1 A) (DGCooperad.d (R := R) (f.app A x)
      - f.app A (DGCooperad.d (R := R) x)) ∈ H A := by
  have hb := isPar_appHom_preHom f hι
  have h1 := toLin_star_d f hι x
  have h2 : toLin ((GrOperad.Inv.star R _ ι' ι').1 A) (f.app A (DGCooperad.d (R := R) x))
      = toLin ((GrOperad.Inv.star R _ (GrOperad.Inv.appHom (preHom (P := Q) f) ι')
        (GrOperad.Inv.appHom (preHom (P := Q) f) ι')).1 A) (DGCooperad.d (R := R) x) := by
    rw [← GrOperad.Inv.appHom_star]
    rfl
  have h3 := toLin_star_d_self hb x
  have hc : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      toLin ((GrOperad.Inv.appDer (preDer (C := C) (P := Q))
        (GrOperad.Inv.appHom (preHom (P := Q) f) ι')).1 A) x
        = -toLin (ι'.1 A) (f.app A (DGCooperad.d (R := R) x)) := fun A _ _ x => by
    show toLin (GrOperad.tw (R := R) true ((GrOperad.Inv.appHom (preHom (P := Q) f) ι').1 A))
      (DGCooperad.d (R := R) x) = _
    rw [GrOperad.tw_hom true (hb A), Bool.and_self, σ_true, neg_one_smul, toLin_neg,
      LinearMap.neg_apply]
    rfl
  have hac : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      toLin ((GrOperad.Inv.appHom (preHom (P := Q) f)
          (GrOperad.Inv.appDer (preDer (C := C') (P := Q)) ι')
        - GrOperad.Inv.appDer (preDer (C := C) (P := Q))
          (GrOperad.Inv.appHom (preHom (P := Q) f) ι')).1 A) x ∈ F A := fun A _ _ x => by
    have e : toLin ((GrOperad.Inv.appHom (preHom (P := Q) f)
          (GrOperad.Inv.appDer (preDer (C := C') (P := Q)) ι')
        - GrOperad.Inv.appDer (preDer (C := C) (P := Q))
          (GrOperad.Inv.appHom (preHom (P := Q) f) ι')).1 A) x
        = -toLin (ι'.1 A) (DGCooperad.d (R := R) (f.app A x)
          - f.app A (DGCooperad.d (R := R) x)) := by
      show toLin ((GrOperad.Inv.appHom (preHom (P := Q) f)
          (GrOperad.Inv.appDer (preDer (C := C') (P := Q)) ι')).1 A) x
        - toLin ((GrOperad.Inv.appDer (preDer (C := C) (P := Q))
          (GrOperad.Inv.appHom (preHom (P := Q) f) ι')).1 A) x = _
      rw [toLin_appHom_preDer f hι, hc, map_sub]
      abel
    rw [e]
    exact neg_mem (hα A x)
  have hβ' : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      toLin ((GrOperad.Inv.appHom (preHom (P := Q) f) ι').1 A) x ∈ G A := fun A _ _ x => hβ A x
  set b := GrOperad.Inv.appHom (preHom (P := Q) f) ι'
  set a := GrOperad.Inv.appHom (preHom (P := Q) f)
    (GrOperad.Inv.appDer (preDer (C := C') (P := Q)) ι')
  set c := GrOperad.Inv.appDer (preDer (C := C) (P := Q)) b
  have es1 : GrOperad.Inv.star R _ (a - c) b
      = GrOperad.Inv.star R _ a b - GrOperad.Inv.star R _ c b := by
    rw [map_sub, LinearMap.sub_apply]
  have es2 : GrOperad.Inv.star R _ b (a - c)
      = GrOperad.Inv.star R _ b a - GrOperad.Inv.star R _ b c := map_sub _ _ _
  have key : toLin ((GrOperad.Inv.star R _ ι' ι').1 A) (DGCooperad.d (R := R) (f.app A x)
      - f.app A (DGCooperad.d (R := R) x))
      = toLin ((GrOperad.Inv.star R _ (a - c) b).1 A) x
        - toLin ((GrOperad.Inv.star R _ b (a - c)).1 A) x := by
    rw [map_sub, h1, h2, h3, es1, es2]
    show (toLin ((GrOperad.Inv.star R _ a b).1 A) x - toLin ((GrOperad.Inv.star R _ b a).1 A) x)
        - (toLin ((GrOperad.Inv.star R _ c b).1 A) x - toLin ((GrOperad.Inv.star R _ b c).1 A) x)
      = (toLin ((GrOperad.Inv.star R _ a b).1 A) x - toLin ((GrOperad.Inv.star R _ c b).1 A) x)
        - (toLin ((GrOperad.Inv.star R _ b a).1 A) x - toLin ((GrOperad.Inv.star R _ b c).1 A) x)
    abel
  rw [key]
  exact sub_mem (toLin_star_mem hG hH hFG hac hβ' A x) (toLin_star_mem hF hH hGF hβ' hac A x)

end ConvOp

namespace Bar

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P}
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]

local notation "𝒞" => FreeGrL R (BarGen I)

/-- **The coderivation rule for the defect**: when all the values of `d ∘ f - f ∘ d` have at
least `k` vertices, their convolution squares have weight at least `k + 1`. -/
lemma ιι_d_sub_mem [Algebra ℚ R] (f : GrCooperadHom R C 𝒞) {k : ℕ}
    (hk : ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      d I A' (f.app A' x') - f.app A' (DGCooperad.d (R := R) x') ∈ vxGe R (BarGen I) k A')
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) :
    ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) (d I A (f.app A x) - f.app A (DGCooperad.d (R := R) x))
      ∈ Cobar.wtGe (V := BarGen I) (k + 1) A := by
  exact ConvOp.toLin_star_d_sub_mem (D := dgFree I) f (Cobar.isPar_ι R 𝒞)
    (Cobar.wtGe_par_all k) (Cobar.wtGe_par_all 1) (Cobar.wtGe_map_all (k + 1))
    (Cobar.wtGe_comp_all k 1 (k + 1) le_rfl) (Cobar.wtGe_comp_all 1 k (k + 1) (by omega))
    (fun A' _ _ x' => Cobar.ιL_mem_wtGe (hk A' x')) (fun A' _ _ x' => Cobar.ιL_mem_wtGe_one _) A x

/-- **A morphism of graded cooperads from a dg cooperad into the bar construction commutes with
the differentials as soon as it does after the universal twisting morphism**:
`π ∘ d ∘ f = π ∘ f ∘ d` implies `d ∘ f = f ∘ d`, over a `ℚ`-algebra, for an ideal without
operations without inputs. The defect `d ∘ f - f ∘ d` is a coderivation along `f`, and a
coderivation into the cut cooperad is determined by its cogenerator part. -/
theorem d_app_eq_app_d [Algebra ℚ R] (hV0 : ∀ v : BarGen I (Fin 0), v = 0)
    (f : GrCooperadHom R C 𝒞)
    (hπ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      piL I A (d I A (f.app A x)) = piL I A (f.app A (DGCooperad.d (R := R) x)))
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) :
    d I A (f.app A x) = f.app A (DGCooperad.d (R := R) x) := by
  have hu : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      unitCoeffL R (BarGen I) A (d I A (f.app A x) - f.app A (DGCooperad.d (R := R) x)) = 0 := by
    intro A _ _ x
    by_cases hA : Nonempty (Unit ≃ A)
    · obtain ⟨e⟩ := hA
      have hx : x = SymSpecies.map (R := R) e (SymSpecies.map (R := R) e.symm x) :=
        (SymSpecies.map_map_symm e x).symm
      generalize SymSpecies.map (R := R) e.symm x = y at hx
      subst hx
      have hm : d I A (f.app A (SymSpecies.map (R := R) e y))
          - f.app A (DGCooperad.d (R := R) (SymSpecies.map (R := R) e y))
          = GrOperad.map (R := R) e (d I Unit (f.app Unit y)
            - f.app Unit (DGCooperad.d (R := R) y)) := by
        have e1 : f.app A (SymSpecies.map (R := R) e y)
            = GrOperad.map (R := R) e (f.app Unit y) := f.app_map e y
        have e2 : DGCooperad.d (R := R) (SymSpecies.map (R := R) e y)
            = SymSpecies.map (R := R) e (DGCooperad.d (R := R) y) :=
          (DGCooperad.map_d (R := R) e y).symm
        have e3 : f.app A (SymSpecies.map (R := R) e (DGCooperad.d (R := R) y))
            = GrOperad.map (R := R) e (f.app Unit (DGCooperad.d (R := R) y)) := f.app_map e _
        rw [e1, e2, e3, d_map, map_sub]
      have c1 : GrCooperad.counit (R := R) (C := 𝒞) (d I Unit (f.app Unit y)) = 0 :=
        (dgFree I).counit_d _
      have c2 : GrCooperad.counit (R := R) (C := 𝒞)
          (f.app Unit (DGCooperad.d (R := R) y)) = 0 :=
        (LinearMap.congr_fun f.counit_app _).trans (DGCooperad.counit_d (R := R) y)
      rw [hm, unitCoeffL_map, ← counit_eq_unitCoeffL, map_sub, c1, c2, sub_zero]
    · exact unitCoeffL_eq_zero (not_nonempty_iff.1 hA) _
  have hg : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      d I A (f.app A x) - f.app A (DGCooperad.d (R := R) x) ∈ vxGe R (BarGen I) 2 A := by
    intro A _ _ x
    have h2 := sub_ι_genCoef_mem (hu A x)
    have hker : vxGe R (BarGen I) 2 A ≤ LinearMap.ker (piL I A) := iSup_le fun j w hw => by
      rw [LinearMap.mem_ker, piL_vx (by have := j.2; omega) hw]
    have h3 := hker h2
    rw [LinearMap.mem_ker, map_sub, map_sub, hπ, sub_self, zero_sub, neg_eq_zero, piL_ι] at h3
    have hg0 : FreeGrL.genCoef R (BarGen I) A
        (d I A (f.app A x) - f.app A (DGCooperad.d (R := R) x)) = 0 := IdealSp.ext I h3
    rwa [hg0, map_zero, sub_zero] at h2
  have key : ∀ k, 2 ≤ k → ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      d I A' (f.app A' x') - f.app A' (DGCooperad.d (R := R) x') ∈ vxGe R (BarGen I) k A' := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hg
    | succ k hk ih =>
      exact fun A' _ _ x' => Cobar.mem_vxGe_succ hV0 hk (ih A' x') (ιι_d_sub_mem f ih A' x')
  exact sub_eq_zero.1 (eq_zero_of_forall_mem_vxGe fun p =>
    vxGe_anti (le_max_left p 2) (key _ (le_max_right p 2) A x))

end Bar

/-! ## Twisting morphisms into an ideal and morphisms into the bar construction -/

namespace Bar

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P}
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R (BarGen I))
local notation "𝒞" => FreeGrL R (BarGen I)
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R

/-- **The universal twisting morphism is the cogenerator part, desuspended.** -/
lemma piL_eq_val_genCoef [Algebra ℚ R] {A : Type} [Fintype A] [DecidableEq A] (z : 𝒞 A) :
    piL I A z = IdealSp.val I (FreeGrL.genCoef R (BarGen I) A z) := by
  obtain ⟨w, rfl⟩ := (𝒥).proj_surjective A z
  refine Lin.induction₁ (S := Reg (TreeOfArity (GrGen R (BarGen I))))
    (piL I A ∘ₗ (𝒥).proj A)
    ((I.sub A).subtype ∘ₗ FreeGrL.genCoef R (BarGen I) A ∘ₗ (𝒥).proj A) (fun t => ?_) w
  show piL I A ((𝒥).proj A (𝔟 t))
    = IdealSp.val I (FreeGrL.genCoef R (BarGen I) A ((𝒥).proj A (𝔟 t)))
  have hmem : (𝒥).proj A (𝔟 t) ∈ vx R (BarGen I) (FreeGr.treeOf t).weight A :=
    mem_eig.2 (by rw [← Cobar.wtD_eq_derSp, wtD_proj_bas])
  by_cases hw : (FreeGr.treeOf t).weight = 1
  · rw [hw] at hmem
    conv_lhs => rw [FreeGrL.eq_ι_genCoef hmem]
    exact piL_ι _
  · rw [piL_vx hw hmem, genCoef_proj, genCoefF_bas, coefReg_of_weight_ne hw]
    rfl

/-- The universal twisting morphism takes its values in the ideal. -/
lemma piL_mem [Algebra ℚ R] {A : Type} [Fintype A] [DecidableEq A] (z : 𝒞 A) :
    piL I A z ∈ I.sub A := by
  rw [piL_eq_val_genCoef]
  exact IdealSp.mem I _

/-- **`π ∘ d_B ∘ f = -(π f) ⋆ (π f)`** for a morphism of graded cooperads `f` into the bar
construction, by the Maurer–Cartan equation of `π`. -/
lemma piL_d_app_eq (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (f : GrCooperadHom R C (BarCoop I))
    {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    piL I A (DGCooperad.d (R := R) (C := BarCoop I) (f.app A x))
      = -ConvOp.toLin ((GrOperad.Inv.star R _
          (GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I))
          (GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I))).1 A) x := by
  have hmc := congrArg (fun q : GrOperad.Inv R (ConvOp R (BarCoop I) (ZeroDG R P)) =>
    ConvOp.toLin (q.1 A) (f.app A x)) (mc_pi I hI0)
  have hpi : GrOperad.tw (R := R) true ((pi I).1 A) = -(pi I).1 A := by
    rw [GrOperad.tw_hom true (isPar_pi A), Bool.and_self, σ_true, neg_one_smul]
  have key : (0 : ZeroDG R P A) - ConvOp.toLin (GrOperad.tw (R := R) true ((pi I).1 A))
      (DGCooperad.d (R := R) (C := BarCoop I) (f.app A x))
      + ConvOp.toLin ((GrOperad.Inv.star R _ (pi I) (pi I)).1 A) (f.app A x) = 0 := hmc
  rw [hpi, ConvOp.toLin_neg, LinearMap.neg_apply, zero_sub, neg_neg] at key
  rw [← GrOperad.Inv.appHom_star]
  exact eq_neg_of_add_eq_zero_left key

/-- **A morphism of graded cooperads into the bar construction whose composite with `π`
satisfies the Maurer–Cartan equation commutes with the differentials**, over a `ℚ`-algebra, for
an ideal without operations without inputs. -/
theorem app_d_of_mc [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (f : GrCooperadHom R C (BarCoop I))
    (hmc : GrOperad.Inv.appDer (ConvOp.postDer (C := C)
        (DGOperad.toDer (R := R) (P := ZeroDG R P)))
          (GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I))
      - GrOperad.Inv.appDer (ConvOp.preDer (C := C) (P := ZeroDG R P))
          (GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I))
      + GrOperad.Inv.star R _ (GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I))
          (GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I)) = 0)
    {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    f.app A (DGCooperad.d (R := R) x) = DGCooperad.d (R := R) (C := BarCoop I) (f.app A x) := by
  have hκ := ConvOp.isPar_appHom_preHom (Q := ZeroDG R P) f (isPar_pi (I := I))
  have hV0 : ∀ v : BarGen I (Fin 0), v = 0 := fun v => IdealSp.ext I (hI0 _ (IdealSp.mem I v))
  refine (d_app_eq_app_d hV0 (C := C) f (fun A _ _ x => ?_) A x).symm
  have h1 := piL_d_app_eq hI0 f x
  have h2 := congrArg (fun q : GrOperad.Inv R (ConvOp R C (ZeroDG R P)) =>
    ConvOp.toLin (q.1 A) x) hmc
  have htw : GrOperad.tw (R := R) true
      ((GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I)).1 A)
      = -(GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I)).1 A := by
    rw [GrOperad.tw_hom true (hκ A), Bool.and_self, σ_true, neg_one_smul]
  have key : (0 : ZeroDG R P A) - ConvOp.toLin (GrOperad.tw (R := R) true
      ((GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I)).1 A))
        (DGCooperad.d (R := R) x)
      + ConvOp.toLin ((GrOperad.Inv.star R _
          (GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I))
          (GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I))).1 A) x = 0 := h2
  rw [htw, ConvOp.toLin_neg, LinearMap.neg_apply, zero_sub, neg_neg] at key
  exact h1.trans (eq_neg_of_add_eq_zero_left key).symm

end Bar

/-! ## The bar side of the adjunction -/

namespace Bar

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P}
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C]

/-- **The morphism to the suspended ideal** of an odd family with values in the ideal. -/
noncomputable def genOf (α : GrOperad.Inv R (ConvOp R C (ZeroDG R P)))
    (hα : GrOperad.Inv.IsPar true α)
    (hI : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1 A) x : P A) ∈ I.sub A) :
    GrSpeciesHom R C (BarGen I) where
  app A _ _ := LinearMap.codRestrict (I.sub A)
    (show C A →ₗ[R] P A from ConvOp.toLin (α.1 A)) (hI A)
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

omit [GrCooperad.Coaug R C] in
lemma val_genOf (α : GrOperad.Inv R (ConvOp R C (ZeroDG R P)))
    (hα : GrOperad.Inv.IsPar true α)
    (hI : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1 A) x : P A) ∈ I.sub A) {A : Type} [Fintype A] [DecidableEq A]
    (x : C A) : IdealSp.val I ((genOf α hα hI).app A x) = ConvOp.toLin (α.1 A) x := rfl

/-- **A twisting morphism with values in the ideal is `π ∘ f` for a coaugmented morphism of dg
cooperads `f` into the bar construction**: on a conilpotent dg cooperad, over a `ℚ`-algebra,
when in each arity the reduced cooperations or the operations of the ideal form a projective
module. The morphism of graded cooperads is the one with cogenerator part the suspension of the
twisting morphism, and it commutes with the differentials by the Maurer–Cartan equation. -/
theorem exists_dgHom [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen I (Fin k)))
    (α : TwistingDG R C (ZeroDG R P))
    (hI : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1.1 A) x : P A) ∈ I.sub A) :
    ∃ f : DGCooperadHom R C (BarCoop I),
      f.app Unit (GrCooperad.Coaug.one (R := R)) = GrCooperad.Coaug.one (R := R) ∧
        twOfHom f = α.1 := by
  obtain ⟨α, hα, hu, hmc⟩ := α
  have hφ : ∀ (A : Type) [Fintype A] [DecidableEq A],
      GrCooperad.unitSpan R C A ≤ LinearMap.ker ((genOf α hα hI).app A) :=
    fun A _ _ x hx => LinearMap.mem_ker.2 (IdealSp.ext I (hu A x hx))
  let g : GrCooperadHom R C (FreeGrL R (BarGen I)) :=
    FreeGrL.liftConil hC (FreeGrL.redLift (genOf α hα hI) hφ) hproj
  have hg : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      piL I A (g.app A x) = ConvOp.toLin (α.1 A) x := fun A _ _ x => by
    rw [piL_eq_val_genCoef, FreeGrL.genCoef_liftConil]
    rfl
  let g' : GrCooperadHom R C (BarCoop I) := g
  have hκ : GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) g') (pi I) = α :=
    Subtype.ext (funext fun A => funext fun _ => funext fun _ => by
      rw [GrOperad.Inv.appHom_apply]
      ext x
      rw [ConvOp.preHom_app, LinearMap.comp_apply, pi_apply]
      exact hg A x)
  exact ⟨⟨g', fun {A} _ _ x => app_d_of_mc hI0 g' (by rw [hκ]; exact hmc) x⟩,
    FreeGrL.liftConil_app_one hC _ hproj, hκ⟩

omit [GrCooperad.Coaug R C] in
/-- **A morphism of dg cooperads into the bar construction is determined by its twisting
morphism** `π ∘ f`, over a `ℚ`-algebra, for an ideal without operations without inputs. -/
theorem dgHom_ext [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    {f f' : DGCooperadHom R C (BarCoop I)} (h : twOfHom f = twOfHom f') : f = f' := by
  have hV0 : ∀ v : BarGen I (Fin 0), v = 0 := fun v => IdealSp.ext I (hI0 _ (IdealSp.mem I v))
  have key : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), f.app A x = f'.app A x :=
    FreeGrL.app_eq_of_genCoef₀ (f := f.toGrCooperadHom) (f' := f'.toGrCooperadHom) hV0
      fun A _ _ x => IdealSp.ext I (by
        have e := congrArg (fun q : GrOperad.Inv R (ConvOp R C (ZeroDG R P)) =>
          ConvOp.toLin (q.1 A) x) h
        have e' : piL I A (f.app A x) = piL I A (f'.app A x) := e
        rwa [piL_eq_val_genCoef, piL_eq_val_genCoef] at e')
  obtain ⟨g, hg⟩ := f
  obtain ⟨g', hg'⟩ := f'
  obtain rfl : g = g' := GrCooperadHom.ext key
  rfl

/-- **The morphism of dg cooperads into the bar construction of a twisting morphism with values
in the ideal.** -/
noncomputable def ofTwisting [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen I (Fin k)))
    (α : {α : TwistingDG R C (ZeroDG R P) // ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1.1 A) x : P A) ∈ I.sub A}) : DGCooperadHom R C (BarCoop I) :=
  Classical.choose (exists_dgHom hI0 hC hproj α.1 α.2)

lemma ofTwisting_one [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen I (Fin k)))
    (α : {α : TwistingDG R C (ZeroDG R P) // ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1.1 A) x : P A) ∈ I.sub A}) :
    (ofTwisting hI0 hC hproj α).app Unit (GrCooperad.Coaug.one (R := R))
      = GrCooperad.Coaug.one (R := R) :=
  (Classical.choose_spec (exists_dgHom hI0 hC hproj α.1 α.2)).1

/-- **The morphism of a twisting morphism desuspends to it**: `π ∘ f = α`. -/
lemma twOfHom_ofTwisting [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen I (Fin k)))
    (α : {α : TwistingDG R C (ZeroDG R P) // ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1.1 A) x : P A) ∈ I.sub A}) :
    twOfHom (ofTwisting hI0 hC hproj α) = α.1.1 :=
  (Classical.choose_spec (exists_dgHom hI0 hC hproj α.1 α.2)).2

/-- **The bar side of the bar–cobar adjunction**: on a conilpotent coaugmented dg cooperad `C`,
the coaugmented morphisms of dg cooperads `C → B(P, I)` are the twisting morphisms `C → P` with
values in `I`, by composition with the universal twisting morphism. Over a `ℚ`-algebra, for an
ideal without operations without inputs, when in each arity the reduced cooperations or the
operations of the ideal form a projective module. -/
noncomputable def homEquiv [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen I (Fin k))) :
    {f : DGCooperadHom R C (BarCoop I) //
      f.app Unit (GrCooperad.Coaug.one (R := R)) = GrCooperad.Coaug.one (R := R)} ≃
    {α : TwistingDG R C (ZeroDG R P) // ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1.1 A) x : P A) ∈ I.sub A} where
  toFun f := ⟨twistingOfHom I hI0 f.1 f.2, fun A _ _ x => piL_mem (f.1.app A x)⟩
  invFun α := ⟨ofTwisting hI0 hC hproj α, ofTwisting_one hI0 hC hproj α⟩
  left_inv f := Subtype.ext (dgHom_ext hI0 (twOfHom_ofTwisting hI0 hC hproj
    ⟨twistingOfHom I hI0 f.1 f.2, fun A _ _ x => piL_mem (f.1.app A x)⟩))
  right_inv α := Subtype.ext (Subtype.ext (twOfHom_ofTwisting hI0 hC hproj α))

/-- The twisting morphism of a morphism into the bar construction is `π ∘ f`. -/
lemma homEquiv_apply [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen I (Fin k)))
    (f : {f : DGCooperadHom R C (BarCoop I) //
      f.app Unit (GrCooperad.Coaug.one (R := R)) = GrCooperad.Coaug.one (R := R)})
    {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    ConvOp.toLin ((homEquiv hI0 hC hproj f).1.1.1 A) x = piL I A (f.1.app A x) := rfl

/-- The morphism of a twisting morphism desuspends to it. -/
lemma piL_homEquiv_symm [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen I (Fin k)))
    (α : {α : TwistingDG R C (ZeroDG R P) // ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1.1 A) x : P A) ∈ I.sub A})
    {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    piL I A (((homEquiv hI0 hC hproj).symm α).1.app A x) = ConvOp.toLin (α.1.1.1 A) x :=
  congrArg (fun q : GrOperad.Inv R (ConvOp R C (ZeroDG R P)) => ConvOp.toLin (q.1 A) x)
    (twOfHom_ofTwisting hI0 hC hproj α)

end Bar

/-! ## The adjunction and its naturality -/

/-- **The composite of morphisms of dg cooperads.** -/
def DGCooperadHom.comp {R : Type*} [CommRing R]
    {C₁ : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C₁ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C₁ A)] [DGCooperad R C₁]
    {C₂ : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C₂ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C₂ A)] [DGCooperad R C₂]
    {C₃ : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C₃ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C₃ A)] [DGCooperad R C₃]
    (g : DGCooperadHom R C₂ C₃) (f : DGCooperadHom R C₁ C₂) : DGCooperadHom R C₁ C₃ where
  toGrCooperadHom := g.toGrCooperadHom.comp f.toGrCooperadHom
  app_d {A} _ _ x := by
    show g.app A (f.app A (DGCooperad.d (R := R) x)) = DGCooperad.d (R := R) (g.app A (f.app A x))
    rw [f.app_d, g.app_d]

namespace Bar

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P}
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C]

/-- **The bar–cobar adjunction** `Hom(ΩC, P) ≅ Tw(C, P) ≅ Hom(C, B(P, I))`: on a conilpotent
coaugmented dg cooperad `C` whose differential kills the coaugmentation, the morphisms of dg
operads `ΩC → P` sending the generators into `I` are the coaugmented morphisms of dg cooperads
`C → B(P, I)`. Over a `ℚ`-algebra, for an ideal without operations without inputs, when in each
arity the reduced cooperations or the operations of the ideal form a projective module; `P` has
the zero differential. -/
noncomputable def barCobarEquiv [Algebra ℚ R] [DGCooperad.DOne R C]
    (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen I (Fin k))) :
    {φ : CobarDGHom R C (ZeroDG R P) // ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (φ.1.app A (Cobar.ιL R C A x) : P A) ∈ I.sub A} ≃
    {f : DGCooperadHom R C (BarCoop I) //
      f.app Unit (GrCooperad.Coaug.one (R := R)) = GrCooperad.Coaug.one (R := R)} :=
  (CobarDG.homEquiv.subtypeEquiv fun _ => Iff.rfl).trans (homEquiv hI0 hC hproj).symm

/-- **Under the adjunction, the two morphisms have the same twisting morphism**:
`π ∘ f = φ ∘ ι`. -/
lemma piL_barCobarEquiv [Algebra ℚ R] [DGCooperad.DOne R C]
    (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen I (Fin k)))
    (φ : {φ : CobarDGHom R C (ZeroDG R P) // ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (φ.1.app A (Cobar.ιL R C A x) : P A) ∈ I.sub A})
    {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    piL I A ((barCobarEquiv hI0 hC hproj φ).1.app A x) = φ.1.1.app A (Cobar.ιL R C A x) :=
  piL_homEquiv_symm hI0 hC hproj _ x

omit [GrCooperad.Coaug R C] in
/-- **Naturality in the cooperad**: the twisting morphism of `f ∘ h` is that of `f` precomposed
with `h`. -/
lemma twOfHom_comp {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [DGCooperad R C']
    (f : DGCooperadHom R C (BarCoop I)) (h : DGCooperadHom R C' C) :
    twOfHom (f.comp h)
      = GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) h.toGrCooperadHom) (twOfHom f) :=
  rfl

/-- **The bar side of the adjunction over a field of characteristic zero**: no projectivity
hypothesis is left. -/
noncomputable def homEquivField {K : Type u} [Field K] [CharZero K]
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (P A)] [GrOperad K P]
    {I : GrOperadIdeal K P}
    {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (C A)] [DGCooperad K C]
    [GrCooperad.Coaug K C] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hC : GrCooperad.Conilpotent K C) :
    {f : DGCooperadHom K C (BarCoop I) //
      f.app Unit (GrCooperad.Coaug.one (R := K)) = GrCooperad.Coaug.one (R := K)} ≃
    {α : TwistingDG K C (ZeroDG K P) // ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1.1 A) x : P A) ∈ I.sub A} :=
  homEquiv hI0 hC fun _ => Or.inl inferInstance

section Functorial

variable {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [GrOperad R P']
  {I' : GrOperadIdeal R P'} (φ : GrOperadHom R P P')
  (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), x ∈ I.sub A → φ.app A x ∈ I'.sub A)

/-- **The morphism of bar constructions** `B(P, I) → B(P', I')` of a morphism of graded operads
sending `I` into `I'`, a morphism of dg cooperads. -/
noncomputable def mapHom : DGCooperadHom R (BarCoop I) (BarCoop I') where
  toGrCooperadHom := FreeGrL.mapCoop (mapGen φ hφ)
  app_d x := map_d φ hφ x

omit [DGCooperad R C] [GrCooperad.Coaug R C] in
lemma epsHom_mapSp :
    (epsHom I').comp (FreeGrL.mapSp (mapGen φ hφ)) = (DualExt.mapHom φ).comp (epsHom I) :=
  FreeGrL.hom_ext fun A _ _ w => by
    show (epsHom I').app A ((FreeGrL.mapSp (mapGen φ hφ)).app A
        ((FreeGrL.ι R (BarGen I)).app A w))
      = (DualExt.mapHom φ).app A ((epsHom I).app A ((FreeGrL.ι R (BarGen I)).app A w))
    rw [FreeGrL.mapSp_ι, epsHom_ι, epsHom_ι]
    exact DualExt.ext (map_zero (φ.app A)).symm rfl

omit [DGCooperad R C] [GrCooperad.Coaug R C] in
/-- **Naturality in the operad**: `π ∘ B(φ) = φ ∘ π`. -/
lemma piL_mapHom {A : Type} [Fintype A] [DecidableEq A] (z : BarCoop I A) :
    piL I' A ((mapHom φ hφ).app A z) = φ.app A (piL I A z) :=
  congrArg DualExt.snd (congrArg (fun ψ : GrOperadHom R (FreeGrL R (BarGen I))
    (DualExt R P' true) => ψ.app A z) (epsHom_mapSp φ hφ))

end Functorial

end Bar

end Operad
