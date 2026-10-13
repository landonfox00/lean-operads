/-
# The Koszul dual cooperad in the bar construction

For quadratic data `(E, r)` presenting `P = T(E)/(r)`, and an ideal `I` of `P` containing the
generators, the suspended generators `sE → sI` (`Koszul.barGen`) induce a morphism of cut
cooperads `T^c(sE) → B(P, I)`, and by restriction **the comparison morphism `P^¡ → B(P, I)`**
(`Koszul.toBar`). It desuspends to the Koszul twisting morphism: **`π ∘ i = κ`**
(`Koszul.pi_toBar`), so by the Maurer–Cartan equations of `π` and `κ`, **`π ∘ d_B ∘ i = 0`**
(`Koszul.piL_d_toBar`). Since a morphism into the cofree cut cooperad is determined by its
cogenerator part (`Bar.d_app_eq_zero`), **`d_B ∘ i = 0`** (`Koszul.d_toBar`): over a field of
characteristic zero, `i` commutes with the differentials, `P^¡` having the zero differential.
-/
import Operad.BarWeights
import Operad.CutFunctor

universe u

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-- **The composite of morphisms of graded cooperads.** -/
def GrCooperadHom.comp {R : Type*} [CommRing R]
    {C₁ : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C₁ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C₁ A)] [GrCooperad R C₁]
    {C₂ : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C₂ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C₂ A)] [GrCooperad R C₂]
    {C₃ : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C₃ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C₃ A)] [GrCooperad R C₃]
    (g : GrCooperadHom R C₂ C₃) (f : GrCooperadHom R C₁ C₂) : GrCooperadHom R C₁ C₃ where
  toGrSpeciesHom := g.toGrSpeciesHom.comp f.toGrSpeciesHom
  counit_app := by
    rw [show (g.toGrSpeciesHom.comp f.toGrSpeciesHom).app Unit = g.app Unit ∘ₗ f.app Unit
      from rfl, ← LinearMap.comp_assoc, g.counit_app, f.counit_app]
  decomp_app i := by
    rw [show (g.toGrSpeciesHom.comp f.toGrSpeciesHom).app _ = g.app _ ∘ₗ f.app _ from rfl,
      show (g.toGrSpeciesHom.comp f.toGrSpeciesHom).app _ = g.app _ ∘ₗ f.app _ from rfl,
      show (g.toGrSpeciesHom.comp f.toGrSpeciesHom).app _ = g.app _ ∘ₗ f.app _ from rfl,
      ← LinearMap.comp_assoc, g.decomp_app, LinearMap.comp_assoc, f.decomp_app,
      ← LinearMap.comp_assoc, ← TensorProduct.map_comp]

namespace Bar

variable {R : Type*} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P} {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]

/-- **`π ∘ d_B ∘ f = -(π f) ⋆ (π f)`** for a morphism of graded cooperads `f` into the bar
construction, by the Maurer–Cartan equation of `π`: so `π ∘ d_B ∘ f` vanishes when the
convolution square of `π f` does. -/
lemma piL_d_app (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (f : GrCooperadHom R C (BarCoop I))
    {κ : GrOperad.Inv R (ConvOp R C (ZeroDG R P))}
    (hπ : GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I) = κ)
    {A : Type} [Fintype A] [DecidableEq A] (x : C A)
    (hκ : ConvOp.toLin ((GrOperad.Inv.star R _ κ κ).1 A) x = 0) :
    piL I A (DGCooperad.d (R := R) (C := BarCoop I) (f.app A x)) = 0 := by
  subst hπ
  have hmc := congrArg (fun q : GrOperad.Inv R (ConvOp R (BarCoop I) (ZeroDG R P)) =>
    ConvOp.toLin (q.1 A) (f.app A x)) (mc_pi I hI0)
  have hpi : GrOperad.tw (R := R) true ((pi I).1 A) = -(pi I).1 A := by
    rw [GrOperad.tw_hom true (isPar_pi A), Bool.and_self, σ_true, neg_one_smul]
  have h3 : GrOperad.Inv.star R _
      (GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I))
      (GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f) (pi I))
        = GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R P) f)
            (GrOperad.Inv.star R _ (pi I) (pi I)) :=
    (GrOperad.Inv.appHom_star _ _ _).symm
  have h4 : ConvOp.toLin ((GrOperad.Inv.star R _ (pi I) (pi I)).1 A) (f.app A x) = 0 := by
    rw [h3] at hκ
    exact hκ
  have key : (0 : ZeroDG R P A) - ConvOp.toLin (GrOperad.tw (R := R) true ((pi I).1 A))
      (DGCooperad.d (R := R) (C := BarCoop I) (f.app A x))
      + ConvOp.toLin ((GrOperad.Inv.star R _ (pi I) (pi I)).1 A) (f.app A x) = 0 := hmc
  rw [hpi, h4, ConvOp.toLin_neg, LinearMap.neg_apply, add_zero, zero_sub, neg_neg] at key
  exact key

end Bar

namespace Koszul

variable {R : Type u} [Field R] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} (I : GrOperadIdeal R (Pres R E r))
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)

local notation "𝒥" => GrOperadIdeal.span R r

/-- **The suspended generators** `sE → sI`. -/
noncomputable def barGen : GrSpeciesHom R (GrSpecies.Shift E R) (BarGen I) where
  app A _ _ := ((𝒥).proj A ∘ₗ (FreeGrL.ι R E).app A).codRestrict (I.sub A) (hE A)
  app_map {A B} _ _ _ _ σ' w := IdealSp.ext I (by
    show (𝒥).proj B ((FreeGrL.ι R E).app B (SymSpecies.map (R := R) (V := E) σ' w))
      = GrOperad.map (R := R) σ' ((𝒥).proj A ((FreeGrL.ι R E).app A w))
    rw [(FreeGrL.ι R E).app_map, FreeGrL.symMap_eq, ← (GrOperadIdeal.span R r).projHom_app,
      (GrOperadIdeal.span R r).projHom.app_map]
    rfl)
  app_par {A} _ _ c w := IdealSp.ext I (by
    show (𝒥).proj A ((FreeGrL.ι R E).app A (GrSpecies.par (R := R) (V := E) (!c) w))
      = GrOperad.par (R := R) (!c) ((𝒥).proj A ((FreeGrL.ι R E).app A w))
    rw [(FreeGrL.ι R E).app_par, FreeGrL.grPar_eq, ← (GrOperadIdeal.span R r).projHom_app,
      (GrOperadIdeal.span R r).projHom.app_par]
    rfl)

lemma val_barGen {A : Type} [Fintype A] [DecidableEq A] (w : E A) :
    IdealSp.val I ((barGen I hE).app A (GrSpecies.Shift.of A w))
      = (𝒥).proj A ((FreeGrL.ι R E).app A w) := rfl

/-- **The comparison morphism `P^¡ → B(P, I)`**: the inclusion of the Koszul dual cooperad into
the cut cooperad `T^c(sE)`, followed by the morphism of cut cooperads induced by `sE → sI`. -/
noncomputable def toBar : GrCooperadHom R (Dual R E r) (BarCoop I) :=
  (FreeGrL.mapCoop (barGen I hE)).comp (dualSub R E r).inclHom

/-- The comparison morphism, into the cut cooperad underlying the bar construction. -/
noncomputable def toCut : GrCooperadHom R (Dual R E r) (FreeGrL R (BarGen I)) :=
  (FreeGrL.mapCoop (barGen I hE)).comp (dualSub R E r).inclHom

lemma toBar_app {A : Type} [Fintype A] [DecidableEq A] (x : Dual R E r A) :
    (toBar I hE).app A x = (FreeGrL.mapSp (barGen I hE)).app A ((dualSub R E r).incl A x) := rfl

/-- The suspended generators desuspend to the generators of `P`. -/
lemma epsHom_mapSp :
    (Bar.epsHom I).comp (FreeGrL.mapSp (barGen I hE))
      = (DualExt.mapHom (𝒥).projHom).comp (epsHom R E) :=
  FreeGrL.hom_ext fun A _ _ w => by
    have h1 : (Bar.epsHom I).app A ((FreeGrL.mapSp (barGen I hE)).app A
        ((FreeGrL.ι R (GrSpecies.Shift E R)).app A w))
        = DualExt.mk 0 (IdealSp.val I ((barGen I hE).app A w)) := by
      rw [FreeGrL.mapSp_ι]
      exact Bar.epsHom_ι _
    have h2 : (epsHom R E).app A ((FreeGrL.ι R (GrSpecies.Shift E R)).app A w)
        = DualExt.mk 0 ((FreeGrL.ι R E).app A w) := by
      rw [epsHom, FreeGrL.homEquiv_symm_ι]
      rfl
    show (Bar.epsHom I).app A ((FreeGrL.mapSp (barGen I hE)).app A
        ((FreeGrL.ι R (GrSpecies.Shift E R)).app A w))
      = (DualExt.mapHom (𝒥).projHom).app A ((epsHom R E).app A
        ((FreeGrL.ι R (GrSpecies.Shift E R)).app A w))
    rw [h1, h2]
    exact DualExt.ext (map_zero ((𝒥).projHom.app A)).symm rfl

/-- **The universal twisting morphism after the comparison morphism desuspends.** -/
lemma piL_mapSp {A : Type} [Fintype A] [DecidableEq A] (y : Cut R E A) :
    Bar.piL I A ((FreeGrL.mapSp (barGen I hE)).app A y) = (𝒥).proj A (kapL R E A y) :=
  congrArg DualExt.snd (congrArg (fun φ : GrOperadHom R (Cut R E) (DualExt R (Pres R E r) true) =>
    φ.app A y) (epsHom_mapSp I hE))

/-- **`π ∘ i = κ`.** -/
lemma pi_toBar :
    GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R (Pres R E r)) (toBar I hE)) (Bar.pi I)
      = kappa R E r :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => by
    rw [GrOperad.Inv.appHom_apply]
    ext x
    rw [ConvOp.preHom_app, LinearMap.comp_apply, Bar.pi_apply, kappa_apply]
    exact piL_mapSp I hE _)

omit hE in
/-- **`κ ⋆ κ = 0`**, `P` having the zero differential. -/
lemma toLin_star_kappa {A : Type} [Fintype A] [DecidableEq A] (x : Dual R E r A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (kappa R E r) (kappa R E r)).1 A) x = 0 := by
  have h := congrArg (fun q : GrOperad.Inv R (ConvOp R (Dual R E r) (ZeroDG R (Pres R E r))) =>
    ConvOp.toLin (q.1 A) x) (mc_kappa r)
  simp only [Submodule.coe_add, Pi.add_apply, ConvOp.toLin_add, LinearMap.add_apply,
    ConvOp.appDer_postDer_apply] at h
  exact (zero_add _).symm.trans h

/-- **`π ∘ d_B ∘ i = 0`**, by the Maurer–Cartan equations of `π` and `κ`. -/
lemma piL_d_toBar (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) {A : Type} [Fintype A] [DecidableEq A]
    (x : Dual R E r A) :
    Bar.piL I A (DGCooperad.d (R := R) (C := BarCoop I) ((toBar I hE).app A x)) = 0 :=
  Bar.piL_d_app hI0 (toBar I hE) (pi_toBar I hE) x (toLin_star_kappa x)

/-- **The comparison morphism commutes with the differentials**: `d_B ∘ i = 0`, over a field
of characteristic zero, for an ideal without operations with at most one input. -/
theorem d_toBar [CharZero R]
    (hI1 : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ y ∈ I.sub B, y = 0)
    {A : Type} [Fintype A] [DecidableEq A] (x : Dual R E r A) :
    DGCooperad.d (R := R) (C := BarCoop I) ((toBar I hE).app A x) = 0 := by
  have hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ v : BarGen I B, v = 0 := fun B _ _ hB v => IdealSp.ext I (hI1 B hB _ (IdealSp.mem I v))
  have hI0 : ∀ y ∈ I.sub (Fin 0), y = 0 := hI1 (Fin 0) (by simp)
  exact Bar.d_app_eq_zero hred (toCut I hE) (fun A _ _ x => piL_d_toBar I hE hI0 x) A x

end Koszul

end Operad
