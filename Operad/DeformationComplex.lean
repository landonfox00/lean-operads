/-
# The deformation complex of a morphism out of a quadratic operad

Let `P = T(E)/(r)` be presented by generators `E` and relators `r` (`Koszul.Pres`), with Koszul
dual cooperad `P^¡` and Koszul twisting morphism `κ : P^¡ → P` (`Operad.GrKoszulDual`), over a
field. Let `Q` be a dg operad and `φ : P → Q` a morphism of graded operads with values in the
cycles of `Q`: a morphism of dg operads, `P` carrying the zero differential.

* **The deformation complex** `Def(φ) = Hom_𝔖(P^¡, Q)` (`Koszul.Def`): the equivariant maps
  `P^¡ → Q`, with the differential `∂ + [φ κ, -]` (`Koszul.defD`). It is a complex
  (`Koszul.defD_defD`): `φ ∘ κ` is a twisting morphism (`Koszul.twistingOf`), the composite of
  a twisting morphism with a morphism of dg operads being one (`Twisting.map`), and the twisted
  differential of a twisting morphism squares to zero (`Twisting.twD_twD`). Its cohomology is
  `Koszul.DefH`. **The deformation complex of the operad `P`** is the case of the identity,
  with differential `[κ, -]` (`Koszul.defDOperad`, `Koszul.defDOperad_apply`).
* **Derivations along a morphism and the product.** A derivation `D` along a morphism `f` of
  graded operads acts on invariant families (`GrOperad.Inv.appDerAlong`) with
  `D (q ⋆ q') = D q ⋆ f q' ± f q ⋆ D q'` (`GrOperad.Inv.appDerAlong_star`), and composing with it
  is a derivation of convolution operads along composition with `f` (`ConvOp.postDerAlong`).
* **Cochains of weight one.** A derivation `D` of `T(E)` along `T(E) → P → Q` has the cochain
  `D ∘ κ_T` (`Koszul.ofDerT`), which determines it (`Koszul.ofDerT_injective`), the generators
  `sE` lying in `P^¡`: these are the cochains of weight one, the maps `sE → Q`. Its bracket with
  `φ κ` is `±D ∘ (κ_T ⋆ κ_T)` (`Koszul.bracket_ofDerT`).
* **The cocycles of weight one are the derivations of `P` along `φ`** (`Koszul.derEquiv`), for
  quadratic relators over a field of characteristic zero, without generators without inputs:
  `[φ κ, D ∘ κ_T] = 0` exactly when `D` vanishes on the relators
  (`Koszul.bracket_ofDerT_eq_zero_iff`), since `κ_T ⋆ κ_T` maps `P^¡` onto the relations
  (`Koszul.star_incl_mem_relSp`, `Koszul.exists_dual_star_eq`), and such a `D` descends to `P`
  (`Koszul.derOfT`). The cochain `D ∘ κ` of a derivation of `P` along `φ` is closed for the
  bracket with `φ κ` for any relators (`Koszul.bracket_ofDer`), and it is a cocycle of
  `Def(φ)` when `D` has values in the cycles of `Q` (`Koszul.defD_ofDer_eq_zero`).

The cochains are graded by parity only, so the cohomology `Koszul.DefH` is not split by weight
here. The coboundaries of weight one, the inner derivations, and the obstructions in weight two
are not in this file.
-/
import Operad.InvLie
import Operad.GrKoszulDual
import Operad.KoszulCorel
import Operad.PInfinity
import Mathlib.LinearAlgebra.Quotient.Basic

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Twisting morphisms and morphisms of dg operads -/

namespace Twisting

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]
  {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [DGOperad R P']

/-- **The composite of a twisting morphism with a morphism of dg operads** is a twisting
morphism. -/
noncomputable def map (g : GrOperadHom R P P')
    (hg : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : P A),
      g.app A (DGOperad.d (R := R) y) = DGOperad.d (R := R) (g.app A y))
    (α : Twisting R C P) : Twisting R C P' :=
  ⟨GrOperad.Inv.appHom (ConvOp.postHom (C := C) g) α.1,
    fun A _ _ => by
      show GrOperad.par (R := R) true ((ConvOp.postHom (C := C) g).app A (α.1.1 A)) = _
      rw [← GrOperadHom.app_par, α.2.1 A]
      rfl,
    fun A _ _ x hx => by
      rw [ConvOp.appHom_postHom_apply, α.2.2.1 A x hx, map_zero],
    by
      have h1 : GrOperad.Inv.appDer (convD R C P')
          (GrOperad.Inv.appHom (ConvOp.postHom (C := C) g) α.1)
          = GrOperad.Inv.appHom (ConvOp.postHom (C := C) g)
              (GrOperad.Inv.appDer (convD R C P) α.1) :=
        Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun y =>
          (hg A _).symm)
      rw [h1, ← GrOperad.Inv.appHom_star, ← map_add, α.2.2.2, map_zero]⟩

lemma map_apply (g : GrOperadHom R P P')
    (hg : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : P A),
      g.app A (DGOperad.d (R := R) y) = DGOperad.d (R := R) (g.app A y))
    (α : Twisting R C P) {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    ConvOp.toLin ((map g hg α).1.1 A) x = g.app A (ConvOp.toLin (α.1.1 A) x) := rfl

end Twisting

/-! ## Derivations along a morphism, on invariant families -/

namespace GrOperad.Inv

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {Q' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q' A)] [GrOperad R Q']
  {f : GrOperadHom R Q Q'} {e : Bool}

/-- **A derivation along a morphism, applied to invariant families.** -/
def appDerAlong (D : GrDer f e) : Inv R Q →ₗ[R] Inv R Q' where
  toFun q := ⟨fun A _ _ => D.app A (q.1 A), fun A B _ _ _ _ σ' => by
    show map (R := R) σ' (D.app A (q.1 A)) = D.app B (q.1 B)
    rw [← D.app_map, map_apply]⟩
  map_add' q q' := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_add (D.app A) _ _)
  map_smul' c q := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_smul (D.app A) _ _)

@[simp] lemma appDerAlong_apply (D : GrDer f e) (q : Inv R Q) (A : Type) [Fintype A]
    [DecidableEq A] : (appDerAlong D q).1 A = D.app A (q.1 A) := rfl

/-- A derivation along a morphism shifts parities. -/
theorem isPar_appDerAlong {p : Bool} (D : GrDer f e) {q : Inv R Q} (hq : IsPar p q) :
    IsPar (xor p e) (appDerAlong D q) := by
  intro A _ _
  show par (R := R) (xor p e) (D.app A (q.1 A)) = D.app A (q.1 A)
  rw [← D.app_par, hq A]

/-- **A derivation along a morphism `f` is a derivation of the product along `f`**:
`D (q ⋆ q') = D q ⋆ f q' ± f q ⋆ D q'`, with the Koszul sign of the left factor. -/
theorem appDerAlong_star {p : Bool} (D : GrDer f e) {q : Inv R Q} (hq : IsPar p q)
    (q' : Inv R Q) :
    appDerAlong D (star R Q q q')
      = star R Q' (appDerAlong D q) (appHom f q')
        + σ R (e && p) • star R Q' (appHom f q) (appDerAlong D q') := by
  refine Subtype.ext (funext fun X => funext fun _ => funext fun _ => ?_)
  show D.app X (∑ S ∈ nonempties X, term (R := R) q.1 q'.1 X S)
    = ∑ S ∈ nonempties X, term (R := R) (appDerAlong D q).1 (appHom f q').1 X S
      + σ R (e && p) • ∑ S ∈ nonempties X,
          term (R := R) (appHom f q).1 (appDerAlong D q').1 X S
  rw [map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [term, D.app_map, D.app_comp, appDerAlong_apply, appHom_apply]
  rw [tw_hom e (show par (R := R) p (f.app _ (q.1 _)) = f.app _ (q.1 _) by
    rw [← GrOperadHom.app_par, hq _]), map_smul, LinearMap.smul_apply, map_add, map_smul]

end GrOperad.Inv

namespace ConvOp

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [GrOperad R P']
  {f : GrOperadHom R P P'}

/-- **Composing with a derivation along `f` is a derivation of convolution operads along
composition with `f`.** -/
noncomputable def postDerAlong {e : Bool} (D : GrDer f e) :
    GrDer (postHom (C := C) f) e where
  app A _ _ := postL (D.app A)
  app_par c g := by
    ext x
    simp only [par_def, toLin_postL, LinearMap.comp_apply, parC_apply, map_sum, D.app_par]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Bool.xor_assoc, Bool.xor_comm c e, ← Bool.xor_assoc]
  app_map σ' g := by
    ext x
    simp only [map_def, toLin_postL, LinearMap.comp_apply, mapC_apply, D.app_map]
  app_one := by
    ext x
    simp only [one_def, toLin_postL, LinearMap.comp_apply, oneC_apply, map_smul, D.app_one,
      smul_zero, toLin_zero, LinearMap.zero_apply]
  app_comp {A₁ B₁} _ _ _ _ i g h := by
    ext x
    simp only [comp_def, toLin_postL, LinearMap.comp_apply, toLin_compC, toLin_add,
      LinearMap.add_apply]
    induction GrCooperad.decomp (R := R) (C := C) i x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hp : ∀ q : Bool, parC (C := C) q (postL (D.app B₁) h)
          = postL (C := C) (D.app B₁) (parC (xor q e) h) :=
        fun q => by
          ext y
          simp only [toLin_postL, LinearMap.comp_apply, parC_apply, map_sum, D.app_par]
          refine Finset.sum_congr rfl fun d _ => ?_
          congr 1
          cases d <;> cases q <;> cases e <;> rfl
      have hp' : ∀ q : Bool, parC (C := C) q ((postHom (C := C) f).app B₁ h)
          = (postHom (C := C) f).app B₁ (parC q h) :=
        fun q => ((postHom (C := C) f).app_par q h).symm
      simp only [kap, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
        LinearMap.comp_apply, mu_tmul, D.app_comp, Finset.sum_add_distrib,
        hp, hp', toLin_postL, postHom_app, tw_apply, GrSpecies.tw_tw]
      congr 1
      simp only [Fintype.sum_bool]
      cases e <;> simp [add_comm]
    | add a b ha hb =>
      simp only [map_add, ha, hb]
      abel

@[simp] lemma postDerAlong_app {e : Bool} (D : GrDer f e) {A : Type} [Fintype A]
    [DecidableEq A] (g : ConvOp R C P A) :
    toLin ((postDerAlong (C := C) D).app A g) = D.app A ∘ₗ toLin g := rfl

end ConvOp

/-! ## The deformation complex -/

namespace Koszul

variable {R : Type u} [Field R] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [DGOperad R Q]
  (φ : GrOperadHom R (ZeroDG R (Pres R E r)) Q)
  (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : Pres R E r A),
    DGOperad.d (R := R) (φ.app A y) = 0)

/-- **The twisting morphism `φ ∘ κ : P^¡ → Q`** of a morphism of dg operads `φ : P → Q` out of
the presented operad, which carries the zero differential. -/
noncomputable def twistingOf : Twisting R (Dual R E r) Q :=
  (twisting R E r).map φ fun A _ _ y => by
    rw [hφ]
    exact map_zero (φ.app A)

variable (R E r Q) in
/-- **The cochains of the deformation complex**: the equivariant maps `P^¡ → Q`. -/
noncomputable abbrev Def := GrOperad.Inv R (ConvOp R (Dual R E r) Q)

/-- **The differential of the deformation complex of `φ`**: `∂ + [φ κ, -]`. -/
noncomputable def defD : Def R E r Q →ₗ[R] Def R E r Q :=
  GrOperad.Inv.twD (Twisting.convD R (Dual R E r) Q) (twistingOf φ hφ).1

/-- **The deformation complex is a complex.** -/
theorem defD_defD (x : Def R E r Q) : defD φ hφ (defD φ hφ x) = 0 :=
  Twisting.twD_twD (twistingOf φ hφ) x

end Koszul

/-! ## Derivations and cochains of weight one -/

/-- **A derivation along `f`, after a morphism `g`**, is a derivation along `f ∘ g`. -/
def GrDer.precomp {R : Type u} [CommRing R]
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
    {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [GrOperad R P']
    {f : GrOperadHom R P Q} {e : Bool} (D : GrDer f e) (g : GrOperadHom R P' P) :
    GrDer (f.comp g) e where
  app A _ _ := D.app A ∘ₗ g.app A
  app_par c x := by
    simp only [LinearMap.comp_apply, g.app_par, D.app_par]
  app_map σ' x := by
    simp only [LinearMap.comp_apply, g.app_map, D.app_map]
  app_one := by
    simp only [LinearMap.comp_apply, g.app_one, D.app_one]
  app_comp i x y := by
    simp only [LinearMap.comp_apply, g.app_comp, D.app_comp]
    rfl

namespace Koszul

variable {R : Type u} [Field R] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [DGOperad R Q]
  (φ : GrOperadHom R (ZeroDG R (Pres R E r)) Q)
  (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : Pres R E r A),
    DGOperad.d (R := R) (φ.app A y) = 0)
  {e : Bool}

/-- The morphism `T(E) → P → Q`. -/
noncomputable def freeHom : GrOperadHom R (FreeGrL R E) Q :=
  φ.comp (GrOperadHom.toZeroDG (GrOperadIdeal.span R r).projHom)

lemma freeHom_app {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R E A) :
    (freeHom φ).app A x = φ.app A ((GrOperadIdeal.span R r).proj A x) := rfl

variable (R E r) in
/-- **The desuspension map on the Koszul dual cooperad**, `κ_T : P^¡ → T(E)`. -/
noncomputable def kapD : GrOperad.Inv R (ConvOp R (Dual R E r) (FreeGrL R E)) :=
  GrOperad.Inv.appHom (ConvOp.preHom (P := FreeGrL R E) (dualSub R E r).inclHom) (kapT R E)

lemma kapD_apply {A : Type} [Fintype A] [DecidableEq A] (c : Dual R E r A) :
    ConvOp.toLin ((kapD R E r).1 A) c = kapL R E A ((dualSub R E r).incl A c) := rfl

lemma isPar_kapD : GrOperad.Inv.IsPar true (kapD R E r) := fun A _ _ => by
  show GrOperad.par (R := R) true ((ConvOp.preHom (P := FreeGrL R E)
    (dualSub R E r).inclHom).app A ((kapT R E).1 A)) = _
  rw [← GrOperadHom.app_par, isPar_kapT A]
  rfl

include hφ in
/-- `φ ∘ κ` is the desuspension map followed by `T(E) → Q`. -/
lemma appHom_freeHom_kapD :
    GrOperad.Inv.appHom (ConvOp.postHom (C := Dual R E r) (freeHom φ)) (kapD R E r)
      = (twistingOf φ hφ).1 :=
  Subtype.ext (funext fun _ => funext fun _ => funext fun _ => ConvOp.ext fun _ => rfl)

/-- **The convolution square of the desuspension map on the Koszul dual cooperad.** -/
lemma toLin_star_kapD {A : Type} [Fintype A] [DecidableEq A] (c : Dual R E r A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (kapD R E r) (kapD R E r)).1 A) c
      = ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A)
          ((dualSub R E r).incl A c) :=
  congrArg (fun q : GrOperad.Inv R (ConvOp R (Dual R E r) (FreeGrL R E)) =>
    ConvOp.toLin (q.1 A) c)
    (GrOperad.Inv.appHom_star (ConvOp.preHom (P := FreeGrL R E) (dualSub R E r).inclHom)
      (kapT R E) (kapT R E)).symm

/-- On the Koszul dual cooperad the convolution square of the desuspension map lands in the
ideal of the relators. -/
lemma star_kapD_mem {A : Type} [Fintype A] [DecidableEq A] (c : Dual R E r A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (kapD R E r) (kapD R E r)).1 A) c
      ∈ (GrOperadIdeal.span R r).sub A := by
  exact (toLin_star_kapD c).symm ▸ GrSubCooperad.cogen_le (admissible R E r) A c.2

/-- **The cochain of a derivation of `T(E)` along `T(E) → Q`**: the derivation after the
desuspension map. -/
noncomputable def ofDerT (D : GrDer (freeHom φ) e) : Def R E r Q :=
  GrOperad.Inv.appDerAlong (ConvOp.postDerAlong (C := Dual R E r) D) (kapD R E r)

lemma ofDerT_apply (D : GrDer (freeHom φ) e) {A : Type} [Fintype A] [DecidableEq A]
    (c : Dual R E r A) :
    ConvOp.toLin ((ofDerT φ D).1 A) c = D.app A (kapL R E A ((dualSub R E r).incl A c)) := rfl

lemma isPar_ofDerT (D : GrDer (freeHom φ) e) : GrOperad.Inv.IsPar (!e) (ofDerT φ D) := by
  have h := GrOperad.Inv.isPar_appDerAlong (ConvOp.postDerAlong (C := Dual R E r) D)
    (isPar_kapD (R := R) (E := E) (r := r))
  rwa [Bool.true_xor] at h

/-- The signs of the bracket of an odd family with a family of parity `!e`. -/
lemma sign_aux {S : Type*} [CommRing S] {M : Type*} [AddCommGroup M] [Module S M] (e : Bool)
    (w u : M) : w - σ S (true && !e) • u = σ S e • (u + σ S (e && true) • w) := by
  cases e
  · simp only [Bool.not_false, Bool.and_self, Bool.false_and, σ_true, σ_false, one_smul,
      neg_one_smul, sub_neg_eq_add]
    exact add_comm _ _
  · simp only [Bool.not_true, Bool.and_false, Bool.and_self, σ_true, σ_false, one_smul,
      neg_one_smul, neg_add_rev, neg_neg]
    exact sub_eq_add_neg _ _

include hφ in
/-- **The bracket with `φ κ` of the cochain of a derivation**: up to the sign of the derivation,
it is the derivation after the convolution square `κ_T ⋆ κ_T`. -/
theorem bracket_ofDerT (D : GrDer (freeHom φ) e) :
    GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
      = σ R e • GrOperad.Inv.appDerAlong (ConvOp.postDerAlong (C := Dual R E r) D)
          (GrOperad.Inv.star R _ (kapD R E r) (kapD R E r)) := by
  have h := GrOperad.Inv.appDerAlong_star (ConvOp.postDerAlong (C := Dual R E r) D)
    (isPar_kapD (R := R) (E := E) (r := r)) (kapD R E r)
  have h1 : GrOperad.Inv.star R _ (ofDerT φ D)
      (GrOperad.Inv.appHom (ConvOp.postHom (C := Dual R E r) (freeHom φ)) (kapD R E r))
      = GrOperad.Inv.star R _ (ofDerT φ D) (twistingOf φ hφ).1 :=
    congrArg (GrOperad.Inv.star R _ (ofDerT φ D)) (appHom_freeHom_kapD φ hφ)
  have h2 : GrOperad.Inv.star R _
      (GrOperad.Inv.appHom (ConvOp.postHom (C := Dual R E r) (freeHom φ)) (kapD R E r))
      (ofDerT φ D) = GrOperad.Inv.star R _ (twistingOf φ hφ).1 (ofDerT φ D) :=
    congrArg (fun z => GrOperad.Inv.star R _ z (ofDerT φ D)) (appHom_freeHom_kapD φ hφ)
  have h' : GrOperad.Inv.appDerAlong (ConvOp.postDerAlong (C := Dual R E r) D)
      (GrOperad.Inv.star R _ (kapD R E r) (kapD R E r))
      = GrOperad.Inv.star R _ (ofDerT φ D) (twistingOf φ hφ).1
        + σ R (e && true) • GrOperad.Inv.star R _ (twistingOf φ hφ).1 (ofDerT φ D) :=
    h.trans (congrArg₂ (fun a b => a + σ R (e && true) • b) h1 h2)
  exact (GrOperad.Inv.bracket_hom (twistingOf φ hφ).2.1 (isPar_ofDerT φ D)).trans
    ((sign_aux e _ _).trans (congrArg (fun z => σ R e • z) h'.symm))

include hφ in
/-- The bracket with `φ κ` of the cochain of a derivation, pointwise. -/
lemma toLin_bracket_ofDerT (D : GrDer (freeHom φ) e) {A : Type} [Fintype A] [DecidableEq A]
    (c : Dual R E r A) :
    ConvOp.toLin ((GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)).1 A) c
      = σ R e • D.app A (ConvOp.toLin
          ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A) ((dualSub R E r).incl A c)) := by
  have h := congrArg (fun q : Def R E r Q => ConvOp.toLin (q.1 A) c) (bracket_ofDerT φ hφ D)
  exact h.trans (congrArg (fun z => σ R e • D.app A z) (toLin_star_kapD c))

/-- **The cochain of a derivation of `P` along `φ`**: the derivation after the Koszul twisting
morphism, `D ∘ κ`. -/
noncomputable def ofDer (D : GrDer φ e) : Def R E r Q :=
  ofDerT φ (D.precomp (GrOperadHom.toZeroDG (GrOperadIdeal.span R r).projHom))

lemma ofDer_apply (D : GrDer φ e) {A : Type} [Fintype A] [DecidableEq A] (c : Dual R E r A) :
    ConvOp.toLin ((ofDer φ D).1 A) c = D.app A (ConvOp.toLin ((kappa R E r).1 A) c) := rfl

include hφ in
/-- The cochain of a derivation of `P` along `φ`, read on `T(E)`, is closed for the bracket with
`φ κ`. -/
theorem bracket_ofDerT_precomp (D : GrDer φ e) :
    GrOperad.Inv.bracket R _ (twistingOf φ hφ).1
      (ofDerT φ (D.precomp (GrOperadHom.toZeroDG (GrOperadIdeal.span R r).projHom))) = 0 := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun c => ?_)
  have h := toLin_bracket_ofDerT φ hφ
    (D.precomp (GrOperadHom.toZeroDG (GrOperadIdeal.span R r).projHom)) c
  refine h.trans ?_
  have h0 : (GrOperadIdeal.span R r).proj A (ConvOp.toLin
      ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A) ((dualSub R E r).incl A c)) = 0 :=
    ((GrOperadIdeal.span R r).proj_eq_zero_iff _).2
      (GrSubCooperad.cogen_le (admissible R E r) A c.2)
  show σ R e • D.app A ((GrOperadIdeal.span R r).proj A _) = 0
  rw [h0]
  exact (congrArg (fun z => σ R e • z) (map_zero (D.app A))).trans (smul_zero _)

include hφ in
/-- **The cochain of a derivation of `P` along `φ` is closed for the bracket with `φ κ`.** -/
theorem bracket_ofDer (D : GrDer φ e) :
    GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDer φ D) = 0 :=
  bracket_ofDerT_precomp φ hφ D

end Koszul

/-! ## Cocycles of weight one are derivations -/

namespace Koszul

open FreeGrL

variable {R : Type u} [Field R] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [DGOperad R Q]
  (φ : GrOperadHom R (ZeroDG R (Pres R E r)) Q)
  (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : Pres R E r A),
    DGOperad.d (R := R) (φ.app A y) = 0)
  {e : Bool}

/-- **On the Koszul dual cooperad, `κ_T ⋆ κ_T` lands in the relations**, for quadratic relators
over a field of characteristic zero. -/
lemma star_incl_mem_relSp [CharZero R] (hq : IsQuadratic R E r) {A : Type} [Fintype A]
    [DecidableEq A] (c : Dual R E r A) :
    starKap R E A ((dualSub R E r).incl A c) ∈ relSp R E r A := by
  rw [← ideal_inf_vx_two hq]
  exact ⟨GrSubCooperad.cogen_le (admissible R E r) A c.2, star_mem_vx _⟩

/-- **Every relation is the image under `κ_T ⋆ κ_T` of an element of the Koszul dual
cooperad**, for quadratic relators over a field of characteristic zero, when there are no
generators without inputs. -/
lemma exists_dual_star_eq [CharZero R] (hq : IsQuadratic R E r) (hE0 : ∀ v : E (Fin 0), v = 0)
    {A : Type} [Fintype A] [DecidableEq A] {ρ : FreeGrL R E A} (hρ : ρ ∈ relSp R E r A) :
    ∃ c : Dual R E r A, starKap R E A ((dualSub R E r).incl A c) = ρ := by
  have h : ρ ∈ (coRel R E r A).map (starKap R E A) := by
    rw [map_coRel (A := A) r hq hE0]
    exact hρ
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨⟨y, coRel_le_dual r hy⟩, rfl⟩

/-- A derivation of `T(E)` vanishing on the relators vanishes on the relations. -/
lemma der_relSp_eq_zero (D : GrDer (freeHom φ) e)
    (h : ∀ n, ∀ ρ ∈ r n, D.app (Fin n) ρ = 0) {A : Type} [Fintype A] [DecidableEq A]
    {ρ : FreeGrL R E A} (hρ : ρ ∈ relSp R E r A) : D.app A ρ = 0 := by
  have hle : relSp R E r A ≤ LinearMap.ker (D.app A) := by
    rw [relSp, Submodule.span_le]
    rintro _ ⟨n, x, hx, e', b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, D.app_par, D.app_map, h n x hx, map_zero, map_zero]
  exact LinearMap.mem_ker.1 (hle hρ)

include hφ in
/-- **The cochain of a derivation of `T(E)` along `T(E) → Q` is closed for the bracket with
`φ κ` exactly when the derivation vanishes on the relators**, for quadratic relators over a
field of characteristic zero, without generators without inputs. -/
theorem bracket_ofDerT_eq_zero_iff [CharZero R] (hq : IsQuadratic R E r)
    (hE0 : ∀ v : E (Fin 0), v = 0) (D : GrDer (freeHom φ) e) :
    GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D) = 0
      ↔ ∀ n, ∀ ρ ∈ r n, D.app (Fin n) ρ = 0 := by
  constructor
  · intro h n ρ hρ
    obtain ⟨c, hc⟩ := exists_dual_star_eq hq hE0 (mem_relSp hρ)
    have h1 := toLin_bracket_ofDerT φ hφ D c
    have h0 : ConvOp.toLin ((GrOperad.Inv.bracket R _ (twistingOf φ hφ).1
        (ofDerT φ D)).1 (Fin n)) c = 0 :=
      congrArg (fun q : Def R E r Q => ConvOp.toLin (q.1 (Fin n)) c) h
    have h2 : σ R e • D.app (Fin n) ρ = 0 := by
      rw [← hc]
      exact h1.symm.trans h0
    cases e
    · rwa [σ_false, one_smul] at h2
    · rwa [σ_true, neg_one_smul, neg_eq_zero] at h2
  · intro h
    refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun c => ?_)
    refine (toLin_bracket_ofDerT φ hφ D c).trans ?_
    have h3 := der_relSp_eq_zero φ D h (star_incl_mem_relSp hq c)
    exact (congrArg (fun z => σ R e • z) h3).trans (smul_zero _)

/-- **The derivation of `P` along `φ` of a derivation of `T(E)` vanishing on the relators.** -/
noncomputable def derOfT (D : GrDer (freeHom φ) e)
    (h : ∀ n, ∀ ρ ∈ r n, D.app (Fin n) ρ = 0) : GrDer φ e :=
  GrDer.ofHom (GrOperadHom.ofZeroDG ((GrOperadIdeal.span R r).liftHom D.toHom
    fun A _ _ x hx => GrOperadIdeal.app_eq_zero_of_mem_span D.toHom
      (fun n ρ hρ => DualExt.ext
        (by
          show φ.app (Fin n) ((GrOperadIdeal.span R r).proj (Fin n) ρ) = 0
          rw [((GrOperadIdeal.span R r).proj_eq_zero_iff ρ).2
            (GrOperadIdeal.subset_span n hρ)]
          exact map_zero (φ.app (Fin n)))
        (h n ρ hρ)) hx))
    fun A _ _ X => by
      obtain ⟨x, rfl⟩ := (GrOperadIdeal.span R r).proj_surjective A X
      rfl

lemma derOfT_proj (D : GrDer (freeHom φ) e) (h : ∀ n, ∀ ρ ∈ r n, D.app (Fin n) ρ = 0)
    {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R E A) :
    (derOfT φ D h).app A ((GrOperadIdeal.span R r).proj A x) = D.app A x := rfl

/-- The derivation of `P` of a derivation of `P` read on `T(E)` is the derivation. -/
lemma derOfT_precomp (D : GrDer φ e)
    (h : ∀ n, ∀ ρ ∈ r n, (D.precomp (GrOperadHom.toZeroDG
      (GrOperadIdeal.span R r).projHom)).app (Fin n) ρ = 0) :
    derOfT φ (D.precomp (GrOperadHom.toZeroDG (GrOperadIdeal.span R r).projHom)) h = D := by
  refine GrDer.ext fun A _ _ X => ?_
  have key : ∀ Y : Pres R E r A,
      (derOfT φ (D.precomp (GrOperadHom.toZeroDG (GrOperadIdeal.span R r).projHom)) h).app A Y
        = D.app A Y := fun Y => by
    obtain ⟨x, rfl⟩ := (GrOperadIdeal.span R r).proj_surjective A Y
    exact derOfT_proj φ
      (D.precomp (GrOperadHom.toZeroDG (GrOperadIdeal.span R r).projHom)) h x
  exact key X

/-- The derivation of `P` of a derivation of `T(E)`, read on `T(E)`, is the derivation. -/
lemma precomp_derOfT (D : GrDer (freeHom φ) e) (h : ∀ n, ∀ ρ ∈ r n, D.app (Fin n) ρ = 0) :
    (derOfT φ D h).precomp (GrOperadHom.toZeroDG (GrOperadIdeal.span R r).projHom) = D :=
  GrDer.ext fun _ _ _ x => derOfT_proj φ D h x

/-- **The derivations of `P` along `φ` are the derivations of `T(E)` along `T(E) → Q` whose
cochain is closed for the bracket with `φ κ`**: the cocycles of weight one of the deformation
complex, for quadratic relators over a field of characteristic zero, without generators without
inputs. -/
noncomputable def derEquiv [CharZero R] (hq : IsQuadratic R E r)
    (hE0 : ∀ v : E (Fin 0), v = 0) :
    GrDer φ e ≃ {D : GrDer (freeHom φ) e //
      GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D) = 0} where
  toFun D := ⟨D.precomp (GrOperadHom.toZeroDG (GrOperadIdeal.span R r).projHom),
    bracket_ofDerT_precomp φ hφ D⟩
  invFun D := derOfT φ D.1 ((bracket_ofDerT_eq_zero_iff φ hφ hq hE0 D.1).1 D.2)
  left_inv D := derOfT_precomp φ D _
  right_inv D := Subtype.ext (precomp_derOfT φ D.1 _)

/-- **The cochain of a derivation of `T(E)` determines it**: the generators lie in the Koszul
dual cooperad, and the desuspension map sends `sv` to `v`. -/
theorem ofDerT_injective : Function.Injective (ofDerT (e := e) φ) := by
  intro D D' h
  refine der_ext fun A _ _ v => ?_
  have h1 := congrArg (fun q : Def R E r Q => ConvOp.toLin (q.1 A)
    (⟨(FreeGrL.ι R (GrSpecies.Shift E R)).app A (GrSpecies.Shift.of A v),
      ι_mem_dual r v⟩ : Dual R E r A)) h
  have h2 : ∀ D₀ : GrDer (freeHom φ) e, ConvOp.toLin ((ofDerT φ D₀).1 A)
      (⟨(FreeGrL.ι R (GrSpecies.Shift E R)).app A (GrSpecies.Shift.of A v),
        ι_mem_dual r v⟩ : Dual R E r A) = D₀.app A ((FreeGrL.ι R E).app A v) := fun D₀ =>
    congrArg (D₀.app A) (kapL_ι (R := R) (E := E) v)
  exact (h2 D).symm.trans (h1.trans (h2 D'))

end Koszul

/-! ## Cohomology, and the deformation complex of the operad -/

namespace Koszul

variable {R : Type u} [Field R] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [DGOperad R Q]
  (φ : GrOperadHom R (ZeroDG R (Pres R E r)) Q)
  (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : Pres R E r A),
    DGOperad.d (R := R) (φ.app A y) = 0)
  {e : Bool}

/-- **The cohomology of the deformation complex of `φ`**: cocycles modulo coboundaries. -/
abbrev DefH : Type _ := Homology R (defD φ hφ)

/-- Coboundaries are cocycles. -/
lemma range_defD_le_ker : LinearMap.range (defD φ hφ) ≤ LinearMap.ker (defD φ hφ) := by
  rintro _ ⟨x, rfl⟩
  exact defD_defD φ hφ x

/-- **The differential of the cochain of a derivation of `P` along `φ`** is the internal
differential of `Q` after it. -/
theorem defD_ofDer (D : GrDer φ e) :
    defD φ hφ (ofDer φ D)
      = GrOperad.Inv.appDer (Twisting.convD R (Dual R E r) Q) (ofDer φ D) :=
  (GrOperad.Inv.twD_apply _ _ _).trans
    ((congrArg (fun z => GrOperad.Inv.appDer (Twisting.convD R (Dual R E r) Q) (ofDer φ D) + z)
      (bracket_ofDer φ hφ D)).trans (add_zero _))

/-- **The cochain of a derivation of `P` along `φ` with values in the cycles of `Q` is a
cocycle of the deformation complex.** -/
theorem defD_ofDer_eq_zero (D : GrDer φ e)
    (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : Pres R E r A),
      DGOperad.d (R := R) (D.app A y) = 0) : defD φ hφ (ofDer φ D) = 0 :=
  (defD_ofDer φ hφ D).trans
    (Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun _ => hD A _))

variable (R E r) in
/-- **The differential of the deformation complex of the operad `P`**: the case of the identity
of `P`, with the zero differential. -/
noncomputable abbrev defDOperad :
    Def R E r (ZeroDG R (Pres R E r)) →ₗ[R] Def R E r (ZeroDG R (Pres R E r)) :=
  defD (GrOperadHom.id R (ZeroDG R (Pres R E r))) fun _ _ _ _ => rfl

/-- **The differential of the deformation complex of the operad is the bracket with `κ`.** -/
theorem defDOperad_apply (x : Def R E r (ZeroDG R (Pres R E r))) :
    defDOperad R E r x = GrOperad.Inv.bracket R _ (kappa R E r) x := by
  have h0 : GrOperad.Inv.appDer (Twisting.convD R (Dual R E r) (ZeroDG R (Pres R E r))) x = 0 :=
    Subtype.ext (funext fun _ => funext fun _ => funext fun _ => ConvOp.ext fun _ => rfl)
  have h1 : (twistingOf (GrOperadHom.id R (ZeroDG R (Pres R E r)))
      (fun _ _ _ _ => rfl)).1 = kappa R E r :=
    Subtype.ext (funext fun _ => funext fun _ => funext fun _ => ConvOp.ext fun _ => rfl)
  exact (GrOperad.Inv.twD_apply _ _ x).trans
    ((congrArg₂ (fun a b => a + GrOperad.Inv.bracket R _ b x) h0 h1).trans (zero_add _))

end Koszul

end Operad
