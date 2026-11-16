/-
# Lifts of a morphism to truncated polynomials, and their obstructions

Let `P = T(E)/(r)` be a presented operad over a field, `Q` a dg operad and `φ : P → Q` a morphism
with values in the cycles of `Q`, with deformation complex `Def(φ) = Hom_𝔖(P^¡, Q)`
(`Operad.DeformationComplex`).

* **Morphisms as Maurer–Cartan elements.** A morphism `f : T(E) → Q'` of graded operads has the
  cochain `f ∘ κ_T` (`Koszul.ofHomT`). For quadratic relators over a field of characteristic
  zero, without generators without inputs, its convolution square vanishes exactly when `f`
  vanishes on the relators (`Koszul.star_ofHomT_eq_zero_iff`), so the morphisms `P → Q'` are
  the morphisms `T(E) → Q'` whose cochain has square zero (`Koszul.homEquivMC`).
* **Lifts.** A lift of `φ` to order `n` (`Koszul.Lift`) is a morphism of graded operads
  `φ̃ : P → Q[t]/tⁿ⁺¹` (`TruncOp`) with constant term `φ` and values in the cycles. The
  coefficients `xₖ = cₖ ∘ φ̃ ∘ κ` of its cochain (`Koszul.Lift.x`) are a lift of `φ κ` by
  coefficients (`Koszul.Lift.toLiftSeq`), the coefficients of a convolution product being the
  Cauchy product of the coefficients (`CoefSys.coefI_star`). Its **obstruction**
  `∑_{i+j=n+1, i,j ≥ 1} xᵢ ⋆ xⱼ` is a cocycle of `Def(φ)` (`Koszul.Lift.defD_obstruction`).
* **The extension theorem** (`Koszul.Lift.extends_iff`, `Koszul.Lift.extends_iff_defD`), for
  quadratic relators over a field of characteristic zero, without generators without inputs: a
  lift `φ̃ : P → Q[t]/tⁿ⁺¹` extends to a lift `P → Q[t]/tⁿ⁺²` exactly when its obstruction is
  minus the differential of a cochain of weight one with values in the cycles, the cochain
  `D ∘ κ_T` of a derivation `D` of `T(E)` along `T(E) → Q` with values in the cycles on the
  generators. The coefficient of order `n + 1` of an extension is such a cochain
  (`Koszul.coefI_ofHomT`, `Koszul.Lift.exists_der_of_extension`), and the morphism with the
  values `φ̃ v + tⁿ⁺¹ D v` on the generators is an extension (`Koszul.Lift.extend`,
  `Koszul.Lift.trunc_extend`).

The cochains are graded by parity only, so the cohomology `Koszul.DefH` is not split by weight:
the vanishing of the class of the obstruction in `H²` is stated as the obstruction being the
differential of a cochain of weight one. The complex `Hom_𝔖(P^¡, P)` of the operad `P` is not
compared with the cochains of `FormalDeformation.lean`.
-/
import Operad.DeformationComplex
import Operad.InvObstruction
import Operad.TruncOperad
import Operad.ConvCoef

universe u v w

namespace Operad

open Sym GerBV

namespace Koszul

open FreeGrL

/-! ## Morphisms out of a quadratic operad are cochains of square zero -/

section Hom

variable {R : Type u} [Field R] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))}
  {Q' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q' A)] [GrOperad R Q']

variable (r) in
/-- **The cochain of a morphism `f : T(E) → Q'`**: the morphism after the desuspension map,
`f ∘ κ_T : P^¡ → Q'`. -/
noncomputable def ofHomT (f : GrOperadHom R (FreeGrL R E) Q') :
    GrOperad.Inv R (ConvOp R (Dual R E r) Q') :=
  GrOperad.Inv.appHom (ConvOp.postHom (C := Dual R E r) f) (kapD R E r)

/-- The convolution square of the cochain of a morphism is the morphism after `κ_T ⋆ κ_T`. -/
lemma toLin_star_ofHomT (f : GrOperadHom R (FreeGrL R E) Q') {A : Type} [Fintype A]
    [DecidableEq A] (c : Dual R E r A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (ofHomT r f) (ofHomT r f)).1 A) c
      = f.app A (starKap R E A ((dualSub R E r).incl A c)) :=
  (congrArg (fun q : GrOperad.Inv R (ConvOp R (Dual R E r) Q') => ConvOp.toLin (q.1 A) c)
    (GrOperad.Inv.appHom_star (ConvOp.postHom (C := Dual R E r) f) (kapD R E r)
      (kapD R E r)).symm).trans (congrArg (f.app A) (toLin_star_kapD c))

/-- A morphism out of `T(E)` vanishing on the relators vanishes on the relations. -/
lemma hom_relSp_eq_zero (f : GrOperadHom R (FreeGrL R E) Q')
    (h : ∀ n, ∀ ρ ∈ r n, f.app (Fin n) ρ = 0) {A : Type} [Fintype A] [DecidableEq A]
    {ρ : FreeGrL R E A} (hρ : ρ ∈ relSp R E r A) : f.app A ρ = 0 := by
  have hle : relSp R E r A ≤ LinearMap.ker (f.app A) := by
    rw [relSp, Submodule.span_le]
    rintro _ ⟨n, x, hx, e', b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, f.app_par, f.app_map, h n x hx, map_zero, map_zero]
  exact LinearMap.mem_ker.1 (hle hρ)

/-- **The cochain of a morphism `f : T(E) → Q'` has convolution square zero exactly when `f`
vanishes on the relators**, for quadratic relators over a field of characteristic zero, without
generators without inputs. -/
theorem star_ofHomT_eq_zero_iff [CharZero R] (hq : IsQuadratic R E r)
    (hE0 : ∀ v : E (Fin 0), v = 0) (f : GrOperadHom R (FreeGrL R E) Q') :
    GrOperad.Inv.star R _ (ofHomT r f) (ofHomT r f) = 0
      ↔ ∀ n, ∀ ρ ∈ r n, f.app (Fin n) ρ = 0 := by
  constructor
  · intro h n ρ hρ
    obtain ⟨c, hc⟩ := exists_dual_star_eq hq hE0 (mem_relSp hρ)
    have h0 : ConvOp.toLin ((GrOperad.Inv.star R _ (ofHomT r f) (ofHomT r f)).1 (Fin n)) c
        = 0 :=
      congrArg (fun q : GrOperad.Inv R (ConvOp R (Dual R E r) Q') =>
        ConvOp.toLin (q.1 (Fin n)) c) h
    rw [← hc]
    exact (toLin_star_ofHomT f c).symm.trans h0
  · intro h
    refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun c => ?_)
    exact (toLin_star_ofHomT f c).trans (hom_relSp_eq_zero f h (star_incl_mem_relSp hq c))

/-- **The morphism out of `P` of a morphism out of `T(E)` vanishing on the relators.** -/
noncomputable def homOfT (f : GrOperadHom R (FreeGrL R E) Q')
    (h : ∀ n, ∀ ρ ∈ r n, f.app (Fin n) ρ = 0) : GrOperadHom R (Pres R E r) Q' :=
  (GrOperadIdeal.span R r).liftHom f fun _ _ _ _ hx =>
    GrOperadIdeal.app_eq_zero_of_mem_span f h hx

lemma homOfT_proj (f : GrOperadHom R (FreeGrL R E) Q')
    (h : ∀ n, ∀ ρ ∈ r n, f.app (Fin n) ρ = 0) {A : Type} [Fintype A] [DecidableEq A]
    (x : FreeGrL R E A) : (homOfT f h).app A ((GrOperadIdeal.span R r).proj A x) = f.app A x :=
  rfl

/-- A morphism out of `P`, read on `T(E)`, vanishes on the relators. -/
lemma comp_proj_rel (ψ : GrOperadHom R (Pres R E r) Q') :
    ∀ n, ∀ ρ ∈ r n, (ψ.comp (GrOperadIdeal.span R r).projHom).app (Fin n) ρ = 0 := by
  intro n ρ hρ
  show ψ.app (Fin n) ((GrOperadIdeal.span R r).proj (Fin n) ρ) = 0
  rw [((GrOperadIdeal.span R r).proj_eq_zero_iff ρ).2 (GrOperadIdeal.subset_span n hρ),
    map_zero]

lemma homOfT_comp (ψ : GrOperadHom R (Pres R E r) Q')
    (h : ∀ n, ∀ ρ ∈ r n, (ψ.comp (GrOperadIdeal.span R r).projHom).app (Fin n) ρ = 0) :
    homOfT (ψ.comp (GrOperadIdeal.span R r).projHom) h = ψ := by
  refine GrOperadHom.ext fun A _ _ X => ?_
  obtain ⟨x, rfl⟩ := (GrOperadIdeal.span R r).proj_surjective A X
  exact homOfT_proj (ψ.comp (GrOperadIdeal.span R r).projHom) h x

lemma comp_homOfT (f : GrOperadHom R (FreeGrL R E) Q')
    (h : ∀ n, ∀ ρ ∈ r n, f.app (Fin n) ρ = 0) :
    (homOfT f h).comp (GrOperadIdeal.span R r).projHom = f :=
  GrOperadHom.ext fun _ _ _ x => homOfT_proj f h x

/-- **The morphisms `P → Q'` are the morphisms `T(E) → Q'` whose cochain `f ∘ κ_T` has
convolution square zero**: the Maurer–Cartan elements of weight one of `Hom_𝔖(P^¡, Q')`. For
quadratic relators over a field of characteristic zero, without generators without inputs. -/
noncomputable def homEquivMC [CharZero R] (hq : IsQuadratic R E r)
    (hE0 : ∀ v : E (Fin 0), v = 0) :
    GrOperadHom R (Pres R E r) Q' ≃ {f : GrOperadHom R (FreeGrL R E) Q' //
      GrOperad.Inv.star R _ (ofHomT r f) (ofHomT r f) = 0} where
  toFun ψ := ⟨ψ.comp (GrOperadIdeal.span R r).projHom,
    (star_ofHomT_eq_zero_iff hq hE0 _).2 (comp_proj_rel ψ)⟩
  invFun f := homOfT f.1 ((star_ofHomT_eq_zero_iff hq hE0 f.1).1 f.2)
  left_inv ψ := homOfT_comp ψ _
  right_inv f := Subtype.ext (comp_homOfT f.1 _)

end Hom

end Koszul

/-! ## Lifts to truncated polynomials -/

/-- **The coefficients of truncated polynomials are a system of coefficients** up to order
`n`. -/
def TruncOp.coefSys {R : Type u} [CommRing R]
    {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] (n : ℕ) :
    CoefSys R (TruncOp R Q n) Q n where
  c k A _ _ := TruncOp.coef R Q n k A
  c_par := by
    intro k A _ _ b z
    exact TruncOp.coef_par b z
  c_map := by
    intro k A B _ _ _ _ e z
    exact TruncOp.coef_map e z
  c_comp := by
    intro k hk A B _ _ _ _ i z w
    exact TruncOp.coef_comp hk i z w

namespace Koszul

open FreeGrL

section Lift

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

/-- The cochain of a morphism out of `T(E)` is odd. -/
lemma isPar_ofHomT {Q' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q' A)] [GrOperad R Q']
    (f : GrOperadHom R (FreeGrL R E) Q') : GrOperad.Inv.IsPar true (ofHomT r f) :=
  fun A _ _ => by
    show GrOperad.par (R := R) true ((ConvOp.postHom (C := Dual R E r) f).app A
      ((kapD R E r).1 A)) = _
    rw [← GrOperadHom.app_par, isPar_kapD A]
    rfl

/-- **The cochain of a morphism out of `P`, read on `T(E)`, has convolution square zero.** -/
lemma star_ofHomT_comp_proj {Q' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q' A)] [GrOperad R Q']
    (ψ : GrOperadHom R (Pres R E r) Q') :
    GrOperad.Inv.star R _ (ofHomT r (ψ.comp (GrOperadIdeal.span R r).projHom))
      (ofHomT r (ψ.comp (GrOperadIdeal.span R r).projHom)) = 0 := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun c => ?_)
  have h1 : (GrOperadIdeal.span R r).proj A (starKap R E A ((dualSub R E r).incl A c)) = 0 :=
    ((GrOperadIdeal.span R r).proj_eq_zero_iff _).2
      (GrSubCooperad.cogen_le (admissible R E r) A c.2)
  exact (toLin_star_ofHomT (ψ.comp (GrOperadIdeal.span R r).projHom) c).trans
    ((congrArg (ψ.app A) h1).trans (map_zero (ψ.app A)))

/-- **A lift of `φ` to `Q[t]/tⁿ⁺¹`**: a morphism of graded operads `P → Q[t]/tⁿ⁺¹` with constant
term `φ` and values in the cycles; a morphism of dg operads, `P` carrying the zero
differential. -/
structure Lift (n : ℕ) where
  /-- The morphism. -/
  hom : GrOperadHom R (Pres R E r) (TruncOp R Q n)
  const : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : Pres R E r A),
    TruncOp.coef R Q n 0 A (hom.app A y) = φ.app A y
  closed : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : Pres R E r A),
    TruncOp.dT R Q n A (hom.app A y) = 0

variable {φ}

/-- A lift, read on `T(E)`. -/
noncomputable def Lift.homT {n : ℕ} (ψ : Lift φ n) :
    GrOperadHom R (FreeGrL R E) (TruncOp R Q n) :=
  ψ.hom.comp (GrOperadIdeal.span R r).projHom

/-- **The coefficients of the cochain of a lift**: `xₖ = cₖ ∘ φ̃ ∘ κ`. -/
noncomputable def Lift.x {n : ℕ} (ψ : Lift φ n) (k : ℕ) : Def R E r Q :=
  (TruncOp.coefSys n).coefI k (ofHomT r ψ.homT)

lemma Lift.x_def {n : ℕ} (ψ : Lift φ n) (k : ℕ) :
    ψ.x k = (TruncOp.coefSys n).coefI k (ofHomT r ψ.homT) := rfl

lemma Lift.x_apply {n : ℕ} (ψ : Lift φ n) (k : ℕ) {A : Type} [Fintype A] [DecidableEq A]
    (c : Dual R E r A) :
    ConvOp.toLin ((ψ.x k).1 A) c
      = TruncOp.coef R Q n k A (ψ.homT.app A (kapL R E A ((dualSub R E r).incl A c))) := rfl

/-- **The coefficient form of a lift**: the coefficients of its cochain are a lift of `φ κ` by
coefficients. -/
noncomputable def Lift.toLiftSeq {n : ℕ} (ψ : Lift φ n) :
    GrOperad.Inv.LiftSeq (Twisting.convD R (Dual R E r) Q) (twistingOf φ hφ).1 n where
  x := ψ.x
  x_zero := Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun _ =>
    ψ.const A _)
  isPar k := (TruncOp.coefSys n).isPar_coefI k (isPar_ofHomT ψ.homT)
  closed k := Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun c =>
    by
      show DGOperad.d (R := R) (TruncOp.coef R Q n k A
        (ψ.homT.app A (kapL R E A ((dualSub R E r).incl A c)))) = 0
      rw [← TruncOp.coef_dT]
      exact (congrArg (TruncOp.coef R Q n k A) (ψ.closed A _)).trans (map_zero _))
  sq_eq m hm := by
    have h := (TruncOp.coefSys n).coefI_star (C := Dual R E r) hm (ofHomT r ψ.homT)
      (ofHomT r ψ.homT)
    have h0 : GrOperad.Inv.star R _ (ofHomT r ψ.homT) (ofHomT r ψ.homT) = 0 :=
      star_ofHomT_comp_proj ψ.hom
    exact h.symm.trans ((congrArg ((TruncOp.coefSys n).coefI m) h0).trans (map_zero _))
  x_succ := Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun _ =>
    TruncOp.coef_of_lt (Nat.lt_succ_self n) _)

end Lift

/-! ## Extending a lift -/

section Extend

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [DGOperad R Q]
  (φ : GrOperadHom R (ZeroDG R (Pres R E r)) Q)
  (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : Pres R E r A),
    DGOperad.d (R := R) (φ.app A y) = 0)

omit [DGOperad R Q] in
/-- The desuspension map takes its values in the generators. -/
lemma kapL_eq_ι {A : Type} [Fintype A] [DecidableEq A] (z : Cut R E A) :
    kapL R E A z = (FreeGrL.ι R E).app A (FreeGrL.genCoef R E A (kapL R E A z)) :=
  FreeGrL.eq_ι_genCoef (kapL_mem_vx z)

/-- **The coefficient of order `k` on the generators** of a morphism `T(E) → Q[t]/tⁿ⁺¹`. -/
noncomputable def coefGen {n : ℕ} (f : GrOperadHom R (FreeGrL R E) (TruncOp R Q n)) (k : ℕ) :
    GrSpeciesHom R E Q where
  app A _ _ := TruncOp.coef R Q n k A ∘ₗ f.app A ∘ₗ (FreeGrL.ι R E).app A
  app_map e v := by
    show TruncOp.coef R Q n k _ (f.app _ ((FreeGrL.ι R E).app _
      (SymSpecies.map (R := R) e v))) = _
    rw [(FreeGrL.ι R E).app_map, GrOperad.toGrSpecies_map, f.app_map, TruncOp.coef_map]
    rfl
  app_par c v := by
    show TruncOp.coef R Q n k _ (f.app _ ((FreeGrL.ι R E).app _
      (GrSpecies.par (R := R) c v))) = _
    rw [(FreeGrL.ι R E).app_par, GrOperad.toGrSpecies_par, f.app_par, TruncOp.coef_par]
    rfl

omit [CharZero R] in
lemma coefGen_apply {n : ℕ} (f : GrOperadHom R (FreeGrL R E) (TruncOp R Q n)) (k : ℕ)
    {A : Type} [Fintype A] [DecidableEq A] (v : E A) :
    (coefGen f k).app A v = TruncOp.coef R Q n k A (f.app A ((FreeGrL.ι R E).app A v)) := rfl

omit [CharZero R] in
lemma isShift_coefGen {n : ℕ} (f : GrOperadHom R (FreeGrL R E) (TruncOp R Q n)) (k : ℕ) :
    FreeGrL.IsShift (coefGen f k).toSymSpeciesHom false := fun A _ _ c v => by
  rw [Bool.xor_false]
  exact (coefGen f k).app_par c v

/-- **The derivation of `T(E)` along `T(E) → Q` with the values of the coefficient of order
`k`** of a morphism `T(E) → Q[t]/tⁿ⁺¹` on the generators. -/
noncomputable def coefDer {n : ℕ} (f : GrOperadHom R (FreeGrL R E) (TruncOp R Q n)) (k : ℕ) :
    GrDer (freeHom φ) false :=
  FreeGrL.derOf (freeHom φ) (coefGen f k).toSymSpeciesHom (isShift_coefGen f k)

omit [CharZero R] in
lemma coefDer_ι {n : ℕ} (f : GrOperadHom R (FreeGrL R E) (TruncOp R Q n)) (k : ℕ)
    {A : Type} [Fintype A] [DecidableEq A] (v : E A) :
    (coefDer φ f k).app A ((FreeGrL.ι R E).app A v)
      = TruncOp.coef R Q n k A (f.app A ((FreeGrL.ι R E).app A v)) :=
  FreeGrL.derOf_ι _ _ _ _

/-- **A coefficient of the cochain of a morphism `T(E) → Q[t]/tⁿ⁺¹` is a cochain of weight
one**: the cochain of the derivation with the same values on the generators. -/
lemma coefI_ofHomT {n : ℕ} (f : GrOperadHom R (FreeGrL R E) (TruncOp R Q n)) (k : ℕ) :
    (TruncOp.coefSys n).coefI k (ofHomT r f) = ofDerT φ (coefDer φ f k) := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun c => ?_)
  have hz := kapL_eq_ι (R := R) (E := E) ((dualSub R E r).incl A c)
  have h1 : TruncOp.coef R Q n k A (f.app A (kapL R E A ((dualSub R E r).incl A c)))
      = (coefGen f k).app A (FreeGrL.genCoef R E A (kapL R E A ((dualSub R E r).incl A c))) :=
    congrArg (fun z => TruncOp.coef R Q n k A (f.app A z)) hz
  have h2 : (coefDer φ f k).app A (kapL R E A ((dualSub R E r).incl A c))
      = (coefGen f k).app A (FreeGrL.genCoef R E A (kapL R E A ((dualSub R E r).incl A c))) :=
    (congrArg (fun z => (coefDer φ f k).app A z) hz).trans (coefDer_ι φ f k _)
  exact h1.trans h2.symm

variable {φ}

omit [CharZero R] in
/-- The coefficients of an extension of a lift, below the new order, are those of the lift. -/
lemma Lift.x_of_trunc {n : ℕ} (ψ : Lift φ n) (ψ' : Lift φ (n + 1))
    (h : (TruncOp.trunc R Q n).comp ψ'.hom = ψ.hom) {k : ℕ} (hk : k ≠ n + 1) :
    ψ'.x k = ψ.x k := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun c => ?_)
  have hc : (TruncOp.trunc R Q n).app A
      (ψ'.homT.app A (kapL R E A ((dualSub R E r).incl A c)))
      = ψ.homT.app A (kapL R E A ((dualSub R E r).incl A c)) :=
    congrArg (fun g : GrOperadHom R (Pres R E r) (TruncOp R Q n) =>
      g.app A ((GrOperadIdeal.span R r).proj A (kapL R E A ((dualSub R E r).incl A c)))) h
  show TruncOp.coef R Q (n + 1) k A (ψ'.homT.app A (kapL R E A ((dualSub R E r).incl A c)))
    = TruncOp.coef R Q n k A (ψ.homT.app A (kapL R E A ((dualSub R E r).incl A c)))
  by_cases hkn : k ≤ n
  · rw [← hc, TruncOp.coef_trunc hkn]
  · rw [TruncOp.coef_of_lt (by omega), TruncOp.coef_of_lt (by omega)]

omit [CharZero R] in
lemma Lift.toLiftSeq_x {n : ℕ} (ψ : Lift φ n) : (ψ.toLiftSeq hφ).x = ψ.x := rfl

/-- **If a lift extends by one order, its obstruction is minus the bracket of `φ κ` with a
cochain of weight one**: the coefficient of the new order, the cochain of a derivation of
`T(E)` along `T(E) → Q` with values in the cycles on the generators. -/
theorem Lift.exists_der_of_extension {n : ℕ} (ψ : Lift φ n) (ψ' : Lift φ (n + 1))
    (h : (TruncOp.trunc R Q n).comp ψ'.hom = ψ.hom) :
    ∃ D : GrDer (freeHom φ) false,
      (∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
        DGOperad.d (R := R) (D.app A ((FreeGrL.ι R E).app A v)) = 0) ∧
      GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
        = -(ψ.toLiftSeq hφ).obstruction := by
  have hy : ψ'.x (n + 1) = ofDerT φ (coefDer φ ψ'.homT (n + 1)) :=
    (Lift.x_def ψ' (n + 1)).trans (coefI_ofHomT φ ψ'.homT (n + 1))
  have hup : (ψ'.toLiftSeq hφ).x = Function.update (ψ.toLiftSeq hφ).x (n + 1)
      (ofDerT φ (coefDer φ ψ'.homT (n + 1))) := funext fun k => by
    by_cases hk : k = n + 1
    · subst hk
      exact hy.trans (Function.update_self (n + 1) (ofDerT φ (coefDer φ ψ'.homT (n + 1)))
        (ψ.toLiftSeq hφ).x).symm
    · have hx : (ψ.toLiftSeq hφ).x k = Function.update (ψ.toLiftSeq hφ).x (n + 1)
          (ofDerT φ (coefDer φ ψ'.homT (n + 1))) k :=
        (Function.update_of_ne hk (ofDerT φ (coefDer φ ψ'.homT (n + 1)))
          (ψ.toLiftSeq hφ).x).symm
      exact (Lift.x_of_trunc ψ ψ' h hk).trans
        ((congrFun (Lift.toLiftSeq_x hφ ψ) k).symm.trans hx)
  have hsq : GrOperad.Inv.sq (Function.update (ψ.toLiftSeq hφ).x (n + 1)
      (ofDerT φ (coefDer φ ψ'.homT (n + 1)))) (n + 1) = 0 :=
    (congrArg (fun x => GrOperad.Inv.sq x (n + 1)) hup).symm.trans
      ((ψ'.toLiftSeq hφ).sq_eq (n + 1) le_rfl)
  have hpar : GrOperad.Inv.IsPar true (ofDerT φ (coefDer φ ψ'.homT (n + 1))) :=
    isPar_ofDerT φ (coefDer φ ψ'.homT (n + 1))
  refine ⟨coefDer φ ψ'.homT (n + 1), fun A _ _ v => ?_,
    ((ψ.toLiftSeq hφ).sq_update_eq_zero_iff hpar).1 hsq⟩
  rw [coefDer_ι, ← TruncOp.coef_dT]
  exact (congrArg (TruncOp.coef R Q (n + 1) (n + 1) A) (ψ'.closed A _)).trans (map_zero _)

/-! ## The extension of a lift by a cochain of weight one -/

omit [CharZero R] in
/-- A morphism `T(E) → Q[t]/tⁿ⁺²` and its truncation have the same coefficients, apart from the
one of order `n + 1`. -/
lemma coefI_ofHomT_trunc {n : ℕ} (f' : GrOperadHom R (FreeGrL R E) (TruncOp R Q (n + 1)))
    (f : GrOperadHom R (FreeGrL R E) (TruncOp R Q n))
    (h : (TruncOp.trunc R Q n).comp f' = f) {k : ℕ} (hk : k ≠ n + 1) :
    (TruncOp.coefSys (n + 1)).coefI k (ofHomT r f')
      = (TruncOp.coefSys n).coefI k (ofHomT r f) := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun c => ?_)
  have hc : (TruncOp.trunc R Q n).app A (f'.app A (kapL R E A ((dualSub R E r).incl A c)))
      = f.app A (kapL R E A ((dualSub R E r).incl A c)) :=
    congrArg (fun g : GrOperadHom R (FreeGrL R E) (TruncOp R Q n) =>
      g.app A (kapL R E A ((dualSub R E r).incl A c))) h
  show TruncOp.coef R Q (n + 1) k A (f'.app A (kapL R E A ((dualSub R E r).incl A c)))
    = TruncOp.coef R Q n k A (f.app A (kapL R E A ((dualSub R E r).incl A c)))
  by_cases hkn : k ≤ n
  · rw [← hc, TruncOp.coef_trunc hkn]
  · rw [TruncOp.coef_of_lt (by omega), TruncOp.coef_of_lt (by omega)]

omit [CharZero R] in
/-- **A cochain with values in `Q[t]/tⁿ⁺¹` vanishes when its coefficients vanish.** -/
lemma coefI_eq_zero {n : ℕ} {X : GrOperad.Inv R (ConvOp R (Dual R E r) (TruncOp R Q n))}
    (h : ∀ k ≤ n, (TruncOp.coefSys n).coefI k X = 0) : X = 0 := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun c =>
    TruncOp.ext fun k hk => ?_)
  have hk0 : TruncOp.coef R Q n k A (ConvOp.toLin (X.1 A) c) = 0 :=
    congrArg (fun q : Def R E r Q => ConvOp.toLin (q.1 A) c) (h k hk)
  exact hk0.trans (map_zero (TruncOp.coef R Q n k A)).symm

omit [CharZero R] in
/-- **The generators of the extension of a lift by a derivation**: `v ↦ φ̃ v + tⁿ⁺¹ D v`. -/
noncomputable def Lift.extGen {n : ℕ} (ψ : Lift φ n) (D : GrDer (freeHom φ) false) :
    GrSpeciesHom R E (TruncOp R Q (n + 1)) where
  app A _ _ := TruncOp.sec R Q n A ∘ₗ ψ.homT.app A ∘ₗ (FreeGrL.ι R E).app A
    + TruncOp.top R Q n A ∘ₗ D.app A ∘ₗ (FreeGrL.ι R E).app A
  app_map e v := by
    show TruncOp.sec R Q n _ (ψ.homT.app _ ((FreeGrL.ι R E).app _
        (SymSpecies.map (R := R) e v)))
      + TruncOp.top R Q n _ (D.app _ ((FreeGrL.ι R E).app _ (SymSpecies.map (R := R) e v)))
      = _
    rw [(FreeGrL.ι R E).app_map, GrOperad.toGrSpecies_map, ψ.homT.app_map, D.app_map,
      TruncOp.sec_map, TruncOp.top_map, ← map_add]
    rfl
  app_par c v := by
    show TruncOp.sec R Q n _ (ψ.homT.app _ ((FreeGrL.ι R E).app _
        (GrSpecies.par (R := R) c v)))
      + TruncOp.top R Q n _ (D.app _ ((FreeGrL.ι R E).app _ (GrSpecies.par (R := R) c v)))
      = _
    rw [(FreeGrL.ι R E).app_par, GrOperad.toGrSpecies_par, ψ.homT.app_par, D.app_par,
      Bool.xor_false, TruncOp.sec_par, TruncOp.top_par, ← map_add]
    rfl

/-- **The extension of a lift by a derivation, on `T(E)`**: the morphism
`T(E) → Q[t]/tⁿ⁺²` with the values `φ̃ v + tⁿ⁺¹ D v` on the generators. -/
noncomputable def Lift.extT {n : ℕ} (ψ : Lift φ n) (D : GrDer (freeHom φ) false) :
    GrOperadHom R (FreeGrL R E) (TruncOp R Q (n + 1)) :=
  FreeGrL.homEquiv.symm (ψ.extGen D)

omit [CharZero R] in
lemma Lift.extT_ι {n : ℕ} (ψ : Lift φ n) (D : GrDer (freeHom φ) false) {A : Type} [Fintype A]
    [DecidableEq A] (v : E A) :
    (ψ.extT D).app A ((FreeGrL.ι R E).app A v)
      = TruncOp.sec R Q n A (ψ.homT.app A ((FreeGrL.ι R E).app A v))
        + TruncOp.top R Q n A (D.app A ((FreeGrL.ι R E).app A v)) :=
  FreeGrL.homEquiv_symm_ι _ v

omit [CharZero R] in
/-- The extension truncates to the lift. -/
lemma Lift.trunc_extT {n : ℕ} (ψ : Lift φ n) (D : GrDer (freeHom φ) false) :
    (TruncOp.trunc R Q n).comp (ψ.extT D) = ψ.homT :=
  FreeGrL.hom_ext fun A _ _ v => by
    show (TruncOp.trunc R Q n).app A ((ψ.extT D).app A ((FreeGrL.ι R E).app A v)) = _
    rw [Lift.extT_ι, map_add, TruncOp.trunc_sec, TruncOp.trunc_top, add_zero]

omit [CharZero R] in
/-- The coefficient of the new order of the extension is the derivation. -/
lemma Lift.coefDer_extT {n : ℕ} (ψ : Lift φ n) (D : GrDer (freeHom φ) false) :
    coefDer φ (ψ.extT D) (n + 1) = D :=
  FreeGrL.der_ext fun A _ _ v => by
    rw [coefDer_ι, Lift.extT_ι, map_add, TruncOp.coef_sec_succ, TruncOp.coef_top_self,
      zero_add]

/-- **The coefficients of the cochain of the extension**: those of the lift, and the cochain of
the derivation in the new order. -/
lemma Lift.coefI_extT {n : ℕ} (ψ : Lift φ n) (D : GrDer (freeHom φ) false) (k : ℕ) :
    (TruncOp.coefSys (n + 1)).coefI k (ofHomT r (ψ.extT D))
      = Function.update (ψ.toLiftSeq hφ).x (n + 1) (ofDerT φ D) k := by
  by_cases hk : k = n + 1
  · subst hk
    have h1 := coefI_ofHomT φ (ψ.extT D) (n + 1)
    have h2 := congrArg (fun D' : GrDer (freeHom φ) false => ofDerT φ D')
      (Lift.coefDer_extT ψ D)
    exact (h1.trans h2).trans
      (Function.update_self (n + 1) (ofDerT φ D) (ψ.toLiftSeq hφ).x).symm
  · have h1 := coefI_ofHomT_trunc (r := r) (ψ.extT D) ψ.homT (Lift.trunc_extT ψ D) hk
    have hx : (ψ.toLiftSeq hφ).x k
        = Function.update (ψ.toLiftSeq hφ).x (n + 1) (ofDerT φ D) k :=
      (Function.update_of_ne hk (ofDerT φ D) (ψ.toLiftSeq hφ).x).symm
    exact h1.trans ((Lift.x_def ψ k).symm.trans
      ((congrFun (Lift.toLiftSeq_x hφ ψ) k).symm.trans hx))

omit [CharZero R] in
/-- The coefficients of the square of the coefficients of the extension vanish up to order
`n + 1`, when the obstruction is minus the bracket of `φ κ` with the cochain of the
derivation. -/
lemma Lift.sq_extT {n : ℕ} (ψ : Lift φ n) (D : GrDer (freeHom φ) false)
    (hbr : GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
      = -(ψ.toLiftSeq hφ).obstruction) {m : ℕ} (hm : m ≤ n + 1) :
    GrOperad.Inv.sq (Function.update (ψ.toLiftSeq hφ).x (n + 1) (ofDerT φ D)) m = 0 := by
  by_cases hmn : m ≤ n
  · exact (ψ.toLiftSeq hφ).sq_update_of_le _ hmn
  · have hpar : GrOperad.Inv.IsPar true (ofDerT φ D) := isPar_ofDerT φ D
    have hmeq : m = n + 1 := by omega
    exact (congrArg (GrOperad.Inv.sq
      (Function.update (ψ.toLiftSeq hφ).x (n + 1) (ofDerT φ D))) hmeq).trans
        (((ψ.toLiftSeq hφ).sq_update_eq_zero_iff hpar).2 hbr)

/-- **The cochain of the extension has convolution square zero** when the obstruction is minus
the bracket of `φ κ` with the cochain of the derivation. -/
lemma Lift.star_extT {n : ℕ} (ψ : Lift φ n) (D : GrDer (freeHom φ) false)
    (hbr : GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
      = -(ψ.toLiftSeq hφ).obstruction) :
    GrOperad.Inv.star R _ (ofHomT r (ψ.extT D)) (ofHomT r (ψ.extT D)) = 0 := by
  refine coefI_eq_zero fun m hm => ?_
  have h := (TruncOp.coefSys (n + 1)).coefI_star (C := Dual R E r) hm
    (ofHomT r (ψ.extT D)) (ofHomT r (ψ.extT D))
  have hx : (fun k => (TruncOp.coefSys (n + 1)).coefI k (ofHomT r (ψ.extT D)))
      = Function.update (ψ.toLiftSeq hφ).x (n + 1) (ofDerT φ D) :=
    funext fun k => Lift.coefI_extT hφ ψ D k
  have hs : GrOperad.Inv.sq
      (fun k => (TruncOp.coefSys (n + 1)).coefI k (ofHomT r (ψ.extT D))) m = 0 :=
    (congrArg (fun x => GrOperad.Inv.sq x m) hx).trans (Lift.sq_extT hφ ψ D hbr hm)
  exact h.trans ((GrOperad.Inv.sq_def
    (fun k => (TruncOp.coefSys (n + 1)).coefI k (ofHomT r (ψ.extT D))) m).symm.trans hs)

/-- **The extension of a lift by a cochain of weight one, as a morphism**: for a derivation `D`
of `T(E)` along `T(E) → Q` whose cochain has bracket with `φ κ` minus the obstruction, the
morphism `P → Q[t]/tⁿ⁺²` with the values `φ̃ v + tⁿ⁺¹ D v` on the generators. For quadratic
relators, without generators without inputs. -/
noncomputable def Lift.extHom (hq : IsQuadratic R E r) (hE0 : ∀ v : E (Fin 0), v = 0) {n : ℕ}
    (ψ : Lift φ n) (D : GrDer (freeHom φ) false)
    (hbr : GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
      = -(ψ.toLiftSeq hφ).obstruction) : GrOperadHom R (Pres R E r) (TruncOp R Q (n + 1)) :=
  homOfT (ψ.extT D) ((star_ofHomT_eq_zero_iff hq hE0 _).1 (Lift.star_extT hφ ψ D hbr))

lemma Lift.extHom_proj (hq : IsQuadratic R E r) (hE0 : ∀ v : E (Fin 0), v = 0) {n : ℕ}
    (ψ : Lift φ n) (D : GrDer (freeHom φ) false)
    (hbr : GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
      = -(ψ.toLiftSeq hφ).obstruction) {A : Type} [Fintype A] [DecidableEq A]
    (x : FreeGrL R E A) :
    (ψ.extHom hφ hq hE0 D hbr).app A ((GrOperadIdeal.span R r).proj A x)
      = (ψ.extT D).app A x := rfl

/-- The extension truncates to the lift. -/
lemma Lift.trunc_extHom (hq : IsQuadratic R E r) (hE0 : ∀ v : E (Fin 0), v = 0) {n : ℕ}
    (ψ : Lift φ n) (D : GrDer (freeHom φ) false)
    (hbr : GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
      = -(ψ.toLiftSeq hφ).obstruction) :
    (TruncOp.trunc R Q n).comp (ψ.extHom hφ hq hE0 D hbr) = ψ.hom := by
  refine GrOperadHom.ext fun A _ _ y => ?_
  obtain ⟨x, rfl⟩ := (GrOperadIdeal.span R r).proj_surjective A y
  exact congrArg (fun g : GrOperadHom R (FreeGrL R E) (TruncOp R Q n) => g.app A x)
    (Lift.trunc_extT ψ D)

/-- The constant term of the extension is `φ`. -/
lemma Lift.const_extHom (hq : IsQuadratic R E r) (hE0 : ∀ v : E (Fin 0), v = 0) {n : ℕ}
    (ψ : Lift φ n) (D : GrDer (freeHom φ) false)
    (hbr : GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
      = -(ψ.toLiftSeq hφ).obstruction) {A : Type} [Fintype A] [DecidableEq A]
    (y : Pres R E r A) :
    TruncOp.coef R Q (n + 1) 0 A ((ψ.extHom hφ hq hE0 D hbr).app A y) = φ.app A y := by
  have h1 : TruncOp.coef R Q n 0 A ((TruncOp.trunc R Q n).app A
      ((ψ.extHom hφ hq hE0 D hbr).app A y)) = TruncOp.coef R Q n 0 A (ψ.hom.app A y) :=
    congrArg (fun g : GrOperadHom R (Pres R E r) (TruncOp R Q n) =>
      TruncOp.coef R Q n 0 A (g.app A y)) (Lift.trunc_extHom hφ hq hE0 ψ D hbr)
  exact (TruncOp.coef_trunc (Nat.zero_le n) _).symm.trans (h1.trans (ψ.const A y))

omit [CharZero R] in
/-- The extension on `T(E)` has values in the cycles, when the derivation has values in the
cycles on the generators. -/
lemma Lift.dT_extT {n : ℕ} (ψ : Lift φ n) (D : GrDer (freeHom φ) false)
    (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
      DGOperad.d (R := R) (D.app A ((FreeGrL.ι R E).app A v)) = 0) {A : Type} [Fintype A]
    [DecidableEq A] (x : FreeGrL R E A) :
    TruncOp.dT R Q (n + 1) A ((ψ.extT D).app A x) = 0 := by
  have h0 : (TruncOp.dDer R Q (n + 1)).compHom (ψ.extT D) = GrDer.zero _ true :=
    FreeGrL.der_eq_zero fun B _ _ v => by
      show TruncOp.dT R Q (n + 1) B ((ψ.extT D).app B ((FreeGrL.ι R E).app B v)) = 0
      have hc := ψ.closed B ((GrOperadIdeal.span R r).proj B ((FreeGrL.ι R E).app B v))
      rw [Lift.extT_ι, map_add, TruncOp.dT_sec, TruncOp.dT_top, hD, map_zero, add_zero]
      exact (congrArg (TruncOp.sec R Q n B) hc).trans (map_zero _)
  exact congrArg (fun D' : GrDer (ψ.extT D) true => D'.app A x) h0

/-- The extension has values in the cycles. -/
lemma Lift.closed_extHom (hq : IsQuadratic R E r) (hE0 : ∀ v : E (Fin 0), v = 0) {n : ℕ}
    (ψ : Lift φ n) (D : GrDer (freeHom φ) false)
    (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
      DGOperad.d (R := R) (D.app A ((FreeGrL.ι R E).app A v)) = 0)
    (hbr : GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
      = -(ψ.toLiftSeq hφ).obstruction) {A : Type} [Fintype A] [DecidableEq A]
    (y : Pres R E r A) :
    TruncOp.dT R Q (n + 1) A ((ψ.extHom hφ hq hE0 D hbr).app A y) = 0 := by
  obtain ⟨x, rfl⟩ := (GrOperadIdeal.span R r).proj_surjective A y
  exact Lift.dT_extT ψ D hD x

/-- **The extension of a lift by a cochain of weight one**: for a derivation `D` of `T(E)` along
`T(E) → Q` with values in the cycles on the generators, whose cochain has bracket with `φ κ`
minus the obstruction, the lift `P → Q[t]/tⁿ⁺²` with the values `φ̃ v + tⁿ⁺¹ D v` on the
generators. For quadratic relators, without generators without inputs. -/
noncomputable def Lift.extend (hq : IsQuadratic R E r) (hE0 : ∀ v : E (Fin 0), v = 0) {n : ℕ}
    (ψ : Lift φ n) (D : GrDer (freeHom φ) false)
    (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
      DGOperad.d (R := R) (D.app A ((FreeGrL.ι R E).app A v)) = 0)
    (hbr : GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
      = -(ψ.toLiftSeq hφ).obstruction) : Lift φ (n + 1) :=
  ⟨ψ.extHom hφ hq hE0 D hbr, fun _ _ _ y => Lift.const_extHom hφ hq hE0 ψ D hbr y,
    fun _ _ _ y => Lift.closed_extHom hφ hq hE0 ψ D hD hbr y⟩

/-- The extension truncates to the lift. -/
lemma Lift.trunc_extend (hq : IsQuadratic R E r) (hE0 : ∀ v : E (Fin 0), v = 0) {n : ℕ}
    (ψ : Lift φ n) (D : GrDer (freeHom φ) false)
    (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
      DGOperad.d (R := R) (D.app A ((FreeGrL.ι R E).app A v)) = 0)
    (hbr : GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
      = -(ψ.toLiftSeq hφ).obstruction) :
    (TruncOp.trunc R Q n).comp (ψ.extend hφ hq hE0 D hD hbr).hom = ψ.hom :=
  Lift.trunc_extHom hφ hq hE0 ψ D hbr

/-- **The extension theorem**: a lift `φ̃ : P → Q[t]/tⁿ⁺¹` of `φ` extends to a lift
`P → Q[t]/tⁿ⁺²` exactly when its obstruction is minus the bracket of `φ κ` with the cochain of a
derivation of `T(E)` along `T(E) → Q` with values in the cycles on the generators. For quadratic
relators over a field of characteristic zero, without generators without inputs. -/
theorem Lift.extends_iff (hq : IsQuadratic R E r) (hE0 : ∀ v : E (Fin 0), v = 0) {n : ℕ}
    (ψ : Lift φ n) :
    (∃ ψ' : Lift φ (n + 1), (TruncOp.trunc R Q n).comp ψ'.hom = ψ.hom)
      ↔ ∃ D : GrDer (freeHom φ) false,
        (∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
          DGOperad.d (R := R) (D.app A ((FreeGrL.ι R E).app A v)) = 0) ∧
        GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D)
          = -(ψ.toLiftSeq hφ).obstruction :=
  ⟨fun h => h.elim fun ψ' h' => Lift.exists_der_of_extension hφ ψ ψ' h',
    fun h => h.elim fun D hD =>
      ⟨ψ.extend hφ hq hE0 D hD.1 hD.2, Lift.trunc_extend hφ hq hE0 ψ D hD.1 hD.2⟩⟩

omit [CharZero R] in
/-- **The obstruction of a lift is a cocycle of the deformation complex.** -/
theorem Lift.defD_obstruction {n : ℕ} (ψ : Lift φ n) :
    defD φ hφ (ψ.toLiftSeq hφ).obstruction = 0 :=
  (ψ.toLiftSeq hφ).twD_obstruction

/-- **The differential of the deformation complex on a cochain of weight one with values in the
cycles** is the bracket with `φ κ`. -/
theorem defD_ofDerT (D : GrDer (freeHom φ) false)
    (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
      DGOperad.d (R := R) (D.app A ((FreeGrL.ι R E).app A v)) = 0) :
    defD φ hφ (ofDerT φ D) = GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D) := by
  have h0 : GrOperad.Inv.appDer (Twisting.convD R (Dual R E r) Q) (ofDerT φ D) = 0 :=
    Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun c =>
      (congrArg (fun z => DGOperad.d (R := R) (D.app A z))
        (kapL_eq_ι (R := R) (E := E) ((dualSub R E r).incl A c))).trans (hD A _))
  exact (GrOperad.Inv.twD_apply _ _ _).trans
    ((congrArg (fun z => z + GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofDerT φ D))
      h0).trans (zero_add _))

/-- **The extension theorem, with the differential of the deformation complex**: a lift extends
by one order exactly when its obstruction is minus the differential of the cochain of a
derivation of `T(E)` along `T(E) → Q` with values in the cycles on the generators. -/
theorem Lift.extends_iff_defD (hq : IsQuadratic R E r) (hE0 : ∀ v : E (Fin 0), v = 0) {n : ℕ}
    (ψ : Lift φ n) :
    (∃ ψ' : Lift φ (n + 1), (TruncOp.trunc R Q n).comp ψ'.hom = ψ.hom)
      ↔ ∃ D : GrDer (freeHom φ) false,
        (∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
          DGOperad.d (R := R) (D.app A ((FreeGrL.ι R E).app A v)) = 0) ∧
        defD φ hφ (ofDerT φ D) = -(ψ.toLiftSeq hφ).obstruction :=
  ⟨fun h => ((Lift.extends_iff hφ hq hE0 ψ).1 h).elim fun D hD =>
      ⟨D, hD.1, (defD_ofDerT hφ D hD.1).trans hD.2⟩,
    fun h => (Lift.extends_iff hφ hq hE0 ψ).2 (h.elim fun D hD =>
      ⟨D, hD.1, (defD_ofDerT hφ D hD.1).symm.trans hD.2⟩)⟩

end Extend

end Koszul

end Operad
