/-
# The Koszul dual cooperad is functorial in the quadratic data

Over a field of characteristic zero, a morphism `j : E → E'` of the generators carrying the
relations `(r)` into the relations `(r')` induces **a morphism of graded cooperads
`P^¡ → P'^¡`** (`Koszul.dualMap`), the restriction of the morphism of cut cooperads
`T^c(sE) → T^c(sE')` (`Koszul.incl_dualMap`).

* The desuspension map and its convolution square are natural in the generators
  (`Koszul.kapL_mapSp`, `Koszul.star_kapT_mapSp`).
* It is enough that `j` carries the relators into the ideal of the relations
  (`Koszul.mapSp_mem_span`).
* The image of `P^¡` lies in `P'^¡` (`Koszul.mapSp_mem_dualSub`), by the universal property
  `Koszul.le_dualSub`.

Not proved: the compatibility of `Koszul.dualMap` with the composition of morphisms of quadratic
data.
-/
import Operad.OrdCut
import Operad.KoszulInhom

universe u

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace Koszul

variable {K : Type u} [Field K] [CharZero K]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {E' : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E' A)] [GrSpecies K E']
  {A : Type} [Fintype A] [DecidableEq A]

omit [CharZero K] in
/-- **The parity shift of a morphism of graded linear species.** -/
def shiftHom (j : GrSpeciesHom K E E') :
    GrSpeciesHom K (GrSpecies.Shift E K) (GrSpecies.Shift E' K) where
  app A _ _ := j.app A
  app_map e x := j.app_map e x
  app_par b x := j.app_par (!b) x

/-- The desuspension map is natural in the generators. -/
lemma kapL_mapSp (j : GrSpeciesHom K E E') (z : Cut K E A) :
    kapL K E' A ((FreeGrL.mapSp (shiftHom j)).app A z)
      = (FreeGrL.mapSp j).app A (kapL K E A z) := by
  rw [kapL_eq_genCoef, kapL_eq_genCoef, FreeGrL.genCoef_mapSp, FreeGrL.mapSp_ι]
  rfl

/-- **The convolution square of the desuspension map is natural in the generators.** -/
lemma star_kapT_mapSp (j : GrSpeciesHom K E E') (z : Cut K E A) :
    ConvOp.toLin ((GrOperad.Inv.star K _ (kapT K E') (kapT K E')).1 A)
        ((FreeGrL.mapSp (shiftHom j)).app A z)
      = (FreeGrL.mapSp j).app A
        (ConvOp.toLin ((GrOperad.Inv.star K _ (kapT K E) (kapT K E)).1 A) z) := by
  have h1 : GrOperad.Inv.appHom (ConvOp.preHom (P := FreeGrL K E')
      (FreeGrL.mapCoop (shiftHom j))) (kapT K E')
      = GrOperad.Inv.appHom (ConvOp.postHom (C := Cut K E) (FreeGrL.mapSp j)) (kapT K E) :=
    Subtype.ext (funext fun B => funext fun _ => funext fun _ =>
      congrArg ConvOp.of (LinearMap.ext fun y => kapL_mapSp j y))
  have h2 := GrOperad.Inv.appHom_star (ConvOp.preHom (P := FreeGrL K E')
    (FreeGrL.mapCoop (shiftHom j))) (kapT K E') (kapT K E')
  have h3 := GrOperad.Inv.appHom_star (ConvOp.postHom (C := Cut K E) (FreeGrL.mapSp j))
    (kapT K E) (kapT K E)
  rw [h1] at h2
  exact congrArg (fun q : GrOperad.Inv K (ConvOp K (Cut K E) (FreeGrL K E')) =>
    ConvOp.toLin (q.1 A) z) (h2.trans h3.symm)

variable (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n))) (r' : ∀ n : ℕ, Set (FreeGrL K E' (Fin n)))

omit [CharZero K] in
/-- A morphism of the generators carrying the relators into the ideal of the relations carries
the ideal of the relations into the ideal of the relations. -/
lemma mapSp_mem_span (j : GrSpeciesHom K E E')
    (hgen : ∀ n, ∀ x ∈ r n, (FreeGrL.mapSp j).app (Fin n) x ∈ (GrOperadIdeal.span K r').sub (Fin n))
    (B : Type) [Fintype B] [DecidableEq B] (x : FreeGrL K E B)
    (hx : x ∈ (GrOperadIdeal.span K r).sub B) :
    (FreeGrL.mapSp j).app B x ∈ (GrOperadIdeal.span K r').sub B := by
  have h : GrOperadIdeal.span K r
      ≤ ((GrOperadIdeal.span K r').projHom.comp (FreeGrL.mapSp j)).ker :=
    GrOperadIdeal.span_le.2 fun n y hy =>
      (GrOperadHom.mem_ker _ _).2 (((GrOperadIdeal.span K r').proj_eq_zero_iff _).2 (hgen n y hy))
  exact ((GrOperadIdeal.span K r').proj_eq_zero_iff _).1 ((GrOperadHom.mem_ker _ _).1 (h B hx))

/-- **A morphism of the generators carrying the relations into the relations maps the Koszul
dual cooperad into the Koszul dual cooperad.** -/
theorem mapSp_mem_dualSub (j : GrSpeciesHom K E E')
    (hr : ∀ (B : Type) [Fintype B] [DecidableEq B] (x : FreeGrL K E B),
      x ∈ (GrOperadIdeal.span K r).sub B →
        (FreeGrL.mapSp j).app B x ∈ (GrOperadIdeal.span K r').sub B)
    {x : Cut K E A} (hx : x ∈ (dualSub K E r).sub A) :
    (FreeGrL.mapSp (shiftHom j)).app A x ∈ (dualSub K E' r').sub A := by
  have hle : (dualSub K E r).map (FreeGrL.mapCoop (shiftHom j)) ≤ dualSub K E' r' :=
    le_dualSub r' fun B _ _ y hy => by
      obtain ⟨x', hx', rfl⟩ := GrSubCooperad.mem_map.1 hy
      rw [FreeGrL.mapCoop_app, star_kapT_mapSp]
      have hadm : x' ∈ admissible K E r B := GrSubCooperad.cogen_le (admissible K E r) B hx'
      exact hr B _ hadm
  exact hle A (GrSubCooperad.mem_map.2 ⟨x, hx, rfl⟩)

/-- **The morphism of Koszul dual cooperads** induced by a morphism of the generators carrying
the relations into the relations. -/
noncomputable def dualMap (j : GrSpeciesHom K E E')
    (hr : ∀ (B : Type) [Fintype B] [DecidableEq B] (x : FreeGrL K E B),
      x ∈ (GrOperadIdeal.span K r).sub B →
        (FreeGrL.mapSp j).app B x ∈ (GrOperadIdeal.span K r').sub B) :
    GrCooperadHom K (Dual K E r) (Dual K E' r') :=
  (dualSub K E' r').liftHom ((FreeGrL.mapCoop (shiftHom j)).comp (dualSub K E r).inclHom)
    fun _ _ _ x => mapSp_mem_dualSub r r' j hr x.2

lemma incl_dualMap (j : GrSpeciesHom K E E')
    (hr : ∀ (B : Type) [Fintype B] [DecidableEq B] (x : FreeGrL K E B),
      x ∈ (GrOperadIdeal.span K r).sub B →
        (FreeGrL.mapSp j).app B x ∈ (GrOperadIdeal.span K r').sub B) (x : Dual K E r A) :
    (dualSub K E' r').incl A ((dualMap r r' j hr).app A x)
      = (FreeGrL.mapSp (shiftHom j)).app A ((dualSub K E r).incl A x) := rfl

end Koszul

end Operad
