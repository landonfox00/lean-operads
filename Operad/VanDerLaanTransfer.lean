/-
# The transfer of twisting morphisms along a retract datum

For a dg operad `P` with a retract datum `(e, h)` (`OpRetract`) and an ideal `I` stable under `∂`
without operations without inputs, a twisting morphism `α : C → P` with values in `I`, out of a
conilpotent dg cooperad `C`, over a `ℚ`-algebra with the projectivity hypothesis of
`BarAdjunction.lean`, **transfers to a twisting morphism `α' : C → P` with values the operations
`x` with `e ∘ x = x`** (`Bar.exists_transfer`): `α'` is the van der Laan map after the morphism
`f : C → B(P, I)` of `Bar.exists_hom_dg` with `π ∘ f = α`.

* **Twisting morphisms from the Maurer–Cartan equation at each element** (`TwistingDG.ofApply`).
* **Twisting morphisms pull back along morphisms commuting with the differentials**
  (`TwistingDG.comap`): for a coaugmented morphism of graded cooperads `f : C → C'` with
  `f ∘ d = d' ∘ f` and a twisting morphism `β : C' → P` for `d'`, `β ∘ f` is one for `d`.
-/
import Operad.VanDerLaan

universe u v w

namespace Operad

open Sym GerBV FreeGrL FreeGr VdL
open scoped TensorProduct

namespace TwistingDG

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]

/-- **A twisting morphism from the Maurer–Cartan equation at each element**:
`∂ (α x) + α (d x) + (α ⋆ α) x = 0`, for `α` odd and vanishing on the coaugmentation. -/
noncomputable def ofApply (α : GrOperad.Inv R (ConvOp R C P)) (hpar : GrOperad.Inv.IsPar true α)
    (hk : KillsUnit R C P α)
    (hmc : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      DGOperad.d (R := R) (ConvOp.toLin (α.1 A) x) + ConvOp.toLin (α.1 A) (DGCooperad.d (R := R) x)
        + ConvOp.toLin ((GrOperad.Inv.star R _ α α).1 A) x = 0) :
    TwistingDG R C P :=
  ⟨α, hpar, hk, Subtype.ext (funext fun A => funext fun _ => funext fun _ => by
    ext x
    have htw : GrOperad.tw (R := R) true (α.1 A) = -α.1 A := by
      rw [GrOperad.tw_hom true (hpar A), Bool.and_self, σ_true, neg_one_smul]
    show DGOperad.d (R := R) (ConvOp.toLin (α.1 A) x)
        - ConvOp.toLin (GrOperad.tw (R := R) true (α.1 A)) (DGCooperad.d (R := R) x)
        + ConvOp.toLin ((GrOperad.Inv.star R _ α α).1 A) x = 0
    rw [htw, ConvOp.toLin_neg, LinearMap.neg_apply, sub_neg_eq_add]
    exact hmc A x)⟩

@[simp] lemma ofApply_coe (α : GrOperad.Inv R (ConvOp R C P)) (hpar : GrOperad.Inv.IsPar true α)
    (hk : KillsUnit R C P α) (hmc) : (ofApply α hpar hk hmc).1 = α := rfl

end TwistingDG

/-! ## The transfer -/

namespace Bar

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]
  {I : GrOperadIdeal R P}
  (hI : ∀ {A : Type} [Fintype A] [DecidableEq A] {x : P A}, x ∈ I.sub A →
    DGOperad.d (R := R) x ∈ I.sub A)
  (ρ : OpRetract R P)
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C]

local notation "𝒞" => FreeGrL R (BarGen I)

/-- **The van der Laan map after a morphism into the bar construction.** -/
noncomputable def vdLAfter (g : GrCooperadHom R C 𝒞) : GrOperad.Inv R (ConvOp R C P) :=
  GrOperad.Inv.appHom (ConvOp.preHom (P := P) g) (vdL I ρ)

omit [GrCooperad.Coaug R C] in
lemma vdLAfter_apply (g : GrCooperadHom R C 𝒞) {A : Type} [Fintype A] [DecidableEq A]
    (x : C A) : ConvOp.toLin ((vdLAfter ρ g).1 A) x = vdLL I ρ A (g.app A x) := rfl

/-- **The transfer of twisting morphisms along a retract datum**: a twisting morphism
`α : C → P` with values in `I` gives a twisting morphism `α' = v ∘ f`, for `v` the van der Laan
map and `f : C → B(P, I)` the morphism commuting with the differentials with `π ∘ f = α`; its
values are operations `x` with `e ∘ x = x`. -/
theorem exists_transfer [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (BarGen I (Fin k)))
    (α : TwistingDG R C P)
    (hIα : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      (ConvOp.toLin (α.1.1 A) x : P A) ∈ I.sub A) :
    ∃ α' : TwistingDG R C P, ∃ g : GrCooperadHom R C 𝒞,
      (∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        piL I A (g.app A x) = ConvOp.toLin (α.1.1 A) x) ∧
      (∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        g.app A (DGCooperad.d (R := R) x) = dTot hI A (g.app A x)) ∧
      (∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        ConvOp.toLin (α'.1.1 A) x = vdLL I ρ A (g.app A x)) ∧
      ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        GrOperad.lcomp R ρ.e (ConvOp.toLin (α'.1.1 A) x) = ConvOp.toLin (α'.1.1 A) x := by
  obtain ⟨g, hg1, hg, hgd⟩ := exists_hom_dg hI hI0 hC hproj α hIα
  have hpar : GrOperad.Inv.IsPar true (vdLAfter ρ g) := by
    intro A _ _
    show GrOperad.par (R := R) true ((ConvOp.preHom (P := P) g).app A ((vdL I ρ).1 A)) = _
    rw [← (ConvOp.preHom (P := P) g).app_par]
    exact congrArg ((ConvOp.preHom (P := P) g).app A) (isPar_vdL ρ A)
  have hk : KillsUnit R C P (vdLAfter ρ g) := by
    intro A _ _ x hx
    rw [vdLAfter_apply]
    refine Submodule.span_induction (p := fun x _ => vdLL I ρ A (g.app A x) = 0) ?_
      (by simp) ?_ ?_ hx
    · rintro _ ⟨e, rfl⟩
      show vdLL I ρ A (g.app A (SymSpecies.map (R := R) e (GrCooperad.Coaug.one (R := R)))) = 0
      rw [g.app_map, hg1]
      exact (vdLL_map ρ e (GrOperad.one (R := R))).trans (by rw [vdLL_one, map_zero])
    · intro x y _ _ hx hy
      beta_reduce at hx hy ⊢
      rw [map_add, map_add, hx, hy, add_zero]
    · intro a x _ hx
      beta_reduce at hx ⊢
      rw [map_smul, map_smul, hx, smul_zero]
  refine ⟨TwistingDG.ofApply (vdLAfter ρ g) hpar hk fun A _ _ x => ?_, g, hg, hgd,
    fun A _ _ x => vdLAfter_apply ρ g x, fun A _ _ x => lcomp_vdLL ρ (g.app A x)⟩
  rw [vdLAfter_apply, vdLAfter_apply, hgd, vdLAfter, ← GrOperad.Inv.appHom_star,
    GrOperad.Inv.appHom_apply, ConvOp.preHom_app, LinearMap.comp_apply]
  exact vdL_mc ρ hI hI0 (g.app A x)

end Bar

end Operad
