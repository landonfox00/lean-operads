/-
# Twisting morphisms and the cobar adjunction

For a coaugmented graded cooperad `C` and a dg operad `P`, a **twisting morphism** `C → P`
(`Twisting R C P`) is an odd invariant family `α` of the convolution operad — an odd equivariant
map `C → P` — vanishing on the coaugmentation and satisfying the **Maurer–Cartan equation**

  `∂α + α ⋆ α = 0`,   `∂α = d ∘ α`,

`⋆` being the convolution product.

* **The cobar adjunction** (`Cobar.homEquiv`): the morphisms of graded operads `ΩC → P` commuting
  with the differentials are the twisting morphisms `C → P`, by composition with the universal
  twisting morphism `ι` (`Cobar.homEquiv_apply`). A morphism out of the free graded operad on
  `s⁻¹ C̄` is an odd equivariant map `C → P` killing the coaugmentation, and it commutes with the
  differentials exactly when that map satisfies the Maurer–Cartan equation: both `d ∘ φ` and
  `φ ∘ d` are derivations along `φ`, determined by their values on the generators.
* The universal twisting morphism satisfies the Maurer–Cartan equation in the convolution operad
  of `C` and the cobar construction (`Cobar.ι_mc`).
-/
import Operad.Cobar

universe u v w

namespace Operad

open Sym GerBV

variable (R : Type u) [CommRing R] (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]

section Defs

variable [GrOperad R P]

/-- An invariant family of the convolution operad **vanishing on the coaugmentation**. -/
def KillsUnit (α : GrOperad.Inv R (ConvOp R C P)) : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), x ∈ GrCooperad.unitSpan R C A →
    ConvOp.toLin (α.1 A) x = 0

end Defs

variable [DGOperad R P]

/-- **Twisting morphisms** `C → P`: the odd equivariant maps vanishing on the coaugmentation and
satisfying the Maurer–Cartan equation `∂α + α ⋆ α = 0`. -/
def Twisting : Type _ :=
  {α : GrOperad.Inv R (ConvOp R C P) // GrOperad.Inv.IsPar true α ∧ KillsUnit R C P α ∧
    GrOperad.Inv.appDer (ConvOp.postDer (C := C) (DGOperad.toDer (R := R) (P := P))) α
      + GrOperad.Inv.star R _ α α = 0}

/-- **Morphisms of graded operads out of the cobar construction commuting with the
differentials.** -/
def CobarHom : Type _ :=
  {φ : GrOperadHom R (CobarGr R C) P // ∀ (A : Type) [Fintype A] [DecidableEq A]
    (y : CobarGr R C A), φ.app A ((Cobar.d R C).app A y) = DGOperad.d (R := R) (φ.app A y)}

namespace Cobar

/-- **The universal twisting morphism satisfies the Maurer–Cartan equation.** -/
theorem ι_mc : GrOperad.Inv.appDer (ConvOp.postDer (C := C) (d R C)) (ι R C) + ιι R C = 0 := by
  rw [d_ι, neg_add_cancel]

variable {R C P}

/-- The twisting morphism of a morphism out of the cobar construction: `φ ∘ ι`. -/
noncomputable def twOf (φ : GrOperadHom R (CobarGr R C) P) : GrOperad.Inv R (ConvOp R C P) :=
  GrOperad.Inv.appHom (ConvOp.postHom (C := C) φ) (ι R C)

lemma twOf_apply (φ : GrOperadHom R (CobarGr R C) P) {A : Type} [Fintype A] [DecidableEq A]
    (x : C A) : ConvOp.toLin ((twOf φ).1 A) x = φ.app A (ιL R C A x) := rfl

lemma isPar_twOf (φ : GrOperadHom R (CobarGr R C) P) : GrOperad.Inv.IsPar true (twOf φ) := by
  intro A _ _
  show ConvOp.parC true ((ConvOp.postHom (C := C) φ).app A ((ι R C).1 A))
    = (ConvOp.postHom (C := C) φ).app A ((ι R C).1 A)
  rw [← ConvOp.par_def, ← (ConvOp.postHom (C := C) φ).app_par, isPar_ι R C A]

lemma killsUnit_twOf (φ : GrOperadHom R (CobarGr R C) P) : KillsUnit R C P (twOf φ) := by
  intro A _ _ x hx
  rw [twOf_apply, ιL_unitSpan R C hx, map_zero]

/-- The values on the generators of the morphism out of the cobar construction defined by an
invariant family vanishing on the coaugmentation. -/
noncomputable def genOf (α : GrOperad.Inv R (ConvOp R C P)) (hα : KillsUnit R C P α)
    (A : Type) [Fintype A] [DecidableEq A] : CobarGen R C A →ₗ[R] P A :=
  Submodule.liftQ (GrCooperad.unitSpan R C A) (ConvOp.toLin (α.1 A)) fun x hx => hα A x hx

lemma genOf_proj (α : GrOperad.Inv R (ConvOp R C P)) (hα : KillsUnit R C P α) {A : Type}
    [Fintype A] [DecidableEq A] (x : C A) :
    genOf α hα A (GrCooperad.Red.proj R C A x) = ConvOp.toLin (α.1 A) x := rfl

/-- The morphism of graded linear species `s⁻¹ C̄ → P` of an odd invariant family vanishing on
the coaugmentation. -/
noncomputable def genSp (α : GrOperad.Inv R (ConvOp R C P)) (hpar : GrOperad.Inv.IsPar true α)
    (hα : KillsUnit R C P α) : GrSpeciesHom R (CobarGen R C) P where
  app A _ _ := genOf α hα A
  app_map {A B} _ _ _ _ e v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    show genOf α hα B (GrCooperad.Red.proj R C B (SymSpecies.map (R := R) e x))
      = GrOperad.map (R := R) e (genOf α hα A (GrCooperad.Red.proj R C A x))
    rw [genOf_proj, genOf_proj, ← GrOperad.Inv.map_apply α e]
    show ConvOp.toLin (ConvOp.mapC e _) _ = _
    rw [ConvOp.mapC_apply, SymSpecies.map_symm_map]
  app_par {A} _ _ b v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    show genOf α hα A (GrCooperad.Red.proj R C A (GrSpecies.par (R := R) (!b) x))
      = GrOperad.par (R := R) b (genOf α hα A (GrCooperad.Red.proj R C A x))
    rw [genOf_proj, genOf_proj, ConvOp.parC_eq_self_iff.1 (hpar A), Bool.xor_true, Bool.not_not]

/-- The morphism of graded operads out of the cobar construction of an odd invariant family
vanishing on the coaugmentation. -/
noncomputable def homOf (α : GrOperad.Inv R (ConvOp R C P)) (hpar : GrOperad.Inv.IsPar true α)
    (hα : KillsUnit R C P α) : GrOperadHom R (CobarGr R C) P :=
  FreeGrL.homEquiv.symm (genSp α hpar hα)

lemma homOf_ιL (α : GrOperad.Inv R (ConvOp R C P)) (hpar : GrOperad.Inv.IsPar true α)
    (hα : KillsUnit R C P α) {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    (homOf α hpar hα).app A (ιL R C A x) = ConvOp.toLin (α.1 A) x := by
  rw [ιL_apply, homOf, FreeGrL.homEquiv_symm_ι]
  exact genOf_proj α hα x

lemma twOf_homOf (α : GrOperad.Inv R (ConvOp R C P)) (hpar : GrOperad.Inv.IsPar true α)
    (hα : KillsUnit R C P α) : twOf (homOf α hpar hα) = α :=
  Subtype.ext (funext fun _ => funext fun _ => funext fun _ =>
    ConvOp.ext fun x => homOf_ιL α hpar hα x)

/-- **The differential of `P` after a morphism out of the cobar construction**, as a derivation
along it. -/
noncomputable def dAfter (φ : GrOperadHom R (CobarGr R C) P) : GrDer φ true :=
  GrDer.compHom (DGOperad.toDer (R := R) (P := P)) φ

/-- **A morphism out of the cobar construction after its differential**, as a derivation along
it. -/
noncomputable def dBefore (φ : GrOperadHom R (CobarGr R C) P) : GrDer φ true :=
  GrDer.homComp φ (d R C)

/-- **The Maurer–Cartan equation of `φ ∘ ι` is `d ∘ φ = φ ∘ d` on the generators.** -/
lemma mc_iff (φ : GrOperadHom R (CobarGr R C) P) :
    GrOperad.Inv.appDer (ConvOp.postDer (C := C) (DGOperad.toDer (R := R) (P := P))) (twOf φ)
      + GrOperad.Inv.star R _ (twOf φ) (twOf φ) = 0
      ↔ ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        DGOperad.d (R := R) (φ.app A (ιL R C A x)) = φ.app A ((d R C).app A (ιL R C A x)) := by
  have hst : GrOperad.Inv.star R _ (twOf φ) (twOf φ)
      = GrOperad.Inv.appHom (ConvOp.postHom (C := C) φ) (ιι R C) :=
    (GrOperad.Inv.appHom_star _ _ _).symm
  rw [hst]
  constructor
  · intro h A _ _ x
    have h1 := congrArg (fun q : GrOperad.Inv R (ConvOp R C P) => ConvOp.toLin (q.1 A) x) h
    simp only at h1
    rw [d_ιL, map_neg]
    rw [eq_neg_iff_add_eq_zero]
    exact h1
  · intro h
    refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun x => ?_)
    show DGOperad.d (R := R) (φ.app A (ιL R C A x))
      + φ.app A (ConvOp.toLin ((ιι R C).1 A) x) = 0
    rw [h, d_ιL, map_neg, neg_add_cancel]

/-- **The morphism of a twisting morphism commutes with the differentials.** -/
lemma homOf_comm (α : GrOperad.Inv R (ConvOp R C P)) (hpar : GrOperad.Inv.IsPar true α)
    (hα : KillsUnit R C P α)
    (hmc : GrOperad.Inv.appDer (ConvOp.postDer (C := C) (DGOperad.toDer (R := R) (P := P))) α
      + GrOperad.Inv.star R _ α α = 0) {A : Type} [Fintype A] [DecidableEq A]
    (y : CobarGr R C A) :
    (homOf α hpar hα).app A ((d R C).app A y) = DGOperad.d (R := R) ((homOf α hpar hα).app A y)
    := by
  have hmc' := (mc_iff (homOf α hpar hα)).1 (by rw [twOf_homOf]; exact hmc)
  have hder : dBefore (homOf α hpar hα) = dAfter (homOf α hpar hα) :=
    FreeGrL.der_ext fun A _ _ v => by
      obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
      exact (hmc' A x).symm
  exact congrArg (fun D : GrDer _ true => D.app A y) hder

lemma homOf_twOf (φ : GrOperadHom R (CobarGr R C) P) :
    homOf (twOf φ) (isPar_twOf φ) (killsUnit_twOf φ) = φ :=
  FreeGrL.hom_ext fun A _ _ v => by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    exact homOf_ιL (twOf φ) (isPar_twOf φ) (killsUnit_twOf φ) x

/-- **The cobar adjunction**: morphisms of graded operads out of the cobar construction commuting
with the differentials are the twisting morphisms, by composition with the universal twisting
morphism. -/
noncomputable def homEquiv : CobarHom R C P ≃ Twisting R C P where
  toFun φ := ⟨twOf φ.1, isPar_twOf φ.1, killsUnit_twOf φ.1,
    (mc_iff φ.1).2 fun A _ _ _ => (φ.2 A _).symm⟩
  invFun α := ⟨homOf α.1 α.2.1 α.2.2.1, fun _ _ _ y => homOf_comm α.1 α.2.1 α.2.2.1 α.2.2.2 y⟩
  left_inv φ := Subtype.ext (homOf_twOf φ.1)
  right_inv α := Subtype.ext (twOf_homOf α.1 α.2.1 α.2.2.1)

/-- The twisting morphism of a morphism out of the cobar construction is its composite with the
universal twisting morphism. -/
lemma homEquiv_apply (φ : CobarHom R C P) {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    ConvOp.toLin ((homEquiv φ).1.1 A) x = φ.1.app A (ιL R C A x) := rfl

end Cobar

end Operad
