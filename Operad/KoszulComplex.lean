/-
# The fundamental theorem of twisting morphisms and the Koszul complex

For a reduced coaugmented graded cooperad `C` over a field of characteristic zero, a dg operad
`P` without operations with no inputs, and a morphism `f_α : ΩC → P` of dg operads with twisting
morphism `α = f_α ∘ ι`:

* **the fundamental theorem of twisting morphisms** (`Cobar.fundamental`): `f_α` is a
  quasi-isomorphism iff `1 ∘ f_α : C ∘_ι ΩC → C ∘_α P` is one. The twisted composite product
  `C ∘_ι ΩC` is acyclic outside the unit (`GrComposite.cobar_contraction`), so this says that
  `f_α` is a quasi-isomorphism iff `C ∘_α P` is acyclic.

For quadratic data `(E, r)` without generators with at most one input and relators without unit
component, the presented operad `P = T(E)/(r)` is augmented (`Koszul.presAug`), and:

* **the Koszul complex criterion** (`Koszul.isKoszul_iff_acyclic`): `P` is Koszul iff the Koszul
  complex `P^¡ ∘_κ P` is acyclic in the arities at least two, when `R·1 → P(1)` is injective.
-/
import Operad.GrTwistedConverse
import Operad.KoszulCriterion

universe u v w

namespace Operad

open Function Sym GerBV ConvOp GrComposite

/-! ## Augmentations of quotients -/

namespace GrAug

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P] (ε : GrAug R P)

/-- **The augmentation ideal.** -/
def ker : GrOperadIdeal R P where
  sub A _ _ := LinearMap.ker (ε.u A)
  par_mem := by
    intro A _ _ b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    cases b
    · rw [GrAug.u_par_false, hx]
    · exact ε.u_par x
  map_mem := by
    intro A B _ _ _ _ e x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [ε.u_map, hx]
  comp_mem_left := by
    intro A B _ _ _ _ i x y hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [ε.u_comp, hx, zero_mul]
  comp_mem_right := by
    intro A B _ _ _ _ i x y hy
    rw [LinearMap.mem_ker] at hy ⊢
    rw [ε.u_comp, hy, mul_zero]

/-- **An augmentation descends to the quotient by an ideal in its kernel.** -/
noncomputable def quot (I : GrOperadIdeal R P)
    (hI : ∀ (A : Type) [Fintype A] [DecidableEq A], I.sub A ≤ LinearMap.ker (ε.u A)) :
    GrAug R I.Quot where
  u A _ _ := (I.sub A).liftQ (ε.u A) (hI A)
  u_map σ X := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ X
    show (I.sub _).liftQ (ε.u _) (hI _) (I.projHom.app _ (GrOperad.map (R := R) σ x)) = _
    exact ε.u_map σ x
  u_par X := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ X
    show (I.sub _).liftQ (ε.u _) (hI _) (I.projHom.app _ (GrOperad.par (R := R) true x)) = 0
    exact ε.u_par x
  u_one := ε.u_one
  u_comp i X Y := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ X
    obtain ⟨y, rfl⟩ := I.proj_surjective _ Y
    show (I.sub _).liftQ (ε.u _) (hI _) (I.projHom.app _ (GrOperad.comp (R := R) i x y)) = _
    exact ε.u_comp i x y
  u_eq_zero h X := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ X
    exact ε.u_eq_zero h x

lemma quot_u_proj (I : GrOperadIdeal R P)
    (hI : ∀ (A : Type) [Fintype A] [DecidableEq A], I.sub A ≤ LinearMap.ker (ε.u A))
    {A : Type} [Fintype A] [DecidableEq A] (x : P A) : (ε.quot I hI).u A (I.proj A x) = ε.u A x :=
  rfl

/-- An augmentation of a graded operad, for its zero differential. -/
def toZeroDG (ε : GrAug R P) : GrAug R (ZeroDG R P) :=
  ⟨ε.u, ε.u_map, ε.u_par, ε.u_one, ε.u_comp, ε.u_eq_zero⟩

end GrAug

/-! ## Free graded operads in the arities at most one -/

namespace FreeGrL

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
include hred

/-- **Without generators with at most one input, there are no trees without inputs.** -/
lemma eq_zero_of_isEmpty {A : Type} [Fintype A] [DecidableEq A] (hA : IsEmpty A)
    (x : FreeGrL R V A) : x = 0 := by
  have h := mem_unitSpan_of_card_le hred (by rw [Fintype.card_eq_zero]; exact Nat.zero_le _) x
  rwa [GrCooperad.unitSpan_eq_bot ⟨fun e => hA.elim (e ())⟩, Submodule.mem_bot] at h

/-- **Without generators with at most one input, the trees with one input are the multiples of
the unit.** -/
lemma eq_smul_one {A : Type} [Fintype A] [DecidableEq A] (e : Unit ≃ A) (x : FreeGrL R V A) :
    ∃ c : R, x = c • GrOperad.map (R := R) e (GrOperad.one (R := R)) := by
  have h := mem_unitSpan_of_card_le hred
    (by rw [← Fintype.card_congr e, Fintype.card_unit]) x
  rw [GrCooperad.unitSpan, GrCooperad.unitSpanOf, Submodule.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  haveI := subsingleton_of_unit e
  rw [Fintype.sum_subsingleton _ e] at hc
  exact ⟨c e, hc.symm⟩

end FreeGrL

/-! ## The fundamental theorem of twisting morphisms -/

namespace Cobar

variable {R : Type u} [Field R] [CharZero R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]
  (ε : GrAug R P)
  (hred : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A ≤ 1 →
    ∀ x : C A, x ∈ GrCooperad.unitSpan R C A)

omit [CharZero R] in
include hred in
/-- The generators of the cobar construction of a reduced cooperad have at least two inputs. -/
lemma gen_eq_zero (B : Type) [Fintype B] [DecidableEq B] (hB : Fintype.card B ≤ 1)
    (v : CobarGen R C B) : v = 0 := by
  obtain ⟨x, hx⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) B
    ((GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R C) B).symm v)
  have h0 : GrCooperad.Red.proj R C B x = 0 := (Submodule.Quotient.mk_eq_zero _).2 (hred B hB x)
  rw [h0] at hx
  have := congrArg (GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R C) B) hx
  rwa [LinearEquiv.apply_symm_apply, map_zero, eq_comm] at this

include hred in
/-- **The data of the comparison** `1 ∘ f : C ∘_ι ΩC → C ∘_α P`. -/
lemma compareData (hP0 : ∀ (B : Type) [Fintype B] [DecidableEq B], IsEmpty B → ∀ y : P B, y = 0)
    (φ : CobarHom R C P) :
    TwCompareData ε (FreeGrL.aug R (CobarGen R C)) (DGOperad.toDer (R := R) (P := P)) (d R C)
      φ.1 (twOf φ.1) (ι R C) where
  hD _ _ _ x := DGOperad.d_d x
  hD' _ _ _ x := d_d R C x
  hg A _ _ x := φ.2 A x
  hβ := isPar_twOf φ.1
  hβ' := isPar_ι R C
  hβ1 A _ _ hA x := killsUnit_twOf φ.1 A x (hred A hA.le x)
  hβ1' A _ _ hA x := ιL_unitSpan R C (hred A hA.le x)
  nat _ _ _ w := map₂_twD ε (FreeGrL.aug R (CobarGen R C)) φ.1 (isPar_ι R C) w
  dd _ _ _ w := twDiff_sq ε _ (fun _ _ _ x => DGOperad.d_d x) (isPar_twOf φ.1)
    ((mc_iff φ.1).2 fun A _ _ _ => (φ.2 A _).symm) w
  dd' _ _ _ w := twDiff_sq _ (d R C) (fun _ _ _ x => d_d R C x) (isPar_ι R C) (ι_mc R C) w
  hP0 := hP0
  hP0' _ _ _ hB y := FreeGrL.eq_zero_of_isEmpty (gen_eq_zero hred) hB y

include hred in
/-- **The fundamental theorem of twisting morphisms**: for a reduced cooperad `C` and a dg operad
`P` without operations with no inputs, over a field of characteristic zero, a morphism of dg
operads `f : ΩC → P` is a quasi-isomorphism iff `1 ∘ f : C ∘_ι ΩC → C ∘_α P` is one, `α = f ∘ ι`
being its twisting morphism. -/
theorem fundamental
    (hP0 : ∀ (B : Type) [Fintype B] [DecidableEq B], IsEmpty B → ∀ y : P B, y = 0)
    (φ : CobarHom R C P) :
    (∀ (A : Type) [Fintype A] [DecidableEq A],
      FreeGrL.SurjAt R (d R C).toSpEnd (DGOperad.toDer (R := R) (P := P)).toSpEnd
          φ.1.toGrSpeciesHom A
        ∧ FreeGrL.InjAt R (d R C).toSpEnd (DGOperad.toDer (R := R) (P := P)).toSpEnd
          φ.1.toGrSpeciesHom A)
      ↔ ∀ (S : Type) [Fintype S] [DecidableEq S],
        QIso.Surj ⊤ ⊤ (twDiff R C (FreeGrL.aug R (CobarGen R C)) (d R C) (ι R C) S)
            (twDiff R C ε (DGOperad.toDer (R := R) (P := P)) (twOf φ.1) S)
            ((map₂ idSpHom φ.1.toGrSpeciesHom).app S)
          ∧ QIso.Inj ⊤ ⊤ (twDiff R C (FreeGrL.aug R (CobarGen R C)) (d R C) (ι R C) S)
            (twDiff R C ε (DGOperad.toDer (R := R) (P := P)) (twOf φ.1) S)
            ((map₂ idSpHom φ.1.toGrSpeciesHom).app S) :=
  ⟨fun h _ _ _ => (compareData ε hred hP0 φ).qiso (fun A _ _ _ => (h A).1)
      (fun A _ _ _ => (h A).2),
    fun h A _ _ => (compareData ε hred hP0 φ).qiso_converse hred h A⟩

end Cobar

end Operad
