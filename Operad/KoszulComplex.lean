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

/-- A multiple of a unit vanishes only if the multiple of the unit does. -/
lemma smul_map_one_eq_zero {R : Type u} [CommRing R]
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P] {A : Type}
    [Fintype A] [DecidableEq A] (e : Unit ≃ A) {a : R}
    (h : a • GrOperad.map (R := R) e (GrOperad.one (R := R) (P := P)) = 0) :
    a • GrOperad.one (R := R) (P := P) = 0 := by
  have h3 := congrArg (GrOperad.map (R := R) e.symm) h
  rwa [map_smul, ← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl, map_zero] at h3

section Units

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {A : Type} [Fintype A] [DecidableEq A]

/-- A derivation kills the multiples of the units. -/
lemma GrDer.app_smul_map_one {f : GrOperadHom R P Q} {q : Bool} (D : GrDer f q) (e : Unit ≃ A)
    (c : R) : D.app A (c • GrOperad.map (R := R) e (GrOperad.one (R := R) (P := P))) = 0 := by
  rw [map_smul, D.app_map, D.app_one, map_zero, smul_zero]

/-- A morphism of graded operads preserves the multiples of the units. -/
lemma GrOperadHom.app_smul_map_one (φ : GrOperadHom R P Q) (e : Unit ≃ A) (c : R) :
    φ.app A (c • GrOperad.map (R := R) e (GrOperad.one (R := R) (P := P)))
      = c • GrOperad.map (R := R) e (GrOperad.one (R := R) (P := Q)) := by
  rw [map_smul, φ.app_map, φ.app_one]

end Units

/-! ## Composites without inputs -/

namespace GrComposite

variable {R : Type u} [CommRing R]
  {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [GrSpecies R M]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrSpecies R N]
  {S : Type} [Fintype S] [DecidableEq S]

/-- **There are no composites without inputs**, without operations with no inputs. -/
lemma eq_zero_of_isEmpty
    (hM0 : ∀ (B : Type) [Fintype B] [DecidableEq B], IsEmpty B → ∀ x : M B, x = 0)
    (hN0 : ∀ (B : Type) [Fintype B] [DecidableEq B], IsEmpty B → ∀ y : N B, y = 0)
    (hS : IsEmpty S) (w : GrComposite R M N S) : w = 0 := by
  induction w using induction_on with
  | h0 => rfl
  | hadd x y hx hy => rw [hx, hy, add_zero]
  | hsmul c x hx => rw [hx, smul_zero]
  | hmk g =>
    by_cases hA : IsEmpty g.A
    · have h := mk_zero_m (R := R) g
      rwa [show ({ g with m := (0 : M g.A) } : GrCompGen M N S) = g by
        rw [← hM0 _ hA g.m]] at h
    · obtain ⟨a⟩ := not_isEmpty_iff.1 hA
      exact mk_of_y_eq_zero g (hN0 _ ⟨fun b => hS.elim (g.e ⟨a, b⟩)⟩ (g.y a))

end GrComposite

/-! ## Free graded operads in the arities at most one -/

namespace FreeGrL

section QIso

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {dV : GrSpEnd R V true} {dW : GrSpEnd R W true} {f : GrSpeciesHom R V W}
  {A : Type} [Fintype A] [DecidableEq A]

lemma surjAt_iff_surj : SurjAt R dV dW f A ↔ QIso.Surj ⊤ ⊤ (dV.app A) (dW.app A) (f.app A) :=
  ⟨fun h y _ hy => let ⟨x, hx, w, hw⟩ := h y hy
      ⟨x, Submodule.mem_top, hx, w, Submodule.mem_top, hw⟩,
    fun h y hy => let ⟨x, _, hx, w, _, hw⟩ := h y Submodule.mem_top hy; ⟨x, hx, w, hw⟩⟩

lemma injAt_iff_inj : InjAt R dV dW f A ↔ QIso.Inj ⊤ ⊤ (dV.app A) (dW.app A) (f.app A) :=
  ⟨fun h x _ hx w _ hw => let ⟨z, hz⟩ := h x hx w hw; ⟨z, Submodule.mem_top, hz⟩,
    fun h x hx w hw => let ⟨z, _, hz⟩ := h x Submodule.mem_top hx w Submodule.mem_top hw
      ⟨z, hz⟩⟩

end QIso

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

/-! ## The Koszul complex -/

namespace Koszul

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))}
  (hEred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : E B, v = 0)
  (hone : ∀ a : R, a • GrOperad.one (R := R) (P := Pres R E r) = 0 → a = 0)

include hEred in
/-- The presented operad has no operations without inputs. -/
lemma pres_eq_zero_of_isEmpty {B : Type} [Fintype B] [DecidableEq B] (hB : IsEmpty B)
    (y : Pres R E r B) : y = 0 := by
  obtain ⟨z, rfl⟩ := (GrOperadIdeal.span R r).proj_surjective B y
  rw [FreeGrL.eq_zero_of_isEmpty hEred hB z, map_zero]

include hEred in
/-- The operations of the presented operad with one input are the multiples of the unit. -/
lemma pres_eq_smul_one {A : Type} [Fintype A] [DecidableEq A] (e : Unit ≃ A)
    (y : Pres R E r A) :
    ∃ c : R, y = c • GrOperad.map (R := R) e (GrOperad.one (R := R) (P := Pres R E r)) := by
  obtain ⟨z, rfl⟩ := (GrOperadIdeal.span R r).proj_surjective A y
  obtain ⟨c, rfl⟩ := FreeGrL.eq_smul_one hEred e z
  exact ⟨c, by rw [map_smul]; rfl⟩

include hEred hone in
/-- **The relators have no unit component**, the unit of the presented operad being free. -/
lemma aug_relator {n : ℕ} {x : FreeGrL R E (Fin n)} (hx : x ∈ r n) :
    (FreeGrL.aug R E).u _ x = 0 := by
  by_cases h : IsEmpty (Unit ≃ Fin n)
  · exact (FreeGrL.aug R E).u_eq_zero h x
  · obtain ⟨e⟩ := not_isEmpty_iff.1 h
    obtain ⟨c, rfl⟩ := FreeGrL.eq_smul_one hEred e x
    have h0 := ((GrOperadIdeal.span R r).proj_eq_zero_iff _).2 (GrOperadIdeal.subset_span n hx)
    rw [map_smul] at h0
    rw [hone c (smul_map_one_eq_zero (P := Pres R E r) e h0), zero_smul, map_zero]

include hEred hone in
/-- **The augmentation of the presented operad**, the coefficient of the unit, for a free
unit. -/
noncomputable def presAug : GrAug R (ZeroDG R (Pres R E r)) :=
  ((FreeGrL.aug R E).quot (GrOperadIdeal.span R r) fun A _ _ =>
    (GrOperadIdeal.span_le (I := (FreeGrL.aug R E).ker)).2
      (fun _ _ hx => LinearMap.mem_ker.2 (aug_relator hEred hone hx)) A).toZeroDG

omit [CharZero R] in
/-- The twisting morphism of `ΩP^¡ → P` is the Koszul twisting morphism. -/
lemma twOf_cobarMor : Cobar.twOf (cobarMor R E r).1 = kappa R E r :=
  Cobar.twOf_homOf _ _ _

omit [CharZero R] in
/-- **Koszulness, arity by arity.** -/
lemma isKoszul_iff_at : IsKoszul R E r ↔ ∀ (A : Type) [Fintype A] [DecidableEq A],
    FreeGrL.SurjAt R (Cobar.d R (Dual R E r)).toSpEnd
        (DGOperad.toDer (R := R) (P := ZeroDG R (Pres R E r))).toSpEnd
        (cobarMor R E r).1.toGrSpeciesHom A
      ∧ FreeGrL.InjAt R (Cobar.d R (Dual R E r)).toSpEnd
        (DGOperad.toDer (R := R) (P := ZeroDG R (Pres R E r))).toSpEnd
        (cobarMor R E r).1.toGrSpeciesHom A :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    (QIso.bijective_iff _ _).trans
      ⟨fun h => ⟨FreeGrL.surjAt_iff_surj.2 h.1, FreeGrL.injAt_iff_inj.2 h.2⟩,
        fun h => ⟨FreeGrL.surjAt_iff_surj.1 h.1, FreeGrL.injAt_iff_inj.1 h.2⟩⟩

include hEred hone in
/-- **`ΩP^¡ → P` is a quasi-isomorphism in the arities at most one.** -/
lemma qiso_le_one {A : Type} [Fintype A] [DecidableEq A] (hA : Fintype.card A ≤ 1) :
    FreeGrL.SurjAt R (Cobar.d R (Dual R E r)).toSpEnd
        (DGOperad.toDer (R := R) (P := ZeroDG R (Pres R E r))).toSpEnd
        (cobarMor R E r).1.toGrSpeciesHom A
      ∧ FreeGrL.InjAt R (Cobar.d R (Dual R E r)).toSpEnd
        (DGOperad.toDer (R := R) (P := ZeroDG R (Pres R E r))).toSpEnd
        (cobarMor R E r).1.toGrSpeciesHom A := by
  have hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ x : Dual R E r B, x ∈ GrCooperad.unitSpan R (Dual R E r) B :=
    fun B _ _ hB x => dual_mem_unitSpan hEred hB x
  by_cases h0 : Fintype.card A = 0
  · have hA' : IsEmpty A := Fintype.card_eq_zero_iff.1 h0
    refine ⟨fun y _ => ⟨0, map_zero _, 0, ?_⟩, fun x _ _ _ => ⟨0, ?_⟩⟩
    · rw [pres_eq_zero_of_isEmpty hEred hA' y, map_zero, map_zero]
      exact sub_self _
    · exact (map_zero _).trans (FreeGrL.eq_zero_of_isEmpty (Cobar.gen_eq_zero hred) hA' x).symm
  · have e : Unit ≃ A := Fintype.equivOfCardEq (by rw [Fintype.card_unit]; omega)
    refine ⟨fun y _ => ?_, fun x _ w hw => ?_⟩
    · refine (pres_eq_smul_one hEred e y).elim fun c hc =>
        ⟨c • GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R (Dual R E r))), ?_,
          0, ?_⟩
      · exact GrDer.app_smul_map_one (Cobar.d R (Dual R E r)) e c
      · show (cobarMor R E r).1.app A _ - y = DGOperad.d (R := R) (P := ZeroDG R (Pres R E r)) 0
        rw [GrOperadHom.app_smul_map_one, map_zero, hc]
        exact sub_self _
    · refine (FreeGrL.eq_smul_one (Cobar.gen_eq_zero hred) e x).elim fun c hc => ⟨0, ?_⟩
      have hw' : (cobarMor R E r).1.app A (c • GrOperad.map (R := R) e
          (GrOperad.one (R := R) (P := CobarGr R (Dual R E r)))) = 0 :=
        (congrArg ((cobarMor R E r).1.app A) hc).symm.trans hw
      rw [GrOperadHom.app_smul_map_one] at hw'
      have hc0 : c = 0 := hone c (smul_map_one_eq_zero (P := Pres R E r) e hw')
      exact (map_zero _).trans (hc.trans (by rw [hc0, zero_smul])).symm

include hEred hone in
/-- **The Koszul complex criterion.** Over a field of characteristic zero, for quadratic data
without generators with at most one input presenting `P` with a free unit: **`P` is Koszul iff
the Koszul complex `P^¡ ∘_κ P` is acyclic in the arities at least two.** -/
theorem isKoszul_iff_acyclic :
    IsKoszul R E r ↔ ∀ (S : Type) [Fintype S] [DecidableEq S], 2 ≤ Fintype.card S →
      ∀ w : GrComposite R (Dual R E r) (ZeroDG R (Pres R E r)) S,
        twDiff R (Dual R E r) (presAug hEred hone)
            (DGOperad.toDer (R := R) (P := ZeroDG R (Pres R E r))) (kappa R E r) S w = 0 →
          ∃ v, twDiff R (Dual R E r) (presAug hEred hone)
            (DGOperad.toDer (R := R) (P := ZeroDG R (Pres R E r))) (kappa R E r) S v = w := by
  have hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ x : Dual R E r B, x ∈ GrCooperad.unitSpan R (Dual R E r) B :=
    fun B _ _ hB x => dual_mem_unitSpan hEred hB x
  have hP0 : ∀ (B : Type) [Fintype B] [DecidableEq B], IsEmpty B →
      ∀ y : ZeroDG R (Pres R E r) B, y = 0 :=
    fun B _ _ hB y => pres_eq_zero_of_isEmpty hEred hB y
  have hunit : ∀ (S : Type) [Fintype S] [DecidableEq S], 2 ≤ Fintype.card S →
      IsEmpty (Unit ≃ S) := fun S _ _ hS => ⟨fun e => by
    have := Fintype.card_congr e
    rw [Fintype.card_unit] at this
    omega⟩
  have hd := Cobar.compareData (presAug hEred hone) hred hP0 (cobarMor R E r)
  refine (isKoszul_iff_at.trans (Cobar.fundamental (presAug hEred hone) hred hP0
    (cobarMor R E r))).trans ?_
  simp only [twOf_cobarMor] at hd ⊢
  constructor
  · intro h S _ _ hS w hw
    refine ((h S).1 w Submodule.mem_top hw).elim fun x hx => hx.2.2.elim fun z hz => ?_
    have hx' := cobar_acyclic hred hx.2.1 ((FreeGrL.aug R _).u_eq_zero (hunit S hS) _)
    have hcomm := hd.nat S (cobarH R (Dual R E r) S x)
    have hleaf := hd.leaf_comm (cobarH R (Dual R E r) S x)
    have key : twDiff R (Dual R E r) (presAug hEred hone)
        (DGOperad.toDer (R := R) (P := ZeroDG R (Pres R E r))) (kappa R E r) S
        ((map₂ idSpHom (cobarMor R E r).1.toGrSpeciesHom).app S (cobarH R (Dual R E r) S x))
        = (map₂ idSpHom (cobarMor R E r).1.toGrSpeciesHom).app S x :=
      ((congrArg₂ (· + ·) hcomm.symm hleaf.symm).trans (map_add _ _ _).symm).trans
        (congrArg _ hx')
    refine ⟨(map₂ idSpHom (cobarMor R E r).1.toGrSpeciesHom).app S
      (cobarH R (Dual R E r) S x) - z, ?_⟩
    exact (map_sub _ _ _).trans ((congrArg (· - _) key).trans
      ((congrArg (_ - ·) hz.2.symm).trans (sub_sub_cancel _ _)))
  · intro h S _ _
    by_cases hS : 2 ≤ Fintype.card S
    · refine ⟨fun y _ hy => (h S hS y hy).elim fun v hv => ⟨0, Submodule.mem_top, map_zero _, -v,
        Submodule.mem_top, by rw [map_zero, map_neg, hv, zero_sub]⟩,
        fun x _ hx _ _ _ => ⟨cobarH R (Dual R E r) S x, Submodule.mem_top,
          cobar_acyclic hred hx ((FreeGrL.aug R _).u_eq_zero (hunit S hS) _)⟩⟩
    · exact hd.qiso (fun A _ _ hA => (qiso_le_one hEred hone (by omega)).1)
        (fun A _ _ hA => (qiso_le_one hEred hone (by omega)).2)

end Koszul

end Operad
