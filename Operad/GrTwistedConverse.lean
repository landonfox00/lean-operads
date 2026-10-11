/-
# The comparison lemma for twisted composite products, converse

For a reduced coaugmented graded cooperad `C`, the composites of `C ∘ P` with an outer operation
of one input are the elements `1 ⊗ z` (`GrComposite.eq_unitOf_of_mem`), recovered by the counit
of the outer cooperation (`GrComposite.counitE_unitOf`). They form a subcomplex isomorphic to `P`,
whose quotient involves `P` only in smaller arities: so **`g` is a quasi-isomorphism as soon as
`1 ∘ g : C ∘_β' P' → C ∘_β P` is one** (`GrComposite.TwCompareData.qiso_converse`), by induction
on the arity.
-/
import Operad.GrTwistedCompare
import Operad.GrTwistedCobar

universe u v w

namespace Operad

open Function Sym GerBV ConvOp

namespace GrComposite

/-! ## The unit and the counit -/

section UnitMaps

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {S : Type} [Fintype S] [DecidableEq S]

open GrCooperad

variable (R C P) in
/-- **The element `1 ⊗ z`.** -/
noncomputable def unitOf (B : Type) [Fintype B] [DecidableEq B] : P B →ₗ[R] GrComposite R C P B :=
  map (leftUnitEquiv B) ∘ₗ (actL R C ()).flip (corolla R P Unit (Coaug.one (R := R) (C := C)))

lemma unitOf_apply {B : Type} [Fintype B] [DecidableEq B] (z : P B) :
    unitOf R C P B z = map (leftUnitEquiv B)
      (act R C () z (corolla R P Unit (Coaug.one (R := R) (C := C)))) := rfl

lemma unitOf_comp {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] (i : A)
    (x : P A) (z : P Y) :
    unitOf R C P _ (GrOperad.comp (R := R) i x z) = act R C i z (unitOf R C P A x) := by
  set w := act R C () x (corolla R P Unit (Coaug.one (R := R) (C := C)))
  have h1 := map_act_seq (V := C) () i x z (corolla R P Unit (Coaug.one (R := R) (C := C)))
  have h2 := map_act (V := C) (leftUnitEquiv A) (Equiv.refl Y) (Sum.inr i) z w
  rw [GrOperad.map_refl] at h2
  rw [unitOf_apply, unitOf_apply, ← h1]
  refine Eq.trans ?_ h2
  rw [← map_trans]
  refine map_congr (fun s => ?_) _
  rcases s with ⟨u | a, hs⟩ | y
  · exact absurd (Subsingleton.elim u.1 ()) u.2
  · rfl
  · rfl

lemma unitOf_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : A ≃ B) (x : P A) :
    unitOf R C P B (GrOperad.map (R := R) σ x) = map σ (unitOf R C P A x) := by
  rw [unitOf_apply, unitOf_apply]
  have h := map_act (V := C) (Equiv.refl Unit) σ () x
    (corolla R P Unit (Coaug.one (R := R) (C := C)))
  rw [map_refl] at h
  erw [← h]
  simp only [← map_trans]
  exact map_congr (fun s => by rcases s with ⟨a, ha⟩ | y <;> first | rfl | exact absurd rfl ha) _

lemma unitOf_one : unitOf R C P Unit (GrOperad.one (R := R)) = corolla R P Unit
    (Coaug.one (R := R) (C := C)) := by
  rw [unitOf_apply]
  refine Eq.trans ?_ (map_act_one (V := C) () _)
  exact map_congr (fun s => by rcases s with ⟨a, ha⟩ | y <;> rfl) _

lemma unitOf_mem {B : Type} [Fintype B] [DecidableEq B] (z : P B) :
    unitOf R C P B z ∈ outerSpan R C P B 1 := by
  rw [unitOf_apply]
  exact relabel_mem_outerSpanP _ (act_mem_outerSpanP _ _ (corolla_mem_outerSpan _))

omit [GrCooperad.Coaug R C] in
variable (R C P) in
/-- **The counit**, as a morphism of linear species `C → P` into the units. -/
noncomputable def counitHom : SymSpeciesHom R C P where
  app A _ _ := ∑ e : Unit ≃ A, (LinearMap.smulRight (counit (R := R) (C := C))
    (GrOperad.map (R := R) (P := P) e (GrOperad.one (R := R)))).comp
      (SymSpecies.map (R := R) e.symm)
  app_map {A B} _ _ _ _ σ x := by
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
      LinearMap.smulRight_apply, map_sum, map_smul]
    refine Fintype.sum_equiv (Equiv.mk (fun e => e.trans σ.symm) (fun e => e.trans σ)
      (fun e => by ext; simp) (fun e => by ext; simp)) _ _ fun e => ?_
    show _ = _ • GrOperad.map (R := R) σ (GrOperad.map (R := R) (e.trans σ.symm) _)
    rw [← SymSpecies.map_trans, ← GrOperad.map_trans]
    congr 2
    congr 1
    ext u
    simp

omit [GrCooperad.Coaug R C] in
lemma counitHom_apply {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    (counitHom R C P).app A x = ∑ e : Unit ≃ A, counit (R := R) (SymSpecies.map (R := R) e.symm x)
      • GrOperad.map (R := R) (P := P) e (GrOperad.one (R := R)) := by
  simp [counitHom]

lemma counitHom_one :
    (counitHom R C P).app Unit (Coaug.one (R := R) (C := C)) = GrOperad.one (R := R) := by
  rw [counitHom_apply, Fintype.sum_unique]
  rw [show (default : Unit ≃ Unit) = Equiv.refl Unit from Subsingleton.elim _ _,
    Equiv.refl_symm, SymSpecies.map_refl, GrOperad.map_refl, Coaug.counit_one, one_smul]

variable (R C P) in
/-- **The counit of the outer cooperation**, leaving the inner operation. -/
noncomputable abbrev counitE (S : Type) [Fintype S] [DecidableEq S] :
    GrComposite R C P S →ₗ[R] P S :=
  total R (counitHom R C P)

omit [GrCooperad.Coaug R C] in
lemma counitE_act {Y : Type} [Fintype Y] [DecidableEq Y] (i : S) (z : P Y)
    (w : GrComposite R C P S) :
    counitE R C P _ (act R C i z w) = GrOperad.comp (R := R) i (counitE R C P S w) z :=
  total_act R C (counitHom R C P) i z w

omit [GrCooperad.Coaug R C] in
lemma counitE_map {S' : Type} [Fintype S'] [DecidableEq S'] (σ : S ≃ S')
    (w : GrComposite R C P S) :
    counitE R C P S' (map σ w) = GrOperad.map (R := R) σ (counitE R C P S w) :=
  total_map (counitHom R C P) σ w

omit [GrCooperad.Coaug R C] in
lemma counitE_corolla {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    counitE R C P A (corolla R P A c) = (counitHom R C P).app A c := by
  rw [corolla_apply, total_corGen, GrOperad.map_refl]

/-- **The counit recovers `z` from `1 ⊗ z`.** -/
lemma counitE_unitOf {B : Type} [Fintype B] [DecidableEq B] (z : P B) :
    counitE R C P B (unitOf R C P B z) = z := by
  rw [unitOf_apply, counitE_map, counitE_act, counitE_corolla, counitHom_one]
  exact GrOperad.one_comp z

/-- **For a reduced cooperad, the composites with an outer operation of one input are the
elements `1 ⊗ z`.** -/
theorem eq_unitOf_of_mem
    (hred : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A ≤ 1 →
      ∀ x : C A, x ∈ unitSpan R C A) {x : GrComposite R C P S}
    (hx : x ∈ outerSpan R C P S 1) : x = unitOf R C P S (counitE R C P S x) := by
  have h := map_mem_outerSpanP (LinearMap.id - (unitOf R C P S).comp (counitE R C P S))
    (⊥ : Submodule R (GrComposite R C P S)) (fun g hg => ?_) hx
  · rw [Submodule.mem_bot, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      sub_eq_zero] at h
    exact h
  · rw [Submodule.mem_bot, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      sub_eq_zero]
    exact induction_card (fun S _ _ w => w = unitOf R C P S (counitE R C P S w))
      (fun S _ _ => by beta_reduce; simp)
      (fun S _ _ x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, map_add, ← hx, ← hy])
      (fun S _ _ r x hx => by beta_reduce at hx ⊢; rw [map_smul, map_smul, ← hx])
      (fun S S' _ _ _ _ σ x hx => by
        beta_reduce at hx ⊢
        rw [counitE_map, unitOf_map, ← hx])
      (fun S Y _ _ _ _ i z x hx => by
        beta_reduce at hx ⊢
        rw [counitE_act, unitOf_comp, ← hx])
      (fun A _ _ c hA => by
        beta_reduce
        have e : Unit ≃ A := (Fintype.equivOfCardEq (by rw [Fintype.card_unit, hA]))
        haveI := subsingleton_of_unit e
        have hc := eq_counit_smul (hred A hA.le) e c
        rw [counitE_corolla, counitHom_apply, Fintype.sum_subsingleton _ e, map_smul,
          unitOf_map, unitOf_one, map_corolla]
        conv_lhs => rw [hc]
        rw [map_smul]) g hg

end UnitMaps

/-! ## More on the projections -/

section ProjMore

variable {R : Type u} [CommRing R]
  {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [GrSpecies R M]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrSpecies R N]
  {S : Type} [Fintype S] [DecidableEq S]

lemma outerProj_add (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ k, Q k ↔ ¬ P k) (x : GrComposite R M N S) :
    outerProj R M N S P x + outerProj R M N S Q x = x := by
  induction x using induction_on with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, add_add_add_comm, hx, hy]
  | hsmul c x hx => rw [map_smul, map_smul, ← smul_add, hx]
  | hmk g =>
    rw [outerProj_mk, outerProj_mk]
    by_cases hP : P (Fintype.card g.A)
    · rw [if_pos hP, if_neg ((h _).not.2 (not_not.2 hP)), add_zero]
    · rw [if_neg hP, if_pos ((h _).2 hP), zero_add]

lemma outerProj_mem_and (P Q : ℕ → Prop) [DecidablePred P] {x : GrComposite R M N S}
    (hx : x ∈ outerSpanP R M N S Q) :
    outerProj R M N S P x ∈ outerSpanP R M N S (fun k => P k ∧ Q k) :=
  map_mem_outerSpanP _ _ (fun g hg => by
    rw [outerProj_mk]
    split_ifs with hP
    · exact mk_mem_outerSpanP g ⟨hP, hg⟩
    · exact zero_mem _) hx

/-- Generators with more outer inputs than inputs vanish, without inner operations with no
inputs. -/
lemma mk_eq_zero_of_card_lt
    (hN0 : ∀ (B : Type) [Fintype B] [DecidableEq B], IsEmpty B → ∀ y : N B, y = 0)
    (g : GrCompGen M N S) (hg : Fintype.card S < Fintype.card g.A) : mk R g = 0 := by
  have hex : ∃ a, IsEmpty (g.B a) := by
    by_contra hne
    simp only [not_exists, not_isEmpty_iff] at hne
    have h1 : Fintype.card g.A ≤ Fintype.card S := by
      rw [← Fintype.card_congr g.e, Fintype.card_sigma]
      calc Fintype.card g.A = ∑ _a : g.A, 1 := by simp
        _ ≤ ∑ a, Fintype.card (g.B a) := Finset.sum_le_sum fun a _ =>
          Fintype.card_pos_iff.2 (hne a)
    omega
  obtain ⟨a, ha⟩ := hex
  exact mk_of_y_eq_zero g (hN0 _ ha (g.y a))


section Fib

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)] [DecidableEq S] in
/-- **A generator whose inner operations have fewer inputs than `n`**, or an empty one. -/
lemma card_fib_lt (g : GrCompGen M N S) (hg : 2 ≤ Fintype.card g.A) (a : g.A) :
    Fintype.card (g.B a) < Fintype.card S ∨ ∃ b, IsEmpty (g.B b) := by
  by_cases hne : ∃ b, IsEmpty (g.B b)
  · exact Or.inr hne
  · left
    simp only [not_exists, not_isEmpty_iff] at hne
    obtain ⟨a', ha'⟩ : ∃ a', a' ≠ a := by
      by_contra h
      simp only [not_exists, not_not] at h
      have : Fintype.card g.A ≤ 1 := Fintype.card_le_one_iff.2 fun x y => (h x).trans (h y).symm
      omega
    rw [← Fintype.card_congr g.e, Fintype.card_sigma,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    have : 0 < ∑ b ∈ Finset.univ.erase a, Fintype.card (g.B b) :=
      Finset.sum_pos' (fun b _ => Nat.zero_le _)
        ⟨a', Finset.mem_erase.2 ⟨ha', Finset.mem_univ _⟩, Fintype.card_pos_iff.2 (hne a')⟩
    omega

end Fib

end ProjMore

/-! ## Splitting off the outer operations of at least two inputs -/

section SplitUW

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (ε : GrAug R P) (D : GrDer (GrOperadHom.id R P) true) {β : GrOperad.Inv R (ConvOp R C P)}
  (hβ : GrOperad.Inv.IsPar true β)
  (hβ1 : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = 1 →
    ∀ x : C A, toLin (β.1 A) x = 0)
  (S : Type) [Fintype S] [DecidableEq S]

variable (R C P) in
/-- The projection onto the outer operations of at least two inputs. -/
noncomputable abbrev projU : GrComposite R C P S →ₗ[R] GrComposite R C P S :=
  outerProj R C P S (2 ≤ ·)

variable (R C P) in
/-- The projection onto the outer operations of at most one input. -/
noncomputable abbrev projW : GrComposite R C P S →ₗ[R] GrComposite R C P S :=
  outerProj R C P S (· < 2)

omit [Algebra ℚ R] in
lemma projU_add_projW (x : GrComposite R C P S) : projU R C P S x + projW R C P S x = x :=
  outerProj_add _ _ (fun k => by omega) x

variable (β) in
/-- The part of the differential preserving the outer operations of at least two inputs. -/
noncomputable abbrev diffU : GrComposite R C P S →ₗ[R] GrComposite R C P S :=
  leafD R C D S + (projU R C P S).comp (twD ε β S)

variable (β) in
/-- The part of the differential from the outer operations of at least two inputs to the others.
-/
noncomputable abbrev diffW : GrComposite R C P S →ₗ[R] GrComposite R C P S :=
  (projW R C P S).comp (twD ε β S)

omit [Algebra ℚ R] in
lemma diffU_add_diffW : diffU ε D β S + diffW ε β S = twDiff R C ε D β S := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, twDiff]
  rw [add_assoc, projU_add_projW, add_comm]

omit [Algebra ℚ R] in
include hβ hβ1 in
lemma twD_projW_mem (x : GrComposite R C P S) : twD ε β S (projW R C P S x) ∈ outerLt R C P S 2 :=
  twD_mem_outerLt_of_lt ε hβ hβ1 (outerProj_mem _ x)

omit [Algebra ℚ R] in
include hβ hβ1 in
lemma projU_twD_projW (x : GrComposite R C P S) :
    projU R C P S (twD ε β S (projW R C P S x)) = 0 :=
  outerProj_eq_zero _ (· < 2) (fun k hk => by omega) (twD_projW_mem ε hβ hβ1 S x)

omit [Algebra ℚ R] in
include hβ hβ1 in
/-- **The split extension** of the outer operations of at least two inputs by the others. -/
lemma splitUW (hdd : ∀ x, twDiff R C ε D β S (twDiff R C ε D β S x) = 0) :
    QIso.Split (diffU ε D β S) (diffW ε β S) (outerSpanP R C P S (2 ≤ ·)) (outerLt R C P S 2) where
  disj := Submodule.disjoint_def.2 fun x hU hW => by
    rw [← outerProj_of_mem (2 ≤ ·) hU]
    exact outerProj_eq_zero _ (· < 2) (fun k hk => by omega) hW
  dd x := by rw [diffU_add_diffW]; exact hdd x
  mem₀ u hu := by
    rw [LinearMap.add_apply]
    exact add_mem (leafMap_mem_outerSpanP _ hu) (outerProj_mem _ _)
  mem₁ u _ := outerProj_mem _ _
  memW w hw := by
    rw [diffU_add_diffW, twDiff, LinearMap.add_apply]
    exact add_mem (twD_mem_outerLt_of_lt ε hβ hβ1 hw) (leafMap_mem_outerSpanP _ hw)

omit [Algebra ℚ R] in
include hβ hβ1 in
/-- `diffU` squares to zero. -/
lemma diffU_sq (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), D.app A (D.app A x) = 0)
    (hdd : ∀ x, twDiff R C ε D β S (twDiff R C ε D β S x) = 0) (x : GrComposite R C P S) :
    diffU ε D β S (diffU ε D β S x) = 0 := by
  have h1 := hdd x
  simp only [twDiff, LinearMap.add_apply, map_add] at h1
  have h1' := congrArg (projU R C P S) h1
  simp only [map_add, map_zero] at h1'
  have h2 := leaf_sq D hD x
  have h2' : projU R C P S (leafD R C D S (leafD R C D S x)) = 0 := by rw [h2, map_zero]
  have h3 := projU_twD_projW ε hβ hβ1 S (twD ε β S x)
  have h4 := projU_add_projW S (twD ε β S x)
  have h5 : twD ε β S (projU R C P S (twD ε β S x))
      = twD ε β S (twD ε β S x) - twD ε β S (projW R C P S (twD ε β S x)) := by
    rw [eq_sub_of_add_eq h4, map_sub]
  have h6 := outerProj_leafMap (2 ≤ ·) (D.toSpEnd) (twD ε β S x)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
  rw [h5, map_sub, h3, sub_zero, h2]
  erw [← h6]
  linear_combination (norm := module) h1' - h2'

end SplitUW

/-! ## The converse -/

section Converse

variable {R : Type u} [Field R] [CharZero R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [GrOperad R P']
  {ε : GrAug R P} {ε' : GrAug R P'}
  {D : GrDer (GrOperadHom.id R P) true} {D' : GrDer (GrOperadHom.id R P') true}
  {g : GrOperadHom R P' P}
  {β : GrOperad.Inv R (ConvOp R C P)} {β' : GrOperad.Inv R (ConvOp R C P')}

open GrCooperad

omit [CharZero R] in
lemma leafD_unitOf (D : GrDer (GrOperadHom.id R P) true) {B : Type} [Fintype B] [DecidableEq B]
    (z : P B) : leafD R C D B (unitOf R C P B z) = unitOf R C P B (D.app B z) := by
  rw [unitOf_apply, unitOf_apply, ← leafMap_map, leafD_act, leafD_corolla, map_zero, zero_add,
    tw_corolla, GrSpecies.tw_hom true (Coaug.par_one (R := R) (C := C)), Bool.and_false, σ_false,
    one_smul]

omit [CharZero R] in
lemma twD_unitOf (ε : GrAug R P) {β : GrOperad.Inv R (ConvOp R C P)} {p : Bool}
    (hβ : GrOperad.Inv.IsPar p β)
    (hβ1 : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = 1 →
      ∀ x : C A, toLin (β.1 A) x = 0)
    {B : Type} [Fintype B] [DecidableEq B] (z : P B) : twD ε β B (unitOf R C P B z) = 0 := by
  have h := twD_corolla_mem ε hβ hβ1 (Coaug.one (R := R) (C := C))
  rw [Fintype.card_unit, outerLt_one_eq_bot ⟨()⟩, Submodule.mem_bot] at h
  rw [unitOf_apply, twD, twF_map, twF_act]
  erw [h]
  rw [map_zero, map_zero]

omit [CharZero R] [GrCooperad.Coaug R C] in
lemma map₂_unitOf [GrCooperad.Coaug R C] (g : GrOperadHom R P' P) {B : Type} [Fintype B]
    [DecidableEq B] (z : P' B) :
    (map₂ idSpHom g.toGrSpeciesHom).app B (unitOf R C P' B z) = unitOf R C P B (g.app B z) := by
  rw [unitOf_apply, unitOf_apply, show (map₂ idSpHom g.toGrSpeciesHom).app B (map _ _)
    = map _ ((map₂ idSpHom g.toGrSpeciesHom).app _ _) from
      (map₂ idSpHom g.toGrSpeciesHom).app_map _ _, map₂_act, map₂_corolla]

omit [CharZero R] in
lemma twDiff_unitOf (ε : GrAug R P) (D : GrDer (GrOperadHom.id R P) true)
    {β : GrOperad.Inv R (ConvOp R C P)} {p : Bool} (hβ : GrOperad.Inv.IsPar p β)
    (hβ1 : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = 1 →
      ∀ x : C A, toLin (β.1 A) x = 0)
    {B : Type} [Fintype B] [DecidableEq B] (z : P B) :
    twDiff R C ε D β B (unitOf R C P B z) = unitOf R C P B (D.app B z) := by
  rw [twDiff, LinearMap.add_apply, twD_unitOf ε hβ hβ1, zero_add, leafD_unitOf]

variable (hd : TwCompareData ε ε' D D' g β β') {S : Type} [Fintype S] [DecidableEq S]

/-- The graded pieces of the filtration of the outer operations of at least two inputs. -/
noncomputable def filtXU (P₀ : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P₀ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P₀ A)] [GrOperad R P₀]
    (S : Type) [Fintype S] [DecidableEq S] (p : ℕ) : Submodule R (GrComposite R C P₀ S) :=
  if p + 2 ≤ Fintype.card S then outerSpan R C P₀ S (Fintype.card S - p) else ⊥

/-- The filtration of the outer operations of at least two inputs. -/
noncomputable abbrev filtSU (P₀ : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P₀ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P₀ A)] [GrOperad R P₀]
    (S : Type) [Fintype S] [DecidableEq S] (p : ℕ) : Submodule R (GrComposite R C P₀ S) :=
  outerSpanP R C P₀ S (fun k => 2 ≤ k ∧ k < Fintype.card S + 1 - p)

omit [CharZero R] [GrCooperad.Coaug R C] in
lemma filtSU_sup (P₀ : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P₀ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P₀ A)] [GrOperad R P₀] (p : ℕ) :
    filtSU (R := R) (C := C) P₀ S p = filtXU (R := R) (C := C) P₀ S p ⊔ filtSU (R := R) (C := C) P₀ S (p + 1) := by
  unfold filtXU
  split_ifs with hp
  · refine le_antisymm ?_ (sup_le (outerSpanP_mono fun k hk => by omega)
      (outerSpanP_mono fun k hk => by omega))
    apply Submodule.span_le.2
    rintro _ ⟨g, ⟨h1, h2⟩, rfl⟩
    by_cases hk : Fintype.card g.A = Fintype.card S - p
    · exact Submodule.mem_sup_left (mk_mem_outerSpanP g hk)
    · exact Submodule.mem_sup_right (mk_mem_outerSpanP g ⟨h1, by omega⟩)
  · rw [bot_sup_eq]
    refine le_antisymm ?_ (outerSpanP_mono fun k hk => by omega)
    apply Submodule.span_le.2
    rintro _ ⟨g, ⟨h1, h2⟩, rfl⟩
    exact absurd h2 (by omega)

include hd in
omit [GrCooperad.Coaug R C] in
lemma TwCompareData.filtDataU :
    QIso.FiltData (filtXU P' S) (filtSU P' S) (filtXU P S) (filtSU P S) (Fintype.card S)
      (leafD R C D' S) ((projU R C P' S).comp (twD ε' β' S)) (leafD R C D S)
      ((projU R C P S).comp (twD ε β S)) ((map₂ idSpHom g.toGrSpeciesHom).app S) where
  split p := by
    refine ⟨?_, fun x => diffU_sq ε' D' hd.hβ' hd.hβ1' S hd.hD' (hd.dd' S) x, fun u hu => ?_,
      fun u hu => ?_, fun w hw => ?_⟩
    · unfold filtXU
      split_ifs with hp
      · exact (disjoint_outerSpan_outerLt _).mono_right (outerSpanP_mono fun k hk => by omega)
      · exact disjoint_bot_left
    · unfold filtXU at hu ⊢
      split_ifs at hu ⊢ with hp
      · exact leafMap_mem_outerSpanP _ hu
      · rw [Submodule.mem_bot] at hu ⊢
        rw [hu, map_zero]
    · unfold filtXU at hu
      split_ifs at hu with hp
      · exact outerSpanP_mono (P := fun k => 2 ≤ k ∧ k < Fintype.card S - p)
          (fun k hk => ⟨hk.1, by omega⟩)
          (outerProj_mem_and _ _ (twD_mem_outerLt ε' hd.hβ' hd.hβ1' hu))
      · rw [Submodule.mem_bot] at hu
        rw [hu, map_zero]
        exact zero_mem _
    · rw [LinearMap.add_apply]
      refine add_mem (leafMap_mem_outerSpanP _ hw) ?_
      exact outerSpanP_mono (P := fun k => 2 ≤ k ∧ k < Fintype.card S - p)
        (fun k hk => ⟨hk.1, by omega⟩)
        (outerProj_mem_and _ _ (twD_mem_outerLt_of_lt ε' hd.hβ' hd.hβ1'
          (outerSpanP_mono (P' := (· < Fintype.card S - p)) (fun k hk => by omega) hw)))
  split' p := by
    refine ⟨?_, fun x => diffU_sq ε D hd.hβ hd.hβ1 S hd.hD (hd.dd S) x, fun u hu => ?_,
      fun u hu => ?_, fun w hw => ?_⟩
    · unfold filtXU
      split_ifs with hp
      · exact (disjoint_outerSpan_outerLt _).mono_right (outerSpanP_mono fun k hk => by omega)
      · exact disjoint_bot_left
    · unfold filtXU at hu ⊢
      split_ifs at hu ⊢ with hp
      · exact leafMap_mem_outerSpanP _ hu
      · rw [Submodule.mem_bot] at hu ⊢
        rw [hu, map_zero]
    · unfold filtXU at hu
      split_ifs at hu with hp
      · exact outerSpanP_mono (P := fun k => 2 ≤ k ∧ k < Fintype.card S - p)
          (fun k hk => ⟨hk.1, by omega⟩)
          (outerProj_mem_and _ _ (twD_mem_outerLt ε hd.hβ hd.hβ1 hu))
      · rw [Submodule.mem_bot] at hu
        rw [hu, map_zero]
        exact zero_mem _
    · rw [LinearMap.add_apply]
      refine add_mem (leafMap_mem_outerSpanP _ hw) ?_
      exact outerSpanP_mono (P := fun k => 2 ≤ k ∧ k < Fintype.card S - p)
        (fun k hk => ⟨hk.1, by omega⟩)
        (outerProj_mem_and _ _ (twD_mem_outerLt_of_lt ε hd.hβ hd.hβ1
          (outerSpanP_mono (P' := (· < Fintype.card S - p)) (fun k hk => by omega) hw)))
  hom p := by
    refine ⟨fun u hu => ?_, fun w hw => map₂_mem_outerSpanP _ hw, fun x => hd.leaf_comm x,
      fun x => ?_⟩
    · unfold filtXU at hu ⊢
      split_ifs at hu ⊢ with hp
      · exact map₂_mem_outerSpanP _ hu
      · rw [Submodule.mem_bot] at hu ⊢
        rw [hu, map_zero]
    · simp only [LinearMap.comp_apply]
      rw [← outerProj_map₂, hd.nat]
  sup p := filtSU_sup P' p
  sup' p := filtSU_sup P p
  top := eq_bot_iff.2 (Submodule.span_le.2 fun _ ⟨_, ⟨h1, h2⟩, _⟩ => absurd h2 (by omega))
  top' := eq_bot_iff.2 (Submodule.span_le.2 fun _ ⟨_, ⟨h1, h2⟩, _⟩ => absurd h2 (by omega))

omit [CharZero R] [GrCooperad.Coaug R C] in
lemma filtSU_zero (P₀ : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P₀ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P₀ A)] [GrOperad R P₀]
    (hP0 : ∀ (B : Type) [Fintype B] [DecidableEq B], IsEmpty B → ∀ y : P₀ B, y = 0) :
    filtSU (R := R) (C := C) P₀ S 0 = outerSpanP R C P₀ S (2 ≤ ·) := by
  refine le_antisymm (outerSpanP_mono fun k hk => hk.1) ?_
  apply Submodule.span_le.2
  rintro _ ⟨g, hg, rfl⟩
  by_cases hk : Fintype.card g.A < Fintype.card S + 1
  · exact mk_mem_outerSpanP g ⟨hg, by omega⟩
  · rw [mk_eq_zero_of_card_lt hP0 g (by omega)]
    exact zero_mem _

omit [CharZero R] [GrCooperad.Coaug R C] in
/-- **Morphisms agreeing in the arities less than `|S|` agree on the composites with an outer
operation of at least two inputs.** -/
lemma map₂_eq_on_outerSpan {N N' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrSpecies R N]
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N' A)] [GrSpecies R N']
    (ψ₁ ψ₂ : GrSpeciesHom R N N')
    (hN0 : ∀ (B : Type) [Fintype B] [DecidableEq B], IsEmpty B → ∀ y : N B, y = 0)
    (h : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B < Fintype.card S →
      ∀ y : N B, ψ₁.app B y = ψ₂.app B y)
    {j : ℕ} (hj : 2 ≤ j) {x : GrComposite R C N S} (hx : x ∈ outerSpan R C N S j) :
    (map₂ idSpHom ψ₁).app S x = (map₂ idSpHom ψ₂).app S x := by
  have h' := map_mem_outerSpanP ((map₂ idSpHom ψ₁).app S - (map₂ idSpHom ψ₂).app S)
    (⊥ : Submodule R (GrComposite R C N' S)) (fun g hg => ?_) hx
  · rwa [Submodule.mem_bot, LinearMap.sub_apply, sub_eq_zero] at h'
  · rw [Submodule.mem_bot, LinearMap.sub_apply, sub_eq_zero]
    by_cases hex : ∃ b, IsEmpty (g.B b)
    · obtain ⟨b, hb⟩ := hex
      rw [mk_of_y_eq_zero g (hN0 _ hb (g.y b)), map_zero, map_zero]
    · have hlt : ∀ a, Fintype.card (g.B a) < Fintype.card S := fun a =>
        (card_fib_lt g (hg ▸ hj) a).resolve_right hex
      rw [map₂_mk, map₂_mk]
      show mk R ⟨g.A, g.B, g.L, g.m, fun a => ψ₁.app _ (g.y a), g.e⟩
        = mk R ⟨g.A, g.B, g.L, g.m, fun a => ψ₂.app _ (g.y a), g.e⟩
      simp only [fun a => h _ (hlt a) (g.y a)]

include hd in
/-- **The inductive step of the converse**: in an arity `S`, if `g` is a quasi-isomorphism in
the arities less than `|S|` and `1 ∘ g` is one in arity `S`, then `g` is one in arity `S`. -/
theorem TwCompareData.qiso_step
    (hred : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A ≤ 1 →
      ∀ x : C A, x ∈ unitSpan R C A) (hS : Nonempty S)
    (hlow : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B < Fintype.card S →
      FreeGrL.SurjAt R D'.toSpEnd D.toSpEnd g.toGrSpeciesHom B
        ∧ FreeGrL.InjAt R D'.toSpEnd D.toSpEnd g.toGrSpeciesHom B)
    (hqS : QIso.Surj ⊤ ⊤ (twDiff R C ε' D' β' S) (twDiff R C ε D β S)
        ((map₂ idSpHom g.toGrSpeciesHom).app S)
      ∧ QIso.Inj ⊤ ⊤ (twDiff R C ε' D' β' S) (twDiff R C ε D β S)
        ((map₂ idSpHom g.toGrSpeciesHom).app S)) :
    FreeGrL.SurjAt R D'.toSpEnd D.toSpEnd g.toGrSpeciesHom S
      ∧ FreeGrL.InjAt R D'.toSpEnd D.toSpEnd g.toGrSpeciesHom S := by
  obtain ⟨s'⟩ := Splitting.exists_of_field D'.toSpEnd (fun A _ _ x => hd.hD' A x)
  obtain ⟨s⟩ := Splitting.exists_of_field D.toSpEnd (fun A _ _ x => hd.hD A x)
  obtain ⟨k, hk⟩ := exists_compat g.toGrSpeciesHom (fun A _ _ x => (hd.hg A x).symm) s' s
    (· < Fintype.card S) (fun m hm => (hlow (Fin m) (by simpa using hm)).1)
    (fun m hm => (hlow (Fin m) (by simpa using hm)).2)
  -- the outer operations of at least two inputs
  have hpiece : ∀ p, QIso.Surj (filtXU P' S p) (filtXU P S p) (leafD R C D' S) (leafD R C D S)
        ((map₂ idSpHom g.toGrSpeciesHom).app S)
      ∧ QIso.Inj (filtXU P' S p) (filtXU P S p) (leafD R C D' S) (leafD R C D S)
        ((map₂ idSpHom g.toGrSpeciesHom).app S) := fun p => by
    unfold filtXU
    split_ifs with hp
    · have hX := le_antisymm (outerSpanP_le_outerEig (R := R) (M := C) (N := P') (S := S)
        (Fintype.card S - p)) (outerEig_le_outerSpan _)
      have hX' := le_antisymm (outerSpanP_le_outerEig (R := R) (M := C) (N := P) (S := S)
        (Fintype.card S - p)) (outerEig_le_outerSpan _)
      rw [hX, hX']
      refine qiso_leaf s' s g.toGrSpeciesHom (fun A _ _ y => hd.hg A y) k _
        (fun x hx => ?_) (fun y hy => ?_)
      · rw [map₂_map₂ k (s.p.toHom.comp (g.toGrSpeciesHom.comp s'.p.toHom))
          (k.comp (s.p.toHom.comp (g.toGrSpeciesHom.comp s'.p.toHom))) (fun _ _ _ _ => rfl)]
        exact map₂_eq_on_outerSpan _ _ hd.hP0' (fun B _ _ hB y => (hk B hB).1 y) (by omega)
          (outerEig_le_outerSpan _ hx)
      · rw [map₂_map₂ (s.p.toHom.comp (g.toGrSpeciesHom.comp s'.p.toHom)) k
          ((s.p.toHom.comp (g.toGrSpeciesHom.comp s'.p.toHom)).comp k) (fun _ _ _ _ => rfl)]
        exact map₂_eq_on_outerSpan _ _ hd.hP0 (fun B _ _ hB y => (hk B hB).2 y) (by omega)
          (outerEig_le_outerSpan _ hy)
    · exact ⟨QIso.surj_bot _ _ _, QIso.inj_bot _ _ _⟩
  have hU := QIso.qiso_filt hd.filtDataU (fun p => (hpiece p).1) (fun p => (hpiece p).2) 0
  rw [filtSU_zero P' hd.hP0', filtSU_zero P hd.hP0] at hU
  -- the split extension
  have hs := splitUW ε' D' hd.hβ' hd.hβ1' S (hd.dd' S)
  have hs' := splitUW ε D hd.hβ hd.hβ1 S (hd.dd S)
  have hF : QIso.SplitHom ((map₂ idSpHom g.toGrSpeciesHom).app S) (diffU ε' D' β' S)
      (diffW ε' β' S) (diffU ε D β S) (diffW ε β S) (outerSpanP R C P' S (2 ≤ ·))
      (outerLt R C P' S 2) (outerSpanP R C P S (2 ≤ ·)) (outerLt R C P S 2) := by
    refine ⟨fun u hu => map₂_mem_outerSpanP _ hu, fun w hw => map₂_mem_outerSpanP _ hw,
      fun x => ?_, fun x => ?_⟩
    · simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
      rw [hd.leaf_comm, ← outerProj_map₂, hd.nat]
    · simp only [LinearMap.comp_apply]
      rw [← outerProj_map₂, hd.nat]
  have htop : ∀ (P₀ : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
      [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P₀ A)]
      [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P₀ A)] [GrOperad R P₀],
      outerSpanP R C P₀ S (2 ≤ ·) ⊔ outerLt R C P₀ S 2 = ⊤ := fun P₀ _ _ _ =>
    eq_top_iff.2 fun x _ => by
      rw [← projU_add_projW S x]
      exact Submodule.add_mem_sup (outerProj_mem _ x) (outerProj_mem _ x)
  have hT := hqS
  rw [← htop P', ← htop P, ← diffU_add_diffW, ← diffU_add_diffW] at hT
  have hWs := QIso.surj_sub hs hs' hF hU.1 hU.2 hT.1
  have hWi := QIso.inj_sub hs hs' hF hU.2 hT.1 hT.2
  rw [diffU_add_diffW, diffU_add_diffW] at hWs hWi
  -- the outer operations of one input
  have hW1 : ∀ (P₀ : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
      [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P₀ A)]
      [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P₀ A)] [GrOperad R P₀]
      {x : GrComposite R C P₀ S}, x ∈ outerLt R C P₀ S 2 → x ∈ outerSpan R C P₀ S 1 :=
    fun P₀ _ _ _ x hx => by
      rw [show (2 : ℕ) = 1 + 1 from rfl, outerLt_succ, outerLt_one_eq_bot hS, sup_bot_eq] at hx
      exact hx
  have hW2 : ∀ (P₀ : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
      [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P₀ A)]
      [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P₀ A)] [GrOperad R P₀] (z : P₀ S),
      unitOf R C P₀ S z ∈ outerLt R C P₀ S 2 := fun P₀ _ _ _ z =>
    outerSpanP_mono (fun k hk => by omega) (unitOf_mem z)
  constructor
  · intro y hy
    have hcy : twDiff R C ε D β S (unitOf R C P S y) = 0 := by
      rw [twDiff_unitOf ε D hd.hβ hd.hβ1]
      exact (congrArg (unitOf R C P S) hy).trans (map_zero _)
    obtain ⟨x, hx, hdx, z, hz, hxz⟩ := hWs (unitOf R C P S y) (hW2 P y) hcy
    have hx1 := eq_unitOf_of_mem hred (hW1 P' hx)
    have hz1 := eq_unitOf_of_mem hred (hW1 P hz)
    refine ⟨counitE R C P' S x, ?_, counitE R C P S z, ?_⟩
    · have h := congrArg (counitE R C P' S) hdx
      rw [hx1, twDiff_unitOf ε' D' hd.hβ' hd.hβ1', counitE_unitOf, map_zero] at h
      exact h
    · have h := congrArg (counitE R C P S) hxz
      rw [hx1, map₂_unitOf, hz1, twDiff_unitOf ε D hd.hβ hd.hβ1, map_sub, counitE_unitOf,
        counitE_unitOf, counitE_unitOf] at h
      exact h
  · intro x hx w' hw'
    have hcx : twDiff R C ε' D' β' S (unitOf R C P' S x) = 0 := by
      rw [twDiff_unitOf ε' D' hd.hβ' hd.hβ1']
      exact (congrArg (unitOf R C P' S) hx).trans (map_zero _)
    obtain ⟨z, hz, hdz⟩ := hWi (unitOf R C P' S x) (hW2 P' x) hcx (unitOf R C P S w') (hW2 P w')
      (by rw [map₂_unitOf, twDiff_unitOf ε D hd.hβ hd.hβ1]; exact congrArg _ hw')
    have hz1 := eq_unitOf_of_mem hred (hW1 P' hz)
    refine ⟨counitE R C P' S z, ?_⟩
    have h := congrArg (counitE R C P' S) hdz
    rw [hz1, twDiff_unitOf ε' D' hd.hβ' hd.hβ1', counitE_unitOf, counitE_unitOf] at h
    exact h

include hd in
/-- **The comparison lemma, converse**: for a reduced cooperad, if `1 ∘ g : C ∘_β' P' → C ∘_β P`
is a quasi-isomorphism in every arity, so is `g`, over a field of characteristic zero. -/
theorem TwCompareData.qiso_converse
    (hred : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A ≤ 1 →
      ∀ x : C A, x ∈ unitSpan R C A)
    (hq : ∀ (S : Type) [Fintype S] [DecidableEq S],
      QIso.Surj ⊤ ⊤ (twDiff R C ε' D' β' S) (twDiff R C ε D β S)
          ((map₂ idSpHom g.toGrSpeciesHom).app S)
        ∧ QIso.Inj ⊤ ⊤ (twDiff R C ε' D' β' S) (twDiff R C ε D β S)
          ((map₂ idSpHom g.toGrSpeciesHom).app S))
    (A : Type) [Fintype A] [DecidableEq A] :
    FreeGrL.SurjAt R D'.toSpEnd D.toSpEnd g.toGrSpeciesHom A
      ∧ FreeGrL.InjAt R D'.toSpEnd D.toSpEnd g.toGrSpeciesHom A := by
  suffices h : ∀ (n : ℕ) (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = n →
      FreeGrL.SurjAt R D'.toSpEnd D.toSpEnd g.toGrSpeciesHom A
        ∧ FreeGrL.InjAt R D'.toSpEnd D.toSpEnd g.toGrSpeciesHom A from h _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ _ hA
    by_cases hA0 : IsEmpty A
    · refine ⟨fun y _ => ⟨0, map_zero _, 0, ?_⟩, fun x _ _ _ => ⟨0, ?_⟩⟩
      · rw [map_zero, map_zero, hd.hP0 A hA0 y, sub_zero]
      · rw [map_zero, hd.hP0' A hA0 x]
    · exact hd.qiso_step hred (not_isEmpty_iff.1 hA0)
        (fun B _ _ hB => ih _ (hA ▸ hB) B rfl) (hq A)

end Converse

end GrComposite

end Operad
