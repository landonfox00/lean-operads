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

end GrComposite

end Operad
