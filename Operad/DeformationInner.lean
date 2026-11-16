/-
# Inner derivations and the coboundaries of weight one

Let `P = T(E)/(r)` be a presented operad over a field, `Q` a dg operad and `φ : P → Q` a morphism
with values in the cycles of `Q`, with deformation complex `Def(φ) = Hom_𝔖(P^¡, Q)`
(`Operad.DeformationComplex`). The cochains of weight zero are the operations of `Q` with one
input, `P^¡` being the unit in weight zero, and their differentials are the inner derivations.

* **The inner derivation of an operation of either parity.** For an operation `D` with one
  input, of parity `p`, `[D, x] = D ∘ x - σ(p |x|) ∑_a x ∘_a D` (`GrOperad.adL`) is a derivation
  of parity `p` (`GrOperad.adDer`, `GrOperad.adL_comp`). The odd case is `GrOperad.innerL` of
  `Operad.InnerDer` (`GrOperad.innerL_eq_adL`).
* **Families concentrated in arity one.** For an invariant family `Θ` that vanishes on the sets
  without exactly one element (`GrOperad.Inv.IsArityOne`), `(Θ ⋆ X) A = Θ ∘ X A` on a nonempty
  set and `(X ⋆ Θ) A = ∑_a X A ∘_a Θ` (`GrOperad.Inv.star_arityOne_left`,
  `GrOperad.Inv.star_arityOne_right`), so **the bracket with `Θ` is the inner derivation** of its
  operation on the nonempty sets (`GrOperad.Inv.bracket_arityOne`). `GrOperad.Inv.ofUnit` is the
  family of an operation with one input. The left product in a convolution operad is also
  `GrOperad.Inv.star_counit_left` of `Operad.ConvUnit`.
* **The convolution operad.** For an operation `θ` of `P` with one input, `ε θ : C → P`
  (`ConvOp.unitC`) is the counit followed by `θ`, and its inner derivation in `Hom(C, P)` is the
  inner derivation of `θ` after the maps (`ConvOp.adL_unitC`), by the counit laws
  (`ConvOp.lcomp_unitC`, `ConvOp.rcomp_unitC`).
* **The coboundaries of weight one are the inner derivations.** For `θ` of parity `p` in
  `Q` with one input, the cochain `θ ε` of weight zero (`Koszul.ofUnit`) has bracket with `φ κ`
  the cochain of the inner derivation of `θ` along `φ`, `[θ ε, φ κ] = [θ, -] ∘ φ ∘ κ`
  (`Koszul.bracket_ofUnit`), so its differential in `Def(φ)` is
  `(dθ) ε - σ(p) [θ, -] ∘ φ ∘ κ` (`Koszul.defD_ofUnit`); for a cycle `θ` it is the cochain of
  the inner derivation, up to sign (`Koszul.defD_ofUnit_of_closed`).

The product of invariant families has no term on the empty set, so the last statements are for
generators with at least one input, and over a field of characteristic zero, where `κ` vanishes
on the empty sets (`Koszul.kappa_of_isEmpty`). The quotient of the derivations of `P` along `φ`
by the inner ones is not formed: the cochains are graded by parity only.
-/
import Operad.DeformationComplex
import Operad.InnerDer

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## The inner derivation of an operation of either parity -/

namespace GrOperad

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- `(x ∘ᵢ y) ∘_a D = σ(|y| |D|) (x ∘_a D) ∘ᵢ y` for an input `a ≠ i` of `x`, with `y` and `D`
homogeneous. -/
lemma rcomp_comp_inl_hom' (D : P Unit) {p : Bool} (hD : par (R := R) p D = D) {i a : A}
    (hai : a ≠ i) (x : P A) {q : Bool} {y : P B} (hy : par (R := R) q y = y) :
    rcomp R D (Sum.inl ⟨a, hai⟩ : Without A i ⊕ B) (comp (R := R) i x y)
      = σ R (q && p) • comp (R := R) i (rcomp R D a x) y := by
  rw [rcomp_apply, rcomp_apply, comp_assoc_par' (Ne.symm hai) x hy hD, map_smul, ← map_trans,
    comp_map_left (rightUnitEquiv a) (Sum.inl ⟨i, Ne.symm hai⟩) i rfl]
  congr 1
  refine congrArg (fun e => map (R := R) e _) (Equiv.ext fun z => ?_)
  rcases z with (⟨(⟨c, hc⟩ | u), hc'⟩ | b)
  · rfl
  · rfl
  · rfl

/-- `(x ∘ᵢ y) ∘_a D = (x ∘_a D) ∘ᵢ ε y` for an input `a ≠ i` of `x`, `ε` the sign twist of the
parity of `D`. -/
lemma rcomp_comp_inl' (D : P Unit) {p : Bool} (hD : par (R := R) p D = D) {i a : A}
    (hai : a ≠ i) (x : P A) (y : P B) :
    rcomp R D (Sum.inl ⟨a, hai⟩ : Without A i ⊕ B) (comp (R := R) i x y)
      = comp (R := R) i (rcomp R D a x) (tw (R := R) p y) := by
  conv_lhs => rw [← par_add (R := R) y]
  rw [map_add, map_add, rcomp_comp_inl_hom' D hD hai x (par_par_self false y),
    rcomp_comp_inl_hom' D hD hai x (par_par_self true y), tw_apply, map_add, map_smul]
  simp

variable (R) in
/-- **The inner derivation of an operation `D` of parity `p`**:
`[D, x] = D ∘ x - σ(p |x|) ∑_a x ∘_a D`. -/
def adL (p : Bool) (D : P Unit) : P A →ₗ[R] P A :=
  lcomp R D - ∑ a : A, (rcomp R D a).comp (tw (R := R) p)

lemma adL_apply (p : Bool) (D : P Unit) (x : P A) :
    adL R p D x = lcomp R D x - ∑ a : A, rcomp R D a (tw (R := R) p x) := by
  simp only [adL, LinearMap.sub_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply]

/-- The inner derivation of an odd operation is the case `p = true`. -/
lemma innerL_eq_adL (D : P Unit) : innerL R D (A := A) = adL R true D := rfl

/-- **The inner derivation is a derivation of the compositions.** -/
theorem adL_comp {p : Bool} (D : P Unit) (hD : par (R := R) p D = D) (i : A) (x : P A)
    (y : P B) :
    adL R p D (comp (R := R) i x y)
      = comp (R := R) i (adL R p D x) y + comp (R := R) i (tw (R := R) p x) (adL R p D y) := by
  have h : ∀ a : Without A i, rcomp R D (Sum.inl a : Without A i ⊕ B)
      (comp (R := R) i (tw (R := R) p x) (tw (R := R) p y))
        = comp (R := R) i (rcomp R D a.1 (tw (R := R) p x)) y := by
    rintro ⟨a, ha⟩
    rw [rcomp_comp_inl' D hD ha, tw_tw]
  rw [adL_apply, adL_apply, adL_apply, tw_comp, lcomp_comp, Fintype.sum_sum_type]
  simp only [h, rcomp_comp_inr, map_sub, LinearMap.sub_apply, map_sum, LinearMap.coe_sum,
    Finset.sum_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun a => comp (R := R) i (rcomp R D a (tw (R := R) p x)) y) i, comp_rcomp_self]
  abel

/-- The inner derivation of a homogeneous operation has the sum of the parities. -/
lemma adL_hom {p : Bool} (D : P Unit) (hD : par (R := R) p D = D) {q : Bool} {x : P A}
    (hx : par (R := R) q x = x) : par (R := R) (xor p q) (adL R p D x) = adL R p D x := by
  rw [adL_apply, map_sub, map_sum]
  congr 1
  · rw [lcomp_apply, ← map_par, par_comp_hom () rfl hD hx]
  · refine Finset.sum_congr rfl fun a _ => ?_
    have htx : par (R := R) q (tw (R := R) p x) = tw (R := R) p x := by
      rw [par_tw, hx]
    rw [rcomp_apply, ← map_par, par_comp_hom a (Bool.xor_comm q p) htx hD]

/-- **The inner derivation shifts the parities by the parity of the operation.** -/
lemma adL_par {p : Bool} (D : P Unit) (hD : par (R := R) p D = D) (c : Bool) (x : P A) :
    adL R p D (par (R := R) c x) = par (R := R) (xor c p) (adL R p D x) := by
  have h : ∀ b, par (R := R) (xor c p) (adL R p D (par (R := R) b x))
      = if c = b then adL R p D (par (R := R) b x) else 0 := by
    intro b
    rw [← adL_hom D hD (par_par_self b x), par_par]
    cases b <;> cases c <;> cases p <;> simp
  conv_rhs => rw [← par_add (R := R) x, map_add, map_add, h, h]
  cases c <;> simp

/-- **The inner derivation commutes with relabelling.** -/
lemma adL_map (p : Bool) (D : P Unit) (e : A ≃ B) (x : P A) :
    adL R p D (map (R := R) e x) = map (R := R) e (adL R p D x) := by
  rw [adL_apply, adL_apply, map_sub, map_sum, lcomp_map, ← map_tw, ← Equiv.sum_comp e]
  simp only [rcomp_map]

/-- **The inner derivation kills the unit.** -/
lemma adL_one (p : Bool) (D : P Unit) : adL R p D (one (R := R) (P := P)) = 0 := by
  have he : leftUnitEquiv Unit = rightUnitEquiv () :=
    Equiv.ext fun _ => Subsingleton.elim _ _
  rw [adL_apply, tw_one, Fintype.sum_unique, lcomp_apply, rcomp_apply, he, comp_one, ← he,
    one_comp, sub_self]

/-- **The inner derivation of an operation of parity `p`**, a derivation of `P` of parity `p`. -/
def adDer (p : Bool) (D : P Unit) (hD : par (R := R) p D = D) :
    GrDer (GrOperadHom.id R P) p where
  app _ _ _ := adL R p D
  app_par c x := adL_par D hD c x
  app_map e x := adL_map p D e x
  app_one := adL_one p D
  app_comp i x y := adL_comp D hD i x y

@[simp] lemma adDer_app (p : Bool) (D : P Unit) (hD : par (R := R) p D = D) (x : P A) :
    (adDer p D hD).app A x = adL R p D x := rfl

/-! ## Invariant families concentrated on the sets with one element -/

namespace Inv

/-- **A family concentrated in arity one**: zero on the sets without exactly one element. -/
def IsArityOne (Θ : Inv R P) : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≠ 1 → Θ.1 B = 0

/-- The term of `Θ ⋆ X` at the full subset is `Θ ∘ X`. -/
lemma term_univ (Θ X : Inv R P) (A : Type) [Fintype A] [DecidableEq A] :
    term (R := R) Θ.1 X.1 A Finset.univ = lcomp R (Θ.1 Unit) (X.1 A) := by
  have hS : ∀ x : A, x ∈ (Finset.univ : Finset A) ↔ ∃ b, leftUnitEquiv A (Sum.inr b) = x :=
    fun x => ⟨fun _ => ⟨x, rfl⟩, fun _ => Finset.mem_univ x⟩
  rw [lcomp_apply, map_comp_canon (leftUnitEquiv A) Finset.univ hS, map_apply Θ, map_apply X]
  rfl

/-- The term of `X ⋆ Θ` at a singleton is `X ∘_a Θ`. -/
lemma term_singleton (X Θ : Inv R P) (A : Type) [Fintype A] [DecidableEq A] (a : A) :
    term (R := R) X.1 Θ.1 A {a} = rcomp R (Θ.1 Unit) a (X.1 A) := by
  have hS : ∀ x : A, x ∈ ({a} : Finset A) ↔ ∃ b, rightUnitEquiv a (Sum.inr b) = x :=
    fun x => ⟨fun h => ⟨(), (Finset.mem_singleton.1 h).symm⟩,
      fun ⟨_, h⟩ => Finset.mem_singleton.2 h.symm⟩
  rw [rcomp_apply, map_comp_canon (rightUnitEquiv a) {a} hS, map_apply X, map_apply Θ]
  rfl

/-- The terms of `Θ ⋆ X` at the proper subsets vanish. -/
lemma term_eq_zero_left {Θ : Inv R P} (hΘ : IsArityOne Θ) (X : Fam P) (A : Type) [Fintype A]
    [DecidableEq A] {S : Finset A} (hS : S ≠ Finset.univ) :
    term (R := R) Θ.1 X A S = 0 := by
  have hc : Fintype.card (SOut S) ≠ 1 := by
    intro h
    have h1 : Fintype.card (SOut S) = Fintype.card {x : A // x ∉ S} + 1 := Fintype.card_option
    have h0 : Fintype.card {x : A // x ∉ S} = 0 := by omega
    rw [Fintype.card_eq_zero_iff] at h0
    exact hS (Finset.eq_univ_iff_forall.2 fun x => by_contra fun hx => h0.elim ⟨x, hx⟩)
  unfold term
  rw [hΘ _ hc, map_zero, LinearMap.zero_apply, map_zero]

/-- The terms of `X ⋆ Θ` at the subsets that are not singletons vanish. -/
lemma term_eq_zero_right {Θ : Inv R P} (hΘ : IsArityOne Θ) (X : Fam P) (A : Type) [Fintype A]
    [DecidableEq A] {S : Finset A} (hS : S.card ≠ 1) :
    term (R := R) X Θ.1 A S = 0 := by
  have hc : Fintype.card (SIn S) ≠ 1 := by
    have h1 : Fintype.card (SIn S) = S.card := Fintype.card_coe S
    omega
  unfold term
  rw [hΘ _ hc, map_zero, map_zero]

/-- **The product with a family concentrated in arity one, on the left**: `(Θ ⋆ X) A = Θ ∘ X A`
on a nonempty set. -/
theorem star_arityOne_left {Θ : Inv R P} (hΘ : IsArityOne Θ) (X : Inv R P) (A : Type)
    [Fintype A] [DecidableEq A] [Nonempty A] :
    (star R P Θ X).1 A = lcomp R (Θ.1 Unit) (X.1 A) := by
  rw [star_apply, Finset.sum_eq_single_of_mem Finset.univ
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.univ_nonempty⟩)
    (fun S _ hS => term_eq_zero_left hΘ X.1 A hS), term_univ]

/-- **The product with a family concentrated in arity one, on the right**:
`(X ⋆ Θ) A = ∑_a X A ∘_a Θ`. -/
theorem star_arityOne_right {Θ : Inv R P} (hΘ : IsArityOne Θ) (X : Inv R P) (A : Type)
    [Fintype A] [DecidableEq A] :
    (star R P X Θ).1 A = ∑ a : A, rcomp R (Θ.1 Unit) a (X.1 A) := by
  have h1 : ∑ S ∈ nonempties A, term (R := R) X.1 Θ.1 A S
      = ∑ S ∈ Finset.univ.map ⟨fun a : A => ({a} : Finset A), Finset.singleton_injective⟩,
          term (R := R) X.1 Θ.1 A S := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro S hS
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hS
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.singleton_nonempty a⟩
    · intro S _ hS
      refine term_eq_zero_right hΘ X.1 A fun hc => hS ?_
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc
      exact Finset.mem_map.2 ⟨a, Finset.mem_univ a, rfl⟩
  rw [star_apply, h1, Finset.sum_map]
  exact Finset.sum_congr rfl fun a _ => term_singleton X Θ A a

/-- The product of invariant families vanishes on the empty sets. -/
lemma star_of_isEmpty (q q' : Inv R P) (A : Type) [Fintype A] [DecidableEq A] [IsEmpty A] :
    (star R P q q').1 A = 0 := by
  rw [star_apply]
  refine Finset.sum_eq_zero fun S hS => ?_
  exact absurd (Finset.mem_filter.1 hS).2
    (Finset.not_nonempty_iff_eq_empty.2 (Finset.eq_empty_of_isEmpty S))

/-- **The bracket with a family concentrated in arity one is its inner derivation**, on a
nonempty set. -/
theorem bracket_arityOne {Θ X : Inv R P} {p q : Bool} (hΘ : IsArityOne Θ) (hp : IsPar p Θ)
    (hq : IsPar q X) (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] :
    (bracket R P Θ X).1 A = adL R p (Θ.1 Unit) (X.1 A) := by
  rw [bracket_hom hp hq]
  show (star R P Θ X).1 A - σ R (p && q) • (star R P X Θ).1 A = _
  rw [star_arityOne_left hΘ X A, star_arityOne_right hΘ X A, adL_apply, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tw_hom p (hq A), map_smul]

/-- The bracket of homogeneous families vanishes on the empty sets. -/
lemma bracket_of_isEmpty {Θ X : Inv R P} {p q : Bool} (hp : IsPar p Θ) (hq : IsPar q X)
    (A : Type) [Fintype A] [DecidableEq A] [IsEmpty A] : (bracket R P Θ X).1 A = 0 := by
  rw [bracket_hom hp hq]
  show (star R P Θ X).1 A - σ R (p && q) • (star R P X Θ).1 A = _
  rw [star_of_isEmpty, star_of_isEmpty, smul_zero, sub_zero]

/-- The bijection from `Unit` to a type with one element. -/
noncomputable def equivOfCardOne (A : Type) [Fintype A] (h : Fintype.card A = 1) : Unit ≃ A :=
  Fintype.equivOfCardEq (Fintype.card_unit.trans h.symm)

variable (R) in
/-- The family of an operation with one input: its relabellings on the sets with one element,
and zero elsewhere. -/
noncomputable def ofUnitF (θ : P Unit) : Fam P := fun A _ _ =>
  if h : Fintype.card A = 1 then map (R := R) (equivOfCardOne A h) θ else 0

lemma ofUnitF_pos (θ : P Unit) {A : Type} [Fintype A] [DecidableEq A]
    (h : Fintype.card A = 1) : ofUnitF R θ A = map (R := R) (equivOfCardOne A h) θ := dif_pos h

lemma ofUnitF_neg (θ : P Unit) {A : Type} [Fintype A] [DecidableEq A]
    (h : Fintype.card A ≠ 1) : ofUnitF R θ A = 0 := dif_neg h

variable (R) in
/-- **The invariant family of an operation with one input**, concentrated in arity one. -/
noncomputable def ofUnit (θ : P Unit) : Inv R P :=
  ⟨ofUnitF R θ, by
    intro A B _ _ _ _ e
    have hc : Fintype.card A = Fintype.card B := Fintype.card_congr e
    show map (R := R) e (ofUnitF R θ A) = ofUnitF R θ B
    by_cases h : Fintype.card A = 1
    · have h' : Fintype.card B = 1 := hc ▸ h
      haveI : Subsingleton B := Fintype.card_le_one_iff_subsingleton.1 h'.le
      rw [ofUnitF_pos θ h, ofUnitF_pos θ h', ← map_trans]
      exact congrArg (fun e' => map (R := R) e' θ) (Equiv.ext fun _ => Subsingleton.elim _ _)
    · have h' : Fintype.card B ≠ 1 := fun hB => h (hc.trans hB)
      rw [ofUnitF_neg θ h, ofUnitF_neg θ h', map_zero]⟩

lemma ofUnit_unit (θ : P Unit) : (ofUnit R θ).1 Unit = θ := by
  have he : equivOfCardOne Unit Fintype.card_unit = Equiv.refl Unit :=
    Equiv.ext fun _ => Subsingleton.elim _ _
  exact (ofUnitF_pos θ Fintype.card_unit).trans (by rw [he, map_refl])

lemma isArityOne_ofUnit (θ : P Unit) : IsArityOne (ofUnit R θ) :=
  fun _ _ _ h => ofUnitF_neg θ h

lemma isPar_ofUnit {p : Bool} {θ : P Unit} (hθ : par (R := R) p θ = θ) :
    IsPar p (ofUnit R θ) := fun A _ _ => by
  show par (R := R) p (ofUnitF R θ A) = ofUnitF R θ A
  by_cases h : Fintype.card A = 1
  · rw [ofUnitF_pos θ h, ← map_par, hθ]
  · rw [ofUnitF_neg θ h, map_zero]

lemma ofUnit_zero : ofUnit R (0 : P Unit) = 0 :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => by
    show ofUnitF R (0 : P Unit) A = 0
    by_cases h : Fintype.card A = 1
    · rw [ofUnitF_pos _ h, map_zero]
    · exact ofUnitF_neg _ h)

/-- **A derivation acts on the family of an operation with one input through the operation.** -/
lemma appDer_ofUnit {e : Bool} (D : GrDer (GrOperadHom.id R P) e) (θ : P Unit) :
    appDer D (ofUnit R θ) = ofUnit R (D.app Unit θ) :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => by
    show D.app A (ofUnitF R θ A) = ofUnitF R (D.app Unit θ) A
    by_cases h : Fintype.card A = 1
    · rw [ofUnitF_pos _ h, ofUnitF_pos _ h, D.app_map]
    · rw [ofUnitF_neg _ h, ofUnitF_neg _ h, map_zero])

end Inv

end GrOperad

/-! ## The counit followed by an operation with one input -/

namespace ConvOp

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable (R C) in
/-- **The counit followed by an operation with one input**: `x ↦ ε(x) θ`. -/
def unitC (θ : P Unit) : ConvOp R C P Unit :=
  of ((GrCooperad.counit (R := R) (C := C)).smulRight θ)

omit [GrOperad R P] in
lemma unitC_apply (θ : P Unit) (x : C Unit) :
    toLin (unitC R C θ) x = GrCooperad.counit (R := R) x • θ := rfl

/-- The counit is even. -/
lemma counit_tw (e : Bool) (x : C Unit) :
    GrCooperad.counit (R := R) (GrSpecies.tw (R := R) e x) = GrCooperad.counit (R := R) x := by
  have h := LinearMap.congr_fun (GrCooperad.counit_par (R := R) (C := C)) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [GrSpecies.tw_apply, map_add, map_smul, h, smul_zero, add_zero, counit_par_false]

omit [GrOperad R P] in
lemma unitC_comp_tw (θ : P Unit) (e : Bool) :
    toLin (unitC R C θ) ∘ₗ GrSpecies.tw (R := R) e = toLin (unitC R C θ) :=
  LinearMap.ext fun x => by
    show GrCooperad.counit (R := R) (GrSpecies.tw (R := R) e x) • θ
      = GrCooperad.counit (R := R) x • θ
    rw [counit_tw]

/-- The counit followed by an operation of parity `p` raises parities by `p`. -/
lemma isParC_unitC {p : Bool} {θ : P Unit} (hθ : GrOperad.par (R := R) p θ = θ) :
    IsParC p (unitC R C θ) := by
  intro c x
  simp only [unitC_apply, map_smul]
  have h := LinearMap.congr_fun (GrCooperad.counit_par (R := R) (C := C)) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  cases c
  · rw [counit_par_false, Bool.false_xor, hθ]
  · rw [h, zero_smul, ← hθ, GrOperad.par_par, Bool.true_xor, if_neg (by cases p <;> decide),
      smul_zero]

lemma par_unitC {p : Bool} {θ : P Unit} (hθ : GrOperad.par (R := R) p θ = θ) :
    GrOperad.par (R := R) p (unitC R C θ) = unitC R C θ :=
  parC_eq_self_iff.2 (isParC_unitC hθ)

/-- **Composing after `ε θ` is composing after `θ`.** -/
theorem lcomp_unitC (θ : P Unit) (g : ConvOp R C P B) :
    GrOperad.lcomp R (unitC R C θ) g = postL (GrOperad.lcomp R θ) g := by
  apply ConvOp.ext
  intro x
  have hc := LinearMap.congr_fun (GrCooperad.counit_left (R := R) (C := C) (B := B)) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at hc
  have hk : kap (unitC R C θ) g = TensorProduct.map (toLin (unitC R C θ)) (toLin g) := by
    simp only [kap, unitC_comp_tw, Fintype.sum_bool, ← TensorProduct.map_add_right, ← toLin_add,
      add_comm (parC true g), parC_add]
  have key : ∀ t, GrOperad.map (R := R) (leftUnitEquiv B)
      (mu () (TensorProduct.map (toLin (unitC R C θ)) (toLin g) t))
      = GrOperad.lcomp R θ (toLin g ((TensorProduct.lid R (C B)) (LinearMap.rTensor (C B)
          (GrCooperad.counit (R := R) (C := C)) t))) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul u b =>
      simp only [TensorProduct.map_tmul, unitC_apply, mu_tmul, map_smul, LinearMap.smul_apply,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul, GrOperad.lcomp_apply]
    | add s t hs ht => simp only [map_add, hs, ht]
  have hL : toLin (GrOperad.lcomp R (unitC R C θ) g) x
      = GrOperad.map (R := R) (leftUnitEquiv B)
          (mu () (TensorProduct.map (toLin (unitC R C θ)) (toLin g)
            (GrCooperad.decomp (R := R) (C := C) ()
              (SymSpecies.map (R := R) (leftUnitEquiv B).symm x)))) := by
    show toLin (mapC (leftUnitEquiv B) (compC () (unitC R C θ) g)) x = _
    rw [mapC_apply, toLin_compC, hk]
    rfl
  rw [hL, key]
  exact congrArg (fun y => GrOperad.lcomp R θ (toLin g y)) hc

/-- **Inserting `ε θ` at an input is inserting `θ`**, after the sign twist of the parity of `θ`
on the cooperad. -/
theorem rcomp_unitC {p : Bool} {θ : P Unit} (hθ : GrOperad.par (R := R) p θ = θ) (a : A)
    (f : ConvOp R C P A) :
    GrOperad.rcomp R (unitC R C θ) a f
      = postL (GrOperad.rcomp R θ a) (of (toLin f ∘ₗ GrSpecies.tw (R := R) p)) := by
  apply ConvOp.ext
  intro x
  have hc := LinearMap.congr_fun (GrCooperad.counit_right (R := R) (C := C) a) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at hc
  have key : ∀ t, GrOperad.map (R := R) (rightUnitEquiv a)
      (mu a (TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) p) (toLin (unitC R C θ)) t))
      = GrOperad.rcomp R θ a (toLin f (GrSpecies.tw (R := R) p
          ((TensorProduct.rid R (C A)) (LinearMap.lTensor (C A)
            (GrCooperad.counit (R := R) (C := C)) t)))) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul y u =>
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, unitC_apply, mu_tmul, map_smul,
        LinearMap.lTensor_tmul, TensorProduct.rid_tmul, GrOperad.rcomp_apply]
    | add s t hs ht => simp only [map_add, hs, ht]
  have hL : toLin (GrOperad.rcomp R (unitC R C θ) a f) x
      = GrOperad.map (R := R) (rightUnitEquiv a)
          (mu a (TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) p) (toLin (unitC R C θ))
            (GrCooperad.decomp (R := R) (C := C) a
              (SymSpecies.map (R := R) (rightUnitEquiv a).symm x)))) := by
    show toLin (mapC (rightUnitEquiv a) (compC a f (unitC R C θ))) x = _
    rw [mapC_apply, toLin_compC, kap_hom f (isParC_unitC hθ)]
    rfl
  rw [hL, key]
  exact congrArg (fun y => GrOperad.rcomp R θ a (toLin f (GrSpecies.tw (R := R) p y))) hc

/-- Composing with a linear map, as a linear map of the linear map. -/
def postR (f : ConvOp R C P A) : (P A →ₗ[R] P A) →ₗ[R] ConvOp R C P A where
  toFun φ := postL φ f
  map_add' _ _ := ConvOp.ext fun _ => rfl
  map_smul' _ _ := ConvOp.ext fun _ => rfl

/-- **The inner derivation of `ε θ` in the convolution operad is the inner derivation of `θ`**,
after the maps. -/
theorem adL_unitC {p : Bool} {θ : P Unit} (hθ : GrOperad.par (R := R) p θ = θ)
    (f : ConvOp R C P A) :
    GrOperad.adL R p (unitC R C θ) f = postL (GrOperad.adL R p θ) f := by
  have h2 : ∀ a : A, GrOperad.rcomp R (unitC R C θ) a (GrOperad.tw (R := R) p f)
      = postR f ((GrOperad.rcomp R θ a).comp (GrOperad.tw (R := R) p)) := fun a => by
    rw [rcomp_unitC hθ]
    apply ConvOp.ext
    intro y
    show GrOperad.rcomp R θ a (toLin (GrOperad.tw (R := R) p f) (GrSpecies.tw (R := R) p y))
      = GrOperad.rcomp R θ a (GrOperad.tw (R := R) p (toLin f y))
    rw [tw_apply, GrSpecies.tw_tw, Bool.xor_self, GrSpecies.tw_false]
  rw [GrOperad.adL_apply, lcomp_unitC, Finset.sum_congr rfl fun a _ => h2 a, ← map_sum]
  show postR f (GrOperad.lcomp R θ)
      - postR f (∑ a : A, (GrOperad.rcomp R θ a).comp (GrOperad.tw (R := R) p))
    = postR f (GrOperad.adL R p θ)
  rw [← map_sub]
  rfl

end ConvOp

/-! ## The coboundaries of weight one -/

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

variable (R E r) in
/-- **The cochain of weight zero of an operation with one input**: `θ` after the counit of
`P^¡`, on the sets with one element. -/
noncomputable def ofUnit (θ : Q Unit) : Def R E r Q :=
  GrOperad.Inv.ofUnit R (ConvOp.unitC R (Dual R E r) θ)

include R in
/-- A generator on an empty set vanishes, without generators without inputs. -/
lemma gen_eq_zero_of_isEmpty (hE0 : ∀ v : E (Fin 0), v = 0) {A : Type} [Fintype A]
    [DecidableEq A] [IsEmpty A] (v : E A) : v = 0 := by
  have he : (Equiv.equivOfIsEmpty A (Fin 0)).trans (Equiv.equivOfIsEmpty (Fin 0) A)
      = Equiv.refl A := Equiv.ext fun a => isEmptyElim a
  have h : SymSpecies.map (R := R) (Equiv.equivOfIsEmpty (Fin 0) A)
      (SymSpecies.map (R := R) (Equiv.equivOfIsEmpty A (Fin 0)) v) = v := by
    rw [← SymSpecies.map_trans, he, SymSpecies.map_refl]
  rw [← h, hE0 (SymSpecies.map (R := R) (Equiv.equivOfIsEmpty A (Fin 0)) v), map_zero]

omit [DGOperad R Q] in
/-- The Koszul twisting morphism vanishes on the empty sets, without generators without
inputs. -/
lemma kappa_of_isEmpty [CharZero R] (hE0 : ∀ v : E (Fin 0), v = 0) {A : Type} [Fintype A]
    [DecidableEq A] [IsEmpty A] (c : Dual R E r A) :
    ConvOp.toLin ((kappa R E r).1 A) c = 0 := by
  have hz : kapL R E A ((dualSub R E r).incl A c)
      = (FreeGrL.ι R E).app A (FreeGrL.genCoef R E A (kapL R E A ((dualSub R E r).incl A c))) :=
    FreeGrL.eq_ι_genCoef (kapL_mem_vx _)
  have h0 : kapL R E A ((dualSub R E r).incl A c) = 0 := by
    rw [hz, gen_eq_zero_of_isEmpty (R := R) hE0 (FreeGrL.genCoef R E A _), map_zero]
  exact (congrArg ((GrOperadIdeal.span R r).proj A) h0).trans (map_zero _)

/-- The cochain of an operation of parity `p` has parity `p`. -/
lemma isPar_ofUnit {p : Bool} {θ : Q Unit} (hθ : GrOperad.par (R := R) p θ = θ) :
    GrOperad.Inv.IsPar p (ofUnit R E r θ) :=
  GrOperad.Inv.isPar_ofUnit (ConvOp.par_unitC hθ)

/-- **The bracket of the cochain of an operation `θ` with one input with `φ κ` is the cochain
of the inner derivation of `θ` along `φ`**: `[θ ε, φ κ] = [θ, -] ∘ φ ∘ κ`. Over a field of
characteristic zero, without generators without inputs. -/
theorem bracket_ofUnit [CharZero R] (hE0 : ∀ v : E (Fin 0), v = 0) {p : Bool} {θ : Q Unit}
    (hθ : GrOperad.par (R := R) p θ = θ) :
    GrOperad.Inv.bracket R _ (ofUnit R E r θ) (twistingOf φ hφ).1
      = ofDer φ ((GrOperad.adDer p θ hθ).compHom φ) := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ?_)
  have hp : GrOperad.Inv.IsPar p (ofUnit R E r θ) := isPar_ofUnit hθ
  have hq : GrOperad.Inv.IsPar true (twistingOf φ hφ).1 := (twistingOf φ hφ).2.1
  by_cases hA : Nonempty A
  · have hb := GrOperad.Inv.bracket_arityOne
      (GrOperad.Inv.isArityOne_ofUnit (ConvOp.unitC R (Dual R E r) θ)) hp hq A
    have h1 : GrOperad.adL R p ((ofUnit R E r θ).1 Unit) ((twistingOf φ hφ).1.1 A)
        = GrOperad.adL R p (ConvOp.unitC R (Dual R E r) θ) ((twistingOf φ hφ).1.1 A) :=
      congrArg (fun D => GrOperad.adL R p D ((twistingOf φ hφ).1.1 A))
        (GrOperad.Inv.ofUnit_unit (ConvOp.unitC R (Dual R E r) θ))
    refine hb.trans (h1.trans ((ConvOp.adL_unitC hθ _).trans ?_))
    exact ConvOp.ext fun c => rfl
  · haveI : IsEmpty A := not_nonempty_iff.1 hA
    refine (GrOperad.Inv.bracket_of_isEmpty hp hq A).trans (ConvOp.ext fun c => ?_).symm
    show GrOperad.adL R p θ (φ.app A (ConvOp.toLin ((kappa R E r).1 A) c)) = 0
    rw [kappa_of_isEmpty hE0 c, map_zero, map_zero]

/-- The differential of `Hom_𝔖(P^¡, Q)` acts on the cochain of an operation with one input
through the operation. -/
lemma appDer_convD_ofUnit (θ : Q Unit) :
    GrOperad.Inv.appDer (Twisting.convD R (Dual R E r) Q) (ofUnit R E r θ)
      = ofUnit R E r (DGOperad.d (R := R) θ) := by
  refine (GrOperad.Inv.appDer_ofUnit _ _).trans ?_
  exact congrArg (GrOperad.Inv.ofUnit R) (ConvOp.ext fun c => by
    show DGOperad.d (R := R) (GrCooperad.counit (R := R) c • θ)
      = GrCooperad.counit (R := R) c • DGOperad.d (R := R) θ
    rw [map_smul])

/-- **The differential of the deformation complex on a cochain of weight zero**: for an
operation `θ` of parity `p` with one input,
`∂(θ ε) + [φ κ, θ ε] = (dθ) ε - σ(p) [θ, -] ∘ φ ∘ κ`. -/
theorem defD_ofUnit [CharZero R] (hE0 : ∀ v : E (Fin 0), v = 0) {p : Bool} {θ : Q Unit}
    (hθ : GrOperad.par (R := R) p θ = θ) :
    defD φ hφ (ofUnit R E r θ)
      = ofUnit R E r (DGOperad.d (R := R) θ)
        - σ R p • ofDer φ ((GrOperad.adDer p θ hθ).compHom φ) := by
  have hp : GrOperad.Inv.IsPar p (ofUnit R E r θ) := isPar_ofUnit hθ
  have hq : GrOperad.Inv.IsPar true (twistingOf φ hφ).1 := (twistingOf φ hφ).2.1
  have hsw : GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofUnit R E r θ)
      = -(σ R p • GrOperad.Inv.bracket R _ (ofUnit R E r θ) (twistingOf φ hφ).1) :=
    GrOperad.Inv.bracket_swap hq hp
  have h3 : GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofUnit R E r θ)
      = -(σ R p • ofDer φ ((GrOperad.adDer p θ hθ).compHom φ)) :=
    hsw.trans (congrArg (fun z => -(σ R p • z)) (bracket_ofUnit φ hφ hE0 hθ))
  have h1 : defD φ hφ (ofUnit R E r θ)
      = GrOperad.Inv.appDer (Twisting.convD R (Dual R E r) Q) (ofUnit R E r θ)
        + GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofUnit R E r θ) :=
    GrOperad.Inv.twD_apply _ _ _
  exact h1.trans ((congrArg (fun z => z
      + GrOperad.Inv.bracket R _ (twistingOf φ hφ).1 (ofUnit R E r θ))
        (appDer_convD_ofUnit θ)).trans
    ((congrArg (fun z => ofUnit R E r (DGOperad.d (R := R) θ) + z) h3).trans
      (sub_eq_add_neg _ _).symm))

/-- **The coboundaries of weight one are the inner derivations**: for a cycle `θ` of parity `p`
with one input, the cochain of the inner derivation `[θ, -] ∘ φ` of `P` along `φ` is, up to the
sign `-σ(p)`, the differential of the cochain `θ ε` of weight zero. -/
theorem defD_ofUnit_of_closed [CharZero R] (hE0 : ∀ v : E (Fin 0), v = 0) {p : Bool}
    {θ : Q Unit} (hθ : GrOperad.par (R := R) p θ = θ) (hd : DGOperad.d (R := R) θ = 0) :
    defD φ hφ (ofUnit R E r θ) = -(σ R p • ofDer φ ((GrOperad.adDer p θ hθ).compHom φ)) := by
  have h0 : ofUnit R E r (DGOperad.d (R := R) θ) = (0 : Def R E r Q) :=
    (congrArg (fun z => ofUnit R E r z) hd).trans
      ((congrArg (GrOperad.Inv.ofUnit R) (ConvOp.ext fun _ => smul_zero _)).trans
        GrOperad.Inv.ofUnit_zero)
  exact (defD_ofUnit φ hφ hE0 hθ).trans
    ((congrArg (fun z => z - σ R p • ofDer φ ((GrOperad.adDer p θ hθ).compHom φ)) h0).trans
      (zero_sub _))

end Koszul

end Operad
