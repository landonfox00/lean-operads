/-
# Inner derivations, dg endomorphism operads and homotopy algebras

An odd operation `D` with one input in a graded operad `P` acts on every operation `x` by the
**inner derivation**

  `[D, x] = D ∘ x - σ(|x|) ∑_a x ∘_a D`

(`GrOperad.innerL`). It is a derivation of the compositions (`GrOperad.innerDer`), and when
`D ∘ D = 0` it squares to zero (`GrOperad.innerL_innerL`), so that `P` is a dg operad
(`GrOperad.innerDG`).

* Composing with `D` on either side commutes with the compositions: `D ∘ (x ∘ᵢ y) = (D ∘ x) ∘ᵢ y`
  and `(x ∘ᵢ y) ∘_b D = x ∘ᵢ (y ∘_b D)` for an input `b` of `y`, by sequential associativity, and
  `(x ∘ᵢ y) ∘_a D = σ(|y|) (x ∘_a D) ∘ᵢ y` for an input `a ≠ i` of `x`, by parallel associativity;
  the term `(x ∘ᵢ D) ∘ᵢ y` at the input `i` itself is `x ∘ᵢ (D ∘ y)`.
* In `[D, [D, x]]` the terms `(x ∘_a D) ∘_b D` cancel in pairs for `a ≠ b` and contain `D ∘ D`
  for `a = b`, without dividing by two.
* **A dg super module** (`DGSuperMod`) is a super module with an odd differential `d` with
  `d² = 0`. Its graded endomorphism operad is a dg operad (`EndGr.instDGOperad`), the differential
  being the inner derivation of `d`: `∂f = d ∘ f - σ(|f|) ∑_a f ∘_a d`, with the Koszul signs of the
  graded endomorphism operad.
* **Homotopy algebras** (`HoAlgebra`): an algebra over the cobar construction `ΩC` of a
  coaugmented graded cooperad `C`, on a dg super module `V`, is a morphism of dg operads
  `ΩC → End_V`. These are **the twisting morphisms `C → End_V`** (`HoAlgebra.equivTwisting`): the
  Maurer–Cartan elements of the convolution Lie algebra of `C` and `End_V`.
-/
import Operad.InvLie
import Operad.GradedEnd

universe u v w

namespace Operad

open Sym GerBV

namespace GrOperad

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## Composites with an operation with one input -/

variable (R) in
/-- **Composing after `D`**: `D ∘ x`. -/
def lcomp (D : P Unit) : P A →ₗ[R] P A :=
  (map (R := R) (leftUnitEquiv A)).comp (comp (R := R) () D)

lemma lcomp_apply (D : P Unit) (x : P A) :
    lcomp R D x = map (R := R) (leftUnitEquiv A) (comp (R := R) () D x) := rfl

variable (R) in
/-- **Inserting `D` at the input `a`**: `x ∘_a D`. -/
def rcomp (D : P Unit) (a : A) : P A →ₗ[R] P A :=
  (map (R := R) (rightUnitEquiv a)).comp ((comp (R := R) a).flip D)

lemma rcomp_apply (D : P Unit) (a : A) (x : P A) :
    rcomp R D a x = map (R := R) (rightUnitEquiv a) (comp (R := R) a x D) := rfl

/-- `D ∘ (x ∘ᵢ y) = (D ∘ x) ∘ᵢ y`. -/
lemma lcomp_comp (D : P Unit) (i : A) (x : P A) (y : P B) :
    lcomp R D (comp (R := R) i x y) = comp (R := R) i (lcomp R D x) y := by
  rw [lcomp_apply, lcomp_apply, comp_map_left (leftUnitEquiv A) (Sum.inr i) i rfl,
    ← comp_assoc_seq () i D x y, ← map_trans]
  refine congrArg (fun e => map (R := R) e _) (Equiv.ext fun z => ?_)
  rcases z with (⟨(⟨u, hu⟩ | a), ha⟩ | b)
  · exact absurd (Subsingleton.elim u ()) hu
  · rfl
  · rfl

/-- `(x ∘ᵢ y) ∘_b D = x ∘ᵢ (y ∘_b D)` for an input `b` of `y`. -/
lemma rcomp_comp_inr (D : P Unit) (i : A) (b : B) (x : P A) (y : P B) :
    rcomp R D (Sum.inr b : Without A i ⊕ B) (comp (R := R) i x y)
      = comp (R := R) i x (rcomp R D b y) := by
  rw [rcomp_apply, rcomp_apply, comp_map_right, comp_assoc_seq' i b x y D, ← map_trans]
  refine congrArg (fun e => map (R := R) e _) (Equiv.ext fun z => ?_)
  rcases z with (a | (b' | u))
  · rfl
  · rfl
  · rfl

/-- `(x ∘ᵢ y) ∘_a D = σ(|y|) (x ∘_a D) ∘ᵢ y` for an input `a ≠ i` of `x` and `y` homogeneous. -/
lemma rcomp_comp_inl_hom (D : P Unit) (hD : par (R := R) true D = D) {i a : A} (hai : a ≠ i)
    (x : P A) {q : Bool} {y : P B} (hy : par (R := R) q y = y) :
    rcomp R D (Sum.inl ⟨a, hai⟩ : Without A i ⊕ B) (comp (R := R) i x y)
      = σ R (q && true) • comp (R := R) i (rcomp R D a x) y := by
  rw [rcomp_apply, rcomp_apply, comp_assoc_par' (Ne.symm hai) x hy hD, map_smul, ← map_trans,
    comp_map_left (rightUnitEquiv a) (Sum.inl ⟨i, Ne.symm hai⟩) i rfl]
  congr 1
  refine congrArg (fun e => map (R := R) e _) (Equiv.ext fun z => ?_)
  rcases z with (⟨(⟨c, hc⟩ | u), hc'⟩ | b)
  · rfl
  · rfl
  · rfl

/-- `(x ∘ᵢ y) ∘_a D = (x ∘_a D) ∘ᵢ ε y` for an input `a ≠ i` of `x`, `ε` the parity involution. -/
lemma rcomp_comp_inl (D : P Unit) (hD : par (R := R) true D = D) {i a : A} (hai : a ≠ i)
    (x : P A) (y : P B) :
    rcomp R D (Sum.inl ⟨a, hai⟩ : Without A i ⊕ B) (comp (R := R) i x y)
      = comp (R := R) i (rcomp R D a x) (tw (R := R) true y) := by
  conv_lhs => rw [← par_add (R := R) y]
  rw [map_add, map_add, rcomp_comp_inl_hom D hD hai x (par_par_self false y),
    rcomp_comp_inl_hom D hD hai x (par_par_self true y), tw_apply, map_add, map_smul]
  simp

/-- `(x ∘ᵢ D) ∘ᵢ y = x ∘ᵢ (D ∘ y)`. -/
lemma comp_rcomp_self (D : P Unit) (i : A) (x : P A) (y : P B) :
    comp (R := R) i (rcomp R D i x) y = comp (R := R) i x (lcomp R D y) := by
  rw [rcomp_apply, lcomp_apply, comp_map_left (rightUnitEquiv i) (Sum.inr ()) i rfl,
    comp_assoc_seq' i () x D y, ← map_trans, comp_map_right]
  refine congrArg (fun e => map (R := R) e _) (Equiv.ext fun z => ?_)
  rcases z with (a | (⟨u, hu⟩ | b))
  · rfl
  · exact absurd (Subsingleton.elim u ()) hu
  · rfl

/-- Composing after `D` commutes with relabelling. -/
lemma lcomp_map (D : P Unit) (e : A ≃ B) (x : P A) :
    lcomp R D (map (R := R) e x) = map (R := R) e (lcomp R D x) := by
  rw [lcomp_apply, lcomp_apply, comp_map_right, ← map_trans, ← map_trans]
  refine congrArg (fun e => map (R := R) e _) (Equiv.ext fun z => ?_)
  rcases z with (⟨u, hu⟩ | a)
  · exact absurd (Subsingleton.elim u ()) hu
  · rfl

/-- Inserting `D` commutes with relabelling, the input transported. -/
lemma rcomp_map (D : P Unit) (e : A ≃ B) (a : A) (x : P A) :
    rcomp R D (e a) (map (R := R) e x) = map (R := R) e (rcomp R D a x) := by
  rw [rcomp_apply, rcomp_apply, comp_map_left e a (e a) rfl, ← map_trans, ← map_trans]
  refine congrArg (fun e => map (R := R) e _) (Equiv.ext fun z => ?_)
  rcases z with (⟨c, hc⟩ | u)
  · rfl
  · rfl

/-- `D ∘ (x ∘_b D) = (D ∘ x) ∘_b D`. -/
lemma lcomp_rcomp (D : P Unit) (b : A) (x : P A) :
    lcomp R D (rcomp R D b x) = rcomp R D b (lcomp R D x) := by
  rw [rcomp_apply, rcomp_apply, lcomp_map, lcomp_comp]

/-- `D ∘ (D ∘ x) = 0` when `D ∘ D = 0`. -/
lemma lcomp_lcomp (D : P Unit) (hDD : comp (R := R) () D D = 0) (x : P A) :
    lcomp R D (lcomp R D x) = 0 := by
  rw [lcomp_apply, lcomp_apply, comp_map_right, ← comp_assoc_seq () () D D x, hDD]
  simp only [map_zero, LinearMap.zero_apply]

/-- `(x ∘_a D) ∘_a D = 0` when `D ∘ D = 0`. -/
lemma rcomp_rcomp_self (D : P Unit) (hDD : comp (R := R) () D D = 0) (a : A) (x : P A) :
    rcomp R D a (rcomp R D a x) = 0 := by
  rw [rcomp_apply, rcomp_apply, comp_map_left (rightUnitEquiv a) (Sum.inr ()) a rfl,
    comp_assoc_seq' a () x D D, hDD]
  simp only [map_zero]

/-- `(x ∘_b D) ∘_a D = -(x ∘_a D) ∘_b D` for `a ≠ b` and `D` odd. -/
lemma rcomp_rcomp_ne (D : P Unit) (hD : par (R := R) true D = D) {a b : A} (hab : a ≠ b)
    (x : P A) : rcomp R D a (rcomp R D b x) = -rcomp R D b (rcomp R D a x) := by
  rw [rcomp_apply, rcomp_apply, rcomp_apply, rcomp_apply,
    comp_map_left (rightUnitEquiv b) (Sum.inl ⟨a, hab⟩) a rfl,
    comp_map_left (rightUnitEquiv a) (Sum.inl ⟨b, Ne.symm hab⟩) b rfl,
    comp_assoc_par' (Ne.symm hab) x hD hD, Bool.and_self, σ_true, neg_one_smul, map_neg,
    map_neg]
  simp only [← map_trans]
  congr 1
  refine congrArg (fun e => map (R := R) e _) (Equiv.ext fun z => ?_)
  rcases z with (⟨(⟨c, hc⟩ | u), hc'⟩ | u')
  · rfl
  · rfl
  · rfl

/-! ## The inner derivation -/

variable (R) in
/-- **The inner derivation** `[D, x] = D ∘ x - σ(|x|) ∑_a x ∘_a D`. -/
def innerL (D : P Unit) : P A →ₗ[R] P A :=
  lcomp R D - ∑ a : A, (rcomp R D a).comp (tw (R := R) true)

lemma innerL_apply (D : P Unit) (x : P A) :
    innerL R D x = lcomp R D x - ∑ a : A, rcomp R D a (tw (R := R) true x) := by
  simp only [innerL, LinearMap.sub_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply]

/-- **The inner derivation is a derivation of the compositions.** -/
theorem innerL_comp (D : P Unit) (hD : par (R := R) true D = D) (i : A) (x : P A) (y : P B) :
    innerL R D (comp (R := R) i x y)
      = comp (R := R) i (innerL R D x) y + comp (R := R) i (tw (R := R) true x) (innerL R D y) := by
  have h : ∀ a : Without A i, rcomp R D (Sum.inl a : Without A i ⊕ B)
      (comp (R := R) i (tw (R := R) true x) (tw (R := R) true y))
        = comp (R := R) i (rcomp R D a.1 (tw (R := R) true x)) y := by
    rintro ⟨a, ha⟩
    rw [rcomp_comp_inl D hD ha, tw_tw]
  rw [innerL_apply, innerL_apply, innerL_apply, tw_comp, lcomp_comp, Fintype.sum_sum_type]
  simp only [h, rcomp_comp_inr, map_sub, LinearMap.sub_apply, map_sum, LinearMap.coe_sum,
    Finset.sum_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun a => comp (R := R) i (rcomp R D a (tw (R := R) true x)) y) i, comp_rcomp_self]
  abel

/-- The inner derivation of a homogeneous operation has the opposite parity. -/
lemma innerL_hom (D : P Unit) (hD : par (R := R) true D = D) {p : Bool} {x : P A}
    (hx : par (R := R) p x = x) : par (R := R) (!p) (innerL R D x) = innerL R D x := by
  rw [innerL_apply, map_sub, map_sum]
  congr 1
  · rw [lcomp_apply, ← map_par, par_comp_hom () (Bool.true_xor p) hD hx]
  · refine Finset.sum_congr rfl fun a _ => ?_
    have htx : par (R := R) p (tw (R := R) true x) = tw (R := R) true x := by
      rw [par_tw, hx]
    rw [rcomp_apply, ← map_par, par_comp_hom a (Bool.xor_true p) htx hD]

/-- **The inner derivation is odd.** -/
lemma innerL_par (D : P Unit) (hD : par (R := R) true D = D) (c : Bool) (x : P A) :
    innerL R D (par (R := R) c x) = par (R := R) (xor c true) (innerL R D x) := by
  have h : ∀ b, par (R := R) (xor c true) (innerL R D (par (R := R) b x))
      = if c = b then innerL R D (par (R := R) b x) else 0 := by
    intro b
    rw [← innerL_hom D hD (par_par_self b x), par_par]
    cases b <;> cases c <;> simp
  conv_rhs => rw [← par_add (R := R) x, map_add, map_add, h, h]
  cases c <;> simp

/-- **The inner derivation commutes with relabelling.** -/
lemma innerL_map (D : P Unit) (e : A ≃ B) (x : P A) :
    innerL R D (map (R := R) e x) = map (R := R) e (innerL R D x) := by
  rw [innerL_apply, innerL_apply, map_sub, map_sum, lcomp_map, ← map_tw, ← Equiv.sum_comp e]
  simp only [rcomp_map]

/-- **The inner derivation kills the unit.** -/
lemma innerL_one (D : P Unit) : innerL R D (one (R := R) (P := P)) = 0 := by
  have he : leftUnitEquiv Unit = rightUnitEquiv () :=
    Equiv.ext fun _ => Subsingleton.elim _ _
  rw [innerL_apply, tw_one, Fintype.sum_unique, lcomp_apply, rcomp_apply, he, comp_one, ← he,
    one_comp, sub_self]

/-- **The inner derivation**, as an odd derivation of `P`. -/
def innerDer (D : P Unit) (hD : par (R := R) true D = D) : GrDer (GrOperadHom.id R P) true where
  app _ _ _ := innerL R D
  app_par c x := innerL_par D hD c x
  app_map e x := innerL_map D e x
  app_one := innerL_one D
  app_comp i x y := innerL_comp D hD i x y

/-- The parity involution of `D ∘ x` for `D` odd. -/
lemma tw_lcomp (D : P Unit) (hD : par (R := R) true D = D) (x : P A) :
    tw (R := R) true (lcomp R D x) = -lcomp R D (tw (R := R) true x) := by
  rw [lcomp_apply, lcomp_apply, ← map_tw, tw_comp, tw_hom true hD, Bool.and_self, σ_true,
    neg_one_smul, map_neg, LinearMap.neg_apply, map_neg]

/-- The parity involution of `x ∘_a D` for `D` odd. -/
lemma tw_rcomp (D : P Unit) (hD : par (R := R) true D = D) (a : A) (x : P A) :
    tw (R := R) true (rcomp R D a x) = -rcomp R D a (tw (R := R) true x) := by
  rw [rcomp_apply, rcomp_apply, ← map_tw, tw_comp, tw_hom true hD, Bool.and_self, σ_true,
    neg_one_smul, map_neg, map_neg]

/-- **The inner derivation of an odd operation `D` with `D ∘ D = 0` squares to zero.** -/
theorem innerL_innerL (D : P Unit) (hD : par (R := R) true D = D)
    (hDD : comp (R := R) () D D = 0) (x : P A) : innerL R D (innerL R D x) = 0 := by
  have hsum : ∑ a : A, ∑ b : A, rcomp R D a (rcomp R D b x) = 0 := by
    rw [← Fintype.sum_prod_type']
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨a, b⟩ _
      show rcomp R D a (rcomp R D b x) + rcomp R D b (rcomp R D a x) = 0
      by_cases hab : a = b
      · subst hab
        rw [rcomp_rcomp_self D hDD, add_zero]
      · rw [rcomp_rcomp_ne D hD hab, neg_add_cancel]
    · rintro ⟨a, b⟩ _ hne heq
      have hab : a = b := (Prod.ext_iff.1 heq).2
      subst hab
      exact hne (rcomp_rcomp_self D hDD a x)
    · intro p _
      exact Finset.mem_univ _
  rw [innerL_apply D (innerL R D x), innerL_apply D x]
  simp only [map_sub, map_add, map_neg, map_sum, lcomp_lcomp D hDD, tw_lcomp D hD,
    tw_rcomp D hD, tw_tw, lcomp_rcomp, Finset.sum_neg_distrib, sub_neg_eq_add,
    Finset.sum_add_distrib, hsum]
  abel

/-- **The dg operad of an odd operation `D` with one input and `D ∘ D = 0`**, with the inner
derivation of `D` as differential. -/
abbrev innerDG (D : P Unit) (hD : par (R := R) true D = D) (hDD : comp (R := R) () D D = 0) :
    DGOperad R P where
  toGrOperad := inferInstance
  d := innerL R D
  d_d := innerL_innerL D hD hDD
  d_par b x := by rw [innerL_par D hD, Bool.xor_true]
  map_d e x := (innerL_map D e x).symm
  d_one := innerL_one D
  d_comp i x y := by rw [innerL_comp D hD, tw_true]

end GrOperad

/-! ## Dg super modules and their endomorphism operads -/

/-- **A dg super module**: a super module with an odd differential squaring to zero. -/
class DGSuperMod (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    [SuperMod R V] where
  /-- The differential. -/
  d : V →ₗ[R] V
  d_d (x : V) : d (d x) = 0
  /-- The differential is odd. -/
  d_pr (b : Bool) (x : V) : d (SuperMod.pr (R := R) b x) = SuperMod.pr (R := R) (!b) (d x)

namespace EndGr

open GrEnd

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] [SuperMod R V]
  [DGSuperMod R V]

variable (R V) in
/-- The differential of `V`, as a multilinear map with one input. -/
noncomputable def dML : EndOp R V Unit :=
  MultilinearMap.ofSubsingleton R V V () (DGSuperMod.d (R := R) (V := V))

lemma dML_apply (x : Unit → V) : dML R V x = DGSuperMod.d (R := R) (x ()) := rfl

/-- The differential is odd. -/
lemma parML_dML : parML R V true (dML R V) = dML R V := by
  refine ext_inp fun c => ?_
  have hc : tot c = c () := by
    unfold tot
    rw [Fintype.sum_unique, bodd_toNat]
  rw [inp_parML, hc]
  refine MultilinearMap.ext fun x => ?_
  rw [out_apply, inp_apply, dML_apply, DGSuperMod.d_pr, Bool.true_xor, pr_self]

variable (R V) in
/-- **The differential of `V`**, as an operation with one input of the graded endomorphism
operad. -/
noncomputable def dE : EndGr R V Unit := ofFam LinOrd.one (dML R V)

lemma dE_odd : GrOperad.par (R := R) true (dE R V) = dE R V := by
  show parE true (dE R V) = dE R V
  rw [dE, parE_ofFam, parML_dML]

/-- **The differential of `V` squares to zero in the graded endomorphism operad.** -/
lemma dE_comp_dE : GrOperad.comp (R := R) () (dE R V) (dE R V) = 0 := by
  show compE () (dE R V) (dE R V) = 0
  refine ext (LinOrd.comp () LinOrd.one LinOrd.one) ?_
  have ht : ∀ q : Bool, twist R V (bsg R LinOrd.one () q) (dML R V) = dML R V := fun q => by
    rw [twist_congr (fun c => bsg_one q c), twist_one]
  have hs : ∑ q, parML R V q (dML R V) = dML R V := by
    rw [Fintype.sum_bool, add_comm, parML_add]
  rw [compE_fam, compFam_comp, dE, ofFam_fam, zero_fam, kcomp_apply]
  simp only [ht]
  rw [← map_sum, hs]
  refine MultilinearMap.ext fun x => ?_
  rw [compL_apply, dML_apply, feed_self, dML_apply, DGSuperMod.d_d, MultilinearMap.zero_apply]

variable (R V) in
/-- **The graded endomorphism operad of a dg super module is a dg operad**, the differential
being the inner derivation of the differential of `V`: `∂f = d ∘ f - σ(|f|) ∑_a f ∘_a d`. -/
noncomputable instance instDGOperad : DGOperad R (EndGr R V) :=
  GrOperad.innerDG (dE R V) dE_odd dE_comp_dE

lemma d_eq {A : Type} [Fintype A] [DecidableEq A] (F : EndGr R V A) :
    DGOperad.d (R := R) F = GrOperad.innerL R (dE R V) F := rfl

end EndGr

/-! ## Homotopy algebras -/

section HoAlgebra

variable (R : Type u) [CommRing R] (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C] (V : Type w) [AddCommGroup V] [Module R V] [SuperMod R V]
  [DGSuperMod R V]

/-- **Homotopy algebras**: the algebras over the cobar construction of `C` on a dg super module
`V`, that is, the morphisms of dg operads `ΩC → End_V`. -/
abbrev HoAlgebra : Type _ := CobarHom R C (EndGr R V)

variable {R C V}

/-- **Homotopy algebras are twisting morphisms**: the `ΩC`-algebra structures on `V` are the
twisting morphisms `C → End_V`, the Maurer–Cartan elements of the convolution Lie algebra. -/
noncomputable def HoAlgebra.equivTwisting : HoAlgebra R C V ≃ Twisting R C (EndGr R V) :=
  Cobar.homEquiv

/-- The twisting morphism of a homotopy algebra is its restriction to the generators. -/
lemma HoAlgebra.equivTwisting_apply (φ : HoAlgebra R C V) {A : Type} [Fintype A] [DecidableEq A]
    (x : C A) :
    ConvOp.toLin ((HoAlgebra.equivTwisting φ).1.1 A) x = φ.1.app A (Cobar.ιL R C A x) := rfl

end HoAlgebra

end Operad
