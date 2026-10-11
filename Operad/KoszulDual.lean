/-
# The Koszul dual of a binary quadratic presentation, and its convolution operad

A binary quadratic presentation is a finite set `E` of binary generators and a space `Rel` of
relations among the two-vertex trees. Chains are the functions on trees of each arity (finitely
many, `BTree.OfArity.instFintype`), and a cochain `f ∈ TConv R E Q n` is evaluated on a chain by
`eval f x = Σₜ x t • f t`.

* **Slices.** Cutting at the slot `a` splits a chain of arity `a + n + b` into its outer slice
  at an inner tree `t₂` and its inner slice at an outer tree `t₁`; a composite of cochains is
  evaluated along slices (`eval_comp_outer`, `eval_comp_inner`).
* **Annihilators.** For a slice-closed collection `C` of chains the cochains vanishing on `C` form
  an ideal of the convolution operad (`ann`); the quotient is the convolution operad `Hom(C, Q)`
  (`HomOp`), whose element of arity `n` is determined by its values on `C n`.
* **The Koszul dual.** `koszulDual Rel` is everything in arities one and two, `Rel` in arity
  three, and from arity four on the chains all of whose proper slices lie in it in lower arity.
  It is slice-closed (`koszulDual_sliceClosed`), so it is the Koszul dual cooperad of the
  presentation and `HomOp (koszulDual Rel)` its convolution operad with coefficients in `Q`: the
  signed total space of that operad is the convolution dg Lie algebra of the presentation, with
  the twisted differentials and cohomology of `Operad.Cohomology`.
-/
import Operad.TreeConv
import Mathlib.Algebra.BigOperators.Fin

universe u v w

namespace Operad

open NSOperad BTree

variable {R : Type u} [CommRing R] {E : Type v}
  {Q : ℕ → Type w} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

namespace TConv

variable (R E) in
/-- **Chains**: the functions on the trees of a given arity. -/
abbrev Chain (n : ℕ) : Type (max u v) := OfArity E n → R

/-- **The outer slice** of a chain at an inner tree. -/
def outerSlice (a b : ℕ) {n : ℕ} (t₂ : OfArity E n) :
    Chain R E (a + n + b) →ₗ[R] Chain R E (a + 1 + b) where
  toFun x t₁ := x (OfArity.graft a b t₁ t₂)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The inner slice** of a chain at an outer tree. -/
def innerSlice (a b : ℕ) {n : ℕ} (t₁ : OfArity E (a + 1 + b)) :
    Chain R E (a + n + b) →ₗ[R] Chain R E n where
  toFun x t₂ := x (OfArity.graft a b t₁ t₂)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma outerSlice_apply (a b : ℕ) {n : ℕ} (t₂ : OfArity E n) (x : Chain R E (a + n + b))
    (t₁ : OfArity E (a + 1 + b)) : outerSlice a b t₂ x t₁ = x (OfArity.graft a b t₁ t₂) := rfl

@[simp] lemma innerSlice_apply (a b : ℕ) {n : ℕ} (t₁ : OfArity E (a + 1 + b))
    (x : Chain R E (a + n + b)) (t₂ : OfArity E n) :
    innerSlice a b t₁ x t₂ = x (OfArity.graft a b t₁ t₂) := rfl

variable (R E) in
/-- **A slice-closed collection of chains**: a sub-collection of the cofree cooperad. -/
structure SliceClosed (C : ∀ n, Submodule R (Chain R E n)) : Prop where
  outer {a b n : ℕ} {x : Chain R E (a + n + b)} (hx : x ∈ C (a + n + b)) (t₂ : OfArity E n) :
    outerSlice a b t₂ x ∈ C (a + 1 + b)
  inner {a b n : ℕ} {x : Chain R E (a + n + b)} (hx : x ∈ C (a + n + b))
    (t₁ : OfArity E (a + 1 + b)) : innerSlice a b t₁ x ∈ C n

/-! ## The Koszul dual of a quadratic presentation -/

/-- **The Koszul dual** of the presentation with relations `Rel` among the two-vertex trees:
everything in arities at most two, `Rel` in arity three, and from arity four on the chains all
of whose proper slices lie in it. -/
def koszulDual (Rel : Submodule R (Chain R E 3)) : (n : ℕ) → Submodule R (Chain R E n)
  | 0 => ⊤
  | 1 => ⊤
  | 2 => ⊤
  | 3 => Rel
  | m + 4 =>
    { carrier := {x | ∀ (a b k : ℕ) (h : a + k + b = m + 4), 2 ≤ k → 1 ≤ a + b →
        (∀ t₂ : OfArity E k, outerSlice a b t₂ (fun t => x (OfArity.cast h t))
          ∈ koszulDual Rel (a + 1 + b)) ∧
        (∀ t₁ : OfArity E (a + 1 + b), innerSlice a b t₁ (fun t => x (OfArity.cast h t))
          ∈ koszulDual Rel k)}
      add_mem' := fun {x y} hx hy a b k h hk hab => by
        refine ⟨fun t₂ => ?_, fun t₁ => ?_⟩
        · exact (koszulDual Rel (a + 1 + b)).add_mem ((hx a b k h hk hab).1 t₂)
            ((hy a b k h hk hab).1 t₂)
        · exact (koszulDual Rel k).add_mem ((hx a b k h hk hab).2 t₁) ((hy a b k h hk hab).2 t₁)
      zero_mem' := fun a b k h hk hab => by
        refine ⟨fun t₂ => ?_, fun t₁ => ?_⟩
        · exact (koszulDual Rel (a + 1 + b)).zero_mem
        · exact (koszulDual Rel k).zero_mem
      smul_mem' := fun c x hx a b k h hk hab => by
        refine ⟨fun t₂ => ?_, fun t₁ => ?_⟩
        · exact (koszulDual Rel (a + 1 + b)).smul_mem c ((hx a b k h hk hab).1 t₂)
        · exact (koszulDual Rel k).smul_mem c ((hx a b k h hk hab).2 t₁) }
  decreasing_by all_goals omega

lemma koszulDual_two (Rel : Submodule R (Chain R E 3)) : koszulDual Rel 2 = ⊤ := by
  rw [koszulDual]

lemma koszulDual_one (Rel : Submodule R (Chain R E 3)) : koszulDual Rel 1 = ⊤ := by
  rw [koszulDual]

lemma koszulDual_three (Rel : Submodule R (Chain R E 3)) : koszulDual Rel 3 = Rel := by
  rw [koszulDual]

lemma mem_koszulDual_add_four (Rel : Submodule R (Chain R E 3)) (m : ℕ)
    (x : Chain R E (m + 4)) :
    x ∈ koszulDual Rel (m + 4) ↔ ∀ (a b k : ℕ) (h : a + k + b = m + 4), 2 ≤ k → 1 ≤ a + b →
      (∀ t₂ : OfArity E k, outerSlice a b t₂ (fun t => x (OfArity.cast h t))
        ∈ koszulDual Rel (a + 1 + b)) ∧
      (∀ t₁ : OfArity E (a + 1 + b), innerSlice a b t₁ (fun t => x (OfArity.cast h t))
        ∈ koszulDual Rel k) := by
  rw [koszulDual]
  rfl

/-- In arity at most two every chain is in the Koszul dual. -/
lemma mem_koszulDual_of_le_two (Rel : Submodule R (Chain R E 3)) {n : ℕ} (hn : n ≤ 2)
    (x : Chain R E n) : x ∈ koszulDual Rel n := by
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl <;>
    (rw [koszulDual]; exact Submodule.mem_top)

/-- A chain of arity one is a multiple of the leaf. -/
lemma slice_trivial_outer (a b : ℕ) (x : Chain R E (a + 1 + b)) :
    outerSlice (R := R) a b OfArity.one x = x := by
  funext t₁
  rw [outerSlice_apply]
  congr 1
  exact Subtype.ext (graft_leaf_right t₁.1 a)

/-- Transport of membership along an equality of arities. -/
lemma mem_koszulDual_cast (Rel : Submodule R (Chain R E 3)) {m n : ℕ} (h : m = n)
    {x : Chain R E n} (hx : x ∈ koszulDual Rel n) :
    (fun t => x (OfArity.cast h t)) ∈ koszulDual Rel m := by
  subst h
  exact hx

/-- **The Koszul dual is slice-closed**: it is a sub-cooperad of the cofree cooperad. -/
theorem koszulDual_sliceClosed (Rel : Submodule R (Chain R E 3)) :
    SliceClosed R E (koszulDual Rel) where
  outer {a b n x} hx t₂ := by
    by_cases hn : n = 1
    · subst hn
      have ht₂ : t₂ = OfArity.one := eq_one t₂
      subst ht₂
      rw [slice_trivial_outer]
      exact hx
    by_cases hab : a + b = 0
    · exact mem_koszulDual_of_le_two Rel (by omega) _
    have hn2 : 2 ≤ n := by
      have := t₂.2
      have := arity_pos t₂.1
      omega
    by_cases hbig : a + n + b ≤ 3
    · exact mem_koszulDual_of_le_two Rel (by omega) _
    obtain ⟨m, hm⟩ : ∃ m, a + n + b = m + 4 := ⟨a + n + b - 4, by omega⟩
    have hx' : (fun t : OfArity E (m + 4) => x (OfArity.cast hm.symm t))
        ∈ koszulDual Rel (m + 4) := mem_koszulDual_cast Rel hm.symm hx
    rw [mem_koszulDual_add_four] at hx'
    have := (hx' a b n hm hn2 (by omega)).1 t₂
    simpa using this
  inner {a b n x} hx t₁ := by
    by_cases hab : a + b = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha
      subst hb
      have ht₁ : t₁ = OfArity.cast (by omega) (OfArity.one (E := E)) := Subtype.ext
        (eq_leaf_of_arity_eq_one (by rw [t₁.2]))
      subst ht₁
      have : innerSlice (R := R) 0 0 (OfArity.cast (by omega) OfArity.one) x
          = fun t => x (OfArity.cast (by omega) t) := by
        funext t₂
        rw [innerSlice_apply]
        congr 1
      rw [this]
      exact mem_koszulDual_cast Rel (by omega) hx
    by_cases hn : n ≤ 2
    · exact mem_koszulDual_of_le_two Rel hn _
    by_cases hbig : a + n + b ≤ 3
    · exfalso
      omega
    obtain ⟨m, hm⟩ : ∃ m, a + n + b = m + 4 := ⟨a + n + b - 4, by omega⟩
    have hx' : (fun t : OfArity E (m + 4) => x (OfArity.cast hm.symm t))
        ∈ koszulDual Rel (m + 4) := mem_koszulDual_cast Rel hm.symm hx
    rw [mem_koszulDual_add_four] at hx'
    have := (hx' a b n hm (by omega) (by omega)).2 t₁
    simpa using this

/-! ## Evaluation, and annihilators -/

section Eval

variable [Fintype E] [DecidableEq E]

/-- **Evaluation of a cochain on a chain.** -/
def eval {n : ℕ} (f : TConv R E Q n) : Chain R E n →ₗ[R] Q n where
  toFun x := ∑ t, x t • f t
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

omit [NSOperad R Q] in
lemma eval_apply {n : ℕ} (f : TConv R E Q n) (x : Chain R E n) :
    eval f x = ∑ t, x t • f t := rfl

omit [NSOperad R Q] in
lemma eval_add {n : ℕ} (f g : TConv R E Q n) (x : Chain R E n) :
    eval (f + g) x = eval f x + eval g x := by
  simp only [eval_apply, Pi.add_apply, smul_add, Finset.sum_add_distrib]

omit [NSOperad R Q] in
lemma eval_smul {n : ℕ} (c : R) (f : TConv R E Q n) (x : Chain R E n) :
    eval (c • f) x = c • eval f x := by
  simp only [eval_apply, Pi.smul_apply, Finset.smul_sum, smul_comm c]

omit [NSOperad R Q] in
lemma eval_neg {n : ℕ} (f : TConv R E Q n) (x : Chain R E n) : eval (-f) x = -eval f x := by
  simp only [eval_apply, Pi.neg_apply, smul_neg, Finset.sum_neg_distrib]

omit [NSOperad R Q] in
lemma eval_sub {n : ℕ} (f g : TConv R E Q n) (x : Chain R E n) :
    eval (f - g) x = eval f x - eval g x := by
  simp only [eval_apply, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

omit [NSOperad R Q] in
@[simp] lemma eval_zero {n : ℕ} (x : Chain R E n) : eval (0 : TConv R E Q n) x = 0 := by
  simp [eval_apply]

omit [NSOperad R Q] in
/-- Evaluation on the indicator of a tree. -/
lemma eval_single {n : ℕ} (f : TConv R E Q n) (t : OfArity E n) (r : R) :
    eval f (Pi.single t r) = r • f t := by
  rw [eval_apply, Finset.sum_eq_single t]
  · rw [Pi.single_eq_same]
  · intro s _ hs
    rw [Pi.single_eq_of_ne hs, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ t) h

omit [NSOperad R Q] in
/-- A cochain is determined by its values on chains. -/
lemma ext_eval {n : ℕ} {f g : TConv R E Q n} (h : ∀ x, eval f x = eval g x) : f = g :=
  funext fun t => by simpa [eval_single] using h (Pi.single t 1)

/-- A composite of cochains, evaluated on a chain, as a sum over the factorizations. -/
lemma eval_comp_pairs (a b : ℕ) {n : ℕ} (f : TConv R E Q (a + 1 + b)) (g : TConv R E Q n)
    (x : Chain R E (a + n + b)) :
    eval (compL a b f g) x = ∑ p : OfArity E (a + 1 + b) × OfArity E n,
      x (OfArity.graft a b p.1 p.2) • NSOperad.comp (R := R) a b (f p.1) (g p.2) := by
  rw [eval_apply]
  refine (Fintype.sum_of_injective (fun p : OfArity E (a + 1 + b) × OfArity E n =>
      OfArity.graft a b p.1 p.2) (fun p q h => ?_) _ _ (fun t ht => ?_) (fun p => ?_)).symm
  · obtain ⟨h1, h2⟩ := OfArity.graft_inj a b h
    exact Prod.ext h1 h2
  · rw [compL_apply, compFun_eq_zero a b f g (fun t₁ t₂ h => ht ⟨(t₁, t₂), Subtype.ext h⟩),
      smul_zero]
  · rw [compL_apply, compFun_eq a b f g p.1 p.2 rfl]

/-- **Evaluating a composite along outer slices.** -/
theorem eval_comp_outer (a b : ℕ) {n : ℕ} (f : TConv R E Q (a + 1 + b)) (g : TConv R E Q n)
    (x : Chain R E (a + n + b)) :
    eval (compL a b f g) x
      = ∑ t₂, NSOperad.comp (R := R) a b (eval f (outerSlice a b t₂ x)) (g t₂) := by
  rw [eval_comp_pairs, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun t₂ _ => ?_
  rw [eval_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  rw [map_smul, LinearMap.smul_apply, outerSlice_apply]

/-- **Evaluating a composite along inner slices.** -/
theorem eval_comp_inner (a b : ℕ) {n : ℕ} (f : TConv R E Q (a + 1 + b)) (g : TConv R E Q n)
    (x : Chain R E (a + n + b)) :
    eval (compL a b f g) x
      = ∑ t₁, NSOperad.comp (R := R) a b (f t₁) (eval g (innerSlice a b t₁ x)) := by
  rw [eval_comp_pairs, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  rw [eval_apply, map_sum]
  refine Finset.sum_congr rfl fun t₂ _ => ?_
  rw [map_smul, innerSlice_apply]

/-! ## Annihilators of slice-closed collections -/

variable (Q) in
/-- **The annihilator of a slice-closed collection**, an ideal of the convolution operad. -/
def ann {C : ∀ n, Submodule R (Chain R E n)} (hC : SliceClosed R E C) :
    OperadIdeal R (TConv R E Q) where
  carrier n :=
    { carrier := {f | ∀ x ∈ C n, eval f x = 0}
      add_mem' := fun hf hg x hx => by rw [eval_add, hf x hx, hg x hx, add_zero]
      zero_mem' := fun x _ => eval_zero x
      smul_mem' := fun c f hf x hx => by rw [eval_smul, hf x hx, smul_zero] }
  comp_mem_left a b n f hf g x hx := by
    show eval (compL a b f g) x = 0
    rw [eval_comp_outer]
    exact Finset.sum_eq_zero fun t₂ _ => by
      rw [hf _ (hC.outer hx t₂), map_zero, LinearMap.zero_apply]
  comp_mem_right a b n f g hg x hx := by
    show eval (compL a b f g) x = 0
    rw [eval_comp_inner]
    exact Finset.sum_eq_zero fun t₁ _ => by rw [hg _ (hC.inner hx t₁), map_zero]

lemma mem_ann {C : ∀ n, Submodule R (Chain R E n)} (hC : SliceClosed R E C) {n : ℕ}
    (f : TConv R E Q n) : f ∈ (ann Q hC).carrier n ↔ ∀ x ∈ C n, eval f x = 0 := Iff.rfl

variable (Q) in
/-- **The convolution operad `Hom(C, Q)`** of a slice-closed collection of chains. -/
abbrev HomOp {C : ∀ n, Submodule R (Chain R E n)} (hC : SliceClosed R E C) : ℕ → Type (max v w) :=
  (ann Q hC).Quot

end Eval

end TConv

end Operad
