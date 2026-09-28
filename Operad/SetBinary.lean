/-
# Binary operations in a set operad

A binary element `g : S (Fin 2)` of a set operad acts on the operad itself: `bin g x y`, for
`x : S A` and `y : S B`, fills the two inputs of `g` with `x` and `y`, and has inputs `A ⊕ B`.
This is the calculus in which quadratic presentations are verified:

* relabellings move to the outside (`bin_map_left`, `bin_map_right`, `comp_map_left_of`,
  `comp_map_right`) and merge (`map_map`), so that every expression becomes a relabelling of a
  tree of `bin`s, and two such agree when the relabellings agree pointwise;
* composing into an input of `bin g u v` composes into `u` or `v` (`comp_inl_bin`,
  `comp_inr_bin`), and `bin g one one` is `g` (`bin_one_one`);
* a relation between two-fold composites of generators, stated with identities in the three
  leaves, holds with arbitrary elements in the leaves (`bin_assoc_of`, `bin_right_of`). This is
  the step from a relator in arity three to the identity it imposes on every algebra, and it is
  proved by substituting into the three leaves (`subst3`).

The first input of `g` is `0 : Fin 2` and the second is `1`; after filling the first, the second
is `slotOne : Without (Fin 2) 0`.
-/
import Operad.SetOperad

/-! The input types below are nested sums of subtypes, and deciding equality on them takes more
instances than the default search allows. -/
set_option synthInstance.maxSize 1024

universe v

namespace Operad

open Sym

namespace Sym

/-- The second input of a binary operation, once the first has been filled. -/
def slotOne : Without (Fin 2) 0 := ⟨1, by decide⟩

lemma eq_slotOne (j : Without (Fin 2) 0) : j = slotOne := by
  obtain ⟨k, hk⟩ := j
  have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
  have : k = 1 := Fin.ext (by have := k.isLt; simp only [Fin.isValue, Fin.val_one]; omega)
  subst this
  rfl

lemma ne_slotOne {A : Type} {j : Without (Fin 2) 0}
    (h : (Sum.inl j : Without (Fin 2) 0 ⊕ A) ≠ Sum.inl slotOne) : False :=
  h (congrArg Sum.inl (eq_slotOne j))

/-- The inputs of a binary operation with both inputs filled, in order. -/
def binEquiv (A B : Type) [DecidableEq A] :
    Without (Without (Fin 2) 0 ⊕ A) (Sum.inl slotOne) ⊕ B ≃ A ⊕ B where
  toFun x :=
    match x with
    | Sum.inl ⟨Sum.inl _, h⟩ => (ne_slotOne h).elim
    | Sum.inl ⟨Sum.inr a, _⟩ => Sum.inl a
    | Sum.inr b => Sum.inr b
  invFun x :=
    match x with
    | Sum.inl a => Sum.inl ⟨Sum.inr a, by simp⟩
    | Sum.inr b => Sum.inr b
  left_inv := by
    rintro (⟨j | a, h⟩ | b)
    · exact (ne_slotOne h).elim
    · rfl
    · rfl
  right_inv := by rintro (a | b) <;> rfl

@[simp] lemma binEquiv_inl_inr (A B : Type) [DecidableEq A] (a : A) (h) :
    binEquiv A B (Sum.inl ⟨Sum.inr a, h⟩) = Sum.inl a := rfl

@[simp] lemma binEquiv_inr (A B : Type) [DecidableEq A] (b : B) :
    binEquiv A B (Sum.inr b) = Sum.inr b := rfl

/-- The two inputs of a binary operation as `Unit ⊕ Unit`. -/
def finTwoSum : Fin 2 ≃ Unit ⊕ Unit where
  toFun k := if k = 0 then Sum.inl () else Sum.inr ()
  invFun x :=
    match x with
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  left_inv := by decide
  right_inv := by rintro (⟨⟩ | ⟨⟩) <;> rfl

/-- The inputs of `bin g u v ∘ᵢ y` when `i` is an input of `u`. -/
def binLeftEquiv {A B C : Type} [DecidableEq A] [DecidableEq B] (a : A) :
    (Without A a ⊕ C) ⊕ B ≃ Without (A ⊕ B) (Sum.inl a) ⊕ C where
  toFun x :=
    match x with
    | Sum.inl (Sum.inl a') => Sum.inl ⟨Sum.inl a'.1, fun h => a'.2 (Sum.inl_injective h)⟩
    | Sum.inl (Sum.inr c) => Sum.inr c
    | Sum.inr b => Sum.inl ⟨Sum.inr b, by simp⟩
  invFun x :=
    match x with
    | Sum.inl ⟨Sum.inl a', h⟩ => Sum.inl (Sum.inl ⟨a', fun h' => h (congrArg Sum.inl h')⟩)
    | Sum.inl ⟨Sum.inr b, _⟩ => Sum.inr b
    | Sum.inr c => Sum.inl (Sum.inr c)
  left_inv := by rintro ((a' | c) | b) <;> rfl
  right_inv := by rintro (⟨a' | b, h⟩ | c) <;> rfl

/-- The inputs of `bin g u v ∘ᵢ y` when `i` is an input of `v`. -/
def binRightEquiv {A B C : Type} [DecidableEq A] [DecidableEq B] (b : B) :
    A ⊕ (Without B b ⊕ C) ≃ Without (A ⊕ B) (Sum.inr b) ⊕ C where
  toFun x :=
    match x with
    | Sum.inl a => Sum.inl ⟨Sum.inl a, by simp⟩
    | Sum.inr (Sum.inl b') => Sum.inl ⟨Sum.inr b'.1, fun h => b'.2 (Sum.inr_injective h)⟩
    | Sum.inr (Sum.inr c) => Sum.inr c
  invFun x :=
    match x with
    | Sum.inl ⟨Sum.inl a, _⟩ => Sum.inl a
    | Sum.inl ⟨Sum.inr b', h⟩ => Sum.inr (Sum.inl ⟨b', fun h' => h (congrArg Sum.inr h')⟩)
    | Sum.inr c => Sum.inr (Sum.inr c)
  left_inv := by rintro (a | (b' | c)) <;> rfl
  right_inv := by rintro (⟨a | b', h⟩ | c) <;> rfl

/-! ### Substituting at three inputs -/

section Subst3

variable {L : Type} [DecidableEq L]

/-- The second input, once the first has been filled. -/
def subst3Slot₂ (ℓ : Fin 3 ≃ L) (A : Type) : Without L (ℓ 0) ⊕ A :=
  Sum.inl ⟨ℓ 1, ℓ.injective.ne (by decide)⟩

/-- The third input, once the first two have been filled. -/
def subst3Slot₃ (ℓ : Fin 3 ≃ L) (A B : Type) [DecidableEq A] :
    Without (Without L (ℓ 0) ⊕ A) (subst3Slot₂ ℓ A) ⊕ B :=
  Sum.inl ⟨Sum.inl ⟨ℓ 2, ℓ.injective.ne (by decide)⟩, fun h =>
    ℓ.injective.ne (show (2 : Fin 3) ≠ 1 by decide) (congrArg Subtype.val (Sum.inl_injective h))⟩

lemma subst3_absurd {A B : Type} [DecidableEq A] (ℓ : Fin 3 ≃ L) {l : L} {h0 : l ≠ ℓ 0}
    {h1 : (Sum.inl ⟨l, h0⟩ : Without L (ℓ 0) ⊕ A) ≠ subst3Slot₂ ℓ A}
    (h2 : (Sum.inl ⟨Sum.inl ⟨l, h0⟩, h1⟩ : Without (Without L (ℓ 0) ⊕ A) (subst3Slot₂ ℓ A) ⊕ B)
      ≠ subst3Slot₃ ℓ A B) : False := by
  obtain ⟨k, rfl⟩ := ℓ.surjective l
  fin_cases k
  · exact h0 rfl
  · exact h1 rfl
  · exact h2 rfl

/-- The inputs after substituting at the three inputs `ℓ 0`, `ℓ 1`, `ℓ 2` of an operation with
exactly those inputs. -/
def subst3Equiv (ℓ : Fin 3 ≃ L) (A B C : Type) [DecidableEq A] [DecidableEq B] :
    Without (Without (Without L (ℓ 0) ⊕ A) (subst3Slot₂ ℓ A) ⊕ B) (subst3Slot₃ ℓ A B) ⊕ C
      ≃ (A ⊕ B) ⊕ C where
  toFun x :=
    match x with
    | Sum.inl ⟨Sum.inl ⟨Sum.inl _, _⟩, h⟩ => (subst3_absurd ℓ h).elim
    | Sum.inl ⟨Sum.inl ⟨Sum.inr a, _⟩, _⟩ => Sum.inl (Sum.inl a)
    | Sum.inl ⟨Sum.inr b, _⟩ => Sum.inl (Sum.inr b)
    | Sum.inr c => Sum.inr c
  invFun x :=
    match x with
    | Sum.inl (Sum.inl a) =>
        Sum.inl ⟨Sum.inl ⟨Sum.inr a, by simp [subst3Slot₂]⟩, by simp [subst3Slot₃]⟩
    | Sum.inl (Sum.inr b) => Sum.inl ⟨Sum.inr b, by simp [subst3Slot₃]⟩
    | Sum.inr c => Sum.inr c
  left_inv := by
    rintro (⟨⟨⟨l, h0⟩ | a, h1⟩ | b, h2⟩ | c)
    · exact (subst3_absurd ℓ h2).elim
    · rfl
    · rfl
    · rfl
  right_inv := by rintro ((a | b) | c) <;> rfl

/-- The leaves of a left comb, in order. -/
def fin3Left : Fin 3 ≃ (Unit ⊕ Unit) ⊕ Unit where
  toFun k := if k = 0 then Sum.inl (Sum.inl ()) else if k = 1 then Sum.inl (Sum.inr ()) else Sum.inr ()
  invFun x :=
    match x with
    | Sum.inl (Sum.inl _) => 0
    | Sum.inl (Sum.inr _) => 1
    | Sum.inr _ => 2
  left_inv := by decide
  right_inv := by rintro ((⟨⟩ | ⟨⟩) | ⟨⟩) <;> rfl

/-- The leaves of a right comb, in order. -/
def fin3Right : Fin 3 ≃ Unit ⊕ (Unit ⊕ Unit) where
  toFun k := if k = 0 then Sum.inl () else if k = 1 then Sum.inr (Sum.inl ()) else Sum.inr (Sum.inr ())
  invFun x :=
    match x with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr _) => 2
  left_inv := by decide
  right_inv := by rintro (⟨⟩ | (⟨⟩ | ⟨⟩)) <;> rfl

lemma fin3Right_eq : fin3Right = fin3Left.trans (Equiv.sumAssoc Unit Unit Unit) := by
  ext k
  fin_cases k <;> rfl

end Subst3

end Sym

namespace SetOperad

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]

/-! ## Moving relabellings -/

section Moves

variable {A A' B B' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C]

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
@[simp] lemma map_map (e : A ≃ B) (f : B ≃ C) (x : S A) : map f (map e x) = map (e.trans f) x :=
  (map_trans e f x).symm

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
lemma map_congr {e f : A ≃ B} (h : ∀ a, e a = f a) (x : S A) : map e x = map f x := by
  rw [Equiv.ext h]

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype C] [DecidableEq C] in
lemma map_eq_self {e : A ≃ A} (h : ∀ a, e a = a) (x : S A) : map e x = x := by
  rw [map_congr (f := Equiv.refl A) h, map_refl]

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
lemma eq_map_symm_of_map_eq {e : A ≃ B} {x : S A} {y : S B} (h : map e x = y) :
    x = map e.symm y := by
  rw [← h, map_symm_map]

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype C] [DecidableEq C] in
/-- The right unit, solved for the composite. -/
lemma comp_one' (i : A) (x : S A) : comp i x one = map (rightUnitEquiv i).symm x :=
  eq_map_symm_of_map_eq (comp_one i x)

omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
  [Fintype C] [DecidableEq C] in
/-- The left unit, solved for the composite. -/
lemma one_comp' (y : S B) : comp () one y = map (leftUnitEquiv B).symm y :=
  eq_map_symm_of_map_eq (one_comp y)

omit [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
lemma comp_map_left (σ : A ≃ A') (i : A) (x : S A) (y : S B) :
    comp (σ i) (map σ x) y = map (compEquiv σ (Equiv.refl B) i) (comp i x y) := by
  rw [map_comp, map_refl]

omit [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] in
lemma comp_map_right (τ : B ≃ B') (i : A) (x : S A) (y : S B) :
    comp i x (map τ y) = map (Equiv.sumCongr (Equiv.refl (Without A i)) τ) (comp i x y) := by
  have h := map_comp (S := S) (Equiv.refl A) τ i x y
  rw [map_refl] at h
  have e : compEquiv (Equiv.refl A) τ i = Equiv.sumCongr (Equiv.refl (Without A i)) τ := by
    ext c; rcases c with a | b <;> rfl
  rw [e] at h
  exact h.symm

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
/-- Composing at two equal inputs. -/
lemma comp_slot {i i' : A} (h : i = i') (x : S A) (y : S B) :
    comp i' x y = map (slotEquiv h) (comp i x y) := by
  subst h
  exact (map_eq_self (fun c => by rcases c with a | b <;> rfl) _).symm

omit [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
/-- **Relabelling the outer operation of a composite**, with the input named on either side. Used
as `rw [comp_map_left_of _ (i := i) ?h]`, which leaves `σ i = i'` to be closed by `rfl`. -/
lemma comp_map_left_of (σ : A ≃ A') {i : A} {i' : A'} (h : σ i = i') (x : S A) (y : S B) :
    comp i' (map σ x) y
      = map ((compEquiv σ (Equiv.refl B) i).trans (slotEquiv h)) (comp i x y) := by
  subst h
  rw [comp_map_left]
  exact map_congr (fun c => by rcases c with a | b <;> rfl) _

end Moves

/-! ## Filling both inputs of a binary operation -/

section Binary

variable {A A' B B' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C]

/-- **Fill the two inputs of a binary operation.** -/
def bin (g : S (Fin 2)) (x : S A) (y : S B) : S (A ⊕ B) :=
  map (binEquiv A B) (comp (Sum.inl slotOne) (comp (0 : Fin 2) g x) y)

omit [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
lemma bin_map_left (g : S (Fin 2)) (σ : A ≃ A') (x : S A) (y : S B) :
    bin g (map σ x) y = map (Equiv.sumCongr σ (Equiv.refl B)) (bin g x y) := by
  unfold bin
  rw [comp_map_right, comp_map_left_of _ (i := Sum.inl slotOne) ?h]
  · simp only [map_map]
    refine map_congr (fun c => ?_) _
    rcases c with ⟨j | a, hj⟩ | b
    · exact (ne_slotOne hj).elim
    · rfl
    · rfl
  · rfl

omit [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] in
lemma bin_map_right (g : S (Fin 2)) (τ : B ≃ B') (x : S A) (y : S B) :
    bin g x (map τ y) = map (Equiv.sumCongr (Equiv.refl A) τ) (bin g x y) := by
  unfold bin
  rw [comp_map_right]
  simp only [map_map]
  refine map_congr (fun c => ?_) _
  rcases c with ⟨j | a, hj⟩ | b
  · exact (ne_slotOne hj).elim
  · rfl
  · rfl

omit [Fintype C] [DecidableEq C] in
lemma bin_map (g : S (Fin 2)) (σ : A ≃ A') (τ : B ≃ B') (x : S A) (y : S B) :
    bin g (map σ x) (map τ y) = map (Equiv.sumCongr σ τ) (bin g x y) := by
  rw [bin_map_left, bin_map_right, map_map]
  exact map_congr (fun c => by rcases c with a | b <;> rfl) _

omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B]
  [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
/-- **Filling both inputs with the identity** gives back the operation. -/
lemma bin_one_one (g : S (Fin 2)) : bin g one one = map finTwoSum g := by
  unfold bin
  rw [comp_one', comp_one']
  simp only [map_map]
  exact map_congr (fun k => by fin_cases k <;> rfl) _

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
/-- **The transposed operation** fills its inputs in the other order. -/
lemma bin_swap (g : S (Fin 2)) (x : S A) (y : S B) :
    bin (map (Equiv.swap 0 1) g) x y = map (Equiv.sumComm B A) (bin g y x) := by
  unfold bin
  rw [comp_map_left_of _ (i := (1 : Fin 2)) ?h1,
    comp_map_left_of _ (i := Sum.inl (⟨0, by decide⟩ : Without (Fin 2) 1)) ?h2,
    eq_map_symm_of_map_eq (comp_assoc_par (show (1 : Fin 2) ≠ 0 by decide) g x y)]
  · simp only [map_map]
    refine map_congr (fun c => ?_) _
    rcases c with ⟨j | b, hj⟩ | a
    · exact (ne_slotOne hj).elim
    · rfl
    · rfl
  · rfl
  · rfl

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
/-- **Composing into the first argument** of a filled binary operation. -/
lemma comp_inl_bin (g : S (Fin 2)) (a : A) (u : S A) (v : S B) (y : S C) :
    comp (Sum.inl a) (bin g u v) y = map (binLeftEquiv a) (bin g (comp a u y) v) := by
  unfold bin
  rw [comp_map_left_of _ (i := Sum.inl ⟨Sum.inr a, by simp⟩) ?h1,
    eq_map_symm_of_map_eq (comp_assoc_par
      (show (Sum.inl slotOne : Without (Fin 2) 0 ⊕ A) ≠ Sum.inr a by simp) (comp 0 g u) v y),
    eq_map_symm_of_map_eq (comp_assoc_seq (0 : Fin 2) a g u y),
    comp_map_left_of _ (i := Sum.inl slotOne) ?h2]
  · simp only [map_map]
    refine map_congr (fun c => ?_) _
    rcases c with ⟨j | (a' | c), hj⟩ | b
    · exact (ne_slotOne hj).elim
    · rfl
    · rfl
    · rfl
  · rfl
  · rfl

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
/-- **Composing into the second argument** of a filled binary operation. -/
lemma comp_inr_bin (g : S (Fin 2)) (b : B) (u : S A) (v : S B) (y : S C) :
    comp (Sum.inr b) (bin g u v) y = map (binRightEquiv b) (bin g u (comp b v y)) := by
  unfold bin
  rw [comp_map_left_of _ (i := Sum.inr b) ?h1,
    eq_map_symm_of_map_eq (comp_assoc_seq (Sum.inl slotOne) b (comp 0 g u) v y)]
  · simp only [map_map]
    refine map_congr (fun c => ?_) _
    rcases c with ⟨j | a, hj⟩ | (b' | c)
    · exact (ne_slotOne hj).elim
    · rfl
    · rfl
    · rfl
  · rfl

end Binary

/-! ## Substituting into three inputs -/

section Subst3

variable {A B C L L' : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L']

/-- **Substitute** `x`, `y`, `z` at the inputs `ℓ 0`, `ℓ 1`, `ℓ 2` of an operation with three
inputs. -/
def subst3 (P : S L) (ℓ : Fin 3 ≃ L) (x : S A) (y : S B) (z : S C) : S ((A ⊕ B) ⊕ C) :=
  map (subst3Equiv ℓ A B C)
    (comp (subst3Slot₃ ℓ A B) (comp (subst3Slot₂ ℓ A) (comp (ℓ 0) P x) y) z)

/-- Substitution does not see how the three inputs are named. -/
lemma subst3_map (σ : L ≃ L') (P : S L) (ℓ : Fin 3 ≃ L) (x : S A) (y : S B) (z : S C) :
    subst3 (map σ P) (ℓ.trans σ) x y z = subst3 P ℓ x y z := by
  unfold subst3
  rw [comp_map_left_of σ (i := ℓ 0) ?h1, comp_map_left_of _ (i := subst3Slot₂ ℓ A) ?h2,
    comp_map_left_of _ (i := subst3Slot₃ ℓ A B) ?h3]
  · simp only [map_map]
    refine map_congr (fun c => ?_) _
    rcases c with ⟨⟨⟨l, h0⟩ | a, h1⟩ | b, h2⟩ | c
    · exact (subst3_absurd ℓ h2).elim
    · rfl
    · rfl
    · rfl
  all_goals rfl

omit [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L'] in
/-- **Substituting into a left comb of identities** gives the left comb of the arguments. -/
lemma subst3_bin_left (p q : S (Fin 2)) (x : S A) (y : S B) (z : S C) :
    subst3 (bin p (bin q one one) one) fin3Left x y z = bin p (bin q x y) z := by
  unfold subst3
  rw [comp_slot (i := Sum.inl (Sum.inl ())) (i' := fin3Left 0) rfl,
    comp_inl_bin p (Sum.inl ()) (bin q one one) one x, comp_inl_bin q () one one x, one_comp']
  simp only [bin_map_left, map_map]
  rw [comp_map_left_of _ (i := Sum.inl (Sum.inr ())) ?h1,
    comp_inl_bin p (Sum.inr ()) (bin q x one) one y, comp_inr_bin q () x one y, one_comp']
  simp only [bin_map_left, bin_map_right, map_map]
  rw [comp_map_left_of _ (i := Sum.inr ()) ?h2, comp_inr_bin p () (bin q x y) one z, one_comp']
  simp only [bin_map_right, map_map]
  · exact map_eq_self (fun c => by rcases c with (a | b) | c <;> rfl) _
  all_goals rfl

omit [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L'] in
/-- **Substituting into a right comb of identities** gives the right comb of the arguments. -/
lemma subst3_bin_right (p q : S (Fin 2)) (x : S A) (y : S B) (z : S C) :
    subst3 (bin p one (bin q one one)) fin3Right x y z
      = map (Equiv.sumAssoc A B C).symm (bin p x (bin q y z)) := by
  unfold subst3
  rw [comp_slot (i := Sum.inl ()) (i' := fin3Right 0) rfl,
    comp_inl_bin p () one (bin q one one) x, one_comp']
  simp only [bin_map_left, map_map]
  rw [comp_map_left_of _ (i := Sum.inr (Sum.inl ())) ?h1,
    comp_inr_bin p (Sum.inl ()) x (bin q one one) y, comp_inl_bin q () one one y, one_comp']
  simp only [bin_map_left, bin_map_right, map_map]
  rw [comp_map_left_of _ (i := Sum.inr (Sum.inr ())) ?h2,
    comp_inr_bin p (Sum.inr ()) x (bin q y one) z, comp_inr_bin q () y one z, one_comp']
  simp only [bin_map_right, map_map]
  · exact map_congr (fun c => by rcases c with a | (b | c) <;> rfl) _
  all_goals rfl

omit [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L'] in
/-- **An associativity-shaped relator holds generically.** If two composites of generators, one
a left comb and one a right comb, agree with identities in the leaves, they agree with arbitrary
elements in the leaves. -/
theorem bin_assoc_of {p q p' q' : S (Fin 2)}
    (h : map (Equiv.sumAssoc Unit Unit Unit) (bin p (bin q one one) one)
      = bin p' one (bin q' one one))
    (x : S A) (y : S B) (z : S C) :
    map (Equiv.sumAssoc A B C) (bin p (bin q x y) z) = bin p' x (bin q' y z) := by
  have h1 := subst3_bin_right p' q' x y z
  rw [← h, fin3Right_eq, subst3_map, subst3_bin_left] at h1
  rw [h1, map_map_symm]

omit [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L'] in
/-- **A relator between two right combs holds generically.** -/
theorem bin_right_of {p q p' q' : S (Fin 2)}
    (h : bin p one (bin q one one) = bin p' one (bin q' one one))
    (x : S A) (y : S B) (z : S C) :
    bin p x (bin q y z) = bin p' x (bin q' y z) := by
  have h1 := subst3_bin_right p q x y z
  rw [h, subst3_bin_right] at h1
  exact (map_injective _ h1).symm

omit [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L'] in
/-- **A relator between two left combs holds generically.** -/
theorem bin_left_of {p q p' q' : S (Fin 2)}
    (h : bin p (bin q one one) one = bin p' (bin q' one one) one)
    (x : S A) (y : S B) (z : S C) :
    bin p (bin q x y) z = bin p' (bin q' x y) z := by
  have h1 := subst3_bin_left p q x y z
  rw [h, subst3_bin_left] at h1
  exact h1.symm

/-- **Commutativity holds generically.** -/
theorem bin_comm_of {g : S (Fin 2)} (h : map (Equiv.swap 0 1) g = g) (x : S A) (y : S B) :
    bin g y x = map (Equiv.sumComm A B) (bin g x y) := by
  rw [← bin_swap, h]

end Subst3

end SetOperad

end Operad
