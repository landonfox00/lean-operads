/-
# May's definition of an operad

May's definition of an operad uses *total composition* `γ x y : S (Σ a, B a)`, inserting an
operation `y a` at every input `a` of `x` at once, subject to equivariance, two unit laws and
associativity (`MaySetOperad`). The library's definition uses partial composition
(`SetOperad`). This file proves that the two definitions are equivalent.

* **From partial to total composition** (`SetOperad.toMaySetOperad`): total composition and May's
  axioms are built in `Operad.MayOperad`.
* **From total to partial composition** (`MaySetOperad.toSetOperad`): `x ∘ᵢ y` is the total
  composite inserting `y` at `i` and the unit at every other input (`MaySetOperad.comp`); the
  inputs inserted at `a` are those of a *padding* (`May.Pad`), a copy of the inputs of `y` at `i`
  and a single input elsewhere. The axioms of partial composition follow from May's
  (`MaySetOperad.map_comp`, `MaySetOperad.comp_one`, `MaySetOperad.one_comp`,
  `MaySetOperad.comp_assoc_seq`, `MaySetOperad.comp_assoc_par`).
* **The two constructions are inverse to each other** (`MaySetOperad.toSetOperad_toMaySetOperad`,
  `MaySetOperad.toMaySetOperad_toSetOperad`).
-/
import Operad.MayOperad

universe u v w

set_option synthInstance.maxSize 1024

namespace Operad

open Sym May

/-- **An operad in May's sense**: relabelling, a unit, and total composition, subject to
equivariance, the two unit laws and associativity. -/
class MaySetOperad (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) where
  /-- Relabelling the inputs along a bijection. -/
  map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    (A ≃ B) → S A → S B
  map_refl {A : Type} [Fintype A] [DecidableEq A] (x : S A) : map (Equiv.refl A) x = x
  map_trans {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (e : A ≃ B) (f : B ≃ C) (x : S A) :
    map (e.trans f) x = map f (map e x)
  /-- The identity operation. -/
  one : S Unit
  /-- **Total composition**: `y a` inserted at every input `a` of `x`. -/
  total {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
    [∀ a, DecidableEq (B a)] : S A → ((a : A) → S (B a)) → S (Σ a, B a)
  /-- **Equivariance.** -/
  total_map {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    {B : A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {B' : A' → Type} [∀ a, Fintype (B' a)] [∀ a, DecidableEq (B' a)]
    (σ : A ≃ A') (τ : ∀ a, B a ≃ B' (σ a)) (x : S A) (y : (a : A) → S (B a))
    (y' : (a : A') → S (B' a)) (hy : ∀ a, y' (σ a) = map (τ a) (y a)) :
    map (Equiv.sigmaCongr σ τ) (total x y) = total (map σ x) y'
  /-- **The left unit law.** -/
  total_one_left {E : Unit → Type} [∀ u, Fintype (E u)] [∀ u, DecidableEq (E u)]
    (y : (u : Unit) → S (E u)) : map (Equiv.uniqueSigma E) (total one y) = y ()
  /-- **The right unit law.** -/
  total_one_right {A : Type} [Fintype A] [DecidableEq A] (x : S A) :
    map (Equiv.sigmaPUnit A) (total x fun _ => one) = x
  /-- **Associativity.** -/
  total_assoc {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
    [∀ a, DecidableEq (B a)] {C : (a : A) → B a → Type} [∀ a b, Fintype (C a b)]
    [∀ a b, DecidableEq (C a b)] (x : S A) (y : (a : A) → S (B a))
    (z : (a : A) → (b : B a) → S (C a b)) :
    map (Equiv.sigmaAssoc C) (total (total x y) fun p => z p.1 p.2)
      = total x fun a => total (y a) (z a)

/-- **A set operad is an operad in May's sense**, with the total composition of
`Operad.MayOperad`. -/
@[reducible] noncomputable def SetOperad.toMaySetOperad
    (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) [SetOperad S] :
    MaySetOperad S where
  map := SetOperad.map
  map_refl := SetOperad.map_refl
  map_trans := SetOperad.map_trans
  one := SetOperad.one
  total := SetOperad.total
  total_map := SetOperad.total_map
  total_one_left := SetOperad.total_one_left
  total_one_right := SetOperad.total_one_right
  total_assoc := SetOperad.total_assoc

/-! ## Padding -/

namespace May

/-- A sum over the one-element type. -/
def unitSigma (E : Unit → Type) : (Σ u, E u) ≃ E () where
  toFun
    | ⟨(), e⟩ => e
  invFun e := ⟨(), e⟩
  left_inv := by
    rintro ⟨⟨⟩, e⟩
    rfl
  right_inv _ := rfl

section Pad

variable {A : Type} [DecidableEq A]

/-- **The padding**: the inputs inserted at `a` when an operation with inputs `B` is inserted at
`i` and the unit at every other input. -/
abbrev Pad (i : A) (B : Type) (a : A) : Type := {_u : Unit // a ≠ i} ⊕ {_b : B // a = i}

instance Pad.instDecidableEq (i : A) (B : Type) [DecidableEq B] (a : A) :
    DecidableEq (Pad i B a) :=
  inferInstanceAs (DecidableEq ({_u : Unit // a ≠ i} ⊕ {_b : B // a = i}))

instance Pad.instFintype (i : A) (B : Type) [Fintype B] (a : A) : Fintype (Pad i B a) :=
  inferInstanceAs (Fintype ({_u : Unit // a ≠ i} ⊕ {_b : B // a = i}))

/-- At `i`, the padding is a copy of `B`. -/
def padIn {i a : A} {B : Type} (h : a = i) : B ≃ Pad i B a where
  toFun b := Sum.inr ⟨b, h⟩
  invFun
    | Sum.inl ⟨_, h'⟩ => absurd h h'
    | Sum.inr ⟨b, _⟩ => b
  left_inv _ := rfl
  right_inv := by
    rintro (⟨u, h'⟩ | ⟨b, _⟩)
    · exact absurd h h'
    · rfl

/-- Away from `i`, the padding is a single input. -/
def padOut {i a : A} {B : Type} (h : a ≠ i) : Unit ≃ Pad i B a where
  toFun u := Sum.inl ⟨u, h⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv := by
    rintro (⟨⟨⟩, _⟩ | ⟨b, h'⟩)
    · rfl
    · exact absurd h' h

/-- **The inputs of a padded total composite** are those of the partial composite. -/
def padEquiv (i : A) (B : Type) : (Σ a, Pad i B a) ≃ Without A i ⊕ B where
  toFun
    | ⟨a, Sum.inl ⟨_, h⟩⟩ => Sum.inl ⟨a, h⟩
    | ⟨_, Sum.inr ⟨b, _⟩⟩ => Sum.inr b
  invFun
    | Sum.inl a => ⟨a.1, Sum.inl ⟨(), a.2⟩⟩
    | Sum.inr b => ⟨i, Sum.inr ⟨b, rfl⟩⟩
  left_inv := by
    rintro ⟨a, (⟨⟨⟩, h⟩ | ⟨b, rfl⟩)⟩ <;> rfl
  right_inv := by
    rintro (a | b) <;> rfl

end Pad

end May

namespace MaySetOperad

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [MaySetOperad S]

section Relabel

variable {P P' Q : Type} [Fintype P] [DecidableEq P] [Fintype P'] [DecidableEq P']
  [Fintype Q] [DecidableEq Q]

/-- Two relabellings in a row, as one. -/
lemma map_map (e : P ≃ P') (f : P' ≃ Q) (X : S P) : map f (map e X) = map (e.trans f) X :=
  (map_trans e f X).symm

/-- Relabellings along equivalences with the same values agree. -/
lemma map_congr {e e' : P ≃ P'} (h : ∀ p, e p = e' p) (X : S P) : map e X = map e' X := by
  rw [Equiv.ext h]

omit [Fintype Q] [DecidableEq Q] in
lemma map_symm_map (e : P ≃ P') (X : S P) : map e.symm (map e X) = X := by
  rw [map_map, Equiv.self_trans_symm, map_refl]

end Relabel

section Total

variable {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  {W : A → Type} [∀ a, Fintype (W a)] [∀ a, DecidableEq (W a)]
  {W' : A → Type} [∀ a, Fintype (W' a)] [∀ a, DecidableEq (W' a)]
  {V : A' → Type} [∀ a, Fintype (V a)] [∀ a, DecidableEq (V a)]

/-- **Relabelling the inserted operations** relabels the total composite. -/
lemma total_congr (x : S A) (w : (a : A) → S (W a)) (τ : ∀ a, W a ≃ W' a) :
    total x (fun a => map (τ a) (w a)) = map (Equiv.sigmaCongrRight τ) (total x w) := by
  have h := total_map (S := S) (Equiv.refl A) τ x w (fun a => map (τ a) (w a)) fun _ => rfl
  rw [map_refl] at h
  rw [← h]
  exact map_congr (fun _ => rfl) _

/-- **Relabelling the outer operation** relabels the total composite. -/
lemma total_map_left (σ : A ≃ A') (x : S A) (w : (a : A') → S (V a)) :
    total (map σ x) w
      = map (Equiv.sigmaCongr σ fun a => Equiv.refl (V (σ a))) (total x fun a => w (σ a)) :=
  (total_map σ (fun a => Equiv.refl (V (σ a))) x (fun a => w (σ a)) w
    fun _ => (map_refl _).symm).symm

/-- **The left unit law**, solved for the total composite. -/
lemma total_one_left' {E : Unit → Type} [∀ u, Fintype (E u)] [∀ u, DecidableEq (E u)]
    (y : (u : Unit) → S (E u)) : total one y = map (unitSigma E).symm (y ()) := by
  rw [← total_one_left y, map_map]
  symm
  refine (map_congr (e' := Equiv.refl (Σ u, E u)) (fun p => ?_) _).trans (map_refl (S := S) _)
  rcases p with ⟨⟨⟩, e⟩
  rfl

/-- **The right unit law**, solved for the total composite. -/
lemma total_one_right' (x : S A) : total x (fun _ => one) = map (Equiv.sigmaPUnit A).symm x := by
  conv_rhs => rw [← total_one_right x]
  rw [map_symm_map]

/-- **Associativity** with the inserted operations indexed by the inputs of the composite. -/
lemma total_assoc' {C : (Σ a, W a) → Type} [∀ p, Fintype (C p)] [∀ p, DecidableEq (C p)]
    (x : S A) (y : (a : A) → S (W a)) (z : (p : Σ a, W a) → S (C p)) :
    total (total x y) z
      = map (Equiv.sigmaAssoc fun a b => C ⟨a, b⟩).symm
          (total x fun a => total (y a) fun b => z ⟨a, b⟩) := by
  have h := total_assoc (S := S) x y fun a b => z ⟨a, b⟩
  exact (map_symm_map (Equiv.sigmaAssoc fun a b => C ⟨a, b⟩) _).symm.trans (congrArg _ h)

end Total


/-! ## Partial composition from total composition -/

section Comp

variable {A A' B B' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D]

/-- **The padded family**: `y` at `i` and the unit at every other input. -/
def pad (i : A) (y : S B) (a : A) : S (Pad i B a) :=
  if h : a = i then map (padIn h) y else map (padOut h) one

omit [Fintype A] in
lemma pad_of_eq {i a : A} (h : a = i) (y : S B) : pad i y a = map (padIn h) y := dif_pos h

omit [Fintype A] in
lemma pad_of_ne {i a : A} (h : a ≠ i) (y : S B) : pad i y a = map (padOut h) one := dif_neg h

/-- **Partial composition from total composition**: insert `y` at `i` and the unit at every other
input. -/
noncomputable def comp (i : A) (x : S A) (y : S B) : S (Without A i ⊕ B) :=
  map (padEquiv i B) (total x (pad i y))

lemma comp_def (i : A) (x : S A) (y : S B) : comp i x y = map (padEquiv i B) (total x (pad i y)) :=
  rfl

/-- Relabelling a padding. -/
def padCongr (σ : A ≃ A') (τ : B ≃ B') (i a : A) : Pad i B a ≃ Pad (σ i) B' (σ a) where
  toFun
    | Sum.inl ⟨u, h⟩ => Sum.inl ⟨u, fun e => h (σ.injective e)⟩
    | Sum.inr ⟨b, h⟩ => Sum.inr ⟨τ b, congrArg σ h⟩
  invFun
    | Sum.inl ⟨u, h⟩ => Sum.inl ⟨u, fun e => h (congrArg σ e)⟩
    | Sum.inr ⟨b, h⟩ => Sum.inr ⟨τ.symm b, σ.injective h⟩
  left_inv := by
    rintro (⟨u, h⟩ | ⟨b, h⟩) <;> simp
  right_inv := by
    rintro (⟨u, h⟩ | ⟨b, h⟩) <;> simp

omit [Fintype A] [Fintype A'] in
lemma pad_map (σ : A ≃ A') (τ : B ≃ B') (i : A) (y : S B) (a : A) :
    pad (σ i) (map τ y) (σ a) = map (padCongr σ τ i a) (pad i y a) := by
  by_cases h : a = i
  · rw [pad_of_eq h, pad_of_eq (congrArg σ h), map_map, map_map]
    refine map_congr (fun _ => ?_) y
    rfl
  · rw [pad_of_ne h, pad_of_ne (fun e => h (σ.injective e)), map_map]
    refine map_congr (fun _ => ?_) (one : S Unit)
    rfl

/-- **Equivariance of partial composition.** -/
theorem map_comp (σ : A ≃ A') (τ : B ≃ B') (i : A) (x : S A) (y : S B) :
    map (compEquiv σ τ i) (comp i x y) = comp (σ i) (map σ x) (map τ y) := by
  rw [comp, comp, ← total_map σ (padCongr σ τ i) x (pad i y) _ (pad_map σ τ i y), map_map,
    map_map]
  refine map_congr (fun p => ?_) _
  rcases p with ⟨a, (⟨u, h⟩ | ⟨b, h⟩)⟩ <;> rfl

/-- The unit at every input, padded. -/
def padUnit (i a : A) : Unit ≃ Pad i Unit a :=
  if h : a = i then padIn h else padOut h

omit [Fintype A] in
lemma pad_one (i a : A) : pad i (one : S Unit) a = map (padUnit i a) one := by
  by_cases h : a = i
  · rw [pad_of_eq h, padUnit, dif_pos h]
  · rw [pad_of_ne h, padUnit, dif_neg h]

/-- **The right unit law of partial composition.** -/
theorem comp_one (i : A) (x : S A) : map (rightUnitEquiv i) (comp i x one) = x := by
  rw [comp, show pad i (one : S Unit) = fun a => map (padUnit i a) one from funext (pad_one i),
    total_congr, total_one_right', map_map, map_map, map_map]
  refine (map_congr (e' := Equiv.refl A) (fun a => ?_) x).trans (map_refl x)
  by_cases h : a = i
  · subst h
    simp [padUnit, padIn, padEquiv]
  · simp [padUnit, padOut, padEquiv, h]

/-- **The left unit law of partial composition.** -/
theorem one_comp (y : S B) : map (leftUnitEquiv B) (comp () one y) = y := by
  rw [comp, total_one_left', pad_of_eq rfl, map_map, map_map, map_map]
  exact (map_congr (e' := Equiv.refl B) (fun b => rfl) y).trans (map_refl y)

end Comp

/-! ### Sequential associativity -/

section Seq

variable {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype D] [DecidableEq D]

/-- The inputs at `a` of the two sides of sequential associativity. -/
def seqPad (i : A) (j : B) (D : Type) (a : A) :
    Pad i (Without B j ⊕ D) a ≃
      Σ b : Pad i B a, Pad (Sum.inr j : Without A i ⊕ B) D (padEquiv i B ⟨a, b⟩) where
  toFun
    | Sum.inl ⟨u, h⟩ => ⟨Sum.inl ⟨u, h⟩, Sum.inl ⟨(), Sum.inl_ne_inr⟩⟩
    | Sum.inr ⟨Sum.inl b, h⟩ =>
        ⟨Sum.inr ⟨b.1, h⟩, Sum.inl ⟨(), fun e => b.2 (Sum.inr_injective e)⟩⟩
    | Sum.inr ⟨Sum.inr d, h⟩ => ⟨Sum.inr ⟨j, h⟩, Sum.inr ⟨d, rfl⟩⟩
  invFun
    | ⟨Sum.inl ⟨u, h⟩, _⟩ => Sum.inl ⟨u, h⟩
    | ⟨Sum.inr ⟨b, h⟩, Sum.inl ⟨_, hb⟩⟩ =>
        Sum.inr ⟨Sum.inl ⟨b, fun e => hb (congrArg Sum.inr e)⟩, h⟩
    | ⟨Sum.inr ⟨_, h⟩, Sum.inr ⟨d, _⟩⟩ => Sum.inr ⟨Sum.inr d, h⟩
  left_inv := by
    rintro (⟨u, h⟩ | ⟨(b | d), h⟩) <;> rfl
  right_inv := by
    rintro ⟨(⟨u, h⟩ | ⟨b, h⟩), (⟨u', h'⟩ | ⟨d, h'⟩)⟩
    · rfl
    · exact absurd h' Sum.inl_ne_inr
    · rfl
    · obtain rfl := Sum.inr_injective h'
      rfl

/-- The padding of `inr j` at an input coming from the inner operation. -/
def padInr (i : A) (j : B) (D : Type) (b : B) :
    Pad j D b ≃ Pad (Sum.inr j : Without A i ⊕ B) D (padEquiv i B ⟨i, padIn rfl b⟩) where
  toFun
    | Sum.inl ⟨u, h⟩ => Sum.inl ⟨u, fun e => h (Sum.inr_injective e)⟩
    | Sum.inr ⟨d, h⟩ => Sum.inr ⟨d, congrArg Sum.inr h⟩
  invFun
    | Sum.inl ⟨u, h⟩ => Sum.inl ⟨u, fun e => h (congrArg Sum.inr e)⟩
    | Sum.inr ⟨d, h⟩ => Sum.inr ⟨d, Sum.inr_injective h⟩
  left_inv := by
    rintro (⟨u, h⟩ | ⟨d, h⟩) <;> rfl
  right_inv := by
    rintro (⟨u, h⟩ | ⟨d, h⟩) <;> rfl

omit [Fintype A] [Fintype B] in
lemma pad_inr (i : A) (j : B) (z : S D) (b : B) :
    pad (Sum.inr j : Without A i ⊕ B) z (padEquiv i B ⟨i, padIn rfl b⟩)
      = map (padInr i j D b) (pad j z b) := by
  by_cases h : b = j
  · rw [pad_of_eq h, pad_of_eq (show padEquiv i B ⟨i, padIn rfl b⟩
      = (Sum.inr j : Without A i ⊕ B) from congrArg Sum.inr h), map_map]
    refine map_congr (fun _ => ?_) z
    rfl
  · rw [pad_of_ne h, pad_of_ne (show padEquiv i B ⟨i, padIn rfl b⟩
      ≠ (Sum.inr j : Without A i ⊕ B) from fun e => h (Sum.inr_injective e)), map_map]
    refine map_congr (fun _ => ?_) (one : S Unit)
    rfl

omit [Fintype A] in
/-- **Sequential associativity at one input** of the outer operation. -/
lemma total_pad_seq (i : A) (j : B) (y : S B) (z : S D) (a : A) :
    total (pad i y a) (fun b => pad (Sum.inr j : Without A i ⊕ B) z (padEquiv i B ⟨a, b⟩))
      = map (seqPad i j D a) (pad i (comp j y z) a) := by
  by_cases h : a = i
  · subst h
    rw [pad_of_eq rfl, pad_of_eq rfl, total_map_left,
      show (fun b => pad (Sum.inr j : Without A a ⊕ B) z (padEquiv a B ⟨a, padIn rfl b⟩))
        = fun b => map (padInr a j D b) (pad j z b) from funext fun b => pad_inr a j z b,
      total_congr, comp_def, map_map, map_map, map_map]
    refine map_congr (fun p => ?_) _
    rcases p with ⟨b, (⟨u, hb⟩ | ⟨d, hb⟩)⟩
    · rfl
    · subst hb
      rfl
  · rw [pad_of_ne h, pad_of_ne h, total_map_left, total_one_left' (S := S),
      pad_of_ne (show padEquiv i B ⟨a, padOut h ()⟩ ≠ (Sum.inr j : Without A i ⊕ B)
        from Sum.inl_ne_inr) z]
    simp only [map_map]
    refine map_congr (fun _ => ?_) (one : S Unit)
    rfl

/-- **Sequential associativity of partial composition.** -/
theorem comp_assoc_seq (i : A) (j : B) (x : S A) (y : S B) (z : S D) :
    map (seqEquiv i j D) (comp (Sum.inr j) (comp i x y) z) = comp i x (comp j y z) := by
  rw [comp_def (Sum.inr j), comp_def i x y, total_map_left, total_assoc',
    show (fun a => total (pad i y a)
        fun b => pad (Sum.inr j : Without A i ⊕ B) z (padEquiv i B ⟨a, b⟩))
      = fun a => map (seqPad i j D a) (pad i (comp j y z) a) from
        funext (total_pad_seq i j y z),
    total_congr, comp_def i x (comp j y z)]
  simp only [map_map]
  refine map_congr (fun p => ?_) _
  rcases p with ⟨a, (⟨u, h⟩ | ⟨(b | d), h⟩)⟩ <;> rfl

end Seq

/-! ### Parallel associativity -/

section Par

variable {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype D] [DecidableEq D]

/-- The inputs at `a` of the two sides of parallel associativity. -/
def parPad {i k : A} (hik : i ≠ k) (B D : Type) (a : A) :
    (Σ d : Pad k D a,
        Pad (Sum.inl ⟨i, hik⟩ : Without A k ⊕ D) B (padEquiv k D ⟨a, d⟩)) ≃
      Σ b : Pad i B a,
        Pad (Sum.inl ⟨k, Ne.symm hik⟩ : Without A i ⊕ B) D (padEquiv i B ⟨a, b⟩) where
  toFun
    | ⟨Sum.inl ⟨_, hk⟩, Sum.inl ⟨_, hi⟩⟩ =>
        ⟨Sum.inl ⟨(), fun e => hi (by subst e; rfl)⟩,
          Sum.inl ⟨(), fun e => hk (congrArg Subtype.val (Sum.inl_injective e))⟩⟩
    | ⟨Sum.inl ⟨_, _⟩, Sum.inr ⟨b, hi⟩⟩ =>
        ⟨Sum.inr ⟨b, congrArg Subtype.val (Sum.inl_injective hi)⟩,
          Sum.inl ⟨(), Sum.inr_ne_inl⟩⟩
    | ⟨Sum.inr ⟨d, hk⟩, _⟩ =>
        ⟨Sum.inl ⟨(), fun e => hik (e.symm.trans hk)⟩, Sum.inr ⟨d, by subst hk; rfl⟩⟩
  invFun
    | ⟨Sum.inl ⟨_, hi⟩, Sum.inl ⟨_, hk⟩⟩ =>
        ⟨Sum.inl ⟨(), fun e => hk (by subst e; rfl)⟩,
          Sum.inl ⟨(), fun e => hi (congrArg Subtype.val (Sum.inl_injective e))⟩⟩
    | ⟨Sum.inl ⟨_, _⟩, Sum.inr ⟨d, hk⟩⟩ =>
        ⟨Sum.inr ⟨d, congrArg Subtype.val (Sum.inl_injective hk)⟩,
          Sum.inl ⟨(), Sum.inr_ne_inl⟩⟩
    | ⟨Sum.inr ⟨b, hi⟩, _⟩ =>
        ⟨Sum.inl ⟨(), fun e => hik (hi.symm.trans e)⟩, Sum.inr ⟨b, by subst hi; rfl⟩⟩
  left_inv := by
    rintro ⟨(⟨u, hk⟩ | ⟨d, hk⟩), (⟨v, hi⟩ | ⟨b, hi⟩)⟩
    · rfl
    · rfl
    · rfl
    · exact absurd hi Sum.inr_ne_inl
  right_inv := by
    rintro ⟨(⟨u, hi⟩ | ⟨b, hi⟩), (⟨v, hk⟩ | ⟨d, hk⟩)⟩
    · rfl
    · rfl
    · rfl
    · exact absurd hk Sum.inr_ne_inl

omit [Fintype A] in
/-- **Parallel associativity at one input** of the outer operation. -/
lemma total_pad_par {i k : A} (hik : i ≠ k) (y : S B) (z : S D) (a : A) :
    total (pad i y a)
        (fun b =>
          pad (Sum.inl ⟨k, Ne.symm hik⟩ : Without A i ⊕ B) z (padEquiv i B ⟨a, b⟩))
      = map (parPad hik B D a) (total (pad k z a)
          fun d => pad (Sum.inl ⟨i, hik⟩ : Without A k ⊕ D) y (padEquiv k D ⟨a, d⟩)) := by
  by_cases hi : a = i
  · subst hi
    have hk : a ≠ k := hik
    rw [pad_of_eq rfl, pad_of_ne hk, total_map_left, total_map_left, total_one_left' (S := S),
      pad_of_eq (show padEquiv k D ⟨a, padOut hk ()⟩
        = (Sum.inl ⟨a, hik⟩ : Without A k ⊕ D) from rfl) y,
      show (fun b => pad (Sum.inl ⟨k, Ne.symm hik⟩ : Without A a ⊕ B) z
          (padEquiv a B ⟨a, padIn rfl b⟩))
        = fun b => map (padOut (show padEquiv a B ⟨a, padIn rfl b⟩
            ≠ (Sum.inl ⟨k, Ne.symm hik⟩ : Without A a ⊕ B) from Sum.inr_ne_inl)) one from
        funext fun b => pad_of_ne _ z,
      total_congr, total_one_right']
    simp only [map_map]
    refine map_congr (fun b => ?_) y
    rfl
  · by_cases hk : a = k
    · subst hk
      rw [pad_of_ne hi, pad_of_eq rfl, total_map_left, total_map_left, total_one_left' (S := S),
        pad_of_eq (show padEquiv i B ⟨a, padOut hi ()⟩
          = (Sum.inl ⟨a, Ne.symm hik⟩ : Without A i ⊕ B) from rfl) z,
        show (fun d => pad (Sum.inl ⟨i, hik⟩ : Without A a ⊕ D) y
            (padEquiv a D ⟨a, padIn rfl d⟩))
          = fun d => map (padOut (show padEquiv a D ⟨a, padIn rfl d⟩
              ≠ (Sum.inl ⟨i, hik⟩ : Without A a ⊕ D) from Sum.inr_ne_inl)) one from
          funext fun d => pad_of_ne _ y,
        total_congr, total_one_right']
      simp only [map_map]
      refine map_congr (fun d => ?_) z
      rfl
    · rw [pad_of_ne hi, pad_of_ne hk, total_map_left, total_map_left, total_one_left' (S := S),
        total_one_left' (S := S),
        pad_of_ne (show padEquiv i B ⟨a, padOut hi ()⟩
          ≠ (Sum.inl ⟨k, Ne.symm hik⟩ : Without A i ⊕ B) from
            fun e => hk (congrArg Subtype.val (Sum.inl_injective e))) z,
        pad_of_ne (show padEquiv k D ⟨a, padOut hk ()⟩
          ≠ (Sum.inl ⟨i, hik⟩ : Without A k ⊕ D) from
            fun e => hi (congrArg Subtype.val (Sum.inl_injective e))) y]
      simp only [map_map]
      refine map_congr (fun u => ?_) (one : S Unit)
      rfl

/-- **Parallel associativity of partial composition.** -/
theorem comp_assoc_par {i k : A} (hik : i ≠ k) (x : S A) (y : S B) (z : S D) :
    map (parEquiv hik B D) (comp (Sum.inl ⟨k, Ne.symm hik⟩) (comp i x y) z)
      = comp (Sum.inl ⟨i, hik⟩) (comp k x z) y := by
  rw [comp_def (Sum.inl ⟨k, Ne.symm hik⟩ : Without A i ⊕ B) (comp i x y) z, comp_def i x y,
    total_map_left, total_assoc',
    show (fun a => total (pad i y a)
        fun b => pad (Sum.inl ⟨k, Ne.symm hik⟩ : Without A i ⊕ B) z (padEquiv i B ⟨a, b⟩))
      = fun a => map (parPad hik B D a) (total (pad k z a)
          fun d => pad (Sum.inl ⟨i, hik⟩ : Without A k ⊕ D) y (padEquiv k D ⟨a, d⟩)) from
        funext (total_pad_par hik y z),
    total_congr, comp_def (Sum.inl ⟨i, hik⟩ : Without A k ⊕ D) (comp k x z) y, comp_def k x z,
    total_map_left, total_assoc']
  simp only [map_map]
  refine map_congr (fun p => ?_) _
  rcases p with ⟨a, ⟨(⟨u, hk⟩ | ⟨d, hk⟩), (⟨v, hi⟩ | ⟨b, hi⟩)⟩⟩
  · rfl
  · rfl
  · rfl
  · exact absurd hi Sum.inr_ne_inl

end Par

/-- **A set operad from an operad in May's sense**, with partial composition by padding. -/
@[reducible] noncomputable def toSetOperad : SetOperad S where
  map := map
  map_refl := map_refl
  map_trans := map_trans
  one := one
  comp := comp
  map_comp := map_comp
  comp_one := comp_one
  one_comp := one_comp
  comp_assoc_seq := comp_assoc_seq
  comp_assoc_par := comp_assoc_par

end MaySetOperad

/-! ## The two constructions are inverse -/

namespace May

section Units

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

/-- The input of `A` that an input of a stage comes from. -/
def stageVal {l : List A} : Stage B l → A
  | Sum.inl c => c.1
  | Sum.inr p => p.1.1

omit [Fintype A] [∀ a, Fintype (B a)] in
lemma stageVal_step_inl {a : A} {l : List A} (ha : a ∉ l)
    (s : Without (Stage B l) (Sum.inl ⟨a, ha⟩)) :
    stageVal (stepEquiv a l ha (Sum.inl s)) = stageVal s.1 := by
  obtain ⟨(c | p), hs⟩ := s <;> rfl

/-- **Filling with relabelled units relabels**, along a bijection that keeps track of the
inputs. -/
theorem fill_units (x : S A) (y : (a : A) → S (B a)) (l : List A) (hl : l.Nodup)
    (hy : ∀ a ∈ l, ∃ τ : Unit ≃ B a, y a = SetOperad.map τ SetOperad.one) :
    ∃ e : A ≃ Stage B l, (∀ a, stageVal (e a) = a) ∧ fill x y l hl = SetOperad.map e x := by
  induction l with
  | nil => exact ⟨initEquiv B, fun _ => rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
    obtain ⟨e, he, hx⟩ := ih hl' fun b hb => hy b (List.mem_cons_of_mem a hb)
    obtain ⟨τ, hτ⟩ := hy a List.mem_cons_self
    have hea : e a = Sum.inl ⟨a, ha⟩ := by
      have h := he a
      revert h
      rcases e a with c | ⟨c, b⟩
      · intro h
        exact congrArg Sum.inl (Subtype.ext h)
      · intro h
        exact absurd (h ▸ c.2) ha
    refine ⟨(rightUnitEquiv a).symm.trans ((Equiv.sumCongr (Equiv.refl _) τ).trans
      (((compEquiv e (Equiv.refl (B a)) a).trans (slotEquiv hea)).trans (stepEquiv a l ha))),
      fun b => ?_, ?_⟩
    · by_cases hb : b = a
      · subst hb
        simp only [Equiv.trans_apply, rightUnitEquiv_symm_self]
        rfl
      · simp only [Equiv.trans_apply, rightUnitEquiv_symm_of_ne hb]
        exact (stageVal_step_inl ha _).trans (he b)
    · rw [fill_cons, hx, hτ, comp_map_left e a _ hea, comp_map_right, comp_one_eq]
      simp only [map_map]
      refine map_congr (fun b => ?_) x
      rfl

end Units

end May


/-! ### Padding along a list -/

namespace May

section PadL

variable {A : Type} [DecidableEq A]

/-- **Padding along a list**: the inputs inserted at `a` when `y a` is inserted at the inputs in
`l` and the unit at the others. -/
abbrev PadL (B : A → Type) (l : List A) (a : A) : Type :=
  {_u : Unit // a ∉ l} ⊕ {_b : B a // a ∈ l}

instance PadL.instDecidableEq (B : A → Type) [∀ a, DecidableEq (B a)] (l : List A) (a : A) :
    DecidableEq (PadL B l a) :=
  inferInstanceAs (DecidableEq ({_u : Unit // a ∉ l} ⊕ {_b : B a // a ∈ l}))

instance PadL.instFintype (B : A → Type) [∀ a, Fintype (B a)] (l : List A) (a : A) :
    Fintype (PadL B l a) :=
  inferInstanceAs (Fintype ({_u : Unit // a ∉ l} ⊕ {_b : B a // a ∈ l}))

/-- At an input in `l`, the padding is a copy of `B a`. -/
def padLIn {B : A → Type} {l : List A} {a : A} (h : a ∈ l) : B a ≃ PadL B l a where
  toFun b := Sum.inr ⟨b, h⟩
  invFun
    | Sum.inl ⟨_, h'⟩ => absurd h h'
    | Sum.inr ⟨b, _⟩ => b
  left_inv _ := rfl
  right_inv := by
    rintro (⟨u, h'⟩ | ⟨b, _⟩)
    · exact absurd h h'
    · rfl

/-- At an input not in `l`, the padding is a single input. -/
def padLOut {B : A → Type} {l : List A} {a : A} (h : a ∉ l) : Unit ≃ PadL B l a where
  toFun u := Sum.inl ⟨u, h⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv := by
    rintro (⟨⟨⟩, _⟩ | ⟨b, h'⟩)
    · rfl
    · exact absurd h' h

/-- **The inputs of a total composite padded along `l`** are those of the stage of `l`. -/
def padLEquiv (B : A → Type) (l : List A) : (Σ a, PadL B l a) ≃ Stage B l where
  toFun
    | ⟨a, Sum.inl ⟨_, h⟩⟩ => Sum.inl ⟨a, h⟩
    | ⟨a, Sum.inr ⟨b, h⟩⟩ => Sum.inr ⟨⟨a, h⟩, b⟩
  invFun
    | Sum.inl c => ⟨c.1, Sum.inl ⟨(), c.2⟩⟩
    | Sum.inr ⟨c, b⟩ => ⟨c.1, Sum.inr ⟨b, c.2⟩⟩
  left_inv := by
    rintro ⟨a, (⟨⟨⟩, h⟩ | ⟨b, h⟩)⟩ <;> rfl
  right_inv := by
    rintro (c | ⟨c, b⟩) <;> rfl

/-- **One more step of padding along a list.** -/
def padLStep {B : A → Type} (a : A) (l : List A) (ha : a ∉ l) (b : A) :
    PadL B (a :: l) b ≃
      Σ u : PadL B l b,
        Pad (Sum.inl ⟨a, ha⟩ : Stage B l) (B a) (padLEquiv B l ⟨b, u⟩) where
  toFun
    | Sum.inl ⟨_, h⟩ => ⟨Sum.inl ⟨(), fun h' => h (List.mem_cons_of_mem a h')⟩,
        Sum.inl ⟨(), fun e => h (by
          have : b = a := congrArg Subtype.val (Sum.inl_injective e)
          exact this ▸ List.mem_cons_self)⟩⟩
    | Sum.inr ⟨c, h⟩ =>
        if hb : b ∈ l then ⟨Sum.inr ⟨c, hb⟩, Sum.inl ⟨(), Sum.inr_ne_inl⟩⟩
        else ⟨Sum.inl ⟨(), hb⟩,
          Sum.inr ⟨cast (congrArg B ((List.mem_cons.1 h).resolve_right hb)) c, by
            have : b = a := (List.mem_cons.1 h).resolve_right hb
            subst this
            rfl⟩⟩
  invFun
    | ⟨Sum.inl ⟨_, hb⟩, Sum.inl ⟨_, hne⟩⟩ => Sum.inl ⟨(), by
        intro h
        rcases List.mem_cons.1 h with h | h
        · exact hne (by subst h; rfl)
        · exact hb h⟩
    | ⟨Sum.inl ⟨_, hb⟩, Sum.inr ⟨c, he⟩⟩ =>
        Sum.inr ⟨cast (congrArg B (show b = a from
          congrArg Subtype.val (Sum.inl_injective he))).symm c, by
            have hba : b = a := congrArg Subtype.val (Sum.inl_injective he)
            rw [hba]
            exact List.mem_cons_self⟩
    | ⟨Sum.inr ⟨c, hb⟩, _⟩ => Sum.inr ⟨c, List.mem_cons_of_mem a hb⟩
  left_inv := by
    rintro (⟨u, h⟩ | ⟨c, h⟩)
    · rfl
    · by_cases hb : b ∈ l
      · simp [hb]
      · have : b = a := (List.mem_cons.1 h).resolve_right hb
        subst this
        simp [hb]
  right_inv := by
    rintro ⟨(⟨u, hb⟩ | ⟨c, hb⟩), (⟨v, hne⟩ | ⟨c', he⟩)⟩
    · rfl
    · have : b = a := congrArg Subtype.val (Sum.inl_injective he)
      subst this
      simp [hb]
    · simp [hb]
    · exact absurd he Sum.inr_ne_inl

end PadL

end May

namespace MaySetOperad

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}


section Converse

variable [MaySetOperad S] {A : Type} [Fintype A] [DecidableEq A] {B : A → Type}
  [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]

/-- **The family padded along a list**: `y a` at the inputs in `l`, the unit at the others. -/
def padL (l : List A) (y : (a : A) → S (B a)) (a : A) : S (PadL B l a) :=
  if h : a ∈ l then map (padLIn h) (y a) else map (padLOut h) one

omit [Fintype A] in
lemma padL_of_mem {l : List A} {a : A} (h : a ∈ l) (y : (a : A) → S (B a)) :
    padL l y a = map (padLIn h) (y a) := dif_pos h

omit [Fintype A] in
lemma padL_of_not_mem {l : List A} {a : A} (h : a ∉ l) (y : (a : A) → S (B a)) :
    padL l y a = map (padLOut h) one := dif_neg h

omit [Fintype A] in
/-- **One more step of padding at one input.** -/
lemma total_padL_step (a : A) (l : List A) (ha : a ∉ l) (y : (a : A) → S (B a)) (b : A) :
    total (padL l y b)
        (fun u => pad (Sum.inl ⟨a, ha⟩ : Stage B l) (y a) (padLEquiv B l ⟨b, u⟩))
      = map (padLStep a l ha b) (padL (a :: l) y b) := by
  by_cases hb : b ∈ l
  · rw [padL_of_mem hb, padL_of_mem (List.mem_cons_of_mem a hb), total_map_left,
      show (fun c =>
          pad (Sum.inl ⟨a, ha⟩ : Stage B l) (y a) (padLEquiv B l ⟨b, padLIn hb c⟩))
        = fun c => map (padOut (show padLEquiv B l ⟨b, padLIn hb c⟩
            ≠ (Sum.inl ⟨a, ha⟩ : Stage B l) from Sum.inr_ne_inl)) one from
        funext fun c => pad_of_ne _ (y a),
      total_congr, total_one_right']
    simp only [map_map]
    refine map_congr (fun c => ?_) (y b)
    simp [padLStep, hb, padLIn, padOut]
    rfl
  · by_cases hba : b = a
    · subst hba
      rw [padL_of_not_mem hb, padL_of_mem List.mem_cons_self, total_map_left,
        total_one_left' (S := S),
        pad_of_eq (show padLEquiv B l ⟨b, padLOut hb ()⟩ = (Sum.inl ⟨b, ha⟩ : Stage B l)
          from rfl) (y b)]
      simp only [map_map]
      refine map_congr (fun c => ?_) (y b)
      simp [padLStep, hb, padLIn, padIn, padLOut, unitSigma]
      rfl
    · have hb' : b ∉ a :: l := by
        intro h
        rcases List.mem_cons.1 h with h | h
        · exact hba h
        · exact hb h
      rw [padL_of_not_mem hb, padL_of_not_mem hb', total_map_left, total_one_left' (S := S),
        pad_of_ne (show padLEquiv B l ⟨b, padLOut hb ()⟩
            ≠ (Sum.inl ⟨a, ha⟩ : Stage B l) from
          fun e => hba (congrArg Subtype.val (Sum.inl_injective e))) (y a)]
      simp only [map_map]
      refine map_congr (fun u => ?_) (one : S Unit)
      rfl

/-- **Filling, for partial composition from total composition, is a padded total composite.** -/
theorem fill_toSetOperad (x : S A) (y : (a : A) → S (B a)) (l : List A) (hl : l.Nodup) :
    @May.fill S toSetOperad A _ _ B _ _ x y l hl = map (padLEquiv B l) (total x (padL l y)) := by
  letI : SetOperad S := toSetOperad
  induction l with
  | nil =>
    rw [fill_nil, show padL [] y = fun a => map (padLOut List.not_mem_nil) one from
      funext fun a => padL_of_not_mem _ y, total_congr, total_one_right']
    show map (initEquiv B) x = _
    simp only [map_map]
    refine map_congr (fun a => ?_) x
    rfl
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
    rw [fill_cons, ih hl']
    show map (stepEquiv a l ha) (comp (Sum.inl ⟨a, ha⟩ : Stage B l)
      (map (padLEquiv B l) (total x (padL l y))) (y a)) = _
    rw [comp_def, total_map_left, total_assoc',
      show (fun b => total (padL l y b)
          fun u => pad (Sum.inl ⟨a, ha⟩ : Stage B l) (y a) (padLEquiv B l ⟨b, u⟩))
        = fun b => map (padLStep a l ha b) (padL (a :: l) y b) from
          funext (total_padL_step a l ha y),
      total_congr]
    simp only [map_map]
    refine map_congr (fun p => ?_) _
    rcases p with ⟨b, (⟨u, hb⟩ | ⟨c, hb⟩)⟩
    · rfl
    · by_cases h : b ∈ l
      · simp [padLStep, h]
        rfl
      · have hba : b = a := (List.mem_cons.1 hb).resolve_right h
        subst hba
        simp [padLStep, h]
        rfl

/-- **Total composition from partial composition from total composition is total
composition.** -/
theorem total_toSetOperad (x : S A) (y : (a : A) → S (B a)) :
    @SetOperad.total S toSetOperad A _ _ B _ _ x y = total x y := by
  letI : SetOperad S := toSetOperad
  have hc : ∀ a, a ∈ (Finset.univ : Finset A).toList :=
    fun a => Finset.mem_toList.2 (Finset.mem_univ a)
  rw [SetOperad.total_eq_fill x y _ (Finset.nodup_toList _) hc, fill_toSetOperad,
    show padL (Finset.univ : Finset A).toList y = fun a => map (padLIn (hc a)) (y a) from
      funext fun a => padL_of_mem (hc a) y, total_congr]
  show map (finalEquiv B _ hc) (map (padLEquiv B _) (map _ (total x y))) = _
  simp only [map_map]
  refine (map_congr (e' := Equiv.refl _) (fun p => ?_) _).trans (map_refl _)
  rfl

end Converse

/-- **Partial composition from the total composition of a set operad is its partial
composition.** -/
theorem comp_toMaySetOperad [SetOperad S] {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (i : A) (x : S A) (y : S B) :
    @comp S (SetOperad.toMaySetOperad S) A B _ _ _ _ i x y = SetOperad.comp i x y := by
  letI := SetOperad.toMaySetOperad S
  have hy : ∀ a ∈ others i, ∃ τ : Unit ≃ Pad i B a,
      pad i y a = SetOperad.map τ SetOperad.one := fun a ha =>
    ⟨padOut fun h => (List.nodup_cons.1 (others_nodup i)).1
      (Eq.subst (motive := fun t => t ∈ others i) h ha), pad_of_ne _ y⟩
  obtain ⟨e, he, hx⟩ := fill_units x (pad i y) (others i) _ hy
  have hei : e i = Sum.inl ⟨i, (List.nodup_cons.1 (others_nodup i)).1⟩ := by
    have h := he i
    revert h
    rcases e i with c | ⟨c, b⟩
    · intro h
      exact congrArg Sum.inl (Subtype.ext h)
    · intro h
      exact absurd (Eq.subst (motive := fun t => t ∈ others i) (show c.1 = i from h) c.2)
        (List.nodup_cons.1 (others_nodup i)).1
  show SetOperad.map (padEquiv i B) (SetOperad.total x (pad i y)) = _
  rw [May.total_eq_comp x _ i, hx, pad_of_eq rfl]
  show SetOperad.map _ (SetOperad.map _ (SetOperad.comp _ (SetOperad.map e x)
    (SetOperad.map (padIn rfl) y))) = _
  rw [comp_map_left e i _ hei, comp_map_right]
  simp only [May.map_map]
  refine (May.map_congr (e' := Equiv.refl _) (fun s => ?_) _).trans (SetOperad.map_refl _)
  rcases s with ⟨a, ha⟩ | b
  · have key : ∀ (s : Stage (Pad i B) (others i))
        (hs : s ≠ Sum.inl ⟨i, (List.nodup_cons.1 (others_nodup i)).1⟩), stageVal s = a →
        padEquiv i B (finalEquiv (Pad i B) (i :: others i) (mem_others i)
          (stepEquiv i (others i) (List.nodup_cons.1 (others_nodup i)).1 (Sum.inl ⟨s, hs⟩)))
          = Sum.inl ⟨a, ha⟩ := by
      rintro (c | ⟨c, (⟨u, hu⟩ | ⟨b, hb⟩)⟩) hs hc
      · have hc : c.1 = a := hc
        exact absurd (List.mem_cons.1 (mem_others i a)) (by
          rintro (h' | h')
          · exact ha h'
          · exact c.2 (Eq.subst (motive := fun t => t ∈ others i) hc.symm h'))
      · have hc : c.1 = a := hc
        exact congrArg Sum.inl (Subtype.ext hc)
      · have hc : c.1 = a := hc
        exact absurd (hc.symm.trans hb) ha
    exact key (e a) _ (he a)
  · rfl

/-! ### The two constructions are inverse -/

/-- **Two set operad structures** with the same relabelling, unit and partial composition are
equal. -/
theorem _root_.Operad.SetOperad.ext_of {I J : SetOperad S}
    (hmap : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (x : S A), @SetOperad.map S I A B _ _ _ _ e x = @SetOperad.map S J A B _ _ _ _ e x)
    (hone : @SetOperad.one S I = @SetOperad.one S J)
    (hcomp : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (x : S A) (y : S B),
      @SetOperad.comp S I A B _ _ _ _ i x y = @SetOperad.comp S J A B _ _ _ _ i x y) :
    I = J := by
  obtain ⟨mI, _, _, oI, cI, _, _, _, _, _⟩ := I
  obtain ⟨mJ, _, _, oJ, cJ, _, _, _, _, _⟩ := J
  have h1 : @mI = @mJ := by
    funext A B _ _ _ _ e x
    exact hmap e x
  have h2 : @cI = @cJ := by
    funext A B _ _ _ _ i x y
    exact hcomp i x y
  subst h1 h2
  cases hone
  rfl

/-- **Two structures of operad in May's sense** with the same relabelling, unit and total
composition are equal. -/
theorem ext_of {I J : MaySetOperad S}
    (hmap : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (x : S A), @MaySetOperad.map S I A B _ _ _ _ e x = @MaySetOperad.map S J A B _ _ _ _ e x)
    (hone : @MaySetOperad.one S I = @MaySetOperad.one S J)
    (htotal : ∀ {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
      [∀ a, DecidableEq (B a)] (x : S A) (y : (a : A) → S (B a)),
      @MaySetOperad.total S I A _ _ B _ _ x y = @MaySetOperad.total S J A _ _ B _ _ x y) :
    I = J := by
  obtain ⟨mI, _, _, oI, tI, _, _, _, _⟩ := I
  obtain ⟨mJ, _, _, oJ, tJ, _, _, _, _⟩ := J
  have h1 : @mI = @mJ := by
    funext A B _ _ _ _ e x
    exact hmap e x
  have h2 : @tI = @tJ := by
    funext A _ _ B _ _ x y
    exact htotal x y
  subst h1 h2
  cases hone
  rfl

/-- **From partial composition to total composition and back.** -/
theorem toSetOperad_toMaySetOperad (inst : SetOperad S) :
    @toSetOperad S (SetOperad.toMaySetOperad S) = inst :=
  SetOperad.ext_of (fun _ _ => rfl) rfl fun i x y => comp_toMaySetOperad i x y

/-- **From total composition to partial composition and back.** -/
theorem toMaySetOperad_toSetOperad (inst : MaySetOperad S) :
    @SetOperad.toMaySetOperad S toSetOperad = inst :=
  ext_of (fun _ _ => rfl) rfl fun x y => total_toSetOperad x y

end MaySetOperad

end Operad
