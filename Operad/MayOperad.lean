/-
# Total composition

Operads in the library are defined by partial composition `x ∘ᵢ y`. May's original definition
uses *total composition*: an operation `x` with inputs `A` and an operation `y a` with inputs `B a`
for each input `a` compose to an operation with inputs `Σ a, B a`,

  `γ x y : S (Σ a, B a)`,

subject to equivariance, two unit laws and associativity. This file builds total composition from
partial composition and proves May's axioms for it; `Operad.MayClass` proves the converse and that
the two definitions are equivalent.

* **Filling** (`May.fill`): the operations `y a` inserted one at a time at the inputs `a` in a
  list. The result does not depend on the order (`May.fill_perm`, by parallel associativity), it
  commutes with relabelling (`May.fill_map`), and filling the inputs of a composite `X ∘ᵢ Y` is
  the composite of the filled operations (`May.fill_comp`, the interchange law, by sequential
  and parallel associativity).
* **Total composition** (`SetOperad.total`): filling every input. It satisfies **May's axioms**:
  equivariance (`SetOperad.total_map`), the unit laws (`SetOperad.total_one_left`,
  `SetOperad.total_one_right`) and associativity (`SetOperad.total_assoc`, from the interchange
  law by `May.fill_fill`).
* **Operads in modules** (`SymOperad.total`): total composition of the underlying set operad,
  linear in the outer operation and multilinear in the inserted ones (`SymOperad.totalL`), with the
  same axioms (`SymOperad.total_assoc`, ...).

Inputs filled so far are tracked by a *stage* (`May.Stage`): the inputs not yet filled, and the
inputs of the operations inserted. Every comparison is an identity of explicit bijections, checked
on elements.
-/
import Operad.SetOperad
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.LinearAlgebra.Multilinear.Basic

universe u v w

set_option synthInstance.maxSize 1024

namespace Operad

open Sym

namespace May

/-! ## Filling the inputs one at a time -/

section Stages

variable {A : Type} [DecidableEq A] {B : A → Type} [∀ a, DecidableEq (B a)]

/-- **The inputs after filling those in `l`**: the inputs not in `l`, and the inputs of the
operations inserted at those in `l`. -/
abbrev Stage (B : A → Type) (l : List A) : Type :=
  {a : A // a ∉ l} ⊕ Σ a : {a : A // a ∈ l}, B a.1

/- The instances on stages are stated once, generically, so that every stage carries the same
instances whatever its type of inputs (membership in a list of a sum type would otherwise be
decided through a different `BEq`). -/
instance Stage.instDecidableEq (l : List A) : DecidableEq (Stage B l) :=
  inferInstanceAs (DecidableEq ({a : A // a ∉ l} ⊕ Σ a : {a : A // a ∈ l}, B a.1))

instance Stage.instFintype [Fintype A] [∀ a, Fintype (B a)] (l : List A) :
    Fintype (Stage B l) :=
  inferInstanceAs (Fintype ({a : A // a ∉ l} ⊕ Σ a : {a : A // a ∈ l}, B a.1))

/-- Before filling anything, the inputs are those of the outer operation. -/
def initEquiv (B : A → Type) : A ≃ Stage B [] where
  toFun a := Sum.inl ⟨a, by simp⟩
  invFun
    | Sum.inl a => a.1
    | Sum.inr p => absurd p.1.2 (by simp)
  left_inv _ := rfl
  right_inv := by
    rintro (a | ⟨⟨a, ha⟩, b⟩)
    · rfl
    · simp at ha

/-- **Filling one more input** `a ∉ l`: the composite of the stage of `l` with the operation
inserted at `a` has the inputs of the stage of `a :: l`. -/
def stepEquiv (a : A) (l : List A) (ha : a ∉ l) :
    Without (Stage B l) (Sum.inl ⟨a, ha⟩) ⊕ B a ≃ Stage B (a :: l) where
  toFun
    | Sum.inl ⟨Sum.inl c, hc⟩ => Sum.inl ⟨c.1, by
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => hc (by rw [Sum.inl.injEq, Subtype.ext_iff, h]), c.2⟩⟩
    | Sum.inl ⟨Sum.inr p, _⟩ => Sum.inr ⟨⟨p.1.1, List.mem_cons_of_mem a p.1.2⟩, p.2⟩
    | Sum.inr b => Sum.inr ⟨⟨a, List.mem_cons_self⟩, b⟩
  invFun
    | Sum.inl c => Sum.inl ⟨Sum.inl ⟨c.1, fun h => c.2 (List.mem_cons_of_mem a h)⟩, by
        intro h
        rw [Sum.inl.injEq, Subtype.ext_iff] at h
        exact c.2 (h ▸ List.mem_cons_self)⟩
    | Sum.inr ⟨c, b⟩ =>
        if h : c.1 = a then Sum.inr (cast (congrArg B h) b)
        else Sum.inl ⟨Sum.inr ⟨⟨c.1, (List.mem_cons.1 c.2).resolve_left h⟩, b⟩, by simp⟩
  left_inv := by
    rintro (⟨(c | ⟨⟨c, hc⟩, b⟩), hne⟩ | b)
    · rfl
    · have hca : c ≠ a := fun h => ha (h ▸ hc)
      simp [hca]
    · simp
  right_inv := by
    rintro (c | ⟨⟨c, hc⟩, b⟩)
    · rfl
    · by_cases h : c = a
      · subst h
        simp
      · simp [h]

/-- **Two lists with the same members give the same stage.** -/
def stagePerm {l l' : List A} (h : ∀ a, a ∈ l ↔ a ∈ l') : Stage B l ≃ Stage B l' where
  toFun
    | Sum.inl c => Sum.inl ⟨c.1, fun hc => c.2 ((h c.1).2 hc)⟩
    | Sum.inr ⟨c, b⟩ => Sum.inr ⟨⟨c.1, (h c.1).1 c.2⟩, b⟩
  invFun
    | Sum.inl c => Sum.inl ⟨c.1, fun hc => c.2 ((h c.1).1 hc)⟩
    | Sum.inr ⟨c, b⟩ => Sum.inr ⟨⟨c.1, (h c.1).2 c.2⟩, b⟩
  left_inv := by rintro (c | ⟨c, b⟩) <;> rfl
  right_inv := by rintro (c | ⟨c, b⟩) <;> rfl

/-- After filling every input, the inputs are those of the inserted operations. -/
def finalEquiv (B : A → Type) (l : List A) (hl : ∀ a, a ∈ l) : Stage B l ≃ Σ a, B a where
  toFun
    | Sum.inl c => absurd (hl c.1) c.2
    | Sum.inr p => ⟨p.1.1, p.2⟩
  invFun p := Sum.inr ⟨⟨p.1, hl p.1⟩, p.2⟩
  left_inv := by
    rintro (c | ⟨c, b⟩)
    · exact absurd (hl c.1) c.2
    · rfl
  right_inv _ := rfl

end Stages

section Relabel

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {P P' Q Q' : Type} [Fintype P] [DecidableEq P] [Fintype P'] [DecidableEq P']
  [Fintype Q] [DecidableEq Q] [Fintype Q'] [DecidableEq Q']

/-- Relabellings along equivalences with the same values agree. -/
lemma map_congr {e e' : P ≃ P'} (h : ∀ p, e p = e' p) (X : S P) :
    SetOperad.map e X = SetOperad.map e' X := by
  rw [Equiv.ext h]

/-- Two relabellings in a row, as one. -/
lemma map_map (e : P ≃ P') (f : P' ≃ Q) (X : S P) :
    SetOperad.map f (SetOperad.map e X) = SetOperad.map (e.trans f) X :=
  (SetOperad.map_trans e f X).symm

/-- **Relabelling the outer operation of a composite**, the slot `i'` being the image of `i`. -/
lemma comp_map_left (e : P ≃ P') (i : P) (i' : P') (hi : e i = i') (X : S P) (Y : S Q) :
    SetOperad.comp i' (SetOperad.map e X) Y
      = SetOperad.map ((compEquiv e (Equiv.refl Q) i).trans (slotEquiv hi))
          (SetOperad.comp i X Y) := by
  subst hi
  rw [← map_map, SetOperad.map_comp, SetOperad.map_refl]
  symm
  refine (map_congr (e' := Equiv.refl _) (fun s => ?_) _).trans (SetOperad.map_refl _)
  rcases s with s | s <;> rfl

/-- **Relabelling the inner operation of a composite.** -/
lemma comp_map_right (i : P) (f : Q ≃ Q') (X : S P) (Y : S Q) :
    SetOperad.comp i X (SetOperad.map f Y)
      = SetOperad.map (Equiv.sumCongr (Equiv.refl (Without P i)) f) (SetOperad.comp i X Y) := by
  have h := SetOperad.map_comp (S := S) (Equiv.refl P) f i X Y
  rw [SetOperad.map_refl] at h
  refine h.symm.trans ?_
  exact map_congr (fun s => by rcases s with s | s <;> rfl) _

/-- **Parallel associativity**, solved for the composite filling `i` first. -/
lemma comp_par_eq {i k : P} (hik : i ≠ k) (X : S P) (Y : S Q) (Z : S Q') :
    SetOperad.comp (Sum.inl ⟨k, Ne.symm hik⟩) (SetOperad.comp i X Y) Z
      = SetOperad.map (parEquiv hik Q Q').symm
          (SetOperad.comp (Sum.inl ⟨i, hik⟩) (SetOperad.comp k X Z) Y) := by
  rw [← SetOperad.comp_assoc_par hik, SetOperad.map_symm_map]

/-- **Sequential associativity**, solved for the composite filling the inner operation first. -/
lemma comp_seq_eq (i : P) (j : Q) (X : S P) (Y : S Q) (Z : S Q') :
    SetOperad.comp (Sum.inr j) (SetOperad.comp i X Y) Z
      = SetOperad.map (seqEquiv i j Q').symm (SetOperad.comp i X (SetOperad.comp j Y Z)) := by
  rw [← SetOperad.comp_assoc_seq i j, SetOperad.map_symm_map]

/-- **The right unit**, solved for the composite. -/
lemma comp_one_eq (i : P) (X : S P) :
    SetOperad.comp i X SetOperad.one = SetOperad.map (rightUnitEquiv i).symm X := by
  conv_lhs => rw [← SetOperad.map_symm_map (rightUnitEquiv i) (SetOperad.comp i X SetOperad.one)]
  rw [SetOperad.comp_one]

/-- **The left unit**, solved for the composite. -/
lemma one_comp_eq (Y : S Q) :
    SetOperad.comp () SetOperad.one Y = SetOperad.map (leftUnitEquiv Q).symm Y := by
  conv_lhs => rw [← SetOperad.map_symm_map (leftUnitEquiv Q) (SetOperad.comp () SetOperad.one Y)]
  rw [SetOperad.one_comp]

end Relabel

section Fill

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

/-- **Filling the inputs in `l`**, the last one first: the operation `y a` is inserted at each
input `a` of `x` in `l`. -/
def fill (x : S A) (y : (a : A) → S (B a)) : (l : List A) → l.Nodup → S (Stage B l)
  | [], _ => SetOperad.map (initEquiv B) x
  | a :: l, h => SetOperad.map (stepEquiv a l (List.nodup_cons.1 h).1)
      (SetOperad.comp (Sum.inl ⟨a, (List.nodup_cons.1 h).1⟩ : Stage B l)
        (fill x y l (List.nodup_cons.1 h).2) (y a))

lemma fill_nil (x : S A) (y : (a : A) → S (B a)) (h : ([] : List A).Nodup) :
    fill x y [] h = SetOperad.map (initEquiv B) x := rfl

lemma fill_cons (x : S A) (y : (a : A) → S (B a)) (a : A) (l : List A) (h : (a :: l).Nodup) :
    fill x y (a :: l) h = SetOperad.map (stepEquiv a l (List.nodup_cons.1 h).1)
      (SetOperad.comp (Sum.inl ⟨a, (List.nodup_cons.1 h).1⟩ : Stage B l)
        (fill x y l (List.nodup_cons.1 h).2) (y a)) := rfl

/-- **Filling does not depend on the order**: two orders of the same inputs give the same
operation, by parallel associativity. -/
theorem fill_perm (x : S A) (y : (a : A) → S (B a)) {l l' : List A} (hp : l.Perm l')
    (hl : l.Nodup) (hl' : l'.Nodup) :
    SetOperad.map (stagePerm (B := B) fun _ => hp.mem_iff) (fill x y l hl) = fill x y l' hl' := by
  revert hl hl'
  induction hp with
  | nil =>
    intro hl hl'
    rw [fill_nil, map_map]
    refine map_congr (fun _ => ?_) x
    rfl
  | cons a hp ih =>
    intro hl hl'
    obtain ⟨ha₁, hl₁⟩ := List.nodup_cons.1 hl
    obtain ⟨ha₂, hl₂⟩ := List.nodup_cons.1 hl'
    rw [fill_cons, fill_cons, ← ih hl₁ hl₂,
      comp_map_left (stagePerm (B := B) fun _ => hp.mem_iff) (Sum.inl ⟨a, ha₁⟩)
        (Sum.inl ⟨a, ha₂⟩) rfl, map_map, map_map]
    refine map_congr (fun s => ?_) _
    rcases s with ⟨(c | ⟨c, b⟩), hc⟩ | b <;> rfl
  | swap a b l =>
    intro hl hl'
    have hab : a ≠ b := fun h => (List.nodup_cons.1 hl').1 (h ▸ List.mem_cons_self)
    have ha : a ∉ l := (List.nodup_cons.1 (List.nodup_cons.1 hl).2).1
    have hb : b ∉ l := fun h => (List.nodup_cons.1 hl).1 (List.mem_cons_of_mem a h)
    have ha' : a ∉ b :: l := (List.nodup_cons.1 hl').1
    have hb' : b ∉ a :: l := (List.nodup_cons.1 hl).1
    have hik : (Sum.inl ⟨a, ha⟩ : Stage B l) ≠ Sum.inl ⟨b, hb⟩ := by
      simp [hab]
    rw [fill_cons, fill_cons, fill_cons, fill_cons,
      comp_map_left (stepEquiv a l ha) (Sum.inl ⟨Sum.inl ⟨b, hb⟩, Ne.symm hik⟩)
        (Sum.inl ⟨b, hb'⟩) rfl,
      comp_map_left (stepEquiv b l hb) (Sum.inl ⟨Sum.inl ⟨a, ha⟩, hik⟩)
        (Sum.inl ⟨a, ha'⟩) rfl,
      comp_par_eq hik]
    simp only [map_map]
    refine map_congr (fun s => ?_) _
    rcases s with ⟨(⟨(c | ⟨⟨c, hc⟩, d⟩), hc'⟩ | d), hd⟩ | d <;> rfl
  | trans hp₁ hp₂ ih₁ ih₂ =>
    intro hl hl'
    have hm := (hp₁.nodup_iff).1 hl
    rw [← ih₂ hm hl', ← ih₁ hl hm, map_map]
    exact map_congr (fun s => by rcases s with c | ⟨c, b⟩ <;> rfl) _

end Fill


section Congr

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  {B : A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
  {B' : A' → Type} [∀ a, Fintype (B' a)] [∀ a, DecidableEq (B' a)]

/-- **Relabelling a stage** along `σ : A ≃ A'` and `τ a : B a ≃ B' (σ a)`. -/
def stageCongr (σ : A ≃ A') (τ : ∀ a, B a ≃ B' (σ a)) (l : List A) :
    Stage B l ≃ Stage B' (l.map σ) :=
  Equiv.sumCongr
    (σ.subtypeEquiv fun _ => not_congr (List.mem_map_of_injective σ.injective).symm)
    (Equiv.sigmaCongr (σ.subtypeEquiv fun _ => (List.mem_map_of_injective σ.injective).symm)
      fun a => τ a.1)

/-- **Filling commutes with relabelling**: relabelling the outer operation and the inserted ones
relabels the filled operation. -/
theorem fill_map (σ : A ≃ A') (τ : ∀ a, B a ≃ B' (σ a)) (x : S A) (y : (a : A) → S (B a))
    (y' : (a : A') → S (B' a)) (hy : ∀ a, y' (σ a) = SetOperad.map (τ a) (y a)) (l : List A)
    (hl : l.Nodup) :
    SetOperad.map (stageCongr σ τ l) (fill x y l hl)
      = fill (SetOperad.map σ x) y' (l.map σ) (hl.map σ.injective) := by
  induction l with
  | nil =>
    dsimp only [List.map_nil]
    rw [fill_nil, fill_nil, map_map, map_map]
    refine map_congr (fun _ => ?_) x
    rfl
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
    have hσa : σ a ∉ l.map σ := fun h => ha ((List.mem_map_of_injective σ.injective).1 h)
    dsimp only [List.map_cons]
    rw [fill_cons, fill_cons, ← ih hl', hy,
      comp_map_left (stageCongr σ τ l) (Sum.inl ⟨a, ha⟩) (Sum.inl ⟨σ a, hσa⟩) rfl,
      comp_map_right]
    simp only [map_map]
    refine map_congr (fun s => ?_) _
    rcases s with ⟨(c | ⟨c, b⟩), hc⟩ | b <;> rfl

end Congr

section Unit

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A]

/-- The input of `A` that an input of a stage with units inserted comes from. -/
def unitVal {l : List A} : Stage (fun _ : A => Unit) l → A
  | Sum.inl c => c.1
  | Sum.inr p => p.1.1

/-- **Filling with units relabels**: inserting the unit at the inputs in `l` relabels the
operation along a bijection that keeps track of the inputs. -/
theorem fill_one (x : S A) (l : List A) (hl : l.Nodup) :
    ∃ e : A ≃ Stage (fun _ : A => Unit) l, (∀ a, unitVal (e a) = a) ∧
      fill x (fun _ => SetOperad.one) l hl = SetOperad.map e x := by
  induction l with
  | nil => exact ⟨initEquiv _, fun _ => rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
    obtain ⟨e, he, hx⟩ := ih hl'
    let r := rightUnitEquiv (A := Stage (fun _ : A => Unit) l) (Sum.inl ⟨a, ha⟩)
    refine ⟨e.trans (r.symm.trans (stepEquiv (B := fun _ : A => Unit) a l ha)), fun b => ?_, ?_⟩
    · have key : ∀ s : Stage (fun _ : A => Unit) l,
          unitVal (stepEquiv (B := fun _ : A => Unit) a l ha (r.symm s)) = unitVal s := by
        intro s
        by_cases hs : s = Sum.inl ⟨a, ha⟩
        · subst hs
          rw [rightUnitEquiv_symm_self]
          rfl
        · rw [rightUnitEquiv_symm_of_ne hs]
          rcases s with c | ⟨c, u⟩ <;> rfl
      simp only [Equiv.trans_apply]
      rw [key, he]
    · rw [fill_cons, hx, comp_one_eq, map_map, map_map]

end Unit

section Interchange

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {W₁ : P → Type} [∀ p, Fintype (W₁ p)] [∀ p, DecidableEq (W₁ p)]
  {W₂ : Q → Type} [∀ q, Fintype (W₂ q)] [∀ q, DecidableEq (W₂ q)]

/-- **The inputs of the operations inserted into a composite**: `W₁` at the inputs coming from the
outer operation, `W₂` at those coming from the inner one. -/
def sumFam (W₁ : P → Type) (W₂ : Q → Type) (i : P) : Without P i ⊕ Q → Type
  | Sum.inl p => W₁ p.1
  | Sum.inr q => W₂ q

instance (i : P) (j : Without P i ⊕ Q) : Fintype (sumFam W₁ W₂ i j) :=
  match j with
  | Sum.inl p => inferInstanceAs (Fintype (W₁ p.1))
  | Sum.inr q => inferInstanceAs (Fintype (W₂ q))

instance (i : P) (j : Without P i ⊕ Q) : DecidableEq (sumFam W₁ W₂ i j) :=
  match j with
  | Sum.inl p => inferInstanceAs (DecidableEq (W₁ p.1))
  | Sum.inr q => inferInstanceAs (DecidableEq (W₂ q))

/-- The operations inserted into a composite. -/
def sumVal (i : P) (w₁ : (p : P) → S (W₁ p)) (w₂ : (q : Q) → S (W₂ q)) :
    (j : Without P i ⊕ Q) → S (sumFam W₁ W₂ i j)
  | Sum.inl p => w₁ p.1
  | Sum.inr q => w₂ q

/-- **Splitting a list of inputs of a composite**: `L₁` and `L₂` list, in order, the inputs in
`L` coming from the outer and from the inner operation. -/
inductive Splits {i : P} : List (Without P i ⊕ Q) → List P → List Q → Prop
  | nil : Splits [] [] []
  | left {L : List (Without P i ⊕ Q)} {L₁ : List P} {L₂ : List Q} (p : Without P i) :
      Splits L L₁ L₂ → Splits (Sum.inl p :: L) (p.1 :: L₁) L₂
  | right {L : List (Without P i ⊕ Q)} {L₁ : List P} {L₂ : List Q} (q : Q) :
      Splits L L₁ L₂ → Splits (Sum.inr q :: L) L₁ (q :: L₂)

namespace Splits

variable {i : P} {L : List (Without P i ⊕ Q)} {L₁ : List P} {L₂ : List Q}

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
lemma mem_left (h : Splits L L₁ L₂) (p : Without P i) : p.1 ∈ L₁ ↔ Sum.inl p ∈ L := by
  induction h with
  | nil => simp
  | left p' _ ih =>
    simp only [List.mem_cons, ih, Sum.inl.injEq]
    exact or_congr_left ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩
  | right q _ ih => simp [ih]

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
lemma mem_right (h : Splits L L₁ L₂) (q : Q) : q ∈ L₂ ↔ Sum.inr q ∈ L := by
  induction h with
  | nil => simp
  | left p _ ih => simp [ih]
  | right q' _ ih => simp [ih]

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
lemma not_mem (h : Splits L L₁ L₂) : i ∉ L₁ := by
  induction h with
  | nil => simp
  | left p _ ih => simp [ih, Ne.symm p.2]
  | right q _ ih => exact ih

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
lemma nodup_left (h : Splits L L₁ L₂) (hL : L.Nodup) : L₁.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | left p h ih =>
    obtain ⟨hp, hL⟩ := List.nodup_cons.1 hL
    exact List.nodup_cons.2 ⟨fun h' => hp ((h.mem_left p).1 h'), ih hL⟩
  | right q _ ih => exact ih (List.nodup_cons.1 hL).2

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
lemma nodup_right (h : Splits L L₁ L₂) (hL : L.Nodup) : L₂.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | left p _ ih => exact ih (List.nodup_cons.1 hL).2
  | right q h ih =>
    obtain ⟨hq, hL⟩ := List.nodup_cons.1 hL
    exact List.nodup_cons.2 ⟨fun h' => hq ((h.mem_right q).1 h'), ih hL⟩

end Splits

/-- **The inputs after filling the inputs in `L` of a composite**, against those of the composite
of the filled operations. -/
def interEquiv {i : P} {L : List (Without P i ⊕ Q)} {L₁ : List P} {L₂ : List Q}
    (h : Splits L L₁ L₂) :
    Stage (sumFam W₁ W₂ i) L ≃
      Without (Stage W₁ L₁) (Sum.inl ⟨i, h.not_mem⟩) ⊕ Stage W₂ L₂ where
  toFun
    | Sum.inl ⟨Sum.inl p, hp⟩ =>
        Sum.inl ⟨Sum.inl ⟨p.1, fun h' => hp ((h.mem_left p).1 h')⟩, by
          simp [Subtype.ext_iff, p.2]⟩
    | Sum.inl ⟨Sum.inr q, hq⟩ => Sum.inr (Sum.inl ⟨q, fun h' => hq ((h.mem_right q).1 h')⟩)
    | Sum.inr ⟨⟨Sum.inl p, hp⟩, w⟩ =>
        Sum.inl ⟨Sum.inr ⟨⟨p.1, (h.mem_left p).2 hp⟩, w⟩, by simp⟩
    | Sum.inr ⟨⟨Sum.inr q, hq⟩, w⟩ =>
        Sum.inr (Sum.inr ⟨⟨q, (h.mem_right q).2 hq⟩, w⟩)
  invFun
    | Sum.inl ⟨Sum.inl c, hc⟩ =>
        Sum.inl ⟨Sum.inl ⟨c.1, fun e => hc (by simp [Subtype.ext_iff, e])⟩,
          fun h' => c.2 ((h.mem_left _).2 h')⟩
    | Sum.inl ⟨Sum.inr ⟨c, w⟩, _⟩ =>
        Sum.inr ⟨⟨Sum.inl ⟨c.1,
            fun e => h.not_mem (Eq.subst (motive := (· ∈ L₁)) e c.2)⟩,
          (h.mem_left ⟨c.1, _⟩).1 c.2⟩, w⟩
    | Sum.inr (Sum.inl d) => Sum.inl ⟨Sum.inr d.1, fun h' => d.2 ((h.mem_right _).2 h')⟩
    | Sum.inr (Sum.inr ⟨d, w⟩) => Sum.inr ⟨⟨Sum.inr d.1, (h.mem_right _).1 d.2⟩, w⟩
  left_inv := by
    rintro (⟨(p | q), hp⟩ | ⟨⟨(p | q), hp⟩, w⟩) <;> rfl
  right_inv := by
    rintro (⟨(c | ⟨c, w⟩), hc⟩ | (d | ⟨d, w⟩)) <;> rfl

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
/-- Inner inputs first, then outer ones. -/
lemma splits_append {i : P} (L₁ : List (Without P i)) (L₂ : List Q) :
    Splits (L₂.map Sum.inr ++ L₁.map Sum.inl) (L₁.map Subtype.val) L₂ := by
  induction L₂ with
  | nil =>
    induction L₁ with
    | nil => exact Splits.nil
    | cons p L₁ ih => exact Splits.left p ih
  | cons q L₂ ih => exact Splits.right q ih

/-- **Filling the inputs of a composite is composing the filled operations** (the interchange
law): inserting operations at some inputs of `X ∘ᵢ Y`, in any order, is the composite of `X`
with those at its inputs inserted and `Y` with those at its inputs inserted. -/
theorem fill_comp (i : P) (X : S P) (Y : S Q) (w₁ : (p : P) → S (W₁ p))
    (w₂ : (q : Q) → S (W₂ q)) {L : List (Without P i ⊕ Q)} {L₁ : List P} {L₂ : List Q}
    (h : Splits L L₁ L₂) (hL : L.Nodup) :
    fill (SetOperad.comp i X Y) (sumVal i w₁ w₂) L hL
      = SetOperad.map (interEquiv h).symm
          (SetOperad.comp (Sum.inl ⟨i, h.not_mem⟩ : Stage W₁ L₁)
            (fill X w₁ L₁ (h.nodup_left hL)) (fill Y w₂ L₂ (h.nodup_right hL))) := by
  induction h with
  | nil =>
    rw [fill_nil, fill_nil, fill_nil,
      comp_map_left (initEquiv W₁) i (Sum.inl ⟨i, List.not_mem_nil⟩ : Stage W₁ []) rfl,
      comp_map_right]
    simp only [map_map]
    refine map_congr (fun s => ?_) _
    rcases s with p | q <;> rfl
  | left p h ih =>
    obtain ⟨hj, hL'⟩ := List.nodup_cons.1 hL
    have hp : p.1 ∉ _ := fun h' => hj ((h.mem_left p).1 h')
    have hik : (Sum.inl ⟨i, h.not_mem⟩ : Stage W₁ _) ≠ Sum.inl ⟨p.1, hp⟩ := by
      simp [Subtype.ext_iff, Ne.symm p.2]
    rw [fill_cons, fill_cons, ih hL',
      comp_map_left (interEquiv h).symm (Sum.inl ⟨Sum.inl ⟨p.1, hp⟩, Ne.symm hik⟩)
        (Sum.inl ⟨Sum.inl p, hj⟩ : Stage (sumFam W₁ W₂ i) _) rfl,
      comp_map_left (stepEquiv p.1 _ hp) (Sum.inl ⟨Sum.inl ⟨i, h.not_mem⟩, hik⟩)
        (Sum.inl ⟨i, (h.left p).not_mem⟩ : Stage W₁ (p.1 :: _)) rfl]
    erw [comp_par_eq hik]
    simp only [map_map]
    refine map_congr (fun s => ?_) _
    rcases s with ⟨(⟨(c | ⟨c, w⟩), hc⟩ | w), hw⟩ | (d | ⟨d, w⟩) <;> rfl
  | right q h ih =>
    obtain ⟨hj, hL'⟩ := List.nodup_cons.1 hL
    have hq : q ∉ _ := fun h' => hj ((h.mem_right q).1 h')
    rw [fill_cons, fill_cons, ih hL',
      comp_map_left (interEquiv h).symm (Sum.inr (Sum.inl ⟨q, hq⟩))
        (Sum.inl ⟨Sum.inr q, hj⟩ : Stage (sumFam W₁ W₂ i) _) rfl,
      comp_map_right]
    erw [comp_seq_eq]
    simp only [map_map]
    refine map_congr (fun s => ?_) _
    rcases s with ⟨(c | ⟨c, w⟩), hc⟩ | (⟨(d | ⟨d, w⟩), hd⟩ | w) <;> rfl

end Interchange

end May

open May

namespace SetOperad

section Total

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

/-- **Total composition**: the operation `y a` inserted at every input `a` of `x`. -/
noncomputable def total (x : S A) (y : (a : A) → S (B a)) : S (Σ a, B a) :=
  map (finalEquiv B _ fun a => Finset.mem_toList.2 (Finset.mem_univ a))
    (fill x y (Finset.univ : Finset A).toList (Finset.nodup_toList _))

/-- **Total composition along any order of the inputs.** -/
theorem total_eq_fill (x : S A) (y : (a : A) → S (B a)) (l : List A) (hl : l.Nodup)
    (hc : ∀ a, a ∈ l) : total x y = map (finalEquiv B l hc) (fill x y l hl) := by
  have hp : (Finset.univ : Finset A).toList.Perm l :=
    (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hl).2 fun a => by simp [hc a]
  rw [total, ← fill_perm x y hp, map_map]
  refine map_congr (fun s => ?_) _
  rcases s with c | ⟨c, b⟩
  · exact absurd (Finset.mem_toList.2 (Finset.mem_univ _)) c.2
  · rfl

/-- **Equivariance of total composition**: relabelling the inputs of the outer operation along
`σ` and those of the inserted operations along `τ a` relabels the composite along
`Equiv.sigmaCongr σ τ`. -/
theorem total_map {A' : Type} [Fintype A'] [DecidableEq A'] {B' : A' → Type}
    [∀ a, Fintype (B' a)] [∀ a, DecidableEq (B' a)] (σ : A ≃ A')
    (τ : ∀ a, B a ≃ B' (σ a)) (x : S A) (y : (a : A) → S (B a)) (y' : (a : A') → S (B' a))
    (hy : ∀ a, y' (σ a) = map (τ a) (y a)) :
    map (Equiv.sigmaCongr σ τ) (total x y) = total (map σ x) y' := by
  have hc : ∀ a, a ∈ (Finset.univ : Finset A).toList :=
    fun a => Finset.mem_toList.2 (Finset.mem_univ a)
  have hc' : ∀ a, a ∈ (Finset.univ : Finset A).toList.map σ :=
    fun a => List.mem_map.2 ⟨σ.symm a, hc _, σ.apply_symm_apply a⟩
  rw [total_eq_fill x y _ (Finset.nodup_toList _) hc,
    total_eq_fill (map σ x) y' _ ((Finset.nodup_toList _).map σ.injective) hc',
    ← fill_map σ τ x y y' hy, map_map, map_map]
  refine map_congr (fun s => ?_) _
  rcases s with c | ⟨c, b⟩
  · exact absurd (hc c.1) c.2
  · rfl

/-- **The right unit law of total composition**: inserting the unit at every input. -/
theorem total_one_right (x : S A) :
    map (Equiv.sigmaPUnit A) (total x fun _ => (one : S Unit)) = x := by
  have hc : ∀ a, a ∈ (Finset.univ : Finset A).toList :=
    fun a => Finset.mem_toList.2 (Finset.mem_univ a)
  obtain ⟨e, he, hx⟩ := fill_one x _ (Finset.nodup_toList (Finset.univ : Finset A))
  rw [total_eq_fill _ _ _ (Finset.nodup_toList _) hc, hx, map_map, map_map]
  refine (map_congr (e' := Equiv.refl A) (fun a => ?_) x).trans (map_refl x)
  have h := he a
  revert h
  simp only [Equiv.trans_apply, Equiv.refl_apply]
  rcases e a with c | ⟨c, u⟩
  · exact absurd (hc c.1) c.2
  · exact id

end Total

section TotalUnit

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {E : Unit → Type} [∀ u, Fintype (E u)] [∀ u, DecidableEq (E u)]

/-- **The left unit law of total composition**: inserting an operation into the unit. -/
theorem total_one_left (y : (u : Unit) → S (E u)) :
    map (Equiv.uniqueSigma E) (total one y) = y () := by
  rw [total_eq_fill one y [()] (List.nodup_singleton _) (fun u => List.mem_singleton.2 rfl),
    fill_cons, fill_nil,
    comp_map_left (initEquiv E) () (Sum.inl ⟨(), List.not_mem_nil⟩ : Stage E []) rfl,
    one_comp_eq]
  simp only [map_map]
  refine (map_congr (e' := Equiv.refl (E ())) (fun b => ?_) _).trans (map_refl _)
  rfl

end TotalUnit

end SetOperad

namespace May

section Assoc

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)] {C : (a : A) → B a → Type} [∀ a b, Fintype (C a b)]
  [∀ a b, DecidableEq (C a b)]

/-- **The inputs of the operations inserted at a stage**: those of `z a b` at an input `b` of
`y a`, and a single one at the inputs not filled yet. -/
def lowFam (C : (a : A) → B a → Type) (l : List A) : Stage B l → Type
  | Sum.inl _ => Unit
  | Sum.inr p => C p.1.1 p.2

instance (l : List A) (s : Stage B l) : Fintype (lowFam C l s) :=
  match s with
  | Sum.inl _ => inferInstanceAs (Fintype Unit)
  | Sum.inr p => inferInstanceAs (Fintype (C p.1.1 p.2))

instance (l : List A) (s : Stage B l) : DecidableEq (lowFam C l s) :=
  match s with
  | Sum.inl _ => inferInstanceAs (DecidableEq Unit)
  | Sum.inr p => inferInstanceAs (DecidableEq (C p.1.1 p.2))

/-- The operations inserted at a stage: `z a b` at an input `b` of `y a`, the unit elsewhere. -/
def lowVal (z : (a : A) → (b : B a) → S (C a b)) (l : List A) :
    (s : Stage B l) → S (lowFam C l s)
  | Sum.inl _ => SetOperad.one
  | Sum.inr p => z p.1.1 p.2

/-- **The inputs after filling all the inputs coming from the inserted operations**, against
those of the stage with the total composites inserted. -/
def assocEquiv (l : List A) (L : List (Stage B l)) (hL : ∀ s, s ∈ L ↔ s.isRight = true) :
    Stage (lowFam C l) L ≃ Stage (fun a => Σ b, C a b) l where
  toFun
    | Sum.inl ⟨Sum.inl c, _⟩ => Sum.inl c
    | Sum.inl ⟨Sum.inr _, h⟩ => absurd ((hL _).2 rfl) h
    | Sum.inr ⟨⟨Sum.inl _, h⟩, _⟩ => absurd ((hL _).1 h) (by simp)
    | Sum.inr ⟨⟨Sum.inr p, _⟩, w⟩ => Sum.inr ⟨p.1, ⟨p.2, w⟩⟩
  invFun
    | Sum.inl c => Sum.inl ⟨Sum.inl c, fun h => by simpa using (hL _).1 h⟩
    | Sum.inr ⟨a, ⟨b, w⟩⟩ => Sum.inr ⟨⟨Sum.inr ⟨a, b⟩, (hL _).2 rfl⟩, w⟩
  left_inv := by
    rintro (⟨(c | p), h⟩ | ⟨⟨(c | p), h⟩, w⟩)
    · rfl
    · exact absurd ((hL _).2 rfl) h
    · exact absurd ((hL _).1 h) (by simp)
    · rfl
  right_inv := by
    rintro (c | ⟨a, ⟨b, w⟩⟩) <;> rfl

/-- At a step, the inputs of the inserted operations agree on both sides. -/
def lowStep (a : A) (l : List A) (ha : a ∉ l) :
    (t : Without (Stage B l) (Sum.inl ⟨a, ha⟩) ⊕ B a) →
      sumFam (lowFam C l) (C a) (Sum.inl ⟨a, ha⟩) t ≃
        lowFam C (a :: l) (stepEquiv a l ha t)
  | Sum.inl ⟨Sum.inl _, _⟩ => Equiv.refl _
  | Sum.inl ⟨Sum.inr _, _⟩ => Equiv.refl _
  | Sum.inr _ => Equiv.refl _

/-- **Filling in two rounds is filling with total composites**: inserting `y a` at the inputs
`a ∈ l` of `x`, and then `z a b` at all the inputs `b` of the `y a`, is inserting the total
composites of the `y a` with the `z a b`. -/
theorem fill_fill (x : S A) (y : (a : A) → S (B a)) (z : (a : A) → (b : B a) → S (C a b))
    (l : List A) (hl : l.Nodup) (L : List (Stage B l)) (hL : L.Nodup)
    (hmem : ∀ s, s ∈ L ↔ s.isRight = true) :
    SetOperad.map (assocEquiv l L hmem) (fill (fill x y l hl) (lowVal z l) L hL)
      = fill x (fun a => SetOperad.total (y a) (z a)) l hl := by
  induction l with
  | nil =>
    obtain rfl : L = [] := List.eq_nil_iff_forall_not_mem.2 fun s hs => by
      rcases s with c | ⟨⟨c, hc⟩, b⟩
      · simpa using (hmem _).1 hs
      · simp at hc
    rw [fill_nil, fill_nil, fill_nil, map_map, map_map]
    refine map_congr (fun a => ?_) x
    rfl
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
    let M : List (B a) := (Finset.univ : Finset (B a)).toList
    let N : List (Without (Stage B l) (Sum.inl ⟨a, ha⟩)) :=
      (Finset.univ.filter fun s : Without (Stage B l) (Sum.inl ⟨a, ha⟩) =>
        s.1.isRight = true).toList
    have hM : M.Nodup := Finset.nodup_toList _
    have hMc : ∀ b, b ∈ M := fun b => Finset.mem_toList.2 (Finset.mem_univ b)
    have hN : N.Nodup := Finset.nodup_toList _
    have hNmem : ∀ n, n ∈ N ↔ n.1.isRight = true := fun n => by simp [N]
    have hNv : ∀ s, s ∈ N.map Subtype.val ↔ s.isRight = true := by
      intro s
      simp only [List.mem_map, hNmem]
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact hn
      · intro hs
        refine ⟨⟨s, ?_⟩, hs, rfl⟩
        rintro rfl
        simp at hs
    let K := M.map Sum.inr ++ N.map Sum.inl
    have hsplit : Splits K (N.map Subtype.val) M := splits_append N M
    have hKn : K.Nodup := by
      refine List.Nodup.append (hM.map Sum.inr_injective) (hN.map Sum.inl_injective) ?_
      intro t h₁ h₂
      simp only [List.mem_map] at h₁ h₂
      obtain ⟨b, -, rfl⟩ := h₁
      obtain ⟨n, -, h⟩ := h₂
      exact Sum.inl_ne_inr h
    have hK : ∀ t, t ∈ K ↔ (stepEquiv a l ha t).isRight = true := by
      rintro (⟨(c | p), hc⟩ | b)
      · simp only [K, List.mem_append, List.mem_map, hNmem]
        simp
        rfl
      · simp only [K, List.mem_append, List.mem_map, hNmem]
        simp
        rfl
      · simp only [K, List.mem_append, List.mem_map]
        simp [hMc]
        rfl
    have hL' : (K.map (stepEquiv a l ha)).Nodup := hKn.map (stepEquiv a l ha).injective
    have hmem' : ∀ s, s ∈ K.map (stepEquiv a l ha) ↔ s.isRight = true := by
      intro s
      rw [List.mem_map]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact (hK t).1 ht
      · intro hs
        exact ⟨(stepEquiv a l ha).symm s, (hK _).2 (by simpa using hs), by simp⟩
    have hp : (K.map (stepEquiv a l ha)).Perm L :=
      (List.perm_ext_iff_of_nodup hL' hL).2 fun s => (hmem' s).trans (hmem s).symm
    have hy : ∀ t, lowVal z (a :: l) (stepEquiv a l ha t)
        = SetOperad.map (lowStep a l ha t) (sumVal (Sum.inl ⟨a, ha⟩) (lowVal z l) (z a) t) := by
      rintro (⟨(c | p), hc⟩ | b) <;> exact (SetOperad.map_refl _).symm
    have ihN : fill (fill x y l hl') (lowVal z l) (N.map Subtype.val) (hN.map Subtype.val_injective)
        = SetOperad.map (assocEquiv l _ hNv).symm
            (fill x (fun a => SetOperad.total (y a) (z a)) l hl') := by
      rw [← ih hl' _ _ hNv, SetOperad.map_symm_map]
    have hyz : fill (y a) (z a) M hM
        = SetOperad.map (finalEquiv _ M hMc).symm (SetOperad.total (y a) (z a)) := by
      rw [SetOperad.total_eq_fill (y a) (z a) M hM hMc, SetOperad.map_symm_map]
    rw [← fill_perm _ _ hp hL' hL, fill_cons x y a l hl,
      ← fill_map (stepEquiv a l ha) (lowStep a l ha) _ _ _ hy K hKn,
      fill_comp _ _ _ _ _ hsplit hKn, ihN, hyz, fill_cons _ _ a l hl,
      comp_map_left (assocEquiv l _ hNv).symm (Sum.inl ⟨a, ha⟩)
        (Sum.inl ⟨Sum.inl ⟨a, ha⟩, hsplit.not_mem⟩ : Stage (lowFam C l) (N.map Subtype.val))
        rfl,
      comp_map_right]
    simp only [map_map]
    refine map_congr (fun s => ?_) _
    rcases s with ⟨(c | ⟨c, ⟨b, w⟩⟩), hc⟩ | ⟨b, w⟩ <;> rfl

end Assoc

end May

namespace SetOperad

section Assoc

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)] {C : (a : A) → B a → Type} [∀ a b, Fintype (C a b)]
  [∀ a b, DecidableEq (C a b)]

/-- The inputs of the operations inserted after a total composition. -/
private def lowFinal (l : List A) (hc : ∀ a, a ∈ l) :
    (s : Stage B l) → lowFam C l s ≃ C (finalEquiv B l hc s).1 (finalEquiv B l hc s).2
  | Sum.inl c => absurd (hc c.1) c.2
  | Sum.inr _ => Equiv.refl _

/-- **Associativity of total composition** (May): composing `y` into `x` and then `z` into the
result is composing into `x` the composites of `z` into the `y a`. -/
theorem total_assoc (x : S A) (y : (a : A) → S (B a)) (z : (a : A) → (b : B a) → S (C a b)) :
    map (Equiv.sigmaAssoc C) (total (total x y) fun p => z p.1 p.2)
      = total x fun a => total (y a) (z a) := by
  let l := (Finset.univ : Finset A).toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hc : ∀ a, a ∈ l := fun a => Finset.mem_toList.2 (Finset.mem_univ a)
  let L := (Finset.univ : Finset (Stage B l)).toList
  have hL : L.Nodup := Finset.nodup_toList _
  have hmem : ∀ s, s ∈ L ↔ s.isRight = true := fun s => by
    simp only [L, Finset.mem_toList, Finset.mem_univ, true_iff]
    rcases s with c | p
    · exact absurd (hc c.1) c.2
    · rfl
  have hL₂ : (L.map (finalEquiv B l hc)).Nodup := hL.map (finalEquiv B l hc).injective
  have hc₂ : ∀ p, p ∈ L.map (finalEquiv B l hc) := fun p =>
    List.mem_map.2
      ⟨(finalEquiv B l hc).symm p, Finset.mem_toList.2 (Finset.mem_univ _), by simp⟩
  have hy : ∀ s, (fun p : Σ a, B a => z p.1 p.2) (finalEquiv B l hc s)
      = map (lowFinal l hc s) (lowVal z l s) := by
    rintro (c | p)
    · exact absurd (hc c.1) c.2
    · exact (map_refl _).symm
  have key := fill_fill x y z l hl L hL hmem
  rw [total_eq_fill (total x y) _ _ hL₂ hc₂, total_eq_fill x y l hl hc,
    ← fill_map (finalEquiv B l hc) (lowFinal l hc) _ _ _ hy L hL,
    total_eq_fill x _ l hl hc, ← key]
  simp only [map_map]
  refine map_congr (fun s => ?_) _
  rcases s with ⟨(c | p), h⟩ | ⟨⟨(c | p), h⟩, w⟩
  · exact absurd (hc c.1) c.2
  · exact absurd ((hmem _).2 rfl) h
  · exact absurd ((hmem _).1 h) (by simp)
  · rfl

end Assoc

end SetOperad

namespace May

section FillCongr

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

/-- **Filling only uses the operations inserted at the inputs filled.** -/
theorem fill_congr (x : S A) {y y' : (a : A) → S (B a)} (l : List A) (hl : l.Nodup)
    (h : ∀ a ∈ l, y a = y' a) : fill x y l hl = fill x y' l hl := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [fill_cons, fill_cons, ih _ fun b hb => h b (List.mem_cons_of_mem a hb),
      h a List.mem_cons_self]

/-- The inputs other than `a`, in some order. -/
noncomputable def others (a : A) : List A := (Finset.univ.erase a).toList

lemma others_nodup (a : A) : (a :: others a).Nodup :=
  List.nodup_cons.2 ⟨by simp [others], Finset.nodup_toList _⟩

lemma mem_others (a b : A) : b ∈ a :: others a := by
  by_cases h : b = a
  · exact h ▸ List.mem_cons_self
  · exact List.mem_cons_of_mem a (by simp [others, h])

/-- **Total composition with the input `a` filled last.** -/
theorem total_eq_comp (x : S A) (y : (a : A) → S (B a)) (a : A) :
    SetOperad.total x y = SetOperad.map
      ((stepEquiv a (others a) (List.nodup_cons.1 (others_nodup a)).1).trans
        (finalEquiv B _ (mem_others a)))
      (SetOperad.comp
        (Sum.inl ⟨a, (List.nodup_cons.1 (others_nodup a)).1⟩ : Stage B (others a))
        (fill x y (others a) (List.nodup_cons.1 (others_nodup a)).2) (y a)) := by
  rw [SetOperad.total_eq_fill x y _ (others_nodup a) (mem_others a), fill_cons, map_map]

end FillCongr

end May

namespace SymOperad

open SetOperad

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]
  {A : Type} [Fintype A] [hA : DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

variable (R) in
/-- **Filling** in an operad in modules: that of its underlying set operad. -/
noncomputable def fill (x : Q A) (y : (a : A) → Q (B a)) (l : List A) (hl : l.Nodup) :
    Q (Stage B l) :=
  (Und.of R Q).symm (May.fill (S := Und R Q) (Und.of R Q x) (fun a => Und.of R Q (y a)) l hl)

lemma fill_nil (x : Q A) (y : (a : A) → Q (B a)) (h : ([] : List A).Nodup) :
    fill R x y [] h = map (R := R) (initEquiv B) x := rfl

lemma fill_cons (x : Q A) (y : (a : A) → Q (B a)) (a : A) (l : List A) (h : (a :: l).Nodup) :
    fill R x y (a :: l) h = map (R := R) (stepEquiv a l (List.nodup_cons.1 h).1)
      (comp (R := R) (Sum.inl ⟨a, (List.nodup_cons.1 h).1⟩ : Stage B l)
        (fill R x y l (List.nodup_cons.1 h).2) (y a)) := rfl

variable (R) in
/-- **Total composition** in an operad in modules: that of its underlying set operad. -/
noncomputable def total (x : Q A) (y : (a : A) → Q (B a)) : Q (Σ a, B a) :=
  (Und.of R Q).symm (SetOperad.total (S := Und R Q) (Und.of R Q x) fun a => Und.of R Q (y a))

/-- Filling, in an operad in modules, is linear in the outer operation. -/
lemma fill_add (x x' : Q A) (y : (a : A) → Q (B a)) (l : List A) (hl : l.Nodup) :
    fill R (x + x') y l hl = fill R x y l hl + fill R x' y l hl := by
  induction l with
  | nil => exact (map (R := R) (initEquiv B)).map_add x x'
  | cons a l ih =>
    rw [fill_cons, fill_cons, fill_cons, ih, map_add, LinearMap.add_apply, map_add]

/-- Filling, in an operad in modules, is linear in the outer operation. -/
lemma fill_smul (c : R) (x : Q A) (y : (a : A) → Q (B a)) (l : List A) (hl : l.Nodup) :
    fill R (c • x) y l hl = c • fill R x y l hl := by
  induction l with
  | nil => exact (map (R := R) (initEquiv B)).map_smul c x
  | cons a l ih =>
    rw [fill_cons, fill_cons, ih, map_smul, LinearMap.smul_apply, map_smul]

lemma total_eq_fill (x : Q A) (y : (a : A) → Q (B a)) (l : List A) (hl : l.Nodup)
    (hc : ∀ a, a ∈ l) : total R x y = map (R := R) (finalEquiv B l hc) (fill R x y l hl) :=
  SetOperad.total_eq_fill (S := Und R Q) _ _ l hl hc

/-- **Total composition is linear in the outer operation.** -/
theorem total_add (x x' : Q A) (y : (a : A) → Q (B a)) :
    total R (x + x') y = total R x y + total R x' y := by
  rw [total_eq_fill _ y _ (Finset.nodup_toList Finset.univ)
      fun a => Finset.mem_toList.2 (Finset.mem_univ a),
    total_eq_fill x y _ (Finset.nodup_toList Finset.univ)
      fun a => Finset.mem_toList.2 (Finset.mem_univ a),
    total_eq_fill x' y _ (Finset.nodup_toList Finset.univ)
      fun a => Finset.mem_toList.2 (Finset.mem_univ a), fill_add, map_add]

/-- **Total composition is linear in the outer operation.** -/
theorem total_smul (c : R) (x : Q A) (y : (a : A) → Q (B a)) :
    total R (c • x) y = c • total R x y := by
  rw [total_eq_fill _ y _ (Finset.nodup_toList Finset.univ)
      fun a => Finset.mem_toList.2 (Finset.mem_univ a),
    total_eq_fill x y _ (Finset.nodup_toList Finset.univ)
      fun a => Finset.mem_toList.2 (Finset.mem_univ a), fill_smul, map_smul]

/-- Total composition with one inserted operation varying. -/
lemma total_update (x : Q A) (y : (a : A) → Q (B a)) (a : A) (v : Q (B a)) :
    total R x (Function.update y a v)
      = map (R := R) ((stepEquiv a (others a) (List.nodup_cons.1 (others_nodup a)).1).trans
          (finalEquiv B _ (mem_others a)))
        (comp (R := R)
          (Sum.inl ⟨a, (List.nodup_cons.1 (others_nodup a)).1⟩ : Stage B (others a))
          (fill R x y (others a) (List.nodup_cons.1 (others_nodup a)).2) v) := by
  have := May.total_eq_comp (S := Und R Q) (Und.of R Q x)
    (fun b => Und.of R Q (Function.update y a v b)) a
  refine this.trans ?_
  congr 2
  · exact May.fill_congr _ _ _ fun b hb => by
      have hba : b ≠ a := by
        rintro rfl
        exact (List.nodup_cons.1 (others_nodup b)).1 hb
      exact Function.update_of_ne hba v y
  · exact Function.update_self a v y

/-- **Total composition is multilinear in the inserted operations.** -/
theorem total_update_add (x : Q A) (y : (a : A) → Q (B a)) (a : A) (v v' : Q (B a)) :
    total R x (Function.update y a (v + v'))
      = total R x (Function.update y a v) + total R x (Function.update y a v') := by
  rw [total_update, total_update, total_update, map_add, map_add]

/-- **Total composition is multilinear in the inserted operations.** -/
theorem total_update_smul (x : Q A) (y : (a : A) → Q (B a)) (a : A) (c : R) (v : Q (B a)) :
    total R x (Function.update y a (c • v)) = c • total R x (Function.update y a v) := by
  rw [total_update, total_update, map_smul, map_smul]

variable (R) in
/-- **Total composition as a multilinear map** of the inserted operations. -/
noncomputable def totalML (x : Q A) : MultilinearMap R (fun a => Q (B a)) (Q (Σ a, B a)) where
  toFun y := total R x y
  map_update_add' := by
    intro d y a v v'
    obtain rfl : d = hA := Subsingleton.elim _ _
    exact total_update_add x y a v v'
  map_update_smul' := by
    intro d y a c v
    obtain rfl : d = hA := Subsingleton.elim _ _
    exact total_update_smul x y a c v

variable (R) in
/-- **Total composition**, linear in the outer operation and multilinear in the inserted ones. -/
noncomputable def totalL : Q A →ₗ[R] MultilinearMap R (fun a => Q (B a)) (Q (Σ a, B a)) where
  toFun := totalML R
  map_add' x x' := MultilinearMap.ext fun y => total_add x x' y
  map_smul' c x := MultilinearMap.ext fun y => total_smul c x y

/-! ### May's axioms in an operad in modules -/

/-- **Equivariance of total composition** in an operad in modules. -/
theorem total_map {A' : Type} [Fintype A'] [DecidableEq A'] {B' : A' → Type}
    [∀ a, Fintype (B' a)] [∀ a, DecidableEq (B' a)] (σ : A ≃ A')
    (τ : ∀ a, B a ≃ B' (σ a)) (x : Q A) (y : (a : A) → Q (B a)) (y' : (a : A') → Q (B' a))
    (hy : ∀ a, y' (σ a) = map (R := R) (τ a) (y a)) :
    map (R := R) (Equiv.sigmaCongr σ τ) (total R x y) = total R (map (R := R) σ x) y' :=
  SetOperad.total_map (S := Und R Q) σ τ _ _ _ hy

/-- **The right unit law of total composition** in an operad in modules. -/
theorem total_one_right (x : Q A) :
    map (R := R) (Equiv.sigmaPUnit A) (total R x fun _ => (one R : Q Unit)) = x :=
  SetOperad.total_one_right (S := Und R Q) x

/-- **The left unit law of total composition** in an operad in modules. -/
theorem total_one_left {E : Unit → Type} [∀ u, Fintype (E u)] [∀ u, DecidableEq (E u)]
    (y : (u : Unit) → Q (E u)) :
    map (R := R) (Equiv.uniqueSigma E) (total R (one R) y) = y () :=
  SetOperad.total_one_left (S := Und R Q) y

/-- **Associativity of total composition** in an operad in modules. -/
theorem total_assoc {C : (a : A) → B a → Type} [∀ a b, Fintype (C a b)]
    [∀ a b, DecidableEq (C a b)] (x : Q A) (y : (a : A) → Q (B a))
    (z : (a : A) → (b : B a) → Q (C a b)) :
    map (R := R) (Equiv.sigmaAssoc C) (total R (total R x y) fun p => z p.1 p.2)
      = total R x fun a => total R (y a) (z a) :=
  SetOperad.total_assoc (S := Und R Q) x y z

end SymOperad

end Operad
