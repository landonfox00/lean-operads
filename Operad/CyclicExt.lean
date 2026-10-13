/-
# Cyclic operads as operads with an extended action

The underlying operad `A ↦ C (Option A)` of a cyclic operad on a species `C`, with the
relabellings of `C` along all bijections of `Option A`, carries a compatible extended symmetric
action (`CycOperad.ExtCompat`). Conversely (`CycOperad.ofExt`), an operad structure on
`A ↦ C (Option A)` for which the relabellings of `C` form a compatible extended action comes from
a cyclic operad structure on `C`, provided `C` vanishes on empty sets of entries, which the
underlying operad does not see: **cyclic operad structures on `C` are the operad structures on
`C ∘ Option` with a compatible extended action** (`CycOperad.extEquiv`).

The gluing of an entry `a` of `x` to an entry `b` of `y` is computed in the underlying operad by
rooting `x` at another entry `r` and `y` at `b`, and filling the input `a` of the first with the
second (`CycOperad.compX`); the compatibility of the extended action makes this independent of
the root (`CycOperad.compX_root`, `CycOperad.compX_eq_compY`).
-/
import Operad.Cyclic

universe u v

set_option synthInstance.maxSize 1024

attribute [-instance] Option.decidableEqNone Option.decidableNoneEq

namespace Operad

open Sym

/-! ## Rooting bijections -/

section Equivs

variable {W V X Y : Type} [DecidableEq W] [DecidableEq V] [DecidableEq X] [DecidableEq Y]

/-- The values of an option type other than `none`. -/
def someEquiv (W : Type) [DecidableEq W] : W ≃ Without (Option W) none where
  toFun w := ⟨some w, Option.some_ne_none w⟩
  invFun o :=
    match o with
    | ⟨some w, _⟩ => w
    | ⟨none, h⟩ => absurd rfl h
  left_inv _ := rfl
  right_inv := by
    rintro ⟨(_ | w), h⟩
    · exact absurd rfl h
    · rfl

/-- A bijection `Option W ≃ V` sending the root `none` to `p` restricts to `W ≃ V ∖ p`. -/
def restrictRoot (e : Option W ≃ V) {p : V} (hp : e none = p) : W ≃ Without V p :=
  (someEquiv W).trans (e.subtypeEquiv fun _ => by rw [← hp]; exact e.injective.ne_iff.symm)

@[simp] lemma restrictRoot_apply_coe (e : Option W ≃ V) {p : V} (hp : e none = p) (w : W) :
    (restrictRoot e hp w).1 = e (some w) := rfl

lemma trans_rootEquiv_symm (e : Option W ≃ V) {p : V} (hp : e none = p) :
    e.trans (rootEquiv p).symm = (restrictRoot e hp).optionCongr := by
  refine Equiv.ext fun o => ?_
  rcases o with _ | w
  · show (rootEquiv p).symm (e none) = none
    rw [hp, rootEquiv_symm_self]
  · show (rootEquiv p).symm (e (some w)) = some (restrictRoot e hp w)
    rw [rootEquiv_symm_of_ne (x := e (some w)) (restrictRoot e hp w).2]
    rfl

/-- The entries of a composite rooted at an entry `r ≠ a` of the first operation:
`Option (((X ∖ r) ∖ a) ⊔ (Y ∖ b)) ≅ (X ∖ a) ⊔ (Y ∖ b)`. -/
def rootedGlueEquiv (a : X) (b : Y) (r : X) (hr : r ≠ a) :
    Option (Without (Without X r) ⟨a, Ne.symm hr⟩ ⊕ Without Y b)
      ≃ Without X a ⊕ Without Y b where
  toFun w :=
    match w with
    | none => Sum.inl ⟨r, hr⟩
    | some (Sum.inl x) => Sum.inl ⟨x.1.1, fun h => x.2 (Subtype.ext h)⟩
    | some (Sum.inr y) => Sum.inr y
  invFun w :=
    match w with
    | Sum.inl x =>
        if h : x.1 = r then none
        else some (Sum.inl ⟨⟨x.1, h⟩, fun e => x.2 (congrArg Subtype.val e)⟩)
    | Sum.inr y => some (Sum.inr y)
  left_inv := by
    rintro (_ | (⟨⟨x, h₁⟩, h₂⟩ | y))
    · simp
    · simp [h₁]
    · rfl
  right_inv := by
    rintro (⟨x, hx⟩ | y)
    · by_cases h : x = r
      · subst h
        simp
      · simp [h]
    · rfl

/-- `compEquiv` with the slot given up to equality. -/
def compEquiv' {A A' B B' : Type} [DecidableEq A] [DecidableEq A'] (σ : A ≃ A') (τ : B ≃ B')
    {i : A} {i' : A'} (hi : σ i = i') : Without A i ⊕ B ≃ Without A' i' ⊕ B' :=
  Equiv.sumCongr (σ.subtypeEquiv fun _ => by rw [← hi]; exact σ.injective.ne_iff.symm) τ

end Equivs

/-! ## Relabelled composites in an operad -/

namespace SymOperad

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype B]
  [DecidableEq B] [Fintype B'] [DecidableEq B']

/-- Composing relabelled operations, at a slot given up to equality. -/
lemma comp_map_map_of_eq (σ : A ≃ A') (τ : B ≃ B') {i : A} {i' : A'} (hi : σ i = i') (x : P A)
    (y : P B) :
    comp (R := R) i' (map (R := R) σ x) (map (R := R) τ y)
      = map (R := R) (compEquiv' σ τ hi) (comp (R := R) i x y) := by
  subst hi
  rw [← map_comp]
  exact congrArg (fun e => map (R := R) e (comp (R := R) i x y))
    (Equiv.ext fun w => by rcases w with ⟨a, ha⟩ | b <;> rfl)

omit [Fintype B'] [DecidableEq B'] in
lemma comp_map_left_of_eq (σ : A ≃ A') {i : A} {i' : A'} (hi : σ i = i') (x : P A) (y : P B) :
    comp (R := R) i' (map (R := R) σ x) y
      = map (R := R) (compEquiv' σ (Equiv.refl B) hi) (comp (R := R) i x y) := by
  have := comp_map_map_of_eq (R := R) σ (Equiv.refl B) hi x y
  rwa [map_refl] at this

omit [Fintype A'] [DecidableEq A'] in
lemma comp_map_right_of_eq (τ : B ≃ B') (i : A) (x : P A) (y : P B) :
    comp (R := R) i x (map (R := R) τ y)
      = map (R := R) (compEquiv' (Equiv.refl A) τ rfl) (comp (R := R) i x y) := by
  have := comp_map_map_of_eq (R := R) (Equiv.refl A) τ (rfl : (Equiv.refl A) i = i) x y
  rwa [map_refl] at this

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
lemma eq_map_symm_of_eq (e : A ≃ B) {x : P A} {y : P B} (h : y = map (R := R) e x) :
    x = map (R := R) e.symm y := by
  rw [h, ← map_trans, Equiv.self_trans_symm, map_refl]

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
/-- Sequential associativity, solved for the nested composite. -/
lemma comp_seq_eq {D : Type} [Fintype D] [DecidableEq D] (i : A) (j : B) (x : P A) (y : P B)
    (z : P D) :
    comp (R := R) (Sum.inr j) (comp (R := R) i x y) z
      = map (R := R) (seqEquiv i j D).symm (comp (R := R) i x (comp (R := R) j y z)) :=
  eq_map_symm_of_eq (R := R) _ (comp_assoc_seq (R := R) i j x y z).symm

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
/-- Parallel associativity, solved for the first nested composite. -/
lemma comp_par_eq {D : Type} [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (x : P A)
    (y : P B) (z : P D) :
    comp (R := R) (Sum.inl ⟨k, Ne.symm hik⟩) (comp (R := R) i x y) z
      = map (R := R) (parEquiv hik B D).symm
          (comp (R := R) (Sum.inl ⟨i, hik⟩) (comp (R := R) k x z) y) :=
  eq_map_symm_of_eq (R := R) _ (comp_assoc_par (R := R) hik x y z).symm

omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
/-- The left unit, solved for the composite. -/
lemma comp_one_left (y : P B) :
    comp (R := R) () (one R) y = map (R := R) (leftUnitEquiv B).symm y :=
  eq_map_symm_of_eq (R := R) _ (one_comp (R := R) y).symm

end SymOperad

namespace CycOperad

/-! ## Compatible extended actions -/

/-- **A compatible extended action** on an operad structure on `A ↦ C (Option A)`: its
relabellings are those of `C` along bijections fixing the output, and the relabellings of `C`
along all bijections of the entries fix the unit and are compatible with composition. -/
class ExtCompat (R : Type u) [CommRing R]
    (C : (X : Type) → [Fintype X] → [DecidableEq X] → Type v)
    [∀ (X : Type) [Fintype X] [DecidableEq X], AddCommGroup (C X)]
    [∀ (X : Type) [Fintype X] [DecidableEq X], Module R (C X)] [SymSpecies R C]
    [SymOperad R (Und C)] : Prop where
  /-- Relabelling the inputs is relabelling the entries, fixing the output. -/
  map_eq {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : Und C A) :
    SymOperad.map (R := R) (P := Und C) e x = SymSpecies.map (R := R) (V := C) e.optionCongr x
  /-- The unit is symmetric. -/
  map_swap_one :
    SymSpecies.map (R := R) (V := C) unitSwap (SymOperad.one (P := Und C) R)
      = SymOperad.one (P := Und C) R
  /-- Rerooting at an input of the outer operation. -/
  reroot_comp_inl {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) (r : Without A i) (x : Und C A) (y : Und C B) :
    SymSpecies.map (R := R) (V := C) (rootEquiv (some (Sum.inl r))).symm
        (SymOperad.comp (R := R) (P := Und C) i x y)
      = SymOperad.map (R := R) (P := Und C) (rerootInlEquiv i r)
          (SymOperad.comp (R := R) (P := Und C)
            ⟨some i, fun h => r.2 (Option.some_injective _ h).symm⟩
            (SymSpecies.map (R := R) (V := C) (rootEquiv (some r.1)).symm x) y)
  /-- Rerooting at an input of the inner operation. -/
  reroot_comp_inr {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) (b : B) (x : Und C A) (y : Und C B) :
    SymSpecies.map (R := R) (V := C) (rootEquiv (some (Sum.inr b))).symm
        (SymOperad.comp (R := R) (P := Und C) i x y)
      = SymOperad.map (R := R) (P := Und C) (rerootInrEquiv i b)
          (SymOperad.comp (R := R) (P := Und C) ⟨none, (Option.some_ne_none b).symm⟩
            (SymSpecies.map (R := R) (V := C) (rootEquiv (some b)).symm y)
            (SymSpecies.map (R := R) (V := C) (rootEquiv (some i)).symm x))

section FromCyc

variable {R : Type u} [CommRing R] {C : (X : Type) → [Fintype X] → [DecidableEq X] → Type v}
  [∀ (X : Type) [Fintype X] [DecidableEq X], AddCommGroup (C X)]
  [∀ (X : Type) [Fintype X] [DecidableEq X], Module R (C X)] [SymSpecies R C] [CycOperad R C]

/-- **The extended action of a cyclic operad is compatible.** -/
instance extCompat : ExtCompat R C where
  map_eq _ _ := rfl
  map_swap_one := und_map_swap_one
  reroot_comp_inl := reroot_comp_inl
  reroot_comp_inr := reroot_comp_inr

end FromCyc

/-! ## Gluing in the underlying operad -/

section Ext

variable {R : Type u} [CommRing R] {C : (X : Type) → [Fintype X] → [DecidableEq X] → Type v}
  [∀ (X : Type) [Fintype X] [DecidableEq X], AddCommGroup (C X)]
  [∀ (X : Type) [Fintype X] [DecidableEq X], Module R (C X)] [SymSpecies R C]
  [SymOperad R (Und C)] [ExtCompat R C]
  {X X' Y Y' Z : Type} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X'] [Fintype Y]
  [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
lemma pmap_eq (e : X ≃ Y) (x : Und C X) :
    SymOperad.map (R := R) (P := Und C) e x = SymSpecies.map (R := R) (V := C) e.optionCongr x :=
  ExtCompat.map_eq e x

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
/-- Rooting a relabelled operation at the image of its root. -/
lemma reroot_map (e : Option X ≃ Y) {p : Y} (hp : e none = p) (u : Und C X) :
    SymSpecies.map (R := R) (V := C) (rootEquiv p).symm (SymSpecies.map (R := R) (V := C) e u)
      = SymOperad.map (R := R) (P := Und C) (restrictRoot e hp) u := by
  rw [map_map, trans_rootEquiv_symm e hp, pmap_eq]

omit [Fintype X'] [DecidableEq X'] [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
  [Fintype Z] [DecidableEq Z] in
/-- Rooting at `r'` is rooting at `r`, then at `r'`, and relabelling. -/
lemma reroot_twice {r r' : X} (h : r' ≠ r) (x : C X) :
    SymSpecies.map (R := R) (V := C) (rootEquiv r').symm x
      = SymOperad.map (R := R) (P := Und C)
          (restrictRoot (p := r')
            ((rootEquiv (some (⟨r', h⟩ : Without X r))).trans (rootEquiv r)) rfl)
          (SymSpecies.map (R := R) (V := C) (rootEquiv (some (⟨r', h⟩ : Without X r))).symm
            (SymSpecies.map (R := R) (V := C) (rootEquiv r).symm x)) := by
  rw [← reroot_map]
  merge_maps
  exact map_congr (Equiv.ext fun t => by simp) x

omit [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
/-- Rooting a relabelled operation. -/
lemma reroot_relabel (σ : X ≃ X') (r : X) (x : C X) :
    SymSpecies.map (R := R) (V := C) (rootEquiv (σ r)).symm (SymSpecies.map (R := R) (V := C) σ x)
      = SymOperad.map (R := R) (P := Und C) (restrictRoot (p := σ r) ((rootEquiv r).trans σ) rfl)
          (SymSpecies.map (R := R) (V := C) (rootEquiv r).symm x) := by
  rw [← reroot_map]
  merge_maps
  exact map_congr (Equiv.ext fun t => by simp) x

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
/-- Rerooting at an input of the outer operation, solved for the composite. -/
lemma comp_eq_reroot_inl (i : X) (r : Without X i) (x : Und C X) (y : Und C Y) :
    SymOperad.comp (R := R) (P := Und C) i x y
      = SymSpecies.map (R := R) (V := C) (rootEquiv (some (Sum.inl r)))
          (SymOperad.map (R := R) (P := Und C) (rerootInlEquiv i r)
            (SymOperad.comp (R := R) (P := Und C)
              ⟨some i, fun h => r.2 (Option.some_injective _ h).symm⟩
              (SymSpecies.map (R := R) (V := C) (rootEquiv (some r.1)).symm x) y)) := by
  rw [← ExtCompat.reroot_comp_inl, map_map, Equiv.symm_trans_self, SymSpecies.map_refl]

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
/-- Rerooting at an input of the inner operation, solved for the composite. -/
lemma comp_eq_reroot_inr (i : X) (b : Y) (x : Und C X) (y : Und C Y) :
    SymOperad.comp (R := R) (P := Und C) i x y
      = SymSpecies.map (R := R) (V := C) (rootEquiv (some (Sum.inr b)))
          (SymOperad.map (R := R) (P := Und C) (rerootInrEquiv i b)
            (SymOperad.comp (R := R) (P := Und C) ⟨none, (Option.some_ne_none b).symm⟩
              (SymSpecies.map (R := R) (V := C) (rootEquiv (some b)).symm y)
              (SymSpecies.map (R := R) (V := C) (rootEquiv (some i)).symm x))) := by
  rw [← ExtCompat.reroot_comp_inr, map_map, Equiv.symm_trans_self, SymSpecies.map_refl]

variable (R) in
/-- **Gluing computed in the underlying operad, rooted at an entry `r ≠ a` of the first
operation**: root the first operation at `r` and the second at `b`, and fill the input `a` of the
first with the second. -/
def compX (a : X) (b : Y) (r : X) (hr : r ≠ a) :
    C X →ₗ[R] C Y →ₗ[R] C (Without X a ⊕ Without Y b) :=
  ((SymOperad.comp (R := R) (P := Und C) (⟨a, Ne.symm hr⟩ : Without X r)).compl₁₂
      (SymSpecies.map (R := R) (V := C) (rootEquiv r).symm)
      (SymSpecies.map (R := R) (V := C) (rootEquiv b).symm)).compr₂
    (SymSpecies.map (R := R) (V := C) (rootedGlueEquiv a b r hr))

omit [ExtCompat R C] [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z]
  [DecidableEq Z] in
lemma compX_apply (a : X) (b : Y) (r : X) (hr : r ≠ a) (x : C X) (y : C Y) :
    compX R a b r hr x y = SymSpecies.map (R := R) (V := C) (rootedGlueEquiv a b r hr)
      (SymOperad.comp (R := R) (P := Und C) (⟨a, Ne.symm hr⟩ : Without X r)
        (SymSpecies.map (R := R) (V := C) (rootEquiv r).symm x)
        (SymSpecies.map (R := R) (V := C) (rootEquiv b).symm y)) := rfl

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
/-- **Gluing does not depend on the root** chosen in the first operation. -/
theorem compX_root (a : X) (b : Y) {r r' : X} (hr : r ≠ a) (hr' : r' ≠ a) (x : C X)
    (y : C Y) : compX R a b r hr x y = compX R a b r' hr' x y := by
  by_cases h : r' = r
  · subst h
    rfl
  rw [compX_apply, compX_apply, reroot_twice h x,
    SymOperad.comp_map_left_of_eq (R := R) (P := Und C)
      (restrictRoot (p := r') ((rootEquiv (some (⟨r', h⟩ : Without X r))).trans (rootEquiv r)) rfl)
      (i := ⟨some ⟨a, Ne.symm hr⟩,
        fun e => hr' (congrArg Subtype.val (Option.some_injective _ e)).symm⟩)
      (i' := ⟨a, Ne.symm hr'⟩) rfl]
  conv_lhs => rw [comp_eq_reroot_inl (R := R) (C := C) (⟨a, Ne.symm hr⟩ : Without X r)
    ⟨⟨r', h⟩, fun e => hr' (congrArg Subtype.val e)⟩]
  simp only [pmap_eq]
  merge_maps
  refine map_congr (Equiv.ext fun t => ?_) _
  rcases t with _ | (⟨⟨⟨(_ | ⟨x', h₀⟩), h₁⟩, h₂⟩, h₃⟩ | y')
  · rfl
  · rfl
  · rfl
  · rfl

/-- Gluing rooted at an entry `s ≠ b` of the second operation. -/
abbrev compY (a : X) (b : Y) (s : Y) (hs : s ≠ b) (x : C X) (y : C Y) :
    C (Without X a ⊕ Without Y b) :=
  SymSpecies.map (R := R) (V := C) (Equiv.sumComm _ _) (compX R b a s hs y x)

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
/-- **Rooting in either operation gives the same gluing.** -/
theorem compX_eq_compY (a : X) (b : Y) {r : X} (hr : r ≠ a) {s : Y} (hs : s ≠ b) (x : C X)
    (y : C Y) : compX R a b r hr x y = compY (R := R) a b s hs x y := by
  rw [compY, compX_apply, compX_apply, reroot_twice hs y, reroot_twice (Ne.symm hr) x,
    SymOperad.comp_map_map_of_eq (R := R) (P := Und C)
      (restrictRoot (p := s)
        ((rootEquiv (some (⟨s, hs⟩ : Without Y b))).trans (rootEquiv b)) rfl)
      (restrictRoot (p := a)
        ((rootEquiv (some (⟨a, Ne.symm hr⟩ : Without X r))).trans (rootEquiv r)) rfl)
      (i := ⟨none, (Option.some_ne_none (⟨s, hs⟩ : Without Y b)).symm⟩)
      (i' := ⟨b, Ne.symm hs⟩) rfl]
  conv_lhs => rw [comp_eq_reroot_inr (R := R) (C := C) (⟨a, Ne.symm hr⟩ : Without X r)
    (⟨s, hs⟩ : Without Y b)]
  simp only [pmap_eq]
  merge_maps
  refine map_congr (Equiv.ext fun t => ?_) _
  rcases t with _ | (⟨⟨⟨(_ | ⟨y', h₀⟩), h₁⟩, h₂⟩, h₃⟩ | ⟨(_ | ⟨x', h₀⟩), h₁⟩)
  · rfl
  · exact absurd rfl h₃
  · rfl
  · rfl
  · rfl

omit [Fintype Z] [DecidableEq Z] in
/-- **Gluing in the underlying operad is equivariant.** -/
theorem compX_map (σ : X ≃ X') (τ : Y ≃ Y') (a : X) (b : Y) (r : X) (hr : r ≠ a) (x : C X)
    (y : C Y) :
    compX R (σ a) (τ b) (σ r) (σ.injective.ne hr) (SymSpecies.map (R := R) (V := C) σ x)
        (SymSpecies.map (R := R) (V := C) τ y)
      = SymSpecies.map (R := R) (V := C) (glueEquiv σ τ a b) (compX R a b r hr x y) := by
  rw [compX_apply, compX_apply, reroot_relabel σ r x, reroot_relabel τ b y,
    SymOperad.comp_map_map_of_eq (R := R) (P := Und C)
      (restrictRoot (p := σ r) ((rootEquiv r).trans σ) rfl)
      (restrictRoot (p := τ b) ((rootEquiv b).trans τ) rfl)
      (i := (⟨a, Ne.symm hr⟩ : Without X r)) (i' := ⟨σ a, Ne.symm (σ.injective.ne hr)⟩) rfl]
  simp only [pmap_eq]
  merge_maps
  refine map_congr (Equiv.ext fun t => ?_) _
  rcases t with _ | (⟨⟨x', h₁⟩, h₂⟩ | ⟨y', h⟩)
  · rfl
  · rfl
  · rfl

omit [SymOperad R (Und C)] [ExtCompat R C] [Fintype X'] [DecidableEq X'] [Fintype Y']
  [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
lemma map_map_symm' (e : X ≃ Y) (y : C Y) :
    SymSpecies.map (R := R) (V := C) e (SymSpecies.map (R := R) (V := C) e.symm y) = y := by
  rw [map_map, Equiv.symm_trans_self, SymSpecies.map_refl]

/-! ## The cyclic composition -/

variable (R) in
/-- **The cyclic composition of an operad with a compatible extended action**: rooted at an
entry of the first operation other than `a` if there is one, otherwise at an entry of the second
other than `b`, and zero when no entries are left. -/
noncomputable def ecomp (a : X) (b : Y) : C X →ₗ[R] C Y →ₗ[R] C (Without X a ⊕ Without Y b) :=
  if h : ∃ r, r ≠ a then compX R a b h.choose h.choose_spec
  else if h' : ∃ s, s ≠ b then
    (compX R b a h'.choose h'.choose_spec).flip.compr₂
      (SymSpecies.map (R := R) (V := C) (Equiv.sumComm _ _))
  else 0

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
lemma ecomp_eq_compX (a : X) (b : Y) {r : X} (hr : r ≠ a) (x : C X) (y : C Y) :
    ecomp R a b x y = compX R a b r hr x y := by
  have h : ∃ r, r ≠ a := ⟨r, hr⟩
  rw [ecomp, dif_pos h]
  exact compX_root a b _ hr x y

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
lemma ecomp_eq_compY (a : X) (b : Y) {s : Y} (hs : s ≠ b) (x : C X) (y : C Y) :
    ecomp R a b x y = compY (R := R) a b s hs x y := by
  by_cases h : ∃ r, r ≠ a
  · obtain ⟨r, hr⟩ := h
    rw [ecomp_eq_compX a b hr, compX_eq_compY a b hr hs]
  · have h' : ∃ s, s ≠ b := ⟨s, hs⟩
    rw [ecomp, dif_neg h, dif_pos h']
    show SymSpecies.map (R := R) (V := C) (Equiv.sumComm _ _) (compX R b a _ _ y x) = _
    rw [compX_root b a h'.choose_spec hs y x]

omit [Fintype Z] [DecidableEq Z] in
/-- **The cyclic composition is equivariant.** -/
theorem ecomp_map (hC : ∀ (X : Type) [Fintype X] [DecidableEq X], IsEmpty X → Subsingleton (C X))
    (σ : X ≃ X') (τ : Y ≃ Y') (a : X) (b : Y) (x : C X) (y : C Y) :
    SymSpecies.map (R := R) (V := C) (glueEquiv σ τ a b) (ecomp R a b x y)
      = ecomp R (σ a) (τ b) (SymSpecies.map (R := R) (V := C) σ x)
          (SymSpecies.map (R := R) (V := C) τ y) := by
  by_cases ha : ∃ r, r ≠ a
  · obtain ⟨r, hr⟩ := ha
    rw [ecomp_eq_compX a b hr, ecomp_eq_compX (σ a) (τ b) (σ.injective.ne hr), compX_map]
  by_cases hb : ∃ s, s ≠ b
  · obtain ⟨s, hs⟩ := hb
    rw [ecomp_eq_compY a b hs, ecomp_eq_compY (σ a) (τ b) (τ.injective.ne hs), compY, compY,
      compX_map]
    merge_maps
    exact map_congr (Equiv.ext fun t => by rcases t with _ | (t | t) <;> rfl) _
  · haveI := hC (Without X' (σ a) ⊕ Without Y' (τ b)) ⟨by
        rintro (⟨x', hx'⟩ | ⟨y', hy'⟩)
        · exact ha ⟨σ.symm x', fun e => hx' (by rw [← e, Equiv.apply_symm_apply])⟩
        · exact hb ⟨τ.symm y', fun e => hy' (by rw [← e, Equiv.apply_symm_apply])⟩⟩
    exact Subsingleton.elim _ _

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
/-- **The cyclic composition is commutative.** -/
theorem ecomp_comm (hC : ∀ (X : Type) [Fintype X] [DecidableEq X], IsEmpty X → Subsingleton (C X))
    (a : X) (b : Y) (x : C X) (y : C Y) :
    SymSpecies.map (R := R) (V := C) (Equiv.sumComm _ _) (ecomp R a b x y) = ecomp R b a y x := by
  by_cases ha : ∃ r, r ≠ a
  · obtain ⟨r, hr⟩ := ha
    rw [ecomp_eq_compX a b hr, ecomp_eq_compY b a hr]
  by_cases hb : ∃ s, s ≠ b
  · obtain ⟨s, hs⟩ := hb
    rw [ecomp_eq_compY a b hs, ecomp_eq_compX b a hs, compY, map_map]
    conv_rhs => rw [← SymSpecies.map_refl (R := R) (compX R b a s hs y x)]
    exact map_congr (Equiv.ext fun t => by rcases t with t | t <;> rfl) _
  · haveI := hC (Without Y b ⊕ Without X a) ⟨by
        rintro (⟨y', hy'⟩ | ⟨x', hx'⟩)
        · exact hb ⟨y', hy'⟩
        · exact ha ⟨x', hx'⟩⟩
    exact Subsingleton.elim _ _

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
/-- **The unit of the operad is a unit for the cyclic composition.** -/
theorem ecomp_one (a : X) (x : C X) :
    SymSpecies.map (R := R) (V := C) (glueUnitEquiv a)
      (ecomp R a none x (SymOperad.one (P := Und C) R)) = x := by
  rw [ecomp_eq_compY a none (Option.some_ne_none ()), compY, compX_apply,
    ← ExtCompat.map_swap_one (R := R) (C := C), reroot_map (p := some ()) unitSwap rfl,
    SymOperad.comp_map_left_of_eq (R := R) (P := Und C) (restrictRoot (p := some ()) unitSwap rfl)
      (i := ()) (i' := ⟨none, (Option.some_ne_none ()).symm⟩) rfl,
    SymOperad.comp_one_left]
  conv_rhs => rw [← map_map_symm' (R := R) (rootEquiv a) x]
  generalize SymSpecies.map (R := R) (V := C) (rootEquiv a).symm x = u
  simp only [pmap_eq]
  merge_maps
  refine map_congr (Equiv.ext fun t => ?_) u
  rcases t with _ | ⟨x', h⟩
  · rfl
  · rfl

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] in
/-- **The cyclic composition is associative.** -/
theorem ecomp_assoc
    (hC : ∀ (X : Type) [Fintype X] [DecidableEq X], IsEmpty X → Subsingleton (C X))
    (a : X) (b : Y) (c : Without Y b) (d : Z) (x : C X) (y : C Y) (z : C Z) :
    SymSpecies.map (R := R) (V := C) (glueAssocEquiv a b c d)
        (ecomp R (Sum.inr c) d (ecomp R a b x y) z)
      = ecomp R a (Sum.inl ⟨b, Ne.symm c.2⟩) x (ecomp R c.1 d y z) := by
  by_cases hA : ∃ r, r ≠ a
  · -- rooted in the first operation
    obtain ⟨r, hr⟩ := hA
    rw [ecomp_eq_compX a b hr x y,
      ecomp_eq_compX (Sum.inr c) d (r := Sum.inl ⟨r, hr⟩) Sum.inl_ne_inr,
      ecomp_eq_compX c.1 d (r := b) (Ne.symm c.2) y z,
      ecomp_eq_compX a (Sum.inl ⟨b, Ne.symm c.2⟩ : Without Y c.1 ⊕ Without Z d) hr x]
    simp only [compX_apply]
    rw [reroot_map (p := Sum.inl ⟨r, hr⟩) (rootedGlueEquiv a b r hr) rfl,
      reroot_map (p := Sum.inl ⟨b, Ne.symm c.2⟩) (rootedGlueEquiv c.1 d b (Ne.symm c.2)) rfl,
      SymOperad.comp_map_left_of_eq (R := R) (P := Und C)
        (restrictRoot (p := Sum.inl ⟨r, hr⟩) (rootedGlueEquiv a b r hr) rfl) (i := Sum.inr c)
        (i' := ⟨Sum.inr c, Sum.inr_ne_inl⟩) rfl,
      SymOperad.comp_seq_eq (R := R) (P := Und C),
      SymOperad.comp_map_right_of_eq (R := R) (P := Und C)
        (restrictRoot (p := Sum.inl ⟨b, Ne.symm c.2⟩) (rootedGlueEquiv c.1 d b (Ne.symm c.2)) rfl)]
    simp only [pmap_eq]
    merge_maps
    refine map_congr (Equiv.ext fun t => ?_) _
    rcases t with _ | (⟨⟨x', h₁⟩, h₂⟩ | (⟨⟨y', h₁⟩, h₂⟩ | ⟨z', h₁⟩))
    · rfl
    · rfl
    · rfl
    · rfl
  by_cases hB : ∃ s, s ≠ b ∧ s ≠ c.1
  · -- rooted in the second operation
    obtain ⟨s, hsb, hsc⟩ := hB
    have hcs : c.1 ≠ s := Ne.symm hsc
    rw [ecomp_eq_compY a b hsb x y,
      ecomp_eq_compX (Sum.inr c) d (r := Sum.inr ⟨s, hsb⟩)
        (fun e => hsc (congrArg Subtype.val (Sum.inr_injective e))),
      ecomp_eq_compX c.1 d (r := s) hsc y z,
      ecomp_eq_compY a (Sum.inl ⟨b, Ne.symm c.2⟩ : Without Y c.1 ⊕ Without Z d)
        (s := Sum.inl ⟨s, hsc⟩) (fun e => hsb (congrArg Subtype.val (Sum.inl_injective e))) x]
    simp only [compY, compX_apply]
    rw [map_map (e := rootedGlueEquiv b a s hsb) (f := Equiv.sumComm _ _),
      reroot_map (p := Sum.inr ⟨s, hsb⟩)
        ((rootedGlueEquiv b a s hsb).trans (Equiv.sumComm _ _)) rfl,
      reroot_map (p := Sum.inl ⟨s, hsc⟩) (rootedGlueEquiv c.1 d s hsc) rfl,
      SymOperad.comp_map_left_of_eq (R := R) (P := Und C)
        (restrictRoot (p := Sum.inr ⟨s, hsb⟩)
          ((rootedGlueEquiv b a s hsb).trans (Equiv.sumComm _ _)) rfl)
        (i := Sum.inl ⟨⟨c.1, hcs⟩, fun e => c.2 (congrArg Subtype.val e)⟩)
        (i' := ⟨Sum.inr c, fun e => hsc (congrArg Subtype.val (Sum.inr_injective e)).symm⟩) rfl,
      SymOperad.comp_par_eq (R := R) (P := Und C) (i := (⟨b, Ne.symm hsb⟩ : Without Y s))
        (k := ⟨c.1, hcs⟩) (fun e => c.2 (congrArg Subtype.val e).symm),
      SymOperad.comp_map_left_of_eq (R := R) (P := Und C)
        (restrictRoot (p := Sum.inl ⟨s, hsc⟩) (rootedGlueEquiv c.1 d s hsc) rfl)
        (i := Sum.inl ⟨⟨b, Ne.symm hsb⟩, fun e => c.2 (congrArg Subtype.val e).symm⟩)
        (i' := ⟨Sum.inl ⟨b, Ne.symm c.2⟩,
          fun e => hsb (congrArg Subtype.val (Sum.inl_injective e)).symm⟩) rfl]
    simp only [pmap_eq]
    merge_maps
    refine map_congr (Equiv.ext fun t => ?_) _
    rcases t with _ | (⟨(⟨⟨y', h₁⟩, h₂⟩ | ⟨z', h₂⟩), h₃⟩ | ⟨x', h₁⟩)
    · rfl
    · rfl
    · rfl
    · rfl
  by_cases hD : ∃ t, t ≠ d
  · -- rooted in the third operation
    obtain ⟨t, ht⟩ := hD
    rw [ecomp_eq_compY a b c.2 x y, ecomp_eq_compY (Sum.inr c) d ht,
      ecomp_eq_compY c.1 d ht y z,
      ecomp_eq_compY a (Sum.inl ⟨b, Ne.symm c.2⟩ : Without Y c.1 ⊕ Without Z d)
        (s := Sum.inr ⟨t, ht⟩) Sum.inr_ne_inl x]
    simp only [compY, compX_apply]
    rw [map_map (e := rootedGlueEquiv b a c.1 c.2) (f := Equiv.sumComm _ _),
      reroot_map (p := Sum.inr c) ((rootedGlueEquiv b a c.1 c.2).trans (Equiv.sumComm _ _)) rfl,
      map_map (e := rootedGlueEquiv d c.1 t ht) (f := Equiv.sumComm _ _),
      reroot_map (p := Sum.inr ⟨t, ht⟩)
        ((rootedGlueEquiv d c.1 t ht).trans (Equiv.sumComm _ _)) rfl,
      SymOperad.comp_map_right_of_eq (R := R) (P := Und C)
        (restrictRoot (p := Sum.inr c) ((rootedGlueEquiv b a c.1 c.2).trans (Equiv.sumComm _ _))
          rfl),
      ← SymOperad.comp_assoc_seq (R := R) (P := Und C) (⟨d, Ne.symm ht⟩ : Without Z t)
        (⟨b, Ne.symm c.2⟩ : Without Y c.1),
      SymOperad.comp_map_left_of_eq (R := R) (P := Und C)
        (restrictRoot (p := Sum.inr ⟨t, ht⟩)
          ((rootedGlueEquiv d c.1 t ht).trans (Equiv.sumComm _ _)) rfl)
        (i := Sum.inr ⟨b, Ne.symm c.2⟩) (i' := ⟨Sum.inl ⟨b, Ne.symm c.2⟩, Sum.inl_ne_inr⟩) rfl]
    simp only [pmap_eq]
    merge_maps
    refine map_congr (Equiv.ext fun t => ?_) _
    rcases t with _ | (⟨(⟨⟨z', h₁⟩, h₂⟩ | ⟨y', h₂⟩), h₃⟩ | ⟨x', h₁⟩)
    · rfl
    · rfl
    · rfl
    · rfl
  · -- no entries are left
    haveI := hC (Without X a ⊕ Without (Without Y c.1 ⊕ Without Z d) (Sum.inl ⟨b, Ne.symm c.2⟩))
      ⟨by
        rintro (⟨x', hx'⟩ | ⟨(⟨y', hy'⟩ | ⟨z', hz'⟩), h⟩)
        · exact hA ⟨x', hx'⟩
        · exact hB ⟨y', fun e => h (congrArg Sum.inl (Subtype.ext e)), hy'⟩
        · exact hD ⟨z', hz'⟩⟩
    exact Subsingleton.elim _ _

variable (R C) in
/-- **The cyclic operad of an operad with a compatible extended action**, on a species vanishing
on empty sets of entries. -/
@[reducible] noncomputable def ofExt
    (hC : ∀ (X : Type) [Fintype X] [DecidableEq X], IsEmpty X → Subsingleton (C X)) :
    CycOperad R C where
  one := SymOperad.one (P := Und C) R
  comp a b := ecomp R a b
  map_comp σ τ a b x y := ecomp_map hC σ τ a b x y
  comp_comm a b x y := ecomp_comm hC a b x y
  comp_one a x := ecomp_one a x
  comp_assoc a b c d x y z := ecomp_assoc hC a b c d x y z

end Ext

/-! ## The equivalence -/

section RoundTrip

variable {R : Type u} [CommRing R] {C : (X : Type) → [Fintype X] → [DecidableEq X] → Type v}
  [∀ (X : Type) [Fintype X] [DecidableEq X], AddCommGroup (C X)]
  [∀ (X : Type) [Fintype X] [DecidableEq X], Module R (C X)] [SymSpecies R C]
  {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

omit [Fintype X] [Fintype Y] in
lemma rootedGlueEquiv_symm_inl_self (a : X) (b : Y) (r : X) (hr : r ≠ a) :
    (rootedGlueEquiv a b r hr).symm (Sum.inl ⟨r, hr⟩) = none := by
  simp [rootedGlueEquiv]

omit [Fintype X] [Fintype Y] in
lemma rootedGlueEquiv_symm_inl_of_ne (a : X) (b : Y) {r x : X} (hr : r ≠ a) (hx : x ≠ a)
    (h : x ≠ r) :
    (rootedGlueEquiv a b r hr).symm (Sum.inl ⟨x, hx⟩)
      = some (Sum.inl ⟨⟨x, h⟩, fun e => hx (congrArg Subtype.val e)⟩) := by
  simp [rootedGlueEquiv, h]

/-- **Gluing in the underlying operad of a cyclic operad is its gluing.** -/
theorem compX_eq_comp [CycOperad R C] (a : X) (b : Y) (r : X) (hr : r ≠ a) (x : C X) (y : C Y) :
    compX R a b r hr x y = comp (R := R) a b x y := by
  rw [compX_apply, und_comp, comp_map_map (R := R) (rootEquiv r).symm (rootEquiv b).symm
    (a := a) (b := b) (a' := some ⟨a, Ne.symm hr⟩) (b' := none)
    (rootEquiv_symm_of_ne (Ne.symm hr)) (rootEquiv_symm_self b)]
  merge_maps
  conv_rhs => rw [← SymSpecies.map_refl (R := R) (comp (R := R) a b x y)]
  refine map_congr (Equiv.symm_bijective.injective (Equiv.ext fun t => ?_)) _
  rcases t with ⟨x', hx⟩ | ⟨y', hy⟩
  · by_cases h : x' = r
    · subst h
      simp only [Equiv.symm_trans_apply, rootedGlueEquiv_symm_inl_self]
      rfl
    · simp only [Equiv.symm_trans_apply, rootedGlueEquiv_symm_inl_of_ne a b hr hx h]
      rfl
  · rfl

/-- **The cyclic composition recovered from the underlying operad is the original one**, on a
species vanishing on empty sets of entries. -/
theorem ecomp_eq_comp [CycOperad R C]
    (hC : ∀ (X : Type) [Fintype X] [DecidableEq X], IsEmpty X → Subsingleton (C X))
    (a : X) (b : Y) (x : C X) (y : C Y) : ecomp R a b x y = comp (R := R) a b x y := by
  by_cases ha : ∃ r, r ≠ a
  · obtain ⟨r, hr⟩ := ha
    rw [ecomp_eq_compX a b hr, compX_eq_comp]
  by_cases hb : ∃ s, s ≠ b
  · obtain ⟨s, hs⟩ := hb
    rw [ecomp_eq_compY a b hs, compY, compX_eq_comp, comp_comm]
  · haveI := hC (Without X a ⊕ Without Y b) ⟨by
      rintro (⟨x', hx'⟩ | ⟨y', hy'⟩)
      · exact ha ⟨x', hx'⟩
      · exact hb ⟨y', hy'⟩⟩
    exact Subsingleton.elim _ _

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- Two cyclic operad structures with the same unit and compositions are equal. -/
theorem ext_of {inst₁ inst₂ : CycOperad R C}
    (hone : one (self := inst₁) R = one (self := inst₂) R)
    (hcomp : ∀ {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (a : X)
      (b : Y) (x : C X) (y : C Y),
      comp (R := R) (self := inst₁) a b x y = comp (R := R) (self := inst₂) a b x y) :
    inst₁ = inst₂ := by
  obtain ⟨one₁, comp₁, _, _, _, _⟩ := inst₁
  obtain ⟨one₂, comp₂, _, _, _, _⟩ := inst₂
  obtain rfl : one₁ = one₂ := hone
  obtain rfl : @comp₁ = @comp₂ := by
    funext X Y _ _ _ _ a b
    exact LinearMap.ext fun x => LinearMap.ext fun y => hcomp a b x y
  rfl

omit [SymSpecies R C] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- Two operad structures with the same relabellings, unit and compositions are equal. -/
theorem _root_.Operad.SymOperad.ext_of {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] {op₁ op₂ : SymOperad R P}
    (hmap : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (x : P A), SymOperad.map (self := op₁) e x = SymOperad.map (self := op₂) e x)
    (hone : SymOperad.one (self := op₁) R = SymOperad.one (self := op₂) R)
    (hcomp : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (x : P A) (y : P B),
      SymOperad.comp (self := op₁) i x y = SymOperad.comp (self := op₂) i x y) :
    op₁ = op₂ := by
  obtain ⟨map₁, _, _, one₁, comp₁, _, _, _, _, _⟩ := op₁
  obtain ⟨map₂, _, _, one₂, comp₂, _, _, _, _, _⟩ := op₂
  obtain rfl : @map₁ = @map₂ := by
    funext A B _ _ _ _ e
    exact LinearMap.ext fun x => hmap e x
  obtain rfl : one₁ = one₂ := hone
  obtain rfl : @comp₁ = @comp₂ := by
    funext A B _ _ _ _ i
    exact LinearMap.ext fun x => LinearMap.ext fun y => hcomp i x y
  rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- **The underlying operad of the cyclic operad of an operad with a compatible extended action
is that operad.** -/
theorem toSymOperad_ofExt [op : SymOperad R (Und C)] [ExtCompat R C]
    (hC : ∀ (X : Type) [Fintype X] [DecidableEq X], IsEmpty X → Subsingleton (C X)) :
    @toSymOperad R _ C _ _ _ (ofExt R C hC) = op := by
  refine SymOperad.ext_of (fun e x => (ExtCompat.map_eq (R := R) (C := C) e x).symm) rfl ?_
  intro A B _ _ _ _ i x y
  show SymSpecies.map (R := R) (V := C) (opGlueEquiv i) (ecomp R (some i) none x y) = _
  rw [ecomp_eq_compX (some i) none (r := none) (Option.some_ne_none i).symm, compX_apply,
    ← SymSpecies.map_refl (R := R) (V := C) x, ← SymSpecies.map_refl (R := R) (V := C) y,
    reroot_map (p := none) (Equiv.refl _) rfl, reroot_map (p := none) (Equiv.refl _) rfl,
    SymOperad.comp_map_map_of_eq (R := R) (P := Und C)
      (restrictRoot (p := none) (Equiv.refl (Option A)) rfl)
      (restrictRoot (p := none) (Equiv.refl (Option B)) rfl)
      (i := i) (i' := ⟨some i, (Option.some_ne_none i).symm.symm⟩) rfl]
  simp only [pmap_eq, SymSpecies.map_refl]
  merge_maps
  conv_rhs => rw [← SymSpecies.map_refl (R := R) (V := C)
    (SymOperad.comp (R := R) (P := Und C) i x y)]
  refine map_congr (Equiv.ext fun t => ?_) _
  rcases t with _ | (⟨a', h⟩ | b')
  · rfl
  · rfl
  · rfl

variable (R C) in
/-- **Cyclic operads are operads with a compatible extended action**: on a species vanishing on
empty sets of entries, cyclic operad structures correspond to the operad structures on
`A ↦ C (Option A)` for which the relabellings of `C` form a compatible extended action. -/
noncomputable def extEquiv
    (hC : ∀ (X : Type) [Fintype X] [DecidableEq X], IsEmpty X → Subsingleton (C X)) :
    CycOperad R C ≃ {op : SymOperad R (Und C) // @ExtCompat R _ C _ _ _ op} where
  toFun inst := ⟨@toSymOperad R _ C _ _ _ inst, @extCompat R _ C _ _ _ inst⟩
  invFun op :=
    letI := op.1
    haveI := op.2
    ofExt R C hC
  left_inv inst := by
    refine ext_of rfl ?_
    intro X Y _ _ _ _ a b x y
    exact ecomp_eq_comp hC a b x y
  right_inv op := by
    obtain ⟨op, h⟩ := op
    exact Subtype.ext (toSymOperad_ofExt (op := op) hC)

end RoundTrip

end CycOperad

end Operad
