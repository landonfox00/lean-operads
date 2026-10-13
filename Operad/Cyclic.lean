/-
# Cyclic operads

A **cyclic operad** is a species of operations whose entries all play the same role: there is no
distinguished output, and two operations compose by gluing an entry of one to an entry of the
other. In the species convention of `Operad.SymOperad`:

* `CycOperad`: a linear species `C` (`SymSpecies`) with compositions
  `comp a b : C X → C Y → C ((X ∖ a) ⊔ (Y ∖ b))`, equivariant, commutative and associative, with
  a two-entry unit (the "entries-only" definition).
* `CycOperad.toSymOperad`: **the underlying operad** `A ↦ C (Option A)`, the entry `none` being
  the output. The relabellings of `Option A` give it an **extended symmetric action**, which fixes
  the unit (`CycOperad.map_swap_one`) and is compatible with composition in the sense of
  Getzler–Kapranov: rerooting a composite at an input of the outer operation
  (`CycOperad.reroot_comp_inl`) or of the inner one (`CycOperad.reroot_comp_inr`) is the
  composite of the rerooted operations.
* `CycOperad.instCom`: the commutative cyclic operad, whose underlying operad is `Com`.
-/
import Operad.SpeciesOp

universe u v

-- The nested input sets `Without (Without X a ⊕ Without Y b) c ⊕ …` carry large instances.
set_option synthInstance.maxSize 1024

/- Deciding `o = none` through the decidable equality of `Option` keeps a single instance on the
input sets `Without (Option A) none`, as in the statements of the operad axioms. -/
attribute [-instance] Option.decidableEqNone Option.decidableNoneEq

namespace Operad

open Sym

/-! ## Gluing bijections -/

section Equivs

variable {X X' Y Y' Z : Type} [DecidableEq X] [DecidableEq X'] [DecidableEq Y]
  [DecidableEq Y'] [DecidableEq Z]

/-- **Equivariance of gluing**: `(X ∖ a) ⊔ (Y ∖ b) ≅ (X' ∖ a') ⊔ (Y' ∖ b')` for bijections
`σ : X ≃ X'`, `τ : Y ≃ Y'` with `σ a = a'` and `τ b = b'`. -/
def glueEquiv' (σ : X ≃ X') (τ : Y ≃ Y') {a : X} {b : Y} {a' : X'} {b' : Y'} (ha : σ a = a')
    (hb : τ b = b') : Without X a ⊕ Without Y b ≃ Without X' a' ⊕ Without Y' b' :=
  Equiv.sumCongr (σ.subtypeEquiv fun _ => by rw [← ha]; exact σ.injective.ne_iff.symm)
    (τ.subtypeEquiv fun _ => by rw [← hb]; exact τ.injective.ne_iff.symm)

/-- **Equivariance of gluing**: `(X ∖ a) ⊔ (Y ∖ b) ≅ (X' ∖ σ a) ⊔ (Y' ∖ τ b)`. -/
abbrev glueEquiv (σ : X ≃ X') (τ : Y ≃ Y') (a : X) (b : Y) :
    Without X a ⊕ Without Y b ≃ Without X' (σ a) ⊕ Without Y' (τ b) :=
  glueEquiv' σ τ rfl rfl

/-- **The unit**: gluing the entry `a` to the entry `none` of the two-entry unit,
`(X ∖ a) ⊔ {some ()} ≅ X`. -/
def glueUnitEquiv (a : X) : Without X a ⊕ Without (Option Unit) none ≃ X where
  toFun z :=
    match z with
    | Sum.inl x => x.1
    | Sum.inr _ => a
  invFun x := if h : x = a then Sum.inr ⟨some (), Option.some_ne_none ()⟩ else Sum.inl ⟨x, h⟩
  left_inv := by
    rintro (⟨x, hx⟩ | ⟨(_ | ⟨⟩), h⟩)
    · simp [hx]
    · exact absurd rfl h
    · simp
  right_inv x := by
    by_cases h : x = a
    · simp [h]
    · simp [h]

/-- **Associativity of gluing**: for `c ≠ b` in `Y`,
`((X ∖ a) ⊔ (Y ∖ b)) ∖ c ⊔ (Z ∖ d) ≅ (X ∖ a) ⊔ ((Y ∖ c) ⊔ (Z ∖ d)) ∖ b`. -/
def glueAssocEquiv (a : X) (b : Y) (c : Without Y b) (d : Z) :
    Without (Without X a ⊕ Without Y b) (Sum.inr c) ⊕ Without Z d
      ≃ Without X a ⊕ Without (Without Y c.1 ⊕ Without Z d) (Sum.inl ⟨b, Ne.symm c.2⟩) where
  toFun w :=
    match w with
    | Sum.inl ⟨Sum.inl x, _⟩ => Sum.inl x
    | Sum.inl ⟨Sum.inr y, hy⟩ =>
        Sum.inr ⟨Sum.inl ⟨y.1, fun h => hy (congrArg Sum.inr (Subtype.ext h))⟩,
          fun h => y.2 (congrArg Subtype.val (Sum.inl_injective h))⟩
    | Sum.inr z => Sum.inr ⟨Sum.inr z, Sum.inr_ne_inl⟩
  invFun w :=
    match w with
    | Sum.inl x => Sum.inl ⟨Sum.inl x, Sum.inl_ne_inr⟩
    | Sum.inr ⟨Sum.inl y, hy⟩ =>
        Sum.inl ⟨Sum.inr ⟨y.1, fun h => hy (congrArg Sum.inl (Subtype.ext h))⟩,
          fun h => y.2 (congrArg Subtype.val (Sum.inr_injective h))⟩
    | Sum.inr ⟨Sum.inr z, _⟩ => Sum.inr z
  left_inv := by rintro (⟨(x | y), h⟩ | z) <;> rfl
  right_inv := by rintro (x | ⟨(y | z), h⟩) <;> rfl

/-- **Rooting at an entry**: `Option (X ∖ r) ≅ X`, the new output `none` going to `r`. -/
def rootEquiv (r : X) : Option (Without X r) ≃ X where
  toFun w :=
    match w with
    | none => r
    | some x => x.1
  invFun x := if h : x = r then none else some ⟨x, h⟩
  left_inv := by
    rintro (_ | ⟨x, hx⟩)
    · simp
    · simp [hx]
  right_inv x := by
    by_cases h : x = r
    · simp [h]
    · simp [h]

@[simp] lemma rootEquiv_none (r : X) : rootEquiv r none = r := rfl

@[simp] lemma rootEquiv_some (r : X) (x : Without X r) : rootEquiv r (some x) = x.1 := rfl

lemma rootEquiv_symm_self (r : X) : (rootEquiv r).symm r = none := by
  simp [rootEquiv]

lemma rootEquiv_symm_of_ne {r x : X} (h : x ≠ r) : (rootEquiv r).symm x = some ⟨x, h⟩ := by
  simp [rootEquiv, h]

/-- The two entries of the unit exchanged. -/
def unitSwap : Option Unit ≃ Option Unit where
  toFun w :=
    match w with
    | none => some ()
    | some _ => none
  invFun w :=
    match w with
    | none => some ()
    | some _ => none
  left_inv := by rintro (_ | ⟨⟩) <;> rfl
  right_inv := by rintro (_ | ⟨⟩) <;> rfl

variable {A B : Type} [DecidableEq A] [DecidableEq B]

/-- **Composition in the underlying operad**: gluing the input `some i` of one operation to the
output `none` of another, `(Option A ∖ some i) ⊔ (Option B ∖ none) ≅ Option ((A ∖ i) ⊔ B)`. -/
def opGlueEquiv (i : A) :
    Without (Option A) (some i) ⊕ Without (Option B) none ≃ Option (Without A i ⊕ B) where
  toFun w :=
    match w with
    | Sum.inl ⟨none, _⟩ => none
    | Sum.inl ⟨some a, h⟩ => some (Sum.inl ⟨a, fun e => h (congrArg some e)⟩)
    | Sum.inr ⟨none, h⟩ => absurd rfl h
    | Sum.inr ⟨some b, _⟩ => some (Sum.inr b)
  invFun w :=
    match w with
    | none => Sum.inl ⟨none, (Option.some_ne_none i).symm⟩
    | some (Sum.inl a) => Sum.inl ⟨some a.1, fun e => a.2 (Option.some_injective _ e)⟩
    | some (Sum.inr b) => Sum.inr ⟨some b, Option.some_ne_none b⟩
  left_inv := by
    rintro (⟨(_ | a), h⟩ | ⟨(_ | b), h⟩)
    · rfl
    · rfl
    · exact absurd rfl h
    · rfl
  right_inv := by rintro (_ | (a | b)) <;> rfl

/-- **Rerooting a composite at an input `r` of the outer operation**: the inputs of the
composite of the rerooted outer operation with the inner one,
`((Option A ∖ r) ∖ i) ⊔ B ≅ Option ((A ∖ i) ⊔ B) ∖ r`. -/
def rerootInlEquiv (i : A) (r : Without A i) :
    Without (Without (Option A) (some r.1)) ⟨some i, fun h => r.2 (Option.some_injective _ h).symm⟩
        ⊕ B ≃ Without (Option (Without A i ⊕ B)) (some (Sum.inl r)) where
  toFun w :=
    match w with
    | Sum.inl ⟨⟨none, _⟩, _⟩ => ⟨none, (Option.some_ne_none _).symm⟩
    | Sum.inl ⟨⟨some a, h₁⟩, h₂⟩ =>
        ⟨some (Sum.inl ⟨a, fun e => h₂ (Subtype.ext (congrArg some e))⟩), fun e =>
          h₁ (congrArg some (congrArg Subtype.val (Sum.inl_injective (Option.some_injective _ e))))⟩
    | Sum.inr b => ⟨some (Sum.inr b), fun e => Sum.inr_ne_inl (Option.some_injective _ e)⟩
  invFun w :=
    match w with
    | ⟨none, _⟩ => Sum.inl ⟨⟨none, (Option.some_ne_none _).symm⟩, fun e =>
        (Option.some_ne_none i).symm (congrArg Subtype.val e)⟩
    | ⟨some (Sum.inl a), h⟩ => Sum.inl ⟨⟨some a.1, fun e =>
          h (congrArg (fun t => some (Sum.inl t)) (Subtype.ext (Option.some_injective _ e)))⟩,
        fun e => a.2 (Option.some_injective _ (congrArg Subtype.val e))⟩
    | ⟨some (Sum.inr b), _⟩ => Sum.inr b
  left_inv := by rintro (⟨⟨(_ | a), h₁⟩, h₂⟩ | b) <;> rfl
  right_inv := by rintro ⟨(_ | (a | b)), h⟩ <;> rfl

/-- **Rerooting a composite at an input `b` of the inner operation**: the inputs of the composite
of the rerooted inner operation with the rerooted outer one,
`((Option B ∖ b) ∖ none) ⊔ (Option A ∖ i) ≅ Option ((A ∖ i) ⊔ B) ∖ b`. -/
def rerootInrEquiv (i : A) (b : B) :
    Without (Without (Option B) (some b)) ⟨none, (Option.some_ne_none b).symm⟩
        ⊕ Without (Option A) (some i) ≃ Without (Option (Without A i ⊕ B)) (some (Sum.inr b)) where
  toFun w :=
    match w with
    | Sum.inl ⟨⟨none, _⟩, h⟩ => absurd rfl h
    | Sum.inl ⟨⟨some b', h₁⟩, _⟩ => ⟨some (Sum.inr b'), fun e =>
        h₁ (congrArg some (Sum.inr_injective (Option.some_injective _ e)))⟩
    | Sum.inr ⟨none, _⟩ => ⟨none, (Option.some_ne_none _).symm⟩
    | Sum.inr ⟨some a, h⟩ => ⟨some (Sum.inl ⟨a, fun e => h (congrArg some e)⟩), fun e =>
        Sum.inl_ne_inr (Option.some_injective _ e)⟩
  invFun w :=
    match w with
    | ⟨none, _⟩ => Sum.inr ⟨none, (Option.some_ne_none i).symm⟩
    | ⟨some (Sum.inl a), _⟩ => Sum.inr ⟨some a.1, fun e => a.2 (Option.some_injective _ e)⟩
    | ⟨some (Sum.inr b'), h⟩ => Sum.inl ⟨⟨some b', fun e =>
          h (congrArg (fun t => some (Sum.inr t)) (Option.some_injective _ e))⟩,
        fun e => Option.some_ne_none b' (congrArg Subtype.val e)⟩
  left_inv := by
    rintro (⟨⟨(_ | b'), h₁⟩, h₂⟩ | ⟨(_ | a), h⟩)
    · exact absurd rfl h₂
    · rfl
    · rfl
    · rfl
  right_inv := by rintro ⟨(_ | (a | b')), h⟩ <;> rfl

end Equivs

/-! ## The class -/

/-- **A cyclic operad in `R`-modules**, on a linear species `C` of operations with entries `X`:
compositions gluing an entry of one operation to an entry of another, equivariant, commutative
and associative, with a two-entry unit. -/
class CycOperad (R : Type u) [CommRing R]
    (C : (X : Type) → [Fintype X] → [DecidableEq X] → Type v)
    [∀ (X : Type) [Fintype X] [DecidableEq X], AddCommGroup (C X)]
    [∀ (X : Type) [Fintype X] [DecidableEq X], Module R (C X)] [SymSpecies R C] where
  /-- The unit, with two entries. -/
  one : C (Option Unit)
  /-- Glue the entry `a` of an operation with entries `X` to the entry `b` of one with entries
  `Y`. -/
  comp {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (a : X) (b : Y) :
    C X →ₗ[R] C Y →ₗ[R] C (Without X a ⊕ Without Y b)
  /-- **Equivariance**: gluing is natural in bijections of both entry sets. -/
  map_comp {X X' Y Y' : Type} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']
    [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (σ : X ≃ X') (τ : Y ≃ Y') (a : X)
    (b : Y) (x : C X) (y : C Y) :
    SymSpecies.map (R := R) (glueEquiv σ τ a b) (comp a b x y)
      = comp (σ a) (τ b) (SymSpecies.map (R := R) σ x) (SymSpecies.map (R := R) τ y)
  /-- **Commutativity**: gluing is symmetric. -/
  comp_comm {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (a : X) (b : Y)
    (x : C X) (y : C Y) :
    SymSpecies.map (R := R) (Equiv.sumComm _ _) (comp a b x y) = comp b a y x
  /-- **The unit**: gluing the unit by its entry `none` changes nothing. -/
  comp_one {X : Type} [Fintype X] [DecidableEq X] (a : X) (x : C X) :
    SymSpecies.map (R := R) (glueUnitEquiv a) (comp a none x one) = x
  /-- **Associativity**: gluing a third operation to an entry coming from the second. -/
  comp_assoc {X Y Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Z]
    [DecidableEq Z] (a : X) (b : Y) (c : Without Y b) (d : Z) (x : C X) (y : C Y) (z : C Z) :
    SymSpecies.map (R := R) (glueAssocEquiv a b c d) (comp (Sum.inr c) d (comp a b x y) z)
      = comp a (Sum.inl ⟨b, Ne.symm c.2⟩) x (comp c.1 d y z)

namespace CycOperad

section Basic

variable {R : Type u} [CommRing R] {C : (X : Type) → [Fintype X] → [DecidableEq X] → Type v}
  [∀ (X : Type) [Fintype X] [DecidableEq X], AddCommGroup (C X)]
  [∀ (X : Type) [Fintype X] [DecidableEq X], Module R (C X)] [SymSpecies R C]
  {X X' Y Y' Z : Type} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X'] [Fintype Y]
  [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] in
lemma map_map (e : X ≃ Y) (f : Y ≃ Z) (x : C X) :
    SymSpecies.map (R := R) f (SymSpecies.map (R := R) e x)
      = SymSpecies.map (R := R) (e.trans f) x :=
  (SymSpecies.map_trans (R := R) e f x).symm

/-- Merge nested relabellings `map f (map e x)` into `map (e.trans f) x`, also when the
instances on the middle set of entries agree only up to unfolding. -/
syntax (name := mergeMaps) "merge_maps" : tactic

macro_rules
  | `(tactic| merge_maps) =>
    `(tactic| ((try simp only [Operad.CycOperad.map_map]); repeat erw [Operad.CycOperad.map_map]))

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
lemma map_congr {e f : X ≃ Y} (h : e = f) (x : C X) :
    SymSpecies.map (R := R) e x = SymSpecies.map (R := R) f x := by
  rw [h]

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
lemma eq_map_symm {e : X ≃ Y} {x : C X} {y : C Y} (h : SymSpecies.map (R := R) e x = y) :
    x = SymSpecies.map (R := R) e.symm y := by
  rw [← h, map_map, Equiv.self_trans_symm, SymSpecies.map_refl]

variable [CycOperad R C]

omit [Fintype Z] [DecidableEq Z] in
/-- Gluing relabelled operations, at entries given up to equality. -/
lemma comp_map_map (σ : X ≃ X') (τ : Y ≃ Y') {a : X} {b : Y} {a' : X'} {b' : Y'}
    (ha : σ a = a') (hb : τ b = b') (x : C X) (y : C Y) :
    comp (R := R) a' b' (SymSpecies.map (R := R) σ x) (SymSpecies.map (R := R) τ y)
      = SymSpecies.map (R := R) (glueEquiv' σ τ ha hb) (comp (R := R) a b x y) := by
  subst ha hb
  exact (map_comp σ τ a b x y).symm

omit [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
lemma comp_map_left (σ : X ≃ X') {a : X} {a' : X'} (ha : σ a = a') (b : Y) (x : C X) (y : C Y) :
    comp (R := R) a' b (SymSpecies.map (R := R) σ x) y
      = SymSpecies.map (R := R) (glueEquiv' σ (Equiv.refl Y) ha rfl) (comp (R := R) a b x y) := by
  have := comp_map_map (R := R) σ (Equiv.refl Y) ha (rfl : (Equiv.refl Y) b = b) x y
  rwa [SymSpecies.map_refl] at this

omit [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] in
lemma comp_map_right (τ : Y ≃ Y') (a : X) {b : Y} {b' : Y'} (hb : τ b = b') (x : C X) (y : C Y) :
    comp (R := R) a b' x (SymSpecies.map (R := R) τ y)
      = SymSpecies.map (R := R) (glueEquiv' (Equiv.refl X) τ rfl hb) (comp (R := R) a b x y) := by
  have := comp_map_map (R := R) (Equiv.refl X) τ (rfl : (Equiv.refl X) a = a) hb x y
  rwa [SymSpecies.map_refl] at this

omit [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] in
/-- Commutativity, solved for the composite. -/
lemma comp_eq_comm (a : X) (b : Y) (x : C X) (y : C Y) :
    comp (R := R) a b x y = SymSpecies.map (R := R) (Equiv.sumComm _ _) (comp (R := R) b a y x) :=
  (comp_comm (R := R) b a y x).symm

/-- **The unit is symmetric**: exchanging its two entries fixes it. -/
lemma map_swap_one : SymSpecies.map (R := R) unitSwap (one R : C (Option Unit)) = one R := by
  have hc := comp_comm (R := R) (C := C) none none (one R) (one R)
  have hu := comp_one (R := R) (C := C) (none : Option Unit) (one R)
  conv_lhs => rw [← hu, map_map]
  conv_rhs => rw [← hu, ← hc, map_map]
  refine map_congr (Equiv.ext fun w => ?_) _
  rcases w with ⟨(_ | ⟨⟩), h⟩ | ⟨(_ | ⟨⟩), h⟩
  · exact absurd rfl h
  · rfl
  · exact absurd rfl h
  · rfl

end Basic

/-! ## The underlying operad -/

/-- **The underlying species of a cyclic operad**: the operations with inputs `A` are those with
entries `Option A`, the entry `none` being the output. -/
@[nolint unusedArguments]
def Und (C : (X : Type) → [Fintype X] → [DecidableEq X] → Type v) :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type v :=
  fun A _ _ => C (Option A)

section Und

variable {R : Type u} [CommRing R] {C : (X : Type) → [Fintype X] → [DecidableEq X] → Type v}
  [∀ (X : Type) [Fintype X] [DecidableEq X], AddCommGroup (C X)]
  [∀ (X : Type) [Fintype X] [DecidableEq X], Module R (C X)]

instance Und.instAddCommGroup (A : Type) [Fintype A] [DecidableEq A] :
    AddCommGroup (Und C A) :=
  inferInstanceAs (AddCommGroup (C (Option A)))

instance Und.instModule (A : Type) [Fintype A] [DecidableEq A] : Module R (Und C A) :=
  inferInstanceAs (Module R (C (Option A)))

variable [SymSpecies R C] [CycOperad R C]

/-- **The underlying operad of a cyclic operad**: relabelling the inputs fixes the output, and
the input `i` of `x` is filled with `y` by gluing the entry `some i` of `x` to the output entry
`none` of `y`. -/
noncomputable instance toSymOperad : SymOperad R (Und C) where
  map e := SymSpecies.map (R := R) (V := C) e.optionCongr
  map_refl x := by
    show SymSpecies.map (R := R) (V := C) (Equiv.refl _).optionCongr x = x
    rw [Equiv.optionCongr_refl]
    exact SymSpecies.map_refl (R := R) (V := C) x
  map_trans e f x := by
    show SymSpecies.map (R := R) (V := C) (e.trans f).optionCongr x
      = SymSpecies.map (R := R) f.optionCongr (SymSpecies.map (R := R) (V := C) e.optionCongr x)
    rw [Equiv.optionCongr_trans]
    exact SymSpecies.map_trans (R := R) (V := C) _ _ x
  one := one R
  comp i := (comp (R := R) (C := C) (some i) none).compr₂
    (SymSpecies.map (R := R) (opGlueEquiv i))
  map_comp := by
    intro A A' B B' _ _ _ _ _ _ _ _ σ τ i x y
    show SymSpecies.map (R := R) (compEquiv σ τ i).optionCongr
        (SymSpecies.map (R := R) (opGlueEquiv i) (comp (R := R) (some i) none x y))
      = SymSpecies.map (R := R) (opGlueEquiv (σ i)) (comp (R := R) (some (σ i)) none
          (SymSpecies.map (R := R) σ.optionCongr x) (SymSpecies.map (R := R) τ.optionCongr y))
    rw [comp_map_map (R := R) (a := some i) (b := none) (a' := some (σ i)) (b' := none)
      σ.optionCongr τ.optionCongr rfl rfl]
    merge_maps
    refine map_congr (Equiv.ext fun w => ?_) _
    rcases w with ⟨(_ | a), h⟩ | ⟨(_ | b), h⟩
    · rfl
    · rfl
    · exact absurd rfl h
    · rfl
  comp_one := by
    intro A _ _ i x
    show SymSpecies.map (R := R) (rightUnitEquiv i).optionCongr
        (SymSpecies.map (R := R) (opGlueEquiv i) (comp (R := R) (some i) none x (one R))) = x
    merge_maps
    refine Eq.trans ?_ (comp_one (R := R) (some i) x)
    refine map_congr (Equiv.ext fun w => ?_) _
    rcases w with ⟨(_ | a), h⟩ | ⟨(_ | ⟨⟩), h⟩
    · rfl
    · rfl
    · exact absurd rfl h
    · rfl
  one_comp := by
    intro B _ _ y
    show SymSpecies.map (R := R) (leftUnitEquiv B).optionCongr
        (SymSpecies.map (R := R) (opGlueEquiv ()) (comp (R := R) (some ()) none (one R) y)) = y
    rw [comp_eq_comm (R := R) (some () : Option Unit) (none : Option B) (one R) y,
      ← map_swap_one (R := R) (C := C),
      comp_map_right (R := R) unitSwap (none : Option B) (b := none) (b' := some ()) rfl]
    merge_maps
    refine Eq.trans ?_ (comp_one (R := R) (none : Option B) y)
    refine map_congr (Equiv.ext fun w => ?_) _
    rcases w with ⟨(_ | b), h⟩ | ⟨(_ | ⟨⟩), h⟩
    · exact absurd rfl h
    · rfl
    · exact absurd rfl h
    · rfl
  comp_assoc_seq := by
    intro A B D _ _ _ _ _ _ i j x y z
    show SymSpecies.map (R := R) (seqEquiv i j D).optionCongr
        (SymSpecies.map (R := R) (opGlueEquiv (Sum.inr j)) (comp (R := R) (some (Sum.inr j)) none
          (SymSpecies.map (R := R) (opGlueEquiv i) (comp (R := R) (some i) none x y)) z))
      = SymSpecies.map (R := R) (opGlueEquiv i) (comp (R := R) (some i) none x
          (SymSpecies.map (R := R) (opGlueEquiv j) (comp (R := R) (some j) none y z)))
    rw [comp_map_left (R := R) (opGlueEquiv i)
        (a := Sum.inr ⟨some j, Option.some_ne_none j⟩) (a' := some (Sum.inr j)) rfl,
      eq_map_symm (comp_assoc (R := R) (some i) none ⟨some j, Option.some_ne_none j⟩ none x y z),
      comp_map_right (R := R) (opGlueEquiv j) (some i)
        (b := Sum.inl ⟨none, (Option.some_ne_none j).symm⟩) (b' := none) rfl]
    merge_maps
    refine map_congr (Equiv.ext fun w => ?_) _
    rcases w with ⟨(_ | a), h⟩ | ⟨⟨(_ | b), h₁⟩ | ⟨(_ | d), h₁⟩, h⟩
    · rfl
    · rfl
    · exact absurd rfl h
    · rfl
    · exact absurd rfl h₁
    · rfl
  comp_assoc_par := by
    intro A B D _ _ _ _ _ _ i k hik x y z
    show SymSpecies.map (R := R) (parEquiv hik B D).optionCongr
        (SymSpecies.map (R := R) (opGlueEquiv (A := Without A i ⊕ B) (B := D)
          (Sum.inl ⟨k, Ne.symm hik⟩))
          (comp (R := R) (some (Sum.inl ⟨k, Ne.symm hik⟩)) none
            (SymSpecies.map (R := R) (opGlueEquiv i) (comp (R := R) (some i) none x y)) z))
      = SymSpecies.map (R := R) (opGlueEquiv (A := Without A k ⊕ D) (B := B) (Sum.inl ⟨i, hik⟩))
          (comp (R := R) (some (Sum.inl ⟨i, hik⟩)) none
            (SymSpecies.map (R := R) (opGlueEquiv k) (comp (R := R) (some k) none x z)) y)
    have hk : some k ≠ some i := fun e => hik (Option.some_injective _ e).symm
    have hi : some i ≠ some k := fun e => hik (Option.some_injective _ e)
    rw [comp_map_left (R := R) (opGlueEquiv i) (a := Sum.inl ⟨some k, hk⟩)
        (a' := some (Sum.inl ⟨k, Ne.symm hik⟩)) rfl,
      comp_eq_comm (R := R) (some i) none x y,
      comp_map_left (R := R)
        (Equiv.sumComm (Without (Option B) none) (Without (Option A) (some i)))
        (a := Sum.inr ⟨some k, hk⟩) (a' := Sum.inl ⟨some k, hk⟩) rfl,
      eq_map_symm (comp_assoc (R := R) none (some i) ⟨some k, hk⟩ none y x z),
      comp_eq_comm (R := R) (none : Option B)
        (Sum.inl ⟨some i, hi⟩ : Without (Option A) (some k) ⊕ Without (Option D) none),
      comp_map_left (R := R) (opGlueEquiv (B := D) k) (a := Sum.inl ⟨some i, hi⟩)
        (a' := some (Sum.inl ⟨i, hik⟩)) rfl]
    merge_maps
    refine map_congr (Equiv.ext fun w => ?_) _
    rcases w with ⟨⟨(_ | a), h₁⟩ | ⟨(_ | d), h₁⟩, h⟩ | ⟨(_ | b), h⟩
    · rfl
    · rfl
    · exact absurd rfl h₁
    · rfl
    · exact absurd rfl h
    · rfl

lemma und_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : Und C A) :
    SymOperad.map (R := R) (P := Und C) e x = SymSpecies.map (R := R) (V := C) e.optionCongr x :=
  rfl

lemma und_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : Und C A) (y : Und C B) :
    SymOperad.comp (R := R) (P := Und C) i x y
      = SymSpecies.map (R := R) (V := C) (opGlueEquiv i)
          (comp (R := R) (C := C) (some i) none x y) :=
  rfl

/-! ## The extended action

The relabellings of `C` along all bijections of `Option A`, not only those fixing the output,
act on the underlying operad. -/

/-- **Rerooting at an input of the outer operation** (Getzler–Kapranov). -/
theorem reroot_comp_inl {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) (r : Without A i) (x : Und C A) (y : Und C B) :
    SymSpecies.map (R := R) (V := C) (rootEquiv (some (Sum.inl r))).symm
        (SymOperad.comp (R := R) (P := Und C) i x y)
      = SymOperad.map (R := R) (P := Und C) (rerootInlEquiv i r)
          (SymOperad.comp (R := R) (P := Und C)
            ⟨some i, fun h => r.2 (Option.some_injective _ h).symm⟩
            (SymSpecies.map (R := R) (V := C) (rootEquiv (some r.1)).symm x) y) := by
  rw [und_comp (R := R) (C := C) i x y, und_comp (R := R) (C := C), und_map (R := R) (C := C),
    comp_map_left (R := R) (rootEquiv (some r.1)).symm
    (a := some i) (rootEquiv_symm_of_ne (X := Option A) (r := some r.1) (x := some i)
      fun h => r.2 (Option.some_injective _ h).symm)]
  merge_maps
  refine map_congr (Equiv.symm_bijective.injective (Equiv.ext fun w => ?_)) _
  rcases w with _ | ⟨(_ | (a | b)), h⟩
  · rfl
  · rfl
  · rfl
  · rfl

/-- **Rerooting at an input of the inner operation** (Getzler–Kapranov). -/
theorem reroot_comp_inr {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) (b : B) (x : Und C A) (y : Und C B) :
    SymSpecies.map (R := R) (V := C) (rootEquiv (some (Sum.inr b))).symm
        (SymOperad.comp (R := R) (P := Und C) i x y)
      = SymOperad.map (R := R) (P := Und C) (rerootInrEquiv i b)
          (SymOperad.comp (R := R) (P := Und C) ⟨none, (Option.some_ne_none b).symm⟩
            (SymSpecies.map (R := R) (V := C) (rootEquiv (some b)).symm y)
            (SymSpecies.map (R := R) (V := C) (rootEquiv (some i)).symm x)) := by
  rw [und_comp (R := R) (C := C) i x y, und_comp (R := R) (C := C), und_map (R := R) (C := C),
    comp_map_map (R := R) (rootEquiv (some b)).symm
    (rootEquiv (some i)).symm (a := none) (b := some i)
    (rootEquiv_symm_of_ne (Option.some_ne_none b).symm) (rootEquiv_symm_self _),
    comp_eq_comm (R := R) none (some i) y x]
  merge_maps
  refine map_congr (Equiv.symm_bijective.injective (Equiv.ext fun w => ?_)) _
  rcases w with _ | ⟨(_ | (a | b')), h⟩
  · rfl
  · rfl
  · rfl
  · rfl

/-- The unit of the underlying operad is fixed by the extended action. -/
theorem und_map_swap_one :
    SymSpecies.map (R := R) (V := C) unitSwap (SymOperad.one (P := Und C) R)
      = SymOperad.one (P := Und C) R :=
  map_swap_one (R := R) (C := C)

end Und

/-! ## The commutative cyclic operad -/

/-- **The commutative cyclic operad**: one operation with any set of entries, gluing being the
product. -/
instance instCom (R : Type u) [CommRing R] : CycOperad R (Com R) where
  one := (1 : R)
  comp _ _ := LinearMap.mul R R
  map_comp _ _ _ _ _ _ := rfl
  comp_comm _ _ x y := mul_comm x y
  comp_one _ x := mul_one x
  comp_assoc _ _ _ _ x y z := mul_assoc x y z

/-- **The underlying operad of the commutative cyclic operad is `Com`**, by the identity maps. -/
def comUndHom (R : Type u) [CommRing R] : SymOperadHom R (Und (Com R)) (Com R) where
  app _ _ _ := LinearMap.id
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

/-- The inverse of `comUndHom`. -/
def comUndHomInv (R : Type u) [CommRing R] : SymOperadHom R (Com R) (Und (Com R)) where
  app _ _ _ := LinearMap.id
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

end CycOperad

end Operad
