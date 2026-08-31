/-
# Non-symmetric (planar) operads in `R`-modules

## Design note: the positional arity convention

The textbook partial composition is `∘ᵢ : P m ⊗ P n → P (m + n - 1)` with a slot index
`i : Fin m`.  Formalising that directly means truncated subtraction and a great deal of `Fin`
bookkeeping to track how slot indices shift after a composition; that is what makes operads
unpleasant to formalise.

Here the slot is recorded *positionally in the arity* instead.  An operation with a
distinguished input slot has type `P (a + 1 + b)`: `a` inputs before the slot, `b` after.
Composition then reads

  `comp a b : P (a + 1 + b) →ₗ[R] P n →ₗ[R] P (a + n + b)`

which has three advantages:

* no subtraction anywhere;
* the right unit law `α ∘ 1 = α` is *definitional* (take `n = 1`);
* every coherence condition becomes a pure `Nat` identity, discharged by `omega`.  There is no
  `Fin` index arithmetic at all, in particular none in parallel associativity.

`a` and `b` must be explicit arguments: from `α : P 3` alone Lean cannot tell whether the slot
is at position 0, 1 or 2, i.e. whether `3` is `0+1+2`, `1+1+1` or `2+1+0`.
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

universe u v

namespace Operad

section Reindex

variable (R : Type u) [CommRing R] (P : ℕ → Type v)
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]

/-- Transport an element of `P` along an equality of arities. All the coherence conditions of
an operad are stated up to this reindexing. -/
def reindex {m n : ℕ} (h : m = n) : P m ≃ₗ[R] P n := by
  subst h; exact LinearEquiv.refl R (P m)

variable {R P}

@[simp]
lemma reindex_rfl {n : ℕ} (x : P n) : reindex R P (rfl : n = n) x = x := rfl

/-- Reindexing along *any* proof of a reflexive equality is the identity. Stronger than
`reindex_rfl`, which only fires when the proof is syntactically `rfl`; in practice the proofs
are produced by `omega` and are never syntactically `rfl`. -/
@[simp]
lemma reindex_self {n : ℕ} (h : n = n) (x : P n) : reindex R P h x = x := by
  obtain rfl : h = rfl := Subsingleton.elim _ _
  rfl

@[simp]
lemma reindex_reindex {l m n : ℕ} (h₁ : l = m) (h₂ : m = n) (x : P l) :
    reindex R P h₂ (reindex R P h₁ x) = reindex R P (h₁.trans h₂) x := by
  subst h₁; subst h₂; rfl

@[simp]
lemma reindex_symm_apply {m n : ℕ} (h : m = n) (x : P n) :
    (reindex R P h).symm x = reindex R P h.symm x := by
  subst h; rfl

lemma reindex_injective {m n : ℕ} (h : m = n) : Function.Injective (reindex R P h) :=
  (reindex R P h).injective

/-- Two elements are equal iff their reindexings are. Useful for rewriting a goal into a
convenient arity before comparing. -/
lemma reindex_eq_iff {m n : ℕ} (h : m = n) (x y : P m) :
    reindex R P h x = reindex R P h y ↔ x = y :=
  (reindex R P h).injective.eq_iff

end Reindex

/-- A non-symmetric (planar) operad in `R`-modules, given by partial compositions in the
positional arity convention described at the top of this file. -/
class NSOperad (R : Type u) [CommRing R] (P : ℕ → Type v)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] where
  /-- The identity operation. -/
  one : P 1
  /-- Insert an arity-`n` operation into the distinguished slot of an operation with `a` inputs
  before and `b` inputs after that slot. -/
  comp (a b : ℕ) {n : ℕ} : P (a + 1 + b) →ₗ[R] P n →ₗ[R] P (a + n + b)
  /-- Right unit: plugging the identity into a slot changes nothing. Note this needs no
  reindexing: `a + 1 + b` is the arity on both sides. -/
  comp_one_right (a b : ℕ) (α : P (a + 1 + b)) : comp a b α one = α
  /-- Left unit: plugging an operation into the identity changes nothing. -/
  comp_one_left {n : ℕ} (α : P n) :
    reindex R P (by omega) (comp 0 0 one α) = α
  /-- Sequential (nested) associativity: composing into a slot that came from an earlier
  composition. -/
  comp_assoc_seq (a b c d : ℕ) {p : ℕ} (α : P (a + 1 + b)) (β : P (c + 1 + d)) (γ : P p) :
    reindex R P (by omega)
        (comp (a + c) (d + b) (reindex R P (by omega) (comp a b α β)) γ)
      = comp a b α (comp c d β γ)
  /-- Parallel (disjoint) associativity: composing into two distinct slots, in either order.
  Note `α`'s arity `a + 1 + b + 1 + c` is already definitionally `(a + 1 + b) + 1 + c`, so only
  the first (left-hand) use needs a reindexing to regroup it as `a + 1 + (b + 1 + c)`. -/
  comp_assoc_par (a b c : ℕ) {n p : ℕ} (α : P (a + 1 + b + 1 + c)) (β : P n) (γ : P p) :
    reindex R P (by omega)
        (comp (a + n + b) c
          (reindex R P (by omega) (comp a (b + 1 + c) (reindex R P (by omega) α) β)) γ)
      = comp a (b + p + c) (reindex R P (by omega) (comp (a + 1 + b) c α γ)) β

namespace NSOperad

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-- Composition is linear in the outer operation. -/
lemma comp_add_left (a b : ℕ) {n : ℕ} (α α' : P (a + 1 + b)) (β : P n) :
    comp (R := R) a b (α + α') β = comp (R := R) a b α β + comp (R := R) a b α' β := by
  rw [map_add]; rfl

/-- Composition is linear in the inserted operation. -/
lemma comp_add_right (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) (β β' : P n) :
    comp (R := R) a b α (β + β') = comp (R := R) a b α β + comp (R := R) a b α β' :=
  map_add _ _ _

@[simp]
lemma comp_zero_left (a b : ℕ) {n : ℕ} (β : P n) :
    comp (R := R) a b (0 : P (a + 1 + b)) β = 0 := by
  rw [map_zero]; rfl

@[simp]
lemma comp_zero_right (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) :
    comp (R := R) a b α (0 : P n) = 0 :=
  map_zero _

lemma comp_smul_left (a b : ℕ) {n : ℕ} (r : R) (α : P (a + 1 + b)) (β : P n) :
    comp (R := R) a b (r • α) β = r • comp (R := R) a b α β := by
  rw [map_smul]; rfl

lemma comp_smul_right (a b : ℕ) {n : ℕ} (r : R) (α : P (a + 1 + b)) (β : P n) :
    comp (R := R) a b α (r • β) = r • comp (R := R) a b α β :=
  map_smul _ _ _

end NSOperad

/-! ## The associative operad `Ass`

`Ass n = R` in every arity, with composition given by multiplication. This is the smallest
nontrivial check that the axioms above are mutually consistent and that the reindexings line
up as intended.

Note this is `Ass`, *not* `Com`. As a **non-symmetric** operad, one free generator in each arity
means exactly one planar way to combine `n` inputs in order, which is the operad governing
associative algebras. `Ass` and `Com` are only distinguished once symmetric group actions are
present (`Ass` carries the regular representation of `Σ n`, `Com` the trivial one), and this file
has no symmetric structure. -/

/-- `Ass R n = R` for every arity `n`. An `abbrev` so that all of `R`'s instances transfer. -/
abbrev Ass (R : Type u) [CommRing R] : ℕ → Type u := fun _ => R

section Ass

variable (R : Type u) [CommRing R]

/-- On a constant family, reindexing is the identity. This is what lets `ring` finish the
coherence obligations below. -/
@[simp]
lemma reindex_ass {m n : ℕ} (h : m = n) (x : Ass R m) :
    reindex R (Ass R) h x = x := by
  cases h; rfl

instance : NSOperad R (Ass R) where
  one := (1 : R)
  comp _ _ := LinearMap.mul R R
  comp_one_right _ _ α := mul_one α
  comp_one_left := by
    intros; simp only [reindex_ass, LinearMap.mul_apply']; ring
  comp_assoc_seq := by
    intros; simp only [reindex_ass, LinearMap.mul_apply']; ring
  comp_assoc_par := by
    intros; simp only [reindex_ass, LinearMap.mul_apply']; ring

end Ass

end Operad
