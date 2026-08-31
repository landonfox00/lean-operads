/-
# The total space as a pre-Lie ring

`Operad.PreLie` proves the pre-Lie identity in *graded* form: `⋆` takes `P (j+1)` and `P (k+1)`
to `P (j+k+1)`, and `star_assoc_symm` is an identity between elements of a fixed arity. To land
on mathlib's `RightPreLieRing` the grading has to be bundled into a single object.

That object is `⨁ k, Piece R P k`, graded by **arity minus one**. Mathlib's graded-ring machinery
does most of the work: `DirectSum.GNonUnitalNonAssocSemiring` asks for exactly a graded
multiplication together with `mul_zero`, `zero_mul`, `mul_add` and `add_mul`, which are the four
bilinearity lemmas for `⋆`, and it produces the `NonUnitalNonAssocRing` structure that
`RightPreLieRing` extends.

`Piece` is a type synonym for `P (k + 1)` carrying `R` as a phantom parameter. Without it the
graded instances below would have `R` appearing nowhere in their conclusions, and Lean rejects
them for having no synthesization order.
-/
import Operad.PreLie
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.NonAssoc.PreLie.Basic
import Mathlib.Algebra.Ring.Associator

universe u v

namespace Operad

open NSOperad DirectSum

/-- The degree-`k` piece of the total space: operations of arity `k + 1`. Arity `0` is excluded,
since it carries no degree and the deformation complex does not use it. -/
def Piece (R : Type u) [CommRing R] (P : ℕ → Type v) (k : ℕ) : Type v := P (k + 1)

section

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]

instance (k : ℕ) : AddCommGroup (Piece R P k) := inferInstanceAs (AddCommGroup (P (k + 1)))

instance (k : ℕ) : Module R (Piece R P k) := inferInstanceAs (Module R (P (k + 1)))

variable [NSOperad R P]

/-- The circle product as a graded multiplication: degrees add. -/
instance : GradedMonoid.GMul (Piece R P) where
  mul {_ _} a b := star (R := R) a b

/-- The four bilinearity lemmas for `⋆` are exactly what a graded non-unital non-associative
semiring structure asks for. -/
instance : DirectSum.GNonUnitalNonAssocSemiring (Piece R P) where
  mul_zero a := star_zero (R := R) a
  zero_mul b := zero_star (R := R) b
  mul_add a b c := star_add_right (R := R) a b c
  add_mul a b c := star_add_left (R := R) a b c

/-- The total space of an operad, graded by arity minus one. -/
abbrev Tot (R : Type u) [CommRing R] (P : ℕ → Type v)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] : Type v :=
  ⨁ k : ℕ, Piece R P k

example : NonUnitalNonAssocRing (Tot R P) := inferInstance

/-- The inclusion of a homogeneous piece. -/
abbrev inc (k : ℕ) : Piece R P k →+ Tot R P := DirectSum.of (Piece R P) k

@[simp] lemma inc_mul_inc {i j : ℕ} (a : Piece R P i) (b : Piece R P j) :
    (inc i a * inc j b : Tot R P) = inc (i + j) (star (R := R) a b) :=
  DirectSum.of_mul_of a b

/-- Moving a homogeneous element between propositionally equal degrees. -/
lemma inc_reindex {m n : ℕ} (h : m = n) (x : Piece R P m) :
    (inc m x : Tot R P) = inc n (reindex R P (by rw [h]) x) := by
  subst h
  rw [reindex_self]

/-! ### The pre-Lie identity on the total space

The associator is additive in each argument, so it is enough to check the identity on
homogeneous elements, where it is `star_assoc_symm`. -/

lemma associator_zero_left (y z : Tot R P) : associator 0 y z = 0 := by
  simp only [← AddMonoidHom.associator_apply, map_zero, AddMonoidHom.zero_apply]

lemma associator_zero_mid (x z : Tot R P) : associator x 0 z = 0 := by
  simp only [← AddMonoidHom.associator_apply, map_zero, AddMonoidHom.zero_apply]

lemma associator_zero_right (x y : Tot R P) : associator x y 0 = 0 := by
  simp only [← AddMonoidHom.associator_apply, map_zero]

lemma associator_add_left (x x' y z : Tot R P) :
    associator (x + x') y z = associator x y z + associator x' y z := by
  simp only [← AddMonoidHom.associator_apply, map_add, AddMonoidHom.add_apply]

lemma associator_add_mid (x y y' z : Tot R P) :
    associator x (y + y') z = associator x y z + associator x y' z := by
  simp only [← AddMonoidHom.associator_apply, map_add, AddMonoidHom.add_apply]

lemma associator_add_right (x y z z' : Tot R P) :
    associator x y (z + z') = associator x y z + associator x y z' := by
  simp only [← AddMonoidHom.associator_apply, map_add]

/-- The pre-Lie identity on homogeneous elements: this is `star_assoc_symm`, with the three
degrees moved to the common index `i + j + k`. -/
lemma associator_inc (i j k : ℕ) (a : Piece R P i) (b : Piece R P j) (c : Piece R P k) :
    associator (inc i a : Tot R P) (inc j b) (inc k c)
      = associator (inc i a : Tot R P) (inc k c) (inc j b) := by
  simp only [associator, inc_mul_inc]
  rw [inc_reindex (show i + (j + k) = i + j + k by omega),
    inc_reindex (show i + k + j = i + j + k by omega),
    inc_reindex (show i + (k + j) = i + j + k by omega), ← map_sub, ← map_sub]
  congr 1
  exact star_assoc_symm a b c

/-- **The associator of the total space is symmetric in its last two arguments.** -/
theorem tot_assoc_symm (x y z : Tot R P) : associator x y z = associator x z y := by
  induction x using DirectSum.induction_on with
  | zero => simp only [associator_zero_left]
  | add x₁ x₂ h₁ h₂ => simp only [associator_add_left, h₁, h₂]
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => simp only [associator_zero_mid, associator_zero_right]
    | add y₁ y₂ h₁ h₂ =>
      simp only [associator_add_mid, associator_add_right, h₁, h₂]
    | of j b =>
      induction z using DirectSum.induction_on with
      | zero => simp only [associator_zero_mid, associator_zero_right]
      | add z₁ z₂ h₁ h₂ =>
        simp only [associator_add_mid, associator_add_right, h₁, h₂]
      | of k c => exact associator_inc i j k a b c

/-- **The total space of a non-symmetric operad is a right pre-Lie ring.** -/
instance : RightPreLieRing (Tot R P) where
  __ := (inferInstance : NonUnitalNonAssocRing (Tot R P))
  assoc_symm' := tot_assoc_symm

/-! ### The commutator is a Lie bracket

Mathlib's pre-Lie file stops at the `Left`/`Right PreLieRing` classes and does not derive a Lie
structure, so the Jacobi identity is proved here. The cyclic sum of double commutators collapses
into six associators which cancel in pairs — each pair being one instance of `tot_assoc_symm`. -/

/-- The commutator of the circle product. -/
def comm (x y : Tot R P) : Tot R P := x * y - y * x

lemma comm_def (x y : Tot R P) : comm x y = x * y - y * x := rfl

@[simp] lemma comm_self (x : Tot R P) : comm x x = 0 := sub_self _

lemma comm_antisymm (x y : Tot R P) : comm x y = - comm y x := by
  simp only [comm_def, neg_sub]

/-- The cyclic sum of double commutators, written out in associators. -/
private lemma jacobi_aux (x y z : Tot R P) :
    comm (comm x y) z + comm (comm y z) x + comm (comm z x) y
      = (associator x y z - associator x z y)
        + (associator y z x - associator y x z)
        + (associator z x y - associator z y x) := by
  simp only [comm_def, associator, sub_mul, mul_sub]
  abel

/-- **The Jacobi identity.** The commutator of a right pre-Lie ring is a Lie bracket, so the
total space of an operad is a Lie ring under `⁅α, β⁆ = α ⋆ β - β ⋆ α`. -/
theorem jacobi (x y z : Tot R P) :
    comm (comm x y) z + comm (comm y z) x + comm (comm z x) y = 0 := by
  rw [jacobi_aux, tot_assoc_symm x y z, tot_assoc_symm y z x, tot_assoc_symm z x y]
  abel

end

end Operad
