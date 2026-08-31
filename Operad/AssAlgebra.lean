/-
# Algebras over `Ass` are associative algebras

This is the end-to-end test of the whole library: an abstract algebra over the operad `Ass`
produces a genuine associative multiplication on `V`, and associativity is *derived* rather than
assumed. The proof is a good illustration of how operads are supposed to be used:

* in `Ass` the two ways of building a ternary operation from binary ones are equal — both are
  `1 * 1 = 1` — and this is true by `rfl`;
* pushing that single equation through the algebra morphism turns it into an equation between
  two elements of `End R V 3`;
* evaluating that equation on a triple is exactly associativity.

Nothing about associativity is put in by hand; it comes from the operad axioms plus the fact
that `Ass` is one-dimensional in each arity.
-/
import Operad.Algebra
import Mathlib.Data.Fin.VecNotation

universe u v

namespace Operad

open NSOperad

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

namespace AssAlgebra

/-- The binary operation carried by an `Ass`-algebra. -/
def mul (A : Algebra R (Ass R) V) (x y : V) : V :=
  A.act (1 : Ass R 2) ![x, y]

lemma mul_def (A : Algebra R (Ass R) V) (x y : V) :
    mul A x y = A.app 2 (1 : Ass R 2) ![x, y] := rfl

/-! ### Computing the two tuple operations in arity 3 -/

lemma midTuple_left (v : Fin 3 → V) :
    End.midTuple (V := V) 0 1 (n := 2) v = ![v 0, v 1] := by
  funext j
  fin_cases j <;> rfl

lemma insTuple_left (w : V) (v : Fin 3 → V) :
    End.insTuple (V := V) 0 1 (n := 2) w v = ![w, v 2] := by
  funext i
  fin_cases i
  · show End.insTuple (V := V) 0 1 (n := 2) w v ⟨0, by omega⟩ = ![w, v 2] ⟨0, by omega⟩
    exact End.insTuple_of_eq (n := 2) 0 1 w v ⟨0, by omega⟩ rfl
  · show End.insTuple (V := V) 0 1 (n := 2) w v ⟨1, by omega⟩ = ![w, v 2] ⟨1, by omega⟩
    rw [End.insTuple_of_gt (n := 2) 0 1 w v ⟨1, by omega⟩ (by norm_num)]
    rfl

lemma midTuple_right (v : Fin 3 → V) :
    End.midTuple (V := V) 1 0 (n := 2) v = ![v 1, v 2] := by
  funext j
  fin_cases j <;> rfl

lemma insTuple_right (w : V) (v : Fin 3 → V) :
    End.insTuple (V := V) 1 0 (n := 2) w v = ![v 0, w] := by
  funext i
  fin_cases i
  · show End.insTuple (V := V) 1 0 (n := 2) w v ⟨0, by omega⟩ = ![v 0, w] ⟨0, by omega⟩
    rw [End.insTuple_of_lt (n := 2) 1 0 w v ⟨0, by omega⟩ (by norm_num)]
    rfl
  · show End.insTuple (V := V) 1 0 (n := 2) w v ⟨1, by omega⟩ = ![v 0, w] ⟨1, by omega⟩
    exact End.insTuple_of_eq (n := 2) 1 0 w v ⟨1, by omega⟩ rfl

/-! ### Associativity -/

/-- In `Ass`, the two ternary operations built from the binary generator coincide: both are
`1 * 1`. This single `rfl` is the entire input to associativity. -/
lemma ass_comp_eq :
    comp (R := R) (P := Ass R) 0 1 (1 : Ass R 2) (1 : Ass R 2)
      = comp (R := R) (P := Ass R) 1 0 (1 : Ass R 2) (1 : Ass R 2) := rfl

/-- **Every algebra over `Ass` is an associative algebra.** -/
theorem mul_assoc (A : Algebra R (Ass R) V) (x y z : V) :
    mul A (mul A x y) z = mul A x (mul A y z) := by
  -- Transport the `Ass`-level identity through the algebra structure.
  have key : NSOperad.comp (R := R) (P := End R V) 0 1
        (A.app 2 (1 : Ass R 2)) (A.app 2 (1 : Ass R 2))
      = NSOperad.comp (R := R) (P := End R V) 1 0
        (A.app 2 (1 : Ass R 2)) (A.app 2 (1 : Ass R 2)) := by
    have h0 := congrArg (A.app 3) (ass_comp_eq (R := R))
    rw [A.app_comp (n := 2) 0 1 (1 : Ass R 2) (1 : Ass R 2),
      A.app_comp (n := 2) 1 0 (1 : Ass R 2) (1 : Ass R 2)] at h0
    exact h0
  -- Evaluate that identity in `End R V 3` on the triple `![x, y, z]`.
  have h : NSOperad.comp (R := R) (P := End R V) 0 1
        (A.app 2 (1 : Ass R 2)) (A.app 2 (1 : Ass R 2)) ![x, y, z]
      = NSOperad.comp (R := R) (P := End R V) 1 0
        (A.app 2 (1 : Ass R 2)) (A.app 2 (1 : Ass R 2)) ![x, y, z] := by
    rw [key]
  rw [End.operad_comp_apply (n := 2) 0 1 _ _ ![x, y, z],
    End.operad_comp_apply (n := 2) 1 0 _ _ ![x, y, z],
    midTuple_left, insTuple_left, midTuple_right, insTuple_right] at h
  simpa [mul_def] using h

end AssAlgebra

end Operad
