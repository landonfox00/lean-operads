/-
# `Perm` in the set-operad calculus

The underlying set operad of `Perm`, seen through `SetOperad.bin`: filling the two inputs of a
binary element `m = (m₀, m₁)` with `x` and `y` gives `(m₀ x Σy, m₁ (Σx) y)` (`bin_inl`,
`bin_inr`). The one consequence recorded here is that `Perm` has no nonzero commutative and
associative binary element (`eq_zero_of_isComm_isAssoc`), over a ring without zero divisors: the
associativity relator forces `m₀ m₁ = 0`, and commutativity forces `m₀ = m₁`. So a morphism of
operads into `Perm` kills every commutative associative binary element
(`app_eq_zero_of_isComm_isAssoc`); in particular every morphism from `Com` to `Perm` vanishes in
arity two.
-/
import Operad.ComSet
import Mathlib.Tactic.LinearCombination

set_option synthInstance.maxSize 1024

universe u

namespace Operad

open Sym SetOperad

namespace Sym.Perm

variable {R : Type u} [CommRing R] {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B]

/-- An element of `Perm`, in the underlying set operad. -/
abbrev und (x : Perm R A) : Und R (Perm R) A := Und.of R (Perm R) x

/-- An element of the underlying set operad, as a function. -/
abbrev fn (x : Und R (Perm R) A) : A → R := (Und.of R (Perm R)).symm x

lemma bin_inl (m : Und R (Perm R) (Fin 2)) (x : Und R (Perm R) A) (y : Und R (Perm R) B)
    (a : A) : fn (bin m x y) (Sum.inl a) = fn m 0 * fn x a * ∑ b, fn y b := rfl

lemma bin_inr (m : Und R (Perm R) (Fin 2)) (x : Und R (Perm R) A) (y : Und R (Perm R) B)
    (b : B) : fn (bin m x y) (Sum.inr b) = fn m 1 * (∑ a, fn x a) * fn y b := by
  show fn m ((⟨1, by decide⟩ : Without (Fin 2) 0) : Fin 2) * (∑ a, fn x a) * fn y b = _
  rfl

lemma one_fn (u : Unit) : fn (one : Und R (Perm R) Unit) u = 1 := rfl

lemma map_fn {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (x : Und R (Perm R) A)
    (a' : A') : fn (map e x) a' = fn x (e.symm a') := rfl

/-- **The associativity relator in `Perm`**: an associative binary element has `m₀ m₁ = 0`. -/
lemma mul_eq_zero_of_isAssoc {m : Und R (Perm R) (Fin 2)} (ha : IsAssoc m) :
    fn m 0 * fn m 1 = 0 := by
  have h := congrArg (fun z => fn z (Sum.inl ())) ha
  simp only [map_fn, Equiv.sumAssoc_symm_apply_inl, bin_inl, one_fn, Fintype.sum_unique,
    Fintype.sum_sum_type, bin_inr, mul_one] at h
  linear_combination -h

/-- **`Perm` has no nonzero commutative associative binary element**, over a ring without zero
divisors. -/
theorem eq_zero_of_isComm_isAssoc [NoZeroDivisors R] {m : Und R (Perm R) (Fin 2)}
    (hc : IsComm m) (ha : IsAssoc m) (k : Fin 2) : fn m k = 0 := by
  have h01 : fn m 0 = fn m 1 := by
    have := congrArg (fun z => fn z 0) hc
    simpa [map_fn] using this.symm
  have h0 : fn m 0 = 0 := by
    have := mul_eq_zero_of_isAssoc ha
    rw [← h01] at this
    exact mul_self_eq_zero.mp this
  fin_cases k
  · exact h0
  · exact h01 ▸ h0

/-- **A morphism of operads into `Perm` kills every commutative associative binary element**,
over a ring without zero divisors. -/
theorem app_eq_zero_of_isComm_isAssoc [NoZeroDivisors R]
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
    (f : SymOperadHom R P (Perm R)) {μ : P (Fin 2)} (hc : IsComm (Und.of R P μ))
    (ha : IsAssoc (Und.of R P μ)) : f.app _ μ = 0 := by
  funext k
  exact eq_zero_of_isComm_isAssoc (isComm_app hc f.und) (isAssoc_app ha f.und) k

end Sym.Perm

end Operad
