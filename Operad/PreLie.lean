/-
# Towards the pre-Lie identity

The associator of `⋆` is symmetric in its last two arguments. Expanding both
`(α ⋆ β) ⋆ γ` and `α ⋆ (β ⋆ γ)` turns the claim into a statement about a double sum over
slot pairs, which splits in two:

* pairs where the second insertion lands **inside** the block created by the first — these are
  matched up by `compFin_assoc_seq` and are exactly `α ⋆ (β ⋆ γ)`;
* pairs where the two insertions are at **disjoint** slots of `α` — these survive into the
  associator, and `compFin_assoc_par` says they are symmetric in `β` and `γ`.

This file builds that expansion.
-/
import Operad.Total
import Operad.Associativity

universe u v w

namespace Operad

open NSOperad Finset

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-! ### `compFin` distributes over finite sums -/

/-- Composing into a fixed slot, as an additive map in the outer operation. -/
def compFinLeftHom {m n : ℕ} (i : Fin m) (β : P n) : P m →+ P (m - 1 + n) where
  toFun α := compFin (R := R) i α β
  map_zero' := compFin_zero_left i β
  map_add' α α' := compFin_add_left i α α' β

/-- Composing into a fixed slot, as an additive map in the inserted operation. -/
def compFinRightHom {m n : ℕ} (i : Fin m) (α : P m) : P n →+ P (m - 1 + n) where
  toFun β := compFin (R := R) i α β
  map_zero' := compFin_zero_right i α
  map_add' β β' := compFin_add_right i α β β'

lemma compFin_sum_left {m n : ℕ} {ι : Type w} (s : Finset ι) (i : Fin m) (f : ι → P m)
    (β : P n) :
    compFin (R := R) i (∑ x ∈ s, f x) β = ∑ x ∈ s, compFin (R := R) i (f x) β :=
  map_sum (compFinLeftHom (R := R) i β) f s

lemma compFin_sum_right {m n : ℕ} {ι : Type w} (s : Finset ι) (i : Fin m) (α : P m)
    (g : ι → P n) :
    compFin (R := R) i α (∑ x ∈ s, g x) = ∑ x ∈ s, compFin (R := R) i α (g x) :=
  map_sum (compFinRightHom (R := R) i α) g s

/-! ### Expanding the two bracketings into double sums -/

/-- `(α ⋆ β) ⋆ γ`, expanded over the slot of the outer composition and the slot of `α`. -/
lemma star_star_left {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    star (R := R) (star (R := R) α β) γ
      = ∑ i' : Fin (j + k + 1), ∑ i : Fin (j + 1),
          compFin (R := R) i' (compFin (R := R) i α β) γ := by
  rw [star_def]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [star_def]
  exact map_sum (compFinLeftHom (R := R) i' γ) _ _

/-- `α ⋆ (β ⋆ γ)`, expanded over the slot of `α` and the slot of `β`. -/
lemma star_star_right {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    star (R := R) α (star (R := R) β γ)
      = ∑ i : Fin (j + 1), ∑ i'' : Fin (k + 1),
          compFin (R := R) i α (compFin (R := R) i'' β γ) := by
  rw [star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_def]
  exact map_sum (compFinRightHom (R := R) i α) _ _

end Operad
