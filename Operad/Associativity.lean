/-
# Associativity in textbook `∘ᵢ` form

`Operad.Basic` states the two associativity axioms in the positional convention, which is what
makes them provable by `omega`. This file restates them for `compFin`, i.e. with genuine slot
indices, which is the form the `⋆` product needs.

The translation is entirely reindex plumbing: `compFin i α β` is *by definition*
`reindex (comp i (m-i-1) (reindex α) β)`, so the positional axioms apply once the reindexings are
pushed around with `reindex_reindex`, `comp_index_congr` and `comp_arity_congr`.
-/
import Operad.Constructions

universe u v

namespace Operad

open NSOperad

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-- **Sequential associativity, `∘ᵢ` form.** Composing `γ` into the slot of `α ∘ᵢ β` that came
from `β`'s slot `j` is the same as composing `β ∘ⱼ γ` into `α`'s slot `i`. -/
lemma compFin_assoc_seq {m n p : ℕ} (i : Fin m) (j : Fin n) (α : P m) (β : P n) (γ : P p) :
    reindex R P (by have := i.isLt; have := j.isLt; omega)
        (compFin (R := R)
          (⟨(i : ℕ) + (j : ℕ), by have := i.isLt; have := j.isLt; omega⟩ : Fin (m - 1 + n))
          (compFin (R := R) i α β) γ)
      = compFin (R := R) i α (compFin (R := R) j β γ) := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [compFin, reindex_reindex]
  -- Split the outer reindex on the left so that the trailing index becomes `d + b`.
  rw [← reindex_reindex
      (show (i : ℕ) + n + (m - (i : ℕ) - 1)
          = ((i : ℕ) + (j : ℕ)) + 1 + ((n - (j : ℕ) - 1) + (m - (i : ℕ) - 1)) by omega)
      (show ((i : ℕ) + (j : ℕ)) + 1 + ((n - (j : ℕ) - 1) + (m - (i : ℕ) - 1))
          = ((i : ℕ) + (j : ℕ)) + 1 + (m - 1 + n - ((i : ℕ) + (j : ℕ)) - 1) by omega),
    comp_index_congr ((i : ℕ) + (j : ℕ))
      (show (n - (j : ℕ) - 1) + (m - (i : ℕ) - 1)
          = m - 1 + n - ((i : ℕ) + (j : ℕ)) - 1 by omega)]
  -- Split the inner reindex so that its target is the grouping `a + (c+1+d) + b` that
  -- `comp_arity_congr` produces.
  rw [← reindex_reindex
      (show (i : ℕ) + n + (m - (i : ℕ) - 1)
          = (i : ℕ) + ((j : ℕ) + 1 + (n - (j : ℕ) - 1)) + (m - (i : ℕ) - 1) by omega)
      (show (i : ℕ) + ((j : ℕ) + 1 + (n - (j : ℕ) - 1)) + (m - (i : ℕ) - 1)
          = ((i : ℕ) + (j : ℕ)) + 1 + ((n - (j : ℕ) - 1) + (m - (i : ℕ) - 1)) by omega)]
  -- Introduce the reindexing of `β` that the positional axiom expects.
  rw [← comp_arity_congr (i : ℕ) (m - (i : ℕ) - 1)
      (show n = (j : ℕ) + 1 + (n - (j : ℕ) - 1) by omega)]
  -- Collapse the accumulated reindexings, then split off exactly the one the axiom carries.
  simp only [reindex_reindex]
  rw [← reindex_reindex
      (show ((i : ℕ) + (j : ℕ)) + p + ((n - (j : ℕ) - 1) + (m - (i : ℕ) - 1))
          = (i : ℕ) + ((j : ℕ) + p + (n - (j : ℕ) - 1)) + (m - (i : ℕ) - 1) by omega)
      (show (i : ℕ) + ((j : ℕ) + p + (n - (j : ℕ) - 1)) + (m - (i : ℕ) - 1)
          = m - 1 + (n - 1 + p) by omega)]
  rw [comp_assoc_seq]
  -- The right-hand side still carries `compFin`'s own reindexing; pull it out.
  rw [comp_arity_congr]
  simp only [reindex_reindex]

end Operad
