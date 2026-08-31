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

/-! ### Splitting the slots of `α ⋆ β`

For a fixed slot `i` of `α`, the slots of `α ⋆ β` divide into the `k+1` slots contributed by
`β` — the image of `nestedEmb i` — and the rest, which are slots of `α` other than `i`. -/

/-- The slots of `α ⋆ β` contributed by `β`, when `β` sits at `α`'s slot `i`. -/
def nestedEmb {j k : ℕ} (i : Fin (j + 1)) : Fin (k + 1) ↪ Fin (j + k + 1) where
  toFun i'' := ⟨(i : ℕ) + (i'' : ℕ), by have := i.isLt; have := i''.isLt; omega⟩
  inj' a b h := by
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)

/-- The set of slots of `α ⋆ β` coming from `β`. -/
def nested {j k : ℕ} (i : Fin (j + 1)) : Finset (Fin (j + k + 1)) :=
  Finset.univ.map (nestedEmb i)

@[simp] lemma mem_nested {j k : ℕ} (i : Fin (j + 1)) (i' : Fin (j + k + 1)) :
    i' ∈ nested (k := k) i ↔ ∃ i'' : Fin (k + 1), (i' : ℕ) = (i : ℕ) + (i'' : ℕ) := by
  constructor
  · rintro h
    obtain ⟨i'', -, rfl⟩ := Finset.mem_map.1 h
    exact ⟨i'', rfl⟩
  · rintro ⟨i'', hi''⟩
    exact Finset.mem_map.2 ⟨i'', Finset.mem_univ _, Fin.ext hi''.symm⟩

/-- The part of the associator that survives: the pairs of *disjoint* slots. -/
def disjointPart {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    P (j + k + l + 1) :=
  ∑ i : Fin (j + 1), ∑ i' ∈ (nested (k := k) i)ᶜ,
    compFin (R := R) i' (compFin (R := R) i α β) γ

/-- Over the nested slots, the double sum reproduces `α ⋆ (β ⋆ γ)` term by term: this is exactly
`compFin_assoc_seq`. -/
lemma sum_nested {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1))
    (i : Fin (j + 1)) :
    reindex R P (by omega)
        (∑ i' ∈ nested (k := k) i, compFin (R := R) i' (compFin (R := R) i α β) γ)
      = ∑ i'' : Fin (k + 1), compFin (R := R) i α (compFin (R := R) i'' β γ) := by
  rw [nested, Finset.sum_map]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i'' _ => ?_
  exact compFin_assoc_seq i i'' α β γ

/-- **The associator, isolated.** `(α ⋆ β) ⋆ γ` is `α ⋆ (β ⋆ γ)` plus the disjoint-slot part. -/
lemma star_star_left_split {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    star (R := R) (star (R := R) α β) γ
      = reindex R P (by omega) (star (R := R) α (star (R := R) β γ))
        + disjointPart (R := R) α β γ := by
  have key : ∀ i : Fin (j + 1),
      (∑ i' : Fin (j + k + 1), compFin (R := R) i' (compFin (R := R) i α β) γ)
        = reindex R P (by omega)
            (∑ i'' : Fin (k + 1), compFin (R := R) i α (compFin (R := R) i'' β γ))
          + ∑ i' ∈ (nested (k := k) i)ᶜ,
              compFin (R := R) i' (compFin (R := R) i α β) γ := by
    intro i
    rw [← Finset.sum_add_sum_compl (nested (k := k) i)]
    congr 1
    rw [← sum_nested α β γ i, reindex_reindex, reindex_self]
  rw [star_star_left, Finset.sum_comm, disjointPart,
    Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib]
  congr 1
  rw [star_star_right]
  exact (map_sum _ _ _).symm

end Operad
