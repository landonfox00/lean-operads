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

/-! ### Splitting the disjoint slots into "before" and "after"

A slot of `α ⋆ β` outside `β`'s block is either strictly before `α`'s slot `i`, or strictly
after the block `[i, i+k]`. Treating the two separately makes each of the two reindexing
bijections below single-case. -/

lemma not_mem_nested_iff {j k : ℕ} (i : Fin (j + 1)) (i' : Fin (j + k + 1)) :
    i' ∉ nested (k := k) i ↔ (i' : ℕ) < (i : ℕ) ∨ (i : ℕ) + k < (i' : ℕ) := by
  simp only [mem_nested, not_exists]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h ⟨(i' : ℕ) - (i : ℕ), by omega⟩
      (by show (i' : ℕ) = (i : ℕ) + ((i' : ℕ) - (i : ℕ)); omega)
  · rintro (h | h) i'' hi''
    · have := i''.isLt; omega
    · have := i''.isLt; omega

/-- Slots of `α ⋆ β` strictly before `α`'s slot `i`. -/
def before {j k : ℕ} (i : Fin (j + 1)) : Finset (Fin (j + k + 1)) :=
  Finset.univ.filter fun i' => (i' : ℕ) < (i : ℕ)

/-- Slots of `α ⋆ β` strictly after the block contributed by `β`. -/
def after {j k : ℕ} (i : Fin (j + 1)) : Finset (Fin (j + k + 1)) :=
  Finset.univ.filter fun i' => (i : ℕ) + k < (i' : ℕ)

@[simp] lemma mem_before {j k : ℕ} (i : Fin (j + 1)) (i' : Fin (j + k + 1)) :
    i' ∈ before (k := k) i ↔ (i' : ℕ) < (i : ℕ) := by simp [before]

@[simp] lemma mem_after {j k : ℕ} (i : Fin (j + 1)) (i' : Fin (j + k + 1)) :
    i' ∈ after (k := k) i ↔ (i : ℕ) + k < (i' : ℕ) := by simp [after]

lemma sum_compl_nested {j k : ℕ} {M : Type w} [AddCommMonoid M] (i : Fin (j + 1))
    (f : Fin (j + k + 1) → M) :
    ∑ i' ∈ (nested (k := k) i)ᶜ, f i'
      = (∑ i' ∈ before (k := k) i, f i') + ∑ i' ∈ after (k := k) i, f i' := by
  rw [← Finset.sum_filter_add_sum_filter_not ((nested (k := k) i)ᶜ)
      fun i' => (i' : ℕ) < (i : ℕ)]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i'
    simp only [Finset.mem_filter, Finset.mem_compl, not_mem_nested_iff, mem_before]
    omega
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i'
    simp only [Finset.mem_filter, Finset.mem_compl, not_mem_nested_iff, mem_after]
    omega

/-! ### The two reindexing bijections

A `β`-then-`γ` pair with `γ` *before* `β` is the same data as a `γ`-then-`β` pair with `β`
*after* `γ`, and vice versa. Term by term the identification is `compFin_assoc_par`. -/

lemma sum_before_eq {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    ((∑ i : Fin (j + 1), ∑ i' ∈ before (k := k) i,
        compFin (R := R) i' (compFin (R := R) i α β) γ) : P (j + k + l + 1))
      = ∑ s : Fin (j + 1), ∑ t ∈ after (k := l) s,
          reindex R P (by omega) (compFin (R := R) t (compFin (R := R) s α γ) β) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x => ⟨⟨min (x.2 : ℕ) j, by omega⟩, ⟨(x.1 : ℕ) + l, by have := x.1.isLt; omega⟩⟩)
    (fun y => ⟨⟨(y.2 : ℕ) - l, by have := y.2.isLt; omega⟩,
               ⟨(y.1 : ℕ), by have := y.1.isLt; omega⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and] at hx
    have := i.isLt
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and]
    show min (i' : ℕ) j + l < (i : ℕ) + l
    omega
  · rintro ⟨s, t⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and] at hy
    have := s.isLt
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and]
    show (s : ℕ) < (t : ℕ) - l
    omega
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and] at hx
    have := i.isLt
    simp only [Sigma.mk.injEq, heq_iff_eq, Fin.ext_iff]
    omega
  · rintro ⟨s, t⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and] at hy
    have := s.isLt
    simp only [Sigma.mk.injEq, heq_iff_eq, Fin.ext_iff]
    omega
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and] at hx
    have hij := i.isLt
    have hmin : min (i' : ℕ) j = (i' : ℕ) := by omega
    dsimp only
    have key : compFin (R := R) (⟨(i : ℕ) + l, by omega⟩ : Fin (j + l + 1))
          (compFin (R := R) (⟨min (i' : ℕ) j, by omega⟩ : Fin (j + 1)) α γ) β
        = reindex R P (by omega)
            (compFin (R := R) (⟨min (i' : ℕ) j, by omega⟩ : Fin (j + k + 1))
              (compFin (R := R) i α β) γ) :=
      compFin_assoc_par _ _ (by show min (i' : ℕ) j < (i : ℕ); omega) α γ β
    rw [key, show (⟨min (i' : ℕ) j, by omega⟩ : Fin (j + k + 1)) = i' from Fin.ext hmin,
      reindex_reindex]
    exact (reindex_self (R := R) (P := P) _ _).symm

lemma sum_after_eq {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    ((∑ i : Fin (j + 1), ∑ i' ∈ after (k := k) i,
        compFin (R := R) i' (compFin (R := R) i α β) γ) : P (j + k + l + 1))
      = ∑ s : Fin (j + 1), ∑ t ∈ before (k := l) s,
          reindex R P (by omega) (compFin (R := R) t (compFin (R := R) s α γ) β) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x => ⟨⟨(x.2 : ℕ) - k, by have := x.2.isLt; omega⟩,
               ⟨(x.1 : ℕ), by have := x.1.isLt; omega⟩⟩)
    (fun y => ⟨⟨min (y.2 : ℕ) j, by omega⟩,
               ⟨(y.1 : ℕ) + k, by have := y.1.isLt; omega⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and] at hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and]
    show (i : ℕ) < (i' : ℕ) - k
    omega
  · rintro ⟨s, t⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and] at hy
    have := s.isLt
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and]
    show min (t : ℕ) j + k < (s : ℕ) + k
    omega
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and] at hx
    have := i.isLt
    simp only [Sigma.mk.injEq, heq_iff_eq, Fin.ext_iff]
    omega
  · rintro ⟨s, t⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and] at hy
    have := s.isLt
    simp only [Sigma.mk.injEq, heq_iff_eq, Fin.ext_iff]
    omega
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and] at hx
    have hi' := i'.isLt
    dsimp only
    have h := compFin_assoc_par (R := R) i (⟨(i' : ℕ) - k, by omega⟩ : Fin (j + 1))
      (by show (i : ℕ) < (i' : ℕ) - k; omega) α β γ
    dsimp only at h
    conv_lhs =>
      rw [show i' = (⟨(i' : ℕ) - k + k, by omega⟩ : Fin (j + k + 1)) from
        Fin.ext (show (i' : ℕ) = (i' : ℕ) - k + k by omega)]
    exact h

/-! ### The pre-Lie identity -/

/-- **The disjoint part is symmetric in `β` and `γ`.** Swapping the two inserted operations
exchanges the "before" and "after" halves of the sum. -/
theorem disjointPart_symm {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    disjointPart (R := R) α β γ
      = reindex R P (by omega) (disjointPart (R := R) α γ β) := by
  unfold disjointPart
  rw [Finset.sum_congr rfl fun i _ => sum_compl_nested i _,
    Finset.sum_congr rfl fun s _ => sum_compl_nested s _,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [sum_before_eq α β γ, sum_after_eq α β γ, map_add, map_sum]
  exact add_comm _ _

/-- **The pre-Lie identity.** The associator of the circle product is symmetric in its last two
arguments, so the total space of a non-symmetric operad is a right pre-Lie algebra. -/
theorem star_assoc_symm {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    star (R := R) (star (R := R) α β) γ
        - reindex R P (by omega) (star (R := R) α (star (R := R) β γ))
      = reindex R P (by omega) (star (R := R) (star (R := R) α γ) β)
        - reindex R P (by omega) (star (R := R) α (star (R := R) γ β)) := by
  rw [star_star_left_split, star_star_left_split α γ β]
  rw [map_add, disjointPart_symm α β γ]
  simp only [reindex_reindex, add_sub_cancel_left]

end Operad
