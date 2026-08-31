/-
# The graded pre-Lie identity

`Operad.PreLie` proves the *ungraded* identity: the associator of `⋆` is symmetric in its last
two arguments. `Operad.DG` introduces the signed product `⋆ₛ` of the operadic suspension. This
file combines them, proving the identity `⋆ₛ` actually satisfies:

`(α ⋆ₛ β) ⋆ₛ γ - α ⋆ₛ (β ⋆ₛ γ) = (-1)^(k l) [(α ⋆ₛ γ) ⋆ₛ β - α ⋆ₛ (γ ⋆ₛ β)]`

where `k` and `l` are the degrees of `β` and `γ`. Two facts make this a decoration of the
ungraded proof rather than a new one.

* Over the **nested** slots the signs cancel identically: the left side carries
  `(-1)^((a+c) l + a k)` and the right needs `(-1)^(a (k+l) + c l)`, and those exponents are
  equal on the nose. So `sum_nested` needs no sign correction at all.
* Over the **disjoint** slots each of the two index bijections contributes exactly `(-1)^(k l)`
  — the same factor in both the "before" and "after" cases.

So the whole sign of the identity is a single global factor, and the combinatorial scaffolding
of `Operad.PreLie` (`nested`, `before`, `after`, `sum_compl_nested`) is reused unchanged.
-/
import Operad.DG
import Operad.PreLie

universe u v w

namespace Operad

open NSOperad Finset

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-! ### Sign arithmetic -/

/-- Adding an even number to the exponent does not change `(-1)^n`. -/
private lemma neg_one_pow_add_two_mul (a b : ℕ) : ((-1 : R)) ^ (a + 2 * b) = (-1) ^ a := by
  rw [pow_add, pow_mul]
  norm_num

/-- Two signs agree once their exponents are exhibited as differing by an even number. -/
private lemma neg_one_pow_eq {a b : ℕ} (c : ℕ) (h : a = b + 2 * c) :
    ((-1 : R)) ^ a = (-1) ^ b := by
  subst h; exact neg_one_pow_add_two_mul b c

/-! ### Expanding the two bracketings -/

/-- `(α ⋆ₛ β) ⋆ₛ γ` as a signed double sum. -/
lemma sstar_sstar_left {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    sstar (R := R) (sstar (R := R) α β) γ
      = ∑ i' : Fin (j + k + 1), ∑ i : Fin (j + 1),
          ((-1 : R) ^ ((i' : ℕ) * l + (i : ℕ) * k))
            • compFin (R := R) i' (compFin (R := R) i α β) γ := by
  rw [sstar_def]
  refine Finset.sum_congr rfl fun i' _ => ?_
  have hinner : compFin (R := R) i' (sstar (R := R) α β) γ
      = ∑ i : Fin (j + 1), ((-1 : R) ^ ((i : ℕ) * k))
          • compFin (R := R) i' (compFin (R := R) i α β) γ := by
    rw [sstar_def]
    refine (map_sum (compFinLeftHom (R := R) i' γ) _ _).trans ?_
    exact Finset.sum_congr rfl fun i _ => compFin_smul_left i' _ _ γ
  rw [hinner]
  refine (map_sum (LinearMap.lsmul R (P (j + k + l + 1))
    ((-1 : R) ^ ((i' : ℕ) * l))) _ _).trans ?_
  exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.lsmul_apply, pow_add, mul_smul]; rfl

/-- `α ⋆ₛ (β ⋆ₛ γ)` as a signed double sum. -/
lemma sstar_sstar_right {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    sstar (R := R) α (sstar (R := R) β γ)
      = ∑ i : Fin (j + 1), ∑ i'' : Fin (k + 1),
          ((-1 : R) ^ ((i : ℕ) * (k + l) + (i'' : ℕ) * l))
            • compFin (R := R) i α (compFin (R := R) i'' β γ) := by
  rw [sstar_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hinner : compFin (R := R) i α (sstar (R := R) β γ)
      = ∑ i'' : Fin (k + 1), ((-1 : R) ^ ((i'' : ℕ) * l))
          • compFin (R := R) i α (compFin (R := R) i'' β γ) := by
    rw [sstar_def]
    refine (map_sum (compFinRightHom (R := R) i α) _ _).trans ?_
    exact Finset.sum_congr rfl fun i'' _ => compFin_smul_right i _ α _
  rw [hinner]
  refine (map_sum (LinearMap.lsmul R (P (j + (k + l) + 1))
    ((-1 : R) ^ ((i : ℕ) * (k + l)))) _ _).trans ?_
  exact Finset.sum_congr rfl fun i'' _ => by rw [LinearMap.lsmul_apply, pow_add, mul_smul]; rfl

/-! ### The nested slots

Here the signs cancel exactly, so this is `compFin_assoc_seq` with a sign carried along
unchanged. -/

/-- The signed disjoint-slot part of the associator. -/
def disjointPartS {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    P (j + k + l + 1) :=
  ∑ i : Fin (j + 1), ∑ i' ∈ (nested (k := k) i)ᶜ,
    ((-1 : R) ^ ((i' : ℕ) * l + (i : ℕ) * k))
      • compFin (R := R) i' (compFin (R := R) i α β) γ

/-- Over the nested slots the signed double sum reproduces `α ⋆ₛ (β ⋆ₛ γ)` term by term. -/
lemma sum_nested_s {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1))
    (i : Fin (j + 1)) :
    reindex R P (by omega)
        (∑ i' ∈ nested (k := k) i, ((-1 : R) ^ ((i' : ℕ) * l + (i : ℕ) * k))
          • compFin (R := R) i' (compFin (R := R) i α β) γ)
      = ∑ i'' : Fin (k + 1), ((-1 : R) ^ ((i : ℕ) * (k + l) + (i'' : ℕ) * l))
          • compFin (R := R) i α (compFin (R := R) i'' β γ) := by
  rw [nested, Finset.sum_map, map_sum]
  refine Finset.sum_congr rfl fun i'' _ => ?_
  rw [map_smul]
  congr 1
  · exact congrArg _ (by simp only [nestedEmb, Function.Embedding.coeFn_mk]; ring)
  · exact compFin_assoc_seq i i'' α β γ

end Operad
