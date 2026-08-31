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

/-- **The signed associator, isolated.** `(α ⋆ₛ β) ⋆ₛ γ` is `α ⋆ₛ (β ⋆ₛ γ)` plus the
disjoint-slot part. -/
lemma sstar_sstar_left_split {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    sstar (R := R) (sstar (R := R) α β) γ
      = reindex R P (by omega) (sstar (R := R) α (sstar (R := R) β γ))
        + disjointPartS (R := R) α β γ := by
  have key : ∀ i : Fin (j + 1),
      (∑ i' : Fin (j + k + 1), ((-1 : R) ^ ((i' : ℕ) * l + (i : ℕ) * k))
          • compFin (R := R) i' (compFin (R := R) i α β) γ)
        = reindex R P (by omega)
            (∑ i'' : Fin (k + 1), ((-1 : R) ^ ((i : ℕ) * (k + l) + (i'' : ℕ) * l))
              • compFin (R := R) i α (compFin (R := R) i'' β γ))
          + ∑ i' ∈ (nested (k := k) i)ᶜ, ((-1 : R) ^ ((i' : ℕ) * l + (i : ℕ) * k))
              • compFin (R := R) i' (compFin (R := R) i α β) γ := by
    intro i
    rw [← Finset.sum_add_sum_compl (nested (k := k) i)]
    congr 1
    rw [← sum_nested_s α β γ i, reindex_reindex, reindex_self]
  rw [sstar_sstar_left, Finset.sum_comm, disjointPartS,
    Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib]
  congr 1
  rw [sstar_sstar_right]
  exact (map_sum _ _ _).symm

/-! ### The two signed bijections

Each carries the global factor `(-1)^(k l)`, absorbed here into the exponent of the image term.
In the "before" case the two exponents differ by `2 k l`; in the "after" case they are equal on
the nose, because `(i' - k) l` already absorbs one `k l`. -/

lemma sum_before_eq_s {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    ((∑ i : Fin (j + 1), ∑ i' ∈ before (k := k) i,
        ((-1 : R) ^ ((i' : ℕ) * l + (i : ℕ) * k))
          • compFin (R := R) i' (compFin (R := R) i α β) γ) : P (j + k + l + 1))
      = ∑ s : Fin (j + 1), ∑ t ∈ after (k := l) s,
          ((-1 : R) ^ (k * l + (t : ℕ) * k + (s : ℕ) * l))
            • reindex R P (by omega) (compFin (R := R) t (compFin (R := R) s α γ) β) := by
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
    congr 1
    · simp only [Fin.val_mk, hmin]
      refine (neg_one_pow_eq (R := R) (k * l) ?_).symm
      ring
    · have key : compFin (R := R) (⟨(i : ℕ) + l, by omega⟩ : Fin (j + l + 1))
            (compFin (R := R) (⟨min (i' : ℕ) j, by omega⟩ : Fin (j + 1)) α γ) β
          = reindex R P (by omega)
              (compFin (R := R) (⟨min (i' : ℕ) j, by omega⟩ : Fin (j + k + 1))
                (compFin (R := R) i α β) γ) :=
        compFin_assoc_par _ _ (by show min (i' : ℕ) j < (i : ℕ); omega) α γ β
      rw [key, show (⟨min (i' : ℕ) j, by omega⟩ : Fin (j + k + 1)) = i' from Fin.ext hmin,
        reindex_reindex]
      exact (reindex_self (R := R) (P := P) _ _).symm

lemma sum_after_eq_s {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    ((∑ i : Fin (j + 1), ∑ i' ∈ after (k := k) i,
        ((-1 : R) ^ ((i' : ℕ) * l + (i : ℕ) * k))
          • compFin (R := R) i' (compFin (R := R) i α β) γ) : P (j + k + l + 1))
      = ∑ s : Fin (j + 1), ∑ t ∈ before (k := l) s,
          ((-1 : R) ^ (k * l + (t : ℕ) * k + (s : ℕ) * l))
            • reindex R P (by omega) (compFin (R := R) t (compFin (R := R) s α γ) β) := by
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
    congr 1
    · refine congrArg (fun e => ((-1 : R)) ^ e) ?_
      obtain ⟨m, hm⟩ : ∃ m, (i' : ℕ) = m + k := ⟨(i' : ℕ) - k, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      ring
    · have h := compFin_assoc_par (R := R) i (⟨(i' : ℕ) - k, by omega⟩ : Fin (j + 1))
        (by show (i : ℕ) < (i' : ℕ) - k; omega) α β γ
      dsimp only at h
      conv_lhs =>
        rw [show i' = (⟨(i' : ℕ) - k + k, by omega⟩ : Fin (j + k + 1)) from
          Fin.ext (show (i' : ℕ) = (i' : ℕ) - k + k by omega)]
      exact h

/-! ### The identity -/

private lemma smul_sum_comm {M : Type*} [AddCommGroup M] [Module R M] {ι : Type w}
    (s : Finset ι) (c : R) (f : ι → M) : c • ∑ x ∈ s, f x = ∑ x ∈ s, c • f x :=
  map_sum (LinearMap.lsmul R M c) f s

/-- **The signed disjoint part is symmetric in `β` and `γ`, up to `(-1)^(k l)`.** -/
theorem disjointPartS_symm {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    disjointPartS (R := R) α β γ
      = ((-1 : R) ^ (k * l)) • reindex R P (by omega) (disjointPartS (R := R) α γ β) := by
  have hR : ((((-1 : R) ^ (k * l)) • reindex R P (show j + l + k + 1 = j + k + l + 1 by omega)
        (disjointPartS (R := R) α γ β)) : P (j + k + l + 1))
      = ∑ s : Fin (j + 1), ∑ t ∈ (nested (k := l) s)ᶜ,
          ((-1 : R) ^ (k * l + (t : ℕ) * k + (s : ℕ) * l))
            • reindex R P (show j + l + k + 1 = j + k + l + 1 by omega)
              (compFin (R := R) t (compFin (R := R) s α γ) β) := by
    unfold disjointPartS
    rw [map_sum]
    refine (smul_sum_comm _ _ _).trans ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_sum]
    refine (smul_sum_comm _ _ _).trans ?_
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show (reindex R P (show j + l + k + 1 = j + k + l + 1 by omega))
          (((-1 : R) ^ ((t : ℕ) * k + (s : ℕ) * l))
            • compFin (R := R) t (compFin (R := R) s α γ) β)
        = ((-1 : R) ^ ((t : ℕ) * k + (s : ℕ) * l))
          • (reindex R P (show j + l + k + 1 = j + k + l + 1 by omega))
            (compFin (R := R) t (compFin (R := R) s α γ) β) from map_smul _ _ _,
      ← mul_smul, ← pow_add, ← Nat.add_assoc]
  rw [hR]
  unfold disjointPartS
  rw [Finset.sum_congr rfl fun i _ => sum_compl_nested i _, Finset.sum_add_distrib,
    sum_before_eq_s α β γ, sum_after_eq_s α β γ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_compl_nested s _]
  exact add_comm _ _

/-- **The graded pre-Lie identity.** The associator of the signed circle product is symmetric in
its last two arguments up to the sign `(-1)^(k l)`, where `k` and `l` are the degrees of the last
two arguments. This is the identity governing the deformation complex; setting all signs to `1`
recovers `Operad.star_assoc_symm`. -/
theorem sstar_assoc_symm {j k l : ℕ} (α : P (j + 1)) (β : P (k + 1)) (γ : P (l + 1)) :
    sstar (R := R) (sstar (R := R) α β) γ
        - reindex R P (by omega) (sstar (R := R) α (sstar (R := R) β γ))
      = ((-1 : R) ^ (k * l))
          • (reindex R P (by omega) (sstar (R := R) (sstar (R := R) α γ) β)
            - reindex R P (by omega) (sstar (R := R) α (sstar (R := R) γ β))) := by
  rw [sstar_sstar_left_split, sstar_sstar_left_split α γ β, map_add, disjointPartS_symm α β γ]
  simp only [reindex_reindex, add_sub_cancel_left]

end Operad
