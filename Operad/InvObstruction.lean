/-
# Obstructions in the Lie algebra of invariant families

For a sequence `x₀, x₁, …` of odd invariant families of a graded operad, `GrOperad.Inv.sq x m`
is the coefficient `∑_{i+j=m} xᵢ ⋆ xⱼ` of `tᵐ` in the square of `∑ tᵏ xₖ`.

* **The obstruction is a cocycle.** If the coefficients of the square vanish up to order `n`,
  the bracket of `x₀` with the coefficient of order `n + 1` vanishes (`GrOperad.Inv.bracket_sq`),
  by the pre-Lie identity (`GrOperad.Inv.sum_sq_star`, `GrOperad.Inv.star_sq_comm`). A
  derivation killing the `xₖ` kills the coefficients of the square (`GrOperad.Inv.appDer_sq`).
* **Adding a term of order `n + 1`** to a sequence with `xₙ₊₁ = 0` changes the coefficient of
  order `n + 1` by the bracket of `x₀` with the term (`GrOperad.Inv.sq_update`), and no lower
  coefficient (`GrOperad.Inv.sq_update_of_le`).
* **Lifts by coefficients.** `GrOperad.Inv.LiftSeq D α n` is a lift of an odd family `α` to
  order `n`: odd families `x₀ = α, …, xₙ` killed by the derivation `D`, with the coefficients of
  the square zero up to order `n`. Its obstruction is the coefficient of order `n + 1`
  (`GrOperad.Inv.LiftSeq.obstruction`), a cocycle of the twisted differential `D + [α, -]`
  (`GrOperad.Inv.LiftSeq.twD_obstruction`), and the sequence extends by an odd family `y`
  exactly when `[α, y]` is minus the obstruction (`GrOperad.Inv.LiftSeq.sq_update_eq_zero_iff`).
-/
import Operad.InvLie
import Mathlib.Algebra.BigOperators.NatAntidiagonal

universe u v

namespace Operad

open Sym GerBV Finset

namespace GrOperad.Inv

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- Regrouping the three indices of a double sum over antidiagonals. -/
private lemma sum_antidiagonal_assoc {β : Type*} [AddCommMonoid β] (N : ℕ) (g : ℕ → ℕ → ℕ → β) :
    ∑ p ∈ antidiagonal N, ∑ q ∈ antidiagonal p.1, g q.1 q.2 p.2
      = ∑ p ∈ antidiagonal N, ∑ q ∈ antidiagonal p.2, g p.1 q.1 q.2 := by
  simp only [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ⟨⟨_, k⟩, ⟨i, j⟩⟩ => ⟨⟨i, j + k⟩, ⟨j, k⟩⟩)
    (fun ⟨⟨i, _⟩, ⟨j, k⟩⟩ => ⟨⟨i + j, k⟩, ⟨i, j⟩⟩)
  all_goals aesop (add simp [Finset.mem_sigma, Finset.mem_antidiagonal]) (add safe (by omega))

/-- **The coefficient of `tᵐ` in the square of `∑ tᵏ xₖ`**: `∑_{i+j=m} xᵢ ⋆ xⱼ`. -/
def sq (x : ℕ → Inv R Q) (m : ℕ) : Inv R Q :=
  ∑ p ∈ antidiagonal m, star R Q (x p.1) (x p.2)

lemma sq_def (x : ℕ → Inv R Q) (m : ℕ) :
    sq x m = ∑ p ∈ antidiagonal m, star R Q (x p.1) (x p.2) := rfl

/-- The coefficients of the square of a sequence of odd families are even. -/
lemma isPar_sq {x : ℕ → Inv R Q} (hx : ∀ k, IsPar true (x k)) (m : ℕ) :
    IsPar false (sq x m) := by
  intro A _ _
  show GrOperad.par (R := R) false ((sq x m).1 A) = (sq x m).1 A
  have h : ∀ p : ℕ × ℕ, IsPar false (star R Q (x p.1) (x p.2)) := fun p => by
    have := isPar_star (hx p.1) (hx p.2)
    rwa [Bool.xor_self] at this
  have hs : (sq x m).1 A = ∑ p ∈ antidiagonal m, (star R Q (x p.1) (x p.2)).1 A := by
    unfold sq
    induction antidiagonal m using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      rfl
  rw [hs, map_sum]
  exact Finset.sum_congr rfl fun p _ => h p A

/-- **The square of a sequence of odd families is associative**:
`∑_{l+k=N} (x²)_l ⋆ xₖ = ∑_{i+m=N} xᵢ ⋆ (x²)_m`, the associators of odd families being
antisymmetric in their last two arguments. -/
theorem sum_sq_star (x : ℕ → Inv R Q) (hx : ∀ k, IsPar true (x k)) (N : ℕ) :
    ∑ p ∈ antidiagonal N, star R Q (sq x p.1) (x p.2)
      = ∑ p ∈ antidiagonal N, star R Q (x p.1) (sq x p.2) := by
  have hL : ∑ p ∈ antidiagonal N, star R Q (sq x p.1) (x p.2)
      = ∑ p ∈ antidiagonal N, ∑ q ∈ antidiagonal p.2,
          star R Q (star R Q (x p.1) (x q.1)) (x q.2) := by
    rw [← sum_antidiagonal_assoc N fun i j k => star R Q (star R Q (x i) (x j)) (x k)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [sq, map_sum, LinearMap.sum_apply]
  have hR : ∑ p ∈ antidiagonal N, star R Q (x p.1) (sq x p.2)
      = ∑ p ∈ antidiagonal N, ∑ q ∈ antidiagonal p.2,
          star R Q (x p.1) (star R Q (x q.1) (x q.2)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [sq, map_sum]
  rw [hL, hR, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_involution (fun q _ => q.swap) (fun q _ => ?_) (fun q _ hq hs => hq ?_)
    (fun q hq => Finset.swap_mem_antidiagonal.2 hq) (fun _ _ => rfl)
  · have h := preLie (x p.1) (x q.1) (x q.2) (hx q.1) (hx q.2)
    rw [Bool.and_self, σ_true, neg_one_smul_inv] at h
    rw [h]
    exact neg_add_cancel _
  · have he : q.2 = q.1 := congrArg Prod.fst hs
    rw [he, assoc_odd (x p.1) (x q.1) (hx q.1), sub_self]

/-- **The obstruction is closed**: if the coefficients of the square vanish up to order `n`, the
coefficient of order `n + 1` commutes with `x₀`. -/
theorem star_sq_comm (x : ℕ → Inv R Q) (hx : ∀ k, IsPar true (x k)) (n : ℕ)
    (h : ∀ m ≤ n, sq x m = 0) :
    star R Q (x 0) (sq x (n + 1)) = star R Q (sq x (n + 1)) (x 0) := by
  have key := sum_sq_star x hx (n + 1)
  rw [Finset.sum_eq_single (n + 1, 0), Finset.sum_eq_single (0, n + 1)] at key
  · exact key.symm
  · intro p hp hne
    have hp' := Finset.mem_antidiagonal.1 hp
    have hle : p.2 ≤ n := by
      by_contra hc
      exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
    rw [h p.2 hle, map_zero]
  · intro hc
    exact absurd (Finset.mem_antidiagonal.2 (by simp)) hc
  · intro p hp hne
    have hp' := Finset.mem_antidiagonal.1 hp
    have hle : p.1 ≤ n := by
      by_contra hc
      exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
    rw [h p.1 hle, map_zero, LinearMap.zero_apply]
  · intro hc
    exact absurd (Finset.mem_antidiagonal.2 (by simp)) hc

/-- **The obstruction is a cocycle for the bracket with `x₀`.** -/
theorem bracket_sq (x : ℕ → Inv R Q) (hx : ∀ k, IsPar true (x k)) (n : ℕ)
    (h : ∀ m ≤ n, sq x m = 0) : bracket R Q (x 0) (sq x (n + 1)) = 0 := by
  rw [bracket_hom (hx 0) (isPar_sq hx (n + 1)), Bool.and_false, σ_false, one_smul,
    star_sq_comm x hx n h, sub_self]

/-- The coefficients of the square below order `n + 1` do not see the term of order `n + 1`. -/
lemma sq_update_of_le (x : ℕ → Inv R Q) (n : ℕ) (y : Inv R Q) {m : ℕ} (hm : m ≤ n) :
    sq (Function.update x (n + 1) y) m = sq x m := by
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Finset.mem_antidiagonal.1 hp
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- **The coefficient of order `n + 1` after adding a term of order `n + 1`**: the obstruction
plus the bracket of `x₀` with the new term. -/
theorem sq_update (x : ℕ → Inv R Q) (hx0 : IsPar true (x 0)) (n : ℕ) (hx : x (n + 1) = 0)
    {y : Inv R Q} (hy : IsPar true y) :
    sq (Function.update x (n + 1) y) (n + 1) = sq x (n + 1) + bracket R Q (x 0) y := by
  have hd : ∀ p ∈ antidiagonal (n + 1),
      star R Q (Function.update x (n + 1) y p.1) (Function.update x (n + 1) y p.2)
        = star R Q (x p.1) (x p.2)
          + ((if p = (0, n + 1) then star R Q (x 0) y else 0)
            + (if p = (n + 1, 0) then star R Q y (x 0) else 0)) := by
    intro p hp
    have hp' := Finset.mem_antidiagonal.1 hp
    obtain ⟨i, j⟩ := p
    simp only at hp'
    by_cases hi : i = n + 1
    · obtain rfl : j = 0 := by omega
      subst hi
      rw [Function.update_self, Function.update_of_ne (by omega), hx, map_zero,
        LinearMap.zero_apply, if_neg (by simp), if_pos rfl, zero_add, zero_add]
    · by_cases hj : j = n + 1
      · obtain rfl : i = 0 := by omega
        subst hj
        rw [Function.update_of_ne (by omega), Function.update_self, hx, map_zero,
          if_pos rfl, if_neg (by simp), add_zero, zero_add]
      · rw [Function.update_of_ne hi, Function.update_of_ne hj, if_neg, if_neg, add_zero,
          add_zero]
        · intro hc
          exact hi (congrArg Prod.fst hc)
        · intro hc
          exact hj (congrArg Prod.snd hc)
  rw [sq, Finset.sum_congr rfl hd, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' , Finset.sum_ite_eq', if_pos (Finset.mem_antidiagonal.2 (by simp)),
    if_pos (Finset.mem_antidiagonal.2 (by simp)), bracket_hom hx0 hy, Bool.and_self, σ_true,
    neg_one_smul_inv, sub_neg_eq_add]
  rfl

/-- **A sequence extends by one order exactly when the obstruction is minus the bracket of `x₀`
with the new term.** -/
theorem sq_update_eq_zero_iff (x : ℕ → Inv R Q) (hx0 : IsPar true (x 0)) (n : ℕ)
    (hx : x (n + 1) = 0) {y : Inv R Q} (hy : IsPar true y) :
    sq (Function.update x (n + 1) y) (n + 1) = 0 ↔ bracket R Q (x 0) y = -sq x (n + 1) := by
  rw [sq_update x hx0 n hx hy, add_comm, add_eq_zero_iff_eq_neg]

/-- **A derivation kills the coefficients of the square of a sequence of odd families it
kills.** -/
theorem appDer_sq {e : Bool} (D : GrDer (GrOperadHom.id R Q) e) (x : ℕ → Inv R Q)
    (hx : ∀ k, IsPar true (x k)) (hD : ∀ k, appDer D (x k) = 0) (m : ℕ) :
    appDer D (sq x m) = 0 := by
  rw [sq, map_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [appDer_star D (hx p.1), hD, hD, map_zero, LinearMap.zero_apply, map_zero, smul_zero,
    add_zero]

/-- **A lift of an odd family `α` to order `n`, by its coefficients**: odd families
`x₀ = α, x₁, …, xₙ` killed by the derivation `D`, with `∑_{i+j=m} xᵢ ⋆ xⱼ = 0` for `m ≤ n`;
the later coefficients are zero. -/
structure LiftSeq (D : GrDer (GrOperadHom.id R Q) true) (α : Inv R Q) (n : ℕ) where
  /-- The coefficients. -/
  x : ℕ → Inv R Q
  x_zero : x 0 = α
  isPar : ∀ k, IsPar true (x k)
  closed : ∀ k, appDer D (x k) = 0
  sq_eq : ∀ m ≤ n, sq x m = 0
  x_succ : x (n + 1) = 0

namespace LiftSeq

variable {D : GrDer (GrOperadHom.id R Q) true} {α : Inv R Q} {n : ℕ}

/-- **The obstruction** to extending a lift to order `n` by one order:
`∑_{i+j=n+1, i,j ≥ 1} xᵢ ⋆ xⱼ`. -/
def obstruction (L : LiftSeq D α n) : Inv R Q := sq L.x (n + 1)

/-- **The obstruction is a cocycle of the twisted differential** `D + [α, -]`. -/
theorem twD_obstruction (L : LiftSeq D α n) : twD D α L.obstruction = 0 := by
  have h1 : appDer D L.obstruction = 0 := appDer_sq D L.x L.isPar L.closed (n + 1)
  have h2 : bracket R Q (L.x 0) L.obstruction = 0 := bracket_sq L.x L.isPar n L.sq_eq
  rw [L.x_zero] at h2
  rw [twD_apply, h1, h2, add_zero]

/-- **A lift extends by one order exactly when its obstruction is minus the bracket of `α` with
the new coefficient**: for an odd family `y`, the coefficient of order `n + 1` of the square of
`x₀, …, xₙ, y` vanishes exactly when `[α, y] = -obstruction`. -/
theorem sq_update_eq_zero_iff (L : LiftSeq D α n) {y : Inv R Q} (hy : IsPar true y) :
    sq (Function.update L.x (n + 1) y) (n + 1) = 0 ↔ bracket R Q α y = -L.obstruction := by
  have h := GrOperad.Inv.sq_update_eq_zero_iff L.x (L.isPar 0) n L.x_succ hy
  rw [L.x_zero] at h
  exact h

/-- The lower coefficients of the square are unchanged by the new coefficient. -/
theorem sq_update_of_le (L : LiftSeq D α n) (y : Inv R Q) {m : ℕ} (hm : m ≤ n) :
    sq (Function.update L.x (n + 1) y) m = 0 :=
  (GrOperad.Inv.sq_update_of_le L.x n y hm).trans (L.sq_eq m hm)

end LiftSeq

end GrOperad.Inv

end Operad
