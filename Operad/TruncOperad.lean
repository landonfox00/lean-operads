/-
# Power series and truncated polynomials with coefficients in a graded operad

For a graded operad `Q`, the power series `Q[[t]]` (`PowOp`) are the sequences of operations,
with the composition by the Cauchy product (`PowOp.compP`, `PowOp.coef_compP`): a graded operad
(`PowOp.instGrOperad`). The series without terms of degree at most `n` are an ideal
(`PowOp.tIdeal`), and **the truncated polynomials** `Q[t]/tⁿ⁺¹` are the quotient (`TruncOp`).

* **Coefficients.** `TruncOp.coef` is the coefficient of `tᵏ`, zero for `k > n`. A truncated
  polynomial is determined by its coefficients (`TruncOp.ext`), which commute with the parity
  projections and the relabellings (`TruncOp.coef_par`, `TruncOp.coef_map`), and the
  coefficients of a composite are the Cauchy product of the coefficients (`TruncOp.coef_comp`).
* **Truncation.** `TruncOp.trunc` is the morphism `Q[t]/tⁿ⁺² → Q[t]/tⁿ⁺¹`, and
  `TruncOp.constHom` is the constant term `Q[t]/tⁿ⁺¹ → Q`. The truncation has a linear section
  (`TruncOp.sec`, `TruncOp.trunc_sec`), and `TruncOp.top` is the monomial of degree `n + 1`.
* **The differential.** Over a dg operad, the differential coefficient by coefficient
  (`TruncOp.dT`, `TruncOp.coef_dT`) is an odd derivation (`TruncOp.dDer`).

`sum_antidiagonal_assoc` and `sum_antidiagonal_swap₂₃` regroup sums over antidiagonals.
-/
import Operad.GrPresentation
import Operad.GrDerivation
import Mathlib.Algebra.BigOperators.NatAntidiagonal

universe u v

namespace Operad

open Sym GerBV Finset

/-! ## Regrouping sums over antidiagonals -/

section Reindex

variable {β : Type*} [AddCommMonoid β]

/-- Regrouping the three indices of a double sum over antidiagonals. -/
lemma sum_antidiagonal_assoc (N : ℕ) (g : ℕ → ℕ → ℕ → β) :
    ∑ p ∈ antidiagonal N, ∑ q ∈ antidiagonal p.1, g q.1 q.2 p.2
      = ∑ p ∈ antidiagonal N, ∑ q ∈ antidiagonal p.2, g p.1 q.1 q.2 := by
  simp only [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ⟨⟨_, k⟩, ⟨i, j⟩⟩ => ⟨⟨i, j + k⟩, ⟨j, k⟩⟩)
    (fun ⟨⟨i, _⟩, ⟨j, k⟩⟩ => ⟨⟨i + j, k⟩, ⟨i, j⟩⟩)
  all_goals aesop (add simp [Finset.mem_sigma, Finset.mem_antidiagonal]) (add safe (by omega))

/-- Exchanging the last two indices of a double sum over antidiagonals. -/
lemma sum_antidiagonal_swap₂₃ (N : ℕ) (g : ℕ → ℕ → ℕ → β) :
    ∑ p ∈ antidiagonal N, ∑ q ∈ antidiagonal p.1, g q.1 q.2 p.2
      = ∑ p ∈ antidiagonal N, ∑ q ∈ antidiagonal p.1, g q.1 p.2 q.2 := by
  simp only [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ⟨⟨_, k⟩, ⟨i, j⟩⟩ => ⟨⟨i + k, j⟩, ⟨i, k⟩⟩)
    (fun ⟨⟨_, k⟩, ⟨i, j⟩⟩ => ⟨⟨i + k, j⟩, ⟨i, k⟩⟩)
  all_goals aesop (add simp [Finset.mem_sigma, Finset.mem_antidiagonal]) (add safe (by omega))

end Reindex

/-! ## The operad of power series -/

/-- **Power series with coefficients in `Q`**: sequences of operations, `∑ₖ tᵏ xₖ`. -/
@[nolint unusedArguments]
def PowOp (R : Type u) [CommRing R] (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (A : Type) [Fintype A] [DecidableEq A] : Type v := ℕ → Q A

namespace PowOp

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)]

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (PowOp R Q A) :=
  inferInstanceAs (AddCommGroup (ℕ → Q A))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (PowOp R Q A) :=
  inferInstanceAs (Module R (ℕ → Q A))

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The coefficient of `tᵏ`.** -/
def coef (k : ℕ) : PowOp R Q A →ₗ[R] Q A := LinearMap.proj k

@[ext] lemma ext {x y : PowOp R Q A} (h : ∀ k, coef k x = coef k y) : x = y := funext h

@[simp] lemma coef_add (k : ℕ) (x y : PowOp R Q A) : coef k (x + y) = coef k x + coef k y := rfl

@[simp] lemma coef_smul (k : ℕ) (c : R) (x : PowOp R Q A) : coef k (c • x) = c • coef k x := rfl

@[simp] lemma coef_zero (k : ℕ) : coef k (0 : PowOp R Q A) = 0 := rfl

variable [GrOperad R Q]

/-- The parity projections, coefficient by coefficient. -/
def parP (b : Bool) : PowOp R Q A →ₗ[R] PowOp R Q A :=
  LinearMap.pi fun k => GrOperad.par (R := R) b ∘ₗ coef k

/-- Relabelling, coefficient by coefficient. -/
def mapP (e : A ≃ B) : PowOp R Q A →ₗ[R] PowOp R Q B :=
  LinearMap.pi fun k => GrOperad.map (R := R) e ∘ₗ coef k

variable (R Q) in
/-- The unit: the constant series `1`. -/
def oneP : PowOp R Q Unit := fun k => if k = 0 then GrOperad.one (R := R) else 0

/-- **The Cauchy product of compositions**: `(x ∘ᵢ y)ₖ = ∑_{a+b=k} xₐ ∘ᵢ y_b`. -/
def compP (i : A) : PowOp R Q A →ₗ[R] PowOp R Q B →ₗ[R] PowOp R Q (Without A i ⊕ B) :=
  LinearMap.mk₂ R (fun x y k => ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (x p.1) (y p.2))
    (fun x x' y => funext fun k => by
      show ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (x p.1 + x' p.1) (y p.2)
        = ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (x p.1) (y p.2)
          + ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (x' p.1) (y p.2)
      simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib])
    (fun c x y => funext fun k => by
      show ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (c • x p.1) (y p.2)
        = c • ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (x p.1) (y p.2)
      simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum])
    (fun x y y' => funext fun k => by
      show ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (x p.1) (y p.2 + y' p.2)
        = ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (x p.1) (y p.2)
          + ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (x p.1) (y' p.2)
      simp only [map_add, Finset.sum_add_distrib])
    (fun c x y => funext fun k => by
      show ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (x p.1) (c • y p.2)
        = c • ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (x p.1) (y p.2)
      simp only [map_smul, Finset.smul_sum])

@[simp] lemma coef_parP (b : Bool) (x : PowOp R Q A) (k : ℕ) :
    coef k (parP b x) = GrOperad.par (R := R) b (coef k x) := rfl

@[simp] lemma coef_mapP (e : A ≃ B) (x : PowOp R Q A) (k : ℕ) :
    coef k (mapP e x) = GrOperad.map (R := R) e (coef k x) := rfl

lemma coef_oneP (k : ℕ) :
    coef k (oneP R Q) = if k = 0 then GrOperad.one (R := R) else 0 := rfl

lemma coef_compP (i : A) (x : PowOp R Q A) (y : PowOp R Q B) (k : ℕ) :
    coef k (compP i x y)
      = ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (coef p.1 x) (coef p.2 y) := rfl

/-- **Power series with coefficients in a graded operad form a graded operad.** -/
instance instGrOperad : GrOperad R (PowOp R Q) where
  par b := parP b
  par_add x := ext fun k => GrOperad.par_add (R := R) (coef k x)
  par_par b b' x := ext fun k => by
    show GrOperad.par (R := R) b (GrOperad.par (R := R) b' (coef k x)) = _
    rw [GrOperad.par_par]
    split_ifs <;> rfl
  map e := mapP e
  map_refl x := ext fun k => GrOperad.map_refl (R := R) (coef k x)
  map_trans e f x := ext fun k => GrOperad.map_trans (R := R) e f (coef k x)
  map_par e b x := ext fun k => GrOperad.map_par (R := R) e b (coef k x)
  one := oneP R Q
  par_one := ext fun k => by
    show GrOperad.par (R := R) false (coef k (oneP R Q)) = _
    rw [coef_oneP]
    split_ifs
    · exact GrOperad.par_one
    · exact map_zero _
  comp i := compP i
  comp_par i p q x y := ext fun k => by
    show GrOperad.par (R := R) (xor p q) (coef k (compP i (parP p x) (parP q y))) = _
    rw [coef_compP, map_sum]
    exact Finset.sum_congr rfl fun a _ => GrOperad.comp_par (R := R) i p q _ _
  map_comp σ τ i x y := ext fun k => by
    show GrOperad.map (R := R) (compEquiv σ τ i) (coef k (compP i x y))
      = coef k (compP (σ i) (mapP σ x) (mapP τ y))
    rw [coef_compP, coef_compP, map_sum]
    exact Finset.sum_congr rfl fun a _ => GrOperad.map_comp (R := R) σ τ i _ _
  comp_one i x := ext fun k => by
    show GrOperad.map (R := R) (rightUnitEquiv i) (coef k (compP i x (oneP R Q))) = coef k x
    rw [coef_compP, Finset.sum_eq_single (k, 0)]
    · rw [coef_oneP, if_pos rfl]
      exact GrOperad.comp_one (R := R) i _
    · intro p hp hne
      have hp' := Finset.mem_antidiagonal.1 hp
      rw [coef_oneP, if_neg, map_zero]
      intro h0
      exact hne (Prod.ext (by simp only; omega) h0)
    · intro hc
      exact absurd (Finset.mem_antidiagonal.2 (by simp)) hc
  one_comp y := ext fun k => by
    show GrOperad.map (R := R) (leftUnitEquiv _) (coef k (compP () (oneP R Q) y)) = coef k y
    rw [coef_compP, Finset.sum_eq_single (0, k)]
    · rw [coef_oneP, if_pos rfl]
      exact GrOperad.one_comp (R := R) _
    · intro p hp hne
      have hp' := Finset.mem_antidiagonal.1 hp
      rw [coef_oneP, if_neg, map_zero, LinearMap.zero_apply]
      intro h0
      exact hne (Prod.ext h0 (by simp only; omega))
    · intro hc
      exact absurd (Finset.mem_antidiagonal.2 (by simp)) hc
  comp_assoc_seq i j x y z := ext fun k => by
    show GrOperad.map (R := R) (seqEquiv i j _)
        (coef k (compP (Sum.inr j) (compP i x y) z)) = coef k (compP i x (compP j y z))
    rw [coef_compP, coef_compP, map_sum]
    have hL : ∀ p ∈ antidiagonal k, GrOperad.map (R := R) (seqEquiv i j _)
        (GrOperad.comp (R := R) (Sum.inr j) (coef p.1 (compP i x y)) (coef p.2 z))
        = ∑ q ∈ antidiagonal p.1, GrOperad.comp (R := R) i (coef q.1 x)
            (GrOperad.comp (R := R) j (coef q.2 y) (coef p.2 z)) := fun p _ => by
      rw [coef_compP, map_sum, LinearMap.sum_apply, map_sum]
      exact Finset.sum_congr rfl fun q _ => GrOperad.comp_assoc_seq (R := R) i j _ _ _
    have hR : ∀ p ∈ antidiagonal k,
        GrOperad.comp (R := R) i (coef p.1 x) (coef p.2 (compP j y z))
        = ∑ q ∈ antidiagonal p.2, GrOperad.comp (R := R) i (coef p.1 x)
            (GrOperad.comp (R := R) j (coef q.1 y) (coef q.2 z)) := fun p _ => by
      rw [coef_compP, map_sum]
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
    exact sum_antidiagonal_assoc k fun a b c => GrOperad.comp (R := R) i (coef a x)
      (GrOperad.comp (R := R) j (coef b y) (coef c z))
  comp_assoc_par {A B D} _ _ _ _ _ _ {i k'} hik x {q r} {y z} hy hz := ext fun k => by
    have hyk : ∀ b, GrOperad.par (R := R) q (coef b y) = coef b y := fun b =>
      congrArg (coef b) hy
    have hzk : ∀ c, GrOperad.par (R := R) r (coef c z) = coef c z := fun c =>
      congrArg (coef c) hz
    show GrOperad.map (R := R) (parEquiv hik B D)
        (coef k (compP (Sum.inl ⟨k', Ne.symm hik⟩) (compP i x y) z))
      = σ R (q && r) • coef k (compP (Sum.inl ⟨i, hik⟩) (compP k' x z) y)
    rw [coef_compP, coef_compP, map_sum, Finset.smul_sum]
    have hL : ∀ p ∈ antidiagonal k, GrOperad.map (R := R) (parEquiv hik B D)
        (GrOperad.comp (R := R) (Sum.inl ⟨k', Ne.symm hik⟩) (coef p.1 (compP i x y))
          (coef p.2 z))
        = ∑ a ∈ antidiagonal p.1, σ R (q && r) • GrOperad.comp (R := R) (Sum.inl ⟨i, hik⟩)
            (GrOperad.comp (R := R) k' (coef a.1 x) (coef p.2 z)) (coef a.2 y) := fun p _ => by
      rw [coef_compP, map_sum, LinearMap.sum_apply, map_sum]
      exact Finset.sum_congr rfl fun a _ =>
        GrOperad.comp_assoc_par (R := R) hik _ (hyk a.2) (hzk p.2)
    have hR : ∀ p ∈ antidiagonal k, σ R (q && r) • GrOperad.comp (R := R) (Sum.inl ⟨i, hik⟩)
        (coef p.1 (compP k' x z)) (coef p.2 y)
        = ∑ a ∈ antidiagonal p.1, σ R (q && r) • GrOperad.comp (R := R) (Sum.inl ⟨i, hik⟩)
            (GrOperad.comp (R := R) k' (coef a.1 x) (coef a.2 z)) (coef p.2 y) := fun p _ => by
      rw [coef_compP, map_sum, LinearMap.sum_apply, Finset.smul_sum]
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
    exact sum_antidiagonal_swap₂₃ k fun a b c => σ R (q && r) •
      GrOperad.comp (R := R) (Sum.inl ⟨i, hik⟩)
        (GrOperad.comp (R := R) k' (coef a x) (coef c z)) (coef b y)

end PowOp

/-! ## Truncated polynomials -/

namespace PowOp

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

variable (R Q) in
/-- **The ideal of the power series divisible by `tⁿ⁺¹`.** -/
def tIdeal (n : ℕ) : GrOperadIdeal R (PowOp R Q) where
  sub A _ _ :=
    { carrier := {x | ∀ k ≤ n, coef k x = 0}
      add_mem' := fun {x y} hx hy k hk => by rw [coef_add, hx k hk, hy k hk, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c x hx k hk => by rw [coef_smul, hx k hk, smul_zero] }
  par_mem := by
    intro A _ _ b x hx k hk
    show GrOperad.par (R := R) b (coef k x) = 0
    rw [hx k hk, map_zero]
  map_mem := by
    intro A B _ _ _ _ e x hx k hk
    show GrOperad.map (R := R) e (coef k x) = 0
    rw [hx k hk, map_zero]
  comp_mem_left := by
    intro A B _ _ _ _ i x y hx k hk
    show coef k (compP i x y) = 0
    rw [coef_compP]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Finset.mem_antidiagonal.1 hp
    rw [hx p.1 (by omega), map_zero, LinearMap.zero_apply]
  comp_mem_right := by
    intro A B _ _ _ _ i x y hy k hk
    show coef k (compP i x y) = 0
    rw [coef_compP]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Finset.mem_antidiagonal.1 hp
    rw [hy p.2 (by omega), map_zero]

lemma mem_tIdeal {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {x : PowOp R Q A} :
    x ∈ (tIdeal R Q n).sub A ↔ ∀ k ≤ n, coef k x = 0 := Iff.rfl

end PowOp

/-- **Truncated polynomials** `Q[t]/tⁿ⁺¹` with coefficients in a graded operad: the power series
modulo `tⁿ⁺¹`, a graded operad. -/
abbrev TruncOp (R : Type u) [CommRing R]
    (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] (n : ℕ) :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type v :=
  (PowOp.tIdeal R Q n).Quot

namespace TruncOp

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {n : ℕ}

variable (R Q) in
/-- **The polynomial with given coefficients**, modulo `tⁿ⁺¹`. -/
def ofCoef (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    PowOp R Q A →ₗ[R] TruncOp R Q n A :=
  (PowOp.tIdeal R Q n).proj A

lemma ofCoef_surjective : Function.Surjective (ofCoef R Q n A) :=
  (PowOp.tIdeal R Q n).proj_surjective A

variable (R Q) in
/-- **The coefficient of `tᵏ`** of a truncated polynomial; zero for `k > n`. -/
def coef (n k : ℕ) (A : Type) [Fintype A] [DecidableEq A] : TruncOp R Q n A →ₗ[R] Q A :=
  Submodule.liftQ _ (if k ≤ n then PowOp.coef k else 0) fun x hx => by
    rw [LinearMap.mem_ker]
    split_ifs with h
    · exact hx k h
    · rfl

lemma coef_ofCoef {k : ℕ} (hk : k ≤ n) (x : PowOp R Q A) :
    coef R Q n k A (ofCoef R Q n A x) = PowOp.coef k x := by
  show (if k ≤ n then PowOp.coef k else 0) x = _
  rw [if_pos hk]

lemma coef_of_lt {k : ℕ} (hk : n < k) (z : TruncOp R Q n A) : coef R Q n k A z = 0 := by
  obtain ⟨x, rfl⟩ := ofCoef_surjective z
  show (if k ≤ n then PowOp.coef k else 0) x = _
  rw [if_neg (by omega)]
  rfl

/-- **A truncated polynomial is determined by its coefficients.** -/
lemma ext {z z' : TruncOp R Q n A} (h : ∀ k ≤ n, coef R Q n k A z = coef R Q n k A z') :
    z = z' := by
  obtain ⟨x, rfl⟩ := ofCoef_surjective z
  obtain ⟨x', rfl⟩ := ofCoef_surjective z'
  rw [← sub_eq_zero, ← map_sub]
  refine ((PowOp.tIdeal R Q n).proj_eq_zero_iff _).2 fun k hk => ?_
  have hk' := h k hk
  rw [coef_ofCoef hk, coef_ofCoef hk] at hk'
  rw [map_sub, hk', sub_self]

lemma coef_par {k : ℕ} (b : Bool) (z : TruncOp R Q n A) :
    coef R Q n k A (GrOperad.par (R := R) b z) = GrOperad.par (R := R) b (coef R Q n k A z) := by
  obtain ⟨x, rfl⟩ := ofCoef_surjective z
  by_cases hk : k ≤ n
  · have h := (PowOp.tIdeal R Q n).projHom.app_par b x
    rw [GrOperadIdeal.projHom_app, GrOperadIdeal.projHom_app] at h
    show coef R Q n k A (GrOperad.par (R := R) b ((PowOp.tIdeal R Q n).proj A x)) = _
    rw [← h]
    exact (coef_ofCoef hk _).trans (congrArg _ (coef_ofCoef hk x).symm)
  · rw [coef_of_lt (by omega), coef_of_lt (by omega), map_zero]

lemma coef_map {k : ℕ} (e : A ≃ B) (z : TruncOp R Q n A) :
    coef R Q n k B (GrOperad.map (R := R) e z) = GrOperad.map (R := R) e (coef R Q n k A z) := by
  obtain ⟨x, rfl⟩ := ofCoef_surjective z
  by_cases hk : k ≤ n
  · have h := (PowOp.tIdeal R Q n).projHom.app_map e x
    rw [GrOperadIdeal.projHom_app, GrOperadIdeal.projHom_app] at h
    show coef R Q n k B (GrOperad.map (R := R) e ((PowOp.tIdeal R Q n).proj A x)) = _
    rw [← h]
    exact (coef_ofCoef hk _).trans (congrArg _ (coef_ofCoef hk x).symm)
  · rw [coef_of_lt (by omega), coef_of_lt (by omega), map_zero]

lemma coef_one {k : ℕ} (hk : k ≤ n) :
    coef R Q n k Unit (GrOperad.one (R := R)) = if k = 0 then GrOperad.one (R := R) else 0 := by
  have h := (PowOp.tIdeal R Q n).projHom.app_one
  rw [GrOperadIdeal.projHom_app] at h
  rw [← h]
  exact coef_ofCoef hk _

/-- **The coefficients of a composite are the Cauchy product of the coefficients.** -/
lemma coef_comp {k : ℕ} (hk : k ≤ n) (i : A) (z : TruncOp R Q n A) (w : TruncOp R Q n B) :
    coef R Q n k _ (GrOperad.comp (R := R) i z w)
      = ∑ p ∈ Finset.antidiagonal k,
          GrOperad.comp (R := R) i (coef R Q n p.1 A z) (coef R Q n p.2 B w) := by
  obtain ⟨x, rfl⟩ := ofCoef_surjective z
  obtain ⟨y, rfl⟩ := ofCoef_surjective w
  have h := (PowOp.tIdeal R Q n).projHom.app_comp i x y
  rw [GrOperadIdeal.projHom_app, GrOperadIdeal.projHom_app, GrOperadIdeal.projHom_app] at h
  show coef R Q n k _ (GrOperad.comp (R := R) i ((PowOp.tIdeal R Q n).proj A x)
    ((PowOp.tIdeal R Q n).proj B y)) = _
  rw [← h]
  refine (coef_ofCoef hk _).trans ((PowOp.coef_compP i x y k).trans ?_)
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Finset.mem_antidiagonal.1 hp
  rw [coef_ofCoef (by omega), coef_ofCoef (by omega)]

variable (R Q) in
/-- **The truncation** `Q[t]/tⁿ⁺² → Q[t]/tⁿ⁺¹`, a morphism of graded operads. -/
def trunc (n : ℕ) : GrOperadHom R (TruncOp R Q (n + 1)) (TruncOp R Q n) :=
  (PowOp.tIdeal R Q (n + 1)).liftHom (PowOp.tIdeal R Q n).projHom fun A _ _ x hx =>
    ((PowOp.tIdeal R Q n).proj_eq_zero_iff x).2 fun k hk => hx k (by omega)

lemma trunc_ofCoef (x : PowOp R Q A) :
    (trunc R Q n).app A (ofCoef R Q (n + 1) A x) = ofCoef R Q n A x := rfl

lemma coef_trunc {k : ℕ} (hk : k ≤ n) (z : TruncOp R Q (n + 1) A) :
    coef R Q n k A ((trunc R Q n).app A z) = coef R Q (n + 1) k A z := by
  obtain ⟨x, rfl⟩ := ofCoef_surjective z
  rw [trunc_ofCoef, coef_ofCoef hk, coef_ofCoef (by omega)]

variable (R Q) in
/-- **The constant term**, a morphism of graded operads `Q[t]/tⁿ⁺¹ → Q`. -/
def constHom (n : ℕ) : GrOperadHom R (TruncOp R Q n) Q where
  app A _ _ := coef R Q n 0 A
  app_par b z := coef_par b z
  app_map e z := coef_map e z
  app_one := by
    rw [coef_one (Nat.zero_le n), if_pos rfl]
  app_comp i z w := by
    rw [coef_comp (Nat.zero_le n), Finset.Nat.antidiagonal_zero, Finset.sum_singleton]

variable (R Q) in
/-- **The linear section of the truncation**: the polynomial with the same coefficients and no
term of degree `n + 1`. -/
def sec (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    TruncOp R Q n A →ₗ[R] TruncOp R Q (n + 1) A :=
  Submodule.liftQ _
    (ofCoef R Q (n + 1) A ∘ₗ LinearMap.pi fun k => if k ≤ n then PowOp.coef k else 0)
    fun x hx => by
      rw [LinearMap.mem_ker]
      refine ((PowOp.tIdeal R Q (n + 1)).proj_eq_zero_iff _).2 fun k _ => ?_
      show (if k ≤ n then PowOp.coef k else 0) x = 0
      split_ifs with h
      · exact hx k h
      · rfl

lemma coef_sec {k : ℕ} (hk : k ≤ n) (z : TruncOp R Q n A) :
    coef R Q (n + 1) k A (sec R Q n A z) = coef R Q n k A z := by
  obtain ⟨x, rfl⟩ := ofCoef_surjective z
  rw [coef_ofCoef hk]
  refine (coef_ofCoef (Nat.le_succ_of_le hk) _).trans ?_
  show (if k ≤ n then PowOp.coef k else 0) x = _
  rw [if_pos hk]

lemma coef_sec_succ (z : TruncOp R Q n A) :
    coef R Q (n + 1) (n + 1) A (sec R Q n A z) = 0 := by
  obtain ⟨x, rfl⟩ := ofCoef_surjective z
  refine (coef_ofCoef le_rfl _).trans ?_
  show (if n + 1 ≤ n then PowOp.coef (n + 1) else 0) x = _
  rw [if_neg (by omega)]
  rfl

/-- The section is a section of the truncation. -/
lemma trunc_sec (z : TruncOp R Q n A) : (trunc R Q n).app A (sec R Q n A z) = z :=
  ext fun k hk => by rw [coef_trunc hk, coef_sec hk]

lemma sec_par (b : Bool) (z : TruncOp R Q n A) :
    sec R Q n A (GrOperad.par (R := R) b z) = GrOperad.par (R := R) b (sec R Q n A z) :=
  ext fun k _ => by
    by_cases h : k ≤ n
    · rw [coef_sec h, coef_par, coef_par, coef_sec h]
    · obtain rfl : k = n + 1 := by omega
      rw [coef_sec_succ, coef_par, coef_sec_succ, map_zero]

lemma sec_map (e : A ≃ B) (z : TruncOp R Q n A) :
    sec R Q n B (GrOperad.map (R := R) e z) = GrOperad.map (R := R) e (sec R Q n A z) :=
  ext fun k _ => by
    by_cases h : k ≤ n
    · rw [coef_sec h, coef_map, coef_map, coef_sec h]
    · obtain rfl : k = n + 1 := by omega
      rw [coef_sec_succ, coef_map, coef_sec_succ, map_zero]

variable (R Q) in
/-- **The monomial of degree `n + 1`** with a given coefficient, in `Q[t]/tⁿ⁺²`. -/
def top (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] : Q A →ₗ[R] TruncOp R Q (n + 1) A :=
  ofCoef R Q (n + 1) A ∘ₗ LinearMap.pi fun k => if k = n + 1 then LinearMap.id else 0

lemma coef_top_self (q : Q A) : coef R Q (n + 1) (n + 1) A (top R Q n A q) = q := by
  refine (coef_ofCoef le_rfl _).trans ?_
  show (if n + 1 = n + 1 then (LinearMap.id : Q A →ₗ[R] Q A) else 0) q = q
  rw [if_pos rfl]
  rfl

lemma coef_top_of_ne {k : ℕ} (hk : k ≠ n + 1) (q : Q A) :
    coef R Q (n + 1) k A (top R Q n A q) = 0 := by
  by_cases h : k ≤ n + 1
  · refine (coef_ofCoef h _).trans ?_
    show (if k = n + 1 then (LinearMap.id : Q A →ₗ[R] Q A) else 0) q = 0
    rw [if_neg hk]
    rfl
  · exact coef_of_lt (by omega) _

/-- The truncation kills the monomials of top degree. -/
lemma trunc_top (q : Q A) : (trunc R Q n).app A (top R Q n A q) = 0 :=
  ext fun k hk => by rw [coef_trunc hk, coef_top_of_ne (by omega), map_zero]

lemma top_par (b : Bool) (q : Q A) :
    top R Q n A (GrOperad.par (R := R) b q) = GrOperad.par (R := R) b (top R Q n A q) :=
  ext fun k _ => by
    by_cases h : k = n + 1
    · subst h
      rw [coef_top_self, coef_par, coef_top_self]
    · rw [coef_top_of_ne h, coef_par, coef_top_of_ne h, map_zero]

lemma top_map (e : A ≃ B) (q : Q A) :
    top R Q n B (GrOperad.map (R := R) e q) = GrOperad.map (R := R) e (top R Q n A q) :=
  ext fun k _ => by
    by_cases h : k = n + 1
    · subst h
      rw [coef_top_self, coef_map, coef_top_self]
    · rw [coef_top_of_ne h, coef_map, coef_top_of_ne h, map_zero]

end TruncOp

/-! ## The differential of truncated polynomials over a dg operad -/

namespace TruncOp

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [DGOperad R Q]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {n : ℕ}

variable (R Q) in
/-- **The differential of `Q[t]/tⁿ⁺¹`**, coefficient by coefficient. -/
def dT (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] : TruncOp R Q n A →ₗ[R] TruncOp R Q n A :=
  Submodule.mapQ _ _ (LinearMap.pi fun k => DGOperad.d (R := R) ∘ₗ PowOp.coef k)
    fun x hx k hk => by
      show DGOperad.d (R := R) (PowOp.coef k x) = 0
      rw [hx k hk, map_zero]

lemma coef_dT (k : ℕ) (z : TruncOp R Q n A) :
    coef R Q n k A (dT R Q n A z) = DGOperad.d (R := R) (coef R Q n k A z) := by
  obtain ⟨x, rfl⟩ := ofCoef_surjective z
  by_cases hk : k ≤ n
  · exact (coef_ofCoef hk _).trans (congrArg _ (coef_ofCoef hk x).symm)
  · rw [coef_of_lt (by omega), coef_of_lt (by omega), map_zero]

variable (R Q) in
/-- **The differential of `Q[t]/tⁿ⁺¹` is an odd derivation.** -/
def dDer (n : ℕ) : GrDer (GrOperadHom.id R (TruncOp R Q n)) true where
  app A _ _ := dT R Q n A
  app_par c z := ext fun k _ => by
    rw [coef_dT, coef_par, coef_par, coef_dT, DGOperad.d_par, Bool.xor_true]
  app_map e z := ext fun k _ => by
    rw [coef_dT, coef_map, coef_map, coef_dT, DGOperad.map_d]
  app_one := ext fun k hk => by
    rw [coef_dT, coef_one hk, map_zero]
    split_ifs
    · exact DGOperad.d_one
    · exact map_zero _
  app_comp i z w := ext fun k hk => by
    rw [coef_dT, coef_comp hk, map_sum, map_add, coef_comp hk, coef_comp hk,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [DGOperad.d_comp, coef_dT, coef_dT, GrOperadHom.id_app, GrOperadHom.id_app,
      GrOperad.tw_true, (coef R Q n p.1 _).map_sub, coef_par, coef_par]

lemma dT_sec (z : TruncOp R Q n A) :
    dT R Q (n + 1) A (sec R Q n A z) = sec R Q n A (dT R Q n A z) :=
  ext fun k _ => by
    by_cases h : k ≤ n
    · rw [coef_dT, coef_sec h, coef_sec h, coef_dT]
    · obtain rfl : k = n + 1 := by omega
      rw [coef_dT, coef_sec_succ, coef_sec_succ, map_zero]

lemma dT_top (q : Q A) :
    dT R Q (n + 1) A (top R Q n A q) = top R Q n A (DGOperad.d (R := R) q) :=
  ext fun k _ => by
    by_cases h : k = n + 1
    · subst h
      rw [coef_dT, coef_top_self, coef_top_self]
    · rw [coef_dT, coef_top_of_ne h, coef_top_of_ne h, map_zero]

end TruncOp

end Operad
