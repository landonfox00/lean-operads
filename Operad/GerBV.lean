/-
# Gerstenhaber and Batalin–Vilkovisky algebras

On a super module `(V, ε)` a homogeneous element of parity `p : Bool` satisfies `ε x = σ p • x`,
with `σ false = 1` and `σ true = -1` (`GerBV.IsPar`). For a product `μ` and an odd operator `Δ`,
the **deviation** of `Δ` from being a derivation is
`⟨x, y⟩ = Δ (x y) - (Δ x) y - σ|x| x (Δ y)` (`GerBV.dev`), and the **derived bracket** is
`[x, y] = σ|x| ⟨x, y⟩` (`GerBV.bracket`).

A **BV algebra** (`GerBV.IsBV`) is a graded commutative product with an odd operator `Δ` with
`Δ² = 0` which is of order at most two: `⟨x, -⟩` is a graded derivation of the product.

**Koszul's theorem**: the derived bracket of a BV algebra is a **Gerstenhaber bracket**:
* graded antisymmetric, `[x, y] = -σ((|x| + 1)(|y| + 1)) [y, x]` (`GerBV.bracket_antisymm`);
* a graded derivation of the product (the Poisson rule, `GerBV.bracket_mul_right`);
* satisfying the graded Jacobi identity (`GerBV.bracket_jacobi`);
and `Δ` is a derivation of the bracket (`GerBV.Δ_bracket`).

The Jacobi identity uses only `Δ² = 0` and the order condition, not the commutativity of the
product (`GerBV.dev_jacobi`).
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

universe u v

namespace Operad

namespace GerBV

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

variable (R) in
/-- The sign of a parity: `σ false = 1`, `σ true = -1`. -/
def σ (b : Bool) : R := if b then -1 else 1

@[simp] lemma σ_false : σ R false = 1 := rfl

@[simp] lemma σ_true : σ R true = -1 := rfl

variable (ε : V →ₗ[R] V) (μ : V →ₗ[R] V →ₗ[R] V) (Δ : V →ₗ[R] V)

/-- A homogeneous element of parity `p`. -/
def IsPar (p : Bool) (x : V) : Prop := ε x = σ R p • x

/-- **The deviation** of `Δ` from being a derivation of `μ`, for `x` of parity `p`:
`⟨x, y⟩ = Δ (x y) - (Δ x) y - σ p x (Δ y)`. -/
def dev (p : Bool) (x y : V) : V := Δ (μ x y) - μ (Δ x) y - σ R p • μ x (Δ y)

/-- **The derived bracket** `[x, y] = σ p ⟨x, y⟩`, for `x` of parity `p`. -/
def bracket (p : Bool) (x y : V) : V := σ R p • dev μ Δ p x y

/-- **A BV algebra**: a graded commutative product and an odd operator `Δ` with `Δ² = 0`, of
order at most two. -/
structure IsBV : Prop where
  /-- Graded commutativity. -/
  comm : ∀ p q x y, IsPar ε p x → IsPar ε q y → μ x y = σ R (p && q) • μ y x
  /-- The product adds parities. -/
  par_mul : ∀ p q x y, IsPar ε p x → IsPar ε q y → IsPar ε (xor p q) (μ x y)
  /-- `Δ` is odd. -/
  par_Δ : ∀ p x, IsPar ε p x → IsPar ε (!p) (Δ x)
  /-- `Δ² = 0`. -/
  Δ_Δ : ∀ x, Δ (Δ x) = 0
  /-- **Order at most two**: the deviation is a graded derivation in its second argument. -/
  order_two : ∀ p q x y z, IsPar ε p x → IsPar ε q y →
    dev μ Δ p x (μ y z) = μ (dev μ Δ p x y) z + σ R ((!p) && q) • μ y (dev μ Δ p x z)

variable {ε μ Δ}

lemma IsPar.add {p : Bool} {x y : V} (hx : IsPar ε p x) (hy : IsPar ε p y) :
    IsPar ε p (x + y) := by
  unfold IsPar at *
  rw [map_add, hx, hy, smul_add]

lemma IsPar.smul {p : Bool} {x : V} (hx : IsPar ε p x) (c : R) : IsPar ε p (c • x) := by
  unfold IsPar at *
  rw [map_smul, hx, smul_comm]

lemma IsPar.sub {p : Bool} {x y : V} (hx : IsPar ε p x) (hy : IsPar ε p y) :
    IsPar ε p (x - y) := by
  unfold IsPar at *
  rw [map_sub, hx, hy, smul_sub]

/-- The deviation of homogeneous elements is homogeneous, of the parity of a bracket. -/
lemma IsBV.par_dev (h : IsBV ε μ Δ) {p q : Bool} {x y : V} (hx : IsPar ε p x)
    (hy : IsPar ε q y) : IsPar ε (!(xor p q)) (dev μ Δ p x y) := by
  unfold dev
  refine ((h.par_Δ _ _ (h.par_mul _ _ _ _ hx hy)).sub ?_).sub ?_
  · have := h.par_mul _ _ _ _ (h.par_Δ _ _ hx) hy
    cases p <;> cases q <;> simpa using this
  · have := h.par_mul _ _ _ _ hx (h.par_Δ _ _ hy)
    refine IsPar.smul ?_ _
    cases p <;> cases q <;> simpa using this

lemma IsBV.par_bracket (h : IsBV ε μ Δ) {p q : Bool} {x y : V} (hx : IsPar ε p x)
    (hy : IsPar ε q y) : IsPar ε (!(xor p q)) (bracket μ Δ p x y) :=
  (h.par_dev hx hy).smul _

lemma dev_sub_right (p : Bool) (x y z : V) :
    dev μ Δ p x (y - z) = dev μ Δ p x y - dev μ Δ p x z := by
  simp only [dev, map_sub, smul_sub]
  abel

lemma dev_smul_right (p : Bool) (c : R) (x y : V) :
    dev μ Δ p x (c • y) = c • dev μ Δ p x y := by
  simp only [dev, map_smul, smul_sub, smul_comm c (σ R p)]

lemma dev_sub_left (p : Bool) (x y z : V) :
    dev μ Δ p (x - y) z = dev μ Δ p x z - dev μ Δ p y z := by
  simp only [dev, map_sub, LinearMap.sub_apply, smul_sub]
  abel

lemma dev_smul_left (p : Bool) (c : R) (x z : V) :
    dev μ Δ p (c • x) z = c • dev μ Δ p x z := by
  simp only [dev, map_smul, LinearMap.smul_apply, smul_sub, smul_comm c (σ R p)]

/-- **`Δ` is a derivation of the deviation**: `Δ ⟨x, y⟩ = -⟨Δ x, y⟩ - σ p ⟨x, Δ y⟩`. -/
lemma Δ_dev (hΔ : ∀ x, Δ (Δ x) = 0) (p : Bool) (x y : V) :
    Δ (dev μ Δ p x y) = -dev μ Δ (!p) (Δ x) y - σ R p • dev μ Δ p x (Δ y) := by
  simp only [dev, map_sub, map_smul, hΔ, LinearMap.zero_apply, map_zero, smul_zero, sub_zero]
  cases p <;> simp <;> abel

/-- **The deviation is graded symmetric**: `⟨x, y⟩ = σ(|x| |y|) ⟨y, x⟩`. -/
lemma IsBV.dev_comm (h : IsBV ε μ Δ) {p q : Bool} {x y : V} (hx : IsPar ε p x)
    (hy : IsPar ε q y) : dev μ Δ p x y = σ R (p && q) • dev μ Δ q y x := by
  have c1 := congrArg Δ (h.comm _ _ _ _ hx hy)
  have c2 := h.comm _ _ _ _ (h.par_Δ _ _ hx) hy
  have c3 := h.comm _ _ _ _ hx (h.par_Δ _ _ hy)
  rw [map_smul] at c1
  unfold dev
  cases p <;> cases q <;> simp at c1 c2 c3 ⊢
  · linear_combination (norm := module) c1 - c2 - c3
  · linear_combination (norm := module) c1 - c2 - c3
  · linear_combination (norm := module) c1 - c2 + c3
  · linear_combination (norm := module) c1 - c2 + c3

/-- **The Jacobi identity for the deviation**:
`⟨x, ⟨y, z⟩⟩ = -σ|x| ⟨⟨x, y⟩, z⟩ - σ(|x| + (|x| + 1)|y|) ⟨y, ⟨x, z⟩⟩`. It needs only `Δ² = 0` and
the order condition, for any notion `H` of homogeneity. -/
theorem dev_jacobi {H : Bool → V → Prop} (hΔ : ∀ x, Δ (Δ x) = 0)
    (hord : ∀ p q x y z, H p x → H q y →
      dev μ Δ p x (μ y z) = μ (dev μ Δ p x y) z + σ R ((!p) && q) • μ y (dev μ Δ p x z))
    (hpΔ : ∀ p x, H p x → H (!p) (Δ x)) {p q : Bool} {x y : V} (z : V)
    (hx : H p x) (hy : H q y) :
    dev μ Δ p x (dev μ Δ q y z)
      = -σ R p • dev μ Δ (!(xor p q)) (dev μ Δ p x y) z
        - σ R (xor p ((!p) && q)) • dev μ Δ q y (dev μ Δ p x z) := by
  have O1 := congrArg Δ (hord p q x y z hx hy)
  have O2 := hord p (!q) x (Δ y) z hx (hpΔ q y hy)
  have O3 := hord p q x y (Δ z) hx hy
  have O4 := hord (!p) q (Δ x) y z (hpΔ p x hx) hy
  simp only [dev, map_sub, map_smul, map_add, hΔ, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, map_zero, smul_zero, sub_zero] at O1 O2 O3 O4 ⊢
  cases p <;> cases q <;> simp at O1 O2 O3 O4 ⊢
  · linear_combination (norm := module) -O1 - O4 - O2 - O3
  · linear_combination (norm := module) -O1 - O4 - O2 + O3
  · linear_combination (norm := module) O1 + O4 - O2 - O3
  · linear_combination (norm := module) O1 + O4 - O2 + O3

/-! ## Koszul's theorem -/

/-- **The derived bracket is graded antisymmetric**: `[x, y] = -σ((|x| + 1)(|y| + 1)) [y, x]`. -/
theorem IsBV.bracket_antisymm (h : IsBV ε μ Δ) {p q : Bool} {x y : V} (hx : IsPar ε p x)
    (hy : IsPar ε q y) :
    bracket μ Δ p x y = -σ R ((!p) && (!q)) • bracket μ Δ q y x := by
  unfold bracket
  rw [h.dev_comm hx hy]
  cases p <;> cases q <;> simp

/-- **The Poisson rule**: the derived bracket is a graded derivation of the product,
`[x, y z] = [x, y] z + σ((|x| + 1)|y|) y [x, z]`. -/
theorem IsBV.bracket_mul_right (h : IsBV ε μ Δ) {p q : Bool} {x y : V} (hx : IsPar ε p x)
    (hy : IsPar ε q y) (z : V) :
    bracket μ Δ p x (μ y z)
      = μ (bracket μ Δ p x y) z + σ R ((!p) && q) • μ y (bracket μ Δ p x z) := by
  unfold bracket
  rw [h.order_two p q x y z hx hy, smul_add, map_smul, LinearMap.smul_apply, map_smul,
    smul_comm (σ R p)]

/-- **The graded Jacobi identity** for the derived bracket:
`[x, [y, z]] = [[x, y], z] + σ((|x| + 1)(|y| + 1)) [y, [x, z]]`. -/
theorem IsBV.bracket_jacobi (h : IsBV ε μ Δ) {p q : Bool} {x y : V} (hx : IsPar ε p x)
    (hy : IsPar ε q y) (z : V) :
    bracket μ Δ p x (bracket μ Δ q y z)
      = bracket μ Δ (!(xor p q)) (bracket μ Δ p x y) z
        + σ R ((!p) && (!q)) • bracket μ Δ q y (bracket μ Δ p x z) := by
  unfold bracket
  rw [dev_smul_right, dev_smul_left, dev_smul_right,
    dev_jacobi h.Δ_Δ h.order_two h.par_Δ z hx hy]
  cases p <;> cases q <;> simp
  module

/-- **`Δ` is a derivation of the derived bracket**:
`Δ [x, y] = [Δ x, y] + σ(|x| + 1) [x, Δ y]`. -/
theorem Δ_bracket (hΔ : ∀ x, Δ (Δ x) = 0) (p : Bool) (x y : V) :
    Δ (bracket μ Δ p x y)
      = bracket μ Δ (!p) (Δ x) y + σ R (!p) • bracket μ Δ p x (Δ y) := by
  unfold bracket
  rw [map_smul, Δ_dev hΔ]
  cases p <;> simp
  module

end GerBV

end Operad
