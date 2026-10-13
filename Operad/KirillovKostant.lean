/-
# Kirillov–Kostant brackets on polynomial algebras

A bracket `c u v` of the variables of a polynomial algebra `K[X_u]` extends to **the
Kirillov–Kostant bracket** `{f, g} = ∑_{u, v} ∂_u f ∂_v g c(u, v)` (`KK.bracket`), the unique
bracket which is a derivation in each argument with `{X_u, X_v} = c u v` (`KK.bracket_X_X`,
`KK.bracket_mul_left`, `KK.bracket_mul_right`). It is built from the derivations
`D_u : X_v ↦ c u v` (`KK.der`): `f ↦ {f, g}` is the derivation `X_u ↦ D_u g` (`KK.brk`).

* **It is antisymmetric** when `c` is (`KK.bracket_antisymm`), both sides being derivations in each
  argument agreeing on the variables.
* **It satisfies the Jacobi identity** when it does on the variables (`KK.jacobi`): the Jacobiator
  of an antisymmetric bracket which is a derivation in each argument is a derivation in each
  argument, so it vanishes as soon as it vanishes on the variables.

So **a polynomial algebra with a Kirillov–Kostant bracket is a Poisson algebra**
(`KK.poisAlg`). The example used to compute the dimensions of the Poisson operad is **the
polynomial algebra on the words**, with the commutator `c u v = X_{uv} - X_{vu}` of the free
associative algebra (`KK.wordBracket`, `KK.wordPoisAlg`): it is the symmetric algebra of the
tensor algebra with its commutator bracket.
-/
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Tactic.LinearCombination
import Operad.BinaryKoszul

universe u v

namespace Operad

namespace KK

open MvPolynomial Sym

variable {K : Type u} [CommRing K] {σ : Type v} (c : σ → σ → MvPolynomial σ K)

/-- **The derivation `D_u`**: `X_v ↦ c u v`. -/
noncomputable def der (u : σ) : Derivation K (MvPolynomial σ K) (MvPolynomial σ K) :=
  mkDerivation K (c u)

/-- **The derivation `f ↦ {f, g}`**: `X_u ↦ D_u g`. -/
noncomputable def brk (g : MvPolynomial σ K) :
    Derivation K (MvPolynomial σ K) (MvPolynomial σ K) :=
  mkDerivation K fun u => der c u g

/-- **The Kirillov–Kostant bracket** `{f, g}`. -/
noncomputable def bracket (f g : MvPolynomial σ K) : MvPolynomial σ K := brk c g f

lemma der_X (u v : σ) : der c u (X v) = c u v := mkDerivation_X _ _ _

lemma brk_X (g : MvPolynomial σ K) (u : σ) : brk c g (X u) = der c u g := mkDerivation_X _ _ _

@[simp] lemma bracket_X_X (u v : σ) : bracket c (X u) (X v) = c u v := by
  rw [bracket, brk_X, der_X]

lemma bracket_X_left (u : σ) (g : MvPolynomial σ K) : bracket c (X u) g = der c u g :=
  brk_X c g u

/-! ### Linearity and the Leibniz rules -/

lemma brk_add (g₁ g₂ : MvPolynomial σ K) : brk c (g₁ + g₂) = brk c g₁ + brk c g₂ :=
  derivation_ext fun u => by
    rw [Derivation.add_apply, brk_X, brk_X, brk_X, map_add]

lemma brk_smul (a : K) (g : MvPolynomial σ K) : brk c (a • g) = a • brk c g :=
  derivation_ext fun u => by
    rw [Derivation.smul_apply, brk_X, brk_X, Derivation.map_smul]

lemma brk_mul (g₁ g₂ : MvPolynomial σ K) : brk c (g₁ * g₂) = g₁ • brk c g₂ + g₂ • brk c g₁ :=
  derivation_ext fun u => by
    rw [Derivation.add_apply, Derivation.smul_apply, Derivation.smul_apply, brk_X, brk_X, brk_X,
      Derivation.leibniz]

lemma brk_C (a : K) : brk c (C a) = 0 :=
  derivation_ext fun u => by
    rw [brk_X, Derivation.zero_apply, ← algebraMap_eq, Derivation.map_algebraMap]

lemma bracket_add_left (f₁ f₂ g : MvPolynomial σ K) :
    bracket c (f₁ + f₂) g = bracket c f₁ g + bracket c f₂ g := map_add _ _ _

lemma bracket_add_right (f g₁ g₂ : MvPolynomial σ K) :
    bracket c f (g₁ + g₂) = bracket c f g₁ + bracket c f g₂ := by
  rw [bracket, brk_add, Derivation.add_apply]
  rfl

lemma bracket_smul_left (a : K) (f g : MvPolynomial σ K) :
    bracket c (a • f) g = a • bracket c f g := Derivation.map_smul _ _ _

lemma bracket_smul_right (a : K) (f g : MvPolynomial σ K) :
    bracket c f (a • g) = a • bracket c f g := by
  rw [bracket, brk_smul, Derivation.smul_apply]
  rfl

lemma bracket_sub_right (f g₁ g₂ : MvPolynomial σ K) :
    bracket c f (g₁ - g₂) = bracket c f g₁ - bracket c f g₂ := by
  rw [sub_eq_add_neg, bracket_add_right, ← neg_one_smul K g₂, bracket_smul_right, neg_one_smul,
    ← sub_eq_add_neg]

/-- **The Leibniz rule in the first argument.** -/
lemma bracket_mul_left (f₁ f₂ g : MvPolynomial σ K) :
    bracket c (f₁ * f₂) g = f₁ * bracket c f₂ g + f₂ * bracket c f₁ g :=
  Derivation.leibniz _ _ _

/-- **The Leibniz rule in the second argument.** -/
lemma bracket_mul_right (f g₁ g₂ : MvPolynomial σ K) :
    bracket c f (g₁ * g₂) = g₁ * bracket c f g₂ + g₂ * bracket c f g₁ := by
  rw [bracket, brk_mul, Derivation.add_apply, Derivation.smul_apply, Derivation.smul_apply]
  rfl

lemma bracket_C_right (f : MvPolynomial σ K) (a : K) : bracket c f (C a) = 0 := by
  rw [bracket, brk_C, Derivation.zero_apply]

lemma bracket_C_left (a : K) (g : MvPolynomial σ K) : bracket c (C a) g = 0 := by
  rw [bracket, ← algebraMap_eq, Derivation.map_algebraMap]

lemma bracket_zero_right (f : MvPolynomial σ K) : bracket c f 0 = 0 := by
  simpa using bracket_C_right c f 0

/-! ### Antisymmetry -/

variable {c}

/-- With an antisymmetric bracket of the variables, `{f, X_v} = -D_v f`. -/
lemma bracket_X_right (hc : ∀ u v, c u v = -c v u) (f : MvPolynomial σ K) (v : σ) :
    bracket c f (X v) = -der c v f := by
  have h : brk c (X v) = -der c v := derivation_ext fun u => by
    rw [brk_X, der_X, Derivation.neg_apply, der_X, hc]
  rw [bracket, h, Derivation.neg_apply]

/-- **The bracket is antisymmetric** when the bracket of the variables is. -/
theorem bracket_antisymm (hc : ∀ u v, c u v = -c v u) (f g : MvPolynomial σ K) :
    bracket c f g = -bracket c g f := by
  induction g using MvPolynomial.induction_on with
  | C a => rw [bracket_C_right, bracket_C_left, neg_zero]
  | add p q hp hq => rw [bracket_add_right, bracket_add_left, hp, hq, neg_add]
  | mul_X p v hp =>
    rw [bracket_mul_right, bracket_mul_left, hp, bracket_X_right hc, bracket_X_left]
    ring

/-! ### The Jacobi identity -/

variable (c) in
/-- **The Jacobiator** `{f, {g, h}} + {g, {h, f}} + {h, {f, g}}`. -/
noncomputable def jac (f g h : MvPolynomial σ K) : MvPolynomial σ K :=
  bracket c f (bracket c g h) + bracket c g (bracket c h f) + bracket c h (bracket c f g)

lemma jac_cycle (f g h : MvPolynomial σ K) : jac c f g h = jac c g h f := by
  rw [jac, jac]
  abel

lemma jac_add (f₁ f₂ g h : MvPolynomial σ K) :
    jac c (f₁ + f₂) g h = jac c f₁ g h + jac c f₂ g h := by
  simp only [jac, bracket_add_left, bracket_add_right]
  abel

lemma jac_C (a : K) (g h : MvPolynomial σ K) : jac c (C a) g h = 0 := by
  simp only [jac, bracket_C_left, bracket_C_right, bracket_zero_right, add_zero]

/-- **The Jacobiator is a derivation in its first argument**, for an antisymmetric bracket. -/
lemma jac_mul (hc : ∀ u v, c u v = -c v u) (f₁ f₂ g h : MvPolynomial σ K) :
    jac c (f₁ * f₂) g h = f₁ * jac c f₂ g h + f₂ * jac c f₁ g h := by
  simp only [jac, bracket_mul_left, bracket_mul_right, bracket_add_right]
  have e1 := bracket_antisymm hc f₂ g
  have e2 := bracket_antisymm hc f₁ g
  linear_combination bracket c h f₁ * e1 + bracket c h f₂ * e2

/-- **The Jacobi identity**, when it holds on the variables. -/
theorem jacobi (hc : ∀ u v, c u v = -c v u)
    (hJ : ∀ u v w, jac c (X u) (X v) (X w) = 0) (f g h : MvPolynomial σ K) :
    jac c f g h = 0 := by
  -- in the first argument, then by the cyclic symmetry in the others
  have h3 : ∀ u v (h : MvPolynomial σ K), jac c (X u) (X v) h = 0 := fun u v h => by
    rw [jac_cycle, jac_cycle]
    induction h using MvPolynomial.induction_on with
    | C a => exact jac_C a _ _
    | add p q hp hq => rw [jac_add, hp, hq, add_zero]
    | mul_X p w hp => rw [jac_mul hc, hp, hJ, mul_zero, mul_zero, add_zero]
  have h2 : ∀ u (g h : MvPolynomial σ K), jac c (X u) g h = 0 := fun u g h => by
    rw [jac_cycle]
    induction g using MvPolynomial.induction_on generalizing h with
    | C a => exact jac_C a _ _
    | add p q hp hq => rw [jac_add, hp, hq, add_zero]
    | mul_X p v hp =>
      rw [jac_mul hc, hp, ← jac_cycle, h3, mul_zero, mul_zero, add_zero]
  induction f using MvPolynomial.induction_on generalizing g h with
  | C a => exact jac_C a _ _
  | add p q hp hq => rw [jac_add, hp, hq, add_zero]
  | mul_X p u hp => rw [jac_mul hc, hp, h2, mul_zero, mul_zero, add_zero]

/-! ### Poisson algebras -/

variable (c) in
/-- The Kirillov–Kostant bracket, as a bilinear map. -/
noncomputable def bracketL :
    MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  LinearMap.mk₂ K (bracket c) (bracket_add_left c) (bracket_smul_left c) (bracket_add_right c)
    (bracket_smul_right c)

/-- **A Kirillov–Kostant bracket makes the polynomial algebra a Poisson algebra.** -/
noncomputable def poisAlg (hc : ∀ u v, c u v = -c v u)
    (hJ : ∀ u v w, jac c (X u) (X v) (X w) = 0) : PoisAlg K (MvPolynomial σ K) where
  mul := FreeBin.bilinOp (LinearMap.mul K (MvPolynomial σ K))
  bracket := FreeBin.bilinOp (bracketL c)
  comm x y := mul_comm x y
  assoc x y z := mul_assoc x y z
  antisymm x y := bracket_antisymm hc x y
  jacobi x y z := by
    show bracket c (bracket c x y) z + bracket c (bracket c y z) x + bracket c (bracket c z x) y
      = 0
    have := jacobi hc hJ z x y
    rw [jac, bracket_antisymm hc z, bracket_antisymm hc x (bracket c y z),
      bracket_antisymm hc y (bracket c z x)] at this
    linear_combination -this
  leibniz x y z := by
    show bracket c x (y * z) = bracket c x y * z + y * bracket c x z
    rw [bracket_mul_right]
    ring

lemma poisAlg_mul (hc : ∀ u v, c u v = -c v u) (hJ : ∀ u v w, jac c (X u) (X v) (X w) = 0)
    (x y : MvPolynomial σ K) : (poisAlg hc hJ).mul ![x, y] = x * y :=
  FreeBin.bilinOp_apply K _ x y

lemma poisAlg_bracket (hc : ∀ u v, c u v = -c v u)
    (hJ : ∀ u v w, jac c (X u) (X v) (X w) = 0) (x y : MvPolynomial σ K) :
    (poisAlg hc hJ).bracket ![x, y] = bracket c x y :=
  FreeBin.bilinOp_apply K _ x y

/-! ## Polynomials in words -/

variable (K) in
/-- **The commutator of words**: `c u v = X_{uv} - X_{vu}`. -/
noncomputable def wordBracket (u v : List ℕ) : MvPolynomial (List ℕ) K := X (u ++ v) - X (v ++ u)

lemma wordBracket_antisymm (u v : List ℕ) : wordBracket K u v = -wordBracket K v u := by
  rw [wordBracket, wordBracket, neg_sub]

lemma wordBracket_jac (u v w : List ℕ) :
    jac (wordBracket K) (X u) (X v) (X w) = 0 := by
  simp only [jac, bracket_X_X, wordBracket, bracket_sub_right, List.append_assoc]
  abel

variable (K) in
/-- **The Poisson algebra of polynomials in words**: the symmetric algebra of the free associative
algebra with its commutator bracket. -/
noncomputable def wordPoisAlg : PoisAlg K (MvPolynomial (List ℕ) K) :=
  poisAlg wordBracket_antisymm wordBracket_jac

end KK

end Operad
