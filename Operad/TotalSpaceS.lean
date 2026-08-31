/-
# The signed total space, and the graded Jacobi identity

`Operad.GradedPreLie` proves the graded pre-Lie identity arity by arity, with explicit
reindexings. Reading off the Jacobi identity from it in that form would mean tracking twelve
products across six different arity expressions at once.

Bundling into a direct sum removes all of that: every product lands in the single type
`TotS R P`, the associator is mathlib's, and the twelve-term regrouping becomes one call to the
`module` tactic. This is the same move `Operad.TotalSpace` makes for the unsigned product; the
two cannot share a type, because a type carries only one multiplication, so `PieceS` is a second
synonym for `P (k + 1)` carrying the signed one.

Note what is *not* claimed. A graded Lie structure is not a `LieRing` on `TotS R P`: the sign
`(-1)^(j k)` depends on the degrees of the arguments, so the identity holds for homogeneous
elements and does not extend to the whole direct sum. The statements below are therefore about
`incS`-images, and the degrees appear explicitly.
-/
import Operad.GradedPreLie
import Operad.TotalSpace

universe u v

namespace Operad

open NSOperad DirectSum

/-- The degree-`k` piece of the signed total space. -/
def PieceS (R : Type u) [CommRing R] (P : ℕ → Type v) (k : ℕ) : Type v := P (k + 1)

section

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]

instance (k : ℕ) : AddCommGroup (PieceS R P k) := inferInstanceAs (AddCommGroup (P (k + 1)))

instance (k : ℕ) : Module R (PieceS R P k) := inferInstanceAs (Module R (P (k + 1)))

variable [NSOperad R P]

/-- The signed circle product as a graded multiplication. -/
instance : GradedMonoid.GMul (PieceS R P) where
  mul {_ _} a b := sstar (R := R) a b

instance : DirectSum.GNonUnitalNonAssocSemiring (PieceS R P) where
  mul_zero a := sstar_zero (R := R) a
  zero_mul b := zero_sstar (R := R) b
  mul_add a b c := sstar_add_right (R := R) a b c
  add_mul a b c := sstar_add_left (R := R) a b c

/-- The total space carrying the signed product. -/
abbrev TotS (R : Type u) [CommRing R] (P : ℕ → Type v)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] : Type v :=
  ⨁ k : ℕ, PieceS R P k

/-- The inclusion of a homogeneous piece. -/
abbrev incS (k : ℕ) : PieceS R P k →+ TotS R P := DirectSum.of (PieceS R P) k

@[simp] lemma incS_mul_incS {i j : ℕ} (a : PieceS R P i) (b : PieceS R P j) :
    (incS i a * incS j b : TotS R P) = incS (i + j) (sstar (R := R) a b) :=
  DirectSum.of_mul_of a b

lemma incS_reindex {m n : ℕ} (h : m = n) (x : PieceS R P m) :
    (incS m x : TotS R P) = incS n (reindex R P (by rw [h]) x) := by
  subst h
  rw [reindex_self]

lemma smul_incS (t : R) {i : ℕ} (a : PieceS R P i) :
    t • (incS i a : TotS R P) = incS i (t • a) :=
  (DirectSum.of_smul (R := R) i t a).symm

/-! ### `R`-bilinearity of the signed product on the total space -/

lemma smul_mul_totS (t : R) (x y : TotS R P) : (t • x) * y = t • (x * y) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [smul_add, add_mul, h₁, h₂]
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp only [mul_add, smul_add, h₁, h₂]
    | of j b =>
      rw [smul_incS, incS_mul_incS, incS_mul_incS, smul_incS]
      exact congrArg _ (sstar_smul_left t a b)

lemma mul_smul_totS (t : R) (x y : TotS R P) : x * (t • y) = t • (x * y) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [smul_add, add_mul, h₁, h₂]
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp only [mul_add, smul_add, h₁, h₂]
    | of j b =>
      rw [smul_incS, incS_mul_incS, incS_mul_incS, smul_incS]
      exact congrArg _ (sstar_smul_right t a b)

/-! ### The graded pre-Lie identity on the total space -/

/-- The graded pre-Lie identity, transported to homogeneous elements of `TotS`. -/
lemma associatorS_inc (i j k : ℕ) (a : PieceS R P i) (b : PieceS R P j) (c : PieceS R P k) :
    associator (incS i a : TotS R P) (incS j b) (incS k c)
      = ((-1 : R) ^ (j * k))
        • associator (incS i a : TotS R P) (incS k c) (incS j b) := by
  simp only [associator, incS_mul_incS]
  rw [incS_reindex (show i + (j + k) = i + j + k by omega),
    incS_reindex (show i + k + j = i + j + k by omega),
    incS_reindex (show i + (k + j) = i + j + k by omega), ← map_sub, ← map_sub, smul_incS]
  exact congrArg _ (sstar_assoc_symm a b c)

/-! ### The graded Jacobi identity -/

/-- The graded bracket of two elements whose degrees are asserted to be `m` and `n`. Degrees are
parameters rather than being read off the elements, because an element of a direct sum need not
be homogeneous; every use below supplies the degree of an `incS`-image. -/
def brT (m n : ℕ) (x y : TotS R P) : TotS R P :=
  x * y - ((-1 : R) ^ (m * n)) • (y * x)

private lemma neg_one_two_mul (n : ℕ) : ((-1 : R)) ^ (2 * n) = 1 := by
  rw [pow_mul]; norm_num

private lemma neg_one_mul_two (n : ℕ) : ((-1 : R)) ^ (n * 2) = 1 := by
  rw [mul_comm]; exact neg_one_two_mul n

/-- The twelve products of a signed double bracket regroup into six associators. This is pure
bilinear algebra in `TotS R P` — no operad axiom is used. -/
private lemma jacobi_regroup (i j k : ℕ) (x y z : TotS R P) :
    ((-1 : R) ^ (i * k)) • brT (i + j) k (brT i j x y) z
      + ((-1 : R) ^ (j * i)) • brT (j + k) i (brT j k y z) x
      + ((-1 : R) ^ (k * j)) • brT (k + i) j (brT k i z x) y
      = ((-1 : R) ^ (i * k)) • (associator x y z - ((-1 : R) ^ (j * k)) • associator x z y)
        + ((-1 : R) ^ (j * i)) • (associator y z x - ((-1 : R) ^ (k * i)) • associator y x z)
        + ((-1 : R) ^ (k * j)) • (associator z x y - ((-1 : R) ^ (i * j)) • associator z y x) := by
  simp only [brT, associator, sub_mul, mul_sub, smul_mul_totS, mul_smul_totS, smul_sub, smul_smul,
    ← pow_add]
  match_scalars
  all_goals ring_nf
  all_goals try simp only [neg_one_mul_two, neg_one_two_mul, mul_one, one_mul]
  all_goals try ring

/-- **The graded Jacobi identity.** Each of the three regrouped brackets is one instance of the
graded pre-Lie identity, so all three vanish. -/
theorem jacobiS (i j k : ℕ) (a : PieceS R P i) (b : PieceS R P j) (c : PieceS R P k) :
    ((-1 : R) ^ (i * k)) • brT (i + j) k (brT i j (incS i a) (incS j b)) (incS k c)
      + ((-1 : R) ^ (j * i)) • brT (j + k) i (brT j k (incS j b) (incS k c)) (incS i a)
      + ((-1 : R) ^ (k * j)) • brT (k + i) j (brT k i (incS k c) (incS i a)) (incS j b) = 0 := by
  rw [jacobi_regroup, associatorS_inc i j k a b c, associatorS_inc j k i b c a,
    associatorS_inc k i j c a b]
  simp

/-! ### An obstruction at the prime 2

Applying the graded pre-Lie identity with its last two arguments *equal and odd* gives
`A(x, Θ, Θ) = -A(x, Θ, Θ)`, so that associator is 2-torsion but need not vanish. This is exactly
what stands between the Maurer–Cartan equation and `d² = 0`: expanding `d = ⁅Θ, -⁆` for odd `Θ`
with `Θ ⋆ₛ Θ = 0` leaves `d²(x) = -A(x, Θ, Θ)`, which the identity kills only after inverting 2.
It is not an artefact of the formalisation — it is why the classical statement is made over a
ring in which 2 is not a zero divisor. -/

/-- The associator with two equal odd arguments is annihilated by 2. -/
lemma two_smul_associator_odd (m : ℕ) (x : PieceS R P m) (T : PieceS R P 1) :
    (2 : ℕ) • associator (incS m x : TotS R P) (incS 1 T) (incS 1 T) = 0 := by
  have h := associatorS_inc m 1 1 x T T
  rw [Nat.mul_one, pow_one, neg_one_smul] at h
  rw [two_smul]
  exact add_eq_zero_iff_eq_neg.2 h

/-! ### The differential

For an odd `Θ` solving the Maurer–Cartan equation, `d = ⁅Θ, -⁆` squares to `-A(x, Θ, Θ)`. That
term is 2-torsion by `two_smul_associator_odd` but not zero, so `d² = 0` is stated with `2`
invertible. -/

/-- `d²` collapses to a single associator: everything else cancels, using the graded pre-Lie
identity once and the Maurer–Cartan equation twice. -/
theorem dsq_eq (m : ℕ) (T : PieceS R P 1) (x : PieceS R P m)
    (hMC : (incS 1 T : TotS R P) * incS 1 T = 0) :
    brT 1 (1 + m) (incS 1 T) (brT 1 m (incS 1 T) (incS m x))
      = - associator (incS m x : TotS R P) (incS 1 T) (incS 1 T) := by
  have hA := associatorS_inc 1 m 1 T x T
  rw [Nat.mul_one] at hA
  have expand : brT 1 (1 + m) (incS 1 T) (brT 1 m (incS 1 T) (incS m x))
      = (incS 1 T * incS 1 T : TotS R P) * incS m x
        - associator (incS 1 T : TotS R P) (incS 1 T) (incS m x)
        + ((-1 : R) ^ m) • associator (incS 1 T : TotS R P) (incS m x) (incS 1 T)
        - associator (incS m x : TotS R P) (incS 1 T) (incS 1 T)
        - (incS m x : TotS R P) * (incS 1 T * incS 1 T) := by
    simp only [brT, associator, mul_sub, sub_mul, smul_mul_totS, mul_smul_totS, smul_sub,
      smul_smul, ← pow_add]
    match_scalars
    all_goals ring_nf
    all_goals try simp only [neg_one_mul_two, neg_one_two_mul, mul_one, one_mul]
    all_goals try ring
  rw [expand, hA, smul_smul, ← pow_add, show m + m = 2 * m from by ring, neg_one_two_mul,
    one_smul, hMC]
  simp

/-- **The differential squares to zero**, once `2` is invertible. -/
theorem dsq_eq_zero [Invertible (2 : R)] (m : ℕ) (T : PieceS R P 1) (x : PieceS R P m)
    (hMC : (incS 1 T : TotS R P) * incS 1 T = 0) :
    brT 1 (1 + m) (incS 1 T) (brT 1 m (incS 1 T) (incS m x)) = 0 := by
  rw [dsq_eq m T x hMC, neg_eq_zero]
  have h2 : ((2 : R)) • associator (incS m x : TotS R P) (incS 1 T) (incS 1 T) = 0 := by
    have h := two_smul_associator_odd m x T
    rw [two_smul] at h
    rw [two_smul]
    exact h
  calc associator (incS m x : TotS R P) (incS 1 T) (incS 1 T)
      = (⅟(2 : R) * 2) • associator (incS m x : TotS R P) (incS 1 T) (incS 1 T) := by
        rw [invOf_mul_self, one_smul]
    _ = ⅟(2 : R) • ((2 : R) • associator (incS m x : TotS R P) (incS 1 T) (incS 1 T)) := by
        rw [mul_smul]
    _ = 0 := by rw [h2, smul_zero]

end

end Operad
