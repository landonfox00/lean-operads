/-
# Operad cohomology

With `d = ⁅Θ, -⁆` squaring to zero, the deformation complex is a cochain complex and its
cohomology is defined. The differential is packaged here as a genuine `LinearMap` between the
graded pieces, which is what `LinearMap.ker` and `LinearMap.range` need.

Degrees are indexed by the *source*: `dLin T m : PieceS R P m →ₗ PieceS R P (1 + m)`. Indexing
by the target would force `1 + (m - 1) = m`, reintroducing the truncated subtraction that the
whole library is arranged to avoid.
-/
import Operad.TotalSpaceS
import Mathlib.LinearAlgebra.Quotient.Basic

universe u v

namespace Operad

open NSOperad DirectSum

section

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-! ### Linearity of the graded bracket in its second argument -/

lemma gbracket_add_right {j k : ℕ} (α : P (j + 1)) (β β' : P (k + 1)) :
    gbracket (R := R) α (β + β') = gbracket (R := R) α β + gbracket (R := R) α β' := by
  simp only [gbracket, sstar_add_right, sstar_add_left, map_add, smul_add]
  abel

lemma gbracket_smul_right {j k : ℕ} (r : R) (α : P (j + 1)) (β : P (k + 1)) :
    gbracket (R := R) α (r • β) = r • gbracket (R := R) α β := by
  simp only [gbracket, sstar_smul_right, sstar_smul_left, map_smul, smul_sub]
  rw [smul_comm]

/-- The differential `d = ⁅Θ, -⁆` of the deformation complex, as a linear map. -/
def dLin (T : PieceS R P 1) (m : ℕ) : PieceS R P m →ₗ[R] PieceS R P (1 + m) where
  toFun x := gbracket (R := R) (P := P) (j := 1) (k := m) T x
  map_add' x y := gbracket_add_right (R := R) (P := P) (j := 1) (k := m) T x y
  map_smul' r x := gbracket_smul_right (R := R) (P := P) (j := 1) (k := m) r T x

@[simp] lemma dLin_apply (T : PieceS R P 1) (m : ℕ) (x : PieceS R P m) :
    dLin T m x = gbracket (R := R) (P := P) (j := 1) (k := m) T x := rfl

/-- `incS` is injective, so identities in the total space descend to the graded pieces. -/
lemma incS_injective {i : ℕ} : Function.Injective (incS (R := R) (P := P) i) := by
  intro a b h
  have h' := congrArg (fun y : TotS R P => y i) h
  simpa only [DirectSum.of_eq_same] using h'

/-- The bracket with `Θ` in the total space is the differential on the pieces. -/
lemma brT_incS (m : ℕ) (T : PieceS R P 1) (x : PieceS R P m) :
    brT 1 m (incS 1 T) (incS m x) = incS (1 + m) (dLin T m x) := by
  rw [brT, incS_mul_incS, incS_mul_incS,
    incS_reindex (show m + 1 = 1 + m by omega) (sstar (R := R) (P := P) (j := m) (k := 1) x T), smul_incS, ← map_sub]
  rfl

/-- The Maurer–Cartan equation, transported to the total space. -/
lemma incS_mul_self_eq_zero {T : PieceS R P 1} (hMC : sstar (R := R) (P := P) (j := 1) (k := 1) T T = 0) :
    (incS 1 T : TotS R P) * incS 1 T = 0 := by
  rw [incS_mul_incS, hMC]
  exact map_zero _

/-- **The differential squares to zero on the pieces.** -/
theorem dLin_dLin [Invertible (2 : R)] (T : PieceS R P 1) (hMC : sstar (R := R) (P := P) (j := 1) (k := 1) T T = 0)
    (m : ℕ) (x : PieceS R P m) : dLin T (1 + m) (dLin T m x) = 0 := by
  apply incS_injective (i := 1 + (1 + m))
  rw [map_zero, ← brT_incS, ← brT_incS]
  exact dsq_eq_zero m T x (incS_mul_self_eq_zero hMC)

/-! ### Cocycles, coboundaries, cohomology -/

/-- The cocycles in degree `1 + m`. -/
def cocycles (T : PieceS R P 1) (m : ℕ) : Submodule R (PieceS R P (1 + m)) :=
  LinearMap.ker (dLin T (1 + m))

/-- The coboundaries in degree `1 + m`. -/
def coboundaries (T : PieceS R P 1) (m : ℕ) : Submodule R (PieceS R P (1 + m)) :=
  LinearMap.range (dLin T m)

theorem coboundaries_le_cocycles [Invertible (2 : R)] (T : PieceS R P 1)
    (hMC : sstar (R := R) (P := P) (j := 1) (k := 1) T T = 0) (m : ℕ) : coboundaries T m ≤ cocycles T m := by
  rintro y ⟨x, rfl⟩
  exact dLin_dLin T hMC m x

/-- **Operad cohomology** in degree `1 + m`: cocycles modulo coboundaries. -/
def cohomology (T : PieceS R P 1) (m : ℕ) : Type v :=
  (cocycles (R := R) T m) ⧸
    ((coboundaries (R := R) T m).comap (cocycles (R := R) T m).subtype)

instance (T : PieceS R P 1) (m : ℕ) : AddCommGroup (cohomology (R := R) T m) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (T : PieceS R P 1) (m : ℕ) : Module R (cohomology (R := R) T m) :=
  inferInstanceAs (Module R (_ ⧸ _))

/-- The class of a cocycle. -/
def cohomologyMk (T : PieceS R P 1) (m : ℕ) (x : cocycles (R := R) T m) :
    cohomology (R := R) T m :=
  Submodule.Quotient.mk x

theorem cohomologyMk_eq_zero_iff (T : PieceS R P 1) (m : ℕ) (x : cocycles (R := R) T m) :
    cohomologyMk T m x = 0 ↔ (x : PieceS R P (1 + m)) ∈ coboundaries (R := R) T m :=
  Submodule.Quotient.mk_eq_zero _

end

end Operad
