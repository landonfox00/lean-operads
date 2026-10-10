/-
# The Chevalley–Eilenberg BV algebra of a Lie algebra

For a Lie algebra `L`, the exterior algebra `Λ L` carries the **Chevalley–Eilenberg operator**
`Δ (m₁ ∧ ⋯ ∧ m_k) = ∑_{i < j} ± [m_i, m_j] ∧ m₁ ∧ ⋯ m̂_i ⋯ m̂_j ⋯ ∧ m_k`, defined by the recursion
`Δ (m ∧ x) = -D_m x - m ∧ Δ x` (`ExtBV.Δ_ι_mul`), where `D_m` is the even derivation extending
`ad m` (`ExtBV.D`). It makes `Λ L` a **BV algebra**:
* `Δ² = 0` (`ExtBV.Δ_Δ`), using `[D_m, D_n] = D_[m, n]` (`ExtBV.D_comm`) and `[Δ, D_m] = 0`
  (`ExtBV.Δ_D`);
* `Δ` is **of order at most two** (`ExtBV.dv_mul_even`, `ExtBV.dv_mul_odd`): its deviation
  `⟨x, y⟩ = Δ (x y) - (Δ x) y - x̂ (Δ y)` (`ExtBV.dv`, with `x̂` the grade involution) is a graded
  derivation in `y`. It is computed by `⟨m ∧ x, y⟩ = -x D_m y - m ∧ ⟨x, y⟩` (`ExtBV.dv_ι_mul`).

The parity of `Λ L` is its `ℤ/2`-grading (`ExtBV.prZ`), making it a super module
(`ExtBV.instSuperMod`); the exterior algebra is graded commutative (`ExtBV.mul_comm_even`,
`ExtBV.mul_comm_odd`). Everything is characteristic free.

Hence `Λ L` is a **Gerstenhaber algebra** under the wedge product and the deviation of `Δ`, the
Schouten bracket up to sign (`ExtBV.isGer`), an algebra over the Gerstenhaber operad
(`ExtBV.gerAlg`). On vectors the deviation is the bracket of `L` up to sign:
`⟨m, n⟩ = -[m, n]` (`ExtBV.dv_ι_ι`).
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.NoncommRing
import Operad.GerOperad
import Operad.BinaryKoszul

universe u v

namespace Operad

namespace ExtBV

open ExteriorAlgebra GrEnd
open Sym (EndOp)
open CliffordAlgebra (evenOdd foldr' foldr'_ι_mul foldr'_algebraMap involute involute_ι
  involute_involutive ι_mem_evenOdd_one)

variable {R : Type u} [CommRing R] {L : Type v} [LieRing L] [LieAlgebra R L]

/-- The exterior algebra, as a Clifford algebra. -/
local notation "E" => ExteriorAlgebra R L

/-- The quadratic form of the exterior algebra. -/
local notation "Q₀" => (0 : QuadraticForm R L)

/-- **Induction on the exterior algebra**, by left multiplication by vectors. -/
@[elab_as_elim]
theorem induction {P : E → Prop} (alg : ∀ r, P (algebraMap R E r))
    (add : ∀ x y, P x → P y → P (x + y)) (ι_mul : ∀ m x, P x → P (ι R m * x)) (x : E) : P x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => exact alg r
  | add x y hx hy => exact add x y hx hy
  | ι_mul x m hx => exact ι_mul m x hx

/-! ## Parity -/

/-- **The parity components** of the exterior algebra, `0` even and `1` odd. -/
noncomputable def prZ (i : ZMod 2) : E →ₗ[R] E := GradedAlgebra.proj (evenOdd Q₀) i

lemma prZ_apply (i : ZMod 2) (x : E) : prZ i x = DirectSum.decompose (evenOdd Q₀) x i := rfl

lemma prZ_mem (i : ZMod 2) (x : E) : prZ i x ∈ evenOdd Q₀ i := by
  exact (DirectSum.decompose (evenOdd Q₀) x i).2

lemma prZ_of_mem {i : ZMod 2} {x : E} (h : x ∈ evenOdd Q₀ i) : prZ i x = x :=
  DirectSum.decompose_of_mem_same _ h

lemma prZ_of_mem_ne {i j : ZMod 2} {x : E} (h : x ∈ evenOdd Q₀ i) (hij : i ≠ j) : prZ j x = 0 :=
  DirectSum.decompose_of_mem_ne _ h hij

lemma ι_mem (m : L) : ι R m ∈ evenOdd Q₀ 1 := ι_mem_evenOdd_one Q₀ m

lemma prZ_ι_mul (i : ZMod 2) (m : L) (x : E) : prZ (1 + i) (ι R m * x) = ι R m * prZ i x :=
  DirectSum.coe_decompose_mul_add_of_left_mem (evenOdd Q₀) (ι_mem (R := R) m)

lemma prZ_zero_ι_mul (m : L) (x : E) : prZ 0 (ι R m * x) = ι R m * prZ 1 x := by
  rw [← prZ_ι_mul]
  rfl

lemma prZ_one_ι_mul (m : L) (x : E) : prZ 1 (ι R m * x) = ι R m * prZ 0 x := by
  rw [← prZ_ι_mul]
  rfl

lemma algebraMap_mem (r : R) : algebraMap R E r ∈ evenOdd Q₀ 0 :=
  SetLike.algebraMap_mem_graded _ _

/-- **Induction on parity components**: properties `Pe` of the even and `Po` of the odd elements,
transported by the left multiplications by vectors. -/
theorem parity_induction {Pe Po : E → Prop} (alg : ∀ r, Pe (algebraMap R E r)) (zero : Po 0)
    (adde : ∀ x y, Pe x → Pe y → Pe (x + y)) (addo : ∀ x y, Po x → Po y → Po (x + y))
    (ιe : ∀ m x, x ∈ evenOdd Q₀ 1 → Po x → Pe (ι R m * x))
    (ιo : ∀ m x, x ∈ evenOdd Q₀ 0 → Pe x → Po (ι R m * x)) (x : E) :
    Pe (prZ 0 x) ∧ Po (prZ 1 x) := by
  induction x using induction with
  | alg r =>
    rw [prZ_of_mem (algebraMap_mem r), prZ_of_mem_ne (algebraMap_mem r) (by decide)]
    exact ⟨alg r, zero⟩
  | add x y hx hy =>
    rw [map_add, map_add]
    exact ⟨adde _ _ hx.1 hy.1, addo _ _ hx.2 hy.2⟩
  | ι_mul m x hx =>
    rw [prZ_zero_ι_mul, prZ_one_ι_mul]
    exact ⟨ιe m _ (prZ_mem 1 x) hx.2, ιo m _ (prZ_mem 0 x) hx.1⟩

lemma even_induction' {Pe Po : E → Prop} (alg : ∀ r, Pe (algebraMap R E r)) (zero : Po 0)
    (adde : ∀ x y, Pe x → Pe y → Pe (x + y)) (addo : ∀ x y, Po x → Po y → Po (x + y))
    (ιe : ∀ m x, x ∈ evenOdd Q₀ 1 → Po x → Pe (ι R m * x))
    (ιo : ∀ m x, x ∈ evenOdd Q₀ 0 → Pe x → Po (ι R m * x)) {x : E} (hx : x ∈ evenOdd Q₀ 0) :
    Pe x := by
  have h := (parity_induction alg zero adde addo ιe ιo x).1
  rwa [prZ_of_mem hx] at h

lemma odd_induction' {Pe Po : E → Prop} (alg : ∀ r, Pe (algebraMap R E r)) (zero : Po 0)
    (adde : ∀ x y, Pe x → Pe y → Pe (x + y)) (addo : ∀ x y, Po x → Po y → Po (x + y))
    (ιe : ∀ m x, x ∈ evenOdd Q₀ 1 → Po x → Pe (ι R m * x))
    (ιo : ∀ m x, x ∈ evenOdd Q₀ 0 → Pe x → Po (ι R m * x)) {x : E} (hx : x ∈ evenOdd Q₀ 1) :
    Po x := by
  have h := (parity_induction alg zero adde addo ιe ιo x).2
  rwa [prZ_of_mem hx] at h

lemma prZ_add (x : E) : prZ 0 x + prZ 1 x = x := by
  induction x using induction with
  | alg r =>
    rw [prZ_of_mem (algebraMap_mem r), prZ_of_mem_ne (algebraMap_mem r) (by decide), add_zero]
  | add x y hx hy =>
    rw [map_add, map_add, add_add_add_comm, hx, hy]
  | ι_mul m x hx =>
    rw [prZ_zero_ι_mul, prZ_one_ι_mul, ← mul_add, add_comm, hx]

/-! ## Graded commutativity -/

/-- Two anticommuting vectors. -/
lemma ι_anti (a b : L) (x : E) : ι R a * (ι R b * x) = -(ι R b * (ι R a * x)) := by
  rw [← mul_assoc, ← mul_assoc, eq_neg_of_add_eq_zero_left (ι_add_mul_swap (R := R) a b),
    neg_mul]

lemma ι_ι (a : L) (x : E) : ι R a * (ι R a * x) = 0 := by
  rw [← mul_assoc, ι_sq_zero, zero_mul]

/-- **A vector twist-commutes** with everything: `m x = x̂ m`. -/
lemma ι_mul_comm (m : L) (x : E) : ι R m * x = involute x * ι R m := by
  induction x using induction with
  | alg r => rw [AlgHom.commutes, Algebra.commutes]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_mul]
  | ι_mul n x hx =>
    rw [ι_anti, hx, map_mul, involute_ι]
    noncomm_ring

lemma ι_mul_involute (m : L) (x : E) : ι R m * involute x = x * ι R m := by
  rw [ι_mul_comm, involute_involutive]

/-- **Graded commutativity**: even elements are central and odd elements twist-commute. -/
theorem mul_comm_parity (x : E) :
    (∀ y, prZ 0 x * y = y * prZ 0 x) ∧ (∀ y, prZ 1 x * y = involute y * prZ 1 x) := by
  refine parity_induction (Pe := fun x => ∀ y, x * y = y * x)
    (Po := fun x => ∀ y, x * y = involute y * x) (fun r y => Algebra.commutes r y)
    (fun y => by rw [zero_mul, mul_zero]) (fun x x' hx hx' y => by rw [add_mul, mul_add, hx, hx'])
    (fun x x' hx hx' y => by rw [add_mul, mul_add, hx, hx']) (fun m x _ hx y => ?_)
    (fun m x _ hx y => ?_) x
  · rw [mul_assoc, hx, ← mul_assoc, ι_mul_involute, mul_assoc]
  · rw [mul_assoc, hx, ← mul_assoc, ι_mul_comm, mul_assoc]

lemma mul_comm_even {x : E} (hx : x ∈ evenOdd Q₀ 0) (y : E) : x * y = y * x := by
  have h := (mul_comm_parity x).1 y
  rwa [prZ_of_mem hx] at h

lemma mul_comm_odd {x : E} (hx : x ∈ evenOdd Q₀ 1) (y : E) : x * y = involute y * x := by
  have h := (mul_comm_parity x).2 y
  rwa [prZ_of_mem hx] at h

/-! ## The even derivations `D_f` -/

/-- The step of the even derivation extending an endomorphism `f`. -/
noncomputable def dStep (f : L →ₗ[R] L) : L →ₗ[R] E × E →ₗ[R] E :=
  LinearMap.mk₂ R (fun m p => ι R (f m) * p.1 + ι R m * p.2)
    (fun m m' p => by simp only [map_add, add_mul]; abel)
    (fun c m p => by simp only [map_smul, smul_mul_assoc, smul_add])
    (fun m p q => by simp only [Prod.fst_add, Prod.snd_add, mul_add]; abel)
    (fun c m p => by simp only [Prod.smul_fst, Prod.smul_snd, mul_smul_comm, smul_add])

lemma dStep_apply (f : L →ₗ[R] L) (m : L) (p : E × E) :
    dStep f m p = ι R (f m) * p.1 + ι R m * p.2 := rfl

/-- **The even derivation extending `f`**: `D_f (m ∧ x) = f m ∧ x + m ∧ D_f x`. -/
noncomputable def D (f : L →ₗ[R] L) : E →ₗ[R] E :=
  foldr' Q₀ (dStep f) (fun m x fx => by
    rw [dStep_apply, dStep_apply, QuadraticMap.zero_apply, zero_smul, mul_add, ι_anti, ι_ι,
      add_zero, neg_add_cancel]) 0

lemma D_ι_mul (f : L →ₗ[R] L) (m : L) (x : E) :
    D f (ι R m * x) = ι R (f m) * x + ι R m * D f x :=
  foldr'_ι_mul _ _ _ _ _ _

lemma D_algebraMap (f : L →ₗ[R] L) (r : R) : D f (algebraMap R E r) = 0 := by
  rw [D, foldr'_algebraMap, smul_zero]

lemma D_one (f : L →ₗ[R] L) : D f 1 = 0 := by
  rw [← map_one (algebraMap R E), D_algebraMap]

lemma D_ι (f : L →ₗ[R] L) (m : L) : D f (ι R m) = ι R (f m) := by
  rw [← mul_one (ι R m), D_ι_mul, D_one, mul_zero, add_zero, mul_one]

/-- **`D_f` is a derivation.** -/
theorem D_mul (f : L →ₗ[R] L) (x y : E) : D f (x * y) = D f x * y + x * D f y := by
  induction x using induction with
  | alg r =>
    rw [D_algebraMap, zero_mul, zero_add, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul, add_mul]; abel
  | ι_mul m x hx =>
    rw [mul_assoc, D_ι_mul, hx, D_ι_mul]
    noncomm_ring

lemma D_add (f g : L →ₗ[R] L) (x : E) : D (f + g) x = D f x + D g x := by
  induction x using induction with
  | alg r => rw [D_algebraMap, D_algebraMap, D_algebraMap, add_zero]
  | add x x' hx hx' => rw [map_add, map_add, map_add, hx, hx']; abel
  | ι_mul m x hx =>
    rw [D_ι_mul, D_ι_mul, D_ι_mul, hx, LinearMap.add_apply, map_add, add_mul, mul_add]; abel

lemma D_smul (c : R) (f : L →ₗ[R] L) (x : E) : D (c • f) x = c • D f x := by
  induction x using induction with
  | alg r => rw [D_algebraMap, D_algebraMap, smul_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', smul_add]
  | ι_mul m x hx =>
    rw [D_ι_mul, D_ι_mul, hx, LinearMap.smul_apply, map_smul, smul_mul_assoc, mul_smul_comm,
      smul_add]

/-- **The commutator of the derivations**: `[D_f, D_g] = D_[f, g]`. -/
theorem D_comm (f g : L →ₗ[R] L) (x : E) :
    D f (D g x) - D g (D f x) = D (f ∘ₗ g - g ∘ₗ f) x := by
  induction x using induction with
  | alg r => rw [D_algebraMap, D_algebraMap, map_zero, map_zero, sub_zero, D_algebraMap]
  | add x x' hx hx' =>
    rw [map_add, map_add, map_add, map_add, map_add, ← hx, ← hx']; abel
  | ι_mul m x hx =>
    rw [D_ι_mul, D_ι_mul, map_add, map_add, D_ι_mul, D_ι_mul, D_ι_mul, D_ι_mul, D_ι_mul,
      ← hx, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_sub, sub_mul,
      mul_sub]
    abel

/-! ## The derivations `D_m` of the adjoint action -/

variable (R L) in
/-- **The derivation `D_m` extending `ad m`**, linear in `m`. -/
noncomputable def Dm : L →ₗ[R] E →ₗ[R] E where
  toFun m := D (LieAlgebra.ad R L m)
  map_add' m n := LinearMap.ext fun x => by rw [map_add, D_add]; rfl
  map_smul' c m := LinearMap.ext fun x => by rw [map_smul, D_smul]; rfl

lemma Dm_apply (m : L) (x : E) : Dm R L m x = D (LieAlgebra.ad R L m) x := rfl

lemma Dm_ι_mul (m n : L) (x : E) : Dm R L m (ι R n * x) = ι R ⁅m, n⁆ * x + ι R n * Dm R L m x :=
  D_ι_mul _ _ _

lemma Dm_algebraMap (m : L) (r : R) : Dm R L m (algebraMap R E r) = 0 := D_algebraMap _ _

lemma Dm_one (m : L) : Dm R L m 1 = 0 := D_one _

lemma Dm_ι (m n : L) : Dm R L m (ι R n) = ι R ⁅m, n⁆ := D_ι _ _

lemma Dm_mul (m : L) (x y : E) : Dm R L m (x * y) = Dm R L m x * y + x * Dm R L m y :=
  D_mul _ _ _

lemma Dm_self (m : L) (x : E) : Dm R L m (ι R m * x) = ι R m * Dm R L m x := by
  rw [Dm_ι_mul, lie_self, map_zero, zero_mul, zero_add]

/-- **`m ↦ D_m` is a Lie morphism**: `[D_m, D_n] = D_[m, n]`. -/
theorem Dm_comm (m n : L) (x : E) :
    Dm R L m (Dm R L n x) - Dm R L n (Dm R L m x) = Dm R L ⁅m, n⁆ x := by
  rw [Dm_apply, Dm_apply, Dm_apply, Dm_apply, D_comm, Dm_apply]
  congr 2
  ext k
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LieAlgebra.ad_apply, lie_lie]

/-! ## The Chevalley–Eilenberg operator -/

/-- The step of the Chevalley–Eilenberg operator. -/
noncomputable def δStep : L →ₗ[R] E × E →ₗ[R] E :=
  LinearMap.mk₂ R (fun m p => -Dm R L m p.1 - ι R m * p.2)
    (fun m m' p => by simp only [map_add, LinearMap.add_apply, add_mul]; abel)
    (fun c m p => by simp only [map_smul, LinearMap.smul_apply, smul_mul_assoc, smul_sub,
      smul_neg])
    (fun m p q => by simp only [Prod.fst_add, Prod.snd_add, mul_add, map_add]; abel)
    (fun c m p => by simp only [Prod.smul_fst, Prod.smul_snd, mul_smul_comm, map_smul, smul_sub,
      smul_neg])

lemma δStep_apply (m : L) (p : E × E) : δStep (R := R) m p = -Dm R L m p.1 - ι R m * p.2 := rfl

variable (R L) in
/-- **The Chevalley–Eilenberg operator** `Δ (m ∧ x) = -D_m x - m ∧ Δ x`. -/
noncomputable def Δ : E →ₗ[R] E :=
  foldr' Q₀ δStep (fun m x fx => by
    rw [δStep_apply, δStep_apply, QuadraticMap.zero_apply, zero_smul, Dm_self, mul_sub, mul_neg,
      ι_ι]
    simp) 0

lemma Δ_ι_mul (m : L) (x : E) : Δ R L (ι R m * x) = -Dm R L m x - ι R m * Δ R L x :=
  foldr'_ι_mul _ _ _ _ _ _

lemma Δ_algebraMap (r : R) : Δ R L (algebraMap R E r) = 0 := by
  rw [Δ, foldr'_algebraMap, smul_zero]

lemma Δ_one : Δ R L (1 : E) = 0 := by
  rw [← map_one (algebraMap R E), Δ_algebraMap]

lemma Δ_ι (m : L) : Δ R L (ι R m) = 0 := by
  rw [← mul_one (ι R m), Δ_ι_mul, Δ_one, Dm_one, mul_zero, neg_zero, sub_zero]

/-- **`Δ` commutes with the derivations `D_m`.** -/
theorem Δ_Dm (m : L) (x : E) : Δ R L (Dm R L m x) = Dm R L m (Δ R L x) := by
  induction x using induction with
  | alg r => rw [Dm_algebraMap, Δ_algebraMap, map_zero, map_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | ι_mul n x hx =>
    have h := Dm_comm (R := R) m n x
    rw [Dm_ι_mul, map_add, Δ_ι_mul, Δ_ι_mul, Δ_ι_mul, hx, map_sub, map_neg, Dm_ι_mul]
    rw [← h]
    abel

/-- **`Δ² = 0`.** -/
theorem Δ_Δ (x : E) : Δ R L (Δ R L x) = 0 := by
  induction x using induction with
  | alg r => rw [Δ_algebraMap, map_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', add_zero]
  | ι_mul n x hx =>
    rw [Δ_ι_mul, map_sub, map_neg, Δ_Dm, Δ_ι_mul, hx, mul_zero, sub_zero]
    abel

/-! ## The deviation -/

variable (R L) in
/-- **The deviation of `Δ`** from being a derivation:
`⟨x, y⟩ = Δ (x y) - (Δ x) y - x̂ (Δ y)`. -/
noncomputable def dv : E →ₗ[R] E →ₗ[R] E :=
  LinearMap.mk₂ R (fun x y => Δ R L (x * y) - Δ R L x * y - involute x * Δ R L y)
    (fun x x' y => by simp only [add_mul, map_add]; abel)
    (fun c x y => by simp only [smul_mul_assoc, map_smul, smul_sub])
    (fun x y y' => by simp only [mul_add, map_add]; abel)
    (fun c x y => by simp only [mul_smul_comm, map_smul, smul_sub])

lemma dv_apply (x y : E) :
    dv R L x y = Δ R L (x * y) - Δ R L x * y - involute x * Δ R L y := rfl

lemma dv_algebraMap (r : R) (y : E) : dv R L (algebraMap R E r) y = 0 := by
  rw [dv_apply, Δ_algebraMap, zero_mul, sub_zero, AlgHom.commutes, ← Algebra.smul_def,
    ← Algebra.smul_def, map_smul, sub_self]

/-- **The recursion of the deviation**: `⟨m ∧ x, y⟩ = -x D_m y - m ∧ ⟨x, y⟩`. -/
theorem dv_ι_mul (m : L) (x y : E) :
    dv R L (ι R m * x) y = -(x * Dm R L m y) - ι R m * dv R L x y := by
  rw [dv_apply, dv_apply, mul_assoc, Δ_ι_mul, Δ_ι_mul, Dm_mul, map_mul involute (ι R m) x,
    involute_ι]
  noncomm_ring

lemma dv_ι (m : L) (y : E) : dv R L (ι R m) y = -Dm R L m y := by
  rw [← mul_one (ι R m), dv_ι_mul, ← map_one (algebraMap R E), dv_algebraMap, map_one, one_mul,
    mul_zero, sub_zero]

/-- **On vectors, the deviation is the opposite of the bracket.** -/
lemma dv_ι_ι (m n : L) : dv R L (ι R m) (ι R n) = -ι R ⁅m, n⁆ := by
  rw [dv_ι, Dm_ι]

/-- **`Δ` is of order at most two**: the deviation is a graded derivation in its second argument,
`⟨x, y z⟩ = ⟨x, y⟩ z + ŷ ⟨x, z⟩` for `x` even and `⟨x, y⟩ z + y ⟨x, z⟩` for `x` odd. -/
theorem dv_mul_parity (x : E) :
    (∀ y z, dv R L (prZ 0 x) (y * z)
      = dv R L (prZ 0 x) y * z + involute y * dv R L (prZ 0 x) z) ∧
    (∀ y z, dv R L (prZ 1 x) (y * z) = dv R L (prZ 1 x) y * z + y * dv R L (prZ 1 x) z) := by
  refine parity_induction
    (Pe := fun x => ∀ y z, dv R L x (y * z) = dv R L x y * z + involute y * dv R L x z)
    (Po := fun x => ∀ y z, dv R L x (y * z) = dv R L x y * z + y * dv R L x z)
    (fun r y z => by rw [dv_algebraMap, dv_algebraMap, dv_algebraMap, zero_mul, mul_zero,
      add_zero])
    (fun y z => by simp only [map_zero, LinearMap.zero_apply, zero_mul, mul_zero, add_zero])
    (fun x x' hx hx' y z => by
      simp only [map_add, LinearMap.add_apply, add_mul, mul_add, hx y z, hx' y z]; abel)
    (fun x x' hx hx' y z => by
      simp only [map_add, LinearMap.add_apply, add_mul, mul_add, hx y z, hx' y z]; abel)
    (fun m x hxo hx y z => ?_) (fun m x hxe hx y z => ?_) x
  · rw [dv_ι_mul, dv_ι_mul, dv_ι_mul, hx, Dm_mul, mul_add, mul_add, ← mul_assoc x y,
      mul_comm_odd hxo y, ← mul_assoc (ι R m) y, ι_mul_comm m y]
    noncomm_ring
  · rw [dv_ι_mul, dv_ι_mul, dv_ι_mul, hx, Dm_mul, mul_add, mul_add, ← mul_assoc x y,
      mul_comm_even hxe y, ← mul_assoc (ι R m) (involute y), ι_mul_involute m y]
    noncomm_ring

lemma dv_mul_even {x : E} (hx : x ∈ evenOdd Q₀ 0) (y z : E) :
    dv R L x (y * z) = dv R L x y * z + involute y * dv R L x z := by
  have h := (dv_mul_parity x).1 y z
  rwa [prZ_of_mem hx] at h

lemma dv_mul_odd {x : E} (hx : x ∈ evenOdd Q₀ 1) (y z : E) :
    dv R L x (y * z) = dv R L x y * z + y * dv R L x z := by
  have h := (dv_mul_parity x).2 y z
  rwa [prZ_of_mem hx] at h

/-! ## Parities of the operations -/

lemma mul_mem' {i j k : ZMod 2} (h : i + j = k) {x y : E} (hx : x ∈ evenOdd Q₀ i)
    (hy : y ∈ evenOdd Q₀ j) : x * y ∈ evenOdd Q₀ k :=
  h ▸ SetLike.mul_mem_graded hx hy

lemma zmod2_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma involute_mem {i : ZMod 2} {x : E} (hx : x ∈ evenOdd Q₀ i) : involute x ∈ evenOdd Q₀ i := by
  obtain rfl | rfl := zmod2_cases i
  · rw [CliffordAlgebra.involute_eq_of_mem_even hx]
    exact hx
  · rw [CliffordAlgebra.involute_eq_of_mem_odd hx]
    exact Submodule.neg_mem _ hx

lemma mem_of_parity {P : ZMod 2 → E → Prop} (h : ∀ x, P 0 (prZ 0 x) ∧ P 1 (prZ 1 x)) {i : ZMod 2}
    {x : E} (hx : x ∈ evenOdd Q₀ i) : P i x := by
  obtain rfl | rfl := zmod2_cases i
  · have := (h x).1
    rwa [prZ_of_mem hx] at this
  · have := (h x).2
    rwa [prZ_of_mem hx] at this

/-- **`D_f` is even.** -/
lemma D_mem (f : L →ₗ[R] L) {i : ZMod 2} {x : E} (hx : x ∈ evenOdd Q₀ i) :
    D f x ∈ evenOdd Q₀ i := by
  refine mem_of_parity (P := fun i x => D f x ∈ evenOdd Q₀ i) (fun x => parity_induction
    (Pe := fun x => D f x ∈ evenOdd Q₀ 0) (Po := fun x => D f x ∈ evenOdd Q₀ 1)
    (fun r => by beta_reduce; rw [D_algebraMap]; exact Submodule.zero_mem _)
    (by beta_reduce; rw [map_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by beta_reduce; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun x y hx hy => by beta_reduce; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun m x hx h => ?_) (fun m x hx h => ?_) x) hx
  · beta_reduce
    rw [D_ι_mul]
    exact Submodule.add_mem _ (mul_mem' (by decide) (ι_mem _) hx) (mul_mem' (by decide) (ι_mem _) h)
  · beta_reduce
    rw [D_ι_mul]
    exact Submodule.add_mem _ (mul_mem' (by decide) (ι_mem _) hx) (mul_mem' (by decide) (ι_mem _) h)

/-- **`Δ` is odd.** -/
lemma Δ_mem {i : ZMod 2} {x : E} (hx : x ∈ evenOdd Q₀ i) : Δ R L x ∈ evenOdd Q₀ (i + 1) := by
  refine mem_of_parity (P := fun i x => Δ R L x ∈ evenOdd Q₀ (i + 1)) (fun x => parity_induction
    (Pe := fun x => Δ R L x ∈ evenOdd Q₀ (0 + 1)) (Po := fun x => Δ R L x ∈ evenOdd Q₀ (1 + 1))
    (fun r => by beta_reduce; rw [Δ_algebraMap]; exact Submodule.zero_mem _)
    (by beta_reduce; rw [map_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by beta_reduce; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun x y hx hy => by beta_reduce; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun m x hx h => ?_) (fun m x hx h => ?_) x) hx
  · beta_reduce
    rw [Δ_ι_mul]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (D_mem _ hx))
      (mul_mem' (by decide) (ι_mem _) h)
  · beta_reduce
    rw [Δ_ι_mul]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (D_mem _ hx))
      (mul_mem' (by decide) (ι_mem _) h)

/-- **The deviation is odd.** -/
lemma dv_mem {i j : ZMod 2} {x y : E} (hx : x ∈ evenOdd Q₀ i) (hy : y ∈ evenOdd Q₀ j) :
    dv R L x y ∈ evenOdd Q₀ (i + j + 1) := by
  rw [dv_apply]
  refine Submodule.sub_mem _ (Submodule.sub_mem _ (Δ_mem (mul_mem' rfl hx hy))
    (mul_mem' (by ring) (Δ_mem hx) hy)) (mul_mem' (by ring) (involute_mem hx) (Δ_mem hy))

/-! ## The super module -/

/-- The parity of a Boolean. -/
def bz (b : Bool) : ZMod 2 := cond b 1 0

lemma bz_xor (a b : Bool) : bz (xor a b) = bz a + bz b := by
  cases a <;> cases b <;> decide

lemma bz_not (a : Bool) : bz (!a) = bz a + 1 := by
  cases a <;> decide

lemma bz_injective : Function.Injective bz := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- **The exterior algebra is a super module**, by its parity components. -/
noncomputable instance instSuperMod : SuperMod R E where
  pr b := prZ (bz b)
  pr_add x := prZ_add x
  pr_pr b b' x := by
    split_ifs with h
    · subst h
      exact prZ_of_mem (prZ_mem _ _)
    · exact prZ_of_mem_ne (prZ_mem _ _) fun h' => h (bz_injective h').symm

lemma isP_iff (p : Bool) (x : E) : EndGr.IsP (R := R) p x ↔ x ∈ evenOdd Q₀ (bz p) :=
  ⟨fun h => h ▸ prZ_mem _ _, fun h => prZ_of_mem h⟩

lemma involute_eq_σ {p : Bool} {x : E} (hx : x ∈ evenOdd Q₀ (bz p)) :
    involute x = GerBV.σ R p • x := by
  cases p
  · rw [CliffordAlgebra.involute_eq_of_mem_even hx, GerBV.σ_false, one_smul]
  · rw [CliffordAlgebra.involute_eq_of_mem_odd hx, GerBV.σ_true, neg_one_smul]

/-- **Graded commutativity**: `x y = σ(|x| |y|) y x`. -/
lemma mul_comm_σ {p q : Bool} {x y : E} (hx : x ∈ evenOdd Q₀ (bz p))
    (hy : y ∈ evenOdd Q₀ (bz q)) : x * y = GerBV.σ R (p && q) • (y * x) := by
  cases p
  · rw [mul_comm_even hx, Bool.false_and, GerBV.σ_false, one_smul]
  · rw [mul_comm_odd hx, involute_eq_σ hy, Bool.true_and, smul_mul_assoc]

/-- **The deviation is graded symmetric**: `⟨x, y⟩ = σ(|x| |y|) ⟨y, x⟩`. -/
lemma dv_comm {p q : Bool} {x y : E} (hx : x ∈ evenOdd Q₀ (bz p))
    (hy : y ∈ evenOdd Q₀ (bz q)) : dv R L x y = GerBV.σ R (p && q) • dv R L y x := by
  have c1 := congrArg (Δ R L) (mul_comm_σ hx hy)
  have c2 := mul_comm_σ (R := R) (L := L) (p := !p) (q := q) (by rw [bz_not]; exact Δ_mem hx) hy
  have c3 := mul_comm_σ (R := R) (L := L) (p := p) (q := !q) hx (by rw [bz_not]; exact Δ_mem hy)
  rw [map_smul] at c1
  rw [dv_apply, dv_apply, involute_eq_σ hx, involute_eq_σ hy]
  cases p <;> cases q <;> simp at c1 c2 c3 ⊢
  · rw [c1, c2, c3]; abel
  · rw [c1, c2, c3]; abel
  · rw [c1, c2, c3]; abel
  · rw [c1, c2, c3]; module

/-! ## The Gerstenhaber algebra -/

lemma dev_eq {p : Bool} {x : E} (hx : x ∈ evenOdd Q₀ (bz p)) (y : E) :
    GerBV.dev (LinearMap.mul R E) (Δ R L) p x y = dv R L x y := by
  rw [dv_apply, involute_eq_σ hx, smul_mul_assoc]
  rfl

/-- **The Leibniz rule**: `⟨x, y z⟩ = ⟨x, y⟩ z + σ((|x| + 1) |y|) y ⟨x, z⟩`. -/
lemma dv_mul_σ {p q : Bool} {x y : E} (hx : x ∈ evenOdd Q₀ (bz p)) (hy : y ∈ evenOdd Q₀ (bz q))
    (z : E) :
    dv R L x (y * z) = dv R L x y * z + GerBV.σ R ((!p) && q) • (y * dv R L x z) := by
  cases p
  · rw [dv_mul_even hx, involute_eq_σ hy, smul_mul_assoc]
    rfl
  · rw [dv_mul_odd hx, Bool.not_true, Bool.false_and, GerBV.σ_false, one_smul]

/-- **The Jacobi identity** of the deviation. -/
lemma dv_jacobi {p q : Bool} {x y : E} (hx : x ∈ evenOdd Q₀ (bz p))
    (hy : y ∈ evenOdd Q₀ (bz q)) (z : E) :
    dv R L (dv R L x y) z + GerBV.σ R p • dv R L x (dv R L y z)
      + GerBV.σ R ((!p) && q) • dv R L y (dv R L x z) = 0 := by
  have J := GerBV.dev_jacobi (μ := LinearMap.mul R E) (Δ := Δ R L)
    (H := fun p x => x ∈ evenOdd Q₀ (bz p)) Δ_Δ
    (fun p q x y z hx hy => by
      simp only [dev_eq hx, LinearMap.mul_apply']
      exact dv_mul_σ hx hy z)
    (fun p x hx => by beta_reduce at hx ⊢; rw [bz_not]; exact Δ_mem hx) z hx hy
  have hxy : dv R L x y ∈ evenOdd Q₀ (bz (!(xor p q))) := by
    rw [bz_not, bz_xor]
    exact dv_mem hx hy
  rw [dev_eq hy, dev_eq hx, dev_eq hx, dev_eq hxy, dev_eq hx, dev_eq hy] at J
  cases p <;> cases q <;> simp at J ⊢
  · rw [J]; abel
  · rw [J]; abel
  · rw [J]; module
  · rw [J]; module

variable (R L) in
/-- The wedge product, as a binary operation. -/
noncomputable def mulOp : EndOp R E (Fin 2) := FreeBin.bilinOp (LinearMap.mul R E)

variable (R L) in
/-- The deviation of `Δ`, as a binary operation. -/
noncomputable def dvOp : EndOp R E (Fin 2) := FreeBin.bilinOp (dv R L)

lemma mulOp_apply (x y : E) : mulOp R L ![x, y] = x * y := rfl

lemma dvOp_apply (x y : E) : dvOp R L ![x, y] = dv R L x y := rfl

/-- A binary operation sending inputs of parities `p, q` to the parity `b + p + q` is of parity
`b`. -/
lemma parML_two {b : Bool} {f : EndOp R E (Fin 2)}
    (h : ∀ p q x y, x ∈ evenOdd Q₀ (bz p) → y ∈ evenOdd Q₀ (bz q) →
      f ![x, y] ∈ evenOdd Q₀ (bz b + bz p + bz q)) :
    parML R E b f = f := by
  refine ext_hom fun c v hv => ?_
  rw [parML_apply_hom hv, EndGr.vec_two v, EndGr.vec_two c, Ger.tot_two]
  refine prZ_of_mem ?_
  rw [bz_xor, bz_xor, ← add_assoc]
  exact h _ _ _ _ ((isP_iff _ _).1 (hv 0)) ((isP_iff _ _).1 (hv 1))

/-- **The exterior algebra of a Lie algebra is a Gerstenhaber algebra** under the wedge product
and the deviation of the Chevalley–Eilenberg operator. -/
theorem isGer : Ger.IsGer (mulOp R L) (dvOp R L) where
  par_m := parML_two fun p q x y hx hy => mul_mem' (by simp [bz]) hx hy
  par_l := parML_two fun p q x y hx hy => by
    rw [dvOp_apply]
    convert dv_mem hx hy using 1
    simp only [bz, cond_true]
    ring_nf
  comm p q x y hx hy := mul_comm_σ ((isP_iff _ _).1 hx) ((isP_iff _ _).1 hy)
  symm p q x y hx hy := dv_comm ((isP_iff _ _).1 hx) ((isP_iff _ _).1 hy)
  assoc p q r x y z _ _ _ := mul_assoc x y z
  leibniz p q r x y z hx hy _ := dv_mul_σ ((isP_iff _ _).1 hx) ((isP_iff _ _).1 hy) z
  jacobi p q r x y z hx hy _ := dv_jacobi ((isP_iff _ _).1 hx) ((isP_iff _ _).1 hy) z

variable (R L) in
/-- **The exterior algebra of a Lie algebra is an algebra over the Gerstenhaber operad.** -/
noncomputable def gerAlg : GrAlgebra R E (GerOp R) :=
  Ger.algebraEquiv.symm ⟨(mulOp R L, dvOp R L), isGer⟩

lemma sv_gerAlg_mul :
    EndGr.sv ((gerAlg R L).app _ (FreeGr.presGen (Ger.rel R) GerGen.mul)) = mulOp R L :=
  congrArg (fun z => z.1.1) (Ger.algebraEquiv.apply_symm_apply
    (⟨(mulOp R L, dvOp R L), isGer⟩ : {ml : EndOp R E (Fin 2) × EndOp R E (Fin 2) //
      Ger.IsGer ml.1 ml.2}))

lemma sv_gerAlg_br :
    EndGr.sv ((gerAlg R L).app _ (FreeGr.presGen (Ger.rel R) GerGen.br)) = dvOp R L :=
  congrArg (fun z => z.1.2) (Ger.algebraEquiv.apply_symm_apply
    (⟨(mulOp R L, dvOp R L), isGer⟩ : {ml : EndOp R E (Fin 2) × EndOp R E (Fin 2) //
      Ger.IsGer ml.1 ml.2}))

end ExtBV

end Operad
