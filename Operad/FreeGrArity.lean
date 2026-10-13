/-
# Counting arities in free graded operads on reduced species

A graded linear species `V` is **reduced** when it vanishes in arities at most one. Endomorphisms
acting on each arity by a scalar (`GrSpEnd.scalar`) extend to derivations of `T(V)` counting the
vertices of a tree with weights depending on their arities, linearly in the weights
(`FreeGrL.derSp_scalar_add`, `FreeGrL.derSp_scalar_smul`).

* **The arity excess**: the derivation weighting a vertex with `k` inputs by `k - 1` is the scalar
  `|A| - 1` on `T(V)(A)` (`FreeGrL.derSp_excess`).
* For weights that are natural numbers on the arities at least two, `T(V)` is the sum of the
  eigenspaces for the natural numbers (`FreeGrL.iSup_eig_scalar`), so **an eigenvector for a
  negative integer vanishes**. Hence on a reduced species: the trees of `T(V)(A)` have fewer than
  `|A|` vertices (`FreeGrL.eig_card_eq_bot`); **the truncation to the arities at most `m` is the
  identity on `T(V)(A)` for `|A| ≤ m`** (`FreeGrL.mapSp_trunc_of_card_le`), and on the trees with
  at least two vertices for `|A| = m + 1` (`FreeGrL.mapSp_trunc_of_two_le`).
-/
import Operad.FreeGrKunneth

universe u v

namespace Operad

open Sym GerBV

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

variable (R V) in
/-- **The endomorphism acting on each arity by a scalar.** -/
def GrSpEnd.scalar (f : ℕ → R) : GrSpEnd R V false where
  app A _ _ := f (Fintype.card A) • LinearMap.id
  app_map {A B} _ _ _ _ σ' x := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Fintype.card_congr σ']
  app_par c x := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Bool.xor_false]

@[simp] lemma GrSpEnd.scalar_app (f : ℕ → R) {A : Type} [Fintype A] [DecidableEq A] (x : V A) :
    (GrSpEnd.scalar R V f).app A x = f (Fintype.card A) • x := rfl

namespace FreeGrL

/-- **Linear combinations of endomorphisms extend to linear combinations of derivations.** -/
theorem derSp_lin {e : Bool} (a b c : GrSpEnd R V e) (α β : R)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A),
      c.app A x = α • a.app A x + β • b.app A x)
    {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (derSp c).app A x = α • (derSp a).app A x + β • (derSp b).app A x := by
  have key := submodule_eq_top (R := R) (V := V)
    (fun A _ _ => LinearMap.ker ((derSp c).app A - α • (derSp a).app A - β • (derSp b).app A))
    (fun A _ _ e => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, GrDer.app_map,
        GrDer.app_one, map_zero, smul_zero, sub_zero])
    (fun n v => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, derSp_ι, h,
        map_add, map_smul]
      abel)
    (fun A B _ _ _ _ σ' x hx => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, GrDer.app_map]
        at hx ⊢
      rw [sub_sub, sub_eq_zero] at hx ⊢
      rw [hx, map_add, map_smul, map_smul])
    (fun A B _ _ _ _ r x y hx hy => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_sub, sub_eq_zero,
        LinearMap.add_apply, LinearMap.smul_apply] at hx hy ⊢
      rw [(derSp c).app_comp, (derSp a).app_comp, (derSp b).app_comp, GrOperadHom.id_app,
        GrOperadHom.id_app, hx, hy]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_add]
      abel) A
  have hx : x ∈ (⊤ : Submodule R (FreeGrL R V A)) := Submodule.mem_top
  rw [← key, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, sub_sub, sub_eq_zero] at hx
  exact hx

/-- **The arity excess**: weighting a vertex with `k` inputs by `k - 1` multiplies `T(V)(A)` by
`|A| - 1`. -/
theorem derSp_excess {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (derSp (GrSpEnd.scalar R V fun n => (n : R) - 1)).app A x
      = ((Fintype.card A : R) - 1) • x := by
  set E := derSp (GrSpEnd.scalar R V fun n => (n : R) - 1)
  have key := submodule_eq_top (R := R) (V := V)
    (fun A _ _ => LinearMap.ker (E.app A - ((Fintype.card A : R) - 1) • LinearMap.id))
    (fun A _ _ e => by
      have hA : Fintype.card A = 1 := by rw [← Fintype.card_congr e, Fintype.card_unit]
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        GrDer.app_map, GrDer.app_one, map_zero, hA, Nat.cast_one, sub_self, zero_smul, sub_zero])
    (fun n v => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, E, derSp_ι, GrSpEnd.scalar_app, map_smul, Fintype.card_fin,
        sub_self])
    (fun A B _ _ _ _ σ' x hx => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero] at hx ⊢
      rw [GrDer.app_map, hx, map_smul, Fintype.card_congr σ'])
    (fun A B _ _ _ _ r x y hx hy => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero] at hx hy ⊢
      rw [E.app_comp, GrOperadHom.id_app, GrOperadHom.id_app, GrOperad.tw_false, hx, hy,
        LinearMap.map_smul₂, map_smul, ← add_smul]
      congr 1
      have h1 : 1 ≤ Fintype.card A := Fintype.card_pos_iff.2 ⟨r⟩
      rw [Fintype.card_sum, Reg.card_without, Nat.cast_add, Nat.cast_sub h1, Nat.cast_one]
      ring) A
  have hx : x ∈ (⊤ : Submodule R (FreeGrL R V A)) := Submodule.mem_top
  rw [← key, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at hx
  exact hx

/-- **Scalar weights that are natural numbers on the arities at least two** have eigenspaces
spanning the free graded operad on a reduced species. -/
theorem iSup_eig_scalar (hred : ∀ (B : Type) [Fintype B] [DecidableEq B],
      Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    (f : ℕ → R) (hf : ∀ n, 2 ≤ n → ∃ j : ℕ, f n = j) (A : Type) [Fintype A] [DecidableEq A] :
    ⨆ j : ℕ, eig R V (GrSpEnd.scalar R V f) j A = ⊤ :=
  iSup_eig_eq_top (fun B _ _ v => by
    rcases le_or_gt (Fintype.card B) 1 with h | h
    · rw [hred B h v]; exact zero_mem _
    · obtain ⟨j, hj⟩ := hf _ h
      exact Submodule.mem_iSup_of_mem j (by
        rw [Module.End.mem_eigenspace_iff, GrSpEnd.scalar_app, hj])) A

/-- The components, in the eigenspaces of a diagonalizable endomorphism, of an eigenvector of a
commuting endomorphism are eigenvectors, over a `ℚ`-algebra. -/
lemma _root_.Operad.exists_finsupp_eig_inf [Algebra ℚ R] {M : Type*} [AddCommGroup M] [Module R M]
    (B N : M →ₗ[R] M) (hc : ∀ x, B (N x) = N (B x))
    (htop : ⨆ j : ℕ, Module.End.eigenspace B (j : R) = ⊤) (k : R) {y : M} (hy : N y = k • y) :
    ∃ f : ℕ →₀ M, (∀ j : ℕ, f j ∈ Module.End.eigenspace B (j : R)) ∧
      (∀ j : ℕ, N (f j) = k • f j) ∧
      f.sum (fun _ v => v) = y := by
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ y).1
    (htop ▸ Submodule.mem_top : y ∈ ⨆ j : ℕ, Module.End.eigenspace B (j : R))
  let φ : M →ₗ[R] M := N - k • LinearMap.id
  have hφ : ∀ j : ℕ, φ (f j) ∈ Module.End.eigenspace B (j : R) := fun j => by
    rw [Module.End.mem_eigenspace_iff]
    simp only [φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul]
    rw [hc, Module.End.mem_eigenspace_iff.1 (hf j), map_smul]
    module
  refine ⟨f, hf, fun j => ?_, rfl⟩
  have h := iSupIndep_finsupp_eq_zero (iSupIndep_eigenspace_nat B) (f.mapRange φ (map_zero φ))
    (fun j => by rw [Finsupp.mapRange_apply]; exact hφ j)
    (by
      rw [Finsupp.sum_mapRange_index (fun _ => rfl), ← map_finsuppSum]
      simp only [φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hy,
        sub_self]) j
  rw [Finsupp.mapRange_apply] at h
  simpa only [φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] using h

variable (R V) in
/-- **The truncation to the arities at most `m`.** -/
def _root_.Operad.GrSpEnd.trunc (m : ℕ) : GrSpEnd R V false :=
  GrSpEnd.scalar R V fun n => if n ≤ m then 1 else 0

lemma _root_.Operad.GrSpEnd.trunc_app (m : ℕ) {A : Type} [Fintype A] [DecidableEq A] (x : V A) :
    (GrSpEnd.trunc R V m).app A x = (if Fintype.card A ≤ m then 1 else 0 : R) • x := rfl

lemma _root_.Operad.GrSpEnd.trunc_trunc (m : ℕ) (A : Type) [Fintype A] [DecidableEq A] (x : V A) :
    (GrSpEnd.trunc R V m).app A ((GrSpEnd.trunc R V m).app A x)
      = (GrSpEnd.trunc R V m).app A x := by
  simp only [GrSpEnd.trunc_app, smul_smul]
  split_ifs <;> simp

/-! ### Vertices of the trees -/

variable [Algebra ℚ R]
  (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
include hred

/-- **A tree with vertices of at least two inputs has fewer vertices than leaves.** -/
theorem eig_card_eq_bot {A : Type} [Fintype A] [DecidableEq A] {k : ℕ}
    (hk : Fintype.card A ≤ k) {x : FreeGrL R V A} (hx : x ∈ eig R V (GrSpEnd.id R V) k A) :
    x = 0 := by
  have htop := iSup_eig_scalar hred (fun n => (n : R) - 2)
    (fun n hn => ⟨n - 2, by rw [Nat.cast_sub hn]; norm_num⟩) A
  refine eq_zero_of_eigen_neg R _ htop (m := k + 1 - Fintype.card A) (by omega) ?_
  rw [derSp_lin (GrSpEnd.scalar R V fun n => (n : R) - 1) (GrSpEnd.id R V) _ 1 (-1)
    (fun A _ _ v => by simp only [GrSpEnd.scalar_app, GrSpEnd.id_app]; module) x,
    derSp_excess, mem_eig.1 hx, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  module

/-- **The truncation to the arities at most `m` is the identity in arities at most `m`.** -/
theorem mapSp_trunc_of_card_le {m : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (hA : Fintype.card A ≤ m) (x : FreeGrL R V A) :
    (mapSp (GrSpEnd.trunc R V m).toHom).app A x = x := by
  set τ := GrSpEnd.trunc R V m
  have hτ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), τ.app A (τ.app A x) = τ.app A x :=
    GrSpEnd.trunc_trunc m
  have hbot : ∀ j : ℕ, ∀ z ∈ eig R V (GrSpEnd.compl R V τ) (j + 1) A, z = 0 := fun j z hz => by
    have htop := iSup_eig_scalar hred
      (fun n => ((n : R) - 1) + (-(m : R)) * (1 - if n ≤ m then 1 else 0))
      (fun n hn => by
        by_cases h : n ≤ m
        · exact ⟨n - 1, by
            beta_reduce
            rw [if_pos h, Nat.cast_sub (by omega)]
            ring⟩
        · exact ⟨n - 1 - m, by
            beta_reduce
            rw [if_neg h, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
            ring⟩) A
    have hmj : Fintype.card A ≤ m * (j + 1) := le_trans hA (Nat.le_mul_of_pos_right _ (by omega))
    refine eq_zero_of_eigen_neg R _ htop (m := m * (j + 1) + 1 - Fintype.card A)
      (by omega) ?_
    rw [derSp_lin (GrSpEnd.scalar R V fun n => (n : R) - 1) (GrSpEnd.compl R V τ) _ 1 (-(m : R))
      (fun A _ _ v => by
        simp only [GrSpEnd.scalar_app, GrSpEnd.compl_app, τ, GrSpEnd.trunc_app]
        module) z,
      derSp_excess, mem_eig.1 hz, Nat.cast_sub (by omega)]
    push_cast
    module
  have hpos := sub_mapSp_mem τ hτ x
  have hle : ⨆ j : ℕ, eig R V (GrSpEnd.compl R V τ) (j + 1) A ≤ ⊥ :=
    iSup_le fun j z hz => (Submodule.mem_bot R).2 (hbot j z hz)
  exact (sub_eq_zero.1 ((Submodule.mem_bot R).1 (hle hpos))).symm

/-- **The truncation to the arities at most `m` is the identity on the trees with at least two
vertices in arity `m + 1`.** -/
theorem mapSp_trunc_of_two_le {m : ℕ} (hm : 1 ≤ m) {A : Type} [Fintype A] [DecidableEq A]
    (hA : Fintype.card A = m + 1) {k : ℕ} (hk : 2 ≤ k) {x : FreeGrL R V A}
    (hx : x ∈ eig R V (GrSpEnd.id R V) k A) :
    (mapSp (GrSpEnd.trunc R V m).toHom).app A x = x := by
  set τ := GrSpEnd.trunc R V m
  have hτ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), τ.app A (τ.app A x) = τ.app A x :=
    GrSpEnd.trunc_trunc m
  have hBN : ∀ y, (derSp (GrSpEnd.compl R V τ)).app A ((derSp (GrSpEnd.id R V)).app A y)
      = (derSp (GrSpEnd.id R V)).app A ((derSp (GrSpEnd.compl R V τ)).app A y) := fun y => by
    have := derSp_comm (a := GrSpEnd.compl R V τ) (b := GrSpEnd.id R V)
      (fun A _ _ v => by simp only [GrSpEnd.id_app, Bool.false_and, σ_false, one_smul]) y
    rwa [Bool.false_and, σ_false, one_smul] at this
  have htopB := iSup_eig_eq_top (a := GrSpEnd.compl R V τ) (fun A _ _ v => mem_iSup_compl τ hτ v) A
  have hy : (derSp (GrSpEnd.id R V)).app A (x - (mapSp τ.toHom).app A x)
      = (k : R) • (x - (mapSp τ.toHom).app A x) := by
    rw [map_sub, mapSp_derSp_comm (a := GrSpEnd.id R V) (φ := τ) (fun A _ _ v => rfl), mem_eig.1 hx,
      map_smul, smul_sub]
  obtain ⟨f, hf, hfN, hfs⟩ := exists_finsupp_eig_inf _ _ hBN htopB (k : R) hy
  have hf0 : ∀ j, j ≠ 0 → f j = 0 := fun j hj => by
    have htopQ := iSup_eig_scalar hred
      (fun n => ((n : R) - 2) + (1 - (m : R)) * (1 - if n ≤ m then 1 else 0))
      (fun n hn => by
        by_cases h : n ≤ m
        · exact ⟨n - 2, by
            beta_reduce
            rw [if_pos h, Nat.cast_sub hn]
            ring⟩
        · exact ⟨n - 1 - m, by
            beta_reduce
            rw [if_neg h, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
            ring⟩) A
    have hmj : m + j ≤ m * j + 1 := by
      obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
      obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.2 hj)
      ring_nf
      omega
    refine eq_zero_of_eigen_neg R _ htopQ (m := k + m * j - m - j) (by omega) ?_
    rw [derSp_lin (GrSpEnd.scalar R V fun n => (n : R) - 2) (GrSpEnd.compl R V τ) _ 1
      (1 - (m : R)) (fun A _ _ v => by
        simp only [GrSpEnd.scalar_app, GrSpEnd.compl_app, τ, GrSpEnd.trunc_app]
        module) (f j),
      derSp_lin (GrSpEnd.scalar R V fun n => (n : R) - 1) (GrSpEnd.id R V) _ 1 (-1)
        (fun A _ _ v => by simp only [GrSpEnd.scalar_app, GrSpEnd.id_app]; module) (f j),
      derSp_excess, hfN j, Module.End.mem_eigenspace_iff.1 (hf j), hA,
      Nat.cast_sub (show j ≤ k + m * j - m by omega), Nat.cast_sub (show m ≤ k + m * j by omega)]
    push_cast
    module
  have hyf : x - (mapSp τ.toHom).app A x = f 0 := by
    rw [← hfs]
    exact Finsupp.sum_eq_single 0 (fun j _ hj => hf0 j hj) (fun _ => rfl)
  have h0 : x - (mapSp τ.toHom).app A x
      ∈ Module.End.eigenspace ((derSp (GrSpEnd.compl R V τ)).app A) ((0 : ℕ) : R) :=
    hyf ▸ hf 0
  have h1 : x - (mapSp τ.toHom).app A x
      ∈ ⨆ (j : ℕ) (_ : j ≠ 0), eig R V (GrSpEnd.compl R V τ) j A :=
    (iSup_le fun j => le_iSup₂_of_le (f := fun (i : ℕ) (_ : i ≠ 0) =>
      eig R V (GrSpEnd.compl R V τ) i A) (j + 1) (by omega) le_rfl) (sub_mapSp_mem τ hτ x)
  have := Submodule.disjoint_def.1 (iSupIndep_eigenspace_nat _ 0) _ h0 h1
  exact (sub_eq_zero.1 this).symm

end FreeGrL

end Operad
