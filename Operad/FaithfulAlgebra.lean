/-
# Every symmetric operad acts faithfully on a free algebra

An operation of arity `n` of a symmetric operad `P` is determined by its action on the free
algebra `S(P, Rⁿ)` on `n` generators (`Operad.Schur.algebra`).

* **Reading the multilinear part** (`Schur.read`): the linear map `S(P, Rⁿ) → P (Fin n)` sending
  the class of `p ⊗ (v₁, …, v_m)` to the sum over the bijections `σ : Fin m ≃ Fin n` of the
  coefficient `∏ᵢ (vᵢ)_{σ i}` times the relabelling of `p` along `σ` (`Schur.readFam`,
  `Schur.readFam_compatible`); it vanishes unless `m = n`.
* **An operation is read off its action on the generators** (`Schur.read_act`):
  `read (p · (e₁, …, eₙ)) = p`, for the basis vectors `eₖ` of `Rⁿ`.
* Hence **the free algebra on `n` generators is faithful in arity `n`**
  (`Schur.algebra_app_injective`), and an operation of arity `n` killed by every algebra on a
  module of the universe of the free algebra is zero (`SymAlgebra.eq_zero_of_forall`).
-/
import Operad.FreeAlgebra
import Mathlib.Data.Fintype.Perm

universe u w

namespace Operad

open Sym

namespace Schur

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-- The coefficient of `e_{σ 0} ⊗ ⋯ ⊗ e_{σ (m - 1)}` in a family of `m` vectors of `Rⁿ`. -/
noncomputable def coefML (n : ℕ) {m : ℕ} (σ : Fin m ≃ Fin n) :
    MultilinearMap R (fun _ : Fin m => Fin n → R) R :=
  (MultilinearMap.mkPiAlgebra R (Fin m) R).compLinearMap fun i => LinearMap.proj (σ i)

lemma coefML_apply (n : ℕ) {m : ℕ} (σ : Fin m ≃ Fin n) (v : Fin m → Fin n → R) :
    coefML n σ v = ∏ i, v i (σ i) := by
  simp [coefML]

variable (R P) in
/-- **Reading the multilinear part**, on generators: `p ⊗ v` to the sum over the bijections `σ`
of the coefficient of `v` along `σ` times the relabelling of `p`. -/
noncomputable def readFam (n m : ℕ) :
    P (Fin m) →ₗ[R] MultilinearMap R (fun _ : Fin m => Fin n → R) (P (Fin n)) where
  toFun p := ∑ σ : Fin m ≃ Fin n, (coefML n σ).smulRight (SymSpecies.map (R := R) σ p)
  map_add' p p' := by
    ext v
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    ext v
    simp [smul_comm c, Finset.smul_sum]

lemma readFam_apply (n m : ℕ) (p : P (Fin m)) (v : Fin m → Fin n → R) :
    readFam R P n m p v
      = ∑ σ : Fin m ≃ Fin n, (∏ i, v i (σ i)) • SymSpecies.map (R := R) σ p := by
  simp [readFam, coefML_apply]

lemma readFam_compatible (n : ℕ) : Compatible (readFam R P n) := by
  intro m τ p v
  rw [readFam_apply, readFam_apply]
  let e : (Fin m ≃ Fin n) ≃ (Fin m ≃ Fin n) :=
    ⟨fun σ => τ.trans σ, fun σ => τ.symm.trans σ, fun σ => by ext; simp, fun σ => by ext; simp⟩
  refine Fintype.sum_equiv e _ _ fun σ => ?_
  rw [← SymSpecies.map_trans]
  refine congrArg (· • _) ?_
  exact (Equiv.prod_comp τ fun j => v j (σ j)).symm

variable (R P) in
/-- **Reading the multilinear part** of the free algebra on `n` generators. -/
noncomputable def read (n : ℕ) : Schur R P (Fin n → R) →ₗ[R] P (Fin n) :=
  lift (readFam R P n) (readFam_compatible n)

/-- **An operation is read off its action on the generators** of the free algebra. -/
theorem read_act (n : ℕ) (p : P (Fin n)) :
    read R P n (act p fun k => ι R P (Fin n → R) (Pi.single k 1)) = p := by
  rw [← mk_eq_act, read, lift_mk, readFam_apply, Finset.sum_eq_single (Equiv.refl _)]
  · simp [SymSpecies.map_refl]
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra h
      exact hσ (Equiv.ext fun i => not_not.1 fun hi => h ⟨i, hi⟩)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), zero_smul]
  · simp

variable (R P) in
/-- **The free algebra on `n` generators is faithful in arity `n`.** -/
theorem algebra_app_injective (n : ℕ) :
    Function.Injective ((algebra R P (Fin n → R)).app (Fin n)) := by
  intro p q h
  have h' := congrArg (fun F : EndOp R (Schur R P (Fin n → R)) (Fin n) =>
    read R P n (F fun k => ι R P (Fin n → R) (Pi.single k 1))) h
  exact (read_act n p).symm.trans (h'.trans (read_act n q))

end Schur

/-- **An operation killed by every algebra is zero**: it suffices to test the algebras on modules
of the universe of the free algebras. -/
theorem SymAlgebra.eq_zero_of_forall {R : Type u} [CommRing R]
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P] {n : ℕ}
    (x : P (Fin n))
    (h : ∀ (V : Type (max u w)) [AddCommGroup V] [Module R V] (α : SymAlgebra R P V),
      α.app (Fin n) x = 0) : x = 0 :=
  Schur.algebra_app_injective R P n ((h _ _).trans (map_zero _).symm)

end Operad
