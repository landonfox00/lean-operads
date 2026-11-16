/-
# A hypercommutative algebra on `R × R`

The scalar hypercommutative algebras of `Operad.HyperComDim` take the same value on all the
relabellings of an operation, so they do not separate the operations `m₂(m₃(…), x_a)` of arity
four. This file gives a hypercommutative algebra which does.

On `R × R`, with the functional `h (p, q) = q - p` (`HCAlg.hL`) and scalars `cₙ`:

* `μ₂` is the product of `R × R`;
* `μₙ(v₁, …, vₙ) = cₙ h(v₁) ⋯ h(vₙ) · 1` for `n ≥ 3` (`HCAlg.modelOps`).

**These operations satisfy the WDVV identities** (`HCAlg.model`). A WDVV composite
`μ(μ(v_S), v_{Sᶜ})` is computed from the products over `S` and over its complement
(`HCAlg.wVal_model`). In arity `n ≥ 4`, among the sets `S` with `i, j ∈ S` and `k ∉ S`, only
`S = {i, j}` and the complement of `{k}` contribute: in the other composites both operations have
arity at least three, the inner one is a multiple of `1`, and `h 1 = 0` (`HCAlg.sum_wVal_model`).
The sum is

  `c_{n-1} ∏ h(v_x) · (h(vᵢ vⱼ) h(v_k) · 1 + h(vᵢ) h(vⱼ) · v_k)`,

the product over the inputs `x` other than `i, j, k` (`HCAlg.modelSum`), and it is symmetric in
`j` and `k` (`HCAlg.modelSum_comm`). In arity three the identity is the associativity and
commutativity of the product (`HCAlg.sum_wVal_model_three`).
-/
import Operad.HyperComDim

universe u

namespace Operad

open Sym Finset

namespace HCAlg

variable (R : Type u) [CommRing R]

/-- **The functional** `(p, q) ↦ q - p` on `R × R`. -/
def hL : R × R →ₗ[R] R := LinearMap.snd R R R - LinearMap.fst R R R

@[simp] lemma hL_apply (x : R × R) : hL R x = x.2 - x.1 := rfl

lemma hL_one : hL R (1 : R × R) = 0 := sub_self _

/-- **The operations of the model**: the product of `R × R` in arity two, and
`cₙ h(v₁) ⋯ h(vₙ) · 1` in arity `n ≥ 3`. -/
@[nolint unusedArguments]
noncomputable def modelOps (c : ℕ → R) (n : ℕ) (_ : 2 ≤ n) : EndOp R (R × R) (Fin n) :=
  if n = 2 then MultilinearMap.mkPiAlgebra R (Fin n) (R × R)
  else c n • ((MultilinearMap.mkPiAlgebra R (Fin n) R).compLinearMap fun _ => hL R).smulRight
    (1 : R × R)

variable {R}

lemma modelOps_two (c : ℕ → R) {n : ℕ} (h : 2 ≤ n) (hn : n = 2) (v : Fin n → R × R) :
    modelOps R c n h v = ∏ i, v i := by
  rw [modelOps, if_pos hn, MultilinearMap.mkPiAlgebra_apply]

lemma modelOps_of_ne (c : ℕ → R) {n : ℕ} (h : 2 ≤ n) (hn : n ≠ 2) (v : Fin n → R × R) :
    modelOps R c n h v = (c n * ∏ i, hL R (v i)) • (1 : R × R) := by
  rw [modelOps, if_neg hn, MultilinearMap.smul_apply, MultilinearMap.smulRight_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, smul_smul]

/-- The inner value of a WDVV composite in the model. -/
def modelInn (c : ℕ → R) (m : ℕ) (a : R × R) (α : R) : R × R :=
  if m = 2 then a else (c m * α) • (1 : R × R)

/-- The outer value of a WDVV composite in the model. -/
def modelOut (c : ℕ → R) (m : ℕ) (z b : R × R) (β : R) : R × R :=
  if m = 2 then z * b else (c m * (hL R z * β)) • (1 : R × R)

/-- **A WDVV composite in the model**, in terms of the products over `S` and its complement. -/
lemma wVal_model (c : ℕ → R) {n : ℕ} (S : Finset (Fin n)) (v : Fin n → R × R) :
    HyperCom.wVal (R × R) (modelOps R c) S v =
      if 2 ≤ S.card ∧ 1 ≤ Sᶜ.card then
        modelOut c (Sᶜ.card + 1) (modelInn c S.card (∏ x ∈ S, v x) (∏ x ∈ S, hL R (v x)))
          (∏ x ∈ Sᶜ, v x) (∏ x ∈ Sᶜ, hL R (v x))
      else 0 := by
  unfold HyperCom.wVal
  split_ifs with h
  · have hin : modelOps R c S.card h.1 (fun t => v (S.orderEmbOfFin rfl t)) =
        modelInn c S.card (∏ x ∈ S, v x) (∏ x ∈ S, hL R (v x)) := by
      unfold modelInn
      split_ifs with h2
      · rw [modelOps_two c _ h2, prod_orderEmbOfFin]
      · rw [modelOps_of_ne c _ h2, prod_orderEmbOfFin S fun x => hL R (v x)]
    rw [hin]
    unfold modelOut
    split_ifs with h2
    · rw [modelOps_two c _ h2, Fin.prod_cons, prod_orderEmbOfFin]
    · rw [modelOps_of_ne c _ h2, Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [prod_orderEmbOfFin Sᶜ fun x => hL R (v x)]
  · rfl

/-! ### The WDVV sums of the model -/

lemma compl_pair_eq {n : ℕ} {i j k : Fin n} (hik : i ≠ k) (hjk : j ≠ k) :
    ({i, j} : Finset (Fin n))ᶜ = insert k ({i, j, k} : Finset (Fin n))ᶜ := by
  ext x
  simp only [mem_compl, mem_insert, mem_singleton, not_or]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hx : x = k
    · exact Or.inl hx
    · exact Or.inr ⟨h1, h2, hx⟩
  · rintro (rfl | ⟨h1, h2, -⟩)
    · exact ⟨Ne.symm hik, Ne.symm hjk⟩
    · exact ⟨h1, h2⟩

lemma compl_singleton_eq {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ({k} : Finset (Fin n))ᶜ = insert i (insert j ({i, j, k} : Finset (Fin n))ᶜ) := by
  ext x
  simp only [mem_compl, mem_insert, mem_singleton, not_or]
  constructor
  · intro h
    by_cases hxi : x = i
    · exact Or.inl hxi
    · by_cases hxj : x = j
      · exact Or.inr (Or.inl hxj)
      · exact Or.inr (Or.inr ⟨hxi, hxj, h⟩)
  · rintro (rfl | rfl | ⟨-, -, h⟩)
    · exact hik
    · exact hjk
    · exact h

lemma prod_compl_pair {n : ℕ} {i j k : Fin n} (hik : i ≠ k) (hjk : j ≠ k) (g : Fin n → R) :
    ∏ x ∈ ({i, j} : Finset (Fin n))ᶜ, g x = g k * ∏ x ∈ ({i, j, k} : Finset (Fin n))ᶜ, g x := by
  rw [compl_pair_eq hik hjk, Finset.prod_insert]
  simp

lemma prod_compl_singleton {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (g : Fin n → R) :
    ∏ x ∈ ({k} : Finset (Fin n))ᶜ, g x =
      g i * (g j * ∏ x ∈ ({i, j, k} : Finset (Fin n))ᶜ, g x) := by
  rw [compl_singleton_eq hij hik hjk, Finset.prod_insert, Finset.prod_insert]
  · simp
  · simp [hij]

/-- The value of the WDVV sum of the model for `i, j ∈ S` and `k ∉ S`, in arity at least four. -/
def modelSum (c : ℕ → R) {n : ℕ} (i j k : Fin n) (v : Fin n → R × R) : R × R :=
  (c (n - 1) * ∏ x ∈ ({i, j, k} : Finset (Fin n))ᶜ, hL R (v x)) •
    ((hL R (v i * v j) * hL R (v k)) • (1 : R × R) + (hL R (v i) * hL R (v j)) • v k)

/-- **The sum is symmetric in the last two inputs.** -/
lemma modelSum_comm (c : ℕ → R) {n : ℕ} (i j k : Fin n) (v : Fin n → R × R) :
    modelSum c i j k v = modelSum c i k j v := by
  unfold modelSum
  rw [show ({i, k, j} : Finset (Fin n)) = {i, j, k} from by rw [Finset.pair_comm k j]]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp [hL] <;> ring

lemma modelInn_two (c : ℕ → R) (a : R × R) (α : R) : modelInn c 2 a α = a := if_pos rfl

lemma modelInn_of_ne (c : ℕ → R) {m : ℕ} (hm : m ≠ 2) (a : R × R) (α : R) :
    modelInn c m a α = (c m * α) • (1 : R × R) := if_neg hm

lemma modelOut_two (c : ℕ → R) (z b : R × R) (β : R) : modelOut c 2 z b β = z * b := if_pos rfl

lemma modelOut_of_ne (c : ℕ → R) {m : ℕ} (hm : m ≠ 2) (z b : R × R) (β : R) :
    modelOut c m z b β = (c m * (hL R z * β)) • (1 : R × R) := if_neg hm

/-- **The WDVV sum of the model in arity at least four**: only `S = {i, j}` and the complement of
`{k}` contribute, the other composites having two operations of arity at least three, the inner
one a multiple of `1`, on which the functional vanishes. -/
lemma sum_wVal_model (c : ℕ → R) {n : ℕ} (hn : 4 ≤ n) {i j k : Fin n} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (v : Fin n → R × R) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin n) => i ∈ S ∧ j ∈ S ∧ k ∉ S),
      HyperCom.wVal (R × R) (modelOps R c) S v = modelSum c i j k v := by
  have hS₁ : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij
  have hS₁c : ({i, j} : Finset (Fin n))ᶜ.card = n - 2 := by
    rw [Finset.card_compl, hS₁, Fintype.card_fin]
  have hS₂ : ({k} : Finset (Fin n))ᶜ.card = n - 1 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hS₂c : (({k} : Finset (Fin n))ᶜ)ᶜ.card = 1 := by
    rw [compl_compl, Finset.card_singleton]
  rw [Finset.sum_eq_add ({i, j} : Finset (Fin n)) ({k}ᶜ)]
  · rw [wVal_model, wVal_model, if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, hS₁,
      hS₁c, hS₂, hS₂c, modelInn_two, modelOut_of_ne c (by omega), modelInn_of_ne c (by omega),
      modelOut_two, show n - 2 + 1 = n - 1 by omega, Finset.prod_pair hij,
      prod_compl_pair hik hjk, prod_compl_singleton hij hik hjk, compl_compl,
      Finset.prod_singleton]
    unfold modelSum
    generalize (∏ x ∈ ({i, j, k} : Finset (Fin n))ᶜ, hL R (v x)) = H
    refine Prod.ext ?_ ?_ <;> simp [hL] <;> ring
  · intro h
    have := congrArg Finset.card h
    rw [hS₁, hS₂] at this
    omega
  · rintro S hS ⟨h1, h2⟩
    obtain ⟨hi, hj, hk⟩ := (Finset.mem_filter.1 hS).2
    have hc2 : S.card ≠ 2 := fun hc => h1 (Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hi (Finset.singleton_subset_iff.2 hj)) (by rw [hc, hS₁])).symm
    have hc1 : Sᶜ.card ≠ 1 := fun hc => h2 (by
      have : ({k} : Finset (Fin n)) = Sᶜ := Finset.eq_of_subset_of_card_le
        (Finset.singleton_subset_iff.2 (Finset.mem_compl.2 hk)) (by rw [hc, Finset.card_singleton])
      rw [this, compl_compl])
    rw [wVal_model]
    split_ifs with h
    · rw [modelInn_of_ne c hc2, modelOut_of_ne c (by omega), map_smul, hL_one, smul_zero,
        zero_mul, mul_zero, zero_smul]
    · rfl
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp, by simp,
      by simp [hik.symm, hjk.symm]⟩) h
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [hik], by simp [hjk],
      by simp⟩) h

/-- **The WDVV sum of the model in arity three**: the product of the three inputs. -/
lemma sum_wVal_model_three (c : ℕ → R) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (v : Fin 3 → R × R) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin 3) => i ∈ S ∧ j ∈ S ∧ k ∉ S),
      HyperCom.wVal (R × R) (modelOps R c) S v = v i * v j * v k := by
  have hc : ({i, j} : Finset (Fin 3))ᶜ = {k} := by
    revert i j k
    decide
  rw [HyperCom.filter_pair _ _ _ hij hik hjk, Finset.sum_singleton, wVal_model, hc,
    Finset.card_pair hij, Finset.card_singleton, if_pos ⟨le_rfl, le_rfl⟩, modelInn_two,
    modelOut_two, Finset.prod_pair hij, Finset.prod_singleton]

/-- **A hypercommutative algebra on `R × R`**: the product in arity two, and
`μₙ(v) = cₙ h(v₁) ⋯ h(vₙ) · 1` in arity `n ≥ 3`, with `h (p, q) = q - p`. -/
noncomputable def model (c : ℕ → R) : HCAlg R (R × R) where
  μ := modelOps R c
  symm n h σ v := by
    by_cases hn : n = 2
    · rw [modelOps_two c h hn, modelOps_two c h hn, Equiv.prod_comp σ v]
    · rw [modelOps_of_ne c h hn, modelOps_of_ne c h hn,
        Equiv.prod_comp σ fun a => hL R (v a)]
  wdvv n i j k hij hik hjk v := by
    have h3 : 3 ≤ n := by
      have := Finset.card_le_univ ({i, j, k} : Finset (Fin n))
      rwa [Fintype.card_fin, Finset.card_insert_of_notMem (by simp [hij, hik]),
        Finset.card_pair hjk] at this
    obtain rfl | h4 : n = 3 ∨ 4 ≤ n := by omega
    · rw [sum_wVal_model_three c hij hik hjk, sum_wVal_model_three c hik hij hjk.symm,
        mul_right_comm]
    · rw [sum_wVal_model c h4 hij hik hjk, sum_wVal_model c h4 hik hij hjk.symm,
        modelSum_comm]

lemma model_μ (c : ℕ → R) : (model c).μ = modelOps R c := rfl

end HCAlg

end Operad
