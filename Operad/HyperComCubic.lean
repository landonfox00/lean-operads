/-
# A hypercommutative algebra on `R[x]/(x³)`

The algebra on `R × R` of `Operad.HyperComModel` does not separate the operations
`m₃(m₃(x_a, x_b, x_c), x_d, x_e)` of arity five: there the value of a composite of two operations
of arity at least three is zero. This file gives a hypercommutative algebra in which they are
separated.

On `R[x]/(x³)`, written as triples `a + b x + c x²` (`Cub R`), with the shift
`s (a + b x + c x²) = b + c x` (`Cub.sh`) and the functional `γ (a + b x + c x²) = c` (`Cub.cL`):

* `μ₂` is the product;
* `μ₃(u, v, w) = s (s u · s v · s w)`, so `μ₃(x, x, x²) = 1` and `μ₃(x, x², x²) = x`;
* `μ₄(v₁, …, v₄) = 2 γ(v₁) ⋯ γ(v₄) · 1`, so `μ₄(x², x², x², x²) = 2`;
* `μₙ = 0` for `n ≥ 5`

(`HCAlg.cubOps`). **These operations satisfy the WDVV identities** (`HCAlg.cub`). The
operations of arity at least three vanish on `1`, the values of `μ₄` are multiples of `1`, and
`γ` vanishes on the values of `μ₃`; so a WDVV composite of two operations of arity at least three
vanishes unless both have arity three, and the identities in arity at least six hold term by
term. In arities four and five they are polynomial identities in the coefficients of the inputs.

This is the structure of the Frobenius manifold of the singularity `A₃`, with its operations
multiplied by `(-4)ⁿ⁻²`.
-/
import Operad.HyperComModel

universe u

namespace Operad

open Sym Finset

/-- **The algebra `R[x]/(x³)`**, as triples `a + b x + c x²`. -/
@[ext] structure Cub (R : Type u) where
  /-- The constant coefficient. -/
  a : R
  /-- The coefficient of `x`. -/
  b : R
  /-- The coefficient of `x²`. -/
  c : R

namespace Cub

variable {R : Type u} [CommRing R]

instance : Zero (Cub R) := ⟨⟨0, 0, 0⟩⟩
instance : One (Cub R) := ⟨⟨1, 0, 0⟩⟩
instance : Add (Cub R) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c⟩⟩
instance : Neg (Cub R) := ⟨fun x => ⟨-x.a, -x.b, -x.c⟩⟩
instance : Mul (Cub R) :=
  ⟨fun x y => ⟨x.a * y.a, x.a * y.b + x.b * y.a, x.a * y.c + x.b * y.b + x.c * y.a⟩⟩
instance : SMul R (Cub R) := ⟨fun r x => ⟨r * x.a, r * x.b, r * x.c⟩⟩

@[simp] lemma zero_a : (0 : Cub R).a = 0 := rfl
@[simp] lemma zero_b : (0 : Cub R).b = 0 := rfl
@[simp] lemma zero_c : (0 : Cub R).c = 0 := rfl
@[simp] lemma one_a : (1 : Cub R).a = 1 := rfl
@[simp] lemma one_b : (1 : Cub R).b = 0 := rfl
@[simp] lemma one_c : (1 : Cub R).c = 0 := rfl
@[simp] lemma add_a (x y : Cub R) : (x + y).a = x.a + y.a := rfl
@[simp] lemma add_b (x y : Cub R) : (x + y).b = x.b + y.b := rfl
@[simp] lemma add_c (x y : Cub R) : (x + y).c = x.c + y.c := rfl
@[simp] lemma neg_a (x : Cub R) : (-x).a = -x.a := rfl
@[simp] lemma neg_b (x : Cub R) : (-x).b = -x.b := rfl
@[simp] lemma neg_c (x : Cub R) : (-x).c = -x.c := rfl
@[simp] lemma mul_a (x y : Cub R) : (x * y).a = x.a * y.a := rfl
@[simp] lemma mul_b (x y : Cub R) : (x * y).b = x.a * y.b + x.b * y.a := rfl
@[simp] lemma mul_c (x y : Cub R) : (x * y).c = x.a * y.c + x.b * y.b + x.c * y.a := rfl
@[simp] lemma smul_a (r : R) (x : Cub R) : (r • x).a = r * x.a := rfl
@[simp] lemma smul_b (r : R) (x : Cub R) : (r • x).b = r * x.b := rfl
@[simp] lemma smul_c (r : R) (x : Cub R) : (r • x).c = r * x.c := rfl

instance : CommRing (Cub R) where
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]
  left_distrib x y z := by ext <;> simp <;> ring
  right_distrib x y z := by ext <;> simp <;> ring
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  mul_comm x y := by ext <;> simp <;> ring

instance : Module R (Cub R) where
  one_smul x := by ext <;> simp
  mul_smul r s x := by ext <;> simp [mul_assoc]
  smul_zero r := by ext <;> simp
  smul_add r x y := by ext <;> simp [mul_add]
  add_smul r s x := by ext <;> simp [add_mul]
  zero_smul x := by ext <;> simp

instance : Algebra R (Cub R) :=
  Algebra.ofModule (fun r x y => by ext <;> simp <;> ring) (fun r x y => by ext <;> simp <;> ring)

variable (R) in
/-- **The shift** `a + b x + c x² ↦ b + c x`. -/
def sh : Cub R →ₗ[R] Cub R where
  toFun x := ⟨x.b, x.c, 0⟩
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

variable (R) in
/-- **The coefficient of `x²`.** -/
def cL : Cub R →ₗ[R] R where
  toFun x := x.c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma sh_a (x : Cub R) : (sh R x).a = x.b := rfl
@[simp] lemma sh_b (x : Cub R) : (sh R x).b = x.c := rfl
@[simp] lemma sh_c (x : Cub R) : (sh R x).c = 0 := rfl
@[simp] lemma cL_apply (x : Cub R) : cL R x = x.c := rfl

end Cub

namespace HCAlg

open Cub

variable (R : Type u) [CommRing R]

/-- **The operations of the model**: the product in arity two, `s (s u · s v · s w)` in arity
three, `2 γ(v₁) ⋯ γ(v₄) · 1` in arity four, and zero in higher arities. -/
@[nolint unusedArguments]
noncomputable def cubOps (n : ℕ) (_ : 2 ≤ n) : EndOp R (Cub R) (Fin n) :=
  if n = 2 then MultilinearMap.mkPiAlgebra R (Fin n) (Cub R)
  else if n = 3 then (sh R).compMultilinearMap
    ((MultilinearMap.mkPiAlgebra R (Fin n) (Cub R)).compLinearMap fun _ => sh R)
  else if n = 4 then (2 : R) • ((MultilinearMap.mkPiAlgebra R (Fin n) R).compLinearMap
    fun _ => cL R).smulRight (1 : Cub R)
  else 0

variable {R}

lemma cubOps_two {n : ℕ} (h : 2 ≤ n) (hn : n = 2) (v : Fin n → Cub R) :
    cubOps R n h v = ∏ i, v i := by
  rw [cubOps, if_pos hn, MultilinearMap.mkPiAlgebra_apply]

lemma cubOps_three {n : ℕ} (h : 2 ≤ n) (hn : n = 3) (v : Fin n → Cub R) :
    cubOps R n h v = sh R (∏ i, sh R (v i)) := by
  rw [cubOps, if_neg (by omega), if_pos hn, LinearMap.compMultilinearMap_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

lemma cubOps_four {n : ℕ} (h : 2 ≤ n) (hn : n = 4) (v : Fin n → Cub R) :
    cubOps R n h v = (2 * ∏ i, cL R (v i)) • (1 : Cub R) := by
  rw [cubOps, if_neg (by omega), if_neg (by omega), if_pos hn, MultilinearMap.smul_apply,
    MultilinearMap.smulRight_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, smul_smul]

lemma cubOps_of_ge {n : ℕ} (h : 2 ≤ n) (hn : 5 ≤ n) (v : Fin n → Cub R) :
    cubOps R n h v = 0 := by
  rw [cubOps, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rfl

/-- The inner value of a WDVV composite in the model. -/
def cubInn (m : ℕ) (p s : Cub R) (g : R) : Cub R :=
  if m = 2 then p else if m = 3 then sh R s else if m = 4 then (2 * g) • (1 : Cub R) else 0

/-- The outer value of a WDVV composite in the model. -/
def cubOut (m : ℕ) (z p s : Cub R) (g : R) : Cub R :=
  if m = 2 then z * p else if m = 3 then sh R (sh R z * s)
  else if m = 4 then (2 * (cL R z * g)) • (1 : Cub R) else 0

/-- **A WDVV composite in the model**, in terms of the products over `S` and its complement. -/
lemma wVal_cub {n : ℕ} (S : Finset (Fin n)) (v : Fin n → Cub R) :
    HyperCom.wVal (Cub R) (cubOps R) S v =
      if 2 ≤ S.card ∧ 1 ≤ Sᶜ.card then
        cubOut (Sᶜ.card + 1)
          (cubInn S.card (∏ x ∈ S, v x) (∏ x ∈ S, sh R (v x)) (∏ x ∈ S, cL R (v x)))
          (∏ x ∈ Sᶜ, v x) (∏ x ∈ Sᶜ, sh R (v x)) (∏ x ∈ Sᶜ, cL R (v x))
      else 0 := by
  unfold HyperCom.wVal
  split_ifs with h
  · have hin : cubOps R S.card h.1 (fun t => v (S.orderEmbOfFin rfl t)) =
        cubInn S.card (∏ x ∈ S, v x) (∏ x ∈ S, sh R (v x)) (∏ x ∈ S, cL R (v x)) := by
      unfold cubInn
      split_ifs with h2 h3 h4
      · rw [cubOps_two _ h2, prod_orderEmbOfFin]
      · rw [cubOps_three _ h3, prod_orderEmbOfFin S fun x => sh R (v x)]
      · rw [cubOps_four _ h4, prod_orderEmbOfFin S fun x => cL R (v x)]
      · exact cubOps_of_ge _ (by omega) _
    rw [hin]
    unfold cubOut
    split_ifs with h2 h3 h4
    · rw [cubOps_two _ h2, Fin.prod_cons, prod_orderEmbOfFin]
    · rw [cubOps_three _ h3, Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [prod_orderEmbOfFin Sᶜ fun x => sh R (v x)]
    · rw [cubOps_four _ h4, Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [prod_orderEmbOfFin Sᶜ fun x => cL R (v x)]
    · exact cubOps_of_ge _ (by omega) _
  · rfl

/-! ### The WDVV sums of the model -/

lemma cubOut_zero (m : ℕ) (p s : Cub R) (g : R) : cubOut m 0 p s g = 0 := by
  unfold cubOut
  split_ifs <;> (ext <;> simp)

/-- **A composite of two operations of arity at least three vanishes unless both have arity
three**: the values of `μ₄` are multiples of `1`, on which the shift and `γ` vanish, and `γ`
vanishes on the values of `μ₃`. -/
lemma cubOut_cubInn_eq_zero {m m' : ℕ} (hm : 3 ≤ m) (hm' : 3 ≤ m') (h : ¬(m = 3 ∧ m' = 3))
    (p s : Cub R) (g : R) (p' s' : Cub R) (g' : R) :
    cubOut m (cubInn m' p s g) p' s' g' = 0 := by
  unfold cubOut cubInn
  split_ifs <;> first | omega | (ext <;> simp)

/-- **In arity at least six every WDVV composite of the model vanishes.** -/
lemma wVal_cub_eq_zero {n : ℕ} (hn : 6 ≤ n) (S : Finset (Fin n)) (v : Fin n → Cub R) :
    HyperCom.wVal (Cub R) (cubOps R) S v = 0 := by
  rw [wVal_cub]
  split_ifs with h
  · have hc : S.card + Sᶜ.card = n := by rw [Finset.card_add_card_compl, Fintype.card_fin]
    by_cases h2 : S.card = 2
    · unfold cubOut
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · by_cases h1 : Sᶜ.card = 1
      · have hz : cubInn S.card (∏ x ∈ S, v x) (∏ x ∈ S, sh R (v x)) (∏ x ∈ S, cL R (v x))
            = 0 := by
          unfold cubInn
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [hz, cubOut_zero]
      · exact cubOut_cubInn_eq_zero (by omega) (by omega) (by omega) _ _ _ _ _ _
  · rfl

/-- **The WDVV sum of the model in arity three**: the product of the three inputs. -/
lemma sum_wVal_cub_three {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : Fin 3 → Cub R) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin 3) => i ∈ S ∧ j ∈ S ∧ k ∉ S),
      HyperCom.wVal (Cub R) (cubOps R) S v = v i * v j * v k := by
  have hc : ({i, j} : Finset (Fin 3))ᶜ = {k} := by
    revert i j k
    decide
  rw [HyperCom.filter_pair _ _ _ hij hik hjk, Finset.sum_singleton, wVal_cub, hc,
    Finset.card_pair hij, Finset.card_singleton, if_pos ⟨le_rfl, le_rfl⟩, Finset.prod_pair hij,
    Finset.prod_singleton]
  rfl

lemma fin4_other (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ l : Fin 4, i ≠ l ∧ j ≠ l ∧ k ≠ l ∧ ({i, j} : Finset (Fin 4))ᶜ = {k, l} ∧
      ({k} : Finset (Fin 4))ᶜ = {i, j, l} ∧ ({i, k} : Finset (Fin 4))ᶜ = {j, l} ∧
      ({j} : Finset (Fin 4))ᶜ = {i, k, l} := by
  revert i j k
  decide

lemma filter_fin4 (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    univ.filter (fun S : Finset (Fin 4) => i ∈ S ∧ j ∈ S ∧ k ∉ S) = {{i, j}, {k}ᶜ} := by
  revert i j k
  decide

lemma pair_ne_compl_fin4 (i j k : Fin 4) (hij : i ≠ j) :
    ({i, j} : Finset (Fin 4)) ≠ {k}ᶜ := fun h => by
  have := congrArg Finset.card h
  rw [Finset.card_pair hij, Finset.card_compl, Finset.card_singleton, Fintype.card_fin] at this
  omega

/-- The value of the WDVV sum of the model in arity four. -/
def cubSum4 (vi vj vk vl : Cub R) : Cub R :=
  sh R (sh R (vi * vj) * (sh R vk * sh R vl)) + sh R (sh R vi * (sh R vj * sh R vl)) * vk

lemma cubSum4_comm (vi vj vk vl : Cub R) : cubSum4 vi vj vk vl = cubSum4 vi vk vj vl := by
  unfold cubSum4
  ext <;> simp <;> ring

lemma sum_wVal_cub_four {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l)
    (h1 : ({i, j} : Finset (Fin 4))ᶜ = {k, l}) (h2 : ({k} : Finset (Fin 4))ᶜ = {i, j, l})
    (v : Fin 4 → Cub R) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin 4) => i ∈ S ∧ j ∈ S ∧ k ∉ S),
      HyperCom.wVal (Cub R) (cubOps R) S v = cubSum4 (v i) (v j) (v k) (v l) := by
  have c3 : ({i, j, l} : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hij, hil]), Finset.card_pair hjl]
  have h3 : ({i, j, l} : Finset (Fin 4))ᶜ = {k} := by rw [← h2, compl_compl]
  have p3 : ∀ {β : Type u} [CommMonoid β] (f : Fin 4 → β),
      ∏ x ∈ ({i, j, l} : Finset (Fin 4)), f x = f i * (f j * f l) := fun f => by
    rw [Finset.prod_insert (by simp [hij, hil]), Finset.prod_pair hjl]
  rw [filter_fin4 i j k hij hik hjk, Finset.sum_pair (pair_ne_compl_fin4 i j k hij),
    wVal_cub, wVal_cub, h1, h2, h3, Finset.card_pair hij, Finset.card_pair hkl, c3,
    Finset.card_singleton, if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩]
  simp only [Finset.prod_pair hij, Finset.prod_pair hkl, Finset.prod_singleton, p3]
  rfl

lemma fin5_others (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ l m : Fin 5, l ≠ m ∧ i ≠ l ∧ i ≠ m ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m := by
  revert i j k
  decide

lemma filter_fin5 (i j k l m : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hlm : l ≠ m)
    (hil : i ≠ l) (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) :
    univ.filter (fun S : Finset (Fin 5) => i ∈ S ∧ j ∈ S ∧ k ∉ S)
      = {{i, j}, {i, j, l}, {i, j, m}, {k}ᶜ} := by
  revert i j k l m
  decide

lemma fin5_sets (i j k l m : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hlm : l ≠ m)
    (hil : i ≠ l) (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) :
    ({i, j} : Finset (Fin 5))ᶜ = {k, l, m} ∧ ({i, j, l} : Finset (Fin 5))ᶜ = {k, m} ∧
      ({i, j, m} : Finset (Fin 5))ᶜ = {k, l} ∧ ({k} : Finset (Fin 5))ᶜ = {i, j, l, m} ∧
      ({i, j} : Finset (Fin 5)) ∉ ({{i, j, l}, {i, j, m}, {k}ᶜ} : Finset (Finset (Fin 5))) ∧
      ({i, j, l} : Finset (Fin 5)) ∉ ({{i, j, m}, {k}ᶜ} : Finset (Finset (Fin 5))) ∧
      ({i, j, m} : Finset (Fin 5)) ≠ {k}ᶜ := by
  revert i j k l m
  decide

lemma prod_three {α β : Type*} [DecidableEq α] [CommMonoid β] {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (f : α → β) :
    ∏ x ∈ ({a, b, c} : Finset α), f x = f a * (f b * f c) := by
  rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc]

lemma prod_four {α β : Type*} [DecidableEq α] [CommMonoid β] {a b c d : α} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (f : α → β) :
    ∏ x ∈ ({a, b, c, d} : Finset α), f x = f a * (f b * (f c * f d)) := by
  rw [Finset.prod_insert (by simp [hab, hac, had]), prod_three hbc hbd hcd]

lemma card_three {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ({a, b, c} : Finset α).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]

lemma card_four {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset α).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]), card_three hbc hbd hcd]

/-- The value of the WDVV sum of the model in arity five. -/
def cubSum5 (vi vj vk vl vm : Cub R) : Cub R :=
  (2 * (cL R (vi * vj) * (cL R vk * (cL R vl * cL R vm)))) • (1 : Cub R)
    + (sh R (sh R (sh R (sh R vi * (sh R vj * sh R vl))) * (sh R vk * sh R vm))
      + (sh R (sh R (sh R (sh R vi * (sh R vj * sh R vm))) * (sh R vk * sh R vl))
        + (2 * (cL R vi * (cL R vj * (cL R vl * cL R vm)))) • (1 : Cub R) * vk))

lemma cubSum5_comm (vi vj vk vl vm : Cub R) :
    cubSum5 vi vj vk vl vm = cubSum5 vi vk vj vl vm := by
  unfold cubSum5
  ext <;> simp <;> ring

lemma sum_wVal_cub_five {i j k l m : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlm : l ≠ m) (hil : i ≠ l) (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l)
    (hkm : k ≠ m) (v : Fin 5 → Cub R) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin 5) => i ∈ S ∧ j ∈ S ∧ k ∉ S),
      HyperCom.wVal (Cub R) (cubOps R) S v = cubSum5 (v i) (v j) (v k) (v l) (v m) := by
  obtain ⟨c1, c2, c3, c4, n1, n2, n3⟩ := fin5_sets i j k l m hij hik hjk hlm hil him hjl hjm
    hkl hkm
  have c5 : ({i, j, l, m} : Finset (Fin 5))ᶜ = {k} := by rw [← c4, compl_compl]
  rw [filter_fin5 i j k l m hij hik hjk hlm hil him hjl hjm hkl hkm, Finset.sum_insert n1,
    Finset.sum_insert n2, Finset.sum_pair n3, wVal_cub, wVal_cub, wVal_cub, wVal_cub, c1, c2,
    c3, c4, c5, Finset.card_pair hij, card_three hkl hkm hlm, card_three hij hil hjl,
    Finset.card_pair hkm, card_three hij him hjm, Finset.card_pair hkl,
    card_four hij hil him hjl hjm hlm, Finset.card_singleton, if_pos ⟨by omega, by omega⟩,
    if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩]
  simp only [Finset.prod_pair hij, Finset.prod_pair hkm, Finset.prod_pair hkl,
    Finset.prod_singleton, prod_three hkl hkm hlm, prod_three hij hil hjl,
    prod_three hij him hjm, prod_four hij hil him hjl hjm hlm]
  rfl

/-- **A hypercommutative algebra on `R[x]/(x³)`**: the product in arity two,
`μ₃(u, v, w) = s (s u · s v · s w)`, `μ₄(v) = 2 γ(v₁) ⋯ γ(v₄) · 1`, and `μₙ = 0` for `n ≥ 5`. -/
noncomputable def cub : HCAlg R (Cub R) where
  μ := cubOps R
  symm n h σ v := by
    obtain hn | hn | hn | hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n := by omega
    · rw [cubOps_two h hn, cubOps_two h hn, Equiv.prod_comp σ v]
    · rw [cubOps_three h hn, cubOps_three h hn, Equiv.prod_comp σ fun a => sh R (v a)]
    · rw [cubOps_four h hn, cubOps_four h hn, Equiv.prod_comp σ fun a => cL R (v a)]
    · rw [cubOps_of_ge h hn, cubOps_of_ge h hn]
  wdvv n i j k hij hik hjk v := by
    have h3 : 3 ≤ n := by
      have := Finset.card_le_univ ({i, j, k} : Finset (Fin n))
      rwa [Fintype.card_fin, Finset.card_insert_of_notMem (by simp [hij, hik]),
        Finset.card_pair hjk] at this
    obtain rfl | rfl | rfl | h6 : n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n := by omega
    · rw [sum_wVal_cub_three hij hik hjk, sum_wVal_cub_three hik hij hjk.symm, mul_right_comm]
    · obtain ⟨l, hil, hjl, hkl, h1, h2, h1', h2'⟩ := fin4_other i j k hij hik hjk
      rw [sum_wVal_cub_four hij hik hjk hil hjl hkl h1 h2 v,
        sum_wVal_cub_four hik hij hjk.symm hil hkl hjl h1' h2' v, cubSum4_comm]
    · obtain ⟨l, m, hlm, hil, him, hjl, hjm, hkl, hkm⟩ := fin5_others i j k hij hik hjk
      rw [sum_wVal_cub_five hij hik hjk hlm hil him hjl hjm hkl hkm v,
        sum_wVal_cub_five hik hij hjk.symm hlm hil him hkl hkm hjl hjm v, cubSum5_comm]
    · exact (Finset.sum_eq_zero fun S _ => wVal_cub_eq_zero h6 S v).trans
        (Finset.sum_eq_zero fun S _ => wVal_cub_eq_zero h6 S v).symm

lemma cub_μ : (cub (R := R)).μ = cubOps R := rfl

end HCAlg

end Operad
