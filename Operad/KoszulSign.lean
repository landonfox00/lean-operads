/-
# Koszul signs in the endomorphism operad

A **super module** is a module `V` with an involution `ε`, the sign `(-1)^|x|` on homogeneous
elements. A multilinear operation `β` of `V` is homogeneous of parity `q` when
`β (ε x₁, …, ε xₙ) = (-1)^q ε (β (x₁, …, xₙ))` (`End.IsHomog`). Inserting `β` into the slot `i`
of `α` moves it across the inputs before the slot, which costs the Koszul sign: the Koszul
composition `α ∘ᵏᵢ β` applies `ε^q` to the inputs before `i` and composes (`End.kcompFin`).

* **Sequential associativity holds on the nose**, the parities adding
  (`End.kcompFin_assoc_seq`), and **parallel associativity holds up to the Koszul sign**
  `(-1)^(|β| |γ|)` (`End.kcompFin_assoc_par`).
* So the Koszul circle product `α ⋆ β = ∑ᵢ α ∘ᵏᵢ β` (`End.kstar`) satisfies **the graded pre-Lie
  identity** (`End.kstar_assoc_symm`): its associator is graded symmetric in the last two
  arguments; for an odd `β` the two orders of insertion cancel outright
  (`End.kstar_kstar_odd`): `(α ⋆ β) ⋆ β = α ⋆ (β ⋆ β)`, with no division by two.

This is the sign calculus of the Gerstenhaber bracket and of `A∞`-structures in the bar
convention, where every structure map is odd (`Operad.AInfinity`).
-/
import Operad.PreLie
import Operad.Associativity
import Operad.Endomorphism

universe u v

namespace Operad

open NSOperad Finset

namespace End

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-! ## Evaluating compositions -/

/-- The inputs of `α` in `compFin i α β`, evaluated at `v`. -/
def cfTuple {m n : ℕ} (i : Fin m) (β : End R V n) (v : Fin (m - 1 + n) → V) (s : Fin m) : V :=
  if h : (s : ℕ) < i then v ⟨s, by have := s.isLt; have := i.isLt; omega⟩
  else if h' : (s : ℕ) = i then
    β (fun t => v ⟨i + t, by have := t.isLt; have := i.isLt; omega⟩)
  else v ⟨s + n - 1, by have := s.isLt; have := i.isLt; omega⟩

lemma cfTuple_of_lt {m n : ℕ} (i : Fin m) (β : End R V n) (v : Fin (m - 1 + n) → V)
    (s : Fin m) (h : (s : ℕ) < i) :
    cfTuple i β v s = v ⟨s, by have := s.isLt; have := i.isLt; omega⟩ := by
  rw [cfTuple, dif_pos h]

lemma cfTuple_of_eq {m n : ℕ} (i : Fin m) (β : End R V n) (v : Fin (m - 1 + n) → V)
    (s : Fin m) (h : (s : ℕ) = i) :
    cfTuple i β v s = β (fun t => v ⟨i + t, by have := t.isLt; have := i.isLt; omega⟩) := by
  rw [cfTuple, dif_neg (by omega), dif_pos h]

lemma cfTuple_of_gt {m n : ℕ} (i : Fin m) (β : End R V n) (v : Fin (m - 1 + n) → V)
    (s : Fin m) (h : (i : ℕ) < s) :
    cfTuple i β v s = v ⟨s + n - 1, by have := s.isLt; have := i.isLt; omega⟩ := by
  rw [cfTuple, dif_neg (by omega), dif_neg (by omega)]

/-- **`compFin` evaluated**: the inputs before the slot, then `β` of the next `n` inputs, then the
rest. -/
lemma compFin_apply {m n : ℕ} (i : Fin m) (α : End R V m) (β : End R V n)
    (v : Fin (m - 1 + n) → V) : compFin (R := R) i α β v = α (cfTuple i β v) := by
  unfold compFin
  rw [reindex_apply, operad_comp_apply, reindex_apply]
  rfl

/-! ## Twists -/

variable (ε : V →ₗ[R] V)

/-- `ε^q` on the inputs before position `i`. -/
def twistFn (q i : ℕ) {n : ℕ} (t : Fin n) : V →ₗ[R] V :=
  if (t : ℕ) < i then ε ^ q else LinearMap.id

/-- **The twist** `α ↦ α ∘ (ε^q ⊗ ⋯ ⊗ ε^q ⊗ 1 ⊗ ⋯ ⊗ 1)`, with `ε^q` on the inputs before `i`. -/
def twist (q i : ℕ) {n : ℕ} : End R V n →ₗ[R] End R V n :=
  MultilinearMap.compLinearMapₗ (twistFn ε q i)

@[simp] lemma twist_apply (q i : ℕ) {n : ℕ} (α : End R V n) (v : Fin n → V) :
    twist ε q i α v = α (fun t => twistFn ε q i t (v t)) := rfl

lemma twistFn_of_lt (q i : ℕ) {n : ℕ} (t : Fin n) (h : (t : ℕ) < i) :
    twistFn ε q i t = ε ^ q := if_pos h

lemma twistFn_of_ge (q i : ℕ) {n : ℕ} (t : Fin n) (h : i ≤ (t : ℕ)) :
    twistFn ε q i t = LinearMap.id := if_neg (by omega)

/-- Twisting the same inputs twice adds the exponents. -/
lemma twist_twist (q r i : ℕ) {n : ℕ} (α : End R V n) :
    twist ε r i (twist ε q i α) = twist ε (q + r) i α := by
  ext v
  simp only [twist_apply]
  congr 1
  funext t
  by_cases h : (t : ℕ) < i
  · simp only [twistFn_of_lt ε _ _ t h, pow_add, Module.End.mul_apply]
  · simp only [twistFn_of_ge ε _ _ t (not_lt.mp h), LinearMap.id_apply]

/-- Twists commute. -/
lemma twist_comm (q r i i' : ℕ) {n : ℕ} (α : End R V n) :
    twist ε r i' (twist ε q i α) = twist ε q i (twist ε r i' α) := by
  ext v
  simp only [twist_apply]
  congr 1
  funext t
  simp only [twistFn]
  split_ifs <;> simp only [← Module.End.mul_apply, ← pow_add, add_comm, ← Module.End.one_eq_id,
    one_mul, mul_one]

lemma reindex_twist {m m' : ℕ} (h : m = m') (q i : ℕ) (α : End R V m) :
    reindex R (End R V) h (twist ε q i α) = twist ε q i (reindex R (End R V) h α) := by
  subst h
  rfl

/-- **Twisting before the slot commutes with composition.** -/
lemma compFin_twist_left (q i' : ℕ) {m n : ℕ} (i : Fin m) (hi : i' ≤ (i : ℕ)) (α : End R V m)
    (β : End R V n) :
    compFin (R := R) i (twist ε q i' α) β = twist ε q i' (compFin (R := R) i α β) := by
  ext v
  rw [compFin_apply, twist_apply, twist_apply, compFin_apply]
  congr 1
  funext s
  have hs := s.isLt
  have hm := i.isLt
  rcases lt_trichotomy (s : ℕ) i with h | h | h
  · rw [cfTuple_of_lt i β _ s h, cfTuple_of_lt i β _ s h]
    simp only [twistFn]
  · rw [cfTuple_of_eq i β _ s h, cfTuple_of_eq i β _ s h,
      twistFn_of_ge ε _ _ s (by omega), LinearMap.id_apply]
    congr 1
    funext t
    rw [twistFn_of_ge ε _ _ _ (by simp; omega), LinearMap.id_apply]
  · rw [cfTuple_of_gt i β _ s h, cfTuple_of_gt i β _ s h, twistFn_of_ge ε _ _ s (by omega),
      twistFn_of_ge ε _ _ _ (by simp; omega)]

/-- **Twisting across a nested slot**: twisting the first `i + j` inputs of `α ∘ᵢ β` twists the
inputs of `α` before `i` and the first `j` inputs of `β`. -/
lemma twist_compFin_nested (r : ℕ) {m n : ℕ} (i : Fin m) (j : ℕ) (hj : j ≤ n) (α : End R V m)
    (β : End R V n) :
    twist ε r (i + j) (compFin (R := R) i α β)
      = compFin (R := R) i (twist ε r i α) (twist ε r j β) := by
  ext v
  rw [compFin_apply, twist_apply, twist_apply, compFin_apply]
  congr 1
  funext s
  have hs := s.isLt
  have hm := i.isLt
  rcases lt_trichotomy (s : ℕ) i with h | h | h
  · rw [cfTuple_of_lt i β _ s h, cfTuple_of_lt i _ _ s h, twistFn_of_lt ε _ _ s h,
      twistFn_of_lt ε _ _ _ (by simp; omega)]
  · rw [cfTuple_of_eq i β _ s h, cfTuple_of_eq i _ _ s h, twistFn_of_ge ε _ _ s (by omega),
      LinearMap.id_apply, twist_apply]
    congr 1
    funext t
    simp only [twistFn]
    split_ifs <;> first | rfl | omega
  · rw [cfTuple_of_gt i β _ s h, cfTuple_of_gt i _ _ s h, twistFn_of_ge ε _ _ s (by omega),
      twistFn_of_ge ε _ _ _ (by simp; omega)]

variable {ε}

/-- `ε^r ∘ ε^r = 1` for an involution. -/
lemma pow_pow_apply (hε : ∀ x, ε (ε x) = x) (r : ℕ) (x : V) : (ε ^ r) ((ε ^ r) x) = x := by
  have h2 : ε * ε = 1 := LinearMap.ext hε
  rw [← Module.End.mul_apply, ← (Commute.refl ε).mul_pow, h2, one_pow, Module.End.one_apply]

variable (ε) in
/-- **Twisting across a disjoint slot**: twisting the first `i' + n - 1` inputs of `α ∘ᵢ β`, for
a slot `i' > i` of `α`, twists the inputs of `α` before `i'` and conjugates `β` by `ε^r`. -/
lemma twist_compFin_par (hε : ∀ x, ε (ε x) = x) (r : ℕ) {m n : ℕ} (i : Fin m) (i' : ℕ)
    (hii' : (i : ℕ) < i') (α : End R V m) (β : End R V n) :
    twist ε r (i' + n - 1) (compFin (R := R) i α β)
      = compFin (R := R) i (twist ε r i' α)
          ((ε ^ r).compMultilinearMap (twist ε r n β)) := by
  ext v
  rw [compFin_apply, twist_apply, twist_apply, compFin_apply]
  congr 1
  funext s
  have hs := s.isLt
  have hm := i.isLt
  rcases lt_trichotomy (s : ℕ) i with h | h | h
  · rw [cfTuple_of_lt i β _ s h, cfTuple_of_lt i _ _ s h, twistFn_of_lt ε _ _ s (by omega),
      twistFn_of_lt ε _ _ _ (by simp; omega)]
  · rw [cfTuple_of_eq i β _ s h, cfTuple_of_eq i _ _ s h, twistFn_of_lt ε _ _ s (by omega),
      LinearMap.compMultilinearMap_apply, pow_pow_apply hε, twist_apply]
    congr 1
    funext t
    have ht := t.isLt
    rw [twistFn_of_lt ε _ _ _ (by simp; omega), twistFn_of_lt ε _ _ t ht]
  · rw [cfTuple_of_gt i β _ s h, cfTuple_of_gt i _ _ s h]
    simp only [twistFn]
    split_ifs <;> first | rfl | omega

/-! ## Homogeneous operations -/

variable (ε) in
/-- **A homogeneous operation of parity `q`**: `β (ε x₁, …, ε xₙ) = (-1)^q ε (β (x₁, …, xₙ))`. -/
def IsHomog (q : ℕ) {n : ℕ} (β : End R V n) : Prop :=
  ∀ v : Fin n → V, β (fun t => ε (v t)) = (-1 : R) ^ q • ε (β v)

/-- Conjugating a homogeneous operation of parity `q` by `ε^r` multiplies it by `(-1)^(q r)`. -/
lemma IsHomog.conj (hε : ∀ x, ε (ε x) = x) {q : ℕ} {n : ℕ} {β : End R V n}
    (hβ : IsHomog ε q β) (r : ℕ) :
    (ε ^ r).compMultilinearMap (twist ε r n β) = (-1 : R) ^ (q * r) • β := by
  have key : ∀ v : Fin n → V, β (fun t => (ε ^ r) (v t)) = (-1 : R) ^ (q * r) • (ε ^ r) (β v) := by
    induction r with
    | zero => intro v; simp
    | succ r ih =>
      intro v
      have h1 := hβ (fun t => (ε ^ r) (v t))
      simp only [pow_succ', Module.End.mul_apply] at h1 ⊢
      rw [h1, ih, map_smul, smul_smul, mul_add, mul_one, pow_add, mul_comm]
  ext v
  simp only [LinearMap.compMultilinearMap_apply, twist_apply, MultilinearMap.smul_apply]
  rw [show (fun t => twistFn ε r n t (v t)) = fun t => (ε ^ r) (v t) from
    funext fun t => by rw [twistFn_of_lt ε _ _ t t.isLt], key, map_smul, pow_pow_apply hε]

/-! ## Koszul compositions -/

variable (ε) in
/-- **The Koszul composition** of an operation `β` of parity `q` into the slot `i` of `α`: the
inputs before the slot are twisted by `ε^q`. -/
def kcompFin (q : ℕ) {m n : ℕ} (i : Fin m) (α : End R V m) (β : End R V n) :
    End R V (m - 1 + n) :=
  compFin (R := R) i (twist ε q i α) β

/-- **Sequential associativity of Koszul compositions**, with no sign. -/
theorem kcompFin_assoc_seq (q r : ℕ) {m n p : ℕ} (i : Fin m) (j : Fin n) (α : End R V m)
    (β : End R V n) (γ : End R V p) :
    reindex R (End R V) (by have := i.isLt; have := j.isLt; omega)
        (kcompFin ε r
          (⟨(i : ℕ) + (j : ℕ), by have := i.isLt; have := j.isLt; omega⟩ : Fin (m - 1 + n))
          (kcompFin ε q i α β) γ)
      = kcompFin ε (q + r) i α (kcompFin ε r j β γ) := by
  unfold kcompFin
  rw [show twist ε r ((i : ℕ) + (j : ℕ)) (compFin (R := R) i (twist ε q i α) β)
      = compFin (R := R) i (twist ε r i (twist ε q i α)) (twist ε r j β) from
    twist_compFin_nested ε r i j j.isLt.le _ β, compFin_assoc_seq, twist_twist]

/-- **Parallel associativity of Koszul compositions**, up to the Koszul sign `(-1)^(q r)` of
moving `γ` (parity `r`) across `β` (parity `q`). -/
theorem kcompFin_assoc_par (hε : ∀ x, ε (ε x) = x) (q r : ℕ) {m n p : ℕ} (i i' : Fin m)
    (hlt : (i : ℕ) < (i' : ℕ)) (α : End R V m) {β : End R V n} (hβ : IsHomog ε q β)
    (γ : End R V p) :
    kcompFin ε r (⟨(i' : ℕ) + n - 1, by have := i'.isLt; omega⟩ : Fin (m - 1 + n))
        (kcompFin ε q i α β) γ
      = (-1 : R) ^ (q * r) • reindex R (End R V) (by have := i'.isLt; omega)
          (kcompFin ε q (⟨(i : ℕ), by have := i'.isLt; omega⟩ : Fin (m - 1 + p))
            (kcompFin ε r i' α γ) β) := by
  unfold kcompFin
  rw [twist_compFin_par ε hε r i i' hlt, hβ.conj hε, compFin_smul_right, compFin_smul_left,
    compFin_assoc_par i i' hlt, ← compFin_twist_left ε q (i : ℕ) i' hlt.le (twist ε r i' α) γ,
    twist_comm]

/-! ## The Koszul circle product -/

lemma kcompFin_sum_left (q : ℕ) {m n : ℕ} {ι : Type*} (s : Finset ι) (i : Fin m)
    (f : ι → End R V m) (β : End R V n) :
    kcompFin ε q i (∑ x ∈ s, f x) β = ∑ x ∈ s, kcompFin ε q i (f x) β := by
  unfold kcompFin
  rw [map_sum, compFin_sum_left]

lemma kcompFin_sum_right (q : ℕ) {m n : ℕ} {ι : Type*} (s : Finset ι) (i : Fin m)
    (α : End R V m) (g : ι → End R V n) :
    kcompFin ε q i α (∑ x ∈ s, g x) = ∑ x ∈ s, kcompFin ε q i α (g x) :=
  compFin_sum_right _ _ _ _

variable (ε) in
/-- **The Koszul circle product** `α ⋆ β = ∑ᵢ α ∘ᵏᵢ β`, for `β` of parity `q`. -/
def kstar (q : ℕ) {j k : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1)) : End R V (j + k + 1) :=
  ∑ i : Fin (j + 1), kcompFin ε q i α β

lemma kstar_kstar_left (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) :
    kstar ε r (kstar ε q α β) γ
      = ∑ i' : Fin (j + k + 1), ∑ i : Fin (j + 1), kcompFin ε r i' (kcompFin ε q i α β) γ := by
  unfold kstar
  exact Finset.sum_congr rfl fun i' _ => kcompFin_sum_left _ _ _ _ _

lemma kstar_kstar_right (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) :
    kstar ε (q + r) α (kstar ε r β γ)
      = ∑ i : Fin (j + 1), ∑ i'' : Fin (k + 1),
          kcompFin ε (q + r) i α (kcompFin ε r i'' β γ) := by
  unfold kstar
  exact Finset.sum_congr rfl fun i _ => kcompFin_sum_right _ _ _ _ _

variable (ε) in
/-- The part of the associator of `⋆` that survives: the pairs of disjoint slots. -/
def kdisjointPart (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) : End R V (j + k + l + 1) :=
  ∑ i : Fin (j + 1), ∑ i' ∈ (nested (k := k) i)ᶜ, kcompFin ε r i' (kcompFin ε q i α β) γ

lemma sum_nested_k (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) (i : Fin (j + 1)) :
    reindex R (End R V) (by omega)
        (∑ i' ∈ nested (k := k) i, kcompFin ε r i' (kcompFin ε q i α β) γ)
      = ∑ i'' : Fin (k + 1), kcompFin ε (q + r) i α (kcompFin ε r i'' β γ) := by
  rw [nested, Finset.sum_map, map_sum]
  exact Finset.sum_congr rfl fun i'' _ => kcompFin_assoc_seq q r i i'' α β γ

/-- **The associator of `⋆`, isolated**: `(α ⋆ β) ⋆ γ` is `α ⋆ (β ⋆ γ)` plus the disjoint
part. -/
lemma kstar_kstar_left_split (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) :
    kstar ε r (kstar ε q α β) γ
      = reindex R (End R V) (by omega) (kstar ε (q + r) α (kstar ε r β γ))
        + kdisjointPart ε q r α β γ := by
  have key : ∀ i : Fin (j + 1),
      (∑ i' : Fin (j + k + 1), kcompFin ε r i' (kcompFin ε q i α β) γ)
        = reindex R (End R V) (by omega)
            (∑ i'' : Fin (k + 1), kcompFin ε (q + r) i α (kcompFin ε r i'' β γ))
          + ∑ i' ∈ (nested (k := k) i)ᶜ, kcompFin ε r i' (kcompFin ε q i α β) γ := by
    intro i
    rw [← Finset.sum_add_sum_compl (nested (k := k) i)]
    congr 1
    rw [← sum_nested_k q r α β γ i, reindex_reindex, reindex_self]
  rw [kstar_kstar_left, Finset.sum_comm, kdisjointPart,
    Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib]
  congr 1
  rw [kstar_kstar_right]
  exact (map_sum _ _ _).symm

lemma neg_one_pow_mul_self (n : ℕ) : ((-1 : R) ^ n) * (-1 : R) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

variable (ε) in
/-- The pairs of disjoint slots with the second insertion before the first. -/
def kbefore (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) : End R V (j + k + l + 1) :=
  ∑ i : Fin (j + 1), ∑ i' ∈ before (k := k) i, kcompFin ε r i' (kcompFin ε q i α β) γ

variable (ε) in
/-- The pairs of disjoint slots with the second insertion after the first. -/
def kafter (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) : End R V (j + k + l + 1) :=
  ∑ i : Fin (j + 1), ∑ i' ∈ after (k := k) i, kcompFin ε r i' (kcompFin ε q i α β) γ

lemma kdisjointPart_eq (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) :
    kdisjointPart ε q r α β γ = kbefore ε q r α β γ + kafter ε q r α β γ := by
  unfold kdisjointPart kbefore kafter
  rw [Finset.sum_congr rfl fun i _ => sum_compl_nested i _, Finset.sum_add_distrib]

variable (hε : ∀ x, ε (ε x) = x)
include hε

/-- The pairs with `γ` before `β`. -/
lemma sum_before_eq_k (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    {γ : End R V (l + 1)} (hγ : IsHomog ε r γ) :
    ((∑ i : Fin (j + 1), ∑ i' ∈ before (k := k) i,
        kcompFin ε r i' (kcompFin ε q i α β) γ) : End R V (j + k + l + 1))
      = ∑ s : Fin (j + 1), ∑ t ∈ after (k := l) s,
          (-1 : R) ^ (q * r) • reindex R (End R V) (by omega)
            (kcompFin ε q t (kcompFin ε r s α γ) β) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x => ⟨⟨min (x.2 : ℕ) j, by omega⟩, ⟨(x.1 : ℕ) + l, by have := x.1.isLt; omega⟩⟩)
    (fun y => ⟨⟨(y.2 : ℕ) - l, by have := y.2.isLt; omega⟩,
               ⟨(y.1 : ℕ), by have := y.1.isLt; omega⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and] at hx
    have := i.isLt
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and]
    show min (i' : ℕ) j + l < (i : ℕ) + l
    omega
  · rintro ⟨s, t⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and] at hy
    have := s.isLt
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and]
    show (s : ℕ) < (t : ℕ) - l
    omega
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and] at hx
    have := i.isLt
    simp only [Sigma.mk.injEq, heq_iff_eq, Fin.ext_iff]
    omega
  · rintro ⟨s, t⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and] at hy
    have := s.isLt
    simp only [Sigma.mk.injEq, heq_iff_eq, Fin.ext_iff]
    omega
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and] at hx
    have hij := i.isLt
    have hmin : min (i' : ℕ) j = (i' : ℕ) := by omega
    dsimp only
    have key : kcompFin ε q (⟨(i : ℕ) + l, by omega⟩ : Fin (j + l + 1))
          (kcompFin ε r (⟨min (i' : ℕ) j, by omega⟩ : Fin (j + 1)) α γ) β
        = (-1 : R) ^ (r * q) • reindex R (End R V) (by omega)
            (kcompFin ε r (⟨min (i' : ℕ) j, by omega⟩ : Fin (j + k + 1))
              (kcompFin ε q i α β) γ) :=
      kcompFin_assoc_par hε r q _ _ (by show min (i' : ℕ) j < (i : ℕ); omega) α hγ β
    rw [key, show (⟨min (i' : ℕ) j, by omega⟩ : Fin (j + k + 1)) = i' from Fin.ext hmin,
      map_smul, reindex_reindex, smul_smul, Nat.mul_comm r q, neg_one_pow_mul_self, one_smul]
    exact (reindex_self _ _).symm

/-- The pairs with `γ` after `β`. -/
lemma sum_after_eq_k (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) {β : End R V (k + 1)}
    (hβ : IsHomog ε q β) (γ : End R V (l + 1)) :
    ((∑ i : Fin (j + 1), ∑ i' ∈ after (k := k) i,
        kcompFin ε r i' (kcompFin ε q i α β) γ) : End R V (j + k + l + 1))
      = ∑ s : Fin (j + 1), ∑ t ∈ before (k := l) s,
          (-1 : R) ^ (q * r) • reindex R (End R V) (by omega)
            (kcompFin ε q t (kcompFin ε r s α γ) β) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x => ⟨⟨(x.2 : ℕ) - k, by have := x.2.isLt; omega⟩,
               ⟨(x.1 : ℕ), by have := x.1.isLt; omega⟩⟩)
    (fun y => ⟨⟨min (y.2 : ℕ) j, by omega⟩,
               ⟨(y.1 : ℕ) + k, by have := y.1.isLt; omega⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and] at hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and]
    show (i : ℕ) < (i' : ℕ) - k
    omega
  · rintro ⟨s, t⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and] at hy
    have := s.isLt
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and]
    show min (t : ℕ) j + k < (s : ℕ) + k
    omega
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and] at hx
    have := i.isLt
    simp only [Sigma.mk.injEq, heq_iff_eq, Fin.ext_iff]
    omega
  · rintro ⟨s, t⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_before, true_and] at hy
    have := s.isLt
    simp only [Sigma.mk.injEq, heq_iff_eq, Fin.ext_iff]
    omega
  · rintro ⟨i, i'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, mem_after, true_and] at hx
    have hi' := i'.isLt
    dsimp only
    have h := kcompFin_assoc_par hε q r i (⟨(i' : ℕ) - k, by omega⟩ : Fin (j + 1))
      (by show (i : ℕ) < (i' : ℕ) - k; omega) α hβ γ
    dsimp only at h
    conv_lhs =>
      rw [show i' = (⟨(i' : ℕ) - k + k, by omega⟩ : Fin (j + k + 1)) from
        Fin.ext (show (i' : ℕ) = (i' : ℕ) - k + k by omega)]
    exact h

/-- The pairs with `γ` before `β` are those with `β` after `γ`, up to the Koszul sign. -/
lemma kbefore_eq (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    {γ : End R V (l + 1)} (hγ : IsHomog ε r γ) :
    kbefore ε q r α β γ
      = (-1 : R) ^ (q * r) • reindex R (End R V) (by omega) (kafter ε r q α γ β) := by
  unfold kbefore kafter
  rw [sum_before_eq_k hε q r α β hγ, map_sum, Finset.smul_sum]
  simp only [map_sum, Finset.smul_sum]
  rfl

/-- **The disjoint part is graded symmetric** in `β` and `γ`. -/
theorem kdisjointPart_symm (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) {β : End R V (k + 1)}
    (hβ : IsHomog ε q β) {γ : End R V (l + 1)} (hγ : IsHomog ε r γ) :
    kdisjointPart ε q r α β γ
      = (-1 : R) ^ (q * r) • reindex R (End R V) (by omega) (kdisjointPart ε r q α γ β) := by
  unfold kdisjointPart
  rw [Finset.sum_congr rfl fun i _ => sum_compl_nested i _,
    Finset.sum_congr rfl fun s _ => sum_compl_nested s _,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [sum_before_eq_k hε q r α β hγ, sum_after_eq_k hε q r α hβ γ, map_add, smul_add,
    map_sum, map_sum, Finset.smul_sum, Finset.smul_sum]
  simp only [map_sum, Finset.smul_sum]
  exact add_comm _ _

/-- **The graded pre-Lie identity**: the associator of the Koszul circle product is graded
symmetric in its last two arguments. -/
theorem kstar_assoc_symm (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) {β : End R V (k + 1)}
    (hβ : IsHomog ε q β) {γ : End R V (l + 1)} (hγ : IsHomog ε r γ) :
    kstar ε r (kstar ε q α β) γ
        - reindex R (End R V) (by omega) (kstar ε (q + r) α (kstar ε r β γ))
      = (-1 : R) ^ (q * r) • (reindex R (End R V) (by omega) (kstar ε q (kstar ε r α γ) β)
        - reindex R (End R V) (by omega) (kstar ε (r + q) α (kstar ε q γ β))) := by
  rw [kstar_kstar_left_split q r α β γ, kstar_kstar_left_split r q α γ β, map_add,
    kdisjointPart_symm hε q r α hβ hγ]
  simp only [reindex_reindex, add_sub_cancel_left]

/-- **An odd operation cancels against itself**: for odd `β`,
`(α ⋆ β) ⋆ β = α ⋆ (β ⋆ β)`, with no division by two. -/
theorem kstar_kstar_odd {j k : ℕ} (α : End R V (j + 1)) {β : End R V (k + 1)}
    (hβ : IsHomog ε 1 β) :
    kstar ε 1 (kstar ε 1 α β) β
      = reindex R (End R V) (by omega) (kstar ε (1 + 1) α (kstar ε 1 β β)) := by
  rw [kstar_kstar_left_split, add_eq_left]
  unfold kdisjointPart
  rw [Finset.sum_congr rfl fun i _ => sum_compl_nested i _, Finset.sum_add_distrib,
    sum_before_eq_k hε 1 1 α β hβ, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun t _ => ?_
  erw [reindex_self]
  simp

end End

end Operad
