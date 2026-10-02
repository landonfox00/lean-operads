/-
# The operad `Perm`

Chapoton's operad, non-symmetrically: `Perm R n = Fin n → R`, with

`(α ∘ β)_j = (Σβ)·α_j` outside the inserted block and `α_a · β_{j-a}` inside it,

where `a` is the slot. Its algebras are permutative algebras, and it is the target of every
"value" in the game-theoretic application this library was started for.

## Why this one is different

Every other operad here keeps index data out of its types — that is the design decision the
library rests on, and it is why the coherence obligations elsewhere are `omega` goals with no `Fin`
arithmetic. `Perm` cannot: its elements *are* indexed by the inputs, so composition is a three-way
case split on the index and the axioms are genuinely `Fin`-sum bookkeeping. That is not a failure
of the convention; it is the one place where the mathematics puts the index in the element.

Three things keep it manageable.

* `sum_split3` splits a sum over `Fin (a + n + b)` into the three ranges, once, so no proof below
  ever touches `Fin.castAdd` or `Fin.natAdd`.
* `permComp_apply_lt`, `_mid`, `_ge` give the value in each range, taking the index bounds as
  explicit arguments rather than rebuilding them, so every branch closes with `omega` on indices
  and `ring` on coefficients.
* `sum_permComp` — the total of a composite is the product of the totals — is proved *before* the
  associativity axioms, because both of them need it.

**`omega` does not know `Fin.isLt`.** Every bound in this file is introduced with
`have := i.isLt` first; without it `omega` sees an unconstrained natural and fails. That is the
single most repeated idiom below.
-/
import Operad.Basic
import Operad.Constructions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

universe u

-- `simp only [val_mk']` is applied uniformly before every arithmetic goal in this file; in the
-- branches where the index is already a bare variable it has nothing to do, and dropping it
-- there would make the proofs read differently from case to case for no gain.
set_option linter.unusedSimpArgs false

namespace Operad

open Finset

/-- **The operad `Perm`**: `R`-valued functions on the inputs.  An `abbrev`, so the `Pi` module
structure transfers without an instance mismatch. -/
@[nolint unusedArguments]
abbrev Perm (R : Type u) [CommRing R] : ℕ → Type u := fun n => Fin n → R

namespace Perm

variable {R : Type u} [CommRing R]

/-! ## 1. Splitting a sum over the three ranges -/

/-- A sum over `Fin (a + n + b)` splits into the part before the inserted block, the block, and
the part after.  Stated with explicit `Fin.mk`s so that no later proof mentions `Fin.castAdd`. -/
lemma sum_split3 {M : Type u} [AddCommMonoid M] {a n b : ℕ} (f : Fin (a + n + b) → M) :
    ∑ j, f j
      = ((∑ i : Fin a, f (Fin.castAdd b (Fin.castAdd n i)))
          + ∑ i : Fin n, f (Fin.castAdd b (Fin.natAdd a i)))
        + ∑ i : Fin b, f (Fin.natAdd (a + n) i) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add]

/-- The coordinate of an explicit `Fin`.  `omega` treats `↑⟨x, h⟩` as an atom unless this fires
first, which is why it appears in front of almost every arithmetic goal below. -/
lemma val_mk' {n : ℕ} (x : ℕ) (h : x < n) : ((⟨x, h⟩ : Fin n) : ℕ) = x := rfl

/-- Reindexing `Perm` along an equality of arities is reindexing the argument. -/
@[simp] lemma reindex_apply {m n : ℕ} (h : m = n) (x : Perm R m) (j : Fin n) :
    reindex R (Perm R) h x j = x ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  subst h; rfl

/-! ## 2. Composition -/

/-- Partial composition in `Perm`: outside the inserted block the value is scaled by the total of
the inserted operation, inside it the slot's own value scales the inserted one. -/
def permComp (a b : ℕ) {n : ℕ} (α : Perm R (a + 1 + b)) (β : Perm R n) : Perm R (a + n + b) :=
  fun j =>
    if h1 : (j : ℕ) < a then (∑ t, β t) * α ⟨(j : ℕ), by omega⟩
    else if h2 : (j : ℕ) < a + n then α ⟨a, by omega⟩ * β ⟨(j : ℕ) - a, by omega⟩
    else (∑ t, β t) * α ⟨(j : ℕ) - n + 1, by have := j.isLt; omega⟩

lemma permComp_apply_lt (a b : ℕ) {n : ℕ} (α : Perm R (a + 1 + b)) (β : Perm R n)
    (j : Fin (a + n + b)) (h : (j : ℕ) < a) (hlt : (j : ℕ) < a + 1 + b) :
    permComp a b α β j = (∑ t, β t) * α ⟨(j : ℕ), hlt⟩ := by
  rw [permComp, dif_pos h]

lemma permComp_apply_mid (a b : ℕ) {n : ℕ} (α : Perm R (a + 1 + b)) (β : Perm R n)
    (j : Fin (a + n + b)) (h1 : a ≤ (j : ℕ)) (h2 : (j : ℕ) < a + n)
    (ha : a < a + 1 + b) (hb : (j : ℕ) - a < n) :
    permComp a b α β j = α ⟨a, ha⟩ * β ⟨(j : ℕ) - a, hb⟩ := by
  rw [permComp, dif_neg (by omega), dif_pos h2]

lemma permComp_apply_ge (a b : ℕ) {n : ℕ} (α : Perm R (a + 1 + b)) (β : Perm R n)
    (j : Fin (a + n + b)) (h : a + n ≤ (j : ℕ)) (hlt : (j : ℕ) - n + 1 < a + 1 + b) :
    permComp a b α β j = (∑ t, β t) * α ⟨(j : ℕ) - n + 1, hlt⟩ := by
  rw [permComp, dif_neg (by omega), dif_neg (by omega)]

/-! ## 3. Bilinearity

Each law is the same three-way split, and in each branch the statement is a ring identity in one
or two values of `α` and `β`. -/

lemma permComp_add_left (a b : ℕ) {n : ℕ} (α α' : Perm R (a + 1 + b)) (β : Perm R n) :
    permComp a b (α + α') β = permComp a b α β + permComp a b α' β := by
  funext j
  have hj := j.isLt
  show permComp a b (α + α') β j = permComp a b α β j + permComp a b α' β j
  by_cases h1 : (j : ℕ) < a
  · rw [permComp_apply_lt _ _ _ _ _ h1 (by omega), permComp_apply_lt _ _ _ _ _ h1 (by omega),
      permComp_apply_lt _ _ _ _ _ h1 (by omega)]
    show (∑ t, β t) * (α _ + α' _) = _
    ring
  · by_cases h2 : (j : ℕ) < a + n
    · rw [permComp_apply_mid _ _ _ _ _ (by omega) h2 (by omega) (by omega),
        permComp_apply_mid _ _ _ _ _ (by omega) h2 (by omega) (by omega),
        permComp_apply_mid _ _ _ _ _ (by omega) h2 (by omega) (by omega)]
      show (α _ + α' _) * β _ = _
      ring
    · rw [permComp_apply_ge _ _ _ _ _ (by omega) (by omega),
        permComp_apply_ge _ _ _ _ _ (by omega) (by omega),
        permComp_apply_ge _ _ _ _ _ (by omega) (by omega)]
      show (∑ t, β t) * (α _ + α' _) = _
      ring

lemma permComp_smul_left (a b : ℕ) {n : ℕ} (r : R) (α : Perm R (a + 1 + b)) (β : Perm R n) :
    permComp a b (r • α) β = r • permComp a b α β := by
  funext j
  have hj := j.isLt
  show permComp a b (r • α) β j = r * permComp a b α β j
  by_cases h1 : (j : ℕ) < a
  · rw [permComp_apply_lt _ _ _ _ _ h1 (by omega), permComp_apply_lt _ _ _ _ _ h1 (by omega)]
    show (∑ t, β t) * (r * α _) = _
    ring
  · by_cases h2 : (j : ℕ) < a + n
    · rw [permComp_apply_mid _ _ _ _ _ (by omega) h2 (by omega) (by omega),
        permComp_apply_mid _ _ _ _ _ (by omega) h2 (by omega) (by omega)]
      show (r * α _) * β _ = _
      ring
    · rw [permComp_apply_ge _ _ _ _ _ (by omega) (by omega),
        permComp_apply_ge _ _ _ _ _ (by omega) (by omega)]
      show (∑ t, β t) * (r * α _) = _
      ring

lemma permComp_add_right (a b : ℕ) {n : ℕ} (α : Perm R (a + 1 + b)) (β β' : Perm R n) :
    permComp a b α (β + β') = permComp a b α β + permComp a b α β' := by
  funext j
  have hj := j.isLt
  have hsum : (∑ t, (β + β') t) = (∑ t, β t) + ∑ t, β' t := by
    rw [← Finset.sum_add_distrib]; rfl
  show permComp a b α (β + β') j = permComp a b α β j + permComp a b α β' j
  by_cases h1 : (j : ℕ) < a
  · rw [permComp_apply_lt _ _ _ _ _ h1 (by omega), permComp_apply_lt _ _ _ _ _ h1 (by omega),
      permComp_apply_lt _ _ _ _ _ h1 (by omega), hsum]
    ring
  · by_cases h2 : (j : ℕ) < a + n
    · rw [permComp_apply_mid _ _ _ _ _ (by omega) h2 (by omega) (by omega),
        permComp_apply_mid _ _ _ _ _ (by omega) h2 (by omega) (by omega),
        permComp_apply_mid _ _ _ _ _ (by omega) h2 (by omega) (by omega)]
      show α _ * (β _ + β' _) = _
      ring
    · rw [permComp_apply_ge _ _ _ _ _ (by omega) (by omega),
        permComp_apply_ge _ _ _ _ _ (by omega) (by omega),
        permComp_apply_ge _ _ _ _ _ (by omega) (by omega), hsum]
      ring

lemma permComp_smul_right (a b : ℕ) {n : ℕ} (r : R) (α : Perm R (a + 1 + b)) (β : Perm R n) :
    permComp a b α (r • β) = r • permComp a b α β := by
  funext j
  have hj := j.isLt
  have hsum : (∑ t, (r • β) t) = r * ∑ t, β t := by
    rw [Finset.mul_sum]; rfl
  show permComp a b α (r • β) j = r * permComp a b α β j
  by_cases h1 : (j : ℕ) < a
  · rw [permComp_apply_lt _ _ _ _ _ h1 (by omega), permComp_apply_lt _ _ _ _ _ h1 (by omega),
      hsum]
    ring
  · by_cases h2 : (j : ℕ) < a + n
    · rw [permComp_apply_mid _ _ _ _ _ (by omega) h2 (by omega) (by omega),
        permComp_apply_mid _ _ _ _ _ (by omega) h2 (by omega) (by omega)]
      show α _ * (r * β _) = _
      ring
    · rw [permComp_apply_ge _ _ _ _ _ (by omega) (by omega),
        permComp_apply_ge _ _ _ _ _ (by omega) (by omega), hsum]
      ring

/-- Composition, bundled as a bilinear map. -/
def compL (a b : ℕ) {n : ℕ} :
    Perm R (a + 1 + b) →ₗ[R] Perm R n →ₗ[R] Perm R (a + n + b) :=
  LinearMap.mk₂ R (permComp a b)
    (permComp_add_left a b) (fun r α β => permComp_smul_left a b r α β)
    (permComp_add_right a b) (fun r α β => permComp_smul_right a b r α β)

@[simp] lemma compL_apply (a b : ℕ) {n : ℕ} (α : Perm R (a + 1 + b)) (β : Perm R n) :
    compL a b α β = permComp a b α β := rfl

/-! ## 4. The total of a composite

This is the lemma both associativity axioms need, and it is the statement that summing is a
morphism of operads `Perm → Ass`. -/

/-- **The total of a composite is the product of the totals.** -/
theorem sum_permComp (a b : ℕ) {n : ℕ} (α : Perm R (a + 1 + b)) (β : Perm R n) :
    (∑ j, permComp a b α β j) = (∑ i, α i) * ∑ t, β t := by
  rw [sum_split3 (permComp a b α β), sum_split3 α]
  have h1 : ∀ i : Fin a, permComp a b α β (Fin.castAdd b (Fin.castAdd n i))
      = (∑ t, β t) * α (Fin.castAdd b (Fin.castAdd 1 i)) := by
    intro i
    have hi := i.isLt
    have e1 : ((Fin.castAdd b (Fin.castAdd n i) : Fin (a + n + b)) : ℕ) = (i : ℕ) := by simp
    rw [permComp_apply_lt a b α β _ (by rw [e1]; omega) (by rw [e1]; omega)]
    exact congrArg _ (congrArg α (Fin.ext (by simp)))
  have h2 : ∀ i : Fin n, permComp a b α β (Fin.castAdd b (Fin.natAdd a i))
      = α (Fin.castAdd b (Fin.natAdd a (0 : Fin 1))) * β i := by
    intro i
    have hi := i.isLt
    have e1 : ((Fin.castAdd b (Fin.natAdd a i) : Fin (a + n + b)) : ℕ) = a + (i : ℕ) := by simp
    rw [permComp_apply_mid a b α β _ (by rw [e1]; omega) (by rw [e1]; omega) (by omega)
      (by rw [e1]; omega)]
    refine congrArg₂ (· * ·) (congrArg α (Fin.ext ?_)) (congrArg β (Fin.ext ?_))
    · simp
    · rw [val_mk', e1]; omega
  have h3 : ∀ i : Fin b, permComp a b α β (Fin.natAdd (a + n) i)
      = (∑ t, β t) * α (Fin.natAdd (a + 1) i) := by
    intro i
    have hi := i.isLt
    have e1 : ((Fin.natAdd (a + n) i : Fin (a + n + b)) : ℕ) = a + n + (i : ℕ) := by simp
    rw [permComp_apply_ge a b α β _ (by rw [e1]; omega) (by rw [e1]; omega)]
    refine congrArg _ (congrArg α (Fin.ext ?_))
    rw [val_mk', e1]
    simp
    omega
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_congr rfl fun i _ => h2 i,
    Finset.sum_congr rfl fun i _ => h3 i]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hone : (∑ i : Fin 1, α (Fin.castAdd b (Fin.natAdd a i)))
      = α (Fin.castAdd b (Fin.natAdd a (0 : Fin 1))) := by simp
  rw [hone]
  ring

/-! ## 5. The four axioms

Each is `funext` followed by the same case analysis on where the index falls, with `omega` on the
indices and `ring` on the coefficients.  The two associativity axioms split into five ranges, and
in each range both sides reduce to a product of the same three values of `α`, `β`, `γ`. -/

/-- The identity of `Perm`: the unique operation of arity one, with value `1`. -/
def permOne : Perm R 1 := fun _ => 1

lemma sum_permOne : (∑ t, (permOne : Perm R 1) t) = 1 := by simp [permOne]

theorem permComp_one_right (a b : ℕ) (α : Perm R (a + 1 + b)) :
    permComp a b α permOne = α := by
  funext j
  have hj := j.isLt
  by_cases h1 : (j : ℕ) < a
  · rw [permComp_apply_lt _ _ _ _ _ h1 (by omega), sum_permOne, one_mul]
  · by_cases h2 : (j : ℕ) < a + 1
    · rw [permComp_apply_mid _ _ _ _ _ (by omega) h2 (by omega) (by omega)]
      show α _ * (1 : R) = _
      rw [mul_one]
      exact congrArg α (Fin.ext (by simp only [val_mk']; omega))
    · rw [permComp_apply_ge _ _ _ _ _ (by omega) (by omega), sum_permOne, one_mul]
      exact congrArg α (Fin.ext (by simp only [val_mk']; omega))

theorem permComp_one_left {n : ℕ} (α : Perm R n) :
    reindex R (Perm R) (show 0 + n + 0 = n by omega) (permComp 0 0 permOne α) = α := by
  funext j
  have hj := j.isLt
  rw [reindex_apply, permComp_apply_mid 0 0 permOne α _ (by rw [val_mk']; omega)
    (by rw [val_mk']; omega) (by omega) (by rw [val_mk']; omega)]
  show (1 : R) * α _ = _
  rw [one_mul]
  exact congrArg α (Fin.ext (by simp))

theorem permComp_assoc_seq (a b c d : ℕ) {p : ℕ} (α : Perm R (a + 1 + b))
    (β : Perm R (c + 1 + d)) (γ : Perm R p) :
    reindex R (Perm R) (show a + c + p + (d + b) = a + (c + p + d) + b by omega)
        (permComp (a + c) (d + b)
          (reindex R (Perm R) (show a + (c + 1 + d) + b = a + c + 1 + (d + b) by omega)
            (permComp a b α β)) γ)
      = permComp a b α (permComp c d β γ) := by
  funext j
  have hj := j.isLt
  rw [reindex_apply]
  by_cases k1 : (j : ℕ) < a
  · rw [permComp_apply_lt (a + c) (d + b) _ γ _ (by rw [val_mk']; omega)
        (by rw [val_mk']; omega),
      reindex_apply,
      permComp_apply_lt a b α β _ (by simp only [val_mk']; omega)
        (by simp only [val_mk']; omega),
      permComp_apply_lt a b α (permComp c d β γ) j k1 (by omega),
      sum_permComp]
    simp only [val_mk']
    ring
  · by_cases k2 : (j : ℕ) < a + c
    · rw [permComp_apply_lt (a + c) (d + b) _ γ _ (by rw [val_mk']; omega)
          (by rw [val_mk']; omega),
        reindex_apply,
        permComp_apply_mid a b α β _ (by simp only [val_mk']; omega)
          (by simp only [val_mk']; omega) (by omega) (by simp only [val_mk']; omega),
        permComp_apply_mid a b α (permComp c d β γ) j (by omega) (by omega) (by omega)
          (by omega),
        permComp_apply_lt c d β γ _ (by rw [val_mk']; omega) (by rw [val_mk']; omega)]
      simp only [val_mk']
      ring
    · by_cases k3 : (j : ℕ) < a + c + p
      · rw [permComp_apply_mid (a + c) (d + b) _ γ _ (by rw [val_mk']; omega)
            (by rw [val_mk']; omega) (by omega) (by rw [val_mk']; omega),
          reindex_apply,
          permComp_apply_mid a b α β _ (by simp only [val_mk']; omega)
            (by simp only [val_mk']; omega) (by omega) (by simp only [val_mk']; omega),
          permComp_apply_mid a b α (permComp c d β γ) j (by omega) (by omega) (by omega)
            (by omega),
          permComp_apply_mid c d β γ _ (by rw [val_mk']; omega) (by rw [val_mk']; omega)
            (by omega) (by rw [val_mk']; omega)]
        simp only [val_mk']
        rw [show ((⟨a + c - a, by omega⟩ : Fin (c + 1 + d))) = ⟨c, by omega⟩ from
          Fin.ext (by simp only [val_mk']; omega)]
        rw [show ((⟨(j : ℕ) - (a + c), by omega⟩ : Fin p))
            = ⟨(j : ℕ) - a - c, by omega⟩ from Fin.ext (by simp only [val_mk']; omega)]
        ring
      · by_cases k4 : (j : ℕ) < a + c + p + d
        · rw [permComp_apply_ge (a + c) (d + b) _ γ _ (by rw [val_mk']; omega)
              (by rw [val_mk']; omega),
            reindex_apply,
            permComp_apply_mid a b α β _ (by simp only [val_mk']; omega)
              (by simp only [val_mk']; omega) (by omega) (by simp only [val_mk']; omega),
            permComp_apply_mid a b α (permComp c d β γ) j (by omega) (by omega) (by omega)
              (by omega),
            permComp_apply_ge c d β γ _ (by rw [val_mk']; omega) (by rw [val_mk']; omega)]
          simp only [val_mk']
          rw [show ((⟨(j : ℕ) - p + 1 - a, by omega⟩ : Fin (c + 1 + d)))
              = ⟨(j : ℕ) - a - p + 1, by omega⟩ from Fin.ext (by simp only [val_mk']; omega)]
          ring
        · rw [permComp_apply_ge (a + c) (d + b) _ γ _ (by rw [val_mk']; omega)
              (by rw [val_mk']; omega),
            reindex_apply,
            permComp_apply_ge a b α β _ (by simp only [val_mk']; omega)
              (by simp only [val_mk']; omega),
            permComp_apply_ge a b α (permComp c d β γ) j (by omega) (by omega),
            sum_permComp]
          simp only [val_mk']
          rw [show ((⟨(j : ℕ) - p + 1 - (c + 1 + d) + 1, by omega⟩ : Fin (a + 1 + b)))
              = ⟨(j : ℕ) - (c + p + d) + 1, by omega⟩ from Fin.ext (by simp only [val_mk']; omega)]
          ring

theorem permComp_assoc_par (a b c : ℕ) {n p : ℕ} (α : Perm R (a + 1 + b + 1 + c))
    (β : Perm R n) (γ : Perm R p) :
    reindex R (Perm R) (show a + n + b + p + c = a + n + (b + p + c) by omega)
        (permComp (a + n + b) c
          (reindex R (Perm R) (show a + n + (b + 1 + c) = a + n + b + 1 + c by omega)
            (permComp a (b + 1 + c)
              (reindex R (Perm R) (show a + 1 + b + 1 + c = a + 1 + (b + 1 + c) by omega) α)
              β)) γ)
      = permComp a (b + p + c)
          (reindex R (Perm R) (show a + 1 + b + p + c = a + 1 + (b + p + c) by omega)
            (permComp (a + 1 + b) c α γ)) β := by
  funext j
  have hj := j.isLt
  rw [reindex_apply]
  by_cases k1 : (j : ℕ) < a
  · rw [permComp_apply_lt (a + n + b) c _ γ _ (by rw [val_mk']; omega)
        (by rw [val_mk']; omega),
      reindex_apply,
      permComp_apply_lt a (b + 1 + c) _ β _ (by simp only [val_mk']; omega)
        (by simp only [val_mk']; omega),
      reindex_apply,
      permComp_apply_lt a (b + p + c) _ β j k1 (by omega),
      reindex_apply,
      permComp_apply_lt (a + 1 + b) c α γ _ (by simp only [val_mk']; omega)
        (by simp only [val_mk']; omega)]
    simp only [val_mk']
    ring
  · by_cases k2 : (j : ℕ) < a + n
    · rw [permComp_apply_lt (a + n + b) c _ γ _ (by rw [val_mk']; omega)
          (by rw [val_mk']; omega),
        reindex_apply,
        permComp_apply_mid a (b + 1 + c) _ β _ (by simp only [val_mk']; omega)
          (by simp only [val_mk']; omega) (by omega) (by simp only [val_mk']; omega),
        reindex_apply,
        permComp_apply_mid a (b + p + c) _ β j (by omega) k2 (by omega) (by omega),
        reindex_apply,
        permComp_apply_lt (a + 1 + b) c α γ _ (by simp only [val_mk']; omega)
          (by simp only [val_mk']; omega)]
      simp only [val_mk']
      ring
    · by_cases k3 : (j : ℕ) < a + n + b
      · rw [permComp_apply_lt (a + n + b) c _ γ _ (by rw [val_mk']; omega)
            (by rw [val_mk']; omega),
          reindex_apply,
          permComp_apply_ge a (b + 1 + c) _ β _ (by simp only [val_mk']; omega)
            (by simp only [val_mk']; omega),
          reindex_apply,
          permComp_apply_ge a (b + p + c) _ β j (by omega) (by omega),
          reindex_apply,
          permComp_apply_lt (a + 1 + b) c α γ _ (by simp only [val_mk']; omega)
            (by simp only [val_mk']; omega)]
        simp only [val_mk']
        ring
      · by_cases k4 : (j : ℕ) < a + n + b + p
        · rw [permComp_apply_mid (a + n + b) c _ γ _ (by rw [val_mk']; omega)
              (by rw [val_mk']; omega) (by omega) (by rw [val_mk']; omega),
            reindex_apply,
            permComp_apply_ge a (b + 1 + c) _ β _ (by simp only [val_mk']; omega)
              (by simp only [val_mk']; omega),
            reindex_apply,
            permComp_apply_ge a (b + p + c) _ β j (by omega) (by omega),
            reindex_apply,
            permComp_apply_mid (a + 1 + b) c α γ _ (by simp only [val_mk']; omega)
              (by simp only [val_mk']; omega) (by omega) (by simp only [val_mk']; omega)]
          simp only [val_mk']
          rw [show ((⟨a + n + b - n + 1, by omega⟩ : Fin (a + 1 + b + 1 + c)))
              = ⟨a + 1 + b, by omega⟩ from Fin.ext (by simp only [val_mk']; omega)]
          rw [show ((⟨(j : ℕ) - (a + n + b), by omega⟩ : Fin p))
              = ⟨(j : ℕ) - n + 1 - (a + 1 + b), by omega⟩ from
            Fin.ext (by simp only [val_mk']; omega)]
          ring
        · rw [permComp_apply_ge (a + n + b) c _ γ _ (by rw [val_mk']; omega)
              (by rw [val_mk']; omega),
            reindex_apply,
            permComp_apply_ge a (b + 1 + c) _ β _ (by simp only [val_mk']; omega)
              (by simp only [val_mk']; omega),
            reindex_apply,
            permComp_apply_ge a (b + p + c) _ β j (by omega) (by omega),
            reindex_apply,
            permComp_apply_ge (a + 1 + b) c α γ _ (by simp only [val_mk']; omega)
              (by simp only [val_mk']; omega)]
          simp only [val_mk']
          rw [show ((⟨(j : ℕ) - p + 1 - n + 1, by omega⟩ : Fin (a + 1 + b + 1 + c)))
              = ⟨(j : ℕ) - n + 1 - p + 1, by omega⟩ from
            Fin.ext (by simp only [val_mk']; omega)]
          ring

end Perm

/-! ## 6. The instance, and `ev` -/

open Perm in
/-- **`Perm` is a non-symmetric operad.**  Elaborating this discharges all four axioms. -/
instance instNSOperadPerm (R : Type u) [CommRing R] : NSOperad R (Perm R) where
  one := permOne
  comp a b := compL a b
  comp_one_right := permComp_one_right
  comp_one_left := permComp_one_left
  comp_assoc_seq := by intro a b c d p α β γ; exact permComp_assoc_seq a b c d α β γ
  comp_assoc_par := by intro a b c n p α β γ; exact permComp_assoc_par a b c α β γ

namespace Perm

variable {R : Type u} [CommRing R]

@[simp] lemma comp_eq (a b : ℕ) {n : ℕ} (α : Perm R (a + 1 + b)) (β : Perm R n) :
    NSOperad.comp (R := R) a b α β = permComp a b α β := rfl

@[simp] lemma one_eq : (NSOperad.one (R := R) (P := Perm R)) = permOne := rfl

/-- Summing the coordinates, as a linear map. -/
def evL (n : ℕ) : Perm R n →ₗ[R] Ass R n where
  toFun α := ∑ i, α i
  map_add' α α' := by
    show (∑ i, (α + α') i) = _
    rw [← Finset.sum_add_distrib]; rfl
  map_smul' r α := by
    show (∑ i, (r • α) i) = r * ∑ i, α i
    rw [Finset.mul_sum]
    rfl

/-- **`ev` is a morphism of operads `Perm → Ass`.**  This is `sum_permComp` packaged: the total of
a composite is the product of the totals, which is exactly the statement that summing respects
composition.  In the game-theoretic reading it is efficiency. -/
def evHom (R : Type u) [CommRing R] : NSOperadHom R (Perm R) (Ass R) where
  app := evL
  app_one := by
    show (∑ t, (permOne : Perm R 1) t) = (1 : R)
    exact sum_permOne
  app_comp a b {n} α β := by
    show (∑ j, permComp a b α β j) = (∑ i, α i) * ∑ t, β t
    exact sum_permComp a b α β

end Perm

end Operad
