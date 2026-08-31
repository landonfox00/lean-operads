/-
# The endomorphism operad

`End R V n` is the space of `n`-ary multilinear operations on `V`. This is the operad every
other operad maps into: an algebra over `P` is exactly a morphism `P → End V`.

## How the composition is built

For `comp a b α β`, the inputs `Fin (a + n + b)` split into two kinds:

* those **consumed** by the inserted operation `β`, at positions `midIdx a b j` for `j : Fin n`;
* those that **survive** as inputs of the outer operation `α`, at positions `outIdx a b k` for
  `k : Fin (a + b)`.

`outIdx` covers *both* the block before the slot and the block after it, which collapses what
would naively be a three-way case analysis into a two-way one (`idxCases`). Correspondingly the
outer arity `Fin (a + 1 + b)` splits as the slot `slotPos` together with `outPos k`.
-/
import Operad.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic

universe u v

namespace Operad

open Function

/-- The `n`-ary multilinear operations on `V`. -/
abbrev End (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] :
    ℕ → Type v := fun n => MultilinearMap R (fun _ : Fin n => V) V

namespace End

/-! ### Index bookkeeping

None of this depends on the module structure; it is pure `Fin` combinatorics. -/

section Indices

/-- Position in `Fin (a + n + b)` of the `j`-th input consumed by the inserted operation. -/
def midIdx (a b : ℕ) {n : ℕ} (j : Fin n) : Fin (a + n + b) :=
  ⟨a + j, by have := j.isLt; omega⟩

/-- Position in `Fin (a + n + b)` of the `k`-th surviving input. -/
def outIdx (a b : ℕ) {n : ℕ} (k : Fin (a + b)) : Fin (a + n + b) :=
  if (k : ℕ) < a then ⟨k, by have := k.isLt; omega⟩ else ⟨(k : ℕ) + n, by have := k.isLt; omega⟩

/-- Position of the distinguished slot in the outer arity `Fin (a + 1 + b)`. -/
def slotPos (a b : ℕ) : Fin (a + 1 + b) := ⟨a, by omega⟩

/-- Position in the outer arity `Fin (a + 1 + b)` of the `k`-th non-slot input. -/
def outPos (a b : ℕ) (k : Fin (a + b)) : Fin (a + 1 + b) :=
  if (k : ℕ) < a then ⟨k, by have := k.isLt; omega⟩ else ⟨(k : ℕ) + 1, by have := k.isLt; omega⟩

@[simp] lemma midIdx_val (a b : ℕ) {n : ℕ} (j : Fin n) : (midIdx a b j : ℕ) = a + j := rfl

@[simp] lemma slotPos_val (a b : ℕ) : (slotPos a b : ℕ) = a := rfl

lemma outIdx_val_of_lt (a b : ℕ) {n : ℕ} (k : Fin (a + b)) (h : (k : ℕ) < a) :
    (outIdx (n := n) a b k : ℕ) = (k : ℕ) := by
  unfold outIdx; rw [if_pos h]

lemma outIdx_val_of_not_lt (a b : ℕ) {n : ℕ} (k : Fin (a + b)) (h : ¬ (k : ℕ) < a) :
    (outIdx (n := n) a b k : ℕ) = (k : ℕ) + n := by
  unfold outIdx; rw [if_neg h]

lemma outPos_val_of_lt (a b : ℕ) (k : Fin (a + b)) (h : (k : ℕ) < a) :
    (outPos a b k : ℕ) = (k : ℕ) := by
  unfold outPos; rw [if_pos h]

lemma outPos_val_of_not_lt (a b : ℕ) (k : Fin (a + b)) (h : ¬ (k : ℕ) < a) :
    (outPos a b k : ℕ) = (k : ℕ) + 1 := by
  unfold outPos; rw [if_neg h]

lemma midIdx_injective (a b : ℕ) {n : ℕ} : Injective (midIdx (n := n) a b) := by
  intro j j' h
  have := congrArg Fin.val h
  simp only [midIdx_val] at this
  exact Fin.ext (by omega)

lemma outIdx_injective (a b : ℕ) {n : ℕ} : Injective (outIdx (n := n) a b) := by
  intro k k' h
  have hv := congrArg Fin.val h
  have hk := k.isLt; have hk' := k'.isLt
  refine Fin.ext ?_
  by_cases h1 : (k : ℕ) < a <;> by_cases h2 : (k' : ℕ) < a
  · rw [outIdx_val_of_lt a b k h1, outIdx_val_of_lt a b k' h2] at hv; omega
  · rw [outIdx_val_of_lt a b k h1, outIdx_val_of_not_lt a b k' h2] at hv; omega
  · rw [outIdx_val_of_not_lt a b k h1, outIdx_val_of_lt a b k' h2] at hv; omega
  · rw [outIdx_val_of_not_lt a b k h1, outIdx_val_of_not_lt a b k' h2] at hv; omega

lemma outPos_injective (a b : ℕ) : Injective (outPos a b) := by
  intro k k' h
  have hv := congrArg Fin.val h
  have hk := k.isLt; have hk' := k'.isLt
  refine Fin.ext ?_
  by_cases h1 : (k : ℕ) < a <;> by_cases h2 : (k' : ℕ) < a
  · rw [outPos_val_of_lt a b k h1, outPos_val_of_lt a b k' h2] at hv; omega
  · rw [outPos_val_of_lt a b k h1, outPos_val_of_not_lt a b k' h2] at hv; omega
  · rw [outPos_val_of_not_lt a b k h1, outPos_val_of_lt a b k' h2] at hv; omega
  · rw [outPos_val_of_not_lt a b k h1, outPos_val_of_not_lt a b k' h2] at hv; omega

lemma midIdx_ne_outIdx (a b : ℕ) {n : ℕ} (j : Fin n) (k : Fin (a + b)) :
    midIdx a b j ≠ outIdx a b k := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt; have hk := k.isLt
  rw [midIdx_val] at hv
  by_cases h1 : (k : ℕ) < a
  · rw [outIdx_val_of_lt a b k h1] at hv; omega
  · rw [outIdx_val_of_not_lt a b k h1] at hv; omega

lemma outPos_ne_slotPos (a b : ℕ) (k : Fin (a + b)) : outPos a b k ≠ slotPos a b := by
  intro h
  have hv := congrArg Fin.val h
  have hk := k.isLt
  rw [slotPos_val] at hv
  by_cases h1 : (k : ℕ) < a
  · rw [outPos_val_of_lt a b k h1] at hv; omega
  · rw [outPos_val_of_not_lt a b k h1] at hv; omega

/-- Every input position is either consumed by the inserted operation or survives. -/
lemma idxCases (a b : ℕ) {n : ℕ} (i : Fin (a + n + b)) :
    (∃ j, i = midIdx a b j) ∨ ∃ k, i = outIdx a b k := by
  have hi := i.isLt
  by_cases h1 : (i : ℕ) < a
  · refine Or.inr ⟨⟨i, by omega⟩, Fin.ext ?_⟩
    rw [outIdx_val_of_lt a b _ (by exact h1)]
  · by_cases h2 : (i : ℕ) < a + n
    · refine Or.inl ⟨⟨(i : ℕ) - a, by omega⟩, Fin.ext ?_⟩
      rw [midIdx_val]
      show (i : ℕ) = a + ((i : ℕ) - a)
      omega
    · refine Or.inr ⟨⟨(i : ℕ) - n, by omega⟩, Fin.ext ?_⟩
      rw [outIdx_val_of_not_lt a b _ (by show ¬ ((i : ℕ) - n) < a; omega)]
      show (i : ℕ) = ((i : ℕ) - n) + n
      omega

/-- Every outer position is either the slot or a surviving input. -/
lemma posCases (a b : ℕ) (i : Fin (a + 1 + b)) :
    i = slotPos a b ∨ ∃ k, i = outPos a b k := by
  have hi := i.isLt
  by_cases h1 : (i : ℕ) < a
  · refine Or.inr ⟨⟨i, by omega⟩, Fin.ext ?_⟩
    rw [outPos_val_of_lt a b _ (by exact h1)]
  · by_cases h2 : (i : ℕ) = a
    · exact Or.inl (Fin.ext (by rw [slotPos_val]; exact h2))
    · refine Or.inr ⟨⟨(i : ℕ) - 1, by omega⟩, Fin.ext ?_⟩
      rw [outPos_val_of_not_lt a b _ (by show ¬ ((i : ℕ) - 1) < a; omega)]
      show (i : ℕ) = ((i : ℕ) - 1) + 1
      omega

end Indices

/-! ### The two tuple operations -/

section Tuples

-- Pure tuple manipulation: no module structure is needed here.
variable {V : Type v}

/-- The `n` inputs consumed by the inserted operation. -/
def midTuple (a b : ℕ) {n : ℕ} (v : Fin (a + n + b) → V) (j : Fin n) : V :=
  v (midIdx a b j)

/-- The `(a + 1 + b)`-tuple fed to the outer operation: the surviving inputs of `v`, with `x`
placed in the distinguished slot. -/
def insTuple (a b : ℕ) {n : ℕ} (x : V) (v : Fin (a + n + b) → V) (i : Fin (a + 1 + b)) : V :=
  if h : (i : ℕ) < a then v ⟨i, by have := i.isLt; omega⟩
  else if h' : (i : ℕ) = a then x
  else v ⟨(i : ℕ) + n - 1, by have := i.isLt; omega⟩

@[simp] lemma midTuple_apply (a b : ℕ) {n : ℕ} (v : Fin (a + n + b) → V) (j : Fin n) :
    midTuple a b v j = v (midIdx a b j) := rfl

lemma insTuple_of_lt (a b : ℕ) {n : ℕ} (x : V) (v : Fin (a + n + b) → V)
    (i : Fin (a + 1 + b)) (h : (i : ℕ) < a) :
    insTuple a b x v i = v ⟨i, by have := i.isLt; omega⟩ := by
  unfold insTuple; rw [dif_pos h]

lemma insTuple_of_eq (a b : ℕ) {n : ℕ} (x : V) (v : Fin (a + n + b) → V)
    (i : Fin (a + 1 + b)) (h : (i : ℕ) = a) :
    insTuple a b x v i = x := by
  unfold insTuple; rw [dif_neg (by omega), dif_pos h]

lemma insTuple_of_gt (a b : ℕ) {n : ℕ} (x : V) (v : Fin (a + n + b) → V)
    (i : Fin (a + 1 + b)) (h : a < (i : ℕ)) :
    insTuple a b x v i = v ⟨(i : ℕ) + n - 1, by have := i.isLt; omega⟩ := by
  unfold insTuple; rw [dif_neg (by omega), dif_neg (by omega)]

@[simp] lemma insTuple_slotPos (a b : ℕ) {n : ℕ} (x : V) (v : Fin (a + n + b) → V) :
    insTuple a b x v (slotPos a b) = x :=
  insTuple_of_eq a b x v _ (slotPos_val a b)

@[simp] lemma insTuple_outPos (a b : ℕ) {n : ℕ} (x : V) (v : Fin (a + n + b) → V)
    (k : Fin (a + b)) :
    insTuple a b x v (outPos a b k) = v (outIdx a b k) := by
  have hk := k.isLt
  by_cases h : (k : ℕ) < a
  · rw [insTuple_of_lt a b x v _ (by rw [outPos_val_of_lt a b k h]; exact h)]
    congr 1
    refine Fin.ext ?_
    rw [outIdx_val_of_lt a b k h]
    exact outPos_val_of_lt a b k h
  · rw [insTuple_of_gt a b x v _ (by rw [outPos_val_of_not_lt a b k h]; omega)]
    congr 1
    refine Fin.ext ?_
    -- Stated via `show` + `omega`: rewriting `outPos a b k` directly fails, because it occurs
    -- inside the bound proof of the `Fin.mk`, making the rewrite motive ill-typed.
    have h1 : ((outPos a b k : Fin (a + 1 + b)) : ℕ) = (k : ℕ) + 1 :=
      outPos_val_of_not_lt a b k h
    have h2 : ((outIdx (n := n) a b k : Fin (a + n + b)) : ℕ) = (k : ℕ) + n :=
      outIdx_val_of_not_lt a b k h
    show ((outPos a b k : Fin (a + 1 + b)) : ℕ) + n - 1
        = ((outIdx (n := n) a b k : Fin (a + n + b)) : ℕ)
    omega

/-! ### How the tuple operations interact with `Function.update` -/

lemma midTuple_update_outIdx (a b : ℕ) {n : ℕ} [DecidableEq (Fin (a + n + b))]
    (v : Fin (a + n + b) → V) (k : Fin (a + b)) (z : V) : midTuple a b (Function.update v (outIdx a b k) z) = midTuple a b v := by
  funext j
  rw [midTuple_apply, midTuple_apply, Function.update_apply,
    if_neg (midIdx_ne_outIdx a b j k)]

lemma midTuple_update_midIdx (a b : ℕ) {n : ℕ} [DecidableEq (Fin (a + n + b))]
    [DecidableEq (Fin n)] (v : Fin (a + n + b) → V) (j : Fin n) (z : V) :
    midTuple a b (Function.update v (midIdx a b j) z)
      = Function.update (midTuple a b v) j z := by
  funext j'
  rw [midTuple_apply, Function.update_apply, Function.update_apply]
  by_cases h : j' = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hh => h (midIdx_injective a b hh)), midTuple_apply]

lemma insTuple_update_midIdx (a b : ℕ) {n : ℕ} [DecidableEq (Fin (a + n + b))]
    (x : V) (v : Fin (a + n + b) → V) (j : Fin n) (z : V) : insTuple a b x (Function.update v (midIdx a b j) z) = insTuple a b x v := by
  funext i
  rcases posCases a b i with rfl | ⟨k, rfl⟩
  · rw [insTuple_slotPos, insTuple_slotPos]
  · rw [insTuple_outPos, insTuple_outPos, Function.update_apply,
      if_neg (fun hh => midIdx_ne_outIdx a b j k hh.symm)]

lemma insTuple_update_outIdx (a b : ℕ) {n : ℕ} [DecidableEq (Fin (a + n + b))]
    [DecidableEq (Fin (a + 1 + b))] (x : V) (v : Fin (a + n + b) → V)
    (k : Fin (a + b)) (z : V) :
    insTuple a b x (Function.update v (outIdx a b k) z)
      = Function.update (insTuple a b x v) (outPos a b k) z := by
  funext i
  rcases posCases a b i with rfl | ⟨k', rfl⟩
  · rw [insTuple_slotPos, Function.update_apply,
      if_neg (fun hh => outPos_ne_slotPos a b k hh.symm), insTuple_slotPos]
  · rw [insTuple_outPos, Function.update_apply, Function.update_apply]
    by_cases h : k' = k
    · rw [if_pos (by rw [h]), if_pos (by rw [h])]
    · rw [if_neg (fun hh => h (outIdx_injective a b hh)),
        if_neg (fun hh => h (outPos_injective a b hh)), insTuple_outPos]

/-- `insTuple` depends on its slot argument only through the slot position. -/
lemma insTuple_eq_update (a b : ℕ) {n : ℕ} [DecidableEq (Fin (a + 1 + b))]
    (x y : V) (v : Fin (a + n + b) → V) :
    insTuple a b y v = Function.update (insTuple a b x v) (slotPos a b) y := by
  funext i
  rcases posCases a b i with rfl | ⟨k, rfl⟩
  · rw [insTuple_slotPos, Function.update_apply, if_pos rfl]
  · rw [insTuple_outPos, Function.update_apply,
      if_neg (outPos_ne_slotPos a b k), insTuple_outPos]

end Tuples

/-! ### The composition, as a multilinear map -/

section Comp

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-- Additivity of the outer operation in the distinguished slot. -/
lemma slot_add (a b : ℕ) {n : ℕ} [DecidableEq (Fin (a + 1 + b))]
    (α : End R V (a + 1 + b)) (x y : V) (v : Fin (a + n + b) → V) :
    α (insTuple a b (x + y) v) = α (insTuple a b x v) + α (insTuple a b y v) := by
  have e1 : insTuple a b (x + y) v
      = Function.update (insTuple a b x v) (slotPos a b) (x + y) := insTuple_eq_update a b x _ v
  have e2 : insTuple a b y v
      = Function.update (insTuple a b x v) (slotPos a b) y := insTuple_eq_update a b x y v
  have e3 : Function.update (insTuple a b x v) (slotPos a b) x = insTuple a b x v := by
    conv_rhs => rw [← Function.update_eq_self (slotPos a b) (insTuple a b x v)]
    rw [insTuple_slotPos]
  rw [e1, e2, α.map_update_add, e3]

/-- Homogeneity of the outer operation in the distinguished slot. -/
lemma slot_smul (a b : ℕ) {n : ℕ} [DecidableEq (Fin (a + 1 + b))]
    (α : End R V (a + 1 + b)) (c : R) (x : V) (v : Fin (a + n + b) → V) :
    α (insTuple a b (c • x) v) = c • α (insTuple a b x v) := by
  have e1 : insTuple a b (c • x) v
      = Function.update (insTuple a b x v) (slotPos a b) (c • x) := insTuple_eq_update a b x _ v
  have e3 : Function.update (insTuple a b x v) (slotPos a b) x = insTuple a b x v := by
    conv_rhs => rw [← Function.update_eq_self (slotPos a b) (insTuple a b x v)]
    rw [insTuple_slotPos]
  rw [e1, α.map_update_smul, e3]

/-- Partial composition of multilinear operations. Multilinearity in the `a + n + b` inputs
splits into exactly two cases: the input is consumed by `β`, or it survives into `α`. -/
def compMap (a b : ℕ) {n : ℕ} (α : End R V (a + 1 + b)) (β : End R V n) :
    End R V (a + n + b) where
  toFun v := α (insTuple a b (β (midTuple a b v)) v)
  map_update_add' := by
    intro inst v i p q
    rcases idxCases a b i with ⟨j, rfl⟩ | ⟨k, rfl⟩
    · rw [midTuple_update_midIdx, midTuple_update_midIdx, midTuple_update_midIdx,
        insTuple_update_midIdx, insTuple_update_midIdx, insTuple_update_midIdx,
        β.map_update_add, slot_add]
    · rw [midTuple_update_outIdx, midTuple_update_outIdx, midTuple_update_outIdx,
        insTuple_update_outIdx, insTuple_update_outIdx, insTuple_update_outIdx,
        α.map_update_add]
  map_update_smul' := by
    intro inst v i c p
    rcases idxCases a b i with ⟨j, rfl⟩ | ⟨k, rfl⟩
    · rw [midTuple_update_midIdx, midTuple_update_midIdx,
        insTuple_update_midIdx, insTuple_update_midIdx,
        β.map_update_smul, slot_smul]
    · rw [midTuple_update_outIdx, midTuple_update_outIdx,
        insTuple_update_outIdx, insTuple_update_outIdx,
        α.map_update_smul]

@[simp] lemma compMap_apply (a b : ℕ) {n : ℕ} (α : End R V (a + 1 + b)) (β : End R V n)
    (v : Fin (a + n + b) → V) :
    compMap a b α β v = α (insTuple a b (β (midTuple a b v)) v) := rfl

/-- The identity operation: the unary multilinear map `v ↦ v 0`. -/
def idEnd : End R V 1 where
  toFun v := v 0
  map_update_add' := by intro _ v i x y; fin_cases i; simp
  map_update_smul' := by intro _ v i c x; fin_cases i; simp

@[simp] lemma idEnd_apply (v : Fin 1 → V) : (idEnd (R := R) (V := V)) v = v 0 := rfl

/-- Partial composition, bundled as a bilinear map. Linearity in the inserted operation is
exactly `slot_add`/`slot_smul`. -/
def compL (a b : ℕ) {n : ℕ} :
    End R V (a + 1 + b) →ₗ[R] End R V n →ₗ[R] End R V (a + n + b) where
  toFun α :=
    { toFun := compMap a b α
      map_add' := fun β β' => by
        refine MultilinearMap.ext fun v => ?_
        show α (insTuple a b ((β + β') (midTuple a b v)) v)
            = α (insTuple a b (β (midTuple a b v)) v)
              + α (insTuple a b (β' (midTuple a b v)) v)
        rw [MultilinearMap.add_apply, slot_add]
      map_smul' := fun c β => by
        refine MultilinearMap.ext fun v => ?_
        show α (insTuple a b ((c • β) (midTuple a b v)) v)
            = c • α (insTuple a b (β (midTuple a b v)) v)
        rw [MultilinearMap.smul_apply, slot_smul] }
  map_add' _ _ := by refine LinearMap.ext fun β => MultilinearMap.ext fun v => ?_; rfl
  map_smul' _ _ := by refine LinearMap.ext fun β => MultilinearMap.ext fun v => ?_; rfl

@[simp] lemma compL_apply (a b : ℕ) {n : ℕ} (α : End R V (a + 1 + b)) (β : End R V n)
    (v : Fin (a + n + b) → V) :
    compL a b α β v = α (insTuple a b (β (midTuple a b v)) v) := rfl

/-- How the arity transport of `Operad.reindex` acts on an endomorphism operation: it
reindexes the input tuple along `Fin.cast`. -/
lemma reindex_apply {m m' : ℕ} (h : m = m') (x : End R V m) (v : Fin m' → V) :
    reindex R (End R V) h x v = x (fun i => v (Fin.cast h i)) := by
  subst h; rfl

/-! ### The unit laws -/

/-- With `n = 1` the surviving-input maps for the two arities coincide. -/
lemma outIdx_one_eq_outPos (a b : ℕ) (k : Fin (a + b)) :
    outIdx (n := 1) a b k = outPos a b k := by
  refine Fin.ext ?_
  by_cases h : (k : ℕ) < a
  · rw [outIdx_val_of_lt a b k h, outPos_val_of_lt a b k h]
  · rw [outIdx_val_of_not_lt a b k h, outPos_val_of_not_lt a b k h]

lemma midIdx_one (a b : ℕ) : midIdx (n := 1) a b 0 = slotPos a b := by
  refine Fin.ext ?_
  rw [midIdx_val, slotPos_val]
  simp

lemma comp_one_right' (a b : ℕ) (α : End R V (a + 1 + b)) :
    compMap a b α (idEnd (R := R) (V := V)) = α := by
  refine MultilinearMap.ext fun v => ?_
  rw [compMap_apply]
  congr 1
  funext i
  rcases posCases a b i with rfl | ⟨k, rfl⟩
  · rw [insTuple_slotPos, idEnd_apply, midTuple_apply, midIdx_one]
  · rw [insTuple_outPos, outIdx_one_eq_outPos]

lemma comp_one_left' {n : ℕ} (α : End R V n) :
    reindex R (End R V) (by omega) (compMap 0 0 (idEnd (R := R) (V := V)) α) = α := by
  refine MultilinearMap.ext fun v => ?_
  rw [reindex_apply, compMap_apply, idEnd_apply,
    insTuple_of_eq 0 0 _ _ _ (by simp)]
  congr 1
  funext j
  rw [midTuple_apply]
  congr 1
  refine Fin.ext ?_
  simp

/-! ### Sequential associativity

Every case bottoms out at `v ⟨X, _⟩ = v ⟨Y, _⟩` with `X = Y` by `omega`; the only structural
step is at the slot itself, where the two `β`-arguments must be shown equal. -/

lemma comp_assoc_seq' (a b c d : ℕ) {p : ℕ} (α : End R V (a + 1 + b)) (β : End R V (c + 1 + d))
    (γ : End R V p) :
    reindex R (End R V) (by omega)
        (compMap (a + c) (d + b) (reindex R (End R V) (by omega) (compMap a b α β)) γ)
      = compMap a b α (compMap c d β γ) := by
  refine MultilinearMap.ext fun v => ?_
  simp only [reindex_apply, compMap_apply]
  congr 1
  funext i
  rcases lt_trichotomy (i : ℕ) a with hi | hi | hi
  · -- an input before the slot: both sides read the same entry of `v`
    rw [insTuple_of_lt a b _ _ i hi, insTuple_of_lt a b _ _ i hi,
      insTuple_of_lt (a + c) (d + b) _ _ _ (by simp; omega)]
    congr 1
  · -- the slot: the two `β`-arguments agree
    rw [insTuple_of_eq a b _ _ i hi, insTuple_of_eq a b _ _ i hi]
    congr 1
    funext j
    rw [midTuple_apply]
    rcases lt_trichotomy (j : ℕ) c with hj | hj | hj
    · rw [insTuple_of_lt c d _ _ j hj,
        insTuple_of_lt (a + c) (d + b) _ _ _ (by simp; omega), midTuple_apply]
      congr 1
    · rw [insTuple_of_eq c d _ _ j hj,
        insTuple_of_eq (a + c) (d + b) _ _ _ (by simp; omega)]
      congr 1
      funext j'
      rw [midTuple_apply, midTuple_apply, midTuple_apply]
      congr 1
      exact Fin.ext (by simp; omega)
    · rw [insTuple_of_gt c d _ _ j hj,
        insTuple_of_gt (a + c) (d + b) _ _ _ (by simp; omega), midTuple_apply]
      congr 1
      exact Fin.ext (by simp; omega)
  · -- an input after the slot
    rw [insTuple_of_gt a b _ _ i hi, insTuple_of_gt a b _ _ i hi,
      insTuple_of_gt (a + c) (d + b) _ _ _ (by simp; omega)]
    congr 1
    exact Fin.ext (by simp; omega)

/-! ### Parallel associativity

Five cases: before the first slot, the first slot (`β`), between the slots, the second slot
(`γ`), and after both. -/

lemma comp_assoc_par' (a b c : ℕ) {n p : ℕ} (α : End R V (a + 1 + b + 1 + c)) (β : End R V n)
    (γ : End R V p) :
    reindex R (End R V) (by omega)
        (compMap (a + n + b) c
          (reindex R (End R V) (by omega)
            (compMap a (b + 1 + c) (reindex R (End R V) (by omega) α) β)) γ)
      = compMap a (b + p + c) (reindex R (End R V) (by omega) (compMap (a + 1 + b) c α γ)) β := by
  refine MultilinearMap.ext fun v => ?_
  simp only [reindex_apply, compMap_apply]
  congr 1
  funext i
  rcases lt_trichotomy (i : ℕ) a with hi | hi | hi
  · -- before the first slot
    rw [insTuple_of_lt a (b + 1 + c) _ _ _ (by simp; omega),
      insTuple_of_lt (a + 1 + b) c _ _ i (by omega),
      insTuple_of_lt (a + n + b) c _ _ _ (by simp; omega),
      insTuple_of_lt a (b + p + c) _ _ _ (by simp; omega)]
    exact congrArg _ (Fin.ext (by simp))
  · -- the first slot: the two `β`-arguments agree
    rw [insTuple_of_eq a (b + 1 + c) _ _ _ (by simp; omega),
      insTuple_of_lt (a + 1 + b) c _ _ i (by omega),
      insTuple_of_eq a (b + p + c) _ _ _ (by simp; omega)]
    refine congrArg _ (funext fun j => ?_)
    rw [midTuple_apply, midTuple_apply,
      insTuple_of_lt (a + n + b) c _ _ _ (by simp; omega)]
    exact congrArg _ (Fin.ext (by simp))
  · rcases lt_trichotomy (i : ℕ) (a + 1 + b) with hi2 | hi2 | hi2
    · -- between the two slots
      rw [insTuple_of_gt a (b + 1 + c) _ _ _ (by simp; omega),
        insTuple_of_lt (a + 1 + b) c _ _ i hi2,
        insTuple_of_lt (a + n + b) c _ _ _ (by simp; omega),
        insTuple_of_gt a (b + p + c) _ _ _ (by simp; omega)]
      exact congrArg _ (Fin.ext (by simp))
    · -- the second slot: the two `γ`-arguments agree
      rw [insTuple_of_gt a (b + 1 + c) _ _ _ (by simp; omega),
        insTuple_of_eq (a + 1 + b) c _ _ i hi2,
        insTuple_of_eq (a + n + b) c _ _ _ (by simp; omega)]
      refine congrArg _ (funext fun j => ?_)
      rw [midTuple_apply, midTuple_apply,
        insTuple_of_gt a (b + p + c) _ _ _ (by simp; omega)]
      exact congrArg _ (Fin.ext (by simp; omega))
    · -- after both slots
      rw [insTuple_of_gt a (b + 1 + c) _ _ _ (by simp; omega),
        insTuple_of_gt (a + 1 + b) c _ _ i hi2,
        insTuple_of_gt (a + n + b) c _ _ _ (by simp; omega),
        insTuple_of_gt a (b + p + c) _ _ _ (by simp; omega)]
      exact congrArg _ (Fin.ext (by simp; omega))

/-- **The endomorphism operad.** All four operad axioms hold for the multilinear operations
on any module. -/
instance endOperad : NSOperad R (End R V) where
  one := idEnd
  comp := compL
  comp_one_right := by intros; apply comp_one_right'
  comp_one_left := by intros; apply comp_one_left'
  comp_assoc_seq := by intros; apply comp_assoc_seq'
  comp_assoc_par := by intros; apply comp_assoc_par'

/-- Operadic composition in `End` is literally "plug `β` into the distinguished slot". This is
the bridge that lets abstract operad identities be evaluated on tuples. -/
@[simp] lemma operad_comp_apply (a b : ℕ) {n : ℕ} (α : End R V (a + 1 + b)) (β : End R V n)
    (v : Fin (a + n + b) → V) :
    NSOperad.comp (R := R) a b α β v = α (insTuple a b (β (midTuple a b v)) v) := rfl

end Comp

end End

end Operad
