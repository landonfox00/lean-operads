/-
# Inversions of a list of natural numbers

The number of inversions of a list (`ListInv.inv`) and its sign (`ListInv.sgn`, in `ℤ`): moving an
entry `x` from behind a list `l₁` to the front multiplies the sign by `(-1)^|l₁|` when `x` does not
occur in `l₁` (`ListInv.sgn_move`), and exchanging the positions of two distinct values changes the
sign (`ListInv.sgn_swap`). These are the parity arguments behind the signs of the bar construction.
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring

namespace Operad

namespace ListInv

/-- **The number of inversions** of a list: the pairs of entries in decreasing order. -/
def inv : List ℕ → ℕ
  | [] => 0
  | a :: l => l.countP (· < a) + inv l

/-- The pairs of an entry of `l₁` and a smaller entry of `l₂`. -/
def cross (l₁ l₂ : List ℕ) : ℕ := (l₁.map fun a => l₂.countP (· < a)).sum

/-- **The sign** of a list, `(-1)` to its number of inversions. -/
def sgn (l : List ℕ) : ℤ := (-1) ^ inv l

@[simp] lemma inv_nil : inv [] = 0 := rfl

@[simp] lemma inv_cons (a : ℕ) (l : List ℕ) : inv (a :: l) = l.countP (· < a) + inv l := rfl

@[simp] lemma cross_nil_left (l : List ℕ) : cross [] l = 0 := rfl

@[simp] lemma cross_cons_left (a : ℕ) (l₁ l₂ : List ℕ) :
    cross (a :: l₁) l₂ = l₂.countP (· < a) + cross l₁ l₂ := by
  simp [cross]

lemma inv_append : ∀ l₁ l₂ : List ℕ, inv (l₁ ++ l₂) = inv l₁ + inv l₂ + cross l₁ l₂
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp only [List.cons_append, inv_cons, List.countP_append, inv_append l₁ l₂, cross_cons_left]
    ring

lemma cross_perm_right (l₁ : List ℕ) {l₂ l₂' : List ℕ} (h : l₂.Perm l₂') :
    cross l₁ l₂ = cross l₁ l₂' := by
  simp only [cross, h.countP_eq]

lemma cross_cons_right (l₁ : List ℕ) (x : ℕ) (l₂ : List ℕ) :
    cross l₁ (x :: l₂) = l₁.countP (x < ·) + cross l₁ l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    simp only [cross_cons_left, List.countP_cons, ih]
    by_cases h : x < a <;> simp [h] <;> ring

lemma countP_lt_add_countP_gt {x : ℕ} : ∀ {l : List ℕ}, x ∉ l →
    l.countP (· < x) + l.countP (x < ·) = l.length
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mem_cons, not_or] at h
    have ih := countP_lt_add_countP_gt h.2
    simp only [List.countP_cons, List.length_cons]
    rcases lt_or_gt_of_ne (Ne.symm h.1) with hax | hax
    · simp [hax, not_lt_of_gt hax]
      omega
    · simp [hax, not_lt_of_gt hax]
      omega

/-- **Moving an entry to the front**, past `l₁`, in which it does not occur. -/
lemma inv_move {x : ℕ} {l₁ : List ℕ} (hx : x ∉ l₁) (l₂ : List ℕ) :
    inv (l₁ ++ x :: l₂) + 2 * l₁.countP (· < x) = inv (x :: (l₁ ++ l₂)) + l₁.length := by
  rw [inv_append, inv_cons, cross_cons_right, inv_cons, List.countP_append, inv_append,
    ← countP_lt_add_countP_gt hx]
  ring

lemma neg_one_pow_eq_of_add {a b c d : ℕ} (h : a + 2 * c = b + d) :
    (-1 : ℤ) ^ a = (-1) ^ d * (-1) ^ b := by
  rw [← pow_add, add_comm d b, ← h, pow_add, pow_mul]
  simp

lemma sgn_move {x : ℕ} {l₁ : List ℕ} (hx : x ∉ l₁) (l₂ : List ℕ) :
    sgn (l₁ ++ x :: l₂) = (-1) ^ l₁.length * sgn (x :: (l₁ ++ l₂)) :=
  neg_one_pow_eq_of_add (inv_move hx l₂)

lemma sgn_mul_self (l : List ℕ) : sgn l * sgn l = 1 := by
  rw [sgn, ← pow_add, ← two_mul, pow_mul]
  norm_num

lemma sgn_cons (a : ℕ) (l : List ℕ) : sgn (a :: l) = (-1) ^ l.countP (· < a) * sgn l := by
  rw [sgn, inv_cons, pow_add, sgn]

lemma sgn_cons_perm (a : ℕ) {l l' : List ℕ} (h : l.Perm l') (hs : sgn l = sgn l') :
    sgn (a :: l) = sgn (a :: l') := by
  rw [sgn_cons, sgn_cons, h.countP_eq, hs]

/-- **Exchanging two distinct values** changes the sign: `β` and `γ` at the front of `l₂` and of
`l₃`, neither occurring elsewhere. -/
lemma sgn_swap {β γ : ℕ} (hβγ : β ≠ γ) {l₂ l₃ : List ℕ} (hγ : γ ∉ l₂) (hβ : β ∉ l₂) :
    sgn (β :: (l₂ ++ γ :: l₃)) = -sgn (γ :: (l₂ ++ β :: l₃)) := by
  rw [sgn_cons, sgn_cons, sgn_move hγ, sgn_move hβ, sgn_cons, sgn_cons]
  have h1 : (l₂ ++ γ :: l₃).countP (· < β) = (γ :: (l₂ ++ l₃)).countP (· < β) :=
    List.Perm.countP_eq _ List.perm_middle
  have h2 : (l₂ ++ β :: l₃).countP (· < γ) = (β :: (l₂ ++ l₃)).countP (· < γ) :=
    List.Perm.countP_eq _ List.perm_middle
  rw [h1, h2, List.countP_cons, List.countP_cons]
  rcases lt_or_gt_of_ne hβγ with h | h
  · simp only [h, not_lt_of_gt h, decide_true, decide_false, if_true, Bool.false_eq_true,
      if_false, add_zero, pow_add, pow_one]
    ring
  · simp only [h, not_lt_of_gt h, decide_true, decide_false, if_true, Bool.false_eq_true,
      if_false, add_zero, pow_add, pow_one]
    ring

end ListInv

end Operad
