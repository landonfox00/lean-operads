/-
# Koszul signs of unshuffles of finite sets

For parities `p : α → Bool` on a linear order `α`, the Koszul sign of moving a finite set `A` of
inputs in front of a finite set `B` is one sign `σ(p i p j)` for each `i ∈ A` and smaller
`j ∈ B` (`KS.ks`); `KS.par A` is the parity of `A`. The unshuffle sign of `LInf.usgn` is
`KS.ks p S Sᶜ`.

* Signs are multiplicative in each set (`KS.ks_union_left`, `KS.ks_union_right`), and moving `A`
  in front of `B` and back costs the product of their parities (`KS.ks_mul_ks`).
* Signs are invariant under order embeddings (`KS.ks_map`, `KS.par_map`).
-/
import Operad.LInfinity

universe u

namespace Operad

namespace KS

open GerBV

variable {R : Type u} [CommRing R] {α : Type*} [LinearOrder α] (p : α → Bool)

/-- **The parity of a set of inputs**, the parity of the number of its odd inputs. -/
def par (A : Finset α) : Bool := Nat.bodd (A.filter fun i => p i = true).card

variable (R) in
/-- **The Koszul sign of moving `A` in front of `B`**: one sign for each pair of an element of
`A` and a smaller element of `B`. -/
def ks (A B : Finset α) : R := ∏ i ∈ A, ∏ j ∈ B.filter (· < i), σ R (p i && p j)

/-! ## Parities -/

omit [LinearOrder α] in
@[simp] lemma par_empty : par p (∅ : Finset α) = false := by
  simp [par]

lemma par_insert {a : α} {A : Finset α} (ha : a ∉ A) :
    par p (insert a A) = xor (p a) (par p A) := by
  unfold par
  rw [Finset.filter_insert]
  by_cases hpa : p a = true
  · rw [if_pos hpa, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.1 h).1),
      Nat.bodd_succ, hpa]
    simp
  · rw [if_neg hpa]
    simp only [Bool.not_eq_true] at hpa
    rw [hpa, Bool.false_xor]

lemma σ_par (A : Finset α) : σ R (par p A) = ∏ i ∈ A, σ R (p i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [par_insert p ha, Finset.prod_insert ha, ← ih, LInf.σ_mul]

lemma par_union {A B : Finset α} (h : Disjoint A B) : par p (A ∪ B) = xor (par p A) (par p B) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    have haB : a ∉ B := Finset.disjoint_left.1 h (Finset.mem_insert_self a A)
    have hAB : Disjoint A B := Finset.disjoint_of_subset_left (Finset.subset_insert a A) h
    rw [Finset.insert_union, par_insert p (fun h' => (Finset.mem_union.1 h').elim ha haB),
      ih hAB, par_insert p ha, Bool.xor_assoc]

lemma σ_and_xor (a b c : Bool) : σ R (a && xor b c) = σ R (a && b) * σ R (a && c) := by
  cases a <;> cases b <;> cases c <;> simp [σ]

lemma σ_xor_and (a b c : Bool) : σ R (xor a b && c) = σ R (a && c) * σ R (b && c) := by
  cases a <;> cases b <;> cases c <;> simp [σ]

lemma σ_and_par (a : Bool) (A : Finset α) : σ R (a && par p A) = ∏ i ∈ A, σ R (a && p i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [σ]
  | insert b A hb ih => rw [par_insert p hb, Finset.prod_insert hb, ← ih, σ_and_xor]

lemma σ_par_and (a : Bool) (A : Finset α) : σ R (par p A && a) = ∏ i ∈ A, σ R (p i && a) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [σ]
  | insert b A hb ih => rw [par_insert p hb, Finset.prod_insert hb, ← ih, σ_xor_and]

lemma σ_par_and_par (A B : Finset α) :
    σ R (par p A && par p B) = ∏ i ∈ A, ∏ j ∈ B, σ R (p i && p j) := by
  rw [σ_par_and]
  exact Finset.prod_congr rfl fun i _ => σ_and_par p _ B

/-! ## Signs of unshuffles -/

@[simp] lemma ks_empty_left (B : Finset α) : ks R p ∅ B = 1 := by
  simp [ks]

@[simp] lemma ks_empty_right (A : Finset α) : ks R p A ∅ = 1 := by
  simp [ks]

lemma ks_union_left {A A' : Finset α} (B : Finset α) (h : Disjoint A A') :
    ks R p (A ∪ A') B = ks R p A B * ks R p A' B := by
  unfold ks
  rw [Finset.prod_union h]

lemma ks_union_right (A : Finset α) {B B' : Finset α} (h : Disjoint B B') :
    ks R p A (B ∪ B') = ks R p A B * ks R p A B' := by
  unfold ks
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.filter_union, Finset.prod_union (Finset.disjoint_filter_filter h)]

lemma ks_singleton_left (a : α) (B : Finset α) :
    ks R p {a} B = ∏ j ∈ B.filter (· < a), σ R (p a && p j) := by
  simp [ks]

lemma ks_singleton_right (A : Finset α) (b : α) :
    ks R p A {b} = ∏ i ∈ A.filter (b < ·), σ R (p i && p b) := by
  unfold ks
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hb : b < i
  · rw [if_pos hb, Finset.filter_singleton, if_pos hb, Finset.prod_singleton]
  · rw [if_neg hb, Finset.filter_singleton, if_neg hb, Finset.prod_empty]

/-- **Moving `A` in front of `B` and back costs the product of their parities.** -/
lemma ks_mul_ks {A B : Finset α} (h : Disjoint A B) :
    ks R p A B * ks R p B A = σ R (par p A && par p B) := by
  rw [σ_par_and_par]
  unfold ks
  simp_rw [Finset.prod_filter]
  rw [Finset.prod_comm (s := B) (t := A), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hij : i ≠ j := fun e => Finset.disjoint_left.1 h hi (e ▸ hj)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · rw [if_neg (not_lt.2 hlt.le), if_pos hlt, one_mul, Bool.and_comm]
  · rw [if_pos hlt, if_neg (not_lt.2 hlt.le), mul_one]

lemma ks_mul_self (A B : Finset α) : ks R p A B * ks R p A B = 1 := by
  unfold ks
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun j _ => LInf.σ_mul_self _

/-! ## Relabelling -/

/-- Signs are invariant under order embeddings. -/
lemma ks_map {β : Type*} [LinearOrder β] (ι : α ↪o β) (q : β → Bool) (A B : Finset α) :
    ks R (q ∘ ι) A B = ks R q (A.map ι.toEmbedding) (B.map ι.toEmbedding) := by
  unfold ks
  rw [Finset.prod_map]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.filter_map, Finset.prod_map]
  refine Finset.prod_congr ?_ fun j _ => rfl
  ext j
  simp

lemma par_map {β : Type*} [LinearOrder β] (ι : α ↪o β) (q : β → Bool) (A : Finset α) :
    par (q ∘ ι) A = par q (A.map ι.toEmbedding) := by
  unfold par
  rw [Finset.filter_map, Finset.card_map]
  rfl

end KS

end Operad
