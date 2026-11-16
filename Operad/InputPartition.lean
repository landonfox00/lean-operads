/-
# Partitions of a set of inputs as root maps

A partition of a finite set `S` of inputs of a linear order is encoded by its **root map**
(`IPart.IsRoot`): every input of `S` goes to the least input of its block, and the other labels
are fixed. The least inputs are `IPart.fix`, the blocks `IPart.blk`, and over a finite order the
partitions of `S` form a finite set (`IPart.roots`). The Koszul sign of a partition has one
factor for each pair of inputs whose order is reversed when the blocks are listed by their least
inputs (`IPart.sgn`).

* **Coarsening.** A partition `s` of the least inputs of `r` gives the coarser partition `s ∘ r`
  (`IPart.IsRoot.comp`); conversely, a coarser partition `t` restricts to the least inputs of a
  finer one (`IPart.IsRoot.restrictRoot`).
* **The sign of a coarsening** (`IPart.sgn_coarsen`): the sign of `t` and of `r` on the blocks of
  `t` is the sign of `r` and of the induced partition of its least inputs, a count of reversed
  pairs modulo two.
* **Gluing** (`IPart.sum_blockRoots`): choosing a partition and a partition of each of its blocks
  is choosing a partition and a partition of its least inputs.
-/
import Operad.UnshuffleSign
import Mathlib.Data.Fintype.Pi

universe u

namespace Operad

namespace IPart

open GerBV KS

variable {α : Type*} [LinearOrder α]

/-- **A partition of `S` as a root map**: every input of `S` goes to the least input of its
block, and the labels outside `S` are fixed. -/
structure IsRoot (S : Finset α) (r : α → α) : Prop where
  mem : ∀ x ∈ S, r x ∈ S
  off : ∀ x, x ∉ S → r x = x
  idem : ∀ x, r (r x) = r x
  le : ∀ x, r x ≤ x

/-- The least inputs of the blocks. -/
def fix (r : α → α) (S : Finset α) : Finset α := S.filter fun x => r x = x

/-- The block with least input `m`. -/
def blk (r : α → α) (S : Finset α) (m : α) : Finset α := S.filter fun x => r x = m

lemma mem_fix {r : α → α} {S : Finset α} {x : α} : x ∈ fix r S ↔ x ∈ S ∧ r x = x := by
  unfold fix
  rw [Finset.mem_filter]

lemma mem_blk {r : α → α} {S : Finset α} {m x : α} : x ∈ blk r S m ↔ x ∈ S ∧ r x = m := by
  unfold blk
  rw [Finset.mem_filter]

lemma IsRoot.root_mem_fix {S : Finset α} {r : α → α} (hr : IsRoot S r) {x : α} (hx : x ∈ S) :
    r x ∈ fix r S :=
  mem_fix.2 ⟨hr.mem x hx, hr.idem x⟩

lemma mem_blk_self {S : Finset α} {r : α → α} {m : α}
    (hm : m ∈ fix r S) : m ∈ blk r S m :=
  mem_blk.2 (mem_fix.1 hm)

/-- The block of `m` is not empty when `m` is a least input. -/
lemma blk_nonempty {S : Finset α} {r : α → α} {m : α}
    (hm : m ∈ fix r S) : (blk r S m).Nonempty :=
  ⟨m, mem_blk_self hm⟩

/-- **The least input of a block is its minimum.** -/
lemma IsRoot.le_of_mem_blk {S : Finset α} {r : α → α} (hr : IsRoot S r) {m x : α}
    (hx : x ∈ blk r S m) : m ≤ x := by
  obtain ⟨-, rfl⟩ := mem_blk.1 hx
  exact hr.le x

/-- The blocks are disjoint. -/
lemma disjoint_blk (r : α → α) (S : Finset α) {m m' : α} (h : m ≠ m') :
    Disjoint (blk r S m) (blk r S m') :=
  Finset.disjoint_left.2 fun _ hx hx' => h ((mem_blk.1 hx).2.symm.trans (mem_blk.1 hx').2)

/-- The blocks cover `S`. -/
lemma biUnion_blk {S : Finset α} {r : α → α} (hr : IsRoot S r) :
    (fix r S).biUnion (blk r S) = S := by
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨m, -, hx⟩
    exact (mem_blk.1 hx).1
  · intro hx
    exact ⟨r x, hr.root_mem_fix hx, mem_blk.2 ⟨hx, rfl⟩⟩

variable (R : Type u) [CommRing R]

/-- **The Koszul sign of a partition**: one sign for each pair of inputs whose order is reversed
when the blocks are listed by their least inputs. -/
def sgn (p : α → Bool) (r : α → α) (S : Finset α) : R :=
  ∏ x ∈ S, ∏ y ∈ S, if y < x ∧ r x < r y then σ R (p x && p y) else 1

section finite

variable {R}
variable [Fintype α]

open Classical in
/-- **The partitions of `S`**, as root maps. -/
noncomputable def roots (S : Finset α) : Finset (α → α) := Finset.univ.filter (IsRoot S)

lemma mem_roots {S : Finset α} {r : α → α} : r ∈ roots S ↔ IsRoot S r := by
  classical
  unfold roots
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

end finite

/-! ## Coarsening -/

/-- **Coarsening a partition by a partition of its least inputs**. -/
lemma IsRoot.comp {S : Finset α} {r s : α → α} (hr : IsRoot S r) (hs : IsRoot (fix r S) s) :
    IsRoot S (s ∘ r) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_⟩
  · exact (mem_fix.1 (hs.mem _ (hr.root_mem_fix hx))).1
  · simp only [Function.comp_apply]
    rw [hr.off x hx, hs.off x fun h => hx (mem_fix.1 h).1]
  · simp only [Function.comp_apply]
    by_cases hx : r x ∈ fix r S
    · have h1 : s (r x) ∈ fix r S := hs.mem _ hx
      rw [(mem_fix.1 h1).2, hs.idem]
    · rw [hs.off _ hx, hr.idem, hs.off _ hx]
  · exact (hs.le (r x)).trans (hr.le x)

/-- A partition `r` finer than `t`: `t` is constant on the blocks of `r`. -/
def Finer (r t : α → α) : Prop := ∀ x, t (r x) = t x

/-- **The partition of the least inputs of a finer partition** induced by a coarser one. -/
noncomputable def restrictRoot (r t : α → α) (S : Finset α) : α → α := by
  classical
  exact fun x => if x ∈ fix r S then t x else x

lemma IsRoot.restrictRoot {S : Finset α} {r t : α → α} (hr : IsRoot S r) (ht : IsRoot S t)
    (hrt : Finer r t) : IsRoot (fix r S) (IPart.restrictRoot r t S) ∧
      IPart.restrictRoot r t S ∘ r = t := by
  classical
  -- the least input of a coarse block is a least input of the fine partition
  have key : ∀ x ∈ S, r (t x) = t x := by
    intro x hx
    have h1 : t (r (t x)) = t x := by rw [hrt, ht.idem]
    have h2 : r (t x) ≤ t x := hr.le _
    have h3 : t x ≤ r (t x) := by
      have := ht.le (r (t x))
      rwa [h1] at this
    exact le_antisymm h2 h3
  have hfix : ∀ x ∈ S, t x ∈ fix r S := fun x hx => mem_fix.2 ⟨ht.mem x hx, key x hx⟩
  unfold IPart.restrictRoot
  refine ⟨⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_⟩, ?_⟩
  · rw [if_pos hx]
    exact hfix x (mem_fix.1 hx).1
  · rw [if_neg hx]
  · by_cases hx : x ∈ fix r S
    · rw [if_pos hx, if_pos (hfix x (mem_fix.1 hx).1), ht.idem]
    · rw [if_neg hx, if_neg hx]
  · split_ifs
    · exact ht.le x
    · exact le_rfl
  · funext x
    simp only [Function.comp_apply]
    by_cases hx : x ∈ S
    · rw [if_pos (hr.root_mem_fix hx), hrt]
    · have hx' : r x ∉ fix r S := by
        rw [hr.off x hx]
        exact fun h => hx (mem_fix.1 h).1
      rw [if_neg hx', hr.off x hx, ht.off x hx]

lemma restrictRoot_comp {S : Finset α} {r s : α → α} (hs : IsRoot (fix r S) s) :
    IPart.restrictRoot r (s ∘ r) S = s := by
  classical
  funext x
  unfold IPart.restrictRoot
  split_ifs with hx
  · simp only [Function.comp_apply]
    rw [(mem_fix.1 hx).2]
  · exact (hs.off x hx).symm

omit [LinearOrder α] in
lemma finer_comp (r s : α → α) (hr : ∀ x, r (r x) = r x) : Finer r (s ∘ r) := fun x => by
  simp only [Function.comp_apply, hr]

/-! ## The sign of a coarsening -/

section coarsen_sign

variable {R}

omit [LinearOrder α] in
lemma prod_ite_prod {M : Type*} [CommMonoid M] {ι κ : Type*} (c : Prop) [Decidable c]
    (s : Finset ι) (t : Finset κ) (g : ι → κ → M) :
    (if c then ∏ x ∈ s, ∏ y ∈ t, g x y else 1) = ∏ x ∈ s, ∏ y ∈ t, if c then g x y else 1 := by
  by_cases hc : c <;> simp [hc]

/-- **Products over ordered pairs**, as products over the pairs `y < x` of both orders and the
diagonal. -/
lemma prod_pairs {M : Type*} [CommMonoid M] (S : Finset α) (A : α → α → M) :
    ∏ x ∈ S, ∏ y ∈ S, A x y = ∏ x ∈ S, (A x x * ∏ y ∈ S.filter (· < x), (A x y * A y x)) := by
  have h1 : ∀ x ∈ S, ∏ y ∈ S, A x y
      = A x x * ((∏ y ∈ S.filter (· < x), A x y) * ∏ y ∈ S.filter (x < ·), A x y) := by
    intro x hx
    rw [← Finset.prod_filter_mul_prod_filter_not S (· < x)]
    have h2 : S.filter (fun y => ¬ y < x) = insert x (S.filter (x < ·)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_insert, not_lt]
      constructor
      · rintro ⟨hy, hxy⟩
        rcases hxy.lt_or_eq with h | h
        · exact Or.inr ⟨hy, h⟩
        · exact Or.inl h.symm
      · rintro (rfl | ⟨hy, h⟩)
        · exact ⟨hx, le_rfl⟩
        · exact ⟨hy, h.le⟩
    rw [h2, Finset.prod_insert (by simp)]
    exact mul_left_comm _ _ _
  rw [Finset.prod_congr rfl h1]
  simp only [Finset.prod_mul_distrib]
  have h3 : ∏ x ∈ S, ∏ y ∈ S.filter (x < ·), A x y = ∏ x ∈ S, ∏ y ∈ S.filter (· < x), A y x := by
    rw [Finset.prod_comm' (t' := S) (s' := fun y => S.filter (· < y))]
    intro x y
    simp only [Finset.mem_filter]
    tauto
  rw [h3]

/-- The signs of a partition on the blocks of a coarser one, as one product over pairs. -/
lemma prod_sgn_blk {S : Finset α} {t : α → α} (ht : IsRoot S t) (p : α → Bool) (r : α → α) :
    ∏ m ∈ fix t S, sgn R p r (blk t S m)
      = ∏ x ∈ S, ∏ y ∈ S, if t x = t y ∧ (y < x ∧ r x < r y) then σ R (p x && p y) else 1 := by
  classical
  unfold sgn
  have step : ∀ m ∈ fix t S, (∏ x ∈ blk t S m, ∏ y ∈ blk t S m,
      if y < x ∧ r x < r y then σ R (p x && p y) else 1)
      = ∏ x ∈ blk t S m, ∏ y ∈ blk t S (t x),
        if y < x ∧ r x < r y then σ R (p x && p y) else 1 := fun m _ =>
    Finset.prod_congr rfl fun x hx => by rw [(mem_blk.1 hx).2]
  rw [Finset.prod_congr rfl step, ← Finset.prod_biUnion fun m _ m' _ h => disjoint_blk t S h,
    biUnion_blk ht]
  refine Finset.prod_congr rfl fun x _ => ?_
  unfold blk
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun y _ => ?_
  by_cases hy : t y = t x
  · rw [if_pos hy]
    simp only [hy, true_and]
  · rw [if_neg hy, if_neg]
    rintro ⟨h, -⟩
    exact hy h.symm

/-- The sign of the induced partition of the least inputs, as one product over pairs. -/
lemma sgn_restrictRoot {S : Finset α} {r t : α → α} (hr : IsRoot S r) (ht : IsRoot S t)
    (hrt : Finer r t) (p : α → Bool) :
    sgn R (fun m => par p (blk r S m)) (restrictRoot r t S) (fix r S)
      = ∏ x ∈ S, ∏ y ∈ S, if r y < r x ∧ t x < t y then σ R (p x && p y) else 1 := by
  classical
  have hs := (hr.restrictRoot ht hrt).2
  unfold sgn
  simp only [σ_par_and_par, prod_ite_prod]
  have hS : ∀ F : α → R, ∏ x ∈ S, F x = ∏ m ∈ fix r S, ∏ x ∈ blk r S m, F x := fun F => by
    rw [← Finset.prod_biUnion fun m _ m' _ h => disjoint_blk r S h, biUnion_blk hr]
  rw [hS]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun x hx => ?_
  obtain ⟨-, hxm⟩ := mem_blk.1 hx
  rw [hS]
  refine Finset.prod_congr rfl fun m' _ => Finset.prod_congr rfl fun y hy => ?_
  obtain ⟨-, hym⟩ := mem_blk.1 hy
  have e1 : restrictRoot r t S m = t x := by
    rw [← hxm, ← Function.comp_apply (f := restrictRoot r t S), hs]
  have e2 : restrictRoot r t S m' = t y := by
    rw [← hym, ← Function.comp_apply (f := restrictRoot r t S), hs]
  rw [e1, e2, ← hxm, ← hym]

/-- **The sign of a coarsening**: the sign of the coarse partition and of the fine partition on
its blocks is the sign of the fine partition and of the induced partition of its least
inputs. -/
theorem sgn_coarsen {S : Finset α} {r t : α → α} (hr : IsRoot S r) (ht : IsRoot S t)
    (hrt : Finer r t) (p : α → Bool) :
    sgn R p t S * ∏ m ∈ fix t S, sgn R p r (blk t S m)
      = sgn R p r S * sgn R (fun m => par p (blk r S m)) (restrictRoot r t S) (fix r S) := by
  rw [prod_sgn_blk ht, sgn_restrictRoot hr ht hrt]
  unfold sgn
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  conv_lhs => arg 2; ext x; rw [← Finset.prod_mul_distrib]
  conv_rhs => arg 2; ext x; rw [← Finset.prod_mul_distrib]
  rw [prod_pairs, prod_pairs]
  refine Finset.prod_congr rfl fun x _ => ?_
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun y hy => ?_
    have hyx : y < x := (Finset.mem_filter.1 hy).2
    have hxy : ¬ x < y := not_lt.2 hyx.le
    have hsym : σ R (p y && p x) = σ R (p x && p y) := by rw [Bool.and_comm]
    have hσ := LInf.σ_mul_self (R := R) (p x && p y)
    simp only [hyx, hxy, true_and, false_and, and_false, if_false, mul_one, hsym]
    rcases lt_trichotomy (t x) (t y) with h | h | h
    · have hne : r x ≠ r y := fun e => h.ne (by rw [← hrt x, e, hrt y])
      have h' : ¬ t x = t y := h.ne
      have h'' : ¬ t y < t x := not_lt.2 h.le
      simp only [h, h', h'', false_and, and_true, and_false, if_true, if_false, mul_one]
      rcases lt_or_gt_of_ne hne with h3 | h3
      · simp [h3, not_lt.2 h3.le]
      · simp [h3, not_lt.2 h3.le]
    · simp only [h, lt_self_iff_false, true_and, and_false, if_false, mul_one, one_mul]
    · have h' : ¬ t x = t y := h.ne'
      have h'' : ¬ t x < t y := not_lt.2 h.le
      simp only [h, h', h'', false_and, and_true, and_false, if_false, mul_one]
      by_cases h3 : r x < r y
      · simp only [h3, if_true, hσ, one_mul]
      · simp only [h3, if_false, mul_one]

end coarsen_sign

/-! ## Partitions of the blocks of a partition -/

section glue

/-- **Gluing partitions of the blocks** of `t`: the input `x` goes where the partition of its
block sends it. -/
def glue (t : α → α) (ρ : α → α → α) : α → α := fun x => ρ (t x) x

/-- **The restriction of a partition to a block**, the identity outside it. -/
noncomputable def restr (r : α → α) (B : Finset α) : α → α := by
  classical
  exact fun x => if x ∈ B then r x else x

lemma restr_of_mem {r : α → α} {B : Finset α} {x : α} (hx : x ∈ B) : restr r B x = r x := by
  classical
  unfold restr
  rw [if_pos hx]

lemma restr_of_notMem {r : α → α} {B : Finset α} {x : α} (hx : x ∉ B) : restr r B x = x := by
  classical
  unfold restr
  rw [if_neg hx]

variable [Fintype α]

/-- The partitions of the blocks of `t`, the identity on the other labels. -/
noncomputable def blockRoots (S : Finset α) (t : α → α) : α → Finset (α → α) := by
  classical
  exact fun m => if m ∈ fix t S then roots (blk t S m) else {id}

lemma IsRoot.glue {S : Finset α} {t : α → α} (ht : IsRoot S t) {ρ : α → α → α}
    (hρ : ∀ m, ρ m ∈ blockRoots S t m) : IsRoot S (glue t ρ) ∧ Finer (glue t ρ) t := by
  classical
  have hin : ∀ x ∈ S, IsRoot (blk t S (t x)) (ρ (t x)) := fun x hx => by
    have := hρ (t x)
    unfold blockRoots at this
    rw [if_pos (ht.root_mem_fix hx)] at this
    exact mem_roots.1 this
  have hout : ∀ m, m ∉ fix t S → ρ m = id := fun m hm => by
    have := hρ m
    unfold blockRoots at this
    rw [if_neg hm] at this
    exact Finset.mem_singleton.1 this
  have hxb : ∀ x ∈ S, x ∈ blk t S (t x) := fun x hx => mem_blk.2 ⟨hx, rfl⟩
  have hblk : ∀ x ∈ S, ρ (t x) x ∈ blk t S (t x) := fun x hx => (hin x hx).mem x (hxb x hx)
  have hoff : ∀ x, x ∉ S → IPart.glue t ρ x = x := fun x hx => by
    unfold IPart.glue
    rw [ht.off x hx, hout x fun h => hx (mem_fix.1 h).1]
    rfl
  have hfin : ∀ x ∈ S, t (IPart.glue t ρ x) = t x := fun x hx => (mem_blk.1 (hblk x hx)).2
  refine ⟨⟨fun x hx => (mem_blk.1 (hblk x hx)).1, hoff, fun x => ?_, fun x => ?_⟩,
    fun x => ?_⟩
  · by_cases hx : x ∈ S
    · have h1 := hfin x hx
      unfold IPart.glue at h1 ⊢
      rw [h1]
      exact (hin x hx).idem x
    · rw [hoff x hx, hoff x hx]
  · by_cases hx : x ∈ S
    · exact (hin x hx).le x
    · rw [hoff x hx]
  · by_cases hx : x ∈ S
    · exact hfin x hx
    · rw [hoff x hx]

/-- The partitions of the blocks of `s ∘ r` induced by `r`. -/
noncomputable def splitRoots (S : Finset α) (r t : α → α) : α → α → α := by
  classical
  exact fun m => if m ∈ fix t S then restr r (blk t S m) else id

lemma splitRoots_mem {S : Finset α} {r t : α → α} (hr : IsRoot S r) (hrt : Finer r t) (m : α) :
    splitRoots S r t m ∈ blockRoots S t m := by
  classical
  unfold splitRoots blockRoots
  split_ifs with hm
  · rw [mem_roots]
    refine ⟨fun x hx => ?_, fun x hx => restr_of_notMem hx, fun x => ?_, fun x => ?_⟩
    · rw [restr_of_mem hx]
      obtain ⟨hxS, hxm⟩ := mem_blk.1 hx
      exact mem_blk.2 ⟨hr.mem x hxS, by rw [hrt x, hxm]⟩
    · by_cases hx : x ∈ blk t S m
      · have h1 : r x ∈ blk t S m := by
          obtain ⟨hxS, hxm⟩ := mem_blk.1 hx
          exact mem_blk.2 ⟨hr.mem x hxS, by rw [hrt x, hxm]⟩
        rw [restr_of_mem hx, restr_of_mem h1, hr.idem]
      · rw [restr_of_notMem hx, restr_of_notMem hx]
    · by_cases hx : x ∈ blk t S m
      · rw [restr_of_mem hx]
        exact hr.le x
      · rw [restr_of_notMem hx]
  · exact Finset.mem_singleton_self _

omit [Fintype α] in
lemma glue_splitRoots {S : Finset α} {r t : α → α} (hr : IsRoot S r) (ht : IsRoot S t) :
    glue t (splitRoots S r t) = r := by
  classical
  funext x
  unfold IPart.glue splitRoots
  by_cases hx : x ∈ S
  · rw [if_pos (ht.root_mem_fix hx), restr_of_mem (mem_blk.2 ⟨hx, rfl⟩)]
  · rw [ht.off x hx, if_neg fun h => hx (mem_fix.1 h).1, hr.off x hx]
    rfl

lemma splitRoots_glue {S : Finset α} {t : α → α} {ρ : α → α → α}
    (hρ : ∀ m, ρ m ∈ blockRoots S t m) : splitRoots S (glue t ρ) t = ρ := by
  classical
  funext m x
  unfold splitRoots
  by_cases hm : m ∈ fix t S
  · rw [if_pos hm]
    have h1 := hρ m
    unfold blockRoots at h1
    rw [if_pos hm] at h1
    have h2 := mem_roots.1 h1
    by_cases hx : x ∈ blk t S m
    · rw [restr_of_mem hx]
      unfold IPart.glue
      rw [(mem_blk.1 hx).2]
    · rw [restr_of_notMem hx, h2.off x hx]
  · rw [if_neg hm]
    have h1 := hρ m
    unfold blockRoots at h1
    rw [if_neg hm] at h1
    rw [Finset.mem_singleton.1 h1]

/-- **Partitions of the blocks of a partition, against partitions of the least inputs of a
partition**: `(t, ρ) ↦ (glue t ρ, t restricted to its least inputs)`. -/
theorem sum_blockRoots {M : Type*} [AddCommMonoid M] (S : Finset α)
    (F : (α → α) → (α → α) → M) :
    ∑ t ∈ roots S, ∑ ρ ∈ Fintype.piFinset (blockRoots S t), F (glue t ρ) t
      = ∑ r ∈ roots S, ∑ s ∈ roots (fix r S), F r (s ∘ r) := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨glue x.1 x.2, restrictRoot (glue x.1 x.2) x.1 S⟩)
    (fun x _ => ⟨x.2 ∘ x.1, splitRoots S x.1 (x.2 ∘ x.1)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨t, ρ⟩ hx
    rw [Finset.mem_sigma, mem_roots, Fintype.mem_piFinset] at hx
    obtain ⟨hg, hgt⟩ := hx.1.glue hx.2
    rw [Finset.mem_sigma, mem_roots, mem_roots]
    exact ⟨hg, (hg.restrictRoot hx.1 hgt).1⟩
  · rintro ⟨r, s⟩ hx
    rw [Finset.mem_sigma, mem_roots, mem_roots] at hx
    rw [Finset.mem_sigma, mem_roots, Fintype.mem_piFinset]
    exact ⟨hx.1.comp hx.2, fun m => splitRoots_mem hx.1 (finer_comp r s hx.1.idem) m⟩
  · rintro ⟨t, ρ⟩ hx
    rw [Finset.mem_sigma, mem_roots, Fintype.mem_piFinset] at hx
    obtain ⟨hg, hgt⟩ := hx.1.glue hx.2
    have e1 := (hg.restrictRoot hx.1 hgt).2
    simp only [e1, splitRoots_glue hx.2]
  · rintro ⟨r, s⟩ hx
    rw [Finset.mem_sigma, mem_roots, mem_roots] at hx
    simp only [glue_splitRoots hx.1 (hx.1.comp hx.2), restrictRoot_comp hx.2]
  · rintro ⟨t, ρ⟩ hx
    rw [Finset.mem_sigma, mem_roots, Fintype.mem_piFinset] at hx
    obtain ⟨hg, hgt⟩ := hx.1.glue hx.2
    simp only [(hg.restrictRoot hx.1 hgt).2]

end glue

end IPart

end Operad
