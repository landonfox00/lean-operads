/-
# Shuffle monomials at the root

A shuffle monomial of arity `n ≥ 2` is a root vertex over two subtrees, the left one carrying the
least label `0`. Standardized, the subtrees are monomials of arities `i` and `n - i`, and the labels
of the left subtree are any set of `i` of the labels `0, …, n - 1` containing `0`; conversely such
a set, a decoration and two monomials give a monomial (`joinAt`, `joinAt_mem`, `eq_joinAt`).

So a property of monomials which depends only on the decoration of the root and on the
standardized subtrees (`RootP`) is counted by a binomial convolution (`card_filter_rootP`):

  `#{m ∈ monomials n | P (root of m) (std l) (std r)} =
    Σ_{1 ≤ i < n} C(n - 1, i - 1) · #{(e, a, b) | a ∈ monomials i, b ∈ monomials (n - i), P e a b}`,

the recursion of the exponential generating series of shuffle trees.
-/
import Operad.ShuffleNormal

namespace Operad

namespace LTree

variable {E : Type*}

/-- **A property of the root vertex**: of its decoration and of its two subtrees, standardized. -/
def RootP (P : E → LTree E → LTree E → Prop) : LTree E → Prop
  | leaf _ => False
  | node e l r => P e (std l) (std r)

/-- **The monomial with root `e` over `a` and `b`**, relabelled by the labels in `S` and by the
other labels of `0, …, n - 1`. -/
noncomputable def joinAt (n : ℕ) (S : Finset ℕ) (e : E) (a b : LTree E) : LTree E :=
  node e (destd S a) (destd (Finset.range n \ S) b)

lemma labels_destd_perm (A : Finset ℕ) {t : LTree E} (ht : t.labels.Perm (List.range A.card)) :
    (destd A t).labels.Nodup ∧ (destd A t).labels.toFinset = A := by
  have hs := strictOn_nth A (t := t) fun _ hi => List.mem_range.1 (ht.subset hi)
  have hinj : ∀ a ∈ t.labels, ∀ b ∈ t.labels, Nat.nth (· ∈ A) a = Nat.nth (· ∈ A) b → a = b := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (hs a ha b hb h).ne
    · exact h
    · exact absurd hab (hs b hb a ha h).ne'
  refine ⟨?_, labelSet_destd A ht⟩
  rw [destd, labels_relabel]
  exact (ht.nodup_iff.2 List.nodup_range).map_on hinj

lemma isShuffle_destd (A : Finset ℕ) {t : LTree E} (ht : t.labels.Perm (List.range A.card))
    (hs : t.IsShuffle) : (destd A t).IsShuffle :=
  (isShuffle_relabel t (strictOn_nth A fun _ hi => List.mem_range.1 (ht.subset hi))).2 hs

variable [Fintype E] [DecidableEq E]

/-- **A set of labels containing `0`, a decoration and two monomials make a monomial.** -/
lemma joinAt_mem {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range n) (h0 : 0 ∈ S) (e : E)
    {a b : LTree E} (ha : a ∈ monomials S.card) (hb : b ∈ monomials (n - S.card)) :
    joinAt n S e a b ∈ monomials n := by
  obtain ⟨has, hal⟩ := (mem_monomials _ _).1 ha
  obtain ⟨hbs, hbl⟩ := (mem_monomials _ _).1 hb
  have hcard : (Finset.range n \ S).card = n - S.card := by
    rw [Finset.card_sdiff_of_subset hS, Finset.card_range]
  rw [← hcard] at hbl
  obtain ⟨hand, hat⟩ := labels_destd_perm S hal
  obtain ⟨hbnd, hbt⟩ := labels_destd_perm (Finset.range n \ S) hbl
  rw [mem_monomials]
  refine ⟨⟨?_, isShuffle_destd S hal has, isShuffle_destd _ hbl hbs⟩, ?_⟩
  · have h1 : (destd S a).minLabel = 0 := by
      have := minLabel_le_of_mem (destd S a) (b := 0) (by
        rw [← List.mem_toFinset, hat]; exact h0)
      omega
    have h2 := minLabel_mem (destd (Finset.range n \ S) b)
    rw [← List.mem_toFinset, hbt, Finset.mem_sdiff] at h2
    rw [h1]
    rcases Nat.eq_zero_or_pos (destd (Finset.range n \ S) b).minLabel with h | h
    · rw [h] at h2
      exact absurd h0 h2.2
    · exact h
  · refine List.perm_of_nodup_nodup_toFinset_eq ?_ List.nodup_range ?_
    · rw [joinAt, labels_node, List.nodup_append]
      refine ⟨hand, hbnd, fun x hx y hy hxy => ?_⟩
      subst hxy
      rw [← List.mem_toFinset, hat] at hx
      rw [← List.mem_toFinset, hbt, Finset.mem_sdiff] at hy
      exact hy.2 hx
    · rw [joinAt, labels_node, List.toFinset_append, hat, hbt, List.toFinset_range,
        Finset.union_sdiff_of_subset hS]

/-- **Every monomial of arity `n ≥ 2` is a join** of its standardized subtrees, along the labels
of its left subtree. -/
lemma eq_joinAt {n : ℕ} {e : E} {l r : LTree E} (hm : node e l r ∈ monomials n) :
    l.labelSet ⊆ Finset.range n ∧ 0 ∈ l.labelSet ∧ l.labelSet.card < n ∧
      std l ∈ monomials l.labelSet.card ∧ std r ∈ monomials (n - l.labelSet.card) ∧
      node e l r = joinAt n l.labelSet e (std l) (std r) := by
  obtain ⟨hs, hl⟩ := (mem_monomials _ _).1 hm
  have hnd : (node e l r).labels.Nodup := hl.nodup_iff.2 List.nodup_range
  have hnd' : (l.labels ++ r.labels).Nodup := by simpa using hnd
  have hlnd : l.labels.Nodup := (List.nodup_append.1 hnd').1
  have hrnd : r.labels.Nodup := (List.nodup_append.1 hnd').2.1
  have hmem : ∀ x, x ∈ l.labels ∨ x ∈ r.labels ↔ x < n := by
    intro x
    rw [← List.mem_append, ← labels_node e, hl.mem_iff, List.mem_range]
  have hsub : l.labelSet ⊆ Finset.range n := fun x hx => by
    rw [labelSet, List.mem_toFinset] at hx
    exact Finset.mem_range.2 ((hmem x).1 (Or.inl hx))
  have h0 : 0 ∈ l.labelSet := by
    have hmin : (node e l r).minLabel = 0 := by
      have := minLabel_le_of_mem (node e l r) (b := 0) (by
        rw [hl.mem_iff, List.mem_range]
        have := (hmem _).1 (Or.inl (minLabel_mem l))
        omega)
      omega
    rw [minLabel_node_of_shuffle hs] at hmin
    rw [labelSet, List.mem_toFinset, ← hmin]
    exact minLabel_mem l
  have hcl : l.labelSet.card = l.arity := card_labelSet hlnd
  have hcr : r.arity = n - l.labelSet.card := by
    have := hl.length_eq
    simp only [labels_node, List.length_append, length_labels, List.length_range] at this
    omega
  have hrset : r.labelSet = Finset.range n \ l.labelSet := by
    ext x
    simp only [labelSet, List.mem_toFinset, Finset.mem_sdiff, Finset.mem_range]
    constructor
    · intro hx
      exact ⟨(hmem x).1 (Or.inr hx), fun h => List.disjoint_of_nodup_append hnd' h hx⟩
    · rintro ⟨hx, hx'⟩
      exact ((hmem x).2 hx).resolve_left hx'
  refine ⟨hsub, h0, ?_, ?_, ?_, ?_⟩
  · have := arity_pos r
    omega
  · rw [mem_monomials, hcl]
    exact ⟨isShuffle_std hs.2.1, labels_std_perm hlnd⟩
  · rw [mem_monomials, ← hcr]
    exact ⟨isShuffle_std hs.2.2, labels_std_perm hrnd⟩
  · rw [joinAt, destd_std, ← hrset, destd_std]

omit [Fintype E] [DecidableEq E] in
lemma joinAt_injective {n : ℕ} {S S' : Finset ℕ} {e e' : E} {a a' b b' : LTree E}
    (ha : a.labels.Perm (List.range S.card)) (ha' : a'.labels.Perm (List.range S'.card))
    (hb : b.labels.Perm (List.range (Finset.range n \ S).card))
    (hb' : b'.labels.Perm (List.range (Finset.range n \ S').card))
    (h : joinAt n S e a b = joinAt n S' e' a' b') : S = S' ∧ e = e' ∧ a = a' ∧ b = b' := by
  simp only [joinAt, node.injEq] at h
  obtain ⟨he, hl, hr⟩ := h
  have hS : S = S' := by rw [← labelSet_destd S ha, hl, labelSet_destd S' ha']
  subst hS
  refine ⟨rfl, he, ?_, ?_⟩
  · rw [← std_destd S ha, hl, std_destd S ha']
  · rw [← std_destd _ hb, hr, std_destd _ hb']

omit [Fintype E] [DecidableEq E] in
lemma rootP_joinAt {P : E → LTree E → LTree E → Prop} {n : ℕ} {S : Finset ℕ} {e : E}
    {a b : LTree E} (ha : a.labels.Perm (List.range S.card))
    (hb : b.labels.Perm (List.range (Finset.range n \ S).card)) :
    RootP P (joinAt n S e a b) ↔ P e a b := by
  rw [joinAt, RootP, std_destd S ha, std_destd _ hb]

omit [Fintype E] [DecidableEq E] in
/-- **The sets of `i` labels among `0, …, n - 1` containing `0`**: there are `C(n - 1, i - 1)`. -/
lemma card_sets_zero {n i : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) :
    ((Finset.range n).powerset.filter fun S => 0 ∈ S ∧ S.card = i).card =
      (n - 1).choose (i - 1) := by
  have : (Finset.range n).powerset.filter (fun S => 0 ∈ S ∧ S.card = i) =
      (((Finset.range n).erase 0).powersetCard (i - 1)).image (insert 0) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hS, h0, hc⟩
      refine ⟨S.erase 0, ⟨Finset.erase_subset_erase _ hS, ?_⟩, Finset.insert_erase h0⟩
      rw [Finset.card_erase_of_mem h0, hc]
    · rintro ⟨T, ⟨hT, hc⟩, rfl⟩
      have h0T : 0 ∉ T := fun h => (Finset.mem_erase.1 (hT h)).1 rfl
      refine ⟨Finset.insert_subset (Finset.mem_range.2 (by omega))
        (hT.trans (Finset.erase_subset _ _)), Finset.mem_insert_self _ _, ?_⟩
      rw [Finset.card_insert_of_notMem h0T, hc]
      omega
  rw [this, Finset.card_image_of_injOn, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_range.2 (by omega)), Finset.card_range]
  intro T hT T' hT' h
  rw [Finset.mem_coe, Finset.mem_powersetCard] at hT hT'
  have h0T : 0 ∉ T := fun h => (Finset.mem_erase.1 (hT.1 h)).1 rfl
  have h0T' : 0 ∉ T' := fun h => (Finset.mem_erase.1 (hT'.1 h)).1 rfl
  rw [← Finset.erase_insert h0T, h, Finset.erase_insert h0T']

noncomputable instance (P : E → LTree E → LTree E → Prop) [∀ e a b, Decidable (P e a b)] :
    DecidablePred (RootP P) := fun t => by
  cases t <;> unfold RootP <;> infer_instance

/-- **Counting at the root**: monomials of arity `n` with a property of the root vertex and of
the standardized subtrees, by the number `i` of labels of the left subtree. -/
theorem card_filter_rootP (P : E → LTree E → LTree E → Prop) [DecidablePred (RootP P)]
    [∀ e a b, Decidable (P e a b)] (n : ℕ) :
    ((monomials (E := E) n).filter (RootP P)).card = ∑ i ∈ Finset.Ico 1 n,
      (n - 1).choose (i - 1) * ((Finset.univ ×ˢ (monomials (E := E) i ×ˢ monomials (n - i))).filter
        fun p => P p.1 p.2.1 p.2.2).card := by
  set Sset := (Finset.range n).powerset.filter fun S => 0 ∈ S ∧ S.card < n
  set F : ℕ → Finset (E × LTree E × LTree E) := fun i =>
    (Finset.univ ×ˢ (monomials (E := E) i ×ˢ monomials (n - i))).filter
      fun p => P p.1 p.2.1 p.2.2
  have hX : (monomials (E := E) n).filter (RootP P) =
      (Sset.sigma fun S => F S.card).image fun q => joinAt n q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_sigma, Sset, F,
      Finset.mem_powerset, Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hm, hP⟩
      cases m with
      | leaf a => exact absurd hP id
      | node e l r =>
        obtain ⟨hsub, h0, hlt, hl, hr, heq⟩ := eq_joinAt hm
        exact ⟨⟨l.labelSet, e, std l, std r⟩, ⟨⟨hsub, h0, hlt⟩, ⟨hl, hr⟩, hP⟩, heq.symm⟩
    · rintro ⟨⟨S, e, a, b⟩, ⟨⟨hsub, h0, hlt⟩, ⟨ha, hb⟩, hP⟩, rfl⟩
      have hcard : (Finset.range n \ S).card = n - S.card := by
        rw [Finset.card_sdiff_of_subset hsub, Finset.card_range]
      have hal := ((mem_monomials _ _).1 ha).2
      have hbl := ((mem_monomials _ _).1 hb).2
      rw [← hcard] at hbl
      exact ⟨joinAt_mem hsub h0 e ha hb, (rootP_joinAt hal hbl).2 hP⟩
  rw [hX, Finset.card_image_of_injOn, Finset.card_sigma]
  · rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.Ico 1 n)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_filter.1 hS).2], Finset.sum_const,
        smul_eq_mul]
      congr 1
      rw [← card_sets_zero (by have := Finset.mem_Ico.1 hi; omega) (Finset.mem_Ico.1 hi).1]
      congr 1
      ext S
      simp only [Sset, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨h1, h2, -⟩, h3⟩
        exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2, h3 ▸ (Finset.mem_Ico.1 hi).2⟩, h3⟩
    · intro S hS
      simp only [Sset, Finset.mem_filter, Finset.mem_powerset] at hS
      exact Finset.mem_Ico.2 ⟨Finset.card_pos.2 ⟨0, hS.2.1⟩, hS.2.2⟩
  · rintro ⟨S, e, a, b⟩ hq ⟨S', e', a', b'⟩ hq' h
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Sset, F, Finset.mem_filter,
      Finset.mem_powerset, Finset.mem_product, Finset.mem_univ, true_and] at hq hq' h
    have hal := ((mem_monomials _ _).1 hq.2.1.1).2
    have hal' := ((mem_monomials _ _).1 hq'.2.1.1).2
    have hbl := ((mem_monomials _ _).1 hq.2.1.2).2
    have hbl' := ((mem_monomials _ _).1 hq'.2.1.2).2
    rw [← Finset.card_range n, ← Finset.card_sdiff_of_subset hq.1.1] at hbl
    rw [← Finset.card_range n, ← Finset.card_sdiff_of_subset hq'.1.1] at hbl'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := joinAt_injective hal hal' hbl hbl' h
    rfl

end LTree

end Operad
