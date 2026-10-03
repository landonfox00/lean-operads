/-
# Shuffle trees with generators of any arity

Trees whose vertices are labelled by generators of any arity (`E k` in arity `k`) and whose
leaves are labelled by natural numbers (`Operad.STree`). A tree is a **shuffle tree**
(`STree.IsShuffle`) when every vertex has an input and the children of every vertex are ordered
by their least leaves; the least leaf of a shuffle tree is its leftmost one (`STree.first`,
`STree.first_le`). The leaves form a multiset (`STree.labels`), and a shuffle tree whose leaves
are distinct is a monomial of the free shuffle operad on the set of its leaves.

The operations of the Gröbner theory, and their algebra:
* **substitution** of trees for the leaves (`STree.subst`): associative, with the leaves as unit,
  keeping shuffle trees shuffle when the substituted trees increase with their least leaves
  (`STree.isShuffle_subst`);
* **positions**, lists of child indices: the subtree at a position (`STree.get?`), the
  replacement of the subtree at a position (`STree.replace`); replacements at incomparable
  positions commute (`STree.replace_comm`), a replacement inside a replaced subtree is a
  replacement at the concatenated position (`STree.replace_append`), and replacing by a shuffle
  tree with the same least leaf keeps a shuffle tree shuffle (`STree.isShuffle_replace`);
* substituting after replacing (`STree.replace_subst`); the subtrees of a substituted tree, those
  of the tree or those of a substituted tree below a leaf (`STree.get?_subst_cases`);
  substituting a single leaf, as a replacement at its position (`STree.subst_update`);
* **truncation** at a set of positions (`STree.trunc`), cutting the subtrees outside it down to
  their least leaves, and the recovery of the tree by substituting the cut subtrees back
  (`STree.exists_subst_trunc`).
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Multiset.Bind
import Mathlib.Order.Monotone.Basic

universe v

namespace Operad

/-- **Trees with generators of any arity**: leaves labelled by natural numbers, and vertices of
arity `k` labelled by generators `E k`, with their children indexed by `Fin k`. -/
inductive STree (E : ℕ → Type v) : Type v
  /-- a leaf -/
  | leaf : ℕ → STree E
  /-- a vertex with its children -/
  | node : {k : ℕ} → E k → (Fin k → STree E) → STree E

namespace STree

variable {E : ℕ → Type v}

/-! ## Leaves, least leaves and shuffle trees -/

/-- **The leftmost leaf**, the least leaf of a shuffle tree. -/
def first : STree E → ℕ
  | leaf a => a
  | @node _ k _ c => if h : 0 < k then (c ⟨0, h⟩).first else 0

/-- **The leaves**, as a multiset. -/
def labels : STree E → Multiset ℕ
  | leaf a => {a}
  | node _ c => ∑ i, (c i).labels

/-- **The weight**: the number of vertices. -/
def weight : STree E → ℕ
  | leaf _ => 0
  | node _ c => 1 + ∑ i, (c i).weight

/-- **A shuffle tree**: every vertex has an input, and the children of each vertex increase with
their least leaves. -/
def IsShuffle : STree E → Prop
  | leaf _ => True
  | @node _ k _ c => 0 < k ∧ (∀ i, (c i).IsShuffle) ∧ StrictMono fun i => (c i).first

@[simp] lemma first_leaf (a : ℕ) : (leaf a : STree E).first = a := rfl

lemma first_node {k : ℕ} (e : E k) (c : Fin k → STree E) (h : 0 < k) :
    (node e c).first = (c ⟨0, h⟩).first := by
  simp only [first, dif_pos h]

@[simp] lemma labels_leaf (a : ℕ) : (leaf a : STree E).labels = {a} := rfl

@[simp] lemma labels_node {k : ℕ} (e : E k) (c : Fin k → STree E) :
    (node e c).labels = ∑ i, (c i).labels := rfl

@[simp] lemma weight_leaf (a : ℕ) : (leaf a : STree E).weight = 0 := rfl

@[simp] lemma weight_node {k : ℕ} (e : E k) (c : Fin k → STree E) :
    (node e c).weight = 1 + ∑ i, (c i).weight := rfl

@[simp] lemma isShuffle_leaf (a : ℕ) : (leaf a : STree E).IsShuffle := trivial

lemma isShuffle_node {k : ℕ} {e : E k} {c : Fin k → STree E} :
    (node e c).IsShuffle ↔ 0 < k ∧ (∀ i, (c i).IsShuffle) ∧ StrictMono fun i => (c i).first :=
  Iff.rfl

lemma mem_labels_node {k : ℕ} {e : E k} {c : Fin k → STree E} {a : ℕ} :
    a ∈ (node e c).labels ↔ ∃ i, a ∈ (c i).labels := by
  simp [Multiset.mem_sum]

lemma labels_le_node {k : ℕ} (e : E k) (c : Fin k → STree E) (i : Fin k) :
    (c i).labels ≤ (node e c).labels :=
  Finset.single_le_sum (f := fun j => (c j).labels) (fun _ _ => Multiset.zero_le _)
    (Finset.mem_univ i)

lemma nodup_of_node {k : ℕ} {e : E k} {c : Fin k → STree E} (h : (node e c).labels.Nodup)
    (i : Fin k) : (c i).labels.Nodup :=
  Multiset.nodup_of_le (labels_le_node e c i) h

lemma disjoint_of_node {k : ℕ} {e : E k} {c : Fin k → STree E} (h : (node e c).labels.Nodup)
    {i j : Fin k} (hij : i ≠ j) : Disjoint (c i).labels (c j).labels := by
  have hle : (c i).labels + (c j).labels ≤ (node e c).labels := by
    rw [labels_node, ← Finset.sum_pair (f := fun x => (c x).labels) hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => Multiset.zero_le _
  exact (Multiset.nodup_add.1 (Multiset.nodup_of_le hle h)).2.2

lemma not_mem_of_node {k : ℕ} {e : E k} {c : Fin k → STree E} (h : (node e c).labels.Nodup)
    {i j : Fin k} (hij : i ≠ j) {a : ℕ} (ha : a ∈ (c i).labels) : a ∉ (c j).labels :=
  Multiset.disjoint_left.1 (disjoint_of_node h hij) ha

lemma IsShuffle.pos {k : ℕ} {e : E k} {c : Fin k → STree E} (h : (node e c).IsShuffle) : 0 < k :=
  h.1

lemma IsShuffle.child {k : ℕ} {e : E k} {c : Fin k → STree E} (h : (node e c).IsShuffle)
    (i : Fin k) : (c i).IsShuffle :=
  h.2.1 i

lemma IsShuffle.mono {k : ℕ} {e : E k} {c : Fin k → STree E} (h : (node e c).IsShuffle) :
    StrictMono fun i => (c i).first :=
  h.2.2

/-- **The least leaf of a shuffle tree is a leaf.** -/
theorem first_mem : ∀ {t : STree E}, t.IsShuffle → t.first ∈ t.labels
  | leaf _, _ => Multiset.mem_singleton_self _
  | @node _ k e c, h => by
    rw [first_node e c h.pos]
    exact Multiset.mem_of_le (labels_le_node e c _) (first_mem (h.child _))

/-- **The leftmost leaf of a shuffle tree is its least leaf.** -/
theorem first_le : ∀ {t : STree E}, t.IsShuffle → ∀ a ∈ t.labels, t.first ≤ a
  | leaf _, _, a, ha => by rw [Multiset.mem_singleton.1 ha]; rfl
  | @node _ k e c, h, a, ha => by
    obtain ⟨i, hi⟩ := mem_labels_node.1 ha
    rw [first_node e c h.pos]
    exact (h.mono.monotone (show (⟨0, h.pos⟩ : Fin k) ≤ i from Nat.zero_le _)).trans
      (first_le (h.child i) a hi)

/-- Two shuffle trees with the same leaves have the same least leaf. -/
theorem first_eq_of_labels_eq {s t : STree E} (hs : s.IsShuffle) (ht : t.IsShuffle)
    (h : s.labels = t.labels) : s.first = t.first :=
  le_antisymm (first_le hs _ (h ▸ first_mem ht)) (first_le ht _ (h.symm ▸ first_mem hs))

/-! ## Substitution -/

/-- **Substitution** of trees for the leaves. -/
def subst : STree E → (ℕ → STree E) → STree E
  | leaf a, xs => xs a
  | node e c, xs => node e fun i => (c i).subst xs

@[simp] lemma subst_leaf' (a : ℕ) (xs : ℕ → STree E) : (leaf a).subst xs = xs a := rfl

@[simp] lemma subst_node {k : ℕ} (e : E k) (c : Fin k → STree E) (xs : ℕ → STree E) :
    (node e c).subst xs = node e fun i => (c i).subst xs := rfl

/-- **The leaves are a unit for substitution.** -/
theorem subst_leaf : ∀ t : STree E, t.subst leaf = t
  | leaf _ => rfl
  | node e c => by
    rw [subst_node]
    congr 1
    funext i
    exact subst_leaf (c i)

/-- **Substitution is associative.** -/
theorem subst_subst : ∀ (t : STree E) (xs ys : ℕ → STree E),
    (t.subst xs).subst ys = t.subst fun a => (xs a).subst ys
  | leaf _, _, _ => rfl
  | node e c, xs, ys => by
    simp only [subst_node]
    congr 1
    funext i
    exact subst_subst (c i) xs ys

/-- Substitution only depends on the substituted trees at the leaves. -/
theorem subst_congr : ∀ (t : STree E) {xs ys : ℕ → STree E}, (∀ a ∈ t.labels, xs a = ys a) →
    t.subst xs = t.subst ys
  | leaf a, _, _, h => h a (Multiset.mem_singleton_self a)
  | node e c, _, _, h => by
    simp only [subst_node]
    congr 1
    funext i
    exact subst_congr (c i) fun a ha => h a (mem_labels_node.2 ⟨i, ha⟩)

lemma sum_bind {ι : Type*} (s : Finset ι) (g : ι → Multiset ℕ) (f : ℕ → Multiset ℕ) :
    (∑ i ∈ s, g i).bind f = ∑ i ∈ s, (g i).bind f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Multiset.add_bind, ih]

/-- **The leaves of a substituted tree.** -/
theorem labels_subst : ∀ (t : STree E) (xs : ℕ → STree E),
    (t.subst xs).labels = t.labels.bind fun a => (xs a).labels
  | leaf a, xs => by simp
  | node e c, xs => by
    simp only [subst_node, labels_node, sum_bind]
    exact Finset.sum_congr rfl fun i _ => labels_subst (c i) xs

/-- **The least leaf of a substituted shuffle tree.** -/
theorem first_subst : ∀ {t : STree E}, t.IsShuffle → ∀ xs : ℕ → STree E,
    (t.subst xs).first = (xs t.first).first
  | leaf _, _, _ => rfl
  | @node _ k e c, h, xs => by
    rw [subst_node, first_node _ _ h.pos, first_node _ _ h.pos]
    exact first_subst (h.child _) xs

/-- **Substitution keeps shuffle trees shuffle** when the substituted trees are shuffle trees
increasing with their least leaves. -/
theorem isShuffle_subst : ∀ {t : STree E}, t.IsShuffle → ∀ {xs : ℕ → STree E},
    (∀ a ∈ t.labels, (xs a).IsShuffle) →
    StrictMonoOn (fun a => (xs a).first) {a | a ∈ t.labels} → (t.subst xs).IsShuffle
  | leaf a, _, _, hx, _ => hx a (Multiset.mem_singleton_self a)
  | @node _ k e c, h, xs, hx, hm => by
    refine ⟨h.pos, fun i => isShuffle_subst (h.child i)
      (fun a ha => hx a (mem_labels_node.2 ⟨i, ha⟩))
      (fun a ha b hb hab => hm (mem_labels_node.2 ⟨i, ha⟩) (mem_labels_node.2 ⟨i, hb⟩) hab),
      fun i j hij => ?_⟩
    simp only [first_subst (h.child _)]
    exact hm (mem_labels_node.2 ⟨i, first_mem (h.child i)⟩)
      (mem_labels_node.2 ⟨j, first_mem (h.child j)⟩) (h.mono hij)

/-! ## Positions -/

/-- **The subtree at a position**, a list of child indices. -/
def get? : STree E → List ℕ → Option (STree E)
  | t, [] => some t
  | leaf _, _ :: _ => none
  | @node _ k _ c, i :: p => if h : i < k then (c ⟨i, h⟩).get? p else none

/-- **Replace the subtree at a position.** A position which is not one of the tree leaves it
unchanged. -/
def replace : STree E → List ℕ → STree E → STree E
  | _, [], u => u
  | leaf a, _ :: _, _ => leaf a
  | node e c, i :: p, u => node e fun j => if (j : ℕ) = i then (c j).replace p u else c j

@[simp] lemma get?_nil (t : STree E) : t.get? [] = some t := by cases t <;> rfl

@[simp] lemma get?_leaf_cons (a i : ℕ) (p : List ℕ) : (leaf a : STree E).get? (i :: p) = none :=
  rfl

lemma get?_node_cons {k : ℕ} (e : E k) (c : Fin k → STree E) (i : ℕ) (p : List ℕ) :
    (node e c).get? (i :: p) = if h : i < k then (c ⟨i, h⟩).get? p else none := rfl

lemma get?_node_cons_fin {k : ℕ} (e : E k) (c : Fin k → STree E) (i : Fin k) (p : List ℕ) :
    (node e c).get? (i.1 :: p) = (c i).get? p := by
  rw [get?_node_cons, dif_pos i.2]

lemma get?_node_cons_eq_some {k : ℕ} {e : E k} {c : Fin k → STree E} {i : ℕ} {p : List ℕ}
    {u : STree E} :
    (node e c).get? (i :: p) = some u ↔ ∃ hi : i < k, (c ⟨i, hi⟩).get? p = some u := by
  rw [get?_node_cons]
  split_ifs with hi
  · exact ⟨fun h => ⟨hi, h⟩, fun ⟨_, h⟩ => h⟩
  · exact ⟨fun h => absurd h (by simp), fun ⟨h', _⟩ => absurd h' hi⟩

lemma get?_node_cons_isSome {k : ℕ} {e : E k} {c : Fin k → STree E} {i : ℕ} {p : List ℕ} :
    ((node e c).get? (i :: p)).isSome ↔ ∃ hi : i < k, ((c ⟨i, hi⟩).get? p).isSome := by
  rw [get?_node_cons]
  split_ifs with hi
  · exact ⟨fun h => ⟨hi, h⟩, fun ⟨_, h⟩ => h⟩
  · exact ⟨fun h => absurd h (by simp), fun ⟨h', _⟩ => absurd h' hi⟩

@[simp] lemma replace_nil (t u : STree E) : t.replace [] u = u := by cases t <;> rfl

@[simp] lemma replace_leaf_cons (a i : ℕ) (p : List ℕ) (u : STree E) :
    (leaf a : STree E).replace (i :: p) u = leaf a := rfl

lemma replace_node_cons {k : ℕ} (e : E k) (c : Fin k → STree E) (i : ℕ) (p : List ℕ)
    (u : STree E) :
    (node e c).replace (i :: p) u =
      node e fun j => if (j : ℕ) = i then (c j).replace p u else c j :=
  rfl

/-- **The subtree at a concatenated position.** -/
theorem get?_append : ∀ (t : STree E) (p q : List ℕ),
    t.get? (p ++ q) = (t.get? p).bind fun u => u.get? q
  | t, [], q => by simp
  | leaf _, _ :: _, _ => rfl
  | @node _ k e c, i :: p, q => by
    simp only [List.cons_append, get?_node_cons]
    split_ifs
    · exact get?_append _ p q
    · rfl

lemma get?_append_of {t u : STree E} {p : List ℕ} (h : t.get? p = some u) (q : List ℕ) :
    t.get? (p ++ q) = u.get? q := by
  rw [get?_append, h, Option.bind_some]

/-- **Replacing a subtree by itself.** -/
theorem replace_self : ∀ {t u : STree E} {p : List ℕ}, t.get? p = some u → t.replace p u = t
  | t, u, [], h => by rw [get?_nil, Option.some_inj] at h; rw [replace_nil, h]
  | leaf _, _, _ :: _, h => by simp at h
  | @node _ k e c, u, i :: p, h => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    rw [replace_node_cons]
    congr 1
    funext j
    split_ifs with hj
    · have : j = ⟨i, hi⟩ := Fin.ext hj
      subst this
      exact replace_self h
    · rfl

/-- **The subtree at a replaced position** is the replacing tree. -/
theorem get?_replace : ∀ {t : STree E} {p : List ℕ}, (t.get? p).isSome → ∀ u : STree E,
    (t.replace p u).get? p = some u
  | t, [], _, u => by simp
  | leaf _, _ :: _, h, _ => by simp at h
  | @node _ k e c, i :: p, h, u => by
    obtain ⟨hi, h⟩ := get?_node_cons_isSome.1 h
    rw [replace_node_cons, get?_node_cons, dif_pos hi]
    show STree.get? (if i = i then _ else _) p = _
    rw [if_pos rfl]
    exact get?_replace h u

/-- **Replacing twice at the same position.** -/
theorem replace_replace : ∀ (t : STree E) (p : List ℕ) (u v : STree E),
    (t.replace p u).replace p v = t.replace p v
  | t, [], u, v => by simp
  | leaf _, _ :: _, _, _ => rfl
  | node e c, i :: p, u, v => by
    simp only [replace_node_cons]
    congr 1
    funext j
    split_ifs with hj
    · exact replace_replace _ p u v
    · rfl

/-- **A replacement inside a replaced subtree.** -/
theorem replace_append : ∀ {t w : STree E} {p : List ℕ}, t.get? p = some w →
    ∀ (q : List ℕ) (v : STree E), t.replace (p ++ q) v = t.replace p (w.replace q v)
  | t, w, [], h, q, v => by
    rw [get?_nil, Option.some_inj] at h
    subst h
    simp
  | leaf _, _, _ :: _, h, _, _ => by simp at h
  | @node _ k e c, w, i :: p, h, q, v => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    simp only [List.cons_append, replace_node_cons]
    congr 1
    funext j
    split_ifs with hj
    · have : j = ⟨i, hi⟩ := Fin.ext hj
      subst this
      exact replace_append h q v
    · rfl

/-- **The subtree at a position of a replaced subtree.** -/
theorem get?_replace_append {t : STree E} {p : List ℕ} (h : (t.get? p).isSome) (u : STree E)
    (q : List ℕ) : (t.replace p u).get? (p ++ q) = u.get? q :=
  get?_append_of (get?_replace h u) q

/-- **Incomparable positions**: they agree up to a common prefix and then differ. -/
def Incomp (p q : List ℕ) : Prop :=
  ∃ r i j p' q', i ≠ j ∧ p = r ++ i :: p' ∧ q = r ++ j :: q'

lemma Incomp.symm {p q : List ℕ} (h : Incomp p q) : Incomp q p := by
  obtain ⟨r, i, j, p', q', hij, rfl, rfl⟩ := h
  exact ⟨r, j, i, q', p', hij.symm, rfl, rfl⟩

/-- **Two positions are comparable or incomparable.** -/
theorem prefix_or_incomp : ∀ p q : List ℕ, p <+: q ∨ q <+: p ∨ Incomp p q
  | [], _ => Or.inl (List.nil_prefix)
  | _ :: _, [] => Or.inr (Or.inl List.nil_prefix)
  | i :: p, j :: q => by
    by_cases hij : i = j
    · subst hij
      rcases prefix_or_incomp p q with h | h | ⟨r, a, b, p', q', hab, rfl, rfl⟩
      · exact Or.inl (List.cons_prefix_cons.2 ⟨rfl, h⟩)
      · exact Or.inr (Or.inl (List.cons_prefix_cons.2 ⟨rfl, h⟩))
      · exact Or.inr (Or.inr ⟨i :: r, a, b, p', q', hab, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨[], i, j, p, q, hij, rfl, rfl⟩)

/-- **The subtree at a position incomparable with the replaced one** does not change. -/
theorem get?_replace_of_incomp : ∀ (r : List ℕ) {i j : ℕ}, i ≠ j → ∀ (t : STree E)
    (p' q' : List ℕ) (u : STree E),
    (t.replace (r ++ i :: p') u).get? (r ++ j :: q') = t.get? (r ++ j :: q')
  | [], i, j, hij, leaf _, _, _, _ => rfl
  | [], i, j, hij, @node _ k e c, p', q', u => by
    rw [List.nil_append, List.nil_append, replace_node_cons, get?_node_cons, get?_node_cons]
    split_ifs with hj h <;> first | rfl | exact absurd h (Ne.symm hij)
  | _ :: _, _, _, _, leaf _, _, _, _ => rfl
  | a :: r, i, j, hij, @node _ k e c, p', q', u => by
    rw [List.cons_append, List.cons_append, replace_node_cons, get?_node_cons, get?_node_cons]
    split_ifs <;> first | rfl | exact get?_replace_of_incomp r hij _ p' q' u

lemma get?_replace_of_incomp' {p q : List ℕ} (h : Incomp p q) (t u : STree E) :
    (t.replace p u).get? q = t.get? q := by
  obtain ⟨r, i, j, p', q', hij, rfl, rfl⟩ := h
  exact get?_replace_of_incomp r hij t p' q' u

/-- **Replacements at incomparable positions commute.** -/
theorem replace_comm_of_incomp : ∀ (r : List ℕ) {i j : ℕ}, i ≠ j → ∀ (t : STree E)
    (p' q' : List ℕ) (u v : STree E),
    (t.replace (r ++ i :: p') u).replace (r ++ j :: q') v =
      (t.replace (r ++ j :: q') v).replace (r ++ i :: p') u
  | [], i, j, hij, leaf _, _, _, _, _ => rfl
  | [], i, j, hij, node e c, p', q', u, v => by
    simp only [List.nil_append, replace_node_cons]
    congr 1
    funext l
    split_ifs <;> first | rfl | (exfalso; omega)
  | _ :: _, _, _, _, leaf _, _, _, _, _ => rfl
  | a :: r, i, j, hij, node e c, p', q', u, v => by
    simp only [List.cons_append, replace_node_cons]
    congr 1
    funext l
    split_ifs with ha
    · exact replace_comm_of_incomp r hij _ p' q' u v
    · rfl

lemma replace_comm {p q : List ℕ} (h : Incomp p q) (t u v : STree E) :
    (t.replace p u).replace q v = (t.replace q v).replace p u := by
  obtain ⟨r, i, j, p', q', hij, rfl, rfl⟩ := h
  exact replace_comm_of_incomp r hij t p' q' u v

/-! ## Positions and shuffle trees -/

lemma isShuffle_get? : ∀ {t u : STree E} {p : List ℕ}, t.IsShuffle → t.get? p = some u →
    u.IsShuffle
  | t, u, [], ht, h => by rw [get?_nil, Option.some_inj] at h; exact h ▸ ht
  | leaf _, _, _ :: _, _, h => by simp at h
  | @node _ k e c, u, i :: p, ht, h => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    exact isShuffle_get? (ht.child _) h

lemma labels_get?_le : ∀ {t u : STree E} {p : List ℕ}, t.get? p = some u →
    u.labels ≤ t.labels
  | t, u, [], h => by rw [get?_nil, Option.some_inj] at h; exact h ▸ le_rfl
  | leaf _, _, _ :: _, h => by simp at h
  | @node _ k e c, u, i :: p, h => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    exact (labels_get?_le h).trans (labels_le_node e c _)

/-- **Replacing a subtree by one with the same least leaf** keeps the least leaf. -/
theorem first_replace : ∀ {t u : STree E} {p : List ℕ}, t.get? p = some u → ∀ {v : STree E},
    v.first = u.first → (t.replace p v).first = t.first
  | t, u, [], h, v, hv => by
    rw [get?_nil, Option.some_inj] at h
    subst h
    simpa using hv
  | leaf _, _, _ :: _, h, _, _ => by simp at h
  | @node _ k e c, u, i :: p, h, v, hv => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    have hk : 0 < k := by omega
    rw [replace_node_cons, first_node _ _ hk, first_node _ _ hk]
    show STree.first (if 0 = i then _ else _) = _
    by_cases h0 : 0 = i
    · subst h0
      rw [if_pos rfl]
      exact first_replace h hv
    · rw [if_neg h0]

/-- **Replacing a subtree of a shuffle tree by a shuffle tree with the same least leaf** gives a
shuffle tree. -/
theorem isShuffle_replace : ∀ {t u : STree E} {p : List ℕ}, t.IsShuffle → t.get? p = some u →
    ∀ {v : STree E}, v.IsShuffle → v.first = u.first → (t.replace p v).IsShuffle
  | t, u, [], _, _, v, hv, _ => by simpa using hv
  | leaf _, _, _ :: _, _, h, _, _, _ => by simp at h
  | @node _ k e c, u, i :: p, ht, h, v, hv, hvu => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    rw [replace_node_cons]
    refine ⟨ht.pos, fun j => ?_, ?_⟩
    · dsimp only
      split_ifs with hj
      · have : j = ⟨i, hi⟩ := Fin.ext hj
        subst this
        exact isShuffle_replace (ht.child _) h hv hvu
      · exact ht.child j
    · have : (fun j : Fin k => (if (j : ℕ) = i then (c j).replace p v else c j).first) =
          fun j => (c j).first := by
        funext j
        split_ifs with hj
        · have : j = ⟨i, hi⟩ := Fin.ext hj
          subst this
          exact first_replace h hvu
        · rfl
      rw [this]
      exact ht.mono

/-- **The leaves of a replaced tree.** -/
theorem labels_replace : ∀ {t u : STree E} {p : List ℕ}, t.get? p = some u → ∀ v : STree E,
    (t.replace p v).labels + u.labels = t.labels + v.labels
  | t, u, [], h, v => by
    rw [get?_nil, Option.some_inj] at h
    subst h
    simp [add_comm]
  | leaf _, _, _ :: _, h, _ => by simp at h
  | @node _ k e c, u, i :: p, h, v => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    have key := labels_replace h v
    let c' : Fin k → STree E := fun j => if (j : ℕ) = i then (c j).replace p v else c j
    have h1 : ∀ j ∈ Finset.univ.erase (⟨i, hi⟩ : Fin k), (c' j).labels = (c j).labels :=
      fun j hj => by
        simp only [c']
        rw [if_neg fun h' => (Finset.mem_erase.1 hj).1 (Fin.ext h')]
    have h2 : c' ⟨i, hi⟩ = (c ⟨i, hi⟩).replace p v := if_pos rfl
    rw [replace_node_cons, labels_node, labels_node]
    change ∑ j, (c' j).labels + u.labels = ∑ j, (c j).labels + v.labels
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨i, hi⟩ : Fin k)),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨i, hi⟩ : Fin k)), Finset.sum_congr rfl h1, h2,
      add_right_comm, key, add_right_comm]

lemma labels_replace_of_eq {t u v : STree E} {p : List ℕ} (h : t.get? p = some u)
    (huv : v.labels = u.labels) : (t.replace p v).labels = t.labels := by
  have := labels_replace h v
  rw [huv] at this
  exact add_right_cancel this

/-- **A leaf has a position.** -/
theorem exists_get?_leaf : ∀ {t : STree E} {a : ℕ}, a ∈ t.labels → ∃ q, t.get? q = some (leaf a)
  | leaf b, a, h => ⟨[], by rw [Multiset.mem_singleton.1 h]; rfl⟩
  | @node _ k e c, a, h => by
    obtain ⟨i, hi⟩ := mem_labels_node.1 h
    obtain ⟨q, hq⟩ := exists_get?_leaf hi
    exact ⟨i.1 :: q, by rw [get?_node_cons_fin]; exact hq⟩

lemma mem_labels_of_get? {t : STree E} {q : List ℕ} {a : ℕ} (h : t.get? q = some (leaf a)) :
    a ∈ t.labels :=
  Multiset.mem_of_le (labels_get?_le h) (Multiset.mem_singleton_self a)

/-- **A leaf of a tree with distinct leaves has a single position.** -/
theorem get?_leaf_unique : ∀ {t : STree E}, t.labels.Nodup → ∀ {a : ℕ} {q q' : List ℕ},
    t.get? q = some (leaf a) → t.get? q' = some (leaf a) → q = q'
  | leaf b, _, a, [], [], _, _ => rfl
  | leaf b, _, a, _ :: _, _, h, _ => by simp at h
  | leaf b, _, a, [], _ :: _, _, h => by simp at h
  | @node _ k e c, _, a, [], _, h, _ => by simp at h
  | @node _ k e c, _, a, _ :: _, [], _, h => by simp at h
  | @node _ k e c, hn, a, i :: q, j :: q', h, h' => by
    rw [get?_node_cons] at h h'
    split_ifs at h with hi
    split_ifs at h' with hj
    by_cases hij : (⟨i, hi⟩ : Fin k) = ⟨j, hj⟩
    · cases Fin.mk.inj_iff.1 hij
      rw [get?_leaf_unique (nodup_of_node hn _) h h']
    · exact absurd (mem_labels_of_get? h')
        (not_mem_of_node hn hij (mem_labels_of_get? h))

open Classical in
/-- **The position of a leaf** (the root when it is not a leaf). -/
noncomputable def pos (t : STree E) (a : ℕ) : List ℕ :=
  if h : ∃ q, t.get? q = some (leaf a) then h.choose else []

lemma get?_pos {t : STree E} {a : ℕ} (h : a ∈ t.labels) : t.get? (t.pos a) = some (leaf a) := by
  have h' := exists_get?_leaf h
  rw [pos, dif_pos h']
  exact h'.choose_spec

lemma pos_eq {t : STree E} (hn : t.labels.Nodup) {a : ℕ} {q : List ℕ}
    (h : t.get? q = some (leaf a)) : t.pos a = q :=
  get?_leaf_unique hn (get?_pos (mem_labels_of_get? h)) h

/-! ## Positions and substitution -/

/-- **The subtrees of a tree, substituted.** -/
theorem get?_subst : ∀ {t u : STree E} {q : List ℕ}, t.get? q = some u → ∀ xs : ℕ → STree E,
    (t.subst xs).get? q = some (u.subst xs)
  | t, u, [], h, xs => by rw [get?_nil, Option.some_inj] at h; subst h; simp
  | leaf _, _, _ :: _, h, _ => by simp at h
  | @node _ k e c, u, i :: q, h, xs => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    rw [subst_node, get?_node_cons, dif_pos hi]
    exact get?_subst h xs

/-- **The subtrees of a substituted tree**: a substituted subtree of the tree, or a subtree of a
substituted tree below a leaf. -/
theorem get?_subst_cases : ∀ {t w : STree E} {xs : ℕ → STree E} {q : List ℕ},
    (t.subst xs).get? q = some w →
    (∃ u, t.get? q = some u ∧ w = u.subst xs) ∨
      ∃ q₀ i q' a, q = q₀ ++ i :: q' ∧ t.get? q₀ = some (leaf a) ∧ (xs a).get? (i :: q') = some w
  | t, w, xs, [], h => by
    rw [get?_nil, Option.some_inj] at h
    exact Or.inl ⟨t, get?_nil t, h.symm⟩
  | leaf a, w, xs, i :: q, h => Or.inr ⟨[], i, q, a, rfl, rfl, h⟩
  | @node _ k e c, w, xs, i :: q, h => by
    rw [subst_node, get?_node_cons] at h
    split_ifs at h with hi
    rcases get?_subst_cases h with ⟨u, hu, rfl⟩ | ⟨q₀, j, q', a, rfl, h₀, h'⟩
    · exact Or.inl ⟨u, by rw [get?_node_cons, dif_pos hi]; exact hu, rfl⟩
    · exact Or.inr ⟨i :: q₀, j, q', a, rfl, by rw [get?_node_cons, dif_pos hi]; exact h₀, h'⟩

/-- **Substituting after replacing.** -/
theorem replace_subst : ∀ {t : STree E} {p : List ℕ}, (t.get? p).isSome →
    ∀ (u : STree E) (xs : ℕ → STree E),
    (t.replace p u).subst xs = (t.subst xs).replace p (u.subst xs)
  | t, [], _, u, xs => by simp
  | leaf _, _ :: _, h, _, _ => by simp at h
  | @node _ k e c, i :: p, h, u, xs => by
    obtain ⟨hi, h⟩ := get?_node_cons_isSome.1 h
    simp only [replace_node_cons, subst_node]
    congr 1
    funext j
    split_ifs with hj
    · have : j = ⟨i, hi⟩ := Fin.ext hj
      subst this
      exact replace_subst h u xs
    · rfl

/-- **Substituting a single leaf** is a replacement at its position, in a tree with distinct
leaves. -/
theorem subst_update : ∀ {t : STree E}, t.labels.Nodup → ∀ {q : List ℕ} {a : ℕ},
    t.get? q = some (leaf a) → ∀ (xs : ℕ → STree E) (w : STree E),
    t.subst (Function.update xs a w) = (t.subst xs).replace q w
  | t, _, [], a, h, xs, w => by
    rw [get?_nil, Option.some_inj] at h
    subst h
    simp
  | leaf _, _, _ :: _, _, h, _, _ => by simp at h
  | @node _ k e c, hn, i :: q, a, h, xs, w => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    simp only [subst_node, replace_node_cons]
    congr 1
    funext j
    split_ifs with hj
    · have : j = ⟨i, hi⟩ := Fin.ext hj
      subst this
      exact subst_update (nodup_of_node hn _) h xs w
    · refine subst_congr _ fun b hb => Function.update_of_ne ?_ _ _
      rintro rfl
      exact not_mem_of_node hn (fun h' => hj (by rw [← h'])) (mem_labels_of_get? h) hb

/-! ## Truncation -/

open Classical in
/-- **Truncation** at a set `V` of positions: the vertices at positions in `V` are kept, and the
subtrees at the first positions outside `V` are cut down to their least leaves. -/
noncomputable def trunc : STree E → Set (List ℕ) → STree E
  | leaf a, _ => leaf a
  | t@(node e c), V => if [] ∈ V then node e fun i => (c i).trunc {p | (i : ℕ) :: p ∈ V}
      else leaf t.first

/-- **The positions below a position.** -/
def shift (V : Set (List ℕ)) (p : List ℕ) : Set (List ℕ) := {q | p ++ q ∈ V}

@[simp] lemma mem_shift {V : Set (List ℕ)} {p q : List ℕ} : q ∈ shift V p ↔ p ++ q ∈ V := Iff.rfl

lemma shift_nil (V : Set (List ℕ)) : shift V [] = V := rfl

lemma shift_shift (V : Set (List ℕ)) (p q : List ℕ) : shift (shift V p) q = shift V (p ++ q) := by
  ext r
  simp [List.append_assoc]

@[simp] lemma trunc_leaf (a : ℕ) (V : Set (List ℕ)) : (leaf a : STree E).trunc V = leaf a := rfl

lemma trunc_node_of_mem {k : ℕ} (e : E k) (c : Fin k → STree E) {V : Set (List ℕ)}
    (h : [] ∈ V) : (node e c).trunc V = node e fun i => (c i).trunc (shift V [i]) := by
  rw [trunc, if_pos h]
  rfl

lemma trunc_node_of_not_mem {k : ℕ} (e : E k) (c : Fin k → STree E) {V : Set (List ℕ)}
    (h : [] ∉ V) : (node e c).trunc V = leaf (node e c).first := by
  rw [trunc, if_neg h]

/-- **Truncation keeps the least leaf.** -/
theorem first_trunc : ∀ {t : STree E}, t.IsShuffle → ∀ V : Set (List ℕ), (t.trunc V).first = t.first
  | leaf _, _, _ => rfl
  | @node _ k e c, h, V => by
    by_cases hV : [] ∈ V
    · rw [trunc_node_of_mem e c hV, first_node _ _ h.pos, first_node _ _ h.pos]
      exact first_trunc (h.child _) _
    · rw [trunc_node_of_not_mem e c hV]
      rfl

/-- **Truncation keeps shuffle trees shuffle.** -/
theorem isShuffle_trunc : ∀ {t : STree E}, t.IsShuffle → ∀ V : Set (List ℕ), (t.trunc V).IsShuffle
  | leaf _, _, _ => trivial
  | @node _ k e c, h, V => by
    by_cases hV : [] ∈ V
    · rw [trunc_node_of_mem e c hV]
      refine ⟨h.pos, fun i => isShuffle_trunc (h.child i) _, ?_⟩
      simp only [first_trunc (h.child _)]
      exact h.mono
    · rw [trunc_node_of_not_mem e c hV]
      trivial

/-- **The leaves of a truncated shuffle tree are among its leaves.** -/
theorem labels_trunc_le : ∀ {t : STree E}, t.IsShuffle → ∀ V : Set (List ℕ),
    (t.trunc V).labels ≤ t.labels
  | leaf _, _, _ => le_rfl
  | @node _ k e c, h, V => by
    by_cases hV : [] ∈ V
    · rw [trunc_node_of_mem e c hV, labels_node, labels_node]
      exact Finset.sum_le_sum fun i _ => labels_trunc_le (h.child i) _
    · rw [trunc_node_of_not_mem e c hV, labels_leaf, Multiset.singleton_le]
      exact first_mem h

/-- **The vertices of a truncated tree** are in the truncating set. -/
theorem get?_trunc_node : ∀ {t : STree E} {V : Set (List ℕ)} {q : List ℕ} {k : ℕ} {e : E k}
    {c : Fin k → STree E}, (t.trunc V).get? q = some (node e c) → q ∈ V
  | leaf _, V, [], _, _, _, h => by simp at h
  | leaf _, V, _ :: _, _, _, _, h => by simp at h
  | @node _ k' e' c', V, q, k, e, c, h => by
    by_cases hV : [] ∈ V
    · rw [trunc_node_of_mem e' c' hV] at h
      cases q with
      | nil => exact hV
      | cons i q =>
        obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
        have := get?_trunc_node h
        exact this
    · rw [trunc_node_of_not_mem e' c' hV] at h
      cases q with
      | nil => simp at h
      | cons i q => simp at h

/-- **The subtrees of a truncated tree**, along positions in the truncating set. -/
theorem get?_trunc : ∀ {t u : STree E} {q : List ℕ}, t.get? q = some u → ∀ {V : Set (List ℕ)},
    (∀ q', q' <+: q → q' ≠ q → q' ∈ V) → (t.trunc V).get? q = some (u.trunc (shift V q))
  | t, u, [], h, V, _ => by
    rw [get?_nil, Option.some_inj] at h
    subst h
    rw [get?_nil, shift_nil]
  | leaf _, _, _ :: _, h, _, _ => by simp at h
  | @node _ k e c, u, i :: q, h, V, hV => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    rw [trunc_node_of_mem e c (hV [] List.nil_prefix (List.cons_ne_nil i q).symm), get?_node_cons,
      dif_pos hi]
    rw [show shift V (i :: q) = shift (shift V [i]) q by rw [shift_shift]; rfl]
    refine get?_trunc h fun q' hq' hne => ?_
    exact hV (i :: q') (List.cons_prefix_cons.2 ⟨rfl, hq'⟩) fun h' => hne (List.cons_injective h')

/-- **Truncating a substituted tree** along a set containing the vertices of the tree. -/
theorem trunc_subst : ∀ {t : STree E}, t.labels.Nodup → ∀ (xs : ℕ → STree E) {V : Set (List ℕ)},
    (∀ q k (e : E k) c, t.get? q = some (node e c) → q ∈ V) →
    (t.subst xs).trunc V = t.subst fun a => (xs a).trunc (shift V (t.pos a))
  | leaf a, _, xs, V, _ => by
    simp only [subst_leaf']
    rw [pos_eq (t := leaf a) (Multiset.nodup_singleton a) (get?_nil _), shift_nil]
  | @node _ k e c, hn, xs, V, hV => by
    rw [subst_node, trunc_node_of_mem _ _ (hV [] k e c (get?_nil _)), subst_node]
    congr 1
    funext i
    rw [trunc_subst (nodup_of_node hn i) xs fun q k' e' c' hq => by
      have := hV (i.1 :: q) k' e' c' (by rw [get?_node_cons_fin]; exact hq)
      exact this]
    refine subst_congr _ fun a ha => ?_
    rw [shift_shift]
    congr 2
    exact (pos_eq hn (by rw [List.singleton_append, get?_node_cons_fin]; exact get?_pos ha)).symm

/-- **A truncated tree is recovered** by substituting the cut subtrees back: the cut subtree at
a leaf `a` of the truncation is a shuffle tree with least leaf `a`, with leaves among those of
the tree. -/
theorem exists_subst_trunc : ∀ {t : STree E}, t.IsShuffle → t.labels.Nodup →
    ∀ V : Set (List ℕ), ∃ zs : ℕ → STree E, (t.trunc V).subst zs = t ∧
      ∀ a ∈ (t.trunc V).labels, (zs a).IsShuffle ∧ (zs a).first = a ∧
        (zs a).labels ≤ t.labels
  | leaf b, _, _, V => ⟨leaf, rfl, fun a ha => by
      rw [trunc_leaf, labels_leaf, Multiset.mem_singleton] at ha
      subst ha
      exact ⟨trivial, rfl, le_rfl⟩⟩
  | @node _ k e c, h, hn, V => by
    by_cases hV : [] ∈ V
    · choose zs hzs hzs' using fun i => exists_subst_trunc (h.child i) (nodup_of_node hn i)
        (shift V [(i : ℕ)])
      classical
      let Z : ℕ → STree E := fun a =>
        if hi : ∃ i, a ∈ ((c i).trunc (shift V [(i : ℕ)])).labels then zs hi.choose a else leaf a
      have hZ : ∀ i, ∀ a ∈ ((c i).trunc (shift V [(i : ℕ)])).labels, Z a = zs i a := by
        intro i a ha
        have hex : ∃ i, a ∈ ((c i).trunc (shift V [(i : ℕ)])).labels := ⟨i, ha⟩
        simp only [Z, dif_pos hex]
        congr 1
        by_contra hne
        exact not_mem_of_node hn hne
          (Multiset.mem_of_le (labels_trunc_le (h.child _) _) hex.choose_spec)
          (Multiset.mem_of_le (labels_trunc_le (h.child _) _) ha)
      refine ⟨Z, ?_, fun a ha => ?_⟩
      · rw [trunc_node_of_mem e c hV, subst_node]
        congr 1
        funext i
        rw [subst_congr _ (hZ i)]
        exact hzs i
      · rw [trunc_node_of_mem e c hV, labels_node] at ha
        obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 ha
        rw [hZ i a hi]
        obtain ⟨h1, h2, h3⟩ := hzs' i a hi
        exact ⟨h1, h2, h3.trans (labels_le_node e c i)⟩
    · refine ⟨fun _ => node e c, ?_, fun a ha => ?_⟩
      · rw [trunc_node_of_not_mem e c hV]
        rfl
      · rw [trunc_node_of_not_mem e c hV, labels_leaf, Multiset.mem_singleton] at ha
        subst ha
        exact ⟨h, rfl, le_rfl⟩

end STree

end Operad
