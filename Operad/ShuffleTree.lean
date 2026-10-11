/-
# Shuffle tree monomials

The free shuffle operad on a set `E` of binary generators has a basis of *shuffle tree monomials*
(Dotsenko–Khoroshkin): planar binary trees with vertices decorated by `E` and distinct leaf
labels, such that at every vertex the least label of the left subtree is smaller than the least
label of the right subtree (`LTree`, `LTree.IsShuffle`). The forgetful functor from symmetric to
shuffle operads makes them a basis of the free symmetric operad on the free `𝔖₂`-module on `E` as
well, which is how they enter Gröbner bases of symmetric operads.

This file has the combinatorics of monomials that quadratic Gröbner bases need.

* **Counting.** The monomials of arity `n` on the labels `0, …, n - 1` (`LTree.monomials`,
  `LTree.mem_monomials`) are obtained by grafting the leaf `n - 1` under a new vertex at any of the
  `2n - 3` positions of a monomial of arity `n - 1` (`graft`, undone by `prune`); so there are
  `(2n - 3)!! |E|ⁿ⁻¹` of them (`card_monomials`).
* **Windows.** The *windows* of a monomial (`LTree.windows`) are its two-vertex submonomials, one
  for each internal edge, with the three input subtrees replaced by leaves and standardized by
  their least labels to `0, 1, 2`. A monomial is divisible by an arity-three monomial exactly when
  one of its windows is that monomial, so it is *normal* for a set `L` of arity-three leading
  monomials when no window lies in `L` (`LTree.IsNormal`).
* **The path-lexicographic key** (`LTree.pathKey`): the words of decorations read from the root to
  the leaves, leaf by leaf in the order of the labels, each word preceded by its length, compared
  lexicographically.
* **Right combs** (`LTree.rightComb`): every internal vertex a right child.

On a shuffle monomial the window of an edge into the first slot is `e (f (0, 1), 2)` or
`e (f (0, 2), 1)` (`window_left_shape`), and the window of an edge into the second slot is the
right comb `e (0, f (1, 2))` (`window_right_eq`). So for a set of leading monomials containing every
window of the first kind, **the normal monomials are the right combs on `0, …, n - 1` whose
consecutive pairs of decorations avoid the right combs in the set** (`isNormal_iff`, from
`isRightCombShape_of_normal`, `labels_sorted_of_rightCombShape` and `windows_rightComb`).
-/
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Action.Defs

universe v

namespace Operad

/-- **A planar binary tree with labelled leaves**, vertices decorated by `E`. -/
inductive LTree (E : Type v) : Type v where
  /-- A leaf with its label. -/
  | leaf (a : ℕ) : LTree E
  /-- A vertex decorated by `e`, with a left and a right subtree. -/
  | node (e : E) (l r : LTree E) : LTree E
  deriving DecidableEq

namespace LTree

variable {E : Type v}

/-- The leaf labels, from left to right. -/
def labels : LTree E → List ℕ
  | leaf a => [a]
  | node _ l r => l.labels ++ r.labels

/-- The least leaf label. -/
def minLabel : LTree E → ℕ
  | leaf a => a
  | node _ l r => min l.minLabel r.minLabel

/-- The number of leaves. -/
def arity : LTree E → ℕ
  | leaf _ => 1
  | node _ l r => l.arity + r.arity

/-- The decorations of the vertices, in preorder. -/
def decorations : LTree E → List E
  | leaf _ => []
  | node e l r => e :: (l.decorations ++ r.decorations)

/-- **The shuffle condition**: at every vertex the least label on the left is smaller than the
least label on the right. -/
def IsShuffle : LTree E → Prop
  | leaf _ => True
  | node _ l r => l.minLabel < r.minLabel ∧ l.IsShuffle ∧ r.IsShuffle

/-- The shuffle condition is decidable, by structural recursion. -/
def decIsShuffle : (t : LTree E) → Decidable t.IsShuffle
  | leaf _ => isTrue trivial
  | node _ l r =>
    @instDecidableAnd _ _ (Nat.decLt _ _) (@instDecidableAnd _ _ (decIsShuffle l) (decIsShuffle r))

instance : DecidablePred (IsShuffle (E := E)) := decIsShuffle

@[simp] lemma labels_leaf (a : ℕ) : (leaf a : LTree E).labels = [a] := rfl
@[simp] lemma labels_node (e : E) (l r : LTree E) :
    (node e l r).labels = l.labels ++ r.labels := rfl
@[simp] lemma minLabel_leaf (a : ℕ) : (leaf a : LTree E).minLabel = a := rfl
@[simp] lemma minLabel_node (e : E) (l r : LTree E) :
    (node e l r).minLabel = min l.minLabel r.minLabel := rfl
@[simp] lemma isShuffle_leaf (a : ℕ) : (leaf a : LTree E).IsShuffle := trivial
@[simp] lemma isShuffle_node (e : E) (l r : LTree E) :
    (node e l r).IsShuffle ↔ l.minLabel < r.minLabel ∧ l.IsShuffle ∧ r.IsShuffle := Iff.rfl

/-- On a shuffle monomial the least label is the least label of the leftmost leaf's subtree:
the left subtree carries it. -/
lemma minLabel_node_of_shuffle {e : E} {l r : LTree E} (h : (node e l r).IsShuffle) :
    (node e l r).minLabel = l.minLabel := by
  simp only [minLabel_node]
  exact min_eq_left h.1.le

/-- The least label is at most every label. -/
lemma minLabel_le_of_mem : ∀ (t : LTree E) {b : ℕ}, b ∈ t.labels → t.minLabel ≤ b
  | leaf a, b, hb => by simp at hb; simp [hb]
  | node e l r, b, hb => by
    simp only [labels_node, List.mem_append] at hb
    rcases hb with hb | hb
    · exact le_trans (min_le_left _ _) (minLabel_le_of_mem l hb)
    · exact le_trans (min_le_right _ _) (minLabel_le_of_mem r hb)

/-- The least label is a label. -/
lemma minLabel_mem : ∀ t : LTree E, t.minLabel ∈ t.labels
  | leaf a => by simp
  | node _ l r => by
    simp only [minLabel_node, labels_node, List.mem_append]
    rcases min_choice l.minLabel r.minLabel with h | h <;> rw [h]
    · exact Or.inl (minLabel_mem l)
    · exact Or.inr (minLabel_mem r)

/-! ## Windows -/

/-- The rank of `x` among three numbers: how many of them are smaller. -/
def rank3 (a b c x : ℕ) : ℕ := (if a < x then 1 else 0) + (if b < x then 1 else 0) +
  (if c < x then 1 else 0)

/-- **The window of an internal edge**: the vertex `e` above the vertex `f`, which sits in the
first slot (`s = false`) or the second (`s = true`); `f` has inputs with least labels `ma`, `mb`,
and `e`'s other input has least label `mo`; the three are standardized to `0, 1, 2`. -/
def window (e f : E) (s : Bool) (ma mb mo : ℕ) : LTree E :=
  if s then
    node e (leaf (rank3 ma mb mo mo)) (node f (leaf (rank3 ma mb mo ma)) (leaf (rank3 ma mb mo mb)))
  else
    node e (node f (leaf (rank3 ma mb mo ma)) (leaf (rank3 ma mb mo mb))) (leaf (rank3 ma mb mo mo))

/-- **The windows of a monomial**: one for each internal edge, top-down. -/
def windows : LTree E → List (LTree E)
  | leaf _ => []
  | node e l r =>
    (match l with
      | leaf _ => []
      | node f a b => [window e f false a.minLabel b.minLabel r.minLabel]) ++
    (match r with
      | leaf _ => []
      | node f a b => [window e f true a.minLabel b.minLabel l.minLabel]) ++
    l.windows ++ r.windows

/-- **Normality** for a set of arity-three leading monomials: no window is a leading monomial. -/
def IsNormal (L : Set (LTree E)) (t : LTree E) : Prop := ∀ w ∈ t.windows, w ∉ L

lemma IsNormal.left {L : Set (LTree E)} {e : E} {l r : LTree E} (h : IsNormal L (node e l r)) :
    IsNormal L l := fun w hw => h w (by
  simp only [windows, List.mem_append]
  exact Or.inl (Or.inr hw))

lemma IsNormal.right {L : Set (LTree E)} {e : E} {l r : LTree E} (h : IsNormal L (node e l r)) :
    IsNormal L r := fun w hw => h w (by
  simp only [windows, List.mem_append]
  exact Or.inr hw)

/-- **A window into the first slot of a shuffle monomial** with distinct labels is
`e (f (0, 1), 2)` or `e (f (0, 2), 1)`. -/
theorem window_left_shape {e f : E} {a b r : LTree E} (h : (node e (node f a b) r).IsShuffle)
    (hnd : (node e (node f a b) r).labels.Nodup) :
    window e f false a.minLabel b.minLabel r.minLabel = node e (node f (leaf 0) (leaf 1)) (leaf 2)
      ∨ window e f false a.minLabel b.minLabel r.minLabel
        = node e (node f (leaf 0) (leaf 2)) (leaf 1) := by
  obtain ⟨h1, ⟨h2, -, -⟩, -⟩ := h
  simp only [minLabel_node] at h1
  have hne : b.minLabel ≠ r.minLabel := by
    simp only [labels_node] at hnd
    exact (List.nodup_append.1 hnd).2.2 _ (List.mem_append.2 (Or.inr (minLabel_mem b))) _
      (minLabel_mem r)
  have e0 : rank3 a.minLabel b.minLabel r.minLabel a.minLabel = 0 := by
    simp only [rank3]
    split_ifs <;> omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · left
    have e1 : rank3 a.minLabel b.minLabel r.minLabel b.minLabel = 1 := by
      simp only [rank3]
      split_ifs <;> omega
    have e2 : rank3 a.minLabel b.minLabel r.minLabel r.minLabel = 2 := by
      simp only [rank3]
      split_ifs <;> omega
    simp only [window, Bool.false_eq_true, ↓reduceIte, e0, e1, e2]
  · right
    have e1 : rank3 a.minLabel b.minLabel r.minLabel b.minLabel = 2 := by
      simp only [rank3]
      split_ifs <;> omega
    have e2 : rank3 a.minLabel b.minLabel r.minLabel r.minLabel = 1 := by
      simp only [rank3]
      split_ifs <;> omega
    simp only [window, Bool.false_eq_true, ↓reduceIte, e0, e1, e2]

/-- **A window into the second slot of a shuffle monomial** is the right comb `e (0, f (1, 2))`. -/
theorem window_right_eq {e f : E} {l a b : LTree E} (h : (node e l (node f a b)).IsShuffle) :
    window e f true a.minLabel b.minLabel l.minLabel
      = node e (leaf 0) (node f (leaf 1) (leaf 2)) := by
  obtain ⟨h1, -, h2, -, -⟩ := h
  simp only [minLabel_node] at h1
  have e0 : rank3 a.minLabel b.minLabel l.minLabel l.minLabel = 0 := by
    simp only [rank3]
    split_ifs <;> omega
  have e1 : rank3 a.minLabel b.minLabel l.minLabel a.minLabel = 1 := by
    simp only [rank3]
    split_ifs <;> omega
  have e2 : rank3 a.minLabel b.minLabel l.minLabel b.minLabel = 2 := by
    simp only [rank3]
    split_ifs <;> omega
  simp only [window, ↓reduceIte, e0, e1, e2]

/-! ## Right combs -/

/-- **The right comb** with decoration word `w`, on the leaves `k, k + 1, …`. -/
def rightComb : List E → ℕ → LTree E
  | [], k => leaf k
  | e :: w, k => node e (leaf k) (rightComb w (k + 1))

/-- A monomial is right-comb-shaped when every internal vertex is a right child. -/
def IsRightCombShape : LTree E → Prop
  | leaf _ => True
  | node _ (leaf _) r => r.IsRightCombShape
  | node _ (node _ _ _) _ => False

/-- **Normal monomials are right combs**, for any set of leading monomials containing every
window of an edge into the first slot. -/
theorem isRightCombShape_of_normal {L : Set (LTree E)}
    (hL : ∀ e f : E, node e (node f (leaf 0) (leaf 1)) (leaf 2) ∈ L ∧
      node e (node f (leaf 0) (leaf 2)) (leaf 1) ∈ L) :
    ∀ t : LTree E, t.IsShuffle → t.labels.Nodup → IsNormal L t → t.IsRightCombShape
  | leaf _, _, _, _ => trivial
  | node e (leaf a) r, hs, hnd, hn =>
    isRightCombShape_of_normal hL r hs.2.2 (List.nodup_append.1 hnd).2.1 hn.right
  | node e (node f a b) r, hs, hnd, hn => by
    have hw : window e f false a.minLabel b.minLabel r.minLabel ∈ L := by
      rcases window_left_shape hs hnd with h | h <;> rw [h]
      · exact (hL e f).1
      · exact (hL e f).2
    refine (hn _ ?_ hw).elim
    simp [windows]

/-- **The labels of a right-comb-shaped shuffle monomial increase** from left to right. -/
theorem labels_sorted_of_rightCombShape :
    ∀ t : LTree E, t.IsShuffle → t.IsRightCombShape → t.labels.Pairwise (· < ·)
  | leaf _, _, _ => List.pairwise_singleton _ _
  | node e (leaf a) r, hs, hr => by
    have ih := labels_sorted_of_rightCombShape r hs.2.2 hr
    simp only [labels_node, labels_leaf, List.singleton_append, List.pairwise_cons]
    exact ⟨fun b hb => lt_of_lt_of_le hs.1 (minLabel_le_of_mem r hb), ih⟩
  | node e (node f a b) r, _, hr => hr.elim

@[simp] lemma length_labels : ∀ t : LTree E, t.labels.length = t.arity
  | leaf _ => rfl
  | node _ l r => by simp [labels, arity, length_labels l, length_labels r]

lemma arity_pos : ∀ t : LTree E, 0 < t.arity
  | leaf _ => Nat.one_pos
  | node _ l _ => Nat.add_pos_left (arity_pos l) _

lemma labels_rightComb : ∀ (w : List E) (k : ℕ),
    (rightComb w k).labels = List.range' k (w.length + 1)
  | [], k => rfl
  | e :: w, k => by
    simp only [rightComb, labels_node, labels_leaf, labels_rightComb w (k + 1),
      List.length_cons, List.singleton_append]
    exact List.range'_succ.symm

lemma decorations_rightComb : ∀ (w : List E) (k : ℕ), (rightComb w k).decorations = w
  | [], _ => rfl
  | e :: w, k => by simp [rightComb, decorations, decorations_rightComb w (k + 1)]

/-- **A right-comb-shaped monomial with consecutive labels is the right comb of its
decorations.** -/
theorem eq_rightComb_of_rightCombShape : ∀ (t : LTree E) (k : ℕ), t.IsRightCombShape →
    t.labels = List.range' k t.arity → t = rightComb t.decorations k
  | leaf a, k, _, hl => by
    simp only [labels_leaf, arity, List.range'_one] at hl
    obtain rfl := List.singleton_injective hl
    rfl
  | node e (leaf a) r, k, hr, hl => by
    have hpos := arity_pos r
    simp only [labels_node, labels_leaf, arity, List.singleton_append] at hl
    rw [show 1 + r.arity = r.arity + 1 by omega, List.range'_succ] at hl
    obtain ⟨rfl, hl'⟩ := List.cons_eq_cons.1 hl
    have ih := eq_rightComb_of_rightCombShape r (a + 1) hr hl'
    simp only [decorations, List.nil_append, rightComb]
    exact congrArg _ ih
  | node e (node f a b) r, _, hr, _ => hr.elim

/-- The least label of a right comb is its first label. -/
lemma minLabel_rightComb : ∀ (w : List E) (k : ℕ), (rightComb w k).minLabel = k
  | [], _ => rfl
  | g :: u, j => by
    simp only [rightComb, minLabel_node, minLabel_leaf, minLabel_rightComb u (j + 1)]
    omega

/-- **The windows of a right comb** are the right combs of the consecutive pairs of its
decoration word. -/
theorem windows_rightComb : ∀ (w : List E) (k : ℕ),
    (rightComb w k).windows
      = (w.zip w.tail).map fun p => node p.1 (leaf 0) (node p.2 (leaf 1) (leaf 2))
  | [], _ => rfl
  | [e], _ => rfl
  | e :: f :: w, k => by
    have hs :
        (node e (leaf k) (node f (leaf (k + 1)) (rightComb w (k + 1 + 1))) :
          LTree E).IsShuffle := by
      refine ⟨?_, trivial, ?_, trivial, isShuffle_rightComb w _⟩
      · simp only [minLabel_leaf, minLabel_node, minLabel_rightComb]
        omega
      · simp only [minLabel_leaf, minLabel_rightComb]
        omega
    show [window e f true (leaf (k + 1) : LTree E).minLabel (rightComb w (k + 1 + 1)).minLabel
        (leaf k : LTree E).minLabel] ++ (rightComb (f :: w) (k + 1)).windows = _
    rw [window_right_eq hs, windows_rightComb (f :: w) (k + 1)]
    rfl
where
  /-- Right combs are shuffle monomials. -/
  isShuffle_rightComb : ∀ (w : List E) (k : ℕ), (rightComb w k).IsShuffle
    | [], _ => trivial
    | g :: u, j => ⟨by simp only [minLabel_leaf, minLabel_rightComb]; omega, trivial,
        isShuffle_rightComb u (j + 1)⟩

/-! ## Normal monomials -/

/-- **The normal monomials** for a set `L` of arity-three leading monomials containing every
window of an edge into the first slot: the right combs on `0, …, n - 1` with no consecutive pair
`(e, f)` of decorations whose right comb `e (0, f (1, 2))` lies in `L`. -/
theorem isNormal_iff {L : Set (LTree E)}
    (hL : ∀ e f : E, node e (node f (leaf 0) (leaf 1)) (leaf 2) ∈ L ∧
      node e (node f (leaf 0) (leaf 2)) (leaf 1) ∈ L)
    {n : ℕ} {t : LTree E} (hs : t.IsShuffle) (hl : t.labels.Perm (List.range n)) :
    IsNormal L t ↔ ∃ w : List E, t = rightComb w 0 ∧
      ∀ p ∈ w.zip w.tail, node p.1 (leaf 0) (node p.2 (leaf 1) (leaf 2)) ∉ L := by
  constructor
  · intro hn
    have hr := isRightCombShape_of_normal hL t hs (hl.nodup_iff.2 List.nodup_range) hn
    have hsorted := labels_sorted_of_rightCombShape t hs hr
    have heq : t.labels = List.range' 0 t.arity := by
      have hlen := hl.length_eq
      rw [length_labels, List.length_range] at hlen
      rw [hlen, ← List.range_eq_range']
      exact List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (hsorted.imp le_of_lt)
        (List.pairwise_lt_range.imp le_of_lt) hl
    refine ⟨t.decorations, eq_rightComb_of_rightCombShape t 0 hr heq, fun p hp hpL => ?_⟩
    refine hn _ ?_ hpL
    rw [eq_rightComb_of_rightCombShape t 0 hr heq, windows_rightComb]
    exact List.mem_map_of_mem hp
  · rintro ⟨w, rfl, hw⟩ x hx
    rw [windows_rightComb] at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact hw p hp

/-! ## The path-lexicographic key -/

/-- The decorations on the path from the root to the leaf labelled `i`. -/
def path (i : ℕ) : LTree E → List E
  | leaf _ => []
  | node e l r => e :: if i ∈ l.labels then l.path i else r.path i

/-- **The path-lexicographic key** of a monomial of arity `n`, for a ranking `rk` of the
decorations: for the leaves in the order of their labels, the length of the path from the root
followed by the ranks along it. Lists of naturals are compared lexicographically, so monomials are
compared by their sequences of paths, each path in degree-lexicographic order: the
path-lexicographic order of Dotsenko and Khoroshkin before its tie-break by the permutation of the
leaves, which separates monomials with the same paths from arity four on. -/
def pathKey (rk : E → ℕ) (n : ℕ) (t : LTree E) : List ℕ :=
  (List.range n).flatMap fun i => (t.path i).length :: (t.path i).map rk

/-! ## Counting shuffle monomials -/

/-- The number of subtrees, the leaves included: the positions in preorder. -/
def size : LTree E → ℕ
  | leaf _ => 1
  | node _ l r => l.size + r.size + 1

@[simp] lemma size_leaf (a : ℕ) : (leaf a : LTree E).size = 1 := rfl
@[simp] lemma size_node (e : E) (l r : LTree E) : (node e l r).size = l.size + r.size + 1 := rfl

lemma size_add_one : ∀ t : LTree E, t.size + 1 = 2 * t.arity
  | leaf _ => rfl
  | node _ l r => by
    have := size_add_one l
    have := size_add_one r
    simp only [size_node, arity]
    omega

/-- **Grafting a new leaf** `a` under a new vertex `e` at the preorder position `p`: the subtree
`s` at that position becomes `node e s (leaf a)`. -/
def graft (e : E) (a : ℕ) : LTree E → ℕ → LTree E
  | t, 0 => node e t (leaf a)
  | leaf b, _ + 1 => leaf b
  | node f l r, p + 1 =>
    if p < l.size then node f (graft e a l p) r else node f l (graft e a r (p - l.size))

@[simp] lemma graft_zero (e : E) (a : ℕ) (t : LTree E) : graft e a t 0 = node e t (leaf a) := by
  cases t <;> rfl

lemma graft_node_succ (e : E) (a : ℕ) (f : E) (l r : LTree E) (p : ℕ) :
    graft e a (node f l r) (p + 1) =
      if p < l.size then node f (graft e a l p) r else node f l (graft e a r (p - l.size)) := rfl

lemma size_graft (e : E) (a : ℕ) : ∀ (t : LTree E) (p : ℕ), p < t.size →
    (graft e a t p).size = t.size + 2
  | t, 0, _ => by simp
  | leaf _, _ + 1, h => by simp at h
  | node f l r, p + 1, h => by
    simp only [size_node] at h
    rw [graft_node_succ]
    split_ifs with hp
    · simp only [size_node, size_graft e a l p hp]
      omega
    · simp only [size_node, size_graft e a r (p - l.size) (by omega)]
      omega

lemma labels_graft (e : E) (a : ℕ) : ∀ (t : LTree E) (p : ℕ), p < t.size →
    (graft e a t p).labels.Perm (t.labels ++ [a])
  | t, 0, _ => by simp
  | leaf _, _ + 1, h => by simp at h
  | node f l r, p + 1, h => by
    simp only [size_node] at h
    rw [graft_node_succ]
    split_ifs with hp
    · simp only [labels_node, List.append_assoc]
      refine ((labels_graft e a l p hp).append_right _).trans ?_
      rw [List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    · simp only [labels_node, List.append_assoc]
      exact (labels_graft e a r _ (by omega)).append_left _

lemma minLabel_graft (e : E) {a : ℕ} : ∀ (t : LTree E) (p : ℕ), (∀ b ∈ t.labels, b < a) →
    p < t.size → (graft e a t p).minLabel = t.minLabel
  | t, 0, ha, _ => by
    simp only [graft_zero, minLabel_node, minLabel_leaf]
    exact min_eq_left (ha _ (minLabel_mem t)).le
  | leaf _, _ + 1, _, h => by simp at h
  | node f l r, p + 1, ha, h => by
    simp only [size_node] at h
    simp only [labels_node, List.mem_append] at ha
    rw [graft_node_succ]
    split_ifs with hp
    · simp only [minLabel_node, minLabel_graft e l p (fun b hb => ha b (Or.inl hb)) hp]
    · simp only [minLabel_node,
        minLabel_graft e r (p - l.size) (fun b hb => ha b (Or.inr hb)) (by omega)]

/-- Grafting a leaf with a label above all the others onto a shuffle monomial gives a shuffle
monomial. -/
lemma isShuffle_graft (e : E) {a : ℕ} : ∀ (t : LTree E) (p : ℕ), t.IsShuffle →
    (∀ b ∈ t.labels, b < a) → p < t.size → (graft e a t p).IsShuffle
  | t, 0, hs, ha, _ => by
    simp only [graft_zero, isShuffle_node, minLabel_leaf, isShuffle_leaf, and_true]
    exact ⟨ha _ (minLabel_mem t), hs⟩
  | leaf _, _ + 1, _, _, h => by simp at h
  | node f l r, p + 1, hs, ha, h => by
    simp only [size_node] at h
    simp only [labels_node, List.mem_append] at ha
    have hal : ∀ b ∈ l.labels, b < a := fun b hb => ha b (Or.inl hb)
    have har : ∀ b ∈ r.labels, b < a := fun b hb => ha b (Or.inr hb)
    obtain ⟨h1, hl, hr⟩ := hs
    rw [graft_node_succ]
    split_ifs with hp
    · exact ⟨by rw [minLabel_graft e l p hal hp]; exact h1, isShuffle_graft e l p hl hal hp, hr⟩
    · exact ⟨by rw [minLabel_graft e r _ har (by omega)]; exact h1, hl,
        isShuffle_graft e r _ hr har (by omega)⟩

lemma graft_eq_node (e : E) (a : ℕ) : ∀ (t : LTree E) (p : ℕ), p < t.size →
    ∃ g x y, graft e a t p = node g x y
  | t, 0, _ => ⟨e, t, leaf a, graft_zero e a t⟩
  | leaf _, _ + 1, h => by simp at h
  | node f l r, p + 1, _ => by
    rw [graft_node_succ]
    split_ifs
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩

/-- **Pruning the leaf** `a`: its parent vertex is removed, and its sibling takes the parent's
place. -/
def prune (a : ℕ) : LTree E → LTree E
  | leaf b => leaf b
  | node f l (leaf b) => if b = a then l else node f (prune a l) (leaf b)
  | node f l (node g x y) =>
    if a ∈ l.labels then node f (prune a l) (node g x y) else node f l (prune a (node g x y))

/-- **Pruning undoes grafting.** -/
lemma prune_graft (e : E) {a : ℕ} : ∀ (t : LTree E) (p : ℕ), a ∉ t.labels → p < t.size →
    prune a (graft e a t p) = t
  | t, 0, _, _ => by simp [prune]
  | leaf _, _ + 1, _, h => by simp at h
  | node f l r, p + 1, ha, h => by
    simp only [size_node] at h
    simp only [labels_node, List.mem_append, not_or] at ha
    rw [graft_node_succ]
    split_ifs with hp
    · have ih := prune_graft e l p ha.1 hp
      have hmem : a ∈ (graft e a l p).labels := (labels_graft e a l p hp).mem_iff.2 (by simp)
      cases r with
      | leaf b =>
        have hb : b ≠ a := fun hb => ha.2 (by simp [hb])
        simp [prune, hb, ih]
      | node g x y => simp [prune, hmem, ih]
    · have hq : p - l.size < r.size := by omega
      have ih := prune_graft e r _ ha.2 hq
      obtain ⟨g, x, y, hg⟩ := graft_eq_node e a r _ hq
      rw [hg] at ih ⊢
      simp [prune, ha.1, ih]

lemma graft_zero_ne (e e' : E) {a : ℕ} : ∀ {t : LTree E} {p : ℕ}, a ∉ t.labels →
    p + 1 < t.size → graft e a t 0 ≠ graft e' a t (p + 1)
  | leaf _, _, _, h => by simp at h
  | node f l r, p, ha, h => by
    simp only [size_node] at h
    simp only [labels_node, List.mem_append, not_or] at ha
    rw [graft_zero, graft_node_succ]
    split_ifs with hp
    · intro he
      simp only [node.injEq] at he
      obtain ⟨-, -, rfl⟩ := he
      exact ha.2 (by simp)
    · intro he
      simp only [node.injEq] at he
      have := congrArg size he.2.2
      rw [size_graft e' a r _ (by omega)] at this
      simp at this

/-- **Grafting at different positions, or with different decorations, gives different
monomials.** -/
theorem graft_inj {e e' : E} {a : ℕ} : ∀ (t : LTree E) (p p' : ℕ), a ∉ t.labels → p < t.size →
    p' < t.size → graft e a t p = graft e' a t p' → p = p' ∧ e = e'
  | t, 0, 0, _, _, _, h => by
    simp only [graft_zero, node.injEq] at h
    exact ⟨rfl, h.1⟩
  | _, 0, _ + 1, ha, _, hp', h => absurd h (graft_zero_ne e e' ha hp')
  | _, _ + 1, 0, ha, hp, _, h => absurd h.symm (graft_zero_ne e' e ha hp)
  | leaf _, _ + 1, _ + 1, _, hp, _, _ => by simp at hp
  | node f l r, p + 1, p' + 1, ha, hp, hp', h => by
    simp only [size_node] at hp hp'
    simp only [labels_node, List.mem_append, not_or] at ha
    rw [graft_node_succ, graft_node_succ] at h
    split_ifs at h with h1 h2 h2
    · simp only [node.injEq, true_and, and_true] at h
      obtain ⟨rfl, rfl⟩ := graft_inj l p p' ha.1 h1 h2 h
      exact ⟨rfl, rfl⟩
    · simp only [node.injEq, true_and] at h
      have := congrArg size h.1
      rw [size_graft e a l p h1] at this
      omega
    · simp only [node.injEq, true_and] at h
      have := congrArg size h.1
      rw [size_graft e' a l p' h2] at this
      omega
    · simp only [node.injEq, true_and] at h
      obtain ⟨h3, rfl⟩ := graft_inj r _ _ ha.2 (by omega) (by omega) h
      exact ⟨by omega, rfl⟩

/-- **Every shuffle monomial with at least two leaves is grafted** from one on fewer leaves, at
its largest label `a`. -/
theorem exists_graft {a : ℕ} : ∀ (t : LTree E), t.IsShuffle → t.labels.Nodup → a ∈ t.labels →
    (∀ b ∈ t.labels, b ≤ a) → 2 ≤ t.arity →
    ∃ (s : LTree E) (p : ℕ) (e : E), p < s.size ∧ s.IsShuffle ∧ (∀ b ∈ s.labels, b < a) ∧
      graft e a s p = t
  | leaf _, _, _, _, _, h2 => absurd h2 (by simp [arity])
  | node f l r, hs, hnd, ha, hle, _ => by
    obtain ⟨h1, hsl, hsr⟩ := hs
    simp only [labels_node, List.mem_append] at ha hle
    have hnd' := List.nodup_append.1 hnd
    by_cases hr : r = leaf a
    · subst hr
      refine ⟨l, 0, f, by have := size_add_one l; omega, hsl, fun b hb => ?_, graft_zero f a l⟩
      have hba : b ≠ a := fun hba => hnd'.2.2 b hb a (by simp) hba
      exact lt_of_le_of_ne (hle b (Or.inl hb)) hba
    by_cases hal : a ∈ l.labels
    · cases l with
      | leaf c =>
        exfalso
        have hc : c = a := (by simpa using hal : a = c).symm
        subst hc
        have := hle _ (Or.inr (minLabel_mem r))
        simp only [minLabel_leaf] at h1
        omega
      | node g x y =>
        have h2 : 2 ≤ (node g x y).arity := by
          have := arity_pos x
          have := arity_pos y
          simp only [arity]
          omega
        obtain ⟨s, p, e, hp, hs, hsa, hg⟩ := exists_graft (node g x y) hsl hnd'.1 hal
          (fun b hb => hle b (Or.inl hb)) h2
        have hra : ∀ b ∈ r.labels, b < a := fun b hb => lt_of_le_of_ne (hle b (Or.inr hb))
          fun hba => hnd'.2.2 a hal b hb hba.symm
        refine ⟨node f s r, p + 1, e, by simp only [size_node]; omega,
          ⟨?_, hs, hsr⟩, ?_, ?_⟩
        · rw [← minLabel_graft e s p hsa hp, hg]
          exact h1
        · intro b hb
          simp only [labels_node, List.mem_append] at hb
          exact hb.elim (hsa b) (hra b)
        · rw [graft_node_succ, if_pos hp, hg]
    · have har : a ∈ r.labels := ha.resolve_left hal
      cases r with
      | leaf c =>
        exfalso
        have hc : c = a := (by simpa using har : a = c).symm
        exact hr (by rw [hc])
      | node g x y =>
        have h2 : 2 ≤ (node g x y).arity := by
          have := arity_pos x
          have := arity_pos y
          simp only [arity]
          omega
        obtain ⟨s, p, e, hp, hs, hsa, hg⟩ := exists_graft (node g x y) hsr hnd'.2.1 har
          (fun b hb => hle b (Or.inr hb)) h2
        have hla : ∀ b ∈ l.labels, b < a := fun b hb => lt_of_le_of_ne (hle b (Or.inl hb))
          fun hba => hal (hba ▸ hb)
        refine ⟨node f l s, l.size + p + 1, e, by simp only [size_node]; omega,
          ⟨?_, hsl, hs⟩, ?_, ?_⟩
        · rw [← minLabel_graft e s p hsa hp, hg]
          exact h1
        · intro b hb
          simp only [labels_node, List.mem_append] at hb
          exact hb.elim (hla b) (hsa b)
        · rw [graft_node_succ, if_neg (by omega), show l.size + p - l.size = p by omega, hg]

lemma size_of_perm {t : LTree E} {n : ℕ} (h : t.labels.Perm (List.range (n + 1))) :
    t.size = 2 * n + 1 := by
  have h1 := size_add_one t
  have h2 := h.length_eq
  rw [length_labels, List.length_range] at h2
  omega

section Monomials

open scoped Nat

variable [Fintype E] [DecidableEq E]

/-- **The shuffle monomials of arity `n`**, on the leaves `0, …, n - 1`: the leaf `n - 1` grafted
onto those of arity `n - 1`, in each of the `2n - 3` positions and with each decoration. -/
def monomials : ℕ → Finset (LTree E)
  | 0 => ∅
  | 1 => {leaf 0}
  | n + 2 => (monomials (n + 1)).biUnion fun s =>
      (Finset.range (2 * n + 1) ×ˢ (Finset.univ : Finset E)).image
        fun pe => graft pe.2 (n + 1) s pe.1

/-- **The monomials of arity `n` are the shuffle monomials** whose labels are `0, …, n - 1`. -/
theorem mem_monomials : ∀ (n : ℕ) (t : LTree E),
    t ∈ monomials n ↔ t.IsShuffle ∧ t.labels.Perm (List.range n)
  | 0, t => by
    simp only [monomials, Finset.notMem_empty, false_iff, not_and, List.range_zero,
      List.perm_nil]
    intro _ h
    have h1 := length_labels t
    have h2 := arity_pos t
    rw [h, List.length_nil] at h1
    omega
  | 1, t => by
    simp only [monomials, Finset.mem_singleton, List.range_one, List.perm_singleton]
    constructor
    · rintro rfl
      exact ⟨trivial, rfl⟩
    · rintro ⟨-, h⟩
      cases t with
      | leaf b => simpa using h
      | node f l r =>
        have h1 := length_labels (node f l r)
        have := arity_pos l
        have := arity_pos r
        rw [h] at h1
        simp only [List.length_singleton, arity] at h1
        omega
  | n + 2, t => by
    simp only [monomials, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product,
      Finset.mem_range, Finset.mem_univ, and_true, Prod.exists, mem_monomials (n + 1)]
    constructor
    · rintro ⟨s, ⟨hs, hsl⟩, p, e, hp, rfl⟩
      have hsize := size_of_perm hsl
      have hlt : ∀ b ∈ s.labels, b < n + 1 := fun b hb => List.mem_range.1 (hsl.subset hb)
      refine ⟨isShuffle_graft e s p hs hlt (by omega), ?_⟩
      refine (labels_graft e (n + 1) s p (by omega)).trans ?_
      rw [List.range_succ]
      exact hsl.append_right _
    · rintro ⟨hs, hl⟩
      have hlen := hl.length_eq
      rw [length_labels, List.length_range] at hlen
      obtain ⟨s, p, e, hp, hss, hsa, rfl⟩ := exists_graft (a := n + 1) t hs
        (hl.nodup_iff.2 List.nodup_range) (hl.mem_iff.2 (by simp))
        (fun b hb => by have := List.mem_range.1 (hl.subset hb); omega) (by omega)
      have hsl : s.labels.Perm (List.range (n + 1)) := by
        have h1 := labels_graft e (n + 1) s p hp
        rw [List.range_succ] at hl
        exact (List.perm_append_right_iff _).1 (h1.symm.trans hl)
      exact ⟨s, ⟨hss, hsl⟩, p, e, by rw [size_of_perm hsl] at hp; exact hp, rfl⟩

lemma doubleFactorial_two_mul_add_one (n : ℕ) : (2 * n + 1)‼ = (2 * n + 1) * (2 * n - 1)‼ := by
  rcases n with _ | n
  · rfl
  · rw [show 2 * (n + 1) + 1 = (2 * (n + 1) - 1) + 2 by omega, Nat.doubleFactorial_add_two]

/-- **There are `(2n - 3)!! |E|ⁿ⁻¹` shuffle monomials of arity `n`**: the free shuffle operad on
binary generators `E` has dimension `(2n - 3)!! |E|ⁿ⁻¹` in arity `n`. -/
theorem card_monomials : ∀ n : ℕ,
    (monomials (E := E) (n + 1)).card = (2 * n - 1)‼ * Fintype.card E ^ n
  | 0 => by simp [monomials]
  | n + 1 => by
    show ((monomials (E := E) (n + 1)).biUnion _).card = _
    rw [Finset.card_biUnion]
    · have hc : ∀ s ∈ monomials (E := E) (n + 1),
          ((Finset.range (2 * n + 1) ×ˢ (Finset.univ : Finset E)).image
            fun pe : ℕ × E => graft pe.2 (n + 1) s pe.1).card = (2 * n + 1) * Fintype.card E := by
        intro s hs
        obtain ⟨-, hsl⟩ := (mem_monomials (n + 1) s).1 hs
        have hsize := size_of_perm hsl
        have hna : n + 1 ∉ s.labels := fun h => by simpa using hsl.subset h
        rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_range, Finset.card_univ]
        rintro ⟨p, e⟩ hpe ⟨p', e'⟩ hpe' h
        simp only [Finset.coe_product, Finset.coe_range, Finset.coe_univ, Set.mem_prod,
          Set.mem_Iio, Set.mem_univ, and_true] at hpe hpe'
        obtain ⟨rfl, rfl⟩ := graft_inj s p p' hna (by omega) (by omega) h
        rfl
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, card_monomials n,
        show 2 * (n + 1) - 1 = 2 * n + 1 by omega, doubleFactorial_two_mul_add_one]
      ring
    · intro s hs s' hs' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro t ht ht'
      simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
        and_true, Prod.exists] at ht ht'
      obtain ⟨p, e, hp, rfl⟩ := ht
      obtain ⟨p', e', hp', h⟩ := ht'
      obtain ⟨-, hsl⟩ := (mem_monomials (n + 1) s).1 hs
      obtain ⟨-, hsl'⟩ := (mem_monomials (n + 1) s').1 hs'
      have hna : n + 1 ∉ s.labels := fun h => by simpa using hsl.subset h
      have hna' : n + 1 ∉ s'.labels := fun h => by simpa using hsl'.subset h
      apply hne
      rw [← prune_graft e s p hna (by rw [size_of_perm hsl]; omega),
        ← prune_graft e' s' p' hna' (by rw [size_of_perm hsl']; omega), h]

end Monomials

end LTree

end Operad
