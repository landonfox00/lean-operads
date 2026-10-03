/-
# Merging along an edge of a planar tree

A **merge function** on generators composes a generator `e` of arity `k` with a generator `e'`
of arity `l` at the input `j`, as a generator of a given arity `m`, meaningful when
`m + 1 = k + l` (`MergeFn`). **Merge-grafting** `s.mgraft μ p u` grafts `u` at the leaf `p` of
`s` and merges the root of `u` into the vertex of `s` carrying that leaf: its children are those
of the vertex, the leaf `p` replaced by the children of the root of `u`, and its label the merge
of the two labels (`Tree.mgraft`). Contracting the edge of a tree at a cut `t = s.graft p u` is
merge-grafting `s.mgraft μ p u`.

* Forests as lists of trees (`Forest.toList`, `Forest.ofList`).
* Merge-grafting a leaf changes nothing (`Tree.mgraft_leaf_right`), merge-grafting into a leaf is
  grafting (`Tree.mgraft_leaf`), and merge-grafting has the arity of grafting
  (`Tree.arity_mgraft`).
-/
import Operad.TreeRelabel

universe v

namespace Operad

/-! ## Forests as lists -/

namespace Forest

variable {E : ℕ → Type v}

/-- The trees of a forest, as a list. -/
def toList : ∀ {k : ℕ}, Forest E k → List (Tree E)
  | _, .nil => []
  | _, .cons t f => t :: f.toList

/-- A list of trees, as a forest. -/
def ofList : (L : List (Tree E)) → Forest E L.length
  | [] => .nil
  | t :: L => .cons t (ofList L)

@[simp] lemma toList_nil : (Forest.nil : Forest E 0).toList = [] := rfl

@[simp] lemma toList_cons {k : ℕ} (t : Tree E) (f : Forest E k) :
    (Forest.cons t f).toList = t :: f.toList := rfl

@[simp] lemma length_toList : ∀ {k : ℕ} (f : Forest E k), f.toList.length = k
  | _, .nil => rfl
  | _, .cons _ f => by simp [length_toList f]

@[simp] lemma toList_ofList : ∀ L : List (Tree E), (ofList L).toList = L
  | [] => rfl
  | t :: L => by simp [ofList, toList_ofList L]

lemma arityF_eq_sum : ∀ {k : ℕ} (f : Forest E k), f.arityF = (f.toList.map Tree.arity).sum
  | _, .nil => rfl
  | _, .cons t f => by simp [arityF_eq_sum f]

lemma arityF_ofList (L : List (Tree E)) : (ofList L).arityF = (L.map Tree.arity).sum := by
  rw [arityF_eq_sum, toList_ofList]

end Forest

/-! ## Merge-grafting -/

/-- **A merge function** on generators: composing `e` of arity `k` with `e'` of arity `l` at the
input `j`, as a generator of arity `m`, meaningful when `m + 1 = k + l`. -/
abbrev MergeFn (E : ℕ → Type v) : Type v := ∀ k l : ℕ, E k → ℕ → E l → (m : ℕ) → E m

namespace Forest

variable {E : ℕ → Type v}

/-- Appending two forests. -/
def append : ∀ {k l : ℕ}, Forest E l → Forest E k → Forest E (k + l)
  | _, _, .nil, f => f
  | _, _, .cons t g, f => .cons t (append g f)

/-- The number of trees of a forest of `k` trees, its tree `j` replaced by `l` trees. -/
def spliceLen : ℕ → ℕ → ℕ → ℕ
  | 0, _, l => l
  | k + 1, 0, l => k + l
  | k + 1, j + 1, l => spliceLen k j l + 1

/-- **Splicing**: the forest `f`, its tree `j` replaced by the trees of the forest `g`. -/
def splice : ∀ {k l : ℕ}, Forest E k → (j : ℕ) → Forest E l → Forest E (spliceLen k j l)
  | _, _, .nil, _, g => g
  | _, _, .cons _ f, 0, g => append g f
  | _, _, .cons t f, j + 1, g => .cons t (splice f j g)

/-- The index of the tree of a forest holding a leaf. -/
def childIdx : ∀ {k : ℕ}, Forest E k → ℕ → ℕ
  | _, .nil, _ => 0
  | _, .cons t f, p => if p < t.arity then 0 else f.childIdx (p - t.arity) + 1

end Forest

namespace Tree

variable {E : ℕ → Type v} (μ : MergeFn E)

/-- Whether a tree is the trivial tree. -/
def isLeaf : Tree E → Bool
  | .leaf => true
  | .node _ _ => false

@[simp] lemma isLeaf_leaf : (Tree.leaf : Tree E).isLeaf = true := rfl

@[simp] lemma isLeaf_node {k : ℕ} (e : E k) (f : Forest E k) : (Tree.node e f).isLeaf = false :=
  rfl

/-- Whether the leaf `p` of a forest is one of its trees. -/
def _root_.Operad.Forest.isDirect : ∀ {k : ℕ}, Forest E k → ℕ → Bool
  | _, .nil, _ => false
  | _, .cons t f, p => if p < t.arity then t.isLeaf else f.isDirect (p - t.arity)

/-- **The merge at the root**: the vertex `e` with forest `f`, its child `j` being a vertex `e'`
with forest `g`, merged. -/
def mergeRoot {k l : ℕ} (e : E k) (f : Forest E k) (j : ℕ) (e' : E l) (g : Forest E l) :
    Tree E :=
  .node (μ k l e j e' (Forest.spliceLen k j l)) (f.splice j g)

mutual

/-- **Merge-grafting**: graft `u` at the leaf `p` of `s`, and merge the root of `u` into the
vertex of `s` carrying that leaf. -/
def mgraft : Tree E → ℕ → Tree E → Tree E
  | .leaf, _, u => u
  | .node e f, p, u =>
    if f.isDirect p then
      (match u with
        | .leaf => .node e f
        | .node e' g => mergeRoot μ e f (f.childIdx p) e' g)
    else .node e (Forest.mgraftF f p u)

/-- Merge-grafting into the tree of a forest holding the leaf. -/
def _root_.Operad.Forest.mgraftF : ∀ {k : ℕ}, Forest E k → ℕ → Tree E → Forest E k
  | _, .nil, _, _ => .nil
  | _, .cons t f, p, u =>
    if p < t.arity then .cons (mgraft t p u) f else .cons t (Forest.mgraftF f (p - t.arity) u)

end

@[simp] lemma mgraft_leaf (p : ℕ) (u : Tree E) : (Tree.leaf : Tree E).mgraft μ p u = u := rfl

lemma mgraft_node {k : ℕ} (e : E k) (f : Forest E k) (p : ℕ) (u : Tree E) :
    (Tree.node e f).mgraft μ p u = if f.isDirect p then
      (match u with
        | .leaf => .node e f
        | .node e' g => mergeRoot μ e f (f.childIdx p) e' g)
      else .node e (f.mgraftF μ p u) := rfl

lemma isDirect_cons_of_lt {k : ℕ} {t : Tree E} {f : Forest E k} {p : ℕ} (h : p < t.arity) :
    (Forest.cons t f).isDirect p = t.isLeaf := by
  rw [Forest.isDirect, if_pos h]

lemma isDirect_cons_of_ge {k : ℕ} {t : Tree E} {f : Forest E k} {p : ℕ} (h : t.arity ≤ p) :
    (Forest.cons t f).isDirect p = f.isDirect (p - t.arity) := by
  rw [Forest.isDirect, if_neg (by omega)]

lemma childIdx_cons_of_lt {k : ℕ} {t : Tree E} {f : Forest E k} {p : ℕ} (h : p < t.arity) :
    (Forest.cons t f).childIdx p = 0 := by
  rw [Forest.childIdx, if_pos h]

lemma childIdx_cons_of_ge {k : ℕ} {t : Tree E} {f : Forest E k} {p : ℕ} (h : t.arity ≤ p) :
    (Forest.cons t f).childIdx p = f.childIdx (p - t.arity) + 1 := by
  rw [Forest.childIdx, if_neg (by omega)]

/-! ## Splicing and grafting -/

/-- The number of leaves of the first `j` trees of a forest. -/
def _root_.Operad.Forest.offset : ∀ {k : ℕ}, Forest E k → ℕ → ℕ
  | _, .nil, _ => 0
  | _, .cons _ _, 0 => 0
  | _, .cons t f, j + 1 => t.arity + f.offset j

/-- The tree of index `j` of a forest. -/
def _root_.Operad.Forest.get : ∀ {k : ℕ}, Forest E k → ℕ → Tree E
  | _, .nil, _ => .leaf
  | _, .cons t _, 0 => t
  | _, .cons _ f, j + 1 => f.get j

@[simp] lemma append_nil {k : ℕ} (f : Forest E k) : Forest.append .nil f = f := rfl

@[simp] lemma append_cons {k l : ℕ} (t : Tree E) (g : Forest E l) (f : Forest E k) :
    Forest.append (.cons t g) f = .cons t (Forest.append g f) := rfl

lemma arityF_append : ∀ {k l : ℕ} (g : Forest E l) (f : Forest E k),
    (Forest.append g f).arityF = g.arityF + f.arityF
  | _, _, .nil, f => by simp
  | _, _, .cons t g, f => by simp [arityF_append g f, Nat.add_assoc]

lemma weightF_append : ∀ {k l : ℕ} (g : Forest E l) (f : Forest E k),
    (Forest.append g f).weightF = g.weightF + f.weightF
  | _, _, .nil, f => by simp
  | _, _, .cons t g, f => by simp [weightF_append g f, Nat.add_assoc]

/-- Grafting into the first part of an appended forest. -/
lemma graftF_append_left : ∀ {k l : ℕ} (g : Forest E l) (f : Forest E k) (q : ℕ) (b : Tree E),
    q < g.arityF → (Forest.append g f).graftF q b = Forest.append (g.graftF q b) f
  | _, _, .nil, _, _, _, h => by simp at h
  | _, _, .cons t g, f, q, b, h => by
    simp only [arityF_cons] at h
    by_cases hq : q < t.arity
    · rw [append_cons, graftF_cons_of_lt _ hq, graftF_cons_of_lt _ hq, append_cons]
    · rw [append_cons, graftF_cons_of_ge _ (by omega), graftF_cons_of_ge _ (by omega),
        append_cons, graftF_append_left g f _ b (by omega)]

/-- Grafting into the second part of an appended forest. -/
lemma graftF_append_right : ∀ {k l : ℕ} (g : Forest E l) (f : Forest E k) (q : ℕ) (b : Tree E),
    (Forest.append g f).graftF (g.arityF + q) b = Forest.append g (f.graftF q b)
  | _, _, .nil, _, _, _ => by simp
  | _, _, .cons t g, f, q, b => by
    rw [append_cons, arityF_cons, graftF_cons_of_ge _ (by omega), append_cons,
      show t.arity + g.arityF + q - t.arity = g.arityF + q by omega, graftF_append_right g f q b]

lemma arityF_splice : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l), j < k →
    (f.splice j g).arityF + (f.get j).arity = f.arityF + g.arityF
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons t f, 0, g, _ => by
    show (Forest.append g f).arityF + t.arity = (Forest.cons t f).arityF + g.arityF
    rw [arityF_append, arityF_cons]
    omega
  | _, _, .cons t f, j + 1, g, h => by
    show (Forest.cons t (f.splice j g)).arityF + (f.get j).arity
      = (Forest.cons t f).arityF + g.arityF
    rw [arityF_cons, arityF_cons]
    have := arityF_splice f j g (by omega)
    omega

lemma weightF_splice : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l), j < k →
    (f.splice j g).weightF + (f.get j).weight = f.weightF + g.weightF
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons t f, 0, g, _ => by
    show (Forest.append g f).weightF + t.weight = (Forest.cons t f).weightF + g.weightF
    rw [weightF_append, weightF_cons]
    omega
  | _, _, .cons t f, j + 1, g, h => by
    show (Forest.cons t (f.splice j g)).weightF + (f.get j).weight
      = (Forest.cons t f).weightF + g.weightF
    rw [weightF_cons, weightF_cons]
    have := weightF_splice f j g (by omega)
    omega

/-- **Grafting into the spliced trees.** -/
lemma graftF_splice_mid : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l) (q : ℕ)
    (b : Tree E), j < k → q < g.arityF →
    (f.splice j g).graftF (f.offset j + q) b = f.splice j (g.graftF q b)
  | _, _, .nil, _, _, _, _, h, _ => by simp at h
  | _, _, .cons t f, 0, g, q, b, _, hq => by
    show (Forest.append g f).graftF (0 + q) b = Forest.append (g.graftF q b) f
    rw [Nat.zero_add]
    exact graftF_append_left g f q b hq
  | _, _, .cons t f, j + 1, g, q, b, h, hq => by
    show (Forest.cons t (f.splice j g)).graftF (t.arity + f.offset j + q) b
      = Forest.cons t (f.splice j (g.graftF q b))
    rw [graftF_cons_of_ge _ (by omega), show t.arity + f.offset j + q - t.arity
      = f.offset j + q by omega, graftF_splice_mid f j g q b (by omega) hq]

/-- The leaf of a forest held by one of its trees, as an offset. -/
lemma offset_childIdx_le : ∀ {k : ℕ} (f : Forest E k) (p : ℕ), p < f.arityF →
    f.offset (f.childIdx p) ≤ p ∧ p < f.offset (f.childIdx p) + (f.get (f.childIdx p)).arity ∧
      f.childIdx p < k
  | _, .nil, _, h => by simp at h
  | _, .cons t f, p, h => by
    simp only [arityF_cons] at h
    by_cases hp : p < t.arity
    · simp [Forest.childIdx, hp, Forest.offset, Forest.get]
    · have ih := offset_childIdx_le f (p - t.arity) (by omega)
      simp only [Forest.childIdx, hp, if_false, Forest.offset, Forest.get]
      omega

/-- A direct leaf is a leaf of the forest. -/
lemma isLeaf_get_of_isDirect : ∀ {k : ℕ} (f : Forest E k) (p : ℕ), p < f.arityF →
    f.isDirect p = true → (f.get (f.childIdx p)).isLeaf = true
  | _, .nil, _, _, h => by simp [Forest.isDirect] at h
  | _, .cons t f, p, hp, h => by
    simp only [arityF_cons] at hp
    by_cases hlt : p < t.arity
    · simp only [Forest.isDirect, hlt, if_true] at h
      simp [Forest.childIdx, hlt, Forest.get, h]
    · simp only [Forest.isDirect, hlt, if_false] at h
      simp only [Forest.childIdx, hlt, if_false, Forest.get]
      exact isLeaf_get_of_isDirect f (p - t.arity) (by omega) h

lemma eq_leaf_of_isLeaf {t : Tree E} (h : t.isLeaf = true) : t = .leaf := by
  cases t with
  | leaf => rfl
  | node e f => simp at h

/-- **The offset of a direct leaf is its position.** -/
lemma offset_childIdx_of_isDirect {k : ℕ} (f : Forest E k) (p : ℕ) (hp : p < f.arityF)
    (h : f.isDirect p = true) : f.offset (f.childIdx p) = p := by
  have h1 := offset_childIdx_le f p hp
  rw [eq_leaf_of_isLeaf (isLeaf_get_of_isDirect f p hp h), arity_leaf] at h1
  omega

/-! ## Arity and weight of merge-grafts -/

mutual

/-- **Merge-grafting has the arity of grafting.** -/
theorem arity_mgraft : ∀ (s : Tree E) (p : ℕ) (u : Tree E), p < s.arity →
    (s.mgraft μ p u).arity + 1 = s.arity + u.arity
  | .leaf, _, u, _ => by simp; omega
  | .node e f, p, u, h => by
    rw [mgraft_node]
    split_ifs with hd
    · cases u with
      | leaf => simp
      | node e' g =>
        simp only [mergeRoot, arity_node]
        have h1 := arityF_splice f (f.childIdx p) g (offset_childIdx_le f p h).2.2
        rw [eq_leaf_of_isLeaf (isLeaf_get_of_isDirect f p h hd), arity_leaf] at h1
        omega
    · simp only [arity_node]
      exact Forest.arityF_mgraftF f p u h

/-- The forest half of `arity_mgraft`. -/
theorem _root_.Operad.Forest.arityF_mgraftF : ∀ {k : ℕ} (f : Forest E k) (p : ℕ) (u : Tree E),
    p < f.arityF → (f.mgraftF μ p u).arityF + 1 = f.arityF + u.arity
  | _, .nil, _, _, h => by simp at h
  | _, .cons t f, p, u, h => by
    simp only [arityF_cons] at h
    simp only [Forest.mgraftF]
    split_ifs with hp
    · simp only [arityF_cons]
      have := arity_mgraft t p u hp
      omega
    · simp only [arityF_cons]
      have := Forest.arityF_mgraftF f (p - t.arity) u (by omega)
      omega

end

mutual

/-- **Merge-grafting merges two vertices.** -/
theorem weight_mgraft : ∀ (s : Tree E) (p : ℕ) (u : Tree E), p < s.arity →
    s.isLeaf = false → u.isLeaf = false → (s.mgraft μ p u).weight + 1 = s.weight + u.weight
  | .leaf, _, _, _, hs, _ => by simp at hs
  | .node e f, p, u, h, _, hu => by
    rw [mgraft_node]
    split_ifs with hd
    · cases u with
      | leaf => simp at hu
      | node e' g =>
        simp only [mergeRoot, weight_node]
        have h1 := weightF_splice f (f.childIdx p) g (offset_childIdx_le f p h).2.2
        rw [eq_leaf_of_isLeaf (isLeaf_get_of_isDirect f p h hd), weight_leaf] at h1
        omega
    · simp only [weight_node]
      have := Forest.weightF_mgraftF f p u h hd hu
      omega

/-- The forest half of `weight_mgraft`. -/
theorem _root_.Operad.Forest.weightF_mgraftF : ∀ {k : ℕ} (f : Forest E k) (p : ℕ) (u : Tree E),
    p < f.arityF → ¬ f.isDirect p = true → u.isLeaf = false →
    (f.mgraftF μ p u).weightF + 1 = f.weightF + u.weight
  | _, .nil, _, _, h, _, _ => by simp at h
  | _, .cons t f, p, u, h, hd, hu => by
    simp only [arityF_cons] at h
    simp only [Forest.mgraftF]
    split_ifs with hp
    · simp only [Forest.isDirect, hp, if_true] at hd
      simp only [weightF_cons]
      have := weight_mgraft t p u hp (by simpa using hd) hu
      omega
    · simp only [Forest.isDirect, hp, if_false] at hd
      simp only [weightF_cons]
      have := Forest.weightF_mgraftF f (p - t.arity) u (by omega) hd hu
      omega

end

mutual

/-- **Merge-grafting the trivial tree changes nothing.** -/
theorem mgraft_leaf_right : ∀ (s : Tree E) (p : ℕ), p < s.arity → s.mgraft μ p .leaf = s
  | .leaf, _, _ => rfl
  | .node e f, p, h => by
    rw [mgraft_node]
    split_ifs
    · rfl
    · rw [Forest.mgraftF_leaf_right f p h]

/-- The forest half of `mgraft_leaf_right`. -/
theorem _root_.Operad.Forest.mgraftF_leaf_right : ∀ {k : ℕ} (f : Forest E k) (p : ℕ),
    p < f.arityF → f.mgraftF μ p .leaf = f
  | _, .nil, _, _ => rfl
  | _, .cons t f, p, h => by
    simp only [arityF_cons] at h
    simp only [Forest.mgraftF]
    split_ifs with hp
    · rw [mgraft_leaf_right t p hp]
    · rw [Forest.mgraftF_leaf_right f (p - t.arity) (by omega)]

end

lemma isLeaf_graft {t : Tree E} {q : ℕ} {b : Tree E} (hb : b.isLeaf = false) :
    (t.graft q b).isLeaf = false := by
  cases t with
  | leaf => simpa using hb
  | node e f => rfl

/-- A leaf of a grafted non-trivial tree is not direct. -/
lemma isDirect_graftF_mid : ∀ {k : ℕ} (f : Forest E k) (q r : ℕ) (b : Tree E), q < f.arityF →
    r < b.arity → b.isLeaf = false → (f.graftF q b).isDirect (q + r) = false
  | _, .nil, _, _, _, h, _, _ => by simp at h
  | _, .cons t f, q, r, b, h, hr, hb => by
    simp only [arityF_cons] at h
    by_cases hq : q < t.arity
    · have : q + r < (t.graft q b).arity := by rw [arity_graft t q b hq]; omega
      rw [graftF_cons_of_lt _ hq, Forest.isDirect, if_pos this, isLeaf_graft hb]
    · rw [graftF_cons_of_ge _ (by omega), Forest.isDirect, if_neg (by omega),
        show q + r - t.arity = (q - t.arity) + r by omega]
      exact isDirect_graftF_mid f (q - t.arity) r b (by omega) hr hb

mutual

/-- **Merge-grafting into a grafted tree**: the merge happens in the grafted tree. -/
theorem mgraft_graft_inner : ∀ (s : Tree E) (q : ℕ) (b : Tree E) (r : ℕ) (u : Tree E),
    q < s.arity → r < b.arity → b.isLeaf = false →
    (s.graft q b).mgraft μ (q + r) u = s.graft q (b.mgraft μ r u)
  | .leaf, q, b, r, u, h, _, _ => by
    obtain rfl : q = 0 := by simpa using h
    simp
  | .node e f, q, b, r, u, h, hr, hb => by
    rw [graft_node, mgraft_node, if_neg (by rw [isDirect_graftF_mid f q r b h hr hb]; simp),
      graft_node, Forest.mgraftF_graftF_inner f q b r u h hr hb]

/-- The forest half of `mgraft_graft_inner`. -/
theorem _root_.Operad.Forest.mgraftF_graftF_inner : ∀ {k : ℕ} (f : Forest E k) (q : ℕ)
    (b : Tree E) (r : ℕ) (u : Tree E), q < f.arityF → r < b.arity → b.isLeaf = false →
    (f.graftF q b).mgraftF μ (q + r) u = f.graftF q (b.mgraft μ r u)
  | _, .nil, _, _, _, _, h, _, _ => by simp at h
  | _, .cons t f, q, b, r, u, h, hr, hb => by
    simp only [arityF_cons] at h
    by_cases hq : q < t.arity
    · have : q + r < (t.graft q b).arity := by rw [arity_graft t q b hq]; omega
      rw [graftF_cons_of_lt _ hq, Forest.mgraftF, if_pos this, graftF_cons_of_lt _ hq,
        mgraft_graft_inner t q b r u hq hr hb]
    · rw [graftF_cons_of_ge _ (by omega), Forest.mgraftF, if_neg (by omega),
        graftF_cons_of_ge _ (by omega), show q + r - t.arity = (q - t.arity) + r by omega,
        Forest.mgraftF_graftF_inner f (q - t.arity) b r u (by omega) hr hb]

end

mutual

/-- **Grafting into a merge-grafted tree**: grafting in the merged tree commutes with the
merge. -/
theorem mgraft_graft_outer : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (q : ℕ) (b : Tree E),
    p < s.arity → q < u.arity → u.isLeaf = false →
    s.mgraft μ p (u.graft q b) = (s.mgraft μ p u).graft (p + q) b
  | .leaf, p, u, q, b, h, _, _ => by
    obtain rfl : p = 0 := by simpa using h
    simp
  | .node e f, p, u, q, b, h, hq, hu => by
    rw [mgraft_node, mgraft_node]
    split_ifs with hd
    · cases u with
      | leaf => simp at hu
      | node e' g =>
        simp only [graft_node, mergeRoot]
        congr 1
        rw [show p + q = f.offset (f.childIdx p) + q by
            rw [offset_childIdx_of_isDirect f p h hd],
          graftF_splice_mid f _ g q b (offset_childIdx_le f p h).2.2 hq]
    · rw [graft_node, Forest.mgraftF_graftF_outer f p u q b h hq hu]

/-- The forest half of `mgraft_graft_outer`. -/
theorem _root_.Operad.Forest.mgraftF_graftF_outer : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (q : ℕ) (b : Tree E), p < f.arityF → q < u.arity → u.isLeaf = false →
    f.mgraftF μ p (u.graft q b) = (f.mgraftF μ p u).graftF (p + q) b
  | _, .nil, _, _, _, _, h, _, _ => by simp at h
  | _, .cons t f, p, u, q, b, h, hq, hu => by
    simp only [arityF_cons] at h
    by_cases hp : p < t.arity
    · have : p + q < (t.mgraft μ p u).arity := by
        have := arity_mgraft μ t p u hp
        omega
      rw [Forest.mgraftF, if_pos hp, Forest.mgraftF, if_pos hp, graftF_cons_of_lt _ this,
        mgraft_graft_outer t p u q b hp hq hu]
    · rw [Forest.mgraftF, if_neg hp, Forest.mgraftF, if_neg hp, graftF_cons_of_ge _ (by omega),
        show p + q - t.arity = (p - t.arity) + q by omega,
        Forest.mgraftF_graftF_outer f (p - t.arity) u q b (by omega) hq hu]

end

/-! ### Merging and grafting at different leaves -/

/-- Splicing commutes with grafting before the splice. -/
lemma splice_graftF_before : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l) (q : ℕ)
    (b : Tree E), q < f.offset j → (f.graftF q b).splice j g = (f.splice j g).graftF q b
  | _, _, .nil, _, _, _, _, h => by simp [Forest.offset] at h
  | _, _, .cons t f, 0, g, q, b, h => by simp [Forest.offset] at h
  | _, _, .cons t f, j + 1, g, q, b, h => by
    simp only [Forest.offset] at h
    by_cases hq : q < t.arity
    · rw [graftF_cons_of_lt _ hq]
      show Forest.cons (t.graft q b) (f.splice j g) = (Forest.cons t (f.splice j g)).graftF q b
      rw [graftF_cons_of_lt _ hq]
    · rw [graftF_cons_of_ge _ (by omega)]
      show Forest.cons t ((f.graftF (q - t.arity) b).splice j g)
        = (Forest.cons t (f.splice j g)).graftF q b
      rw [graftF_cons_of_ge _ (by omega), splice_graftF_before f j g _ b (by omega)]

/-- Splicing commutes with grafting after the splice. -/
lemma splice_graftF_after : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l) (q : ℕ)
    (b : Tree E), j < k → f.offset j + (f.get j).arity ≤ q →
    (f.graftF q b).splice j g = (f.splice j g).graftF (q - (f.get j).arity + g.arityF) b
  | _, _, .nil, _, _, _, _, h, _ => by simp at h
  | _, _, .cons t f, 0, g, q, b, _, h => by
    simp only [Forest.offset, Forest.get, Nat.zero_add] at h ⊢
    rw [graftF_cons_of_ge _ h]
    show Forest.append g (f.graftF (q - t.arity) b)
      = (Forest.append g f).graftF (q - t.arity + g.arityF) b
    rw [Nat.add_comm (q - t.arity), graftF_append_right]
  | _, _, .cons t f, j + 1, g, q, b, hj, h => by
    simp only [Forest.offset, Forest.get] at h ⊢
    rw [graftF_cons_of_ge _ (by omega)]
    show Forest.cons t ((f.graftF (q - t.arity) b).splice j g)
      = (Forest.cons t (f.splice j g)).graftF (q - (f.get j).arity + g.arityF) b
    rw [graftF_cons_of_ge _ (by omega), splice_graftF_after f j g _ b (by omega) (by omega),
      show q - t.arity - (f.get j).arity + g.arityF = q - (f.get j).arity + g.arityF - t.arity
        by omega]

/-- Grafting after a leaf keeps its position. -/
lemma isDirect_childIdx_graftF_after : ∀ {k : ℕ} (f : Forest E k) (p q : ℕ) (b : Tree E),
    p < q → q < f.arityF →
    (f.graftF q b).isDirect p = f.isDirect p ∧ (f.graftF q b).childIdx p = f.childIdx p
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, p, q, b, hpq, h => by
    simp only [arityF_cons] at h
    by_cases hq : q < t.arity
    · have hp : p < (t.graft q b).arity := by rw [arity_graft t q b hq]; omega
      have hb : (t.graft q b).isLeaf = t.isLeaf := by
        cases t with
        | leaf => simp at hq; omega
        | node e f' => rfl
      rw [graftF_cons_of_lt _ hq, isDirect_cons_of_lt hp, isDirect_cons_of_lt (by omega), hb,
        childIdx_cons_of_lt hp, childIdx_cons_of_lt (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [graftF_cons_of_ge _ (by omega)]
      by_cases hp : p < t.arity
      · rw [isDirect_cons_of_lt hp, isDirect_cons_of_lt hp, childIdx_cons_of_lt hp,
          childIdx_cons_of_lt hp]
        exact ⟨rfl, rfl⟩
      · obtain ⟨h1, h2⟩ := isDirect_childIdx_graftF_after f (p - t.arity) (q - t.arity) b
          (by omega) (by omega)
        rw [isDirect_cons_of_ge (by omega), isDirect_cons_of_ge (by omega), h1,
          childIdx_cons_of_ge (by omega), childIdx_cons_of_ge (by omega), h2]
        exact ⟨rfl, rfl⟩

/-- Grafting before a leaf shifts its position. -/
lemma isDirect_childIdx_graftF_before : ∀ {k : ℕ} (f : Forest E k) (q p : ℕ) (b : Tree E),
    q < p → p < f.arityF →
    (f.graftF q b).isDirect (p - 1 + b.arity) = f.isDirect p ∧
      (f.graftF q b).childIdx (p - 1 + b.arity) = f.childIdx p
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, q, p, b, hqp, h => by
    simp only [arityF_cons] at h
    by_cases hq : q < t.arity
    · have hga := arity_graft t q b hq
      rw [graftF_cons_of_lt _ hq]
      by_cases hp : p < t.arity
      · have hp' : p - 1 + b.arity < (t.graft q b).arity := by rw [hga]; omega
        have hb : (t.graft q b).isLeaf = t.isLeaf := by
          cases t with
          | leaf => simp at hp; omega
          | node e f' => rfl
        rw [isDirect_cons_of_lt hp', isDirect_cons_of_lt hp, hb, childIdx_cons_of_lt hp',
          childIdx_cons_of_lt hp]
        exact ⟨rfl, rfl⟩
      · rw [isDirect_cons_of_ge (by omega), isDirect_cons_of_ge (by omega),
          childIdx_cons_of_ge (by omega), childIdx_cons_of_ge (by omega), hga,
          show p - 1 + b.arity - (t.arity - 1 + b.arity) = p - t.arity by omega]
        exact ⟨rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := isDirect_childIdx_graftF_before f (q - t.arity) (p - t.arity) b
        (by omega) (by omega)
      rw [graftF_cons_of_ge _ (by omega), isDirect_cons_of_ge (by omega),
        isDirect_cons_of_ge (by omega), childIdx_cons_of_ge (by omega),
        childIdx_cons_of_ge (by omega),
        show p - 1 + b.arity - t.arity = p - t.arity - 1 + b.arity by omega, h1, h2]
      exact ⟨rfl, rfl⟩

mutual

/-- **Grafting after the merge.** -/
theorem graft_mgraft_after : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (q : ℕ) (b : Tree E),
    p < q → q < s.arity →
    (s.graft q b).mgraft μ p u = (s.mgraft μ p u).graft (q - 1 + u.arity) b
  | .leaf, _, _, q, _, hpq, h => by simp at h; omega
  | .node e f, p, u, q, b, hpq, h => by
    obtain ⟨h1, h2⟩ := isDirect_childIdx_graftF_after f p q b hpq h
    rw [graft_node, mgraft_node, mgraft_node, h1, h2]
    split_ifs with hd
    · cases u with
      | leaf =>
        have : q - 1 + 1 = q := by omega
        simp [this]
      | node e' g =>
        simp only [mergeRoot, graft_node]
        congr 1
        have hp : p < f.arityF := by simp at h; omega
        have hc := offset_childIdx_le f p hp
        rw [eq_leaf_of_isLeaf (isLeaf_get_of_isDirect f p hp hd), arity_leaf] at hc
        have := splice_graftF_after f (f.childIdx p) g q b hc.2.2 (by
          rw [eq_leaf_of_isLeaf (isLeaf_get_of_isDirect f p hp hd), arity_leaf]; omega)
        rw [this, eq_leaf_of_isLeaf (isLeaf_get_of_isDirect f p hp hd), arity_leaf]
        rfl
    · rw [graft_node, Forest.graftF_mgraftF_after f p u q b hpq h]

/-- The forest half of `graft_mgraft_after`. -/
theorem _root_.Operad.Forest.graftF_mgraftF_after : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (q : ℕ) (b : Tree E), p < q → q < f.arityF →
    (f.graftF q b).mgraftF μ p u = (f.mgraftF μ p u).graftF (q - 1 + u.arity) b
  | _, .nil, _, _, _, _, _, h => by simp at h
  | _, .cons t f, p, u, q, b, hpq, h => by
    simp only [arityF_cons] at h
    by_cases hq : q < t.arity
    · have hp' : p < (t.graft q b).arity := by rw [arity_graft t q b hq]; omega
      have hq' : q - 1 + u.arity < (t.mgraft μ p u).arity := by
        have := arity_mgraft μ t p u (by omega)
        omega
      rw [graftF_cons_of_lt _ hq, Forest.mgraftF, if_pos hp', Forest.mgraftF,
        if_pos (show p < t.arity by omega), graftF_cons_of_lt _ hq',
        graft_mgraft_after t p u q b hpq hq]
    · by_cases hp : p < t.arity
      · have hq' : ¬ q - 1 + u.arity < (t.mgraft μ p u).arity := by
          have := arity_mgraft μ t p u hp
          omega
        rw [graftF_cons_of_ge _ (by omega), Forest.mgraftF, if_pos hp, Forest.mgraftF,
          if_pos hp, graftF_cons_of_ge _ (by omega)]
        have := arity_mgraft μ t p u hp
        rw [show q - 1 + u.arity - (t.mgraft μ p u).arity = q - t.arity by omega]
      · rw [graftF_cons_of_ge _ (by omega), Forest.mgraftF, if_neg hp, Forest.mgraftF,
          if_neg hp, graftF_cons_of_ge _ (by omega),
          Forest.graftF_mgraftF_after f (p - t.arity) u (q - t.arity) b (by omega) (by omega),
          show q - t.arity - 1 + u.arity = q - 1 + u.arity - t.arity by omega]

end

mutual

/-- **Grafting before the merge.** -/
theorem graft_mgraft_before : ∀ (s : Tree E) (q : ℕ) (b : Tree E) (p : ℕ) (u : Tree E),
    q < p → p < s.arity →
    (s.graft q b).mgraft μ (p - 1 + b.arity) u = (s.mgraft μ p u).graft q b
  | .leaf, _, _, p, _, hqp, h => by simp at h; omega
  | .node e f, q, b, p, u, hqp, h => by
    obtain ⟨h1, h2⟩ := isDirect_childIdx_graftF_before f q p b hqp h
    rw [graft_node, mgraft_node, mgraft_node, h1, h2]
    split_ifs with hd
    · cases u with
      | leaf => simp
      | node e' g =>
        simp only [mergeRoot, graft_node]
        congr 1
        have hp : p < f.arityF := by simpa using h
        have hc := offset_childIdx_le f p hp
        rw [eq_leaf_of_isLeaf (isLeaf_get_of_isDirect f p hp hd), arity_leaf] at hc
        exact splice_graftF_before f (f.childIdx p) g q b (by omega)
    · rw [graft_node, Forest.graftF_mgraftF_before f q b p u hqp h]

/-- The forest half of `graft_mgraft_before`. -/
theorem _root_.Operad.Forest.graftF_mgraftF_before : ∀ {k : ℕ} (f : Forest E k) (q : ℕ)
    (b : Tree E) (p : ℕ) (u : Tree E), q < p → p < f.arityF →
    (f.graftF q b).mgraftF μ (p - 1 + b.arity) u = (f.mgraftF μ p u).graftF q b
  | _, .nil, _, _, _, _, _, h => by simp at h
  | _, .cons t f, q, b, p, u, hqp, h => by
    simp only [arityF_cons] at h
    by_cases hq : q < t.arity
    · by_cases hp : p < t.arity
      · have hp' : p - 1 + b.arity < (t.graft q b).arity := by
          rw [arity_graft t q b hq]; omega
        have hq' : q < (t.mgraft μ p u).arity := by
          have := arity_mgraft μ t p u hp
          omega
        rw [graftF_cons_of_lt _ hq, Forest.mgraftF, if_pos hp', Forest.mgraftF, if_pos hp,
          graftF_cons_of_lt _ hq', graft_mgraft_before t q b p u hqp hp]
      · have hp' : ¬ p - 1 + b.arity < (t.graft q b).arity := by
          rw [arity_graft t q b hq]; omega
        rw [graftF_cons_of_lt _ hq, Forest.mgraftF, if_neg hp', Forest.mgraftF, if_neg hp,
          graftF_cons_of_lt _ hq, arity_graft t q b hq,
          show p - 1 + b.arity - (t.arity - 1 + b.arity) = p - t.arity by omega]
    · have hp : ¬ p < t.arity := by omega
      rw [graftF_cons_of_ge _ (by omega), Forest.mgraftF, if_neg (by omega), Forest.mgraftF,
        if_neg hp, graftF_cons_of_ge _ (by omega),
        show p - 1 + b.arity - t.arity = p - t.arity - 1 + b.arity by omega,
        Forest.graftF_mgraftF_before f (q - t.arity) b (p - t.arity) u (by omega) (by omega)]

end

/-! ## Cutting at a vertex -/

mutual

/-- **The number of vertices before a leaf**, in the preorder. -/
def vb : Tree E → ℕ → ℕ
  | .leaf, _ => 0
  | .node _ f, p => f.vbF p + 1

/-- The number of vertices of a forest before a leaf. -/
def _root_.Operad.Forest.vbF : ∀ {k : ℕ}, Forest E k → ℕ → ℕ
  | _, .nil, _ => 0
  | _, .cons t f, p => if p < t.arity then t.vb p else t.weight + f.vbF (p - t.arity)

end

mutual

/-- **The cut at a vertex**: the subtree `u` at the vertex `v` of the preorder, cut off as the
leaf `p` of the rest `s`, so that `s.graft p u = t`. -/
def cutV : Tree E → ℕ → Tree E × Tree E × ℕ
  | t, 0 => (.leaf, t, 0)
  | .leaf, _ + 1 => (.leaf, .leaf, 0)
  | .node e f, v + 1 => ((.node e (f.cutVF v).1), (f.cutVF v).2.1, (f.cutVF v).2.2)

/-- The cut of a forest at a vertex. -/
def _root_.Operad.Forest.cutVF : ∀ {k : ℕ}, Forest E k → ℕ → Forest E k × Tree E × ℕ
  | _, .nil, _ => (.nil, .leaf, 0)
  | _, .cons t f, v =>
    if v < t.weight then (.cons (t.cutV v).1 f, (t.cutV v).2.1, (t.cutV v).2.2)
    else (.cons t (f.cutVF (v - t.weight)).1, (f.cutVF (v - t.weight)).2.1,
      t.arity + (f.cutVF (v - t.weight)).2.2)

end

@[simp] lemma vb_leaf (p : ℕ) : (Tree.leaf : Tree E).vb p = 0 := rfl

@[simp] lemma vb_node {k : ℕ} (e : E k) (f : Forest E k) (p : ℕ) :
    (Tree.node e f).vb p = f.vbF p + 1 := rfl

lemma vbF_cons_of_lt {k : ℕ} {t : Tree E} {f : Forest E k} {p : ℕ} (h : p < t.arity) :
    (Forest.cons t f).vbF p = t.vb p := by
  rw [Forest.vbF, if_pos h]

lemma vbF_cons_of_ge {k : ℕ} {t : Tree E} {f : Forest E k} {p : ℕ} (h : t.arity ≤ p) :
    (Forest.cons t f).vbF p = t.weight + f.vbF (p - t.arity) := by
  rw [Forest.vbF, if_neg (by omega)]

@[simp] lemma cutV_zero (t : Tree E) : t.cutV 0 = (.leaf, t, 0) := by
  cases t <;> rfl

@[simp] lemma cutV_node_succ {k : ℕ} (e : E k) (f : Forest E k) (v : ℕ) :
    (Tree.node e f).cutV (v + 1) = ((.node e (f.cutVF v).1), (f.cutVF v).2.1, (f.cutVF v).2.2) :=
  rfl

lemma cutVF_cons_of_lt {k : ℕ} {t : Tree E} {f : Forest E k} {v : ℕ} (h : v < t.weight) :
    (Forest.cons t f).cutVF v = (.cons (t.cutV v).1 f, (t.cutV v).2.1, (t.cutV v).2.2) := by
  rw [Forest.cutVF, if_pos h]

lemma cutVF_cons_of_ge {k : ℕ} {t : Tree E} {f : Forest E k} {v : ℕ} (h : t.weight ≤ v) :
    (Forest.cutVF (.cons t f) v) = (.cons t (f.cutVF (v - t.weight)).1,
      (f.cutVF (v - t.weight)).2.1, t.arity + (f.cutVF (v - t.weight)).2.2) := by
  rw [Forest.cutVF, if_neg (by omega)]

mutual

/-- The vertices before a leaf are among all the vertices. -/
theorem vb_le_weight : ∀ (t : Tree E) (p : ℕ), t.vb p ≤ t.weight
  | .leaf, _ => le_rfl
  | .node _ f, p => by
    simp only [vb_node, weight_node]
    have := Forest.vbF_le_weightF f p
    omega

/-- The forest half of `vb_le_weight`. -/
theorem _root_.Operad.Forest.vbF_le_weightF : ∀ {k : ℕ} (f : Forest E k) (p : ℕ),
    f.vbF p ≤ f.weightF
  | _, .nil, _ => le_rfl
  | _, .cons t f, p => by
    by_cases h : p < t.arity
    · rw [vbF_cons_of_lt h, weightF_cons]
      have := vb_le_weight t p
      omega
    · rw [vbF_cons_of_ge (by omega), weightF_cons]
      have := Forest.vbF_le_weightF f (p - t.arity)
      omega

end

mutual

/-- **The cut at a vertex is a cut**: the leaf is a leaf of the rest. -/
theorem lt_arity_cutV : ∀ (t : Tree E) (v : ℕ), v < t.weight →
    (t.cutV v).2.2 < (t.cutV v).1.arity
  | t, 0, _ => by simp
  | .leaf, _ + 1, h => by simp at h
  | .node e f, v + 1, h => by
    simp only [cutV_node_succ, arity_node]
    exact Forest.lt_arityF_cutVF f v (by simpa using h)

/-- The forest half of `lt_arity_cutV`. -/
theorem _root_.Operad.Forest.lt_arityF_cutVF : ∀ {k : ℕ} (f : Forest E k) (v : ℕ),
    v < f.weightF → (f.cutVF v).2.2 < (f.cutVF v).1.arityF
  | _, .nil, _, h => by simp at h
  | _, .cons t f, v, h => by
    simp only [weightF_cons] at h
    by_cases hv : v < t.weight
    · rw [cutVF_cons_of_lt hv]
      simp only [arityF_cons]
      have := lt_arity_cutV t v hv
      omega
    · rw [cutVF_cons_of_ge (by omega)]
      simp only [arityF_cons]
      have := Forest.lt_arityF_cutVF f (v - t.weight) (by omega)
      omega

end

mutual

/-- **The cut at a vertex grafts back to the tree.** -/
theorem graft_cutV : ∀ (t : Tree E) (v : ℕ), v < t.weight →
    (t.cutV v).1.graft (t.cutV v).2.2 (t.cutV v).2.1 = t
  | t, 0, _ => by simp
  | .leaf, _ + 1, h => by simp at h
  | .node e f, v + 1, h => by
    simp only [cutV_node_succ, graft_node]
    rw [Forest.graftF_cutVF f v (by simpa using h)]

/-- The forest half of `graft_cutV`. -/
theorem _root_.Operad.Forest.graftF_cutVF : ∀ {k : ℕ} (f : Forest E k) (v : ℕ),
    v < f.weightF → (f.cutVF v).1.graftF (f.cutVF v).2.2 (f.cutVF v).2.1 = f
  | _, .nil, _, h => by simp at h
  | _, .cons t f, v, h => by
    simp only [weightF_cons] at h
    by_cases hv : v < t.weight
    · rw [cutVF_cons_of_lt hv, graftF_cons_of_lt _ (lt_arity_cutV t v hv), graft_cutV t v hv]
    · rw [cutVF_cons_of_ge (by omega)]
      dsimp only
      rw [graftF_cons_of_ge _ (by omega),
        show t.arity + (f.cutVF (v - t.weight)).2.2 - t.arity = (f.cutVF (v - t.weight)).2.2
          by omega, Forest.graftF_cutVF f (v - t.weight) (by omega)]

end

mutual

/-- **The cut at a vertex has that many vertices before its leaf.** -/
theorem vb_cutV : ∀ (t : Tree E) (v : ℕ), v < t.weight → (t.cutV v).1.vb (t.cutV v).2.2 = v
  | t, 0, _ => by simp
  | .leaf, _ + 1, h => by simp at h
  | .node e f, v + 1, h => by
    simp only [cutV_node_succ, vb_node]
    rw [Forest.vbF_cutVF f v (by simpa using h)]

/-- The forest half of `vb_cutV`. -/
theorem _root_.Operad.Forest.vbF_cutVF : ∀ {k : ℕ} (f : Forest E k) (v : ℕ),
    v < f.weightF → (f.cutVF v).1.vbF (f.cutVF v).2.2 = v
  | _, .nil, _, h => by simp at h
  | _, .cons t f, v, h => by
    simp only [weightF_cons] at h
    by_cases hv : v < t.weight
    · rw [cutVF_cons_of_lt hv, vbF_cons_of_lt (lt_arity_cutV t v hv), vb_cutV t v hv]
    · rw [cutVF_cons_of_ge (by omega)]
      dsimp only
      rw [vbF_cons_of_ge (by omega),
        show t.arity + (f.cutVF (v - t.weight)).2.2 - t.arity = (f.cutVF (v - t.weight)).2.2
          by omega, Forest.vbF_cutVF f (v - t.weight) (by omega)]
      omega

end

mutual

/-- **The subtree at a vertex is not trivial.** -/
theorem isLeaf_cutV : ∀ (t : Tree E) (v : ℕ), v < t.weight → (t.cutV v).2.1.isLeaf = false
  | .leaf, _, h => by simp at h
  | .node e f, 0, _ => rfl
  | .node e f, v + 1, h => by
    simp only [cutV_node_succ]
    exact Forest.isLeaf_cutVF f v (by simpa using h)

/-- The forest half of `isLeaf_cutV`. -/
theorem _root_.Operad.Forest.isLeaf_cutVF : ∀ {k : ℕ} (f : Forest E k) (v : ℕ),
    v < f.weightF → (f.cutVF v).2.1.isLeaf = false
  | _, .nil, _, h => by simp at h
  | _, .cons t f, v, h => by
    simp only [weightF_cons] at h
    by_cases hv : v < t.weight
    · rw [cutVF_cons_of_lt hv]
      exact isLeaf_cutV t v hv
    · rw [cutVF_cons_of_ge (by omega)]
      exact Forest.isLeaf_cutVF f (v - t.weight) (by omega)

end

mutual

/-- **A cut is the cut at the vertex of its subtree**: cuts are determined by the position of
the cut vertex. -/
theorem cutV_graft : ∀ (s : Tree E) (p : ℕ) (u : Tree E), p < s.arity → u.isLeaf = false →
    (s.graft p u).cutV (s.vb p) = (s, u, p)
  | .leaf, p, u, h, _ => by
    obtain rfl : p = 0 := by simpa using h
    simp
  | .node e f, p, u, h, hu => by
    simp only [graft_node, vb_node, cutV_node_succ]
    rw [Forest.cutVF_graftF f p u h hu]

/-- The forest half of `cutV_graft`. -/
theorem _root_.Operad.Forest.cutVF_graftF : ∀ {k : ℕ} (f : Forest E k) (p : ℕ) (u : Tree E),
    p < f.arityF → u.isLeaf = false → (f.graftF p u).cutVF (f.vbF p) = (f, u, p)
  | _, .nil, _, _, h, _ => by simp at h
  | _, .cons t f, p, u, h, hu => by
    simp only [arityF_cons] at h
    have hw : 0 < u.weight := by
      cases u with
      | leaf => simp at hu
      | node e g => simp
    by_cases hp : p < t.arity
    · have hlt : t.vb p < (t.graft p u).weight := by
        rw [weight_graft t p u hp]
        have := vb_le_weight t p
        omega
      rw [graftF_cons_of_lt _ hp, vbF_cons_of_lt hp, cutVF_cons_of_lt hlt,
        cutV_graft t p u hp hu]
    · rw [graftF_cons_of_ge _ (by omega), vbF_cons_of_ge (by omega),
        cutVF_cons_of_ge (by omega), Nat.add_sub_cancel_left,
        Forest.cutVF_graftF f (p - t.arity) u (by omega) hu]
      simp only [Prod.mk.injEq, true_and]
      omega

end


/-! ## Parities and vertex counts of appended and spliced forests -/

section SpliceStats

variable (gp : ∀ k, E k → Bool)

lemma tparF_append : ∀ {k l : ℕ} (g : Forest E l) (f : Forest E k),
    Forest.tparF gp (Forest.append g f) = xor (Forest.tparF gp g) (Forest.tparF gp f)
  | _, _, .nil, f => by simp [Forest.tparF]
  | _, _, .cons t g, f => by
    rw [append_cons, tparF_cons, tparF_cons, tparF_append g f, Bool.xor_assoc]

lemma aparF_append_left : ∀ {k l : ℕ} (g : Forest E l) (f : Forest E k) (q : ℕ),
    q < g.arityF →
    Forest.aparF gp (Forest.append g f) q = xor (Forest.aparF gp g q) (Forest.tparF gp f)
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons t g, f, q, h => by
    simp only [arityF_cons] at h
    rw [append_cons]
    by_cases hq : q < t.arity
    · rw [aparF_cons_of_lt gp _ _ hq, aparF_cons_of_lt gp _ _ hq, tparF_append, Bool.xor_assoc]
    · rw [aparF_cons_of_ge gp _ _ (by omega), aparF_cons_of_ge gp _ _ (by omega),
        aparF_append_left g f _ (by omega)]

lemma aparF_append_right : ∀ {k l : ℕ} (g : Forest E l) (f : Forest E k) (q : ℕ),
    Forest.aparF gp (Forest.append g f) (g.arityF + q) = Forest.aparF gp f q
  | _, _, .nil, _, _ => by simp
  | _, _, .cons t g, f, q => by
    rw [append_cons, arityF_cons, aparF_cons_of_ge gp _ _ (by omega),
      show t.arity + g.arityF + q - t.arity = g.arityF + q by omega, aparF_append_right g f q]

lemma vbF_append_left : ∀ {k l : ℕ} (g : Forest E l) (f : Forest E k) (q : ℕ),
    q < g.arityF → (Forest.append g f).vbF q = g.vbF q
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons t g, f, q, h => by
    simp only [arityF_cons] at h
    rw [append_cons]
    by_cases hq : q < t.arity
    · rw [vbF_cons_of_lt hq, vbF_cons_of_lt hq]
    · rw [vbF_cons_of_ge (by omega), vbF_cons_of_ge (by omega),
        vbF_append_left g f _ (by omega)]

lemma vbF_append_right : ∀ {k l : ℕ} (g : Forest E l) (f : Forest E k) (q : ℕ),
    (Forest.append g f).vbF (g.arityF + q) = g.weightF + f.vbF q
  | _, _, .nil, _, _ => by simp
  | _, _, .cons t g, f, q => by
    rw [append_cons, arityF_cons, vbF_cons_of_ge (by omega),
      show t.arity + g.arityF + q - t.arity = g.arityF + q by omega, vbF_append_right g f q,
      weightF_cons, Nat.add_assoc]

lemma tparF_splice : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l), j < k →
    xor (Forest.tparF gp (f.splice j g)) (tpar gp (f.get j))
      = xor (Forest.tparF gp f) (Forest.tparF gp g)
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons t f, 0, g, _ => by
    show xor (Forest.tparF gp (Forest.append g f)) (tpar gp t) = _
    rw [tparF_append, tparF_cons]
    cases Forest.tparF gp g <;> cases Forest.tparF gp f <;> cases tpar gp t <;> rfl
  | _, _, .cons t f, j + 1, g, h => by
    show xor (Forest.tparF gp (Forest.cons t (f.splice j g))) (tpar gp (f.get j)) = _
    rw [tparF_cons, tparF_cons, Bool.xor_assoc, tparF_splice f j g (by omega), Bool.xor_assoc]

lemma aparF_splice_before : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l) (q : ℕ),
    j < k → q < f.offset j →
    xor (Forest.aparF gp (f.splice j g) q) (tpar gp (f.get j))
      = xor (Forest.aparF gp f q) (Forest.tparF gp g)
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons t f, 0, g, q, _, h => by simp [Forest.offset] at h
  | _, _, .cons t f, j + 1, g, q, hj, h => by
    simp only [Forest.offset] at h
    show xor (Forest.aparF gp (Forest.cons t (f.splice j g)) q) (tpar gp (f.get j)) = _
    by_cases hq : q < t.arity
    · rw [aparF_cons_of_lt gp _ _ hq, aparF_cons_of_lt gp _ _ hq, Bool.xor_assoc,
        tparF_splice gp f j g (by omega)]
      cases apar gp t q <;> cases Forest.tparF gp f <;> cases Forest.tparF gp g <;> rfl
    · rw [aparF_cons_of_ge gp _ _ (by omega), aparF_cons_of_ge gp _ _ (by omega),
        aparF_splice_before f j g _ (by omega) (by omega)]

lemma aparF_splice_inner : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l) (q : ℕ),
    j < k → (f.get j).isLeaf = true → q < g.arityF →
    Forest.aparF gp (f.splice j g) (f.offset j + q)
      = xor (Forest.aparF gp g q) (Forest.aparF gp f (f.offset j))
  | _, _, .nil, _, _, _, h, _, _ => by simp at h
  | _, _, .cons t f, 0, g, q, _, ht, hq => by
    obtain rfl := eq_leaf_of_isLeaf ht
    show Forest.aparF gp (Forest.append g f) (0 + q)
      = xor (Forest.aparF gp g q) (Forest.aparF gp (Forest.cons .leaf f) 0)
    rw [Nat.zero_add, aparF_append_left gp g f q hq, aparF_cons_of_lt gp _ _ (by simp)]
    simp
  | _, _, .cons t f, j + 1, g, q, hj, ht, hq => by
    show Forest.aparF gp (Forest.cons t (f.splice j g)) (t.arity + f.offset j + q)
      = xor (Forest.aparF gp g q) (Forest.aparF gp (Forest.cons t f) (t.arity + f.offset j))
    rw [aparF_cons_of_ge gp _ _ (by omega), aparF_cons_of_ge gp _ _ (by omega),
      show t.arity + f.offset j + q - t.arity = f.offset j + q by omega, Nat.add_sub_cancel_left,
      aparF_splice_inner f j g q (by omega) ht hq]

lemma aparF_splice_after : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l) (q : ℕ),
    j < k → (f.get j).isLeaf = true → f.offset j < q → q < f.arityF →
    Forest.aparF gp (f.splice j g) (q - 1 + g.arityF) = Forest.aparF gp f q
  | _, _, .nil, _, _, _, h, _, _, _ => by simp at h
  | _, _, .cons t f, 0, g, q, _, ht, hq, _ => by
    obtain rfl := eq_leaf_of_isLeaf ht
    simp only [Forest.offset] at hq
    show Forest.aparF gp (Forest.append g f) (q - 1 + g.arityF)
      = Forest.aparF gp (Forest.cons .leaf f) q
    rw [show q - 1 + g.arityF = g.arityF + (q - 1) by omega, aparF_append_right,
      aparF_cons_of_ge gp _ _ (by simp; omega), arity_leaf]
  | _, _, .cons t f, j + 1, g, q, hj, ht, hq, hqa => by
    simp only [Forest.offset, arityF_cons] at hq hqa
    show Forest.aparF gp (Forest.cons t (f.splice j g)) (q - 1 + g.arityF)
      = Forest.aparF gp (Forest.cons t f) q
    rw [aparF_cons_of_ge gp _ _ (by omega), aparF_cons_of_ge gp _ _ (by omega),
      show q - 1 + g.arityF - t.arity = q - t.arity - 1 + g.arityF by omega,
      aparF_splice_after f j g _ (by omega) ht (by omega) (by omega)]

lemma vbF_splice_before : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l) (q : ℕ),
    q < f.offset j → (f.splice j g).vbF q = f.vbF q
  | _, _, .nil, _, _, _, h => by simp [Forest.offset] at h
  | _, _, .cons t f, 0, g, q, h => by simp [Forest.offset] at h
  | _, _, .cons t f, j + 1, g, q, h => by
    simp only [Forest.offset] at h
    show (Forest.cons t (f.splice j g)).vbF q = (Forest.cons t f).vbF q
    by_cases hq : q < t.arity
    · rw [vbF_cons_of_lt hq, vbF_cons_of_lt hq]
    · rw [vbF_cons_of_ge (by omega), vbF_cons_of_ge (by omega),
        vbF_splice_before f j g _ (by omega)]

lemma vbF_splice_inner : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l) (q : ℕ),
    j < k → (f.get j).isLeaf = true → q < g.arityF →
    (f.splice j g).vbF (f.offset j + q) = f.vbF (f.offset j) + g.vbF q
  | _, _, .nil, _, _, _, h, _, _ => by simp at h
  | _, _, .cons t f, 0, g, q, _, ht, hq => by
    obtain rfl := eq_leaf_of_isLeaf ht
    show (Forest.append g f).vbF (0 + q) = (Forest.cons .leaf f).vbF 0 + g.vbF q
    rw [Nat.zero_add, vbF_append_left g f q hq, vbF_cons_of_lt (by simp), vb_leaf, Nat.zero_add]
  | _, _, .cons t f, j + 1, g, q, hj, ht, hq => by
    show (Forest.cons t (f.splice j g)).vbF (t.arity + f.offset j + q)
      = (Forest.cons t f).vbF (t.arity + f.offset j) + g.vbF q
    rw [vbF_cons_of_ge (by omega), vbF_cons_of_ge (by omega),
      show t.arity + f.offset j + q - t.arity = f.offset j + q by omega, Nat.add_sub_cancel_left,
      vbF_splice_inner f j g q (by omega) ht hq, Nat.add_assoc]

lemma vbF_splice_after : ∀ {k l : ℕ} (f : Forest E k) (j : ℕ) (g : Forest E l) (q : ℕ),
    j < k → (f.get j).isLeaf = true → f.offset j < q → q < f.arityF →
    (f.splice j g).vbF (q - 1 + g.arityF) = f.vbF q + g.weightF
  | _, _, .nil, _, _, _, h, _, _, _ => by simp at h
  | _, _, .cons t f, 0, g, q, _, ht, hq, _ => by
    obtain rfl := eq_leaf_of_isLeaf ht
    simp only [Forest.offset] at hq
    show (Forest.append g f).vbF (q - 1 + g.arityF) = (Forest.cons .leaf f).vbF q + g.weightF
    rw [show q - 1 + g.arityF = g.arityF + (q - 1) by omega, vbF_append_right,
      vbF_cons_of_ge (by simp; omega), arity_leaf, weight_leaf]
    omega
  | _, _, .cons t f, j + 1, g, q, hj, ht, hq, hqa => by
    simp only [Forest.offset, arityF_cons] at hq hqa
    show (Forest.cons t (f.splice j g)).vbF (q - 1 + g.arityF)
      = (Forest.cons t f).vbF q + g.weightF
    rw [vbF_cons_of_ge (by omega), vbF_cons_of_ge (by omega),
      show q - 1 + g.arityF - t.arity = q - t.arity - 1 + g.arityF by omega,
      vbF_splice_after f j g _ (by omega) ht (by omega) (by omega), Nat.add_assoc]

end SpliceStats


/-! ## Parities relative to the vertex carrying a leaf -/

/-- A merge function **adds the parities of the merged generators, plus one**, as in a bar
construction. -/
abbrev _root_.Operad.MergeFn.Odd (gp : ∀ k, E k → Bool) (μ : MergeFn E) : Prop :=
  ∀ k l (e : E k) j (e' : E l) m, gp m (μ k l e j e' m) = !(xor (gp k e) (gp l e'))

mutual

/-- **Whether the leaf `q` comes before the vertex carrying the leaf `p`**, in the preorder. -/
def qbp : Tree E → ℕ → ℕ → Bool
  | .leaf, _, _ => false
  | .node _ f, q, p => if f.isDirect p then false else Forest.qbpF f q p

/-- Whether a leaf comes before the vertex carrying another one, in a forest. -/
def _root_.Operad.Forest.qbpF : ∀ {k : ℕ}, Forest E k → ℕ → ℕ → Bool
  | _, .nil, _, _ => false
  | _, .cons t f, q, p =>
    if p < t.arity then qbp t q p
    else if q < t.arity then true else Forest.qbpF f (q - t.arity) (p - t.arity)

end

section LeafPar

variable (gp : ∀ k, E k → Bool)

/-- The parity of the root vertex, `false` for the trivial tree. -/
def rpar : Tree E → Bool
  | .leaf => false
  | .node e _ => gp _ e

@[simp] lemma rpar_leaf : rpar gp (.leaf : Tree E) = false := rfl

@[simp] lemma rpar_node {k : ℕ} (e : E k) (f : Forest E k) : rpar gp (.node e f) = gp _ e := rfl

lemma rpar_graft {s : Tree E} (hs : s.isLeaf = false) (p : ℕ) (u : Tree E) :
    rpar gp (s.graft p u) = rpar gp s := by
  cases s with
  | leaf => simp at hs
  | node e f => rfl

mutual

/-- **The parity before the vertex carrying a leaf**: the sum of the parities of the vertices
met before it in the preorder. -/
def lpar : Tree E → ℕ → Bool
  | .leaf, _ => false
  | .node e f, p => if f.isDirect p then false else xor (gp _ e) (Forest.lparF f p)

/-- The parity before the vertex carrying a leaf, in a forest. -/
def _root_.Operad.Forest.lparF : ∀ {k : ℕ}, Forest E k → ℕ → Bool
  | _, .nil, _ => false
  | _, .cons t f, p =>
    if p < t.arity then lpar t p else xor (tpar gp t) (Forest.lparF f (p - t.arity))

end

mutual

/-- **The parity between the vertex carrying a leaf and the leaf**: the sum of the parities of
the vertices met after that vertex and before the leaf in the preorder. -/
def mpar : Tree E → ℕ → Bool
  | .leaf, _ => false
  | .node _ f, p =>
    if f.isDirect p then xor (Forest.tparF gp f) (Forest.aparF gp f p) else Forest.mparF f p

/-- The parity between the vertex carrying a leaf and the leaf, in a forest. -/
def _root_.Operad.Forest.mparF : ∀ {k : ℕ}, Forest E k → ℕ → Bool
  | _, .nil, _ => false
  | _, .cons t f, p => if p < t.arity then mpar t p else Forest.mparF f (p - t.arity)

end

lemma lpar_node {k : ℕ} (e : E k) (f : Forest E k) (p : ℕ) :
    lpar gp (.node e f) p = if f.isDirect p then false else xor (gp _ e) (Forest.lparF gp f p) :=
  rfl

lemma mpar_node {k : ℕ} (e : E k) (f : Forest E k) (p : ℕ) :
    mpar gp (.node e f) p = if f.isDirect p then xor (Forest.tparF gp f) (Forest.aparF gp f p)
      else Forest.mparF gp f p :=
  rfl

lemma lparF_cons_of_lt {k : ℕ} (t : Tree E) (f : Forest E k) {p : ℕ} (h : p < t.arity) :
    Forest.lparF gp (.cons t f) p = lpar gp t p := by
  rw [Forest.lparF, if_pos h]

lemma lparF_cons_of_ge {k : ℕ} (t : Tree E) (f : Forest E k) {p : ℕ} (h : t.arity ≤ p) :
    Forest.lparF gp (.cons t f) p = xor (tpar gp t) (Forest.lparF gp f (p - t.arity)) := by
  rw [Forest.lparF, if_neg (by omega)]

lemma mparF_cons_of_lt {k : ℕ} (t : Tree E) (f : Forest E k) {p : ℕ} (h : p < t.arity) :
    Forest.mparF gp (.cons t f) p = mpar gp t p := by
  rw [Forest.mparF, if_pos h]

lemma mparF_cons_of_ge {k : ℕ} (t : Tree E) (f : Forest E k) {p : ℕ} (h : t.arity ≤ p) :
    Forest.mparF gp (.cons t f) p = Forest.mparF gp f (p - t.arity) := by
  rw [Forest.mparF, if_neg (by omega)]

/-! ### Merge-grafting: parities -/

mutual

/-- **Merge-grafting adds the parities, plus one**, for a merge function adding one. -/
theorem tpar_mgraft (hμ : MergeFn.Odd gp μ) : ∀ (s : Tree E) (p : ℕ) (u : Tree E),
    p < s.arity → s.isLeaf = false → u.isLeaf = false →
    tpar gp (s.mgraft μ p u) = !(xor (tpar gp s) (tpar gp u))
  | .leaf, _, _, _, hs, _ => by simp at hs
  | .node e f, p, u, h, _, hu => by
    rw [mgraft_node]
    split_ifs with hd
    · cases u with
      | leaf => simp at hu
      | node e' g =>
        have hp : p < f.arityF := by simpa using h
        have hs := tparF_splice gp f (f.childIdx p) g (offset_childIdx_le f p hp).2.2
        rw [eq_leaf_of_isLeaf (isLeaf_get_of_isDirect f p hp hd), tpar_leaf,
          Bool.xor_false] at hs
        simp only [mergeRoot, tpar_node, hμ, hs]
        cases gp _ e <;> cases gp _ e' <;> cases Forest.tparF gp f <;>
          cases Forest.tparF gp g <;> rfl
    · simp only [tpar_node]
      rw [Forest.tparF_mgraftF hμ f p u (by simpa using h) hd hu]
      cases gp _ e <;> cases Forest.tparF gp f <;> cases tpar gp u <;> rfl

/-- The forest half of `tpar_mgraft`. -/
theorem _root_.Operad.Forest.tparF_mgraftF (hμ : MergeFn.Odd gp μ) : ∀ {k : ℕ}
    (f : Forest E k) (p : ℕ) (u : Tree E), p < f.arityF → ¬ f.isDirect p = true →
    u.isLeaf = false → Forest.tparF gp (f.mgraftF μ p u) = !(xor (Forest.tparF gp f) (tpar gp u))
  | _, .nil, _, _, h, _, _ => by simp at h
  | _, .cons t f, p, u, h, hd, hu => by
    simp only [arityF_cons] at h
    simp only [Forest.mgraftF]
    split_ifs with hp
    · rw [isDirect_cons_of_lt hp] at hd
      rw [tparF_cons, tparF_cons, tpar_mgraft hμ t p u hp (by simpa using hd) hu]
      cases tpar gp t <;> cases tpar gp u <;> cases Forest.tparF gp f <;> rfl
    · rw [isDirect_cons_of_ge (by omega)] at hd
      rw [tparF_cons, tparF_cons, Forest.tparF_mgraftF hμ f (p - t.arity) u (by omega) hd hu]
      cases tpar gp t <;> cases tpar gp u <;> cases Forest.tparF gp f <;> rfl

end

mutual

/-- **The leaves of a merge-grafted tree** see its vertices after them, and then those of the outer
tree after the graft point. -/
theorem apar_mgraft_inner : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (j : ℕ), p < s.arity →
    j < u.arity → u.isLeaf = false →
    apar gp (s.mgraft μ p u) (p + j) = xor (apar gp u j) (apar gp s p)
  | .leaf, p, u, j, h, _, _ => by
    obtain rfl : p = 0 := by simpa using h
    simp
  | .node e f, p, u, j, h, hj, hu => by
    rw [mgraft_node]
    split_ifs with hd
    · cases u with
      | leaf => simp at hu
      | node e' g =>
        have hp : p < f.arityF := by simpa using h
        have hc := offset_childIdx_le f p hp
        have ho := offset_childIdx_of_isDirect f p hp hd
        simp only [mergeRoot, apar_node]
        rw [show p + j = f.offset (f.childIdx p) + j by rw [ho],
          aparF_splice_inner gp f _ g j hc.2.2 (isLeaf_get_of_isDirect f p hp hd)
            (by simpa using hj), ho]
    · simp only [apar_node]
      exact Forest.aparF_mgraftF_inner f p u j (by simpa using h) hj hu

/-- The forest half of `apar_mgraft_inner`. -/
theorem _root_.Operad.Forest.aparF_mgraftF_inner : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (j : ℕ), p < f.arityF → j < u.arity → u.isLeaf = false →
    Forest.aparF gp (f.mgraftF μ p u) (p + j) = xor (apar gp u j) (Forest.aparF gp f p)
  | _, .nil, _, _, _, h, _, _ => by simp at h
  | _, .cons t f, p, u, j, h, hj, hu => by
    simp only [arityF_cons] at h
    simp only [Forest.mgraftF]
    split_ifs with hp
    · have ha := arity_mgraft μ t p u hp
      rw [aparF_cons_of_lt gp t f hp, aparF_cons_of_lt gp (t.mgraft μ p u) f (by omega),
        apar_mgraft_inner t p u j hp hj hu, Bool.xor_assoc]
    · rw [aparF_cons_of_ge gp t f (by omega), aparF_cons_of_ge gp t _ (by omega),
        show p + j - t.arity = p - t.arity + j by omega,
        Forest.aparF_mgraftF_inner f (p - t.arity) u j (by omega) hj hu]

end

mutual

/-- **The leaves after a merge-graft point** see no change. -/
theorem apar_mgraft_after : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (q : ℕ), p < q →
    q < s.arity → apar gp (s.mgraft μ p u) (q - 1 + u.arity) = apar gp s q
  | .leaf, _, _, q, hpq, h => by simp at h; omega
  | .node e f, p, u, q, hpq, h => by
    rw [mgraft_node]
    split_ifs with hd
    · cases u with
      | leaf => simp [Nat.sub_add_cancel (show 1 ≤ q by omega)]
      | node e' g =>
        have hp : p < f.arityF := by simp at h; omega
        have hc := offset_childIdx_le f p hp
        have ho := offset_childIdx_of_isDirect f p hp hd
        simp only [mergeRoot, apar_node, arity_node]
        exact aparF_splice_after gp f _ g q hc.2.2 (isLeaf_get_of_isDirect f p hp hd)
          (by omega) (by simpa using h)
    · simp only [apar_node]
      exact Forest.aparF_mgraftF_after f p u q hpq (by simpa using h)

/-- The forest half of `apar_mgraft_after`. -/
theorem _root_.Operad.Forest.aparF_mgraftF_after : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (q : ℕ), p < q → q < f.arityF →
    Forest.aparF gp (f.mgraftF μ p u) (q - 1 + u.arity) = Forest.aparF gp f q
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, p, u, q, hpq, h => by
    simp only [arityF_cons] at h
    simp only [Forest.mgraftF]
    split_ifs with hp
    · have ha := arity_mgraft μ t p u hp
      by_cases hq : q < t.arity
      · rw [aparF_cons_of_lt gp t f hq, aparF_cons_of_lt gp (t.mgraft μ p u) f (by omega),
          apar_mgraft_after t p u q hpq hq]
      · rw [aparF_cons_of_ge gp t f (by omega), aparF_cons_of_ge gp (t.mgraft μ p u) f (by omega),
          show q - 1 + u.arity - (t.mgraft μ p u).arity = q - t.arity by omega]
    · rw [aparF_cons_of_ge gp t f (by omega), aparF_cons_of_ge gp t _ (by omega),
        show q - 1 + u.arity - t.arity = q - t.arity - 1 + u.arity by omega,
        Forest.aparF_mgraftF_after f (p - t.arity) u (q - t.arity) (by omega) (by omega)]

end

mutual

/-- **The leaves before a merge-graft point** see the merged tree in addition, with the merged
vertex when it comes after them. -/
theorem apar_mgraft_before (hμ : MergeFn.Odd gp μ) : ∀ (s : Tree E) (q p : ℕ) (u : Tree E),
    q < p → p < s.arity → u.isLeaf = false →
    apar gp (s.mgraft μ p u) q
      = xor (apar gp s q) (xor (tpar gp u) (if qbp s q p then true else rpar gp u))
  | .leaf, _, p, _, hqp, h, _ => by simp at h; omega
  | .node e f, q, p, u, hqp, h, hu => by
    rw [mgraft_node]
    by_cases hd : f.isDirect p = true
    · rw [if_pos hd]
      cases u with
      | leaf => simp at hu
      | node e' g =>
        have hp : p < f.arityF := by simpa using h
        have hc := offset_childIdx_le f p hp
        have ho := offset_childIdx_of_isDirect f p hp hd
        have hs := aparF_splice_before gp f _ g q hc.2.2 (by omega)
        rw [eq_leaf_of_isLeaf (isLeaf_get_of_isDirect f p hp hd), tpar_leaf,
          Bool.xor_false] at hs
        simp only [mergeRoot, apar_node, qbp, hd, tpar_node, rpar_node, hs, ↓reduceIte,
          Bool.false_eq_true]
        cases Forest.aparF gp f q <;> cases gp _ e' <;> cases Forest.tparF gp g <;> rfl
    · rw [if_neg hd]
      have hd' : f.isDirect p = false := by simpa using hd
      simp only [apar_node, qbp, hd', Bool.false_eq_true, ↓reduceIte]
      exact Forest.aparF_mgraftF_before hμ f q p u hqp (by simpa using h) hd hu

/-- The forest half of `apar_mgraft_before`. -/
theorem _root_.Operad.Forest.aparF_mgraftF_before (hμ : MergeFn.Odd gp μ) : ∀ {k : ℕ}
    (f : Forest E k) (q p : ℕ) (u : Tree E), q < p → p < f.arityF → ¬ f.isDirect p = true →
    u.isLeaf = false →
    Forest.aparF gp (f.mgraftF μ p u) q
      = xor (Forest.aparF gp f q)
          (xor (tpar gp u) (if Forest.qbpF f q p then true else rpar gp u))
  | _, .nil, _, _, _, _, h, _, _ => by simp at h
  | _, .cons t f, q, p, u, hqp, h, hd, hu => by
    simp only [arityF_cons] at h
    simp only [Forest.mgraftF]
    by_cases hp : p < t.arity
    · rw [if_pos hp]
      have ha := arity_mgraft μ t p u hp
      rw [aparF_cons_of_lt gp t f (show q < t.arity by omega),
        aparF_cons_of_lt gp (t.mgraft μ p u) f (by omega),
        apar_mgraft_before hμ t q p u hqp hp hu]
      simp only [Forest.qbpF, hp, ↓reduceIte]
      cases apar gp t q <;> cases tpar gp u <;> cases qbp t q p <;> cases rpar gp u <;>
        cases Forest.tparF gp f <;> rfl
    · rw [if_neg hp]
      rw [isDirect_cons_of_ge (by omega)] at hd
      by_cases hq : q < t.arity
      · rw [aparF_cons_of_lt gp t f hq, aparF_cons_of_lt gp t _ hq,
          Forest.tparF_mgraftF μ gp hμ f (p - t.arity) u (by omega) hd hu]
        simp only [Forest.qbpF, hp, hq, ↓reduceIte]
        cases apar gp t q <;> cases tpar gp u <;> cases Forest.tparF gp f <;> rfl
      · rw [aparF_cons_of_ge gp t f (by omega), aparF_cons_of_ge gp t _ (by omega),
          Forest.aparF_mgraftF_before hμ f (q - t.arity) (p - t.arity) u (by omega) (by omega)
            hd hu]
        simp only [Forest.qbpF, hp, hq, ↓reduceIte]

end

end LeafPar

/-! ## Vertex counts before a leaf: grafting and merge-grafting -/

lemma vb_pos {t : Tree E} (h : t.isLeaf = false) (q : ℕ) : 1 ≤ t.vb q := by
  cases t with
  | leaf => simp at h
  | node e f => simp

mutual

/-- **The vertex count before a leaf is monotone.** -/
theorem vb_mono : ∀ (t : Tree E) (q q' : ℕ), q ≤ q' → q' < t.arity → t.vb q ≤ t.vb q'
  | .leaf, _, _, _, _ => le_rfl
  | .node e f, q, q', h, h' => by
    simp only [vb_node]
    have := Forest.vbF_mono f q q' h (by simpa using h')
    omega

/-- The forest half of `vb_mono`. -/
theorem _root_.Operad.Forest.vbF_mono : ∀ {k : ℕ} (f : Forest E k) (q q' : ℕ), q ≤ q' →
    q' < f.arityF → f.vbF q ≤ f.vbF q'
  | _, .nil, _, _, _, h' => by simp at h'
  | _, .cons t f, q, q', h, h' => by
    simp only [arityF_cons] at h'
    by_cases hq' : q' < t.arity
    · rw [vbF_cons_of_lt hq', vbF_cons_of_lt (show q < t.arity by omega)]
      exact vb_mono t q q' h hq'
    · rw [vbF_cons_of_ge (show t.arity ≤ q' by omega)]
      by_cases hq : q < t.arity
      · rw [vbF_cons_of_lt hq]
        have := vb_le_weight t q
        omega
      · rw [vbF_cons_of_ge (show t.arity ≤ q by omega)]
        have := Forest.vbF_mono f (q - t.arity) (q' - t.arity) (by omega) (by omega)
        omega

end

mutual

/-- Grafting after a leaf does not change the vertices before it. -/
theorem vb_graft_before : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (q : ℕ), q < p → p < s.arity →
    (s.graft p u).vb q = s.vb q
  | .leaf, p, _, q, hqp, h => by simp at h; omega
  | .node e f, p, u, q, hqp, h => by
    simp only [graft_node, vb_node]
    rw [Forest.vbF_graftF_before f p u q hqp (by simpa using h)]

/-- The forest half of `vb_graft_before`. -/
theorem _root_.Operad.Forest.vbF_graftF_before : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (q : ℕ), q < p → p < f.arityF → (f.graftF p u).vbF q = f.vbF q
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, p, u, q, hqp, h => by
    simp only [arityF_cons] at h
    by_cases hp : p < t.arity
    · have ha := arity_graft t p u hp
      rw [graftF_cons_of_lt _ hp, vbF_cons_of_lt (show q < (t.graft p u).arity by omega),
        vbF_cons_of_lt (show q < t.arity by omega), vb_graft_before t p u q hqp hp]
    · rw [graftF_cons_of_ge _ (by omega)]
      by_cases hq : q < t.arity
      · rw [vbF_cons_of_lt hq, vbF_cons_of_lt hq]
      · rw [vbF_cons_of_ge (by omega), vbF_cons_of_ge (by omega),
          Forest.vbF_graftF_before f (p - t.arity) u (q - t.arity) (by omega) (by omega)]

end

mutual

/-- The leaves of a grafted tree see the vertices of the outer tree before the graft point. -/
theorem vb_graft_inner : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (j : ℕ), p < s.arity →
    j < u.arity → (s.graft p u).vb (p + j) = s.vb p + u.vb j
  | .leaf, p, u, j, h, _ => by
    obtain rfl : p = 0 := by simpa using h
    simp
  | .node e f, p, u, j, h, hj => by
    simp only [graft_node, vb_node]
    rw [Forest.vbF_graftF_inner f p u j (by simpa using h) hj]
    omega

/-- The forest half of `vb_graft_inner`. -/
theorem _root_.Operad.Forest.vbF_graftF_inner : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (j : ℕ), p < f.arityF → j < u.arity →
    (f.graftF p u).vbF (p + j) = f.vbF p + u.vb j
  | _, .nil, _, _, _, h, _ => by simp at h
  | _, .cons t f, p, u, j, h, hj => by
    simp only [arityF_cons] at h
    by_cases hp : p < t.arity
    · have ha := arity_graft t p u hp
      rw [graftF_cons_of_lt _ hp, vbF_cons_of_lt (show p + j < (t.graft p u).arity by omega),
        vbF_cons_of_lt hp, vb_graft_inner t p u j hp hj]
    · rw [graftF_cons_of_ge _ (by omega), vbF_cons_of_ge (show t.arity ≤ p + j by omega),
        vbF_cons_of_ge (show t.arity ≤ p by omega),
        show p + j - t.arity = p - t.arity + j by omega,
        Forest.vbF_graftF_inner f (p - t.arity) u j (by omega) hj, Nat.add_assoc]

end

mutual

/-- The leaves after a graft point see the grafted tree in addition. -/
theorem vb_graft_after : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (q : ℕ), p < q → q < s.arity →
    (s.graft p u).vb (q - 1 + u.arity) = s.vb q + u.weight
  | .leaf, _, _, q, hpq, h => by simp at h; omega
  | .node e f, p, u, q, hpq, h => by
    simp only [graft_node, vb_node]
    rw [Forest.vbF_graftF_after f p u q hpq (by simpa using h)]
    omega

/-- The forest half of `vb_graft_after`. -/
theorem _root_.Operad.Forest.vbF_graftF_after : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (q : ℕ), p < q → q < f.arityF →
    (f.graftF p u).vbF (q - 1 + u.arity) = f.vbF q + u.weight
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, p, u, q, hpq, h => by
    simp only [arityF_cons] at h
    by_cases hp : p < t.arity
    · have ha := arity_graft t p u hp
      have hw := weight_graft t p u hp
      rw [graftF_cons_of_lt _ hp]
      by_cases hq : q < t.arity
      · rw [vbF_cons_of_lt (show q - 1 + u.arity < (t.graft p u).arity by omega),
          vbF_cons_of_lt hq, vb_graft_after t p u q hpq hq]
      · rw [vbF_cons_of_ge (show (t.graft p u).arity ≤ q - 1 + u.arity by omega),
          vbF_cons_of_ge (show t.arity ≤ q by omega),
          show q - 1 + u.arity - (t.graft p u).arity = q - t.arity by omega, hw]
        omega
    · rw [graftF_cons_of_ge _ (by omega),
        vbF_cons_of_ge (show t.arity ≤ q - 1 + u.arity by omega),
        vbF_cons_of_ge (show t.arity ≤ q by omega),
        show q - 1 + u.arity - t.arity = q - t.arity - 1 + u.arity by omega,
        Forest.vbF_graftF_after f (p - t.arity) u (q - t.arity) (by omega) (by omega)]
      omega

end

mutual

/-- Merge-grafting after a leaf does not change the vertices before it. -/
theorem vb_mgraft_before : ∀ (s : Tree E) (q p : ℕ) (u : Tree E), q < p → p < s.arity →
    (s.mgraft μ p u).vb q = s.vb q
  | .leaf, _, p, _, hqp, h => by simp at h; omega
  | .node e f, q, p, u, hqp, h => by
    rw [mgraft_node]
    split_ifs with hd
    · cases u with
      | leaf => rfl
      | node e' g =>
        have hp : p < f.arityF := by simpa using h
        have ho := offset_childIdx_of_isDirect f p hp hd
        simp only [mergeRoot, vb_node]
        rw [vbF_splice_before f _ g q (by omega)]
    · simp only [vb_node]
      rw [Forest.vbF_mgraftF_before f q p u hqp (by simpa using h)]

/-- The forest half of `vb_mgraft_before`. -/
theorem _root_.Operad.Forest.vbF_mgraftF_before : ∀ {k : ℕ} (f : Forest E k) (q p : ℕ)
    (u : Tree E), q < p → p < f.arityF → (f.mgraftF μ p u).vbF q = f.vbF q
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, q, p, u, hqp, h => by
    simp only [arityF_cons] at h
    simp only [Forest.mgraftF]
    split_ifs with hp
    · have ha := arity_mgraft μ t p u hp
      rw [vbF_cons_of_lt (show q < (t.mgraft μ p u).arity by omega),
        vbF_cons_of_lt (show q < t.arity by omega), vb_mgraft_before t q p u hqp hp]
    · by_cases hq : q < t.arity
      · rw [vbF_cons_of_lt hq, vbF_cons_of_lt hq]
      · rw [vbF_cons_of_ge (by omega), vbF_cons_of_ge (by omega),
          Forest.vbF_mgraftF_before f (q - t.arity) (p - t.arity) u (by omega) (by omega)]

end

mutual

/-- The leaves of a merge-grafted tree see the merged vertex once. -/
theorem vb_mgraft_inner : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (j : ℕ), p < s.arity →
    j < u.arity → s.isLeaf = false → u.isLeaf = false →
    (s.mgraft μ p u).vb (p + j) + 1 = s.vb p + u.vb j
  | .leaf, _, _, _, _, _, hs, _ => by simp at hs
  | .node e f, p, u, j, h, hj, _, hu => by
    rw [mgraft_node]
    split_ifs with hd
    · cases u with
      | leaf => simp at hu
      | node e' g =>
        have hp : p < f.arityF := by simpa using h
        have hc := offset_childIdx_le f p hp
        have ho := offset_childIdx_of_isDirect f p hp hd
        simp only [mergeRoot, vb_node]
        rw [show p + j = f.offset (f.childIdx p) + j by rw [ho],
          vbF_splice_inner f _ g j hc.2.2 (isLeaf_get_of_isDirect f p hp hd)
            (by simpa using hj), ho]
        omega
    · simp only [vb_node]
      have := Forest.vbF_mgraftF_inner f p u j (by simpa using h) hj hd hu
      omega

/-- The forest half of `vb_mgraft_inner`. -/
theorem _root_.Operad.Forest.vbF_mgraftF_inner : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (j : ℕ), p < f.arityF → j < u.arity → ¬ f.isDirect p = true →
    u.isLeaf = false → (f.mgraftF μ p u).vbF (p + j) + 1 = f.vbF p + u.vb j
  | _, .nil, _, _, _, h, _, _, _ => by simp at h
  | _, .cons t f, p, u, j, h, hj, hd, hu => by
    simp only [arityF_cons] at h
    simp only [Forest.mgraftF]
    split_ifs with hp
    · rw [isDirect_cons_of_lt hp] at hd
      have ha := arity_mgraft μ t p u hp
      rw [vbF_cons_of_lt (show p + j < (t.mgraft μ p u).arity by omega), vbF_cons_of_lt hp,
        vb_mgraft_inner t p u j hp hj (by simpa using hd) hu]
    · rw [isDirect_cons_of_ge (by omega)] at hd
      rw [vbF_cons_of_ge (show t.arity ≤ p + j by omega),
        vbF_cons_of_ge (show t.arity ≤ p by omega),
        show p + j - t.arity = p - t.arity + j by omega]
      have := Forest.vbF_mgraftF_inner f (p - t.arity) u j (by omega) hj hd hu
      omega

end

mutual

/-- The leaves after a merge-graft point see the merged tree, without its root. -/
theorem vb_mgraft_after : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (q : ℕ), p < q → q < s.arity →
    u.isLeaf = false → (s.mgraft μ p u).vb (q - 1 + u.arity) + 1 = s.vb q + u.weight
  | .leaf, _, _, q, hpq, h, _ => by simp at h; omega
  | .node e f, p, u, q, hpq, h, hu => by
    rw [mgraft_node]
    split_ifs with hd
    · cases u with
      | leaf => simp at hu
      | node e' g =>
        have hp : p < f.arityF := by simp at h; omega
        have hc := offset_childIdx_le f p hp
        have ho := offset_childIdx_of_isDirect f p hp hd
        simp only [mergeRoot, vb_node, arity_node, weight_node]
        rw [vbF_splice_after f _ g q hc.2.2 (isLeaf_get_of_isDirect f p hp hd) (by omega)
          (by simpa using h)]
        omega
    · simp only [vb_node]
      have := Forest.vbF_mgraftF_after f p u q hpq (by simpa using h) hd hu
      omega

/-- The forest half of `vb_mgraft_after`. -/
theorem _root_.Operad.Forest.vbF_mgraftF_after : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (q : ℕ), p < q → q < f.arityF → ¬ f.isDirect p = true → u.isLeaf = false →
    (f.mgraftF μ p u).vbF (q - 1 + u.arity) + 1 = f.vbF q + u.weight
  | _, .nil, _, _, _, _, h, _, _ => by simp at h
  | _, .cons t f, p, u, q, hpq, h, hd, hu => by
    simp only [arityF_cons] at h
    simp only [Forest.mgraftF]
    split_ifs with hp
    · rw [isDirect_cons_of_lt hp] at hd
      have ht : t.isLeaf = false := by simpa using hd
      have ha := arity_mgraft μ t p u hp
      have hw := weight_mgraft μ t p u hp ht hu
      by_cases hq : q < t.arity
      · rw [vbF_cons_of_lt (show q - 1 + u.arity < (t.mgraft μ p u).arity by omega),
          vbF_cons_of_lt hq, vb_mgraft_after t p u q hpq hq hu]
      · rw [vbF_cons_of_ge (show (t.mgraft μ p u).arity ≤ q - 1 + u.arity by omega),
          vbF_cons_of_ge (show t.arity ≤ q by omega),
          show q - 1 + u.arity - (t.mgraft μ p u).arity = q - t.arity by omega]
        omega
    · rw [isDirect_cons_of_ge (by omega)] at hd
      rw [vbF_cons_of_ge (show t.arity ≤ q - 1 + u.arity by omega),
        vbF_cons_of_ge (show t.arity ≤ q by omega),
        show q - 1 + u.arity - t.arity = q - t.arity - 1 + u.arity by omega]
      have := Forest.vbF_mgraftF_after f (p - t.arity) u (q - t.arity) (by omega) (by omega)
        hd hu
      omega

end

/-! ## Grafting: parities relative to the vertex carrying a leaf -/

section GraftPar

variable (gp : ∀ k, E k → Bool)

mutual

/-- Grafting after a leaf does not change the vertices before its vertex. -/
theorem lpar_graft_after : ∀ (s : Tree E) (q : ℕ) (u : Tree E) (p : ℕ), p < q →
    q < s.arity → lpar gp (s.graft q u) p = lpar gp s p
  | .leaf, q, _, _, hpq, h => by simp at h; omega
  | .node e f, q, u, p, hpq, h => by
    have hf : q < f.arityF := by simpa using h
    obtain ⟨h1, -⟩ := isDirect_childIdx_graftF_after f p q u hpq hf
    simp only [graft_node, lpar_node, h1]
    rw [Forest.lparF_graftF_after f q u p hpq hf]

/-- The forest half of `lpar_graft_after`. -/
theorem _root_.Operad.Forest.lparF_graftF_after : ∀ {k : ℕ} (f : Forest E k) (q : ℕ)
    (u : Tree E) (p : ℕ), p < q → q < f.arityF →
    Forest.lparF gp (f.graftF q u) p = Forest.lparF gp f p
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, q, u, p, hpq, h => by
    simp only [arityF_cons] at h
    by_cases hq : q < t.arity
    · have ha := arity_graft t q u hq
      rw [graftF_cons_of_lt _ hq, lparF_cons_of_lt gp (t.graft q u) f (by omega),
        lparF_cons_of_lt gp t f (by omega), lpar_graft_after t q u p hpq hq]
    · rw [graftF_cons_of_ge _ (by omega)]
      by_cases hp : p < t.arity
      · rw [lparF_cons_of_lt gp t _ hp, lparF_cons_of_lt gp t f hp]
      · rw [lparF_cons_of_ge gp t _ (by omega), lparF_cons_of_ge gp t f (by omega),
          Forest.lparF_graftF_after f (q - t.arity) u (p - t.arity) (by omega) (by omega)]

end

mutual

/-- Grafting after a leaf does not change the vertices between its vertex and itself. -/
theorem mpar_graft_after : ∀ (s : Tree E) (q : ℕ) (u : Tree E) (p : ℕ), p < q →
    q < s.arity → mpar gp (s.graft q u) p = mpar gp s p
  | .leaf, q, _, _, hpq, h => by simp at h; omega
  | .node e f, q, u, p, hpq, h => by
    have hf : q < f.arityF := by simpa using h
    obtain ⟨h1, -⟩ := isDirect_childIdx_graftF_after f p q u hpq hf
    simp only [graft_node, mpar_node, h1]
    split_ifs
    · rw [Forest.tparF_graftF gp f q u hf, Forest.aparF_graftF_before gp f q u p hpq hf]
      cases Forest.tparF gp f <;> cases Forest.aparF gp f p <;> cases tpar gp u <;> rfl
    · exact Forest.mparF_graftF_after f q u p hpq hf

/-- The forest half of `mpar_graft_after`. -/
theorem _root_.Operad.Forest.mparF_graftF_after : ∀ {k : ℕ} (f : Forest E k) (q : ℕ)
    (u : Tree E) (p : ℕ), p < q → q < f.arityF →
    Forest.mparF gp (f.graftF q u) p = Forest.mparF gp f p
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, q, u, p, hpq, h => by
    simp only [arityF_cons] at h
    by_cases hq : q < t.arity
    · have ha := arity_graft t q u hq
      rw [graftF_cons_of_lt _ hq, mparF_cons_of_lt gp (t.graft q u) f (by omega),
        mparF_cons_of_lt gp t f (by omega), mpar_graft_after t q u p hpq hq]
    · rw [graftF_cons_of_ge _ (by omega)]
      by_cases hp : p < t.arity
      · rw [mparF_cons_of_lt gp t _ hp, mparF_cons_of_lt gp t f hp]
      · rw [mparF_cons_of_ge gp t _ (by omega), mparF_cons_of_ge gp t f (by omega),
          Forest.mparF_graftF_after f (q - t.arity) u (p - t.arity) (by omega) (by omega)]

end

mutual

/-- **The vertex carrying a leaf of a grafted tree** is in the grafted tree, after the vertices of
the outer tree before the graft point. -/
theorem lpar_graft_inner : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (j : ℕ), p < s.arity →
    j < u.arity → u.isLeaf = false →
    lpar gp (s.graft p u) (p + j) = xor (xor (tpar gp s) (apar gp s p)) (lpar gp u j)
  | .leaf, p, u, j, h, _, _ => by
    obtain rfl : p = 0 := by simpa using h
    simp
  | .node e f, p, u, j, h, hj, hu => by
    have hf : p < f.arityF := by simpa using h
    simp only [graft_node, lpar_node, isDirect_graftF_mid f p j u hf hj hu, tpar_node, apar_node,
      Bool.false_eq_true, ↓reduceIte]
    rw [Forest.lparF_graftF_inner f p u j hf hj hu]
    cases gp _ e <;> cases Forest.tparF gp f <;> cases Forest.aparF gp f p <;>
      cases lpar gp u j <;> rfl

/-- The forest half of `lpar_graft_inner`. -/
theorem _root_.Operad.Forest.lparF_graftF_inner : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (j : ℕ), p < f.arityF → j < u.arity → u.isLeaf = false →
    Forest.lparF gp (f.graftF p u) (p + j)
      = xor (xor (Forest.tparF gp f) (Forest.aparF gp f p)) (lpar gp u j)
  | _, .nil, _, _, _, h, _, _ => by simp at h
  | _, .cons t f, p, u, j, h, hj, hu => by
    simp only [arityF_cons] at h
    by_cases hp : p < t.arity
    · have ha := arity_graft t p u hp
      rw [graftF_cons_of_lt _ hp, lparF_cons_of_lt gp (t.graft p u) f (by omega),
        lpar_graft_inner t p u j hp hj hu, tparF_cons, aparF_cons_of_lt gp t f hp]
      cases tpar gp t <;> cases apar gp t p <;> cases Forest.tparF gp f <;>
        cases lpar gp u j <;> rfl
    · rw [graftF_cons_of_ge _ (by omega),
        lparF_cons_of_ge gp t _ (show t.arity ≤ p + j by omega),
        show p + j - t.arity = p - t.arity + j by omega,
        Forest.lparF_graftF_inner f (p - t.arity) u j (by omega) hj hu, tparF_cons,
        aparF_cons_of_ge gp t f (by omega)]
      cases tpar gp t <;> cases Forest.aparF gp f (p - t.arity) <;> cases Forest.tparF gp f <;>
        cases lpar gp u j <;> rfl

end

mutual

/-- The vertices between the vertex carrying a leaf of a grafted tree and the leaf are in the
grafted tree. -/
theorem mpar_graft_inner : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (j : ℕ), p < s.arity →
    j < u.arity → u.isLeaf = false → mpar gp (s.graft p u) (p + j) = mpar gp u j
  | .leaf, p, u, j, h, _, _ => by
    obtain rfl : p = 0 := by simpa using h
    simp
  | .node e f, p, u, j, h, hj, hu => by
    have hf : p < f.arityF := by simpa using h
    simp only [graft_node, mpar_node, isDirect_graftF_mid f p j u hf hj hu, Bool.false_eq_true,
      ↓reduceIte]
    exact Forest.mparF_graftF_inner f p u j hf hj hu

/-- The forest half of `mpar_graft_inner`. -/
theorem _root_.Operad.Forest.mparF_graftF_inner : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (j : ℕ), p < f.arityF → j < u.arity → u.isLeaf = false →
    Forest.mparF gp (f.graftF p u) (p + j) = mpar gp u j
  | _, .nil, _, _, _, h, _, _ => by simp at h
  | _, .cons t f, p, u, j, h, hj, hu => by
    simp only [arityF_cons] at h
    by_cases hp : p < t.arity
    · have ha := arity_graft t p u hp
      rw [graftF_cons_of_lt _ hp, mparF_cons_of_lt gp (t.graft p u) f (by omega),
        mpar_graft_inner t p u j hp hj hu]
    · rw [graftF_cons_of_ge _ (by omega),
        mparF_cons_of_ge gp t _ (show t.arity ≤ p + j by omega),
        show p + j - t.arity = p - t.arity + j by omega,
        Forest.mparF_graftF_inner f (p - t.arity) u j (by omega) hj hu]

end

mutual

/-- **Grafting before a leaf** adds the grafted tree before its vertex, or between its vertex
and itself (`qbp`). -/
theorem lpar_graft_before : ∀ (s : Tree E) (q : ℕ) (u : Tree E) (p : ℕ), q < p →
    p < s.arity →
    lpar gp (s.graft q u) (p - 1 + u.arity) = xor (lpar gp s p) (qbp s q p && tpar gp u)
  | .leaf, _, _, p, hqp, h => by simp at h; omega
  | .node e f, q, u, p, hqp, h => by
    have hf : p < f.arityF := by simpa using h
    obtain ⟨h1, -⟩ := isDirect_childIdx_graftF_before f q p u hqp hf
    simp only [graft_node, lpar_node, qbp, h1]
    split_ifs
    · rfl
    · rw [Forest.lparF_graftF_before f q u p hqp hf]
      cases gp _ e <;> cases Forest.lparF gp f p <;> cases Forest.qbpF f q p <;>
        cases tpar gp u <;> rfl

/-- The forest half of `lpar_graft_before`. -/
theorem _root_.Operad.Forest.lparF_graftF_before : ∀ {k : ℕ} (f : Forest E k) (q : ℕ)
    (u : Tree E) (p : ℕ), q < p → p < f.arityF →
    Forest.lparF gp (f.graftF q u) (p - 1 + u.arity)
      = xor (Forest.lparF gp f p) (Forest.qbpF f q p && tpar gp u)
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, q, u, p, hqp, h => by
    simp only [arityF_cons] at h
    by_cases hq : q < t.arity
    · have ha := arity_graft t q u hq
      rw [graftF_cons_of_lt _ hq]
      by_cases hp : p < t.arity
      · rw [lparF_cons_of_lt gp (t.graft q u) f
            (show p - 1 + u.arity < (t.graft q u).arity by omega),
          lparF_cons_of_lt gp t f hp, lpar_graft_before t q u p hqp hp]
        simp only [Forest.qbpF, hp, ↓reduceIte]
      · rw [lparF_cons_of_ge gp (t.graft q u) f
            (show (t.graft q u).arity ≤ p - 1 + u.arity by omega),
          lparF_cons_of_ge gp t f (by omega), tpar_graft gp t q u hq,
          show p - 1 + u.arity - (t.graft q u).arity = p - t.arity by omega]
        simp only [Forest.qbpF, hp, hq, ↓reduceIte, Bool.true_and]
        cases tpar gp t <;> cases tpar gp u <;> cases Forest.lparF gp f (p - t.arity) <;> rfl
    · rw [graftF_cons_of_ge _ (by omega),
        lparF_cons_of_ge gp t _ (show t.arity ≤ p - 1 + u.arity by omega),
        lparF_cons_of_ge gp t f (by omega),
        show p - 1 + u.arity - t.arity = p - t.arity - 1 + u.arity by omega,
        Forest.lparF_graftF_before f (q - t.arity) u (p - t.arity) (by omega) (by omega)]
      simp only [Forest.qbpF, show ¬ p < t.arity by omega, hq, ↓reduceIte, Bool.xor_assoc]

end

mutual

/-- Grafting before a leaf, between its vertex and itself, adds the grafted tree in between. -/
theorem mpar_graft_before : ∀ (s : Tree E) (q : ℕ) (u : Tree E) (p : ℕ), q < p →
    p < s.arity →
    mpar gp (s.graft q u) (p - 1 + u.arity) = xor (mpar gp s p) (!qbp s q p && tpar gp u)
  | .leaf, _, _, p, hqp, h => by simp at h; omega
  | .node e f, q, u, p, hqp, h => by
    have hf : p < f.arityF := by simpa using h
    obtain ⟨h1, -⟩ := isDirect_childIdx_graftF_before f q p u hqp hf
    simp only [graft_node, mpar_node, qbp, h1]
    split_ifs
    · rw [Forest.tparF_graftF gp f q u (by omega),
        show p - 1 + u.arity = p + u.arity - 1 by omega,
        Forest.aparF_graftF_after gp f q u p hqp hf]
      cases Forest.tparF gp f <;> cases Forest.aparF gp f p <;> cases tpar gp u <;> rfl
    · rw [Forest.mparF_graftF_before f q u p hqp hf]

/-- The forest half of `mpar_graft_before`. -/
theorem _root_.Operad.Forest.mparF_graftF_before : ∀ {k : ℕ} (f : Forest E k) (q : ℕ)
    (u : Tree E) (p : ℕ), q < p → p < f.arityF →
    Forest.mparF gp (f.graftF q u) (p - 1 + u.arity)
      = xor (Forest.mparF gp f p) (!Forest.qbpF f q p && tpar gp u)
  | _, .nil, _, _, _, _, h => by simp at h
  | _, .cons t f, q, u, p, hqp, h => by
    simp only [arityF_cons] at h
    by_cases hq : q < t.arity
    · have ha := arity_graft t q u hq
      rw [graftF_cons_of_lt _ hq]
      by_cases hp : p < t.arity
      · rw [mparF_cons_of_lt gp (t.graft q u) f
            (show p - 1 + u.arity < (t.graft q u).arity by omega),
          mparF_cons_of_lt gp t f hp, mpar_graft_before t q u p hqp hp]
        simp only [Forest.qbpF, hp, ↓reduceIte]
      · rw [mparF_cons_of_ge gp (t.graft q u) f
            (show (t.graft q u).arity ≤ p - 1 + u.arity by omega),
          mparF_cons_of_ge gp t f (by omega),
          show p - 1 + u.arity - (t.graft q u).arity = p - t.arity by omega]
        simp only [Forest.qbpF, hp, hq, ↓reduceIte, Bool.not_true, Bool.false_and,
          Bool.xor_false]
    · rw [graftF_cons_of_ge _ (by omega),
        mparF_cons_of_ge gp t _ (show t.arity ≤ p - 1 + u.arity by omega),
        mparF_cons_of_ge gp t f (by omega),
        show p - 1 + u.arity - t.arity = p - t.arity - 1 + u.arity by omega,
        Forest.mparF_graftF_before f (q - t.arity) u (p - t.arity) (by omega) (by omega)]
      simp only [Forest.qbpF, show ¬ p < t.arity by omega, hq, ↓reduceIte]

end

end GraftPar


/-! ## Contracting an edge -/

lemma weight_pos {t : Tree E} (h : t.isLeaf = false) : 1 ≤ t.weight := by
  cases t with
  | leaf => simp at h
  | node e f => simp

lemma isLeaf_of_weight {t : Tree E} (h : 1 ≤ t.weight) : t.isLeaf = false := by
  cases t with
  | leaf => simp at h
  | node e f => rfl

lemma isLeaf_graft_left {s : Tree E} (hs : s.isLeaf = false) (q : ℕ) (b : Tree E) :
    (s.graft q b).isLeaf = false := by
  cases s with
  | leaf => simp at hs
  | node e f => rfl

/-- The data of the cut at a vertex. -/
lemma cutV_spec {t y z : Tree E} {k p : ℕ} (hk : k < t.weight) (hc : t.cutV k = (y, z, p)) :
    y.graft p z = t ∧ p < y.arity ∧ y.vb p = k ∧ z.isLeaf = false := by
  have h1 := graft_cutV t k hk
  have h2 := lt_arity_cutV t k hk
  have h3 := vb_cutV t k hk
  have h4 := isLeaf_cutV t k hk
  rw [hc] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- Below a vertex other than the root, the rest of a cut is not trivial. -/
lemma isLeaf_cutV_fst {t y z : Tree E} {k p : ℕ} (hk1 : 1 ≤ k) (hk : k < t.weight)
    (hc : t.cutV k = (y, z, p)) : y.isLeaf = false := by
  cases t with
  | leaf => simp at hk
  | node e f =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [cutV_node_succ, Prod.mk.injEq] at hc
    rw [← hc.1]
    rfl

/-- **A cut is determined by the position of its vertex.** -/
lemma graft_inj {a a' b b' : Tree E} {r r' : ℕ} (hr : r < a.arity) (hr' : r' < a'.arity)
    (hb : b.isLeaf = false) (hb' : b'.isLeaf = false) (h : a.graft r b = a'.graft r' b')
    (hv : a.vb r = a'.vb r') : a = a' ∧ b = b' ∧ r = r' := by
  have h1 := cutV_graft a r b hr hb
  have h2 := cutV_graft a' r' b' hr' hb'
  rw [h, hv, h2] at h1
  simp only [Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.1.symm, h1.2.2.symm⟩

/-- **Contracting the edge below the vertex `k`** of the preorder, `1 ≤ k`: the subtree at `k` is
cut off and merge-grafted back, merging its root into the vertex below it. -/
def contr (t : Tree E) (k : ℕ) : Tree E :=
  if k < t.weight then (t.cutV k).1.mgraft μ (t.cutV k).2.2 (t.cutV k).2.1 else t

lemma contr_eq {t y z : Tree E} {k p : ℕ} (hk : k < t.weight) (hc : t.cutV k = (y, z, p)) :
    t.contr μ k = y.mgraft μ p z := by
  rw [contr, if_pos hk, hc]

/-- **Contracting an edge keeps the leaves.** -/
lemma arity_contr (t : Tree E) (k : ℕ) : (t.contr μ k).arity = t.arity := by
  by_cases hk : k < t.weight
  · rcases hc : t.cutV k with ⟨y, z, p⟩
    obtain ⟨h1, h2, -, -⟩ := cutV_spec hk hc
    rw [contr_eq μ hk hc, ← h1, arity_graft y p z h2]
    have := arity_mgraft μ y p z h2
    omega
  · rw [contr, if_neg hk]

/-- **Contracting an edge removes a vertex.** -/
lemma weight_contr {t : Tree E} {k : ℕ} (hk1 : 1 ≤ k) (hk : k < t.weight) :
    (t.contr μ k).weight + 1 = t.weight := by
  rcases hc : t.cutV k with ⟨y, z, p⟩
  obtain ⟨h1, h2, -, h4⟩ := cutV_spec hk hc
  rw [contr_eq μ hk hc, ← h1, weight_graft y p z h2]
  exact weight_mgraft μ y p z h2 (isLeaf_cutV_fst hk1 hk hc) h4

/-- **Contracting an edge flips the parity**, for a merge function adding one. -/
lemma tpar_contr (gp : ∀ k, E k → Bool) (hμ : MergeFn.Odd gp μ) {t : Tree E} {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k < t.weight) : tpar gp (t.contr μ k) = !(tpar gp t) := by
  rcases hc : t.cutV k with ⟨y, z, p⟩
  obtain ⟨h1, h2, -, h4⟩ := cutV_spec hk hc
  rw [contr_eq μ hk hc, ← h1, tpar_graft gp y p z h2,
    tpar_mgraft μ gp hμ y p z h2 (isLeaf_cutV_fst hk1 hk hc) h4]

/-! ### Cuts of a grafted tree -/

section CutGraft

variable {y y₁ y₂ z : Tree E} {p p' k : ℕ}

lemma cutV_graft_inside (hk : k < y.weight) (hc : y.cutV k = (y₁, y₂, p'))
    (hz : z.isLeaf = false) (h1 : p' ≤ p) (h2 : p < p' + y₂.arity) :
    (y.graft p z).cutV k = (y₁, y₂.graft (p - p') z, p') := by
  obtain ⟨hy, hp', hv, hy₂⟩ := cutV_spec hk hc
  have e : y.graft p z = y₁.graft p' (y₂.graft (p - p') z) := by
    rw [← hy, ← graft_graft_seq y₁ p' y₂ (p - p') z hp' (by omega),
      show p' + (p - p') = p by omega]
  rw [e, ← hv]
  exact cutV_graft y₁ p' _ hp' (isLeaf_graft_left hy₂ _ _)

lemma cutV_graft_after (hk : k < y.weight) (hc : y.cutV k = (y₁, y₂, p'))
    (hp : p < y.arity) (h : p' + y₂.arity ≤ p) :
    (y.graft p z).cutV k = (y₁.graft (p + 1 - y₂.arity) z, y₂, p') := by
  obtain ⟨hy, hp', hv, hy₂⟩ := cutV_spec hk hc
  have ha := arity_graft y₁ p' y₂ hp'
  rw [hy] at ha
  have e : y.graft p z = (y₁.graft (p + 1 - y₂.arity) z).graft p' y₂ := by
    rw [← graft_graft_par y₁ p' y₂ (p + 1 - y₂.arity) z (by omega) (by omega), hy,
      show p + 1 - y₂.arity - 1 + y₂.arity = p by omega]
  rw [e, ← hv, ← vb_graft_before y₁ (p + 1 - y₂.arity) z p' (by omega) (by omega)]
  exact cutV_graft _ p' y₂ (by rw [arity_graft y₁ _ z (by omega)]; omega) hy₂

lemma cutV_graft_before (hk : k < y.weight) (hc : y.cutV k = (y₁, y₂, p')) (h : p < p') :
    (y.graft p z).cutV (k + z.weight) = (y₁.graft p z, y₂, p' - 1 + z.arity) := by
  obtain ⟨hy, hp', hv, hy₂⟩ := cutV_spec hk hc
  have e : y.graft p z = (y₁.graft p z).graft (p' - 1 + z.arity) y₂ := by
    rw [graft_graft_par y₁ p z p' y₂ h hp', hy]
  rw [e, ← hv, ← vb_graft_after y₁ p z p' h hp']
  exact cutV_graft _ _ y₂ (by rw [arity_graft y₁ p z (by omega)]; omega) hy₂

lemma cutV_graft_inner {z₁ z₂ : Tree E} {q k₂ : ℕ} (hp : p < y.arity) (hk : k₂ < z.weight)
    (hc : z.cutV k₂ = (z₁, z₂, q)) :
    (y.graft p z).cutV (y.vb p + k₂) = (y.graft p z₁, z₂, p + q) := by
  obtain ⟨hz, hq, hv, hz₂⟩ := cutV_spec hk hc
  have e : y.graft p z = (y.graft p z₁).graft (p + q) z₂ := by
    rw [graft_graft_seq y p z₁ q z₂ hp hq, hz]
  rw [e, ← hv, ← vb_graft_inner y p z₁ q hp hq]
  exact cutV_graft _ _ z₂ (by rw [arity_graft y p z₁ hp]; omega) hz₂

/-- A leaf comes before the subtree at a vertex exactly when the vertex does not come before the
leaf. -/
lemma lt_cutV_iff (hk : k < y.weight) (hc : y.cutV k = (y₁, y₂, p')) (hp : p < y.arity) :
    p < p' ↔ y.vb p ≤ k := by
  obtain ⟨hy, hp', hv, hy₂⟩ := cutV_spec hk hc
  have ha := arity_graft y₁ p' y₂ hp'
  rw [hy] at ha
  constructor
  · intro h
    rw [← hy, vb_graft_before y₁ p' y₂ p h hp', ← hv]
    exact vb_mono y₁ p p' h.le hp'
  · intro h
    by_contra hn
    by_cases h2 : p < p' + y₂.arity
    · have e := vb_graft_inner y₁ p' y₂ (p - p') hp' (by omega)
      rw [show p' + (p - p') = p by omega, hy] at e
      have := vb_pos hy₂ (p - p')
      omega
    · have e := vb_graft_after y₁ p' y₂ (p + 1 - y₂.arity) (by omega) (by omega)
      rw [show p + 1 - y₂.arity - 1 + y₂.arity = p by omega, hy] at e
      have := vb_mono y₁ p' (p + 1 - y₂.arity) (by omega) (by omega)
      have := weight_pos hy₂
      omega

end CutGraft

/-! ### Contracting an edge of a grafted tree -/

section ContrGraft

variable {y z : Tree E} {p k : ℕ}

/-- **Contracting an edge of the outer tree commutes with grafting.** The vertex `k` of `y` is
the vertex `k` of the grafted tree, or `k + z.weight` when it comes after the graft point. -/
theorem contr_graft_outer (hp : p < y.arity) (hz : z.isLeaf = false) (hk1 : 1 ≤ k)
    (hk : k < y.weight) :
    (y.graft p z).contr μ (k + if y.vb p ≤ k then z.weight else 0) = (y.contr μ k).graft p z := by
  rcases hc : y.cutV k with ⟨y₁, y₂, p'⟩
  obtain ⟨hy, hp', hv, hy₂⟩ := cutV_spec hk hc
  have ha := arity_graft y₁ p' y₂ hp'
  rw [hy] at ha
  have hw : k + (if y.vb p ≤ k then z.weight else 0) < (y.graft p z).weight := by
    rw [weight_graft y p z hp]; split_ifs <;> omega
  rw [contr_eq μ hk hc]
  by_cases h : p < p'
  · rw [if_pos ((lt_cutV_iff hk hc hp).1 h)] at hw ⊢
    rw [contr_eq μ hw (cutV_graft_before hk hc h)]
    exact graft_mgraft_before μ y₁ p z p' y₂ h hp'
  · rw [if_neg (mt (lt_cutV_iff hk hc hp).2 h), Nat.add_zero] at hw ⊢
    by_cases h2 : p < p' + y₂.arity
    · rw [contr_eq μ hw (cutV_graft_inside hk hc hz (by omega) h2),
        mgraft_graft_outer μ y₁ p' y₂ (p - p') z hp' (by omega) hy₂,
        show p' + (p - p') = p by omega]
    · rw [contr_eq μ hw (cutV_graft_after hk hc hp (by omega)),
        graft_mgraft_after μ y₁ p' y₂ (p + 1 - y₂.arity) z (by omega) (by omega),
        show p + 1 - y₂.arity - 1 + y₂.arity = p by omega]

/-- **Contracting an edge of the grafted tree commutes with grafting.** -/
theorem contr_graft_inner (hp : p < y.arity) (hk1 : 1 ≤ k) (hk : k < z.weight) :
    (y.graft p z).contr μ (y.vb p + k) = y.graft p (z.contr μ k) := by
  rcases hc : z.cutV k with ⟨z₁, z₂, q⟩
  obtain ⟨hz, hq, hv, hz₂⟩ := cutV_spec hk hc
  have hw : y.vb p + k < (y.graft p z).weight := by
    rw [weight_graft y p z hp]; have := vb_le_weight y p; omega
  rw [contr_eq μ hw (cutV_graft_inner hp hk hc), contr_eq μ hk hc,
    mgraft_graft_inner μ y p z₁ q z₂ hp hq (isLeaf_cutV_fst hk1 hk hc)]

/-- **Contracting the edge of the graft point is merge-grafting.** -/
theorem contr_graft_root (hp : p < y.arity) (hz : z.isLeaf = false) :
    (y.graft p z).contr μ (y.vb p) = y.mgraft μ p z := by
  have hw : y.vb p < (y.graft p z).weight := by
    rw [weight_graft y p z hp]; have := vb_le_weight y p; have := weight_pos hz; omega
  rw [contr_eq μ hw (cutV_graft y p z hp hz)]

end ContrGraft

/-- **The vertices before a leaf after contracting an edge**: one fewer when the edge comes before
the leaf. -/
theorem vb_contr {t : Tree E} {k q : ℕ} (hk1 : 1 ≤ k) (hk : k < t.weight) (hq : q < t.arity) :
    (t.contr μ k).vb q + (if k < t.vb q then 1 else 0) = t.vb q := by
  rcases hc : t.cutV k with ⟨y, z, p⟩
  obtain ⟨hy, hp, hv, hz⟩ := cutV_spec hk hc
  have hyl := isLeaf_cutV_fst hk1 hk hc
  rw [contr_eq μ hk hc]
  subst hy
  have ha := arity_graft y p z hp
  by_cases h1 : q < p
  · rw [vb_mgraft_before μ y q p z h1 hp, vb_graft_before y p z q h1 hp, if_neg]
    · rfl
    · have := vb_mono y q p h1.le hp; omega
  · by_cases h2 : q < p + z.arity
    · have e1 := vb_mgraft_inner μ y p z (q - p) hp (by omega) hyl hz
      have e2 := vb_graft_inner y p z (q - p) hp (by omega)
      rw [show p + (q - p) = q by omega] at e1 e2
      have := vb_pos hz (q - p)
      rw [e2, if_pos (by omega)]; omega
    · have e1 := vb_mgraft_after μ y p z (q + 1 - z.arity) (by omega) (by omega) hz
      have e2 := vb_graft_after y p z (q + 1 - z.arity) (by omega) (by omega)
      rw [show q + 1 - z.arity - 1 + z.arity = q by omega] at e1 e2
      have := vb_mono y p (q + 1 - z.arity) (by omega) (by omega)
      have := weight_pos hz
      rw [e2, if_pos (by omega)]; omega

/-- **Lifting a cut along a contraction**: a cut of a contracted tree is a cut of the tree, with the
contracted edge in one of its parts. -/
theorem contr_eq_graft {t a b : Tree E} {k r : ℕ} (hk1 : 1 ≤ k) (hk : k < t.weight)
    (hr : r < a.arity) (hb : b.isLeaf = false) (h : t.contr μ k = a.graft r b) :
    (∃ (a' : Tree E) (k₁ : ℕ), a'.graft r b = t ∧ r < a'.arity ∧ 1 ≤ k₁ ∧ k₁ < a'.weight ∧
        a'.contr μ k₁ = a ∧ k = k₁ + if a'.vb r ≤ k₁ then b.weight else 0) ∨
      ∃ (b' : Tree E) (k₂ : ℕ), a.graft r b' = t ∧ b'.isLeaf = false ∧ 1 ≤ k₂ ∧ k₂ < b'.weight ∧
        b'.contr μ k₂ = b ∧ k = a.vb r + k₂ := by
  have hwt := weight_contr μ hk1 hk
  rw [h, weight_graft a r b hr] at hwt
  have hva := vb_le_weight a r
  have hbw := weight_pos hb
  obtain ⟨w, hw⟩ : ∃ w, w = if a.vb r < k then a.vb r else a.vb r + 1 := ⟨_, rfl⟩
  have hw' : (w = a.vb r ∧ a.vb r < k) ∨ (w = a.vb r + 1 ∧ k ≤ a.vb r) := by
    by_cases h' : a.vb r < k
    · rw [if_pos h'] at hw; omega
    · rw [if_neg h'] at hw; omega
  have hwlt : w < t.weight := by omega
  rcases hc : t.cutV w with ⟨A, B, R⟩
  obtain ⟨hA, hR, hvA, hB⟩ := cutV_spec hwlt hc
  have hwt' := weight_graft A R B hR
  rw [hA] at hwt'
  have hBw := weight_pos hB
  by_cases hin : w < k ∧ k < w + B.weight
  · right
    have hww : w = a.vb r := by omega
    have e := contr_graft_inner μ hR (show 1 ≤ k - w by omega) (show k - w < B.weight by omega)
    rw [hvA, show w + (k - w) = k by omega, hA, h] at e
    have hcw := weight_contr μ (show 1 ≤ k - w by omega) (show k - w < B.weight by omega)
    obtain ⟨h1, h2, h3⟩ := graft_inj hr hR hb (isLeaf_of_weight (by omega)) e
      (by rw [hvA, hww])
    subst h1
    subst h3
    exact ⟨B, k - w, hA, hB, by omega, by omega, h2.symm, by omega⟩
  · left
    have hAl : A.isLeaf = false := by
      cases A with
      | leaf =>
        exfalso
        simp only [vb_leaf] at hvA
        simp only [graft_leaf] at hA
        subst hA
        omega
      | node e f => rfl
    have hAv := vb_pos hAl R
    have hAvw := vb_le_weight A R
    obtain ⟨k₁, hk₁⟩ : ∃ k₁, k₁ = if k < w then k else k - B.weight := ⟨_, rfl⟩
    have hk₁' : (k < w ∧ k₁ = k) ∨ (w ≤ k ∧ k₁ = k - B.weight) := by
      by_cases h' : k < w
      · rw [if_pos h'] at hk₁; omega
      · rw [if_neg h'] at hk₁; omega
    have hk₁1 : 1 ≤ k₁ := by omega
    have hk₁w : k₁ < A.weight := by omega
    have hkk : k = k₁ + if A.vb R ≤ k₁ then B.weight else 0 := by
      rw [hvA]; split_ifs <;> omega
    have e := contr_graft_outer μ hR hB hk₁1 hk₁w
    rw [← hkk, hA, h] at e
    have hvc := vb_contr μ hk₁1 hk₁w hR
    have hacw := weight_contr μ hk₁1 hk₁w
    rw [hvA] at hvc
    obtain ⟨h1, h2, h3⟩ := graft_inj hr (by rw [arity_contr]; exact hR) hb hB e (by
      split_ifs at hvc <;> omega)
    subst h2
    subst h3
    exact ⟨A, k₁, hA, hR, hk₁1, hk₁w, h1.symm, hkk⟩

/-! ### The sign of a contraction -/

section ContrSgn

variable (gp : ∀ k, E k → Bool)

/-- **The sign of merge-grafting** at the leaf `p` of `s` a tree with root of parity `c`: the
parity of the vertices before the vertex carrying the leaf, plus `c` times the parity of the
vertices between that vertex and the leaf. -/
def mgSgn (s : Tree E) (p : ℕ) (c : Bool) : Bool := xor (lpar gp s p) (c && mpar gp s p)

/-- **The sign of contracting the edge below the vertex `k`.** -/
def contrSgn (t : Tree E) (k : ℕ) : Bool :=
  mgSgn gp (t.cutV k).1 (t.cutV k).2.2 (rpar gp (t.cutV k).2.1)

lemma contrSgn_eq {t y z : Tree E} {k p : ℕ} (hc : t.cutV k = (y, z, p)) :
    contrSgn gp t k = mgSgn gp y p (rpar gp z) := by
  rw [contrSgn, hc]

variable {y z : Tree E} {p k : ℕ}

/-- **The sign of contracting an edge of the outer tree of a graft.** -/
theorem contrSgn_graft_outer (hμ : MergeFn.Odd gp μ) (hp : p < y.arity) (hz : z.isLeaf = false)
    (hk1 : 1 ≤ k) (hk : k < y.weight) :
    xor (tpar gp z && apar gp y p)
        (contrSgn gp (y.graft p z) (k + if y.vb p ≤ k then z.weight else 0))
      = xor (contrSgn gp y k) (tpar gp z && apar gp (y.contr μ k) p) := by
  rcases hc : y.cutV k with ⟨y₁, y₂, p'⟩
  obtain ⟨hy, hp', hv, hy₂⟩ := cutV_spec hk hc
  have ha := arity_graft y₁ p' y₂ hp'
  rw [hy] at ha
  rw [contrSgn_eq gp hc, contr_eq μ hk hc]
  by_cases h : p < p'
  · rw [if_pos ((lt_cutV_iff hk hc hp).1 h), contrSgn_eq gp (cutV_graft_before hk hc h)]
    simp only [mgSgn]
    rw [lpar_graft_before gp y₁ p z p' h hp', mpar_graft_before gp y₁ p z p' h hp',
      apar_mgraft_before μ gp hμ y₁ p p' y₂ h hp' hy₂, ← hy, apar_graft_before gp y₁ p' y₂ p h hp']
    cases tpar gp z <;> cases apar gp y₁ p <;> cases tpar gp y₂ <;> cases lpar gp y₁ p' <;>
      cases mpar gp y₁ p' <;> cases qbp y₁ p p' <;> cases rpar gp y₂ <;> rfl
  · rw [if_neg (mt (lt_cutV_iff hk hc hp).2 h), Nat.add_zero]
    by_cases h2 : p < p' + y₂.arity
    · rw [contrSgn_eq gp (cutV_graft_inside hk hc hz (by omega) h2), rpar_graft gp hy₂, ← hy,
        show p = p' + (p - p') by omega,
        apar_mgraft_inner μ gp y₁ p' y₂ (p - p') hp' (by omega) hy₂,
        apar_graft_inner gp y₁ p' y₂ (p - p') hp' (by omega)]
      exact Bool.xor_comm _ _
    · rw [contrSgn_eq gp (cutV_graft_after hk hc hp (by omega))]
      simp only [mgSgn]
      rw [lpar_graft_after gp y₁ (p + 1 - y₂.arity) z p' (by omega) (by omega),
        mpar_graft_after gp y₁ (p + 1 - y₂.arity) z p' (by omega) (by omega), ← hy,
        show p = p + 1 - y₂.arity - 1 + y₂.arity by omega,
        apar_mgraft_after μ gp y₁ p' y₂ (p + 1 - y₂.arity) (by omega) (by omega),
        show p + 1 - y₂.arity - 1 + y₂.arity = p + 1 - y₂.arity + y₂.arity - 1 by omega,
        apar_graft_after gp y₁ p' y₂ (p + 1 - y₂.arity) (by omega) (by omega)]
      exact Bool.xor_comm _ _

/-- **The sign of contracting an edge of the grafted tree.** -/
theorem contrSgn_graft_inner (hp : p < y.arity) (hk1 : 1 ≤ k) (hk : k < z.weight) :
    contrSgn gp (y.graft p z) (y.vb p + k)
      = xor (xor (tpar gp y) (apar gp y p)) (contrSgn gp z k) := by
  rcases hc : z.cutV k with ⟨z₁, z₂, q⟩
  obtain ⟨hz, hq, hv, hz₂⟩ := cutV_spec hk hc
  have hzl := isLeaf_cutV_fst hk1 hk hc
  rw [contrSgn_eq gp (cutV_graft_inner hp hk hc), contrSgn_eq gp hc]
  simp only [mgSgn]
  rw [lpar_graft_inner gp y p z₁ q hp hq hzl, mpar_graft_inner gp y p z₁ q hp hq hzl,
    Bool.xor_assoc]

/-- **The sign of contracting the edge of the graft point.** -/
theorem contrSgn_graft_root (hp : p < y.arity) (hz : z.isLeaf = false) :
    contrSgn gp (y.graft p z) (y.vb p) = mgSgn gp y p (rpar gp z) := by
  rw [contrSgn_eq gp (cutV_graft y p z hp hz)]

end ContrSgn

/-! ### Contractions of the parts of a cut -/

/-- **Contracting an edge of the outer tree of a graft, with any grafted tree.** -/
theorem contr_graft_outer' {y z : Tree E} {p k : ℕ} (hp : p < y.arity) (hk1 : 1 ≤ k)
    (hk : k < y.weight) :
    (y.graft p z).contr μ (k + if y.vb p ≤ k then z.weight else 0) = (y.contr μ k).graft p z := by
  by_cases hz : z.isLeaf = true
  · rw [eq_leaf_of_isLeaf hz, graft_leaf_right, graft_leaf_right, weight_leaf]
    simp
  · exact contr_graft_outer μ hp (by simpa using hz) hk1 hk

/-- **The sign of contracting an edge of the outer tree of a graft, with any grafted tree.** -/
theorem contrSgn_graft_outer' (gp : ∀ k, E k → Bool) (hμ : MergeFn.Odd gp μ) {y z : Tree E}
    {p k : ℕ} (hp : p < y.arity) (hk1 : 1 ≤ k) (hk : k < y.weight) :
    xor (tpar gp z && apar gp y p)
        (contrSgn gp (y.graft p z) (k + if y.vb p ≤ k then z.weight else 0))
      = xor (contrSgn gp y k) (tpar gp z && apar gp (y.contr μ k) p) := by
  by_cases hz : z.isLeaf = true
  · rw [eq_leaf_of_isLeaf hz, graft_leaf_right, weight_leaf, tpar_leaf]
    simp
  · exact contrSgn_graft_outer μ gp hμ hp (by simpa using hz) hk1 hk

/-- Contracting edges of the outer trees of two cuts at a leaf, with the same grafted tree, gives
the same trees at the same vertices only for the same cut and the same edge. -/
lemma contr_outer_inj {a a' b : Tree E} {r k k' : ℕ} (hr : r < a.arity) (hr' : r < a'.arity)
    (hb : b.isLeaf = false) (hk1 : 1 ≤ k) (hk : k < a.weight) (hk1' : 1 ≤ k')
    (hk' : k' < a'.weight) (h : a.graft r b = a'.graft r b) (hc : a.contr μ k = a'.contr μ k')
    (hi : k + (if a.vb r ≤ k then b.weight else 0) = k' + if a'.vb r ≤ k' then b.weight else 0) :
    a = a' ∧ k = k' := by
  have h1 := vb_contr μ hk1 hk hr
  have h2 := vb_contr μ hk1' hk' hr'
  rw [hc] at h1
  have hbw := weight_pos hb
  have hv : a.vb r = a'.vb r := by split_ifs at h1 h2 hi <;> omega
  obtain ⟨rfl, -, -⟩ := graft_inj hr hr' hb hb h hv
  refine ⟨rfl, ?_⟩
  split_ifs at hi <;> omega

/-- Contracting an edge of the outer tree of a cut never gives the contraction of an edge of the
grafted tree of another cut at the same leaf, at the same vertex. -/
lemma contr_outer_ne_inner {a a' b b' : Tree E} {r k₁ k₂ : ℕ} (hr : r < a.arity)
    (hb' : b'.isLeaf = false) (hk1 : 1 ≤ k₁) (hk : k₁ < a.weight) (hk₂1 : 1 ≤ k₂)
    (hk₂ : k₂ < b'.weight) (h : a.graft r b = a'.graft r b') (hc : a.contr μ k₁ = a')
    (hc' : b'.contr μ k₂ = b) (hi : k₁ + (if a.vb r ≤ k₁ then b.weight else 0) = a'.vb r + k₂) :
    False := by
  have hbw : (b'.contr μ k₂).weight + 1 = b'.weight := weight_contr μ hk₂1 hk₂
  rw [hc'] at hbw
  have hb : b.isLeaf = false := isLeaf_of_weight (by omega)
  have h1 := vb_contr μ hk1 hk hr
  rw [hc] at h1
  have haw := weight_contr μ hk1 hk
  rw [hc] at haw
  have hbpos := weight_pos hb
  by_cases hlt : k₁ < a.vb r
  · rw [if_pos hlt] at h1
    rw [if_neg (by omega)] at hi
    omega
  · rw [if_neg hlt] at h1
    rw [if_pos (by omega)] at hi
    have hr' : r < a'.arity := by rw [← hc, arity_contr]; exact hr
    obtain ⟨rfl, -, -⟩ := graft_inj hr hr' hb hb' h (by omega)
    omega

/-- Grafting at a leaf is injective in the grafted tree. -/
lemma graft_inj_right {a b b' : Tree E} {r : ℕ} (hr : r < a.arity)
    (h : a.graft r b = a.graft r b') : b = b' :=
  (graft_cancel (fun _ e => e) a a b b' r hr h rfl).2

end Tree

end Operad
