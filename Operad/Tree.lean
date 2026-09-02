/-
# Planar trees, and grafting

The free non-symmetric operad on a collection `E` of generators is the operad of planar trees
whose internal vertices of arity `k` carry a label from `E k`. This file builds the trees and
their grafting, and proves the four operad laws at the level of trees; `Operad.Free` then
linearises.

The one design decision that matters: **arity is a function, not an index.** Writing
`Tree E n` with `n` an index forces every definition to be a dependent pattern match and every
recursive call to carry a transport. Writing `Tree E` and `Tree.arity : Tree E → ℕ` keeps
grafting a plain structural recursion and moves all the arithmetic into propositions, where
`omega` can discharge it. It is the same trade that `reindex` makes in `Operad.Basic`.
-/

import Mathlib.Data.Nat.Notation

universe u v

namespace Operad

/-! A planar tree whose internal vertices are labelled by `E`, together with the forests of
subtrees hanging below such a vertex. `Forest E k` is a list of exactly `k` trees. -/
mutual

/-- A planar tree with vertices labelled by `E`. -/
inductive Tree (E : ℕ → Type v) : Type v where
  /-- The trivial tree: a single leaf, the operadic identity. -/
  | leaf : Tree E
  /-- A vertex labelled by a `k`-ary generator, with `k` subtrees below it. -/
  | node {k : ℕ} (e : E k) (f : Forest E k) : Tree E

/-- A list of exactly `k` planar trees. -/
inductive Forest (E : ℕ → Type v) : ℕ → Type v where
  /-- The empty forest. -/
  | nil : Forest E 0
  /-- Prepend a tree to a forest. -/
  | cons {k : ℕ} (t : Tree E) (f : Forest E k) : Forest E (k + 1)

end

namespace Tree

variable {E : ℕ → Type v}

/-! The number of leaves of a tree, and of a forest. This is the operadic arity. -/
mutual

/-- The number of leaves of a tree. -/
def arity : Tree E → ℕ
  | .leaf => 1
  | .node _ f => f.arityF

/-- The total number of leaves of a forest. -/
def _root_.Operad.Forest.arityF : ∀ {k : ℕ}, Forest E k → ℕ
  | _, .nil => 0
  | _, .cons t f => t.arity + f.arityF

end

@[simp] lemma arity_leaf : (Tree.leaf (E := E)).arity = 1 := rfl

@[simp] lemma arity_node {k : ℕ} (e : E k) (f : Forest E k) :
    (Tree.node e f).arity = f.arityF := rfl

@[simp] lemma arityF_nil : (Forest.nil (E := E)).arityF = 0 := rfl

@[simp] lemma arityF_cons {k : ℕ} (t : Tree E) (f : Forest E k) :
    (Forest.cons t f).arityF = t.arity + f.arityF := rfl

/-! Grafting: replace the leaf in position `i` (counting from the left, from zero) by the tree
`s`. Positions at or beyond `arity` are out of range; the value there is junk, and every lemma
below carries the hypothesis `i < arity` that rules it out. -/
mutual

/-- Replace the `i`-th leaf of a tree by `s`. -/
def graft : Tree E → ℕ → Tree E → Tree E
  | .leaf, _, s => s
  | .node e f, i, s => .node e (f.graftF i s)

/-- Replace the `i`-th leaf of a forest by `s`. -/
def _root_.Operad.Forest.graftF : ∀ {k : ℕ}, Forest E k → ℕ → Tree E → Forest E k
  | _, .nil, _, _ => .nil
  | _, .cons t f, i, s =>
      if i < t.arity then .cons (t.graft i s) f
      else .cons t (f.graftF (i - t.arity) s)

end

@[simp] lemma graft_leaf (i : ℕ) (s : Tree E) : (Tree.leaf (E := E)).graft i s = s := rfl

@[simp] lemma graft_node {k : ℕ} (e : E k) (f : Forest E k) (i : ℕ) (s : Tree E) :
    (Tree.node e f).graft i s = .node e (f.graftF i s) := rfl

@[simp] lemma graftF_nil (i : ℕ) (s : Tree E) :
    (Forest.nil (E := E)).graftF i s = .nil := rfl

lemma graftF_cons {k : ℕ} (t : Tree E) (f : Forest E k) (i : ℕ) (s : Tree E) :
    (Forest.cons t f).graftF i s =
      if i < t.arity then .cons (t.graft i s) f else .cons t (f.graftF (i - t.arity) s) := rfl

lemma graftF_cons_of_lt {k : ℕ} {t : Tree E} {f : Forest E k} {i : ℕ} (s : Tree E)
    (h : i < t.arity) : (Forest.cons t f).graftF i s = .cons (t.graft i s) f := by
  rw [graftF_cons, if_pos h]

lemma graftF_cons_of_ge {k : ℕ} {t : Tree E} {f : Forest E k} {i : ℕ} (s : Tree E)
    (h : t.arity ≤ i) : (Forest.cons t f).graftF i s = .cons t (f.graftF (i - t.arity) s) := by
  rw [graftF_cons, if_neg (by omega)]


/-! ### The arity of a graft

Grafting removes one leaf and adds the leaves of the grafted tree. Everything below is a mutual
induction over trees and forests; the forest half always splits on whether the target leaf lies
in the head tree or further along. -/

mutual

/-- Grafting replaces one leaf by `s`, so the arity drops by one and gains `s.arity`. -/
theorem arity_graft : ∀ (t : Tree E) (i : ℕ) (s : Tree E), i < t.arity →
    (t.graft i s).arity = t.arity - 1 + s.arity
  | .leaf, _, s, _ => by simp
  | .node _ f, i, s, h => by
      simp only [graft_node, arity_node]
      exact Forest.arityF_graftF f i s h

/-- The forest half of `arity_graft`. -/
theorem _root_.Operad.Forest.arityF_graftF : ∀ {k : ℕ} (f : Forest E k) (i : ℕ) (s : Tree E),
    i < f.arityF → (f.graftF i s).arityF = f.arityF - 1 + s.arity
  | _, .nil, _, _, h => by simp at h
  | _, .cons t f, i, s, h => by
      simp only [arityF_cons] at h
      by_cases hlt : i < t.arity
      · rw [graftF_cons_of_lt s hlt]
        simp only [arityF_cons]
        rw [arity_graft t i s hlt]
        omega
      · rw [graftF_cons_of_ge s (by omega)]
        simp only [arityF_cons]
        rw [Forest.arityF_graftF f (i - t.arity) s (by omega)]
        omega

end

/-! ### The unit laws -/

mutual

/-- **Right unit.** Grafting a bare leaf changes nothing, at any position. -/
theorem graft_leaf_right : ∀ (t : Tree E) (i : ℕ), t.graft i .leaf = t
  | .leaf, _ => rfl
  | .node _ f, i => by rw [graft_node, Forest.graftF_leaf f i]

/-- The forest half of `graft_leaf_right`. -/
theorem _root_.Operad.Forest.graftF_leaf : ∀ {k : ℕ} (f : Forest E k) (i : ℕ),
    f.graftF i .leaf = f
  | _, .nil, _ => rfl
  | _, .cons t f, i => by
      by_cases hlt : i < t.arity
      · rw [graftF_cons_of_lt _ hlt, graft_leaf_right t i]
      · rw [graftF_cons_of_ge _ (by omega), Forest.graftF_leaf f (i - t.arity)]

end

/-- **Left unit.** A leaf is the operadic identity. -/
@[simp] theorem leaf_graft (s : Tree E) : (Tree.leaf (E := E)).graft 0 s = s := rfl

/-! ### Sequential associativity

Grafting `s` at leaf `i` puts the leaves of `s` in positions `i, …, i + s.arity - 1`, so leaf `j`
of `s` is leaf `i + j` of the composite. -/

mutual

/-- **Sequential associativity**: grafting into a tree that was itself just grafted in. -/
theorem graft_graft_seq : ∀ (t : Tree E) (i : ℕ) (s : Tree E) (j : ℕ) (u : Tree E),
    i < t.arity → j < s.arity →
    (t.graft i s).graft (i + j) u = t.graft i (s.graft j u)
  | .leaf, i, s, j, u, h, _ => by
      obtain rfl : i = 0 := by simpa using h
      simp
  | .node _ f, i, s, j, u, h, hj => by
      simp only [graft_node]
      rw [Forest.graftF_graftF_seq f i s j u h hj]

/-- The forest half of `graft_graft_seq`. -/
theorem _root_.Operad.Forest.graftF_graftF_seq :
    ∀ {k : ℕ} (f : Forest E k) (i : ℕ) (s : Tree E) (j : ℕ) (u : Tree E),
    i < f.arityF → j < s.arity →
    (f.graftF i s).graftF (i + j) u = f.graftF i (s.graft j u)
  | _, .nil, _, _, _, _, h, _ => by simp at h
  | _, .cons t f, i, s, j, u, h, hj => by
      simp only [arityF_cons] at h
      by_cases hlt : i < t.arity
      · have hsub : i + j < (t.graft i s).arity := by
          rw [arity_graft t i s hlt]; omega
        rw [graftF_cons_of_lt s hlt, graftF_cons_of_lt u hsub,
          graftF_cons_of_lt (s.graft j u) hlt, graft_graft_seq t i s j u hlt hj]
      · have hge : t.arity ≤ i + j := by omega
        rw [graftF_cons_of_ge s (by omega), graftF_cons_of_ge u hge,
          graftF_cons_of_ge (s.graft j u) (by omega),
          show i + j - t.arity = (i - t.arity) + j by omega,
          Forest.graftF_graftF_seq f (i - t.arity) s j u (by omega) hj]

end

/-! ### Parallel associativity

Grafting at two distinct leaves, in either order. Grafting `s` at leaf `i` shifts every later
leaf by `s.arity - 1`, so the slot that was `i'` becomes `i' - 1 + s.arity`. -/

mutual

/-- **Parallel associativity**: grafting at two distinct slots commutes, after the shift that
the first graft induces on the second slot. -/
theorem graft_graft_par : ∀ (t : Tree E) (i : ℕ) (s : Tree E) (i' : ℕ) (u : Tree E),
    i < i' → i' < t.arity →
    (t.graft i s).graft (i' - 1 + s.arity) u = (t.graft i' u).graft i s
  | .leaf, _, _, _, _, h, h' => by simp only [arity_leaf] at h'; omega
  | .node _ f, i, s, i', u, h, h' => by
      simp only [graft_node]
      rw [Forest.graftF_graftF_par f i s i' u h h']

/-- The forest half of `graft_graft_par`. -/
theorem _root_.Operad.Forest.graftF_graftF_par :
    ∀ {k : ℕ} (f : Forest E k) (i : ℕ) (s : Tree E) (i' : ℕ) (u : Tree E),
    i < i' → i' < f.arityF →
    (f.graftF i s).graftF (i' - 1 + s.arity) u = (f.graftF i' u).graftF i s
  | _, .nil, _, _, _, _, _, h' => by simp at h'
  | _, .cons t f, i, s, i', u, h, h' => by
      simp only [arityF_cons] at h'
      by_cases hi' : i' < t.arity
      · -- Both slots lie in the head tree.
        have hi : i < t.arity := by omega
        have hL : i' - 1 + s.arity < (t.graft i s).arity := by
          rw [arity_graft t i s hi]; omega
        have hR : i < (t.graft i' u).arity := by
          rw [arity_graft t i' u hi']; omega
        rw [graftF_cons_of_lt s hi, graftF_cons_of_lt u hL, graftF_cons_of_lt u hi',
          graftF_cons_of_lt s hR, graft_graft_par t i s i' u h hi']
      · by_cases hi : i < t.arity
        · -- The head tree holds `i` only: the two grafts touch disjoint parts of the forest.
          have hL : (t.graft i s).arity ≤ i' - 1 + s.arity := by
            rw [arity_graft t i s hi]; omega
          rw [graftF_cons_of_lt s hi, graftF_cons_of_ge u hL,
            graftF_cons_of_ge u (by omega), graftF_cons_of_lt s hi,
            arity_graft t i s hi,
            show i' - 1 + s.arity - (t.arity - 1 + s.arity) = i' - t.arity by omega]
        · -- Both slots lie further along the forest.
          rw [graftF_cons_of_ge s (by omega), graftF_cons_of_ge u (by omega),
            graftF_cons_of_ge u (by omega), graftF_cons_of_ge s (by omega),
            show i' - 1 + s.arity - t.arity = (i' - t.arity) - 1 + s.arity by omega,
            Forest.graftF_graftF_par f (i - t.arity) s (i' - t.arity) u (by omega) (by omega)]

end


/-! ### Weight

The weight of a tree is its number of internal vertices. It is the grading that Koszul duality
uses: grafting *adds* weights, because a graft replaces a leaf — which has weight zero — by the
grafted tree. Unlike arity, weight is unchanged by where the graft happens. -/

mutual

/-- The number of internal vertices of a tree. -/
def weight : Tree E → ℕ
  | .leaf => 0
  | .node _ f => f.weightF + 1

/-- The total number of internal vertices of a forest. -/
def _root_.Operad.Forest.weightF : ∀ {k : ℕ}, Forest E k → ℕ
  | _, .nil => 0
  | _, .cons t f => t.weight + f.weightF

end

@[simp] lemma weight_leaf : (Tree.leaf (E := E)).weight = 0 := rfl

@[simp] lemma weight_node {k : ℕ} (e : E k) (f : Forest E k) :
    (Tree.node e f).weight = f.weightF + 1 := rfl

@[simp] lemma weightF_nil : (Forest.nil (E := E)).weightF = 0 := rfl

@[simp] lemma weightF_cons {k : ℕ} (t : Tree E) (f : Forest E k) :
    (Forest.cons t f).weightF = t.weight + f.weightF := rfl

mutual

/-- **Grafting adds weights.** -/
theorem weight_graft : ∀ (t : Tree E) (i : ℕ) (s : Tree E), i < t.arity →
    (t.graft i s).weight = t.weight + s.weight
  | .leaf, _, s, _ => by simp
  | .node _ f, i, s, h => by
      simp only [graft_node, weight_node]
      rw [Forest.weightF_graftF f i s h]
      omega

/-- The forest half of `weight_graft`. -/
theorem _root_.Operad.Forest.weightF_graftF : ∀ {k : ℕ} (f : Forest E k) (i : ℕ) (s : Tree E),
    i < f.arityF → (f.graftF i s).weightF = f.weightF + s.weight
  | _, .nil, _, _, h => by simp at h
  | _, .cons t f, i, s, h => by
      simp only [arityF_cons] at h
      by_cases hlt : i < t.arity
      · rw [graftF_cons_of_lt s hlt]
        simp only [weightF_cons]
        rw [weight_graft t i s hlt]
        omega
      · rw [graftF_cons_of_ge s (by omega)]
        simp only [weightF_cons]
        rw [Forest.weightF_graftF f (i - t.arity) s (by omega)]
        omega

end

end Tree

end Operad
