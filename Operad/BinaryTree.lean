/-
# Planar binary trees, and unique factorization

The free non-symmetric set operad on a set `E` of binary operations is the set of planar binary
trees with vertices labelled by `E`, composed by grafting a tree onto a leaf. `Operad.Tree` builds
planar trees for generators of every arity; this file specializes to binary generators, where the
one extra fact needed for deformation theory holds:

**unique factorization** (`graft_inj`): a tree is a graft `t₁ ∘ₐ t₂` in at most one way once the
slot `a` and the arity of `t₂` are fixed.

It is the fact that makes the linear dual of the free operad a cooperad, and the cochains on
trees an operad (`Operad.TreeConv`). Arity and weight are functions, not indices, as in
`Operad.Tree`: a binary tree with `n` leaves has `n - 1` vertices (`weight_add_one`).
-/
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Image

universe v

namespace Operad

/-- **A planar binary tree** with vertices labelled by `E`. -/
inductive BTree (E : Type v) : Type v where
  /-- The trivial tree: a single leaf, the operadic identity. -/
  | leaf : BTree E
  /-- A vertex labelled by a binary generator, with a left and a right subtree. -/
  | node (e : E) (l r : BTree E) : BTree E
  deriving DecidableEq

namespace BTree

variable {E : Type v}

/-- The number of leaves: the operadic arity. -/
def arity : BTree E → ℕ
  | leaf => 1
  | node _ l r => l.arity + r.arity

/-- The number of vertices: the weight. -/
def weight : BTree E → ℕ
  | leaf => 0
  | node _ l r => l.weight + r.weight + 1

@[simp] lemma arity_leaf : (leaf : BTree E).arity = 1 := rfl
@[simp] lemma arity_node (e : E) (l r : BTree E) : (node e l r).arity = l.arity + r.arity := rfl
@[simp] lemma weight_leaf : (leaf : BTree E).weight = 0 := rfl
@[simp] lemma weight_node (e : E) (l r : BTree E) :
    (node e l r).weight = l.weight + r.weight + 1 := rfl

lemma arity_pos : ∀ t : BTree E, 0 < t.arity
  | leaf => Nat.one_pos
  | node _ l _ => Nat.lt_of_lt_of_le (arity_pos l) (Nat.le_add_right _ _)

/-- **A binary tree with `n` leaves has `n - 1` vertices.** -/
lemma weight_add_one : ∀ t : BTree E, t.weight + 1 = t.arity
  | leaf => rfl
  | node _ l r => by
    have hl := weight_add_one l
    have hr := weight_add_one r
    simp only [weight_node, arity_node]
    omega

/-- The only tree of arity one is the leaf. -/
lemma eq_leaf_of_arity_eq_one : ∀ {t : BTree E}, t.arity = 1 → t = leaf
  | leaf, _ => rfl
  | node _ l r, h => by
    have := arity_pos l
    have := arity_pos r
    simp only [arity_node] at h
    omega

/-- Replace the leaf in position `i` (counting from the left, from zero) by `s`. Out of range, the
value is junk; every lemma carries `i < arity`. -/
def graft : BTree E → ℕ → BTree E → BTree E
  | leaf, _, s => s
  | node e l r, i, s =>
    if i < l.arity then node e (l.graft i s) r else node e l (r.graft (i - l.arity) s)

@[simp] lemma graft_leaf (i : ℕ) (s : BTree E) : (leaf : BTree E).graft i s = s := rfl

lemma graft_node (e : E) (l r : BTree E) (i : ℕ) (s : BTree E) :
    (node e l r).graft i s =
      if i < l.arity then node e (l.graft i s) r else node e l (r.graft (i - l.arity) s) := rfl

lemma graft_node_of_lt {e : E} {l : BTree E} (r : BTree E) {i : ℕ} (s : BTree E)
    (h : i < l.arity) : (node e l r).graft i s = node e (l.graft i s) r := by
  rw [graft_node, if_pos h]

lemma graft_node_of_ge {e : E} (l : BTree E) {r : BTree E} {i : ℕ} (s : BTree E)
    (h : l.arity ≤ i) : (node e l r).graft i s = node e l (r.graft (i - l.arity) s) := by
  rw [graft_node, if_neg (by omega)]

/-- Grafting replaces one leaf by `s`. -/
theorem arity_graft : ∀ (t : BTree E) (i : ℕ) (s : BTree E), i < t.arity →
    (t.graft i s).arity + 1 = t.arity + s.arity
  | leaf, _, s, _ => by simp only [graft_leaf, arity_leaf]; omega
  | node e l r, i, s, h => by
    simp only [arity_node] at h
    by_cases hi : i < l.arity
    · rw [graft_node_of_lt r s hi]
      have := arity_graft l i s hi
      simp only [arity_node]
      omega
    · rw [graft_node_of_ge l s (by omega)]
      have := arity_graft r (i - l.arity) s (by omega)
      simp only [arity_node]
      omega

/-- **Grafting adds weights.** -/
theorem weight_graft : ∀ (t : BTree E) (i : ℕ) (s : BTree E), i < t.arity →
    (t.graft i s).weight = t.weight + s.weight
  | leaf, _, s, _ => by simp
  | node e l r, i, s, h => by
    simp only [arity_node] at h
    by_cases hi : i < l.arity
    · rw [graft_node_of_lt r s hi]
      have := weight_graft l i s hi
      simp only [weight_node]
      omega
    · rw [graft_node_of_ge l s (by omega)]
      have := weight_graft r (i - l.arity) s (by omega)
      simp only [weight_node]
      omega

/-- **Right unit.** Grafting a bare leaf changes nothing. -/
theorem graft_leaf_right : ∀ (t : BTree E) (i : ℕ), t.graft i leaf = t
  | leaf, _ => rfl
  | node e l r, i => by
    by_cases hi : i < l.arity
    · rw [graft_node_of_lt r _ hi, graft_leaf_right l i]
    · rw [graft_node_of_ge l _ (by omega), graft_leaf_right r]

/-- **Sequential associativity**: grafting into a tree that was itself just grafted in. -/
theorem graft_graft_seq : ∀ (t : BTree E) (i : ℕ) (s : BTree E) (j : ℕ) (u : BTree E),
    i < t.arity → j < s.arity → (t.graft i s).graft (i + j) u = t.graft i (s.graft j u)
  | leaf, i, s, j, u, h, _ => by
    obtain rfl : i = 0 := by simp only [arity_leaf] at h; omega
    simp
  | node e l r, i, s, j, u, h, hj => by
    simp only [arity_node] at h
    by_cases hi : i < l.arity
    · have hl := arity_graft l i s hi
      rw [graft_node_of_lt r s hi, graft_node_of_lt r u (by omega),
        graft_node_of_lt r (s.graft j u) hi, graft_graft_seq l i s j u hi hj]
    · rw [graft_node_of_ge l s (by omega), graft_node_of_ge l u (by omega),
        graft_node_of_ge l (s.graft j u) (by omega),
        show i + j - l.arity = (i - l.arity) + j by omega,
        graft_graft_seq r (i - l.arity) s j u (by omega) hj]

/-- **Parallel associativity**: grafting at two distinct leaves commutes, after the shift the
first graft induces on the second slot. -/
theorem graft_graft_par : ∀ (t : BTree E) (i : ℕ) (s : BTree E) (i' : ℕ) (u : BTree E),
    i < i' → i' < t.arity → (t.graft i s).graft (i' - 1 + s.arity) u = (t.graft i' u).graft i s
  | leaf, _, _, _, _, h, h' => by simp only [arity_leaf] at h'; omega
  | node e l r, i, s, i', u, h, h' => by
    simp only [arity_node] at h'
    have hs := arity_pos s
    have hu := arity_pos u
    by_cases hi' : i' < l.arity
    · have hi : i < l.arity := by omega
      have h1 := arity_graft l i s hi
      have h2 := arity_graft l i' u hi'
      rw [graft_node_of_lt r s hi, graft_node_of_lt r u (by omega), graft_node_of_lt r u hi',
        graft_node_of_lt r s (by omega), graft_graft_par l i s i' u h hi']
    · by_cases hi : i < l.arity
      · have h1 := arity_graft l i s hi
        rw [graft_node_of_lt r s hi, graft_node_of_ge _ u (by omega),
          graft_node_of_ge l u (by omega), graft_node_of_lt _ s hi,
          show i' - 1 + s.arity - (l.graft i s).arity = i' - l.arity by omega]
      · rw [graft_node_of_ge l s (by omega), graft_node_of_ge l u (by omega),
          graft_node_of_ge l u (by omega), graft_node_of_ge l s (by omega),
          show i' - 1 + s.arity - l.arity = (i' - l.arity) - 1 + s.arity by omega,
          graft_graft_par r (i - l.arity) s (i' - l.arity) u (by omega) (by omega)]

/-- **Unique factorization.** A tree is a graft at a given slot of a tree of a given arity in at
most one way. -/
theorem graft_inj : ∀ (t t' : BTree E) (i : ℕ) (s s' : BTree E), i < t.arity → i < t'.arity →
    s.arity = s'.arity → t.graft i s = t'.graft i s' → t = t' ∧ s = s'
  | leaf, leaf, _, s, s', _, _, _, h => ⟨rfl, h⟩
  | leaf, node e l r, i, s, s', hi, hi', hs, h => by
    exfalso
    obtain rfl : i = 0 := by simp only [arity_leaf] at hi; omega
    have hl := arity_pos l
    have hr := arity_pos r
    rw [graft_leaf, graft_node_of_lt r s' hl] at h
    have := congrArg arity h
    have h2 := arity_graft l 0 s' hl
    simp only [arity_node] at this
    omega
  | node e l r, leaf, i, s, s', hi, hi', hs, h => by
    exfalso
    obtain rfl : i = 0 := by simp only [arity_leaf] at hi'; omega
    have hl := arity_pos l
    have hr := arity_pos r
    rw [graft_leaf, graft_node_of_lt r s hl] at h
    have := congrArg arity h
    have h2 := arity_graft l 0 s hl
    simp only [arity_node] at this
    omega
  | node e l r, node e' l' r', i, s, s', hi, hi', hs, h => by
    simp only [arity_node] at hi hi'
    have hs1 := arity_pos s
    by_cases h1 : i < l.arity <;> by_cases h2 : i < l'.arity
    · rw [graft_node_of_lt r s h1, graft_node_of_lt r' s' h2] at h
      obtain ⟨rfl, hl, rfl⟩ := node.inj h
      obtain ⟨rfl, rfl⟩ := graft_inj l l' i s s' h1 h2 hs hl
      exact ⟨rfl, rfl⟩
    · exfalso
      rw [graft_node_of_lt r s h1, graft_node_of_ge l' s' (by omega)] at h
      obtain ⟨_, hl, _⟩ := node.inj h
      have := congrArg arity hl
      have := arity_graft l i s h1
      omega
    · exfalso
      rw [graft_node_of_ge l s (by omega), graft_node_of_lt r' s' h2] at h
      obtain ⟨_, hl, _⟩ := node.inj h
      have := congrArg arity hl
      have := arity_graft l' i s' h2
      omega
    · rw [graft_node_of_ge l s (by omega), graft_node_of_ge l' s' (by omega)] at h
      obtain ⟨rfl, rfl, hr⟩ := node.inj h
      obtain ⟨rfl, rfl⟩ := graft_inj r r' (i - l.arity) s s' (by omega) (by omega) hs hr
      exact ⟨rfl, rfl⟩

/-! ## Trees of a given arity -/

/-- **Binary trees with `n` leaves.** -/
def OfArity (E : Type v) (n : ℕ) : Type v := {t : BTree E // t.arity = n}

namespace OfArity

@[ext] lemma ext {n : ℕ} {s t : OfArity E n} (h : s.1 = t.1) : s = t := Subtype.ext h

/-- The leaf, of arity one. -/
def one : OfArity E 1 := ⟨leaf, rfl⟩

/-- The corolla of a generator. -/
def corolla (e : E) : OfArity E 2 := ⟨node e leaf leaf, rfl⟩

/-- Grafting at the positional slot `a`: after `a` leaves and before `b`. -/
def graft (a b : ℕ) {n : ℕ} (t : OfArity E (a + 1 + b)) (s : OfArity E n) :
    OfArity E (a + n + b) :=
  ⟨t.1.graft a s.1, by
    have := BTree.arity_graft t.1 a s.1 (by rw [t.2]; omega)
    rw [t.2, s.2] at this
    omega⟩

@[simp] lemma graft_val (a b : ℕ) {n : ℕ} (t : OfArity E (a + 1 + b)) (s : OfArity E n) :
    (graft a b t s).1 = t.1.graft a s.1 := rfl

/-- **Unique factorization**, for trees of fixed arities. -/
theorem graft_inj (a b : ℕ) {n : ℕ} {t t' : OfArity E (a + 1 + b)} {s s' : OfArity E n}
    (h : graft a b t s = graft a b t' s') : t = t' ∧ s = s' := by
  have := BTree.graft_inj t.1 t'.1 a s.1 s'.1 (by rw [t.2]; omega) (by rw [t'.2]; omega)
    (by rw [s.2, s'.2]) (congrArg Subtype.val h)
  exact ⟨Subtype.ext this.1, Subtype.ext this.2⟩

/-- Changing the arity index along an equality. -/
def cast {m n : ℕ} (h : m = n) (t : OfArity E m) : OfArity E n := ⟨t.1, t.2.trans h⟩

@[simp] lemma cast_val {m n : ℕ} (h : m = n) (t : OfArity E m) : (cast h t).1 = t.1 := rfl

@[simp] lemma cast_cast {l m n : ℕ} (h₁ : l = m) (h₂ : m = n) (t : OfArity E l) :
    cast h₂ (cast h₁ t) = cast (h₁.trans h₂) t := rfl

@[simp] lemma cast_self {n : ℕ} (h : n = n) (t : OfArity E n) : cast h t = t := rfl

end OfArity

/-! ## Finitely many trees of each arity -/

section Finite

variable [Fintype E] [DecidableEq E]

/-- The trees of arity `n`, enumerated. -/
def ofArityFinset : ℕ → Finset (BTree E)
  | 0 => ∅
  | 1 => {leaf}
  | n + 2 => (Finset.univ : Finset (Fin (n + 1))).biUnion fun k =>
      ((Finset.univ : Finset E) ×ˢ (ofArityFinset (k.1 + 1) ×ˢ ofArityFinset (n + 1 - k.1))).image
        fun p => node p.1 p.2.1 p.2.2
  decreasing_by all_goals omega

theorem mem_ofArityFinset : ∀ (t : BTree E) (n : ℕ), t ∈ ofArityFinset n ↔ t.arity = n
  | leaf, 0 => by simp [ofArityFinset]
  | leaf, 1 => by simp [ofArityFinset]
  | leaf, n + 2 => by
    simp only [ofArityFinset, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
      Finset.mem_product, true_and, arity_leaf]
    constructor
    · rintro ⟨_, _, _, h⟩
      cases h
    · omega
  | node e l r, 0 => by
    simp only [ofArityFinset, Finset.notMem_empty, arity_node, false_iff]
    have := arity_pos l
    omega
  | node e l r, 1 => by
    simp only [ofArityFinset, Finset.mem_singleton, arity_node]
    have := arity_pos l
    have := arity_pos r
    constructor
    · intro h; cases h
    · intro h; omega
  | node e l r, n + 2 => by
    simp only [ofArityFinset, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
      Finset.mem_product, true_and, arity_node]
    have hl := arity_pos l
    have hr := arity_pos r
    constructor
    · rintro ⟨k, ⟨e', l', r'⟩, ⟨hl', hr'⟩, h⟩
      obtain ⟨rfl, rfl, rfl⟩ := node.inj h
      rw [mem_ofArityFinset] at hl' hr'
      have := k.2
      omega
    · intro h
      refine ⟨⟨l.arity - 1, by omega⟩, ⟨e, l, r⟩, ⟨?_, ?_⟩, rfl⟩
      · show l ∈ ofArityFinset (l.arity - 1 + 1)
        rw [mem_ofArityFinset]
        omega
      · show r ∈ ofArityFinset (n + 1 - (l.arity - 1))
        rw [mem_ofArityFinset]
        omega

namespace OfArity

variable [Fintype E] [DecidableEq E] in
instance instFintype (n : ℕ) : Fintype (OfArity E n) :=
  Fintype.subtype (ofArityFinset n) fun t => mem_ofArityFinset t n

variable [DecidableEq E] in
instance instDecidableEq (n : ℕ) : DecidableEq (OfArity E n) :=
  inferInstanceAs (DecidableEq {t : BTree E // t.arity = n})

end OfArity

end Finite

end BTree

end Operad
