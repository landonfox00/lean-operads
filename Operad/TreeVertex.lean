/-
# Relabelling one vertex of a planar tree

A map of generators `g : E k → E k`, arity by arity, relabels the vertex `v` of a planar tree in
the preorder (`Tree.relabelAt`), keeping its shape. The parity of the vertices before `v`
(`Tree.bpar`) is the Koszul sign of an odd operation reaching that vertex.

* Relabelling a vertex keeps the arity, the weight and the shape (`Tree.arity_relabelAt`,
  `Tree.weight_relabelAt`, `Tree.shape_relabelAt`), and flips the parity of the tree when `g`
  flips the parities of the generators (`Tree.tpar_relabelAt`).
* **Relabelling a vertex of a graft** relabels the vertex of the outer tree or of the grafted tree
  it comes from (`Tree.relabelAt_graft_outer`, `Tree.relabelAt_graft_inner`), with the vertices
  numbered as in `Operad.sum_Ico_graft`; the parities before the vertex add accordingly
  (`Tree.bpar_graft_outer`, `Tree.bpar_graft_inner`).
* **Cuts of a relabelled tree** are cuts of the tree with one side relabelled
  (`Tree.graft_eq_relabelAt`).
-/
import Operad.TreeMerge
import Operad.TreeRelabel

universe v

namespace Operad

namespace Tree

variable {E : ℕ → Type v} (g : ∀ k, E k → E k)

mutual

/-- **Relabel the vertex `v`** of the preorder by `g`. -/
def relabelAt : Tree E → ℕ → Tree E
  | .leaf, _ => .leaf
  | .node e f, 0 => .node (g _ e) f
  | .node e f, v + 1 => .node e (Forest.relabelAtF f v)

/-- Relabel the vertex `v` of a forest, its trees numbered in turn. -/
def _root_.Operad.Forest.relabelAtF : ∀ {k : ℕ}, Forest E k → ℕ → Forest E k
  | _, .nil, _ => .nil
  | _, .cons t f, v =>
    if v < t.weight then .cons (relabelAt t v) f else .cons t (Forest.relabelAtF f (v - t.weight))

end

@[simp] lemma relabelAt_leaf (v : ℕ) : relabelAt g (.leaf : Tree E) v = .leaf := rfl

@[simp] lemma relabelAt_node_zero {k : ℕ} (e : E k) (f : Forest E k) :
    relabelAt g (.node e f) 0 = .node (g _ e) f := rfl

@[simp] lemma relabelAt_node_succ {k : ℕ} (e : E k) (f : Forest E k) (v : ℕ) :
    relabelAt g (.node e f) (v + 1) = .node e (Forest.relabelAtF g f v) := rfl

@[simp] lemma relabelAtF_nil (v : ℕ) : Forest.relabelAtF g (.nil : Forest E 0) v = .nil := rfl

lemma relabelAtF_cons_of_lt {k : ℕ} {t : Tree E} {f : Forest E k} {v : ℕ} (h : v < t.weight) :
    Forest.relabelAtF g (.cons t f) v = .cons (relabelAt g t v) f := by
  rw [Forest.relabelAtF, if_pos h]

lemma relabelAtF_cons_of_ge {k : ℕ} {t : Tree E} {f : Forest E k} {v : ℕ} (h : t.weight ≤ v) :
    Forest.relabelAtF g (.cons t f) v = .cons t (Forest.relabelAtF g f (v - t.weight)) := by
  rw [Forest.relabelAtF, if_neg (by omega)]

mutual

/-- Relabelling a vertex keeps the leaves. -/
theorem arity_relabelAt : ∀ (t : Tree E) (v : ℕ), (relabelAt g t v).arity = t.arity
  | .leaf, _ => rfl
  | .node _ _, 0 => rfl
  | .node _ f, v + 1 => by
    simp only [relabelAt_node_succ, arity_node]
    exact Forest.arityF_relabelAtF f v

/-- The forest half of `arity_relabelAt`. -/
theorem _root_.Operad.Forest.arityF_relabelAtF : ∀ {k : ℕ} (f : Forest E k) (v : ℕ),
    (Forest.relabelAtF g f v).arityF = f.arityF
  | _, .nil, _ => rfl
  | _, .cons t f, v => by
    by_cases h : v < t.weight
    · rw [relabelAtF_cons_of_lt g h, arityF_cons, arityF_cons, arity_relabelAt t v]
    · rw [relabelAtF_cons_of_ge g (by omega), arityF_cons, arityF_cons,
        Forest.arityF_relabelAtF f]

end

mutual

/-- Relabelling a vertex keeps the vertices. -/
theorem weight_relabelAt : ∀ (t : Tree E) (v : ℕ), (relabelAt g t v).weight = t.weight
  | .leaf, _ => rfl
  | .node _ _, 0 => rfl
  | .node _ f, v + 1 => by
    simp only [relabelAt_node_succ, weight_node]
    rw [Forest.weightF_relabelAtF f v]

/-- The forest half of `weight_relabelAt`. -/
theorem _root_.Operad.Forest.weightF_relabelAtF : ∀ {k : ℕ} (f : Forest E k) (v : ℕ),
    (Forest.relabelAtF g f v).weightF = f.weightF
  | _, .nil, _ => rfl
  | _, .cons t f, v => by
    by_cases h : v < t.weight
    · rw [relabelAtF_cons_of_lt g h, weightF_cons, weightF_cons, weight_relabelAt t v]
    · rw [relabelAtF_cons_of_ge g (by omega), weightF_cons, weightF_cons,
        Forest.weightF_relabelAtF f]

end

mutual

/-- Relabelling a vertex beyond the last changes nothing. -/
theorem relabelAt_of_le : ∀ (t : Tree E) (v : ℕ), t.weight ≤ v → relabelAt g t v = t
  | .leaf, _, _ => rfl
  | .node _ _, 0, h => by simp at h
  | .node _ f, v + 1, h => by
    simp only [weight_node] at h
    rw [relabelAt_node_succ, Forest.relabelAtF_of_le f v (by omega)]

/-- The forest half of `relabelAt_of_le`. -/
theorem _root_.Operad.Forest.relabelAtF_of_le : ∀ {k : ℕ} (f : Forest E k) (v : ℕ),
    f.weightF ≤ v → Forest.relabelAtF g f v = f
  | _, .nil, _, _ => rfl
  | _, .cons t f, v, h => by
    simp only [weightF_cons] at h
    rw [relabelAtF_cons_of_ge g (by omega), Forest.relabelAtF_of_le f _ (by omega)]

end

/-- The shape of a tree: its labels forgotten. -/
def shape (t : Tree E) : Tree (fun _ => PUnit.{v + 1}) := relabel (fun _ _ => PUnit.unit) t

mutual

/-- **Relabelling a vertex keeps the shape.** -/
theorem shape_relabelAt : ∀ (t : Tree E) (v : ℕ), shape (relabelAt g t v) = shape t
  | .leaf, _ => rfl
  | .node _ _, 0 => rfl
  | .node e f, v + 1 => by
    unfold shape
    rw [relabelAt_node_succ, relabel_node, relabel_node, Forest.shapeF_relabelAtF f v]

/-- The forest half of `shape_relabelAt`. -/
theorem _root_.Operad.Forest.shapeF_relabelAtF : ∀ {k : ℕ} (f : Forest E k) (v : ℕ),
    Forest.relabelF (fun _ _ => PUnit.unit) (Forest.relabelAtF g f v)
      = Forest.relabelF (fun _ _ => PUnit.unit) f
  | _, .nil, _ => rfl
  | _, .cons t f, v => by
    by_cases h : v < t.weight
    · rw [relabelAtF_cons_of_lt g h, relabelF_cons, relabelF_cons]
      have := shape_relabelAt t v
      unfold shape at this
      rw [this]
    · rw [relabelAtF_cons_of_ge g (by omega), relabelF_cons, relabelF_cons,
        Forest.shapeF_relabelAtF f]

end

/-! ## Relabelling a vertex of a graft -/

mutual

/-- **A vertex of the grafted tree.** -/
theorem relabelAt_graft_inner : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (k : ℕ), p < s.arity →
    k < u.weight → relabelAt g (s.graft p u) (s.vb p + k) = s.graft p (relabelAt g u k)
  | .leaf, _, u, k, _, _ => by simp
  | .node e f, p, u, k, h, hk => by
    simp only [graft_node, vb_node]
    rw [show f.vbF p + 1 + k = (f.vbF p + k) + 1 by omega, relabelAt_node_succ,
      Forest.relabelAtF_graftF_inner f p u k (by simpa using h) hk]

/-- The forest half of `relabelAt_graft_inner`. -/
theorem _root_.Operad.Forest.relabelAtF_graftF_inner : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (j : ℕ), p < f.arityF → j < u.weight →
    Forest.relabelAtF g (f.graftF p u) (f.vbF p + j) = f.graftF p (relabelAt g u j)
  | _, .nil, _, _, _, h, _ => by simp at h
  | _, .cons t f, p, u, j, h, hj => by
    simp only [arityF_cons] at h
    by_cases hp : p < t.arity
    · have hw := weight_graft t p u hp
      have hv := vb_le_weight t p
      rw [graftF_cons_of_lt _ hp, vbF_cons_of_lt hp, relabelAtF_cons_of_lt g (by omega),
        relabelAt_graft_inner t p u j hp hj, graftF_cons_of_lt _ hp]
    · rw [graftF_cons_of_ge _ (by omega), vbF_cons_of_ge (by omega),
        relabelAtF_cons_of_ge g (by omega), show t.weight + f.vbF (p - t.arity) + j - t.weight
          = f.vbF (p - t.arity) + j by omega,
        Forest.relabelAtF_graftF_inner f (p - t.arity) u j (by omega) hj,
        graftF_cons_of_ge _ (by omega)]

end

mutual

/-- **A vertex of the outer tree.** -/
theorem relabelAt_graft_outer : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (k : ℕ), p < s.arity →
    k < s.weight →
    relabelAt g (s.graft p u) (k + if s.vb p ≤ k then u.weight else 0)
      = (relabelAt g s k).graft p u
  | .leaf, _, _, _, _, hk => by simp at hk
  | .node e f, p, u, 0, _, _ => by
    simp only [vb_node, graft_node]
    rw [if_neg (by omega), Nat.add_zero, relabelAt_node_zero, relabelAt_node_zero, graft_node]
  | .node e f, p, u, k + 1, h, hk => by
    simp only [vb_node, graft_node, weight_node] at hk ⊢
    have := Forest.relabelAtF_graftF_outer f p u k (by simpa using h) (by omega)
    by_cases hvk : f.vbF p ≤ k
    · simp only [show f.vbF p + 1 ≤ k + 1 by omega, if_true] at this ⊢
      simp only [hvk, if_true] at this
      rw [show k + 1 + u.weight = (k + u.weight) + 1 by omega, relabelAt_node_succ,
        relabelAt_node_succ, graft_node, this]
    · simp only [show ¬(f.vbF p + 1 ≤ k + 1) by omega, if_false, Nat.add_zero] at this ⊢
      simp only [hvk, if_false, Nat.add_zero] at this
      rw [relabelAt_node_succ, relabelAt_node_succ, graft_node, this]

/-- The forest half of `relabelAt_graft_outer`. -/
theorem _root_.Operad.Forest.relabelAtF_graftF_outer : ∀ {k : ℕ} (f : Forest E k) (p : ℕ)
    (u : Tree E) (j : ℕ), p < f.arityF → j < f.weightF →
    Forest.relabelAtF g (f.graftF p u) (j + if f.vbF p ≤ j then u.weight else 0)
      = (Forest.relabelAtF g f j).graftF p u
  | _, .nil, _, _, _, h, _ => by simp at h
  | _, .cons t f, p, u, j, h, hj => by
    simp only [arityF_cons, weightF_cons] at h hj
    by_cases hp : p < t.arity
    · have hw := weight_graft t p u hp
      have hv := vb_le_weight t p
      rw [graftF_cons_of_lt _ hp, vbF_cons_of_lt hp]
      by_cases hjt : j < t.weight
      · rw [relabelAtF_cons_of_lt g (show (j + if t.vb p ≤ j then u.weight else 0)
            < (t.graft p u).weight by split_ifs <;> omega),
          relabelAt_graft_outer t p u j hp hjt, relabelAtF_cons_of_lt g hjt,
          graftF_cons_of_lt _ (by rwa [arity_relabelAt])]
      · rw [if_pos (by omega), relabelAtF_cons_of_ge g (by omega),
          relabelAtF_cons_of_ge g (by omega), graftF_cons_of_lt _ hp,
          show j + u.weight - (t.graft p u).weight = j - t.weight by omega]
    · rw [graftF_cons_of_ge _ (by omega), vbF_cons_of_ge (by omega)]
      by_cases hjt : j < t.weight
      · have := Forest.vbF_le_weightF f (p - t.arity)
        simp only [show ¬(t.weight + f.vbF (p - t.arity) ≤ j) by omega, if_false, Nat.add_zero]
        rw [relabelAtF_cons_of_lt g hjt, relabelAtF_cons_of_lt g hjt,
          graftF_cons_of_ge _ (by rw [arity_relabelAt]; omega),
          arity_relabelAt]
      · have e1 : (j + if t.weight + f.vbF (p - t.arity) ≤ j then u.weight else 0) - t.weight
            = (j - t.weight) + if f.vbF (p - t.arity) ≤ j - t.weight then u.weight else 0 := by
          split_ifs <;> omega
        rw [relabelAtF_cons_of_ge g (by split_ifs <;> omega), e1,
          Forest.relabelAtF_graftF_outer f (p - t.arity) u (j - t.weight) (by omega) (by omega),
          relabelAtF_cons_of_ge g (by omega), graftF_cons_of_ge _ (by omega)]

end

/-! ## Cuts of a relabelled tree -/

/-- **A cut of a tree with a vertex relabelled** is a cut of the tree with the vertex relabelled
on the side it lies on. -/
theorem graft_eq_relabelAt {t s' u' : Tree E} {r k : ℕ} (hr : r < s'.arity) (hk : k < t.weight)
    (h : s'.graft r u' = relabelAt g t k) :
    ∃ s u, s.graft r u = t ∧ r < s.arity ∧
      ((s.vb r ≤ k ∧ k < s.vb r + u.weight ∧ s' = s ∧ u' = relabelAt g u (k - s.vb r)) ∨
       (¬(s.vb r ≤ k ∧ k < s.vb r + u.weight) ∧
        s' = relabelAt g s (k - if s.vb r ≤ k then u.weight else 0) ∧ u' = u)) := by
  have hsh : (shape s').graft r (shape u') = relabel (fun _ _ => PUnit.unit) t := by
    have := congrArg shape h
    rw [shape_relabelAt] at this
    unfold shape at this
    rw [relabel_graft] at this
    exact this
  obtain ⟨s, u, hsu, hs, hu⟩ := exists_graft_of_relabel_graft (fun _ _ => PUnit.unit) t
    (shape s') (shape u') r (by unfold shape; rwa [arity_relabel]) hsh
  have hrs : r < s.arity := by
    rw [← arity_relabel (fun _ _ => PUnit.unit) s, hs]
    unfold shape
    rwa [arity_relabel]
  have hw : t.weight = s.weight + u.weight := by rw [← hsu, weight_graft s r u hrs]
  refine ⟨s, u, hsu, hrs, ?_⟩
  by_cases hin : s.vb r ≤ k ∧ k < s.vb r + u.weight
  · refine Or.inl ⟨hin.1, hin.2, ?_⟩
    rw [← hsu, show k = s.vb r + (k - s.vb r) by omega,
      relabelAt_graft_inner g s r u _ hrs (by omega)] at h
    have := graft_cancel (fun _ _ => PUnit.unit) s' s u' _ r hr h (by rw [hs]; rfl)
    exact this
  · refine Or.inr ⟨hin, ?_⟩
    have hvw := vb_le_weight s r
    have hk0 : k - (if s.vb r ≤ k then u.weight else 0) < s.weight := by split_ifs <;> omega
    have hk1 : k = (k - if s.vb r ≤ k then u.weight else 0)
        + if s.vb r ≤ k - (if s.vb r ≤ k then u.weight else 0) then u.weight else 0 := by
      by_cases h1 : s.vb r ≤ k
      · simp only [h1, if_true, show s.vb r ≤ k - u.weight by omega]
        omega
      · simp only [h1, if_false, Nat.sub_zero, Nat.add_zero]
    rw [← hsu, hk1, relabelAt_graft_outer g s r u _ hrs hk0] at h
    have := graft_cancel (fun _ _ => PUnit.unit) s' _ u' u r hr h (by
      show shape s' = shape (relabelAt g s _)
      rw [shape_relabelAt]
      exact hs.symm)
    exact this

/-! ## Parities -/

section Par

variable (gp : ∀ k, E k → Bool)

mutual

/-- **The parity of the vertices before the vertex `v`** in the preorder. -/
def bpar : Tree E → ℕ → Bool
  | .leaf, _ => false
  | .node _ _, 0 => false
  | .node e f, v + 1 => xor (gp _ e) (Forest.bparF f v)

/-- The parity of the vertices of a forest before its vertex `v`. -/
def _root_.Operad.Forest.bparF : ∀ {k : ℕ}, Forest E k → ℕ → Bool
  | _, .nil, _ => false
  | _, .cons t f, v =>
    if v < t.weight then bpar t v else xor (tpar gp t) (Forest.bparF f (v - t.weight))

end

@[simp] lemma bpar_leaf (v : ℕ) : bpar gp (.leaf : Tree E) v = false := rfl

@[simp] lemma bpar_node_zero {k : ℕ} (e : E k) (f : Forest E k) : bpar gp (.node e f) 0 = false :=
  rfl

@[simp] lemma bpar_node_succ {k : ℕ} (e : E k) (f : Forest E k) (v : ℕ) :
    bpar gp (.node e f) (v + 1) = xor (gp _ e) (Forest.bparF gp f v) := rfl

lemma bparF_cons_of_lt {k : ℕ} {t : Tree E} {f : Forest E k} {v : ℕ} (h : v < t.weight) :
    Forest.bparF gp (.cons t f) v = bpar gp t v := by
  rw [Forest.bparF, if_pos h]

lemma bparF_cons_of_ge {k : ℕ} {t : Tree E} {f : Forest E k} {v : ℕ} (h : t.weight ≤ v) :
    Forest.bparF gp (.cons t f) v = xor (tpar gp t) (Forest.bparF gp f (v - t.weight)) := by
  rw [Forest.bparF, if_neg (by omega)]

mutual

/-- Before the first vertex, nothing. -/
theorem bpar_zero : ∀ t : Tree E, bpar gp t 0 = false
  | .leaf => rfl
  | .node _ _ => rfl

/-- The forest half of `bpar_zero`. -/
theorem _root_.Operad.Forest.bparF_zero : ∀ {k : ℕ} (f : Forest E k), Forest.bparF gp f 0 = false
  | _, .nil => rfl
  | _, .cons t f => by
    by_cases h : 0 < t.weight
    · rw [bparF_cons_of_lt gp h, bpar_zero t]
    · have ht : t.weight = 0 := by omega
      rw [bparF_cons_of_ge gp (by omega), ht, Nat.sub_zero, Forest.bparF_zero f]
      cases t with
      | leaf => rfl
      | node _ _ => simp at ht

end

mutual

/-- After the last vertex, all of them. -/
theorem bpar_of_le : ∀ (t : Tree E) (v : ℕ), t.weight ≤ v → bpar gp t v = tpar gp t
  | .leaf, _, _ => rfl
  | .node _ _, 0, h => by simp at h
  | .node e f, v + 1, h => by
    simp only [weight_node] at h
    rw [bpar_node_succ, Forest.bparF_of_le f v (by omega), tpar_node]

/-- The forest half of `bpar_of_le`. -/
theorem _root_.Operad.Forest.bparF_of_le : ∀ {k : ℕ} (f : Forest E k) (v : ℕ),
    f.weightF ≤ v → Forest.bparF gp f v = Forest.tparF gp f
  | _, .nil, _, _ => rfl
  | _, .cons t f, v, h => by
    simp only [weightF_cons] at h
    rw [bparF_cons_of_ge gp (by omega), Forest.bparF_of_le f _ (by omega), tparF_cons]

end

lemma bparF_cons_vb {k : ℕ} {t : Tree E} {f : Forest E k} {p : ℕ} :
    Forest.bparF gp (.cons t f) (t.vb p) = bpar gp t (t.vb p) := by
  by_cases h : t.vb p < t.weight
  · rw [bparF_cons_of_lt gp h]
  · have hv := vb_le_weight t p
    rw [bparF_cons_of_ge gp (by omega), show t.vb p - t.weight = 0 by omega,
      Forest.bparF_zero, Bool.xor_false, bpar_of_le gp t _ (by omega)]

variable {g}

mutual

/-- **Relabelling a vertex by a map flipping the parities flips the parity of the tree.** -/
theorem tpar_relabelAt (hg : ∀ k e, gp k (g k e) = !gp k e) : ∀ (t : Tree E) (v : ℕ),
    tpar gp (relabelAt g t v) = xor (tpar gp t) (decide (v < t.weight))
  | .leaf, _ => by simp
  | .node e f, 0 => by
    simp only [relabelAt_node_zero, tpar_node, hg, weight_node]
    cases gp _ e <;> cases Forest.tparF gp f <;> simp
  | .node e f, v + 1 => by
    simp only [relabelAt_node_succ, tpar_node, weight_node,
      Forest.tparF_relabelAtF hg f v, Bool.xor_assoc]
    congr 2
    exact decide_eq_decide.2 (by omega)

/-- The forest half of `tpar_relabelAt`. -/
theorem _root_.Operad.Forest.tparF_relabelAtF (hg : ∀ k e, gp k (g k e) = !gp k e) :
    ∀ {k : ℕ} (f : Forest E k) (v : ℕ),
    Forest.tparF gp (Forest.relabelAtF g f v) = xor (Forest.tparF gp f) (decide (v < f.weightF))
  | _, .nil, _ => by simp
  | _, .cons t f, v => by
    by_cases h : v < t.weight
    · rw [relabelAtF_cons_of_lt g h, tparF_cons, tparF_cons, tpar_relabelAt hg t v,
        weightF_cons, decide_eq_true h, decide_eq_true (by omega : v < t.weight + f.weightF)]
      cases tpar gp t <;> cases Forest.tparF gp f <;> rfl
    · rw [relabelAtF_cons_of_ge g (by omega), tparF_cons, tparF_cons,
        Forest.tparF_relabelAtF hg f, weightF_cons, Bool.xor_assoc]
      congr 2
      exact decide_eq_decide.2 (by omega)

end

mutual

/-- Relabelling a vertex keeps the vertices before each leaf. -/
theorem vb_relabelAt : ∀ (t : Tree E) (k p : ℕ), (relabelAt g t k).vb p = t.vb p
  | .leaf, _, _ => rfl
  | .node _ _, 0, _ => rfl
  | .node _ f, k + 1, p => by
    rw [relabelAt_node_succ, vb_node, vb_node, Forest.vbF_relabelAtF f k p]

/-- The forest half of `vb_relabelAt`. -/
theorem _root_.Operad.Forest.vbF_relabelAtF : ∀ {n : ℕ} (f : Forest E n) (k p : ℕ),
    (Forest.relabelAtF g f k).vbF p = f.vbF p
  | _, .nil, _, _ => rfl
  | _, .cons t f, k, p => by
    by_cases hk : k < t.weight
    · rw [relabelAtF_cons_of_lt g hk]
      by_cases hp : p < t.arity
      · rw [vbF_cons_of_lt (by rwa [arity_relabelAt]), vbF_cons_of_lt hp, vb_relabelAt t k p]
      · rw [vbF_cons_of_ge (by rw [arity_relabelAt]; omega), vbF_cons_of_ge (by omega),
          weight_relabelAt, arity_relabelAt]
    · rw [relabelAtF_cons_of_ge g (by omega)]
      by_cases hp : p < t.arity
      · rw [vbF_cons_of_lt hp, vbF_cons_of_lt hp]
      · rw [vbF_cons_of_ge (by omega), vbF_cons_of_ge (by omega), Forest.vbF_relabelAtF f]

end

mutual

/-- **The parity after a leaf** changes when the relabelled vertex comes after the leaf. -/
theorem apar_relabelAt (hg : ∀ k e, gp k (g k e) = !gp k e) : ∀ (t : Tree E) (k p : ℕ),
    p < t.arity →
    apar gp (relabelAt g t k) p = xor (apar gp t p) (decide (t.vb p ≤ k ∧ k < t.weight))
  | .leaf, _, _, _ => by simp
  | .node e f, 0, p, _ => by
    simp only [relabelAt_node_zero, apar_node, vb_node]
    simp
  | .node e f, k + 1, p, h => by
    simp only [relabelAt_node_succ, apar_node, vb_node, weight_node]
    rw [Forest.aparF_relabelAtF hg f k p h]
    congr 1
    exact decide_eq_decide.2 (by omega)

/-- The forest half of `apar_relabelAt`. -/
theorem _root_.Operad.Forest.aparF_relabelAtF (hg : ∀ k e, gp k (g k e) = !gp k e) :
    ∀ {n : ℕ} (f : Forest E n) (k p : ℕ), p < f.arityF →
    Forest.aparF gp (Forest.relabelAtF g f k) p
      = xor (Forest.aparF gp f p) (decide (f.vbF p ≤ k ∧ k < f.weightF))
  | _, .nil, _, _, h => by simp at h
  | _, .cons t f, k, p, h => by
    simp only [arityF_cons] at h
    have hv := vb_le_weight t p
    by_cases hk : k < t.weight
    · rw [relabelAtF_cons_of_lt g hk]
      by_cases hp : p < t.arity
      · rw [aparF_cons_of_lt gp _ _ (by rwa [arity_relabelAt]), apar_relabelAt hg t k p hp,
          aparF_cons_of_lt gp _ _ hp, vbF_cons_of_lt hp, weightF_cons]
        rw [show decide (t.vb p ≤ k ∧ k < t.weight) = decide (t.vb p ≤ k ∧ k < t.weight
          + f.weightF) from decide_eq_decide.2 (by omega)]
        cases apar gp t p <;> cases Forest.tparF gp f <;> simp
      · have hw := Forest.vbF_le_weightF f (p - t.arity)
        rw [aparF_cons_of_ge gp _ _ (by rw [arity_relabelAt]; omega),
          aparF_cons_of_ge gp _ _ (by omega), vbF_cons_of_ge (by omega), arity_relabelAt]
        simp only [show ¬(t.weight + f.vbF (p - t.arity) ≤ k) by omega, false_and,
          decide_false, Bool.xor_false]
    · rw [relabelAtF_cons_of_ge g (by omega), weightF_cons]
      by_cases hp : p < t.arity
      · rw [aparF_cons_of_lt gp _ _ hp, aparF_cons_of_lt gp _ _ hp, vbF_cons_of_lt hp,
          Forest.tparF_relabelAtF gp hg f, Bool.xor_assoc]
        congr 2
        exact decide_eq_decide.2 (by omega)
      · rw [aparF_cons_of_ge gp _ _ (by omega), aparF_cons_of_ge gp _ _ (by omega),
          vbF_cons_of_ge (by omega), Forest.aparF_relabelAtF hg f _ _ (by omega)]
        congr 1
        exact decide_eq_decide.2 (by omega)

end

variable (g) in
mutual

/-- **The vertices before a leaf, and those after it**, are all of them. -/
theorem bpar_vb_xor_apar : ∀ (s : Tree E) (p : ℕ), p < s.arity →
    xor (bpar gp s (s.vb p)) (apar gp s p) = tpar gp s
  | .leaf, _, _ => rfl
  | .node e f, p, h => by
    rw [vb_node, bpar_node_succ, apar_node, tpar_node, Bool.xor_assoc,
      Forest.bparF_vbF_xor_aparF f p h]

/-- The forest half of `bpar_vb_xor_apar`. -/
theorem _root_.Operad.Forest.bparF_vbF_xor_aparF : ∀ {n : ℕ} (f : Forest E n) (p : ℕ),
    p < f.arityF → xor (Forest.bparF gp f (f.vbF p)) (Forest.aparF gp f p) = Forest.tparF gp f
  | _, .nil, _, h => by simp at h
  | _, .cons t f, p, h => by
    simp only [arityF_cons] at h
    by_cases hp : p < t.arity
    · rw [vbF_cons_of_lt hp, bparF_cons_vb, aparF_cons_of_lt gp _ _ hp, tparF_cons,
        ← Bool.xor_assoc, bpar_vb_xor_apar t p hp]
    · rw [vbF_cons_of_ge (by omega), bparF_cons_of_ge gp (by omega),
        aparF_cons_of_ge gp _ _ (by omega), tparF_cons, Nat.add_sub_cancel_left, Bool.xor_assoc,
        Forest.bparF_vbF_xor_aparF f _ (by omega)]

end

mutual

/-- **Before a vertex of the grafted tree**: the vertices of the outer tree before the graft
point, and those of the grafted tree before it. -/
theorem bpar_graft_inner : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (k : ℕ), p < s.arity →
    k < u.weight →
    bpar gp (s.graft p u) (s.vb p + k) = xor (bpar gp s (s.vb p)) (bpar gp u k)
  | .leaf, _, u, k, _, _ => by simp
  | .node e f, p, u, k, h, hk => by
    simp only [graft_node, vb_node]
    rw [show f.vbF p + 1 + k = (f.vbF p + k) + 1 by omega, bpar_node_succ, bpar_node_succ,
      Forest.bparF_graftF_inner f p u k (by simpa using h) hk, Bool.xor_assoc]

/-- The forest half of `bpar_graft_inner`. -/
theorem _root_.Operad.Forest.bparF_graftF_inner : ∀ {n : ℕ} (f : Forest E n) (p : ℕ)
    (u : Tree E) (j : ℕ), p < f.arityF → j < u.weight →
    Forest.bparF gp (f.graftF p u) (f.vbF p + j)
      = xor (Forest.bparF gp f (f.vbF p)) (bpar gp u j)
  | _, .nil, _, _, _, h, _ => by simp at h
  | _, .cons t f, p, u, j, h, hj => by
    simp only [arityF_cons] at h
    by_cases hp : p < t.arity
    · have hw := weight_graft t p u hp
      have hv := vb_le_weight t p
      rw [graftF_cons_of_lt _ hp, vbF_cons_of_lt hp, bparF_cons_of_lt gp (by omega),
        bpar_graft_inner t p u j hp hj, bparF_cons_vb]
    · rw [graftF_cons_of_ge _ (by omega), vbF_cons_of_ge (by omega),
        bparF_cons_of_ge gp (by omega), bparF_cons_of_ge gp (by omega),
        show t.weight + f.vbF (p - t.arity) + j - t.weight = f.vbF (p - t.arity) + j by omega,
        Nat.add_sub_cancel_left, Forest.bparF_graftF_inner f (p - t.arity) u j (by omega) hj,
        Bool.xor_assoc]

end

mutual

/-- **Before a vertex of the outer tree**: the grafted tree comes in when the vertex comes after
the graft point. -/
theorem bpar_graft_outer : ∀ (s : Tree E) (p : ℕ) (u : Tree E) (k : ℕ), p < s.arity →
    k < s.weight →
    bpar gp (s.graft p u) (k + if s.vb p ≤ k then u.weight else 0)
      = xor (bpar gp s k) (tpar gp u && decide (s.vb p ≤ k))
  | .leaf, _, _, _, _, hk => by simp at hk
  | .node e f, p, u, 0, _, _ => by
    simp only [vb_node, graft_node]
    simp
  | .node e f, p, u, k + 1, h, hk => by
    simp only [vb_node, graft_node, weight_node] at hk ⊢
    have := Forest.bparF_graftF_outer f p u k (by simpa using h) (by omega)
    by_cases hvk : f.vbF p ≤ k
    · simp only [show f.vbF p + 1 ≤ k + 1 by omega, if_true, decide_true] at this ⊢
      simp only [hvk, if_true, decide_true] at this
      rw [show k + 1 + u.weight = (k + u.weight) + 1 by omega, bpar_node_succ, bpar_node_succ,
        this, Bool.xor_assoc]
    · simp only [show ¬(f.vbF p + 1 ≤ k + 1) by omega, if_false, Nat.add_zero, decide_false,
        Bool.and_false, Bool.xor_false] at this ⊢
      simp only [hvk, if_false, Nat.add_zero, decide_false, Bool.and_false,
        Bool.xor_false] at this
      rw [bpar_node_succ, bpar_node_succ, this]

/-- The forest half of `bpar_graft_outer`. -/
theorem _root_.Operad.Forest.bparF_graftF_outer : ∀ {n : ℕ} (f : Forest E n) (p : ℕ)
    (u : Tree E) (j : ℕ), p < f.arityF → j < f.weightF →
    Forest.bparF gp (f.graftF p u) (j + if f.vbF p ≤ j then u.weight else 0)
      = xor (Forest.bparF gp f j) (tpar gp u && decide (f.vbF p ≤ j))
  | _, .nil, _, _, _, h, _ => by simp at h
  | _, .cons t f, p, u, j, h, hj => by
    simp only [arityF_cons, weightF_cons] at h hj
    by_cases hp : p < t.arity
    · have hw := weight_graft t p u hp
      have hv := vb_le_weight t p
      rw [graftF_cons_of_lt _ hp, vbF_cons_of_lt hp]
      by_cases hjt : j < t.weight
      · rw [bparF_cons_of_lt gp (show (j + if t.vb p ≤ j then u.weight else 0)
            < (t.graft p u).weight by split_ifs <;> omega),
          bpar_graft_outer t p u j hp hjt, bparF_cons_of_lt gp hjt]
      · simp only [show t.vb p ≤ j by omega, if_true, decide_true, Bool.and_true]
        rw [bparF_cons_of_ge gp (by omega), bparF_cons_of_ge gp (by omega),
          show j + u.weight - (t.graft p u).weight = j - t.weight by omega,
          tpar_graft gp t p u hp]
        cases tpar gp t <;> cases tpar gp u <;> simp
    · rw [graftF_cons_of_ge _ (by omega), vbF_cons_of_ge (by omega)]
      by_cases hjt : j < t.weight
      · have := Forest.vbF_le_weightF f (p - t.arity)
        simp only [show ¬(t.weight + f.vbF (p - t.arity) ≤ j) by omega, if_false, Nat.add_zero,
          decide_false, Bool.and_false, Bool.xor_false]
        rw [bparF_cons_of_lt gp hjt, bparF_cons_of_lt gp hjt]
      · have e1 : (j + if t.weight + f.vbF (p - t.arity) ≤ j then u.weight else 0) - t.weight
            = (j - t.weight) + if f.vbF (p - t.arity) ≤ j - t.weight then u.weight else 0 := by
          split_ifs <;> omega
        rw [bparF_cons_of_ge gp (by split_ifs <;> omega), e1,
          Forest.bparF_graftF_outer f (p - t.arity) u (j - t.weight) (by omega) (by omega),
          bparF_cons_of_ge gp (by omega), Bool.xor_assoc]
        congr 3
        exact decide_eq_decide.2 (by omega)

end

end Par

end Tree

end Operad
