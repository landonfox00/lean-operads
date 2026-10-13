/-
# The convolution square on the cut cooperad, vertex by vertex

The decomposition of a planar tree `t` with its leaves labelled, in the cut cooperad of the free
graded operad, sums over the factorizations `t = e·(p ∘ᵢ q)`. A factorization with both factors
nontrivial is determined by **its vertex**, the vertex of `t` at the root of `q`
(`FreeGr.vert`, `Tree.cutV_graft`), and every vertex of `t` other than the root is the vertex of a
factorization, at the subset of inputs above it (`FreeGr.exists_rep`).

So, for invariant families `f, g` of the convolution operad killing the trivial tree, **the
convolution square on a basis tree is a sum over its vertices other than the root**
(`FreeGr.star_bas`), whose term at a vertex is the composite of `f` and `g` on the two parts of
the cut there, relabelled (`FreeGr.starV`), the same for every factorization with that vertex
(`FreeGr.repW_eq`, `FreeGr.starV_eq`).

The vertices of a graft `s.graft q b` are those of `s`, shifted after the graft point, and those
of `b` (`Tree.vb_graft_of_lt`, `Tree.vb_graft_of_gt`, `Tree.vb_graft_mid`).
-/
import Operad.BarCobar

universe u v w

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

/-! ## Vertices of grafts -/

namespace Tree

variable {E : ℕ → Type v}

mutual

/-- **Grafting after a leaf** does not change the vertices before it. -/
theorem vb_graft_of_lt : ∀ (s : Tree E) (q : ℕ) (b : Tree E) (p : ℕ), p < q → q < s.arity →
    (s.graft q b).vb p = s.vb p
  | .leaf, q, _, p, hpq, hq => by simp at hq; omega
  | .node e f, q, b, p, hpq, hq => by
    simp only [graft_node, vb_node]
    rw [Forest.vbF_graftF_of_lt f q b p hpq hq]

/-- The forest half of `vb_graft_of_lt`. -/
theorem _root_.Operad.Forest.vbF_graftF_of_lt : ∀ {k : ℕ} (f : Forest E k) (q : ℕ) (b : Tree E)
    (p : ℕ), p < q → q < f.arityF → (f.graftF q b).vbF p = f.vbF p
  | _, .nil, _, _, _, _, hq => by simp at hq
  | _, .cons t f, q, b, p, hpq, hq => by
    simp only [arityF_cons] at hq
    by_cases hqt : q < t.arity
    · have hpt : p < (t.graft q b).arity := by
        rw [arity_graft t q b hqt]
        omega
      rw [graftF_cons_of_lt b hqt, vbF_cons_of_lt hpt, vbF_cons_of_lt (by omega),
        vb_graft_of_lt t q b p hpq hqt]
    · rw [graftF_cons_of_ge b (by omega)]
      by_cases hpt : p < t.arity
      · rw [vbF_cons_of_lt hpt, vbF_cons_of_lt hpt]
      · rw [vbF_cons_of_ge (by omega), vbF_cons_of_ge (by omega),
          Forest.vbF_graftF_of_lt f (q - t.arity) b (p - t.arity) (by omega) (by omega)]

end

mutual

/-- **Grafting before a leaf** adds the vertices of the grafted tree before it. -/
theorem vb_graft_of_gt : ∀ (s : Tree E) (q : ℕ) (b : Tree E) (p : ℕ), q < p → p < s.arity →
    (s.graft q b).vb (p - 1 + b.arity) = s.vb p + b.weight
  | .leaf, q, _, p, hqp, hp => by simp at hp; omega
  | .node e f, q, b, p, hqp, hp => by
    simp only [graft_node, vb_node]
    rw [Forest.vbF_graftF_of_gt f q b p hqp hp]
    omega

/-- The forest half of `vb_graft_of_gt`. -/
theorem _root_.Operad.Forest.vbF_graftF_of_gt : ∀ {k : ℕ} (f : Forest E k) (q : ℕ)
    (b : Tree E) (p : ℕ), q < p → p < f.arityF →
    (f.graftF q b).vbF (p - 1 + b.arity) = f.vbF p + b.weight
  | _, .nil, _, _, _, _, hp => by simp at hp
  | _, .cons t f, q, b, p, hqp, hp => by
    simp only [arityF_cons] at hp
    by_cases hqt : q < t.arity
    · rw [graftF_cons_of_lt b hqt]
      by_cases hpt : p < t.arity
      · have hpt' : p - 1 + b.arity < (t.graft q b).arity := by
          rw [arity_graft t q b hqt]
          omega
        rw [vbF_cons_of_lt hpt', vbF_cons_of_lt hpt, vb_graft_of_gt t q b p hqp hpt]
      · have hpt' : (t.graft q b).arity ≤ p - 1 + b.arity := by
          rw [arity_graft t q b hqt]
          omega
        rw [vbF_cons_of_ge hpt', vbF_cons_of_ge (by omega), weight_graft t q b hqt,
          arity_graft t q b hqt,
          show p - 1 + b.arity - (t.arity - 1 + b.arity) = p - t.arity by omega]
        omega
    · rw [graftF_cons_of_ge b (by omega), vbF_cons_of_ge (by omega), vbF_cons_of_ge (by omega),
        show p - 1 + b.arity - t.arity = p - t.arity - 1 + b.arity by omega,
        Forest.vbF_graftF_of_gt f (q - t.arity) b (p - t.arity) (by omega) (by omega)]
      omega

end

mutual

/-- **The vertices before a leaf of the grafted tree**: those before the graft point, and those
of the grafted tree before the leaf. -/
theorem vb_graft_mid : ∀ (s : Tree E) (q : ℕ) (b : Tree E) (p : ℕ), q < s.arity → q ≤ p →
    p < q + b.arity → (s.graft q b).vb p = s.vb q + b.vb (p - q)
  | .leaf, q, b, p, hq, _, _ => by
    obtain rfl : q = 0 := by simpa using hq
    simp
  | .node e f, q, b, p, hq, hqp, hpb => by
    simp only [graft_node, vb_node]
    rw [Forest.vbF_graftF_mid f q b p hq hqp hpb]
    omega

/-- The forest half of `vb_graft_mid`. -/
theorem _root_.Operad.Forest.vbF_graftF_mid : ∀ {k : ℕ} (f : Forest E k) (q : ℕ) (b : Tree E)
    (p : ℕ), q < f.arityF → q ≤ p → p < q + b.arity →
    (f.graftF q b).vbF p = f.vbF q + b.vb (p - q)
  | _, .nil, _, _, _, hq, _, _ => by simp at hq
  | _, .cons t f, q, b, p, hq, hqp, hpb => by
    simp only [arityF_cons] at hq
    by_cases hqt : q < t.arity
    · have hpt : p < (t.graft q b).arity := by
        rw [arity_graft t q b hqt]
        omega
      rw [graftF_cons_of_lt b hqt, vbF_cons_of_lt hpt, vbF_cons_of_lt hqt,
        vb_graft_mid t q b p hqt hqp hpb]
    · rw [graftF_cons_of_ge b (by omega), vbF_cons_of_ge (by omega), vbF_cons_of_ge (by omega),
        Forest.vbF_graftF_mid f (q - t.arity) b (p - t.arity) (by omega) (by omega) (by omega),
        show p - t.arity - (q - t.arity) = p - q by omega]
      omega

end


/-! ## Trees without nullary vertices -/

mutual

/-- **A tree without nullary vertices.** -/
def NoNull : Tree E → Prop
  | .leaf => True
  | .node (k := k) _ f => 0 < k ∧ f.NoNullF

/-- A forest of trees without nullary vertices. -/
def _root_.Operad.Forest.NoNullF : ∀ {k : ℕ}, Forest E k → Prop
  | _, .nil => True
  | _, .cons t f => t.NoNull ∧ f.NoNullF

end

@[simp] lemma noNull_leaf : (Tree.leaf : Tree E).NoNull := trivial

@[simp] lemma noNull_node {k : ℕ} (e : E k) (f : Forest E k) :
    (Tree.node e f).NoNull ↔ 0 < k ∧ f.NoNullF := Iff.rfl

@[simp] lemma noNullF_nil : (Forest.nil : Forest E 0).NoNullF := trivial

@[simp] lemma noNullF_cons {k : ℕ} (t : Tree E) (f : Forest E k) :
    (Forest.cons t f).NoNullF ↔ t.NoNull ∧ f.NoNullF := Iff.rfl

mutual

/-- **A tree without nullary vertices has leaves.** -/
theorem NoNull.arity_pos : ∀ {t : Tree E}, t.NoNull → 0 < t.arity
  | .leaf, _ => by simp
  | .node (k := k) _ f, h => by
    simp only [arity_node]
    have := Forest.NoNullF.le_arityF h.2
    have := h.1
    omega

/-- The forest half of `NoNull.arity_pos`. -/
theorem _root_.Operad.Forest.NoNullF.le_arityF : ∀ {k : ℕ} {f : Forest E k}, f.NoNullF →
    k ≤ f.arityF
  | _, .nil, _ => le_rfl
  | _, .cons t f, h => by
    simp only [arityF_cons]
    have := NoNull.arity_pos h.1
    have := Forest.NoNullF.le_arityF h.2
    omega

end

mutual

/-- **A graft has no nullary vertices exactly when its parts have none.** -/
theorem noNull_graft : ∀ (s : Tree E) (p : ℕ) (u : Tree E), p < s.arity →
    ((s.graft p u).NoNull ↔ s.NoNull ∧ u.NoNull)
  | .leaf, _, u, _ => by simp
  | .node (k := k) e f, p, u, hp => by
    simp only [graft_node, noNull_node]
    rw [Forest.noNullF_graftF f p u hp, and_assoc]

/-- The forest half of `noNull_graft`. -/
theorem _root_.Operad.Forest.noNullF_graftF : ∀ {k : ℕ} (f : Forest E k) (p : ℕ) (u : Tree E),
    p < f.arityF → ((f.graftF p u).NoNullF ↔ f.NoNullF ∧ u.NoNull)
  | _, .nil, _, _, h => by simp at h
  | _, .cons t f, p, u, h => by
    simp only [arityF_cons] at h
    by_cases hpt : p < t.arity
    · rw [graftF_cons_of_lt u hpt, noNullF_cons, noNullF_cons, noNull_graft t p u hpt]
      tauto
    · rw [graftF_cons_of_ge u (by omega), noNullF_cons, noNullF_cons,
        Forest.noNullF_graftF f (p - t.arity) u (by omega)]
      tauto

end

/-- **The parts of a cut of a tree without nullary vertices have none.** -/
lemma NoNull.cutV {t : Tree E} (ht : t.NoNull) {v : ℕ} (hv : v < t.weight) :
    (t.cutV v).1.NoNull ∧ (t.cutV v).2.1.NoNull := by
  rw [← noNull_graft _ _ _ (lt_arity_cutV t v hv), graft_cutV t v hv]
  exact ht

mutual

/-- **A tree with a nullary vertex** is a graft of a nullary corolla. -/
theorem exists_null : ∀ (t : Tree E), ¬ t.NoNull →
    ∃ (s : Tree E) (p : ℕ) (g : E 0), p < s.arity ∧ s.graft p (.node g .nil) = t
  | .leaf, h => absurd trivial h
  | .node (k := k) e f, h => by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      cases f
      exact ⟨.leaf, 0, e, by simp, rfl⟩
    · obtain ⟨g, p, c, hp, hg⟩ := Forest.exists_nullF f (fun hf => h ⟨hk, hf⟩)
      exact ⟨.node e g, p, c, hp, by rw [graft_node, hg]⟩

/-- The forest half of `exists_null`. -/
theorem _root_.Operad.Forest.exists_nullF : ∀ {k : ℕ} (f : Forest E k), ¬ f.NoNullF →
    ∃ (g : Forest E k) (p : ℕ) (c : E 0), p < g.arityF ∧ g.graftF p (.node c .nil) = f
  | _, .nil, h => absurd trivial h
  | _, .cons t f, h => by
    by_cases ht : t.NoNull
    · obtain ⟨g, p, c, hp, hg⟩ := Forest.exists_nullF f (fun hf => h ⟨ht, hf⟩)
      refine ⟨.cons t g, t.arity + p, c, by simp only [arityF_cons]; omega, ?_⟩
      rw [graftF_cons_of_ge _ (by omega), Nat.add_sub_cancel_left, hg]
    · obtain ⟨s, p, c, hp, hs⟩ := exists_null t ht
      refine ⟨.cons s f, p, c, by simp only [arityF_cons]; omega, ?_⟩
      rw [graftF_cons_of_lt _ hp, hs]

end

/-- A tree with a vertex has a vertex before each leaf: its root. -/
lemma one_le_vb {t : Tree E} (ht : t.isLeaf = false) (p : ℕ) : 1 ≤ t.vb p := by
  cases t with
  | leaf => simp [isLeaf] at ht
  | node e f => simp

/-- A tree with a vertex has one. -/
lemma one_le_weight {t : Tree E} (ht : t.isLeaf = false) : 1 ≤ t.weight := by
  cases t with
  | leaf => simp [isLeaf] at ht
  | node e f => simp

end Tree

/-! ## Factorizations and their vertices -/

namespace FreeGr

variable {T : ℕ → Type v} {A B X : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype X] [DecidableEq X]

/-- **The vertex of a factorization** `p ∘ᵢ q`: the vertex of the composite at the root of `q`,
in the preorder. -/
noncomputable abbrev vert (i : A) (p : Reg (TreeOfArity T) A) : ℕ := (treeOf p).vb (p.1.rank i)

/-- The planar tree of a relabelled composite. -/
lemma treeOf_rep {i : A} {p : Reg (TreeOfArity T) A} {q : Reg (TreeOfArity T) B}
    {e : Without A i ⊕ B ≃ X} {t : Reg (TreeOfArity T) X}
    (h : SetOperad.map e (SetOperad.comp i p q) = t) :
    treeOf t = (treeOf p).graft (p.1.rank i) (treeOf q) := by
  rw [← h, treeOf_map, treeOf_comp]

/-- **The cut at the vertex of a factorization is the factorization.** -/
lemma cutV_vert {i : A} {p : Reg (TreeOfArity T) A} {q : Reg (TreeOfArity T) B}
    {e : Without A i ⊕ B ≃ X} {t : Reg (TreeOfArity T) X}
    (h : SetOperad.map e (SetOperad.comp i p q) = t) (hq : (treeOf q).isLeaf = false) :
    (treeOf t).cutV (vert i p) = (treeOf p, treeOf q, p.1.rank i) := by
  rw [treeOf_rep h]
  exact Tree.cutV_graft _ _ _ (rank_lt_arity p i) hq

lemma weight_rep {i : A} {p : Reg (TreeOfArity T) A} {q : Reg (TreeOfArity T) B}
    {e : Without A i ⊕ B ≃ X} {t : Reg (TreeOfArity T) X}
    (h : SetOperad.map e (SetOperad.comp i p q) = t) :
    (treeOf t).weight = (treeOf p).weight + (treeOf q).weight := by
  rw [treeOf_rep h, Tree.weight_graft _ _ _ (rank_lt_arity p i)]

/-- **The vertex of a factorization into nontrivial parts** is a vertex other than the root. -/
lemma vert_mem {i : A} {p : Reg (TreeOfArity T) A} {q : Reg (TreeOfArity T) B}
    {e : Without A i ⊕ B ≃ X} {t : Reg (TreeOfArity T) X}
    (h : SetOperad.map e (SetOperad.comp i p q) = t) (hp : (treeOf p).isLeaf = false)
    (hq : (treeOf q).isLeaf = false) : vert i p ∈ Finset.Ico 1 (treeOf t).weight := by
  rw [Finset.mem_Ico, weight_rep h]
  show 1 ≤ (treeOf p).vb (p.1.rank i) ∧ (treeOf p).vb (p.1.rank i) < _
  have h1 := Tree.one_le_vb hp (p.1.rank i)
  have h2 := Tree.vb_le_weight (treeOf p) (p.1.rank i)
  have h3 := Tree.one_le_weight hq
  omega

/-- **Relabellings of labelled trees are unique.** -/
lemma eq_of_map_eq {e e' : A ≃ B} {x : Reg (TreeOfArity T) A}
    (h : SetOperad.map e x = SetOperad.map e' x) : e = e' := by
  have h1 : LinOrd.map e x.1 = LinOrd.map e' x.1 := congrArg Prod.fst h
  ext a
  have r1 : (LinOrd.map e x.1).rank (e a) = x.1.rank a := by
    rw [LinOrd.rank_map, Equiv.symm_apply_apply]
  have r2 : (LinOrd.map e' x.1).rank (e' a) = x.1.rank a := by
    rw [LinOrd.rank_map, Equiv.symm_apply_apply]
  rw [← h1] at r2
  exact (LinOrd.map e x.1).rank_injective (r1.trans r2.symm)

/-- The standard labelling of a planar tree. -/
abbrev stdT (s : Tree T) : Reg (TreeOfArity T) (Fin s.arity) :=
  Reg.std (⟨s, rfl⟩ : TreeOfArity T s.arity)

@[simp] lemma treeOf_stdT (s : Tree T) : treeOf (stdT s) = s := rfl

@[simp] lemma rank_stdT (s : Tree T) (r : Fin s.arity) : (stdT s).1.rank r = r :=
  LinOrd.rank_std _ r

/-- **Every vertex other than the root is the vertex of a factorization**: the cut there, as a
relabelled composite of standard labelled trees. -/
lemma exists_rep (t : Reg (TreeOfArity T) X) {v : ℕ} (hv : v < (treeOf t).weight) :
    ∃ e : Without (Fin ((treeOf t).cutV v).1.arity)
        ⟨((treeOf t).cutV v).2.2, Tree.lt_arity_cutV _ v hv⟩ ⊕ Fin ((treeOf t).cutV v).2.1.arity
        ≃ X,
      SetOperad.map e (SetOperad.comp ⟨((treeOf t).cutV v).2.2, Tree.lt_arity_cutV _ v hv⟩
        (stdT ((treeOf t).cutV v).1) (stdT ((treeOf t).cutV v).2.1)) = t := by
  refine exists_map_eq ?_
  rw [treeOf_comp, treeOf_stdT, treeOf_stdT, rank_stdT]
  exact Tree.graft_cutV _ v hv

end FreeGr

/-! ## The convolution square, vertex by vertex -/

section Star

variable {R : Type u} [CommRing R] {T : ℕ → Type v} {gp : ∀ k, T k → Bool}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {A B X : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype X]
  [DecidableEq X]

namespace FreeGr

/-- **An invariant family of the convolution operad commutes with relabellings.** -/
lemma inv_toLin_map (q : GrOperad.Inv R (ConvOp R (FreeGr R gp) Q)) (e : A ≃ B)
    (y : FreeGr R gp A) :
    ConvOp.toLin (q.1 B) (GrOperad.map (R := R) e y)
      = GrOperad.map (R := R) e (ConvOp.toLin (q.1 A) y) := by
  rw [← GrOperad.Inv.map_apply q e]
  show GrOperad.map (R := R) e (ConvOp.toLin _ (GrOperad.map (R := R) e.symm
    (GrOperad.map (R := R) e y))) = _
  rw [map_symm_map]

variable (f g : GrOperad.Inv R (ConvOp R (FreeGr R gp) Q))

/-- **The term of a factorization** `e·(p ∘ᵢ q)` in the convolution square of `f` and `g`. -/
noncomputable def repW {i : A} (e : Without A i ⊕ B ≃ X) (p : Reg (TreeOfArity T) A)
    (q : Reg (TreeOfArity T) B) : Q X :=
  GrOperad.map (R := R) e (σ R (cSgn gp i p q) • GrOperad.comp (R := R) i
    (ConvOp.toLin (f.1 A) (GrSpecies.tw (R := R) true (SgnLin.bas (treeSgn gp) R p)))
    (ConvOp.toLin (g.1 B) (SgnLin.bas (treeSgn gp) R q)))

/-- **The term of a factorization only depends on its vertex.** -/
theorem repW_eq {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    {i : A} {i' : A'} {p : Reg (TreeOfArity T) A} {q : Reg (TreeOfArity T) B}
    {p' : Reg (TreeOfArity T) A'} {q' : Reg (TreeOfArity T) B'} {e : Without A i ⊕ B ≃ X}
    {e' : Without A' i' ⊕ B' ≃ X}
    (h : SetOperad.map e (SetOperad.comp i p q) = SetOperad.map e' (SetOperad.comp i' p' q'))
    (hq : (treeOf q).isLeaf = false) (hq' : (treeOf q').isLeaf = false)
    (hv : vert i p = vert i' p') : repW f g e p q = repW f g e' p' q' := by
  have c1 := cutV_vert (rfl : SetOperad.map e (SetOperad.comp i p q) = _) hq
  have c2 := cutV_vert h.symm hq'
  rw [hv, c2] at c1
  simp only [Prod.mk.injEq] at c1
  obtain ⟨hp1, hq1, hr1⟩ := c1
  obtain ⟨α, rfl⟩ := exists_map_eq hp1.symm
  obtain ⟨β, rfl⟩ := exists_map_eq hq1.symm
  have hi : α i = i' := by
    apply (SetOperad.map α p).1.rank_injective
    rw [hr1, map_fst, LinOrd.rank_map, Equiv.symm_apply_apply]
  subst hi
  rw [← SetOperad.map_comp, ← SetOperad.map_trans] at h
  obtain rfl := eq_of_map_eq h
  have hs : cSgn gp (α i) (SetOperad.map α p) (SetOperad.map β q) = cSgn gp i p q := by
    simp only [cSgn, treeOf_map, map_fst, LinOrd.rank_map, Equiv.symm_apply_apply]
  have htw : GrSpecies.tw (R := R) true (GrOperad.map (R := R) α (SgnLin.bas (treeSgn gp) R p))
      = GrOperad.map (R := R) α (GrSpecies.tw (R := R) true (SgnLin.bas (treeSgn gp) R p)) :=
    (GrSpecies.map_tw true α _).symm
  unfold repW
  rw [hs, ← SgnLin.map_bas, ← SgnLin.map_bas, htw, inv_toLin_map f α,
    inv_toLin_map g β, ← GrOperad.map_comp, GrOperad.map_trans, map_smul]

/-- **The term of the convolution square at a vertex**: the term of the cut there. -/
noncomputable def starV (t : Reg (TreeOfArity T) X) (v : ℕ) : Q X :=
  if hv : v < (treeOf t).weight then
    repW f g (Classical.choose (exists_rep t hv)) (stdT ((treeOf t).cutV v).1)
      (stdT ((treeOf t).cutV v).2.1)
  else 0

/-- **The term at a vertex is the term of any factorization with that vertex.** -/
theorem starV_eq {i : A} {p : Reg (TreeOfArity T) A} {q : Reg (TreeOfArity T) B}
    {e : Without A i ⊕ B ≃ X} {t : Reg (TreeOfArity T) X}
    (h : SetOperad.map e (SetOperad.comp i p q) = t) (hq : (treeOf q).isLeaf = false) :
    starV f g t (vert i p) = repW f g e p q := by
  have hv : vert i p < (treeOf t).weight := by
    rw [weight_rep h]
    show (treeOf p).vb (p.1.rank i) < _
    have h2 := Tree.vb_le_weight (treeOf p) (p.1.rank i)
    have h3 := Tree.one_le_weight hq
    omega
  rw [starV, dif_pos hv]
  refine repW_eq f g ?_ (Tree.isLeaf_cutV _ _ hv) hq ?_
  · rw [Classical.choose_spec (exists_rep t hv), h]
  · show (treeOf (stdT _)).vb ((stdT _).1.rank _) = vert i p
    rw [treeOf_stdT, rank_stdT]
    exact Tree.vb_cutV _ _ hv

/-- **The inputs above the vertex of a factorization at a splitting** form the window of ranks of
the inner tree. -/
lemma mem_of_rep {S : Finset X} {p : Reg (TreeOfArity T) (SOut S)}
    {q : Reg (TreeOfArity T) (SIn S)} {t : Reg (TreeOfArity T) X}
    (h : SetOperad.map (splitEquiv S) (SetOperad.comp none p q) = t) (a : X) :
    a ∈ S ↔ (p.1.rank none ≤ t.1.rank a ∧ t.1.rank a < p.1.rank none + (treeOf q).arity) := by
  have ht : t.1 = LinOrd.map (splitEquiv S) (LinOrd.comp none p.1 q.1) := by
    rw [← h]
    rfl
  have hc : (treeOf q).arity = Fintype.card (SIn S) := by
    rw [treeOf_arity]
    exact q.2.2
  rw [ht, LinOrd.rank_map, hc, LinOrd.mem_window]
  constructor
  · intro ha
    exact ⟨⟨a, ha⟩, by simp [splitEquiv, ha]⟩
  · rintro ⟨b, hb⟩
    have := congrArg (splitEquiv S) hb
    rw [Equiv.apply_symm_apply, splitEquiv_inr] at this
    rw [this]
    exact b.2

/-- **The convolution square on a basis tree, vertex by vertex**: for `g` odd, and `f`, `g`
killing the trivial trees, the sum of the terms at the vertices other than the root with inputs
above them. -/
theorem star_bas (hg : ∀ (B : Type) [Fintype B] [DecidableEq B], ConvOp.IsParC true (g.1 B))
    (hf0 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity T) A),
      (treeOf x).isLeaf = true → ConvOp.toLin (f.1 A) (SgnLin.bas (treeSgn gp) R x) = 0)
    (hg0 : ∀ (B : Type) [Fintype B] [DecidableEq B] (x : Reg (TreeOfArity T) B),
      (treeOf x).isLeaf = true → ConvOp.toLin (g.1 B) (SgnLin.bas (treeSgn gp) R x) = 0)
    (t : Reg (TreeOfArity T) X) :
    ConvOp.toLin ((GrOperad.Inv.star R _ f g).1 X) (SgnLin.bas (treeSgn gp) R t)
      = ∑ v ∈ (Finset.Ico 1 (treeOf t).weight).filter
          (fun v => 0 < ((treeOf t).cutV v).2.1.arity), starV f g t v := by
  have h1 : ConvOp.toLin ((GrOperad.Inv.star R _ f g).1 X) (SgnLin.bas (treeSgn gp) R t)
      = ∑ x ∈ (nonempties X).sigma (fun S => (SetOperad.FiniteFact.finite none
          (SetOperad.map (splitEquiv S).symm t)).toFinset),
          repW f g (splitEquiv x.1) x.2.1 x.2.2 := by
    rw [GrOperad.Inv.star_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply,
      Finset.sum_sigma]
    refine Finset.sum_congr rfl fun S _ => ?_
    show ConvOp.toLin (ConvOp.mapC (splitEquiv S)
      (ConvOp.compC none (f.1 (SOut S)) (g.1 (SIn S)))) _ = _
    rw [ConvOp.mapC_apply]
    show GrOperad.map (R := R) (splitEquiv S) (ConvOp.toLin (ConvOp.compC none _ _)
      (GrOperad.map (R := R) (splitEquiv S).symm _)) = _
    rw [SgnLin.map_bas, compC_bas none _ (hg (SIn S)), map_sum]
    rfl
  rw [h1, ← Finset.sum_filter_of_ne (p := fun x => (treeOf x.2.1).isLeaf = false ∧
    (treeOf x.2.2).isLeaf = false)]
  swap
  · rintro ⟨S, p, q⟩ _ hne
    by_contra hc
    apply hne
    dsimp only at hc ⊢
    unfold repW
    by_cases hp : (treeOf p).isLeaf = false
    · have hq : (treeOf q).isLeaf = true := by
        simpa [hp] using hc
      rw [hg0 _ q hq, map_zero, smul_zero, map_zero]
    · have hp' : (treeOf p).isLeaf = true := by simpa using hp
      have h0 : ConvOp.toLin (f.1 (SOut S))
          (GrSpecies.tw (R := R) true (SgnLin.bas (treeSgn gp) R p)) = 0 := by
        rw [tw_bas', map_smul, hf0 _ p hp', smul_zero]
      rw [h0, LinearMap.map_zero₂, smul_zero, map_zero]
  refine Finset.sum_bij (fun x _ => vert none x.2.1) ?_ ?_ ?_ ?_
  · rintro ⟨S, p, q⟩ hx
    rw [Finset.mem_filter, Finset.mem_sigma] at hx
    obtain ⟨⟨hS, hpq⟩, hp, hq⟩ := hx
    have hrep : SetOperad.map (splitEquiv S) (SetOperad.comp none p q) = t := by
      rw [(mem_fib (pq := (p, q))).1 hpq, SetOperad.map_map_symm]
    refine Finset.mem_filter.2 ⟨vert_mem hrep hp hq, ?_⟩
    rw [cutV_vert hrep hq, treeOf_arity, q.2.2]
    exact Fintype.card_pos_iff.2 (by
      obtain ⟨a, ha⟩ := (Finset.mem_filter.1 hS).2
      exact ⟨⟨a, ha⟩⟩)
  · rintro ⟨S₁, p₁, q₁⟩ hx₁ ⟨S₂, p₂, q₂⟩ hx₂ hv
    rw [Finset.mem_filter, Finset.mem_sigma] at hx₁ hx₂
    obtain ⟨⟨hS₁, hpq₁⟩, -, hq₁⟩ := hx₁
    obtain ⟨⟨hS₂, hpq₂⟩, -, hq₂⟩ := hx₂
    have hrep₁ : SetOperad.map (splitEquiv S₁) (SetOperad.comp none p₁ q₁) = t := by
      rw [(mem_fib (pq := (p₁, q₁))).1 hpq₁, SetOperad.map_map_symm]
    have hrep₂ : SetOperad.map (splitEquiv S₂) (SetOperad.comp none p₂ q₂) = t := by
      rw [(mem_fib (pq := (p₂, q₂))).1 hpq₂, SetOperad.map_map_symm]
    have c1 := cutV_vert hrep₁ hq₁
    have c2 := cutV_vert hrep₂ hq₂
    dsimp only at hv
    rw [hv, c2] at c1
    simp only [Prod.mk.injEq] at c1
    obtain ⟨hp, hq, hr⟩ := c1
    have hS : S₁ = S₂ := by
      ext a
      rw [mem_of_rep hrep₁, mem_of_rep hrep₂, hr, hq]
    subst hS
    have hc : SetOperad.comp none p₁ q₁ = SetOperad.comp none p₂ q₂ := by
      rw [(mem_fib (pq := (p₁, q₁))).1 hpq₁, (mem_fib (pq := (p₂, q₂))).1 hpq₂]
    obtain ⟨a, ha⟩ := (Finset.mem_filter.1 hS₁).2
    have ho := LinOrd.comp_cancel (⟨a, ha⟩ : SIn S₁) (congrArg Prod.fst hc)
    rw [reg_ext ho.1 hp.symm, reg_ext ho.2 hq.symm]
  · intro v hv
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.1 hv
    rw [Finset.mem_Ico] at hv1
    obtain ⟨e, he⟩ := exists_rep t hv1.2
    obtain ⟨S, hSdef⟩ : ∃ S : Finset X, S = Finset.univ.map ⟨fun b => e (Sum.inr b),
        fun b b' h => by simpa using e.injective h⟩ := ⟨_, rfl⟩
    have hS : ∀ x, x ∈ S ↔ ∃ b, e (Sum.inr b) = x := fun x => by simp [hSdef]
    have hcanon := map_comp_canon_reg e S hS (stdT ((treeOf t).cutV v).1)
      (stdT ((treeOf t).cutV v).2.1)
    rw [he] at hcanon
    have hfact : SetOperad.comp none
        (SetOperad.map (GrOperad.canonOut e S hS) (stdT ((treeOf t).cutV v).1))
        (SetOperad.map (GrOperad.canonIn e S hS) (stdT ((treeOf t).cutV v).2.1))
          = SetOperad.map (splitEquiv S).symm t := by
      conv_rhs => rw [hcanon]
      rw [SetOperad.map_symm_map]
    refine ⟨⟨S, SetOperad.map (GrOperad.canonOut e S hS) (stdT ((treeOf t).cutV v).1),
      SetOperad.map (GrOperad.canonIn e S hS) (stdT ((treeOf t).cutV v).2.1)⟩, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_sigma]
      exact ⟨⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨e (Sum.inr ⟨0, hv2⟩), (hS _).2 ⟨_, rfl⟩⟩⟩,
        (mem_fib).2 hfact⟩, Tree.isLeaf_cutV_fst hv1.1 hv1.2 rfl, Tree.isLeaf_cutV _ _ hv1.2⟩
    · show (treeOf (SetOperad.map (GrOperad.canonOut e S hS) (stdT _))).vb
        ((SetOperad.map (GrOperad.canonOut e S hS) (stdT _)).1.rank none) = v
      rw [treeOf_map, treeOf_stdT, map_fst, LinOrd.rank_map]
      have hsymm : (GrOperad.canonOut e S hS).symm none
          = ⟨((treeOf t).cutV v).2.2, Tree.lt_arity_cutV _ v hv1.2⟩ := by
        rw [Equiv.symm_apply_eq, GrOperad.canonOut_self]
      rw [hsymm, rank_stdT]
      exact Tree.vb_cutV _ _ hv1.2
  · rintro ⟨S, p, q⟩ hx
    rw [Finset.mem_filter, Finset.mem_sigma] at hx
    obtain ⟨⟨-, hpq⟩, -, hq⟩ := hx
    have hrep : SetOperad.map (splitEquiv S) (SetOperad.comp none p q) = t := by
      rw [(mem_fib (pq := (p, q))).1 hpq, SetOperad.map_map_symm]
    exact (starV_eq f g hrep hq).symm

/-! ## Vertices of factorizations of composites -/

variable {D : Type} [Fintype D] [DecidableEq D]

/-- **The vertex of a factorization of the inner tree of a composite**, in the composite: shifted
by the vertices before the graft point. -/
lemma vert_comp_inr (j : A) (t₁ : Reg (TreeOfArity T) A) (i₂ : B)
    (p₂ : Reg (TreeOfArity T) B) :
    vert (Sum.inr i₂) (SetOperad.comp j t₁ p₂) = vert j t₁ + vert i₂ p₂ := by
  show (treeOf (SetOperad.comp j t₁ p₂)).vb ((SetOperad.comp j t₁ p₂).1.rank (Sum.inr i₂)) = _
  rw [treeOf_comp, comp_fst, LinOrd.rank_comp_inr]
  have h1 := rank_lt_arity t₁ j
  have h2 := rank_lt_arity p₂ i₂
  rw [Tree.vb_graft_mid _ _ _ _ h1 (by omega) (by omega), Nat.add_sub_cancel_left]

/-- **The vertex of a factorization of the outer tree of a composite**, in the composite: shifted
by the vertices of the inner tree when the graft point comes first. -/
lemma vert_comp_inl {a i₁ : A} (ha : i₁ ≠ a) (p₁ : Reg (TreeOfArity T) A)
    (t₂ : Reg (TreeOfArity T) D) :
    vert (Sum.inl ⟨i₁, ha⟩) (SetOperad.comp a p₁ t₂)
      = vert i₁ p₁ + if p₁.1.rank a < p₁.1.rank i₁ then (treeOf t₂).weight else 0 := by
  show (treeOf (SetOperad.comp a p₁ t₂)).vb
    ((SetOperad.comp a p₁ t₂).1.rank (Sum.inl ⟨i₁, ha⟩)) = _
  rw [treeOf_comp, comp_fst]
  have hD : Fintype.card D = (treeOf t₂).arity := by
    rw [treeOf_arity]
    exact t₂.2.2.symm
  rcases p₁.1.total i₁ a ha with h | h
  · have hr := p₁.1.rank_lt_rank h
    rw [LinOrd.rank_comp_inl_of_lt _ _ _ _ h,
      Tree.vb_graft_of_lt _ _ _ _ hr (rank_lt_arity p₁ a), if_neg (by omega), add_zero]
  · have hr := p₁.1.rank_lt_rank h
    rw [LinOrd.rank_comp_inl_of_gt _ _ _ _ h, hD,
      Tree.vb_graft_of_gt _ _ _ _ hr (rank_lt_arity p₁ i₁), if_pos hr]

/-- **A cut above the graft point comes before it.** -/
lemma vert_lt_of_inr {i₁ : A} {p₁ : Reg (TreeOfArity T) A} {q₁ : Reg (TreeOfArity T) B}
    {e₁ : Without A i₁ ⊕ B ≃ X} {t₁ : Reg (TreeOfArity T) X}
    (h : SetOperad.map e₁ (SetOperad.comp i₁ p₁ q₁) = t₁) (hq : (treeOf q₁).isLeaf = false)
    {j : X} {b : B} (hj : e₁.symm j = Sum.inr b) : vert i₁ p₁ < vert j t₁ := by
  have hr : t₁.1.rank j = p₁.1.rank i₁ + q₁.1.rank b := by
    rw [← h, map_fst, LinOrd.rank_map, hj, comp_fst, LinOrd.rank_comp_inr]
  show (treeOf p₁).vb (p₁.1.rank i₁) < (treeOf t₁).vb (t₁.1.rank j)
  rw [treeOf_rep h, hr, Tree.vb_graft_mid _ _ _ _ (rank_lt_arity p₁ i₁) (by omega)
    (by have := rank_lt_arity q₁ b; omega)]
  have := Tree.one_le_vb hq (p₁.1.rank i₁ + q₁.1.rank b - p₁.1.rank i₁)
  omega

/-- **A cut after the graft point comes after it.** -/
lemma vert_le_of_inl_lt {i₁ : A} {p₁ : Reg (TreeOfArity T) A} {q₁ : Reg (TreeOfArity T) B}
    {e₁ : Without A i₁ ⊕ B ≃ X} {t₁ : Reg (TreeOfArity T) X}
    (h : SetOperad.map e₁ (SetOperad.comp i₁ p₁ q₁) = t₁) {j : X} {a : A} (ha : a ≠ i₁)
    (hj : e₁.symm j = Sum.inl ⟨a, ha⟩) (hlt : p₁.1.lt a i₁) : vert j t₁ ≤ vert i₁ p₁ := by
  have hr : t₁.1.rank j = p₁.1.rank a := by
    rw [← h, map_fst, LinOrd.rank_map, hj, comp_fst, LinOrd.rank_comp_inl_of_lt _ _ _ _ hlt]
  show (treeOf t₁).vb (t₁.1.rank j) ≤ (treeOf p₁).vb (p₁.1.rank i₁)
  rw [treeOf_rep h, hr, Tree.vb_graft_of_lt _ _ _ _ (p₁.1.rank_lt_rank hlt)
    (rank_lt_arity p₁ i₁)]
  exact Tree.vb_mono _ _ _ (p₁.1.rank_lt_rank hlt).le (rank_lt_arity p₁ i₁)

/-- **A cut before the graft point, not above it, comes before it.** -/
lemma vert_lt_of_inl_gt {i₁ : A} {p₁ : Reg (TreeOfArity T) A} {q₁ : Reg (TreeOfArity T) B}
    {e₁ : Without A i₁ ⊕ B ≃ X} {t₁ : Reg (TreeOfArity T) X}
    (h : SetOperad.map e₁ (SetOperad.comp i₁ p₁ q₁) = t₁) (hq : (treeOf q₁).isLeaf = false)
    {j : X} {a : A} (ha : a ≠ i₁) (hj : e₁.symm j = Sum.inl ⟨a, ha⟩) (hgt : p₁.1.lt i₁ a) :
    vert i₁ p₁ < vert j t₁ := by
  have hB : Fintype.card B = (treeOf q₁).arity := by
    rw [treeOf_arity]
    exact q₁.2.2.symm
  have hr : t₁.1.rank j = p₁.1.rank a - 1 + (treeOf q₁).arity := by
    rw [← h, map_fst, LinOrd.rank_map, hj, comp_fst, LinOrd.rank_comp_inl_of_gt _ _ _ _ hgt, hB]
  show (treeOf p₁).vb (p₁.1.rank i₁) < (treeOf t₁).vb (t₁.1.rank j)
  rw [treeOf_rep h, hr, Tree.vb_graft_of_gt _ _ _ _ (p₁.1.rank_lt_rank hgt) (rank_lt_arity p₁ a)]
  have h1 := Tree.vb_mono (treeOf p₁) _ _ (p₁.1.rank_lt_rank hgt).le (rank_lt_arity p₁ a)
  have h2 := Tree.one_le_weight hq
  omega

/-- **Trees without nullary vertices** at the level of labelled trees: a composite has none
exactly when its factors have none. -/
lemma noNull_comp (j : A) (t₁ : Reg (TreeOfArity T) A) (t₂ : Reg (TreeOfArity T) B) :
    (treeOf (SetOperad.comp j t₁ t₂)).NoNull ↔ (treeOf t₁).NoNull ∧ (treeOf t₂).NoNull := by
  rw [treeOf_comp]
  exact Tree.noNull_graft _ _ _ (rank_lt_arity t₁ j)

end FreeGr

end Star

end Operad
