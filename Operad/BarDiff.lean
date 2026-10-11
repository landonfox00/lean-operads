/-
# The bar differential of the free graded operad

Generators of any arity with parities `gp` and a merge function `μ` adding the parities plus one
(`MergeFn.Odd`) give, on the free graded operad `FreeGr R gp`, **the bar differential**: the
signed sum of the contractions of the edges of a tree (`FreeGr.barD`), and **merge-composition**,
merging the root of a tree into the vertex of another carrying an input (`FreeGr.mcomp`).

* **The bar differential is a derivation up to merge-composition**:
  `d (x ∘ᵢ y) = d x ∘ᵢ y + (-1)^|x| x ∘ᵢ d y + x ⊛ᵢ y` (`FreeGr.barD_comp_bas`): the edges of a
  composite are those of its factors and the new edge.
-/
import Operad.TreeMerge
import Operad.GrDecCooperad

universe u v

namespace Operad

open Sym GerBV TreeOfArity
open scoped TensorProduct

/-- Splitting the vertices of a graft: those of the outer tree, the root of the grafted tree, and
its other vertices. -/
lemma sum_Ico_graft {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n m v : ℕ} (hv1 : 1 ≤ v)
    (hv : v ≤ n) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico 1 (n + m), f k
      = ∑ k ∈ Finset.Ico 1 n, f (k + if v ≤ k then m else 0) + f v
        + ∑ k ∈ Finset.Ico 1 m, f (v + k) := by
  rw [← Finset.sum_Ico_consecutive _ hv1 (show v ≤ n + m by omega),
    ← Finset.sum_Ico_consecutive _ (show v ≤ v + m by omega) (show v + m ≤ n + m by omega),
    ← Finset.sum_Ico_consecutive _ hv1 hv,
    Finset.sum_eq_sum_Ico_succ_bot (show v < v + m by omega)]
  have h1 : ∑ k ∈ Finset.Ico 1 v, f (k + if v ≤ k then m else 0) = ∑ k ∈ Finset.Ico 1 v, f k :=
    Finset.sum_congr rfl fun k hk => by
      rw [Finset.mem_Ico] at hk
      rw [if_neg (by omega), Nat.add_zero]
  have h2 : ∑ k ∈ Finset.Ico v n, f (k + if v ≤ k then m else 0)
      = ∑ k ∈ Finset.Ico (v + m) (n + m), f k := by
    rw [← Finset.sum_Ico_add']
    exact Finset.sum_congr rfl fun k hk => by
      rw [Finset.mem_Ico] at hk
      rw [if_pos hk.1]
  have h3 : ∑ k ∈ Finset.Ico 1 m, f (v + k) = ∑ k ∈ Finset.Ico (v + 1) (v + m), f k := by
    rw [show v + 1 = 1 + v by omega, show v + m = m + v by omega, ← Finset.sum_Ico_add']
    exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm]
  rw [h1, h2, h3]
  abel

namespace FreeGr

variable {T : ℕ → Type v} (μ : MergeFn T)
variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma reg_ext {x y : Reg (TreeOfArity T) A} (h1 : x.1 = y.1) (h2 : treeOf x = treeOf y) :
    x = y :=
  Reg.ext h1 (arr_ext h2)

/-! ## Contraction and merge-composition of labelled trees -/

/-- **Contracting the edge below the vertex `k`** of a planar tree with its leaves labelled. -/
def contrR (x : Reg (TreeOfArity T) A) (k : ℕ) : Reg (TreeOfArity T) A :=
  (x.1, ⟨⟨x.2.1.1, ⟨(treeOf x).contr μ k, (Tree.arity_contr μ _ k).trans (treeOf_arity x)⟩⟩,
    x.2.2⟩)

@[simp] lemma contrR_fst (x : Reg (TreeOfArity T) A) (k : ℕ) : (contrR μ x k).1 = x.1 := rfl

@[simp] lemma treeOf_contrR (x : Reg (TreeOfArity T) A) (k : ℕ) :
    treeOf (contrR μ x k) = (treeOf x).contr μ k := rfl

/-- **Merge-composition** of planar trees with their leaves labelled: the root of the second tree
merged into the vertex of the first carrying the input. -/
noncomputable def mcompR (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    Reg (TreeOfArity T) (Without A i ⊕ B) :=
  ((SetOperad.comp i x y : Reg (TreeOfArity T) _).1,
    ⟨⟨(SetOperad.comp i x y : Reg (TreeOfArity T) _).2.1.1,
      ⟨(treeOf x).mgraft μ (x.1.rank i) (treeOf y), by
        have h := treeOf_arity (SetOperad.comp i x y)
        rw [treeOf_comp, Tree.arity_graft _ _ _ (rank_lt_arity x i)] at h
        have h' := Tree.arity_mgraft μ (treeOf x) (x.1.rank i) (treeOf y) (rank_lt_arity x i)
        have := rank_lt_arity x i
        omega⟩⟩, (SetOperad.comp i x y : Reg (TreeOfArity T) _).2.2⟩)

@[simp] lemma mcompR_fst (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    (mcompR μ i x y).1 = (SetOperad.comp i x y : Reg (TreeOfArity T) _).1 := rfl

@[simp] lemma treeOf_mcompR (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    treeOf (mcompR μ i x y) = (treeOf x).mgraft μ (x.1.rank i) (treeOf y) := rfl

lemma comp_fst (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    (SetOperad.comp i x y : Reg (TreeOfArity T) _).1 = LinOrd.comp i x.1 y.1 := rfl

variable (gp : ∀ k, T k → Bool)

/-- **The sign of merge-composing.** -/
noncomputable def mcompSgn (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) : Bool :=
  xor (Tree.tpar gp (treeOf y) && Tree.apar gp (treeOf x) (x.1.rank i))
    (Tree.mgSgn gp (treeOf x) (x.1.rank i) (Tree.rpar gp (treeOf y)))

lemma sgn_treeSgn (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    SgnData.sgn i ((treeSgn gp).app A x) ((treeSgn gp).app B y)
      = (Tree.tpar gp (treeOf y) && Tree.apar gp (treeOf x) (x.1.rank i)) := rfl

lemma tot_treeSgn (x : Reg (TreeOfArity T) A) :
    ((treeSgn gp).app A x).tot = Tree.tpar gp (treeOf x) := rfl

/-! ## The bar differential and merge-composition -/

variable (R : Type u) [CommRing R]

/-- **The bar differential on the free graded operad**: the signed sum of the contractions of the
edges of a tree. -/
noncomputable def barD (A : Type) [Fintype A] [DecidableEq A] :
    FreeGr R gp A →ₗ[R] FreeGr R gp A :=
  Finsupp.linearCombination R fun x : Reg (TreeOfArity T) A =>
    (∑ k ∈ Finset.Ico 1 (treeOf x).weight,
      σ R (Tree.contrSgn gp (treeOf x) k) • SgnLin.bas (treeSgn gp) R (contrR μ x k) :
        FreeGr R gp A)

lemma barD_bas (x : Reg (TreeOfArity T) A) :
    barD μ gp R A (SgnLin.bas (treeSgn gp) R x)
      = ∑ k ∈ Finset.Ico 1 (treeOf x).weight,
          σ R (Tree.contrSgn gp (treeOf x) k) • SgnLin.bas (treeSgn gp) R (contrR μ x k) := by
  unfold barD
  exact (Finsupp.linearCombination_single R _ _).trans (one_smul R _)

/-- **Merge-composition on the free graded operad**: the root of the second tree merged into the
vertex of the first carrying the input, zero when one of the trees is trivial. -/
noncomputable def mcomp (i : A) :
    FreeGr R gp A →ₗ[R] FreeGr R gp B →ₗ[R] FreeGr R gp (Without A i ⊕ B) :=
  Finsupp.linearCombination R fun x : Reg (TreeOfArity T) A =>
    Finsupp.linearCombination R fun y : Reg (TreeOfArity T) B =>
      (if (treeOf x).isLeaf = false ∧ (treeOf y).isLeaf = false then
        σ R (mcompSgn gp i x y) • SgnLin.bas (treeSgn gp) R (mcompR μ i x y) else 0 :
          FreeGr R gp (Without A i ⊕ B))

lemma mcomp_bas (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    mcomp μ gp R i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y)
      = if (treeOf x).isLeaf = false ∧ (treeOf y).isLeaf = false then
          σ R (mcompSgn gp i x y) • SgnLin.bas (treeSgn gp) R (mcompR μ i x y) else 0 := by
  unfold mcomp
  exact (LinearMap.congr_fun
    ((Finsupp.linearCombination_single R (1 : R) x).trans (one_smul R _)) _).trans
      ((Finsupp.linearCombination_single R (1 : R) y).trans (one_smul R _))

/-! ## The bar differential of a composite -/

variable {μ gp R}

lemma comp_bas_eq (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y)
      = σ R (Tree.tpar gp (treeOf y) && Tree.apar gp (treeOf x) (x.1.rank i)) •
          SgnLin.bas (treeSgn gp) R (SetOperad.comp i x y) :=
  SgnLin.comp_bas i x y

/-- **The bar differential of a composite**: `d (x ∘ᵢ y) = d x ∘ᵢ y + (-1)^|x| x ∘ᵢ d y + x ⊛ᵢ y`.
The edges of a composite are those of its factors and the new edge, whose contraction is the
merge-composite. -/
lemma barD_bas_of_isLeaf {x : Reg (TreeOfArity T) A} (hx : (treeOf x).isLeaf = true) :
    barD μ gp R A (SgnLin.bas (treeSgn gp) R x) = 0 := by
  rw [barD_bas, Tree.eq_leaf_of_isLeaf hx, Tree.weight_leaf, Finset.Ico_eq_empty_of_le zero_le_one,
    Finset.sum_empty]

/-- Contracting an edge of the outer tree of a composite. -/
lemma contrR_comp_outer (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k < (treeOf x).weight) :
    contrR μ (SetOperad.comp i x y)
        (k + if (treeOf x).vb (x.1.rank i) ≤ k then (treeOf y).weight else 0)
      = SetOperad.comp i (contrR μ x k) y := by
  refine reg_ext rfl ?_
  rw [treeOf_contrR, treeOf_comp, treeOf_comp, treeOf_contrR, contrR_fst]
  by_cases hy : (treeOf y).isLeaf = true
  · rw [Tree.eq_leaf_of_isLeaf hy, Tree.graft_leaf_right, Tree.graft_leaf_right, Tree.weight_leaf]
    simp
  · exact Tree.contr_graft_outer μ (rank_lt_arity x i) (by simpa using hy) hk1 hk

/-- Contracting an edge of the inner tree of a composite. -/
lemma contrR_comp_inner (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k < (treeOf y).weight) :
    contrR μ (SetOperad.comp i x y) ((treeOf x).vb (x.1.rank i) + k)
      = SetOperad.comp i x (contrR μ y k) := by
  refine reg_ext rfl ?_
  rw [treeOf_contrR, treeOf_comp, treeOf_comp, treeOf_contrR]
  exact Tree.contr_graft_inner μ (rank_lt_arity x i) hk1 hk

/-- Contracting the edge of a composition is merge-composing. -/
lemma contrR_comp_root (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B)
    (hy : (treeOf y).isLeaf = false) :
    contrR μ (SetOperad.comp i x y) ((treeOf x).vb (x.1.rank i)) = mcompR μ i x y := by
  refine reg_ext rfl ?_
  rw [treeOf_contrR, treeOf_comp, treeOf_mcompR]
  exact Tree.contr_graft_root μ (rank_lt_arity x i) hy

/-- **The bar differential of a composite**: `d (x ∘ᵢ y) = d x ∘ᵢ y + (-1)^|x| x ∘ᵢ d y + x ⊛ᵢ y`.
The edges of a composite are those of its factors and the new edge, whose contraction is the
merge-composite. -/
theorem barD_comp_bas (hμ : MergeFn.Odd gp μ) (i : A) (x : Reg (TreeOfArity T) A)
    (y : Reg (TreeOfArity T) B) :
    barD μ gp R _ (GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R x)
        (SgnLin.bas (treeSgn gp) R y))
      = GrOperad.comp (R := R) i (barD μ gp R A (SgnLin.bas (treeSgn gp) R x))
          (SgnLin.bas (treeSgn gp) R y)
        + σ R (Tree.tpar gp (treeOf x)) • GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R x)
          (barD μ gp R B (SgnLin.bas (treeSgn gp) R y))
        + mcomp μ gp R i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y) := by
  have hr := rank_lt_arity x i
  have ht := treeOf_comp i x y
  have hw : (treeOf (SetOperad.comp i x y)).weight = (treeOf x).weight + (treeOf y).weight := by
    rw [ht, Tree.weight_graft _ _ _ hr]
  -- the outer terms
  have houter : ∀ k ∈ Finset.Ico 1 (treeOf x).weight,
      σ R (Tree.tpar gp (treeOf y) && Tree.apar gp (treeOf x) (x.1.rank i)) •
        σ R (Tree.contrSgn gp (treeOf (SetOperad.comp i x y))
          (k + if (treeOf x).vb (x.1.rank i) ≤ k then (treeOf y).weight else 0)) •
        SgnLin.bas (treeSgn gp) R (contrR μ (SetOperad.comp i x y)
          (k + if (treeOf x).vb (x.1.rank i) ≤ k then (treeOf y).weight else 0))
      = σ R (Tree.contrSgn gp (treeOf x) k) • GrOperad.comp (R := R) i
          (SgnLin.bas (treeSgn gp) R (contrR μ x k)) (SgnLin.bas (treeSgn gp) R y) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [contrR_comp_outer i x y hk.1 hk.2, comp_bas_eq, smul_smul, smul_smul, ← σ_xor, ← σ_xor,
      treeOf_contrR, contrR_fst]
    congr 2
    by_cases hy : (treeOf y).isLeaf = true
    · rw [ht, Tree.eq_leaf_of_isLeaf hy, Tree.graft_leaf_right, Tree.tpar_leaf, Tree.weight_leaf]
      simp
    · rw [ht]
      exact Tree.contrSgn_graft_outer μ gp hμ hr (by simpa using hy) hk.1 hk.2
  -- the inner terms
  have hinner : ∀ k ∈ Finset.Ico 1 (treeOf y).weight,
      σ R (Tree.tpar gp (treeOf y) && Tree.apar gp (treeOf x) (x.1.rank i)) •
        σ R (Tree.contrSgn gp (treeOf (SetOperad.comp i x y))
          ((treeOf x).vb (x.1.rank i) + k)) •
        SgnLin.bas (treeSgn gp) R (contrR μ (SetOperad.comp i x y)
          ((treeOf x).vb (x.1.rank i) + k))
      = σ R (Tree.tpar gp (treeOf x)) • σ R (Tree.contrSgn gp (treeOf y) k) •
          GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R x)
            (SgnLin.bas (treeSgn gp) R (contrR μ y k)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [contrR_comp_inner i x y hk.1 hk.2, comp_bas_eq, smul_smul, smul_smul, smul_smul,
      ← σ_xor, ← σ_xor, ← σ_xor, treeOf_contrR, ht,
      Tree.contrSgn_graft_inner gp hr hk.1 hk.2, Tree.tpar_contr μ gp hμ hk.1 hk.2]
    congr 2
    cases Tree.tpar gp (treeOf y) <;> cases Tree.apar gp (treeOf x) (x.1.rank i) <;>
      cases Tree.tpar gp (treeOf x) <;> cases Tree.contrSgn gp (treeOf y) k <;> rfl
  -- the root term
  have hroot (hy : (treeOf y).isLeaf = false) (hx : (treeOf x).isLeaf = false) :
      σ R (Tree.tpar gp (treeOf y) && Tree.apar gp (treeOf x) (x.1.rank i)) •
        σ R (Tree.contrSgn gp (treeOf (SetOperad.comp i x y)) ((treeOf x).vb (x.1.rank i))) •
        SgnLin.bas (treeSgn gp) R (contrR μ (SetOperad.comp i x y) ((treeOf x).vb (x.1.rank i)))
      = mcomp μ gp R i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y) := by
    rw [mcomp_bas, if_pos ⟨hx, hy⟩, contrR_comp_root i x y hy, smul_smul, ← σ_xor, ht,
      Tree.contrSgn_graft_root gp hr hy]
    rfl
  have hL : barD μ gp R _ (GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R x)
        (SgnLin.bas (treeSgn gp) R y))
      = ∑ k ∈ Finset.Ico 1 ((treeOf x).weight + (treeOf y).weight),
          σ R (Tree.tpar gp (treeOf y) && Tree.apar gp (treeOf x) (x.1.rank i)) •
            σ R (Tree.contrSgn gp (treeOf (SetOperad.comp i x y)) k) •
            SgnLin.bas (treeSgn gp) R (contrR μ (SetOperad.comp i x y) k) := by
    rw [comp_bas_eq, map_smul, barD_bas, Finset.smul_sum, hw]
  have hR1 : GrOperad.comp (R := R) i (barD μ gp R A (SgnLin.bas (treeSgn gp) R x))
        (SgnLin.bas (treeSgn gp) R y)
      = ∑ k ∈ Finset.Ico 1 (treeOf x).weight, σ R (Tree.contrSgn gp (treeOf x) k) •
          GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R (contrR μ x k))
            (SgnLin.bas (treeSgn gp) R y) := by
    rw [barD_bas, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply]
  have hR2 : σ R (Tree.tpar gp (treeOf x)) • GrOperad.comp (R := R) i
        (SgnLin.bas (treeSgn gp) R x) (barD μ gp R B (SgnLin.bas (treeSgn gp) R y))
      = ∑ k ∈ Finset.Ico 1 (treeOf y).weight, σ R (Tree.tpar gp (treeOf x)) •
          σ R (Tree.contrSgn gp (treeOf y) k) • GrOperad.comp (R := R) i
            (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R (contrR μ y k)) := by
    rw [barD_bas, map_sum, Finset.smul_sum]
    simp only [map_smul]
  rw [hL, hR1, hR2]
  by_cases hy : (treeOf y).isLeaf = true
  · have hwy : (treeOf y).weight = 0 := by rw [Tree.eq_leaf_of_isLeaf hy]; rfl
    rw [mcomp_bas, if_neg (by simp [hy]), add_zero, hwy, Nat.add_zero,
      Finset.Ico_eq_empty_of_le zero_le_one, Finset.sum_empty, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← houter k hk, hwy]
    simp only [ite_self, Nat.add_zero]
  by_cases hx : (treeOf x).isLeaf = true
  · have hv : (treeOf x).vb (x.1.rank i) = 0 := by rw [Tree.eq_leaf_of_isLeaf hx]; rfl
    have hwx : (treeOf x).weight = 0 := by rw [Tree.eq_leaf_of_isLeaf hx]; rfl
    rw [mcomp_bas, if_neg (by simp [hx]), add_zero, hwx, Nat.zero_add,
      Finset.Ico_eq_empty_of_le zero_le_one, Finset.sum_empty, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← hinner k hk, hv, Nat.zero_add]
  have hx' : (treeOf x).isLeaf = false := by simpa using hx
  have hy' : (treeOf y).isLeaf = false := by simpa using hy
  rw [sum_Ico_graft _ (Tree.vb_pos hx' _) (Tree.vb_le_weight _ _) (Tree.weight_pos hy'),
    hroot hy' hx']
  rw [Finset.sum_congr rfl houter, Finset.sum_congr rfl hinner]
  abel

/-! ## The bar differential is a coderivation -/

/-- A labelled tree with its tree replaced by one with as many leaves. -/
def withTree (x : Reg (TreeOfArity T) A) (t : Tree T) (h : t.arity = (treeOf x).arity) :
    Reg (TreeOfArity T) A :=
  (x.1, ⟨⟨x.2.1.1, ⟨t, h.trans (treeOf_arity x)⟩⟩, x.2.2⟩)

@[simp] lemma withTree_fst (x : Reg (TreeOfArity T) A) (t : Tree T)
    (h : t.arity = (treeOf x).arity) : (withTree x t h).1 = x.1 := rfl

@[simp] lemma treeOf_withTree (x : Reg (TreeOfArity T) A) (t : Tree T)
    (h : t.arity = (treeOf x).arity) : treeOf (withTree x t h) = t := rfl

variable (gp R) in
/-- **The decomposition of a basis element**: the signed sum of its factorizations. -/
lemma decomp_bas (i : A) (s : Reg (TreeOfArity T) (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := FreeGr R gp) i (SgnLin.bas (treeSgn gp) R s)
      = ∑ pq ∈ (SetOperad.FiniteFact.finite i s).toFinset,
          σ R (Tree.tpar gp (treeOf pq.2) && Tree.apar gp (treeOf pq.1) (pq.1.1.rank i)) •
            (SgnLin.bas (treeSgn gp) R pq.1 ⊗ₜ[R] SgnLin.bas (treeSgn gp) R pq.2) := by
  refine (SgnLin.decompT_single (treeSgn gp) i s (1 : R)).trans
    (Finset.sum_congr rfl fun pq _ => ?_)
  rw [mul_one]
  rfl

lemma mem_fib {i : A} {s : Reg (TreeOfArity T) (Without A i ⊕ B)}
    {pq : Reg (TreeOfArity T) A × Reg (TreeOfArity T) B} :
    pq ∈ (SetOperad.FiniteFact.finite i s).toFinset ↔ SetOperad.comp i pq.1 pq.2 = s :=
  SgnLin.mem_fact_iff i s pq

/-- The tree and the order of a factorization. -/
lemma comp_eq_iff {i : A} {p : Reg (TreeOfArity T) A} {q : Reg (TreeOfArity T) B}
    {s : Reg (TreeOfArity T) (Without A i ⊕ B)} :
    SetOperad.comp i p q = s ↔
      LinOrd.comp i p.1 q.1 = s.1 ∧ (treeOf p).graft (p.1.rank i) (treeOf q) = treeOf s := by
  constructor
  · rintro rfl
    exact ⟨rfl, (treeOf_comp i p q).symm⟩
  · rintro ⟨h1, h2⟩
    exact reg_ext h1 ((treeOf_comp i p q).trans h2)


variable (gp) in
/-- The sign of a composite of labelled trees. -/
noncomputable abbrev cSgn (i : A) (p : Reg (TreeOfArity T) A) (q : Reg (TreeOfArity T) B) : Bool :=
  Tree.tpar gp (treeOf q) && Tree.apar gp (treeOf p) (p.1.rank i)

variable (μ gp R) in
/-- The terms of the decomposition of the bar differential of a basis element, indexed by an
edge and a factorization of its contraction. -/
noncomputable def decTermL (i : A) (s : Reg (TreeOfArity T) (Without A i ⊕ B))
    (x : (_ : ℕ) × (Reg (TreeOfArity T) A × Reg (TreeOfArity T) B)) :
    FreeGr R gp A ⊗[R] FreeGr R gp B :=
  (σ R (Tree.contrSgn gp (treeOf s) x.1) * σ R (cSgn gp i x.2.1 x.2.2)) •
    (SgnLin.bas (treeSgn gp) R x.2.1 ⊗ₜ[R] SgnLin.bas (treeSgn gp) R x.2.2)

variable (μ gp R) in
/-- The terms of the bar differential of the outer factors of the decomposition. -/
noncomputable def decTermO (i : A)
    (y : (_ : Reg (TreeOfArity T) A × Reg (TreeOfArity T) B) × ℕ) :
    FreeGr R gp A ⊗[R] FreeGr R gp B :=
  (σ R (cSgn gp i y.1.1 y.1.2) * σ R (Tree.contrSgn gp (treeOf y.1.1) y.2)) •
    (SgnLin.bas (treeSgn gp) R (contrR μ y.1.1 y.2) ⊗ₜ[R] SgnLin.bas (treeSgn gp) R y.1.2)

variable (μ gp R) in
/-- The terms of the bar differential of the inner factors of the decomposition. -/
noncomputable def decTermI (i : A)
    (y : (_ : Reg (TreeOfArity T) A × Reg (TreeOfArity T) B) × ℕ) :
    FreeGr R gp A ⊗[R] FreeGr R gp B :=
  (σ R (cSgn gp i y.1.1 y.1.2) *
      (σ R (Tree.tpar gp (treeOf y.1.1)) * σ R (Tree.contrSgn gp (treeOf y.1.2) y.2))) •
    (SgnLin.bas (treeSgn gp) R y.1.1 ⊗ₜ[R] SgnLin.bas (treeSgn gp) R (contrR μ y.1.2 y.2))

lemma decomp_barD_bas_eq (i : A) (s : Reg (TreeOfArity T) (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := FreeGr R gp) i (barD μ gp R _ (SgnLin.bas (treeSgn gp) R s))
      = ∑ x ∈ (Finset.Ico 1 (treeOf s).weight).sigma
          (fun k => (SetOperad.FiniteFact.finite i (contrR μ s k)).toFinset),
          decTermL gp R i s x := by
  rw [barD_bas, map_sum, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, decomp_bas, Finset.smul_sum]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [smul_smul]
  rfl

lemma map_barD_id_decomp_bas (i : A) (s : Reg (TreeOfArity T) (Without A i ⊕ B)) :
    TensorProduct.map (barD μ gp R A) LinearMap.id
        (GrCooperad.decomp (R := R) (C := FreeGr R gp) i (SgnLin.bas (treeSgn gp) R s))
      = ∑ y ∈ (SetOperad.FiniteFact.finite i s).toFinset.sigma
          (fun pq => Finset.Ico 1 (treeOf pq.1).weight), decTermO μ gp R i y := by
  rw [decomp_bas, map_sum, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [map_smul, TensorProduct.map_tmul, LinearMap.id_apply, barD_bas, TensorProduct.sum_tmul,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.smul_tmul', smul_smul]
  rfl

lemma map_tw_barD_decomp_bas (i : A) (s : Reg (TreeOfArity T) (Without A i ⊕ B)) :
    TensorProduct.map (GrSpecies.tw (R := R) (V := FreeGr R gp) true) (barD μ gp R B)
        (GrCooperad.decomp (R := R) (C := FreeGr R gp) i (SgnLin.bas (treeSgn gp) R s))
      = ∑ y ∈ (SetOperad.FiniteFact.finite i s).toFinset.sigma
          (fun pq => Finset.Ico 1 (treeOf pq.2).weight), decTermI μ gp R i y := by
  have htw : ∀ p : Reg (TreeOfArity T) A, GrSpecies.tw (R := R) (V := FreeGr R gp) true
      (SgnLin.bas (treeSgn gp) R p)
        = σ R (Tree.tpar gp (treeOf p)) • SgnLin.bas (treeSgn gp) R p :=
    fun p => (GrSpecies.tw_hom true (SgnLin.par_bas p)).trans (by rw [Bool.true_and]; rfl)
  rw [decomp_bas, map_sum, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [map_smul, TensorProduct.map_tmul, htw, barD_bas, TensorProduct.tmul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [decTermI, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  congr 1
  ring_nf

variable (μ) in
/-- The vertex of a composite, and the factorization of the contraction at that vertex, given by an
edge of a factor of a factorization. -/
noncomputable def liftIdx (i : A) :
    ((_ : Reg (TreeOfArity T) A × Reg (TreeOfArity T) B) × ℕ) ⊕
        ((_ : Reg (TreeOfArity T) A × Reg (TreeOfArity T) B) × ℕ) →
      (_ : ℕ) × (Reg (TreeOfArity T) A × Reg (TreeOfArity T) B) :=
  Sum.elim
    (fun y => ⟨y.2 + if (treeOf y.1.1).vb (y.1.1.1.rank i) ≤ y.2 then (treeOf y.1.2).weight
      else 0, (contrR μ y.1.1 y.2, y.1.2)⟩)
    (fun y => ⟨(treeOf y.1.1).vb (y.1.1.1.rank i) + y.2, (y.1.1, contrR μ y.1.2 y.2)⟩)

/-- **The bar differential is a coderivation**, on basis elements:
`Δᵢ (d x) = (d ⊗ 1) (Δᵢ x) + (1 ⊗ d) (Δᵢ x)`, with the Koszul sign of `d` passing the outer
factor. A factorization of a contracted tree is a factorization of the tree with the contracted
edge in one of its factors, in exactly one way. -/
theorem decomp_barD_bas (hμ : MergeFn.Odd gp μ) (i : A)
    (s : Reg (TreeOfArity T) (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := FreeGr R gp) i
        (barD μ gp R _ (SgnLin.bas (treeSgn gp) R s))
      = TensorProduct.map (barD μ gp R A) LinearMap.id
          (GrCooperad.decomp (R := R) (C := FreeGr R gp) i (SgnLin.bas (treeSgn gp) R s))
        + TensorProduct.map (GrSpecies.tw (R := R) (V := FreeGr R gp) true) (barD μ gp R B)
          (GrCooperad.decomp (R := R) (C := FreeGr R gp) i (SgnLin.bas (treeSgn gp) R s)) := by
  classical
  have hfac : ∀ {p : Reg (TreeOfArity T) A} {q : Reg (TreeOfArity T) B},
      SetOperad.comp i p q = s →
        treeOf s = (treeOf p).graft (p.1.rank i) (treeOf q) ∧
          (treeOf s).weight = (treeOf p).weight + (treeOf q).weight ∧
            LinOrd.comp i p.1 q.1 = s.1 := by
    intro p q h
    have e := (comp_eq_iff.1 h)
    refine ⟨e.2.symm, ?_, e.1⟩
    rw [← e.2, Tree.weight_graft _ _ _ (rank_lt_arity p i)]
  rw [decomp_barD_bas_eq, map_barD_id_decomp_bas, map_tw_barD_decomp_bas, ← Finset.sum_sumElim]
  symm
  refine Finset.sum_bij (fun z _ => liftIdx μ i z) ?_ ?_ ?_ ?_
  · -- the images are edges and factorizations of their contractions
    rintro (⟨⟨p, q⟩, k⟩ | ⟨⟨p, q⟩, k⟩) hz
    · rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico] at hz
      dsimp only at hz
      obtain ⟨hpq, hk1, hk⟩ := hz
      obtain ⟨-, hw, -⟩ := hfac hpq
      subst hpq
      simp only [liftIdx, Sum.elim_inl, Finset.mem_sigma, Finset.mem_Ico, mem_fib]
      refine ⟨⟨by omega, by rw [hw]; split_ifs <;> omega⟩, ?_⟩
      exact (contrR_comp_outer i p q hk1 hk).symm
    · rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico] at hz
      dsimp only at hz
      obtain ⟨hpq, hk1, hk⟩ := hz
      obtain ⟨-, hw, -⟩ := hfac hpq
      subst hpq
      have := Tree.vb_le_weight (treeOf p) (p.1.rank i)
      simp only [liftIdx, Sum.elim_inr, Finset.mem_sigma, Finset.mem_Ico, mem_fib]
      refine ⟨⟨by omega, by rw [hw]; omega⟩, ?_⟩
      exact (contrR_comp_inner i p q hk1 hk).symm
  · -- the map is injective
    rintro (⟨⟨p, q⟩, k⟩ | ⟨⟨p, q⟩, k⟩) h₁ (⟨⟨p', q'⟩, k'⟩ | ⟨⟨p', q'⟩, k'⟩) h₂ heq
    · rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico] at h₁ h₂
      dsimp only at h₁ h₂
      simp only [liftIdx, Sum.elim_inl, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at heq
      obtain ⟨hi, hc, rfl⟩ := heq
      obtain ⟨ht, -, -⟩ := hfac h₁.1
      obtain ⟨ht', -, -⟩ := hfac h₂.1
      have h1 : p.1 = p'.1 := by rw [← contrR_fst μ p k, hc, contrR_fst]
      rw [← h1] at ht' hi
      have hc' : (treeOf p).contr μ k = (treeOf p').contr μ k' := by
        rw [← treeOf_contrR, ← treeOf_contrR, hc]
      by_cases hq : (treeOf q).isLeaf = true
      · rw [Tree.eq_leaf_of_isLeaf hq, Tree.graft_leaf_right] at ht ht'
        have e : p = p' := reg_ext h1 (ht.symm.trans ht')
        subst e
        rw [Tree.eq_leaf_of_isLeaf hq, Tree.weight_leaf] at hi
        simp only [ite_self, Nat.add_zero] at hi
        rw [hi]
      · have hr' : p.1.rank i < (treeOf p').arity := by rw [h1]; exact rank_lt_arity p' i
        obtain ⟨e1, e2⟩ := Tree.contr_outer_inj μ (rank_lt_arity p i) hr' (by simpa using hq)
          h₁.2.1 h₁.2.2 h₂.2.1 h₂.2.2 (ht.symm.trans ht') hc' hi
        have e : p = p' := reg_ext h1 e1
        subst e
        rw [e2]
    · rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico] at h₁
      rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico] at h₂
      dsimp only at h₁ h₂
      simp only [liftIdx, Sum.elim_inl, Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq,
        Prod.mk.injEq] at heq
      obtain ⟨hi, hc, hc'⟩ := heq
      exfalso
      obtain ⟨ht, -, -⟩ := hfac h₁.1
      obtain ⟨ht', -, -⟩ := hfac h₂.1
      have h1 : p.1 = p'.1 := by rw [← contrR_fst μ p k, hc]
      rw [← h1] at ht' hi
      have hct : (treeOf p).contr μ k = treeOf p' := by rw [← treeOf_contrR, hc]
      have hct' : (treeOf q').contr μ k' = treeOf q := by rw [← treeOf_contrR, hc']
      have hcw := Tree.weight_contr μ h₂.2.1 h₂.2.2
      exact Tree.contr_outer_ne_inner μ (rank_lt_arity p i) (Tree.isLeaf_of_weight (by omega))
        h₁.2.1 h₁.2.2 h₂.2.1 h₂.2.2 (ht.symm.trans ht') hct hct' hi
    · rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico] at h₁
      rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico] at h₂
      dsimp only at h₁ h₂
      simp only [liftIdx, Sum.elim_inl, Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq,
        Prod.mk.injEq] at heq
      obtain ⟨hi, hc, hc'⟩ := heq
      exfalso
      obtain ⟨ht, -, -⟩ := hfac h₁.1
      obtain ⟨ht', -, -⟩ := hfac h₂.1
      have h1 : p.1 = p'.1 := by rw [hc, contrR_fst]
      rw [← h1] at ht' hi
      have hct : (treeOf p').contr μ k' = treeOf p := by rw [← treeOf_contrR, ← hc]
      have hct' : (treeOf q).contr μ k = treeOf q' := by rw [← treeOf_contrR, hc']
      have hcw := Tree.weight_contr μ h₁.2.1 h₁.2.2
      have hr' : p.1.rank i < (treeOf p').arity := by rw [h1]; exact rank_lt_arity p' i
      exact Tree.contr_outer_ne_inner μ hr' (Tree.isLeaf_of_weight (by omega))
        h₂.2.1 h₂.2.2 h₁.2.1 h₁.2.2 (ht'.symm.trans ht) hct hct' hi.symm
    · rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico] at h₁ h₂
      dsimp only at h₁ h₂
      simp only [liftIdx, Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at heq
      obtain ⟨hi, rfl, hc⟩ := heq
      obtain ⟨ht, -, -⟩ := hfac h₁.1
      obtain ⟨ht', -, -⟩ := hfac h₂.1
      have h1 : q.1 = q'.1 := by rw [← contrR_fst μ q k, hc, contrR_fst]
      have e : q = q' := reg_ext h1
        (Tree.graft_inj_right (rank_lt_arity p i) (ht.symm.trans ht'))
      subst e
      have e2 : k = k' := by omega
      subst e2
      rfl
  · -- the map is surjective
    rintro ⟨k, ⟨p, q⟩⟩ hx
    rw [Finset.mem_sigma, Finset.mem_Ico, mem_fib] at hx
    dsimp only at hx
    obtain ⟨⟨hk1, hk⟩, hpq⟩ := hx
    have hr := rank_lt_arity p i
    have hst : (treeOf s).contr μ k = (treeOf p).graft (p.1.rank i) (treeOf q) := by
      rw [← treeOf_contrR, ← hpq, treeOf_comp]
    have hord : LinOrd.comp i p.1 q.1 = s.1 := by
      rw [← comp_fst, hpq, contrR_fst]
    by_cases hq : (treeOf q).isLeaf = true
    · have hst' : (treeOf s).contr μ k = treeOf p := by
        rw [hst, Tree.eq_leaf_of_isLeaf hq, Tree.graft_leaf_right]
      have har : (treeOf s).arity = (treeOf p).arity := by
        rw [← hst', Tree.arity_contr]
      refine ⟨Sum.inl ⟨(withTree p (treeOf s) har, q), k⟩, ?_, ?_⟩
      · rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico]
        refine ⟨comp_eq_iff.2 ⟨hord, ?_⟩, hk1, hk⟩
        rw [treeOf_withTree, withTree_fst, Tree.eq_leaf_of_isLeaf hq, Tree.graft_leaf_right]
      · simp only [liftIdx, Sum.elim_inl, Tree.eq_leaf_of_isLeaf hq, Tree.weight_leaf, ite_self,
          Nat.add_zero]
        congr 1
        exact Prod.ext (reg_ext rfl (by rw [treeOf_contrR, treeOf_withTree, hst'])) rfl
    · rcases Tree.contr_eq_graft μ hk1 hk hr (by simpa using hq) hst with
        ⟨a', k₁, ha', hra, hk₁1, hk₁, hca, hkk⟩ | ⟨b', k₂, hb', hbl, hk₂1, hk₂, hcb, hkk⟩
      · have har : a'.arity = (treeOf p).arity := by rw [← hca, Tree.arity_contr]
        refine ⟨Sum.inl ⟨(withTree p a' har, q), k₁⟩, ?_, ?_⟩
        · rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico]
          exact ⟨comp_eq_iff.2 ⟨hord, by rw [treeOf_withTree, withTree_fst, ha']⟩, hk₁1, hk₁⟩
        · simp only [liftIdx, Sum.elim_inl, treeOf_withTree, withTree_fst]
          rw [← hkk]
          congr 1
          exact Prod.ext (reg_ext rfl (by rw [treeOf_contrR, treeOf_withTree, hca])) rfl
      · have hbr : b'.arity = (treeOf q).arity := by rw [← hcb, Tree.arity_contr]
        refine ⟨Sum.inr ⟨(p, withTree q b' hbr), k₂⟩, ?_, ?_⟩
        · rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico]
          exact ⟨comp_eq_iff.2 ⟨by rw [withTree_fst, hord], by rw [treeOf_withTree, hb']⟩,
            hk₂1, hk₂⟩
        · simp only [liftIdx, Sum.elim_inr]
          rw [← hkk]
          congr 1
          exact Prod.ext rfl (reg_ext rfl (by rw [treeOf_contrR, treeOf_withTree, hcb]))
  · -- the terms agree
    rintro (⟨⟨p, q⟩, k⟩ | ⟨⟨p, q⟩, k⟩) hz
    · rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico] at hz
      dsimp only at hz
      obtain ⟨hpq, hk1, hk⟩ := hz
      obtain ⟨ht, -, -⟩ := hfac hpq
      have e := Tree.contrSgn_graft_outer' μ gp hμ (z := treeOf q) (rank_lt_arity p i) hk1 hk
      rw [← ht] at e
      simp only [liftIdx, Sum.elim_inl, decTermO, decTermL, cSgn, contrR_fst, treeOf_contrR]
      congr 1
      simp only [← σ_xor]
      congr 1
      revert e
      cases Tree.tpar gp (treeOf q) && Tree.apar gp (treeOf p) (p.1.rank i) <;>
        cases Tree.contrSgn gp (treeOf p) k <;>
        cases Tree.tpar gp (treeOf q) && Tree.apar gp ((treeOf p).contr μ k) (p.1.rank i) <;>
        cases Tree.contrSgn gp (treeOf s) (k + if (treeOf p).vb (p.1.rank i) ≤ k
          then (treeOf q).weight else 0) <;> decide
    · rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_Ico] at hz
      dsimp only at hz
      obtain ⟨hpq, hk1, hk⟩ := hz
      obtain ⟨ht, -, -⟩ := hfac hpq
      simp only [liftIdx, Sum.elim_inr, decTermI, decTermL, cSgn, treeOf_contrR]
      rw [ht, Tree.contrSgn_graft_inner gp (rank_lt_arity p i) hk1 hk,
        Tree.tpar_contr μ gp hμ hk1 hk]
      congr 1
      simp only [← σ_xor]
      congr 1
      cases Tree.tpar gp (treeOf q) <;> cases Tree.apar gp (treeOf p) (p.1.rank i) <;>
        cases Tree.tpar gp (treeOf p) <;> cases Tree.contrSgn gp (treeOf q) k <;> rfl

/-- **The bar differential is a coderivation**:
`Δᵢ ∘ d = (d ⊗ 1 + (-1)^• ⊗ d) ∘ Δᵢ`, the Koszul sign of `d` passing the outer factor. -/
theorem decomp_barD (hμ : MergeFn.Odd gp μ) (i : A) (x : FreeGr R gp (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := FreeGr R gp) i (barD μ gp R _ x)
      = TensorProduct.map (barD μ gp R A) LinearMap.id
          (GrCooperad.decomp (R := R) (C := FreeGr R gp) i x)
        + TensorProduct.map (GrSpecies.tw (R := R) (V := FreeGr R gp) true) (barD μ gp R B)
          (GrCooperad.decomp (R := R) (C := FreeGr R gp) i x) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity T))
    (GrCooperad.decomp (R := R) (C := FreeGr R gp) (B := B) i ∘ₗ barD μ gp R _)
    (TensorProduct.map (barD μ gp R A) LinearMap.id ∘ₗ
        GrCooperad.decomp (R := R) (C := FreeGr R gp) (B := B) i +
      TensorProduct.map (GrSpecies.tw (R := R) (V := FreeGr R gp) true) (barD μ gp R B) ∘ₗ
        GrCooperad.decomp (R := R) (C := FreeGr R gp) (B := B) i)
    (fun s => decomp_barD_bas hμ i s) x
  simpa using h

/-- **The bar differential of a composite**, for all operations:
`d (x ∘ᵢ y) = d x ∘ᵢ y + (-1)^|x| x ∘ᵢ d y + x ⊛ᵢ y`. -/
theorem barD_comp (hμ : MergeFn.Odd gp μ) (i : A) (x : FreeGr R gp A) (y : FreeGr R gp B) :
    barD μ gp R _ (GrOperad.comp (R := R) i x y)
      = GrOperad.comp (R := R) i (barD μ gp R A x) y
        + GrOperad.comp (R := R) i (GrSpecies.tw (R := R) (V := FreeGr R gp) true x)
            (barD μ gp R B y)
        + mcomp μ gp R i x y := by
  have htw : ∀ p : Reg (TreeOfArity T) A, GrSpecies.tw (R := R) (V := FreeGr R gp) true
      (SgnLin.bas (treeSgn gp) R p)
        = σ R (Tree.tpar gp (treeOf p)) • SgnLin.bas (treeSgn gp) R p :=
    fun p => (GrSpecies.tw_hom true (SgnLin.par_bas p)).trans (by rw [Bool.true_and]; rfl)
  have h : (GrOperad.comp (R := R) (P := FreeGr R gp) (B := B) i).compr₂ (barD μ gp R _)
      = (GrOperad.comp (R := R) (P := FreeGr R gp) (B := B) i).comp (barD μ gp R A)
        + ((GrOperad.comp (R := R) (P := FreeGr R gp) (B := B) i).comp
            (GrSpecies.tw (R := R) (V := FreeGr R gp) true)).compl₂ (barD μ gp R B)
        + mcomp μ gp R i := by
    refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring
      (Finsupp.lhom_ext' fun t => LinearMap.ext_ring ?_)
    have e := barD_comp_bas (R := R) hμ i s t
    show barD μ gp R _ (GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R s)
        (SgnLin.bas (treeSgn gp) R t))
      = GrOperad.comp (R := R) i (barD μ gp R A (SgnLin.bas (treeSgn gp) R s))
          (SgnLin.bas (treeSgn gp) R t)
        + GrOperad.comp (R := R) i (GrSpecies.tw (R := R) (V := FreeGr R gp) true
            (SgnLin.bas (treeSgn gp) R s)) (barD μ gp R B (SgnLin.bas (treeSgn gp) R t))
        + mcomp μ gp R i (SgnLin.bas (treeSgn gp) R s) (SgnLin.bas (treeSgn gp) R t)
    rw [htw, map_smul, LinearMap.smul_apply]
    exact e
  have := LinearMap.congr_fun (LinearMap.congr_fun h x) y
  simpa using this

/-- **The bar differential is odd.** -/
theorem par_barD (hμ : MergeFn.Odd gp μ) (b : Bool) (x : FreeGr R gp A) :
    GrOperad.par (R := R) b (barD μ gp R A x) = barD μ gp R A (GrOperad.par (R := R) (!b) x) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity T)) (GrOperad.par (R := R) b ∘ₗ barD μ gp R A)
    (barD μ gp R A ∘ₗ GrOperad.par (R := R) (P := FreeGr R gp) (A := A) (!b)) (fun s => ?_) x
  · simpa using h
  show GrOperad.par (R := R) b (barD μ gp R A (SgnLin.bas (treeSgn gp) R s))
    = barD μ gp R A (GrOperad.par (R := R) (!b) (SgnLin.bas (treeSgn gp) R s))
  have hp : ∀ (c : Bool) (t : Reg (TreeOfArity T) A),
      GrOperad.par (R := R) c (SgnLin.bas (treeSgn gp) R t)
        = if Tree.tpar gp (treeOf t) = c then SgnLin.bas (treeSgn gp) R t else 0 :=
    fun c t => SgnLin.parT_single c t 1
  rw [hp, barD_bas, map_sum]
  simp only [map_smul, hp, treeOf_contrR]
  by_cases hs : Tree.tpar gp (treeOf s) = !b
  · rw [if_pos hs, barD_bas]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rw [if_pos (by rw [Tree.tpar_contr μ gp hμ hk.1 hk.2, hs, Bool.not_not])]
  · rw [if_neg hs, map_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hc := Tree.tpar_contr μ gp hμ hk.1 hk.2
    rw [if_neg (fun h => hs (by rw [hc] at h; rw [← h, Bool.not_not])), smul_zero]

/-- **The bar differential commutes with relabellings.** -/
theorem map_barD {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (x : FreeGr R gp A) :
    GrOperad.map (R := R) e (barD μ gp R A x) = barD μ gp R A' (GrOperad.map (R := R) e x) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity T)) (GrOperad.map (R := R) e ∘ₗ barD μ gp R A)
    (barD μ gp R A' ∘ₗ GrOperad.map (R := R) (P := FreeGr R gp) e) (fun s => ?_) x
  · simpa using h
  show GrOperad.map (R := R) e (barD μ gp R A (SgnLin.bas (treeSgn gp) R s))
    = barD μ gp R A' (GrOperad.map (R := R) e (SgnLin.bas (treeSgn gp) R s))
  rw [SgnLin.map_bas, barD_bas, barD_bas, map_sum]
  simp only [map_smul, SgnLin.map_bas]
  rfl

/-- **The bar differential kills the counit.** -/
theorem counit_barD (x : FreeGr R gp Unit) :
    GrCooperad.counit (R := R) (C := FreeGr R gp) (barD μ gp R Unit x) = 0 := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity T))
    (GrCooperad.counit (R := R) (C := FreeGr R gp) ∘ₗ barD μ gp R Unit) 0 (fun s => ?_) x
  · simpa using h
  show GrCooperad.counit (R := R) (C := FreeGr R gp)
      (barD μ gp R Unit (SgnLin.bas (treeSgn gp) R s)) = 0
  rw [barD_bas, map_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  rw [map_smul]
  have hw := Tree.weight_contr μ hk.1 hk.2
  have hne : contrR μ s k ≠ SetOperad.one := fun h => by
    have := congrArg (fun x => (treeOf x).weight) h
    simp only [treeOf_contrR] at this
    rw [this] at hw
    have h1 : (treeOf (SetOperad.one : Reg (TreeOfArity T) Unit)).weight = 0 := rfl
    omega
  show σ R _ • (Finsupp.single (contrR μ s k) (1 : R)) SetOperad.one = 0
  rw [Finsupp.single_eq_of_ne hne.symm, smul_zero]

/-- The bar differential of a trivial tree vanishes. -/
theorem barD_one : barD μ gp R Unit (GrCooperad.Coaug.one (R := R) (C := FreeGr R gp)) = 0 :=
  barD_bas_of_isLeaf (x := (SetOperad.one : Reg (TreeOfArity T) Unit)) rfl

omit [CommRing R] in
lemma weightF_leaves : ∀ k : ℕ, (TreeOfArity.leaves (E := T) k).weightF = 0
  | 0 => rfl
  | k + 1 => by
    simp only [TreeOfArity.leaves, Tree.weightF_cons, Tree.weight_leaf, weightF_leaves k]

/-- **The bar differential vanishes on the generators.** -/
theorem barD_gen {k : ℕ} (g : T k) :
    barD μ gp R (Fin k) (FreeGr.gen (R := R) (gp := gp) g) = 0 := by
  rw [FreeGr.gen, barD_bas]
  have h : (treeOf (Reg.std (corolla g) : Reg (TreeOfArity T) (Fin k))).weight = 1 := by
    show (Tree.node g (TreeOfArity.leaves k)).weight = 1
    rw [Tree.weight_node, weightF_leaves]
  rw [h, Finset.Ico_self, Finset.sum_empty]

end FreeGr

end Operad
