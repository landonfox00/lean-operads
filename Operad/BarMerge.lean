/-
# The laws of merge-composition

Merge-composition `x ⊛ᵢ y` on the free graded operad `FreeGr R gp` (`FreeGr.mcomp`) merges the
root of `y` into the vertex of `x` carrying the input `i`. It is the term by which the bar
differential fails to be a derivation (`FreeGr.barD_comp`), and it satisfies the laws of a
composition of degree one with the compositions of the free graded operad:

* **relabelling** (`FreeGr.mcomp_map`);
* **parallel**: `(x ∘ᵢ y) ⊛ₖ z = (-1)^{|y||z|} (x ⊛ₖ z) ∘ᵢ y` for `i ≠ k` (`FreeGr.mcomp_comp_par`);
* **inner**: `(x ∘ᵢ y) ⊛ⱼ z = (-1)^{|x|} x ∘ᵢ (y ⊛ⱼ z)` for `j` an input of `y`, when `y` is not
  the unit (`FreeGr.mcomp_comp_inner`);
* **outer**: `(x ⊛ᵢ y) ∘ⱼ z = x ⊛ᵢ (y ∘ⱼ z)`, when `y` has no unit component
  (`FreeGr.comp_mcomp_outer`);
* **corollas**: merge-grafting two corollas gives the corolla of the merged label
  (`FreeGr.corolla_mgraft`).

The coefficient of the unit tree (`FreeGr.unitCoeff`) is multiplicative, so the operations without
unit component form an ideal (`FreeGr.noUnitIdeal`).
-/
import Operad.BarDiff

universe u v

namespace Operad

open Sym GerBV TreeOfArity
open scoped TensorProduct

namespace Tree

variable {E : ℕ → Type v} (μ : MergeFn E) (gp : ∀ k, E k → Bool)

/-- **The sign of merge-grafting** `u` at the leaf `p` of `s`: the Koszul sign of grafting, and
the sign of contracting the new edge. -/
def mSgn (s : Tree E) (p : ℕ) (u : Tree E) : Bool :=
  xor (tpar gp u && apar gp s p) (mgSgn gp s p (rpar gp u))

/-- The sign of merging at a leaf before a graft point. -/
theorem mSgn_graft_after {s b u : Tree E} {p q : ℕ} (hpq : p < q) (hq : q < s.arity) :
    xor (tpar gp b && apar gp s q) (mSgn gp (s.graft q b) p u)
      = xor (tpar gp b && tpar gp u)
          (xor (mSgn gp s p u) (tpar gp b && apar gp (s.mgraft μ p u) (q - 1 + u.arity))) := by
  simp only [mSgn, mgSgn, apar_graft_before gp s q b p hpq hq, lpar_graft_after gp s q b p hpq hq,
    mpar_graft_after gp s q b p hpq hq, apar_mgraft_after μ gp s p u q hpq hq]
  cases tpar gp b <;> cases tpar gp u <;> cases apar gp s p <;> cases apar gp s q <;>
    cases lpar gp s p <;> cases rpar gp u <;> cases mpar gp s p <;> rfl

/-- The sign of merging at a leaf after a graft point. -/
theorem mSgn_graft_before (hμ : MergeFn.Odd gp μ) {s b u : Tree E} {p q : ℕ} (hqp : q < p)
    (hp : p < s.arity) (hu : u.isLeaf = false) :
    xor (tpar gp b && apar gp s q) (mSgn gp (s.graft q b) (p - 1 + b.arity) u)
      = xor (tpar gp b && tpar gp u)
          (xor (mSgn gp s p u) (tpar gp b && apar gp (s.mgraft μ p u) q)) := by
  have ha : apar gp (s.graft q b) (p - 1 + b.arity) = apar gp s p := by
    rw [show p - 1 + b.arity = p + b.arity - 1 by omega]
    exact apar_graft_after gp s q b p hqp hp
  simp only [mSgn, mgSgn, ha, lpar_graft_before gp s q b p hqp hp,
    mpar_graft_before gp s q b p hqp hp, apar_mgraft_before μ gp hμ s q p u hqp hp hu]
  cases tpar gp b <;> cases tpar gp u <;> cases apar gp s p <;> cases apar gp s q <;>
    cases lpar gp s p <;> cases rpar gp u <;> cases mpar gp s p <;> cases qbp s q p <;> rfl

/-- The sign of merging into a grafted tree. -/
theorem mSgn_graft_inner (hμ : MergeFn.Odd gp μ) {s b u : Tree E} {q r : ℕ} (hq : q < s.arity)
    (hr : r < b.arity) (hb : b.isLeaf = false) (hu : u.isLeaf = false) :
    xor (tpar gp b && apar gp s q) (mSgn gp (s.graft q b) (q + r) u)
      = xor (tpar gp s) (xor (mSgn gp b r u) (tpar gp (b.mgraft μ r u) && apar gp s q)) := by
  simp only [mSgn, mgSgn, apar_graft_inner gp s q b r hq hr, lpar_graft_inner gp s q b r hq hr hb,
    mpar_graft_inner gp s q b r hq hr hb, tpar_mgraft μ gp hμ b r u hr hb hu]
  cases tpar gp b <;> cases tpar gp u <;> cases tpar gp s <;> cases apar gp s q <;>
    cases apar gp b r <;> cases lpar gp b r <;> cases rpar gp u <;> cases mpar gp b r <;> rfl

/-- The sign of grafting into a merge-grafted tree, at a leaf of the merged tree. -/
theorem mSgn_graft_outer {s b u : Tree E} {p q : ℕ} (hp : p < s.arity) (hq : q < b.arity)
    (hb : b.isLeaf = false) :
    xor (mSgn gp s p b) (tpar gp u && apar gp (s.mgraft μ p b) (p + q))
      = xor (tpar gp u && apar gp b q) (mSgn gp s p (b.graft q u)) := by
  simp only [mSgn, mgSgn, apar_mgraft_inner μ gp s p b q hp hq hb, tpar_graft gp b q u hq,
    rpar_graft gp hb]
  cases tpar gp b <;> cases tpar gp u <;> cases apar gp s p <;> cases apar gp b q <;>
    cases lpar gp s p <;> cases rpar gp b <;> cases mpar gp s p <;> rfl

end Tree

namespace FreeGr

variable {T : ℕ → Type v} (μ : MergeFn T)
variable {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype D] [DecidableEq D]

/-! ## The laws on labelled trees -/

@[simp] lemma treeOf_map (e : A ≃ B) (x : Reg (TreeOfArity T) A) :
    treeOf (SetOperad.map e x) = treeOf x := rfl

@[simp] lemma map_fst (e : A ≃ B) (x : Reg (TreeOfArity T) A) :
    (SetOperad.map e x).1 = LinOrd.map e x.1 := rfl

/-- **Merge-composition commutes with relabelling.** -/
lemma mcompR_map {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (σ' : A ≃ A') (τ : B ≃ B') (i : A) (x : Reg (TreeOfArity T) A)
    (y : Reg (TreeOfArity T) B) :
    SetOperad.map (compEquiv σ' τ i) (mcompR μ i x y)
      = mcompR μ (σ' i) (SetOperad.map σ' x) (SetOperad.map τ y) := by
  refine reg_ext ?_ ?_
  · show (SetOperad.map (compEquiv σ' τ i) (SetOperad.comp i x y)).1
      = (SetOperad.comp (σ' i) (SetOperad.map σ' x) (SetOperad.map τ y)).1
    rw [SetOperad.map_comp]
  · simp only [treeOf_map, treeOf_mcompR, map_fst, LinOrd.rank_map, Equiv.symm_apply_apply]

/-- **Merging at an input other than the one composed at.** -/
lemma mcompR_comp_par {i k : A} (hik : i ≠ k) (x : Reg (TreeOfArity T) A)
    (y : Reg (TreeOfArity T) B) (z : Reg (TreeOfArity T) D) :
    SetOperad.map (parEquiv hik B D)
        (mcompR μ (Sum.inl ⟨k, Ne.symm hik⟩) (SetOperad.comp i x y) z)
      = SetOperad.comp (Sum.inl ⟨i, hik⟩) (mcompR μ k x z) y := by
  refine reg_ext ?_ ?_
  · exact SetOperad.comp_assoc_par (S := fun A _ _ => LinOrd A) hik x.1 y.1 z.1
  · simp only [treeOf_map, treeOf_mcompR, treeOf_comp, mcompR_fst, comp_fst]
    have hy : Fintype.card B = (treeOf y).arity := by rw [treeOf_arity]; exact y.2.2.symm
    have hz : Fintype.card D = (treeOf z).arity := by rw [treeOf_arity]; exact z.2.2.symm
    rcases x.1.total i k hik with h | h
    · rw [LinOrd.rank_comp_inl_of_gt _ _ _ _ h, LinOrd.rank_comp_inl_of_lt _ _ _ _ h, hy]
      exact Tree.graft_mgraft_before μ _ _ _ _ _ (x.1.rank_lt_rank h) (rank_lt_arity x k)
    · rw [LinOrd.rank_comp_inl_of_lt _ _ _ _ h, LinOrd.rank_comp_inl_of_gt _ _ _ _ h, hz]
      exact Tree.graft_mgraft_after μ _ _ _ _ _ (x.1.rank_lt_rank h) (rank_lt_arity x i)

/-- **Merging into the inner factor of a composite.** -/
lemma mcompR_comp_inner (i : A) (j : B) (x : Reg (TreeOfArity T) A)
    (y : Reg (TreeOfArity T) B) (z : Reg (TreeOfArity T) D) (hy : (treeOf y).isLeaf = false) :
    SetOperad.map (seqEquiv i j D) (mcompR μ (Sum.inr j) (SetOperad.comp i x y) z)
      = SetOperad.comp i x (mcompR μ j y z) := by
  refine reg_ext ?_ ?_
  · exact SetOperad.comp_assoc_seq (S := fun A _ _ => LinOrd A) i j x.1 y.1 z.1
  · simp only [treeOf_map, treeOf_mcompR, treeOf_comp, comp_fst, LinOrd.rank_comp_inr]
    exact Tree.mgraft_graft_inner μ _ _ _ _ _ (rank_lt_arity x i) (rank_lt_arity y j) hy

/-- **Composing into a merge-composite at an input of its inner factor.** -/
lemma comp_mcompR_outer (i : A) (j : B) (x : Reg (TreeOfArity T) A)
    (y : Reg (TreeOfArity T) B) (z : Reg (TreeOfArity T) D) (hy : (treeOf y).isLeaf = false) :
    SetOperad.map (seqEquiv i j D) (SetOperad.comp (Sum.inr j) (mcompR μ i x y) z)
      = mcompR μ i x (SetOperad.comp j y z) := by
  refine reg_ext ?_ ?_
  · exact SetOperad.comp_assoc_seq (S := fun A _ _ => LinOrd A) i j x.1 y.1 z.1
  · simp only [treeOf_map, treeOf_mcompR, treeOf_comp, mcompR_fst, comp_fst,
      LinOrd.rank_comp_inr]
    exact (Tree.mgraft_graft_outer μ _ _ _ _ _ (rank_lt_arity x i) (rank_lt_arity y j) hy).symm

/-! ## The laws on the free graded operad -/

section Laws

variable (gp : ∀ k, T k → Bool) {R : Type u} [CommRing R]

lemma mcompSgn_eq (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    mcompSgn gp i x y = Tree.mSgn gp (treeOf x) (x.1.rank i) (treeOf y) := rfl

lemma mcompSgn_map {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (σ' : A ≃ A') (τ : B ≃ B') (i : A) (x : Reg (TreeOfArity T) A)
    (y : Reg (TreeOfArity T) B) :
    mcompSgn gp (σ' i) (SetOperad.map σ' x) (SetOperad.map τ y) = mcompSgn gp i x y := by
  simp only [mcompSgn, treeOf_map, map_fst, LinOrd.rank_map, Equiv.symm_apply_apply]

variable {gp}

lemma mcomp_bas_of {i : A} {x : Reg (TreeOfArity T) A} {y : Reg (TreeOfArity T) B}
    (hx : (treeOf x).isLeaf = false) (hy : (treeOf y).isLeaf = false) :
    mcomp μ gp R i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y)
      = σ R (mcompSgn gp i x y) • SgnLin.bas (treeSgn gp) R (mcompR μ i x y) := by
  rw [mcomp_bas, if_pos ⟨hx, hy⟩]

lemma mcomp_bas_of_left {i : A} {x : Reg (TreeOfArity T) A} (y : Reg (TreeOfArity T) B)
    (hx : (treeOf x).isLeaf = true) :
    mcomp μ gp R i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y) = 0 := by
  rw [mcomp_bas, if_neg (fun h => by rw [h.1] at hx; exact Bool.false_ne_true hx)]

lemma mcomp_bas_of_right {i : A} (x : Reg (TreeOfArity T) A) {y : Reg (TreeOfArity T) B}
    (hy : (treeOf y).isLeaf = true) :
    mcomp μ gp R i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y) = 0 := by
  rw [mcomp_bas, if_neg (fun h => by rw [h.2] at hy; exact Bool.false_ne_true hy)]

/-- An operation with two distinct inputs is not the unit. -/
lemma isLeaf_of_ne {i k : A} (hik : i ≠ k) (x : Reg (TreeOfArity T) A) :
    (treeOf x).isLeaf = false := by
  by_contra h
  have hl : (treeOf x).isLeaf = true := by simpa using h
  have h1 := treeOf_arity x
  rw [Tree.eq_leaf_of_isLeaf hl, Tree.arity_leaf, x.2.2] at h1
  exact hik (Fintype.card_le_one_iff.1 h1.symm.le i k)

/-- **Merge-composition commutes with relabelling.** -/
theorem mcomp_map {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (σ' : A ≃ A') (τ : B ≃ B') (i : A) (x : FreeGr R gp A) (y : FreeGr R gp B) :
    mcomp μ gp R (σ' i) (GrOperad.map (R := R) σ' x) (GrOperad.map (R := R) τ y)
      = GrOperad.map (R := R) (compEquiv σ' τ i) (mcomp μ gp R i x y) := by
  have h : (mcomp μ gp R (σ' i)).compl₁₂ (GrOperad.map (R := R) (P := FreeGr R gp) σ')
        (GrOperad.map (R := R) (P := FreeGr R gp) τ)
      = (mcomp μ gp R i).compr₂ (GrOperad.map (R := R) (P := FreeGr R gp) (compEquiv σ' τ i)) := by
    refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring
      (Finsupp.lhom_ext' fun t => LinearMap.ext_ring ?_)
    show mcomp μ gp R (σ' i) (GrOperad.map (R := R) σ' (SgnLin.bas (treeSgn gp) R s))
        (GrOperad.map (R := R) τ (SgnLin.bas (treeSgn gp) R t))
      = GrOperad.map (R := R) (compEquiv σ' τ i)
          (mcomp μ gp R i (SgnLin.bas (treeSgn gp) R s) (SgnLin.bas (treeSgn gp) R t))
    rw [SgnLin.map_bas, SgnLin.map_bas, mcomp_bas, mcomp_bas]
    simp only [treeOf_map]
    split_ifs
    · rw [map_smul, SgnLin.map_bas, mcompR_map, mcompSgn_map]
    · rw [map_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

/-- **Merging at an input other than the one composed at**, on basis elements:
`(x ∘ᵢ y) ⊛ₖ z = (-1)^{|y||z|} (x ⊛ₖ z) ∘ᵢ y`. -/
theorem mcomp_comp_par_bas (hμ : MergeFn.Odd gp μ) {i k : A} (hik : i ≠ k)
    (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) (z : Reg (TreeOfArity T) D) :
    GrOperad.map (R := R) (parEquiv hik B D)
        (mcomp μ gp R (Sum.inl ⟨k, Ne.symm hik⟩)
          (GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y))
          (SgnLin.bas (treeSgn gp) R z))
      = σ R (Tree.tpar gp (treeOf y) && Tree.tpar gp (treeOf z)) •
          GrOperad.comp (R := R) (Sum.inl ⟨i, hik⟩)
            (mcomp μ gp R k (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R z))
            (SgnLin.bas (treeSgn gp) R y) := by
  have hx := isLeaf_of_ne hik x
  rw [comp_bas_eq, map_smul, LinearMap.smul_apply]
  by_cases hz : (treeOf z).isLeaf = false
  · have hxy : (treeOf (SetOperad.comp i x y)).isLeaf = false := by
      rw [treeOf_comp]
      exact Tree.isLeaf_graft_left hx _ _
    rw [mcomp_bas_of μ hxy hz, mcomp_bas_of μ hx hz, map_smul, map_smul, SgnLin.map_bas,
      mcompR_comp_par, map_smul, LinearMap.smul_apply, comp_bas_eq, smul_smul, smul_smul,
      smul_smul]
    congr 1
    simp only [mcompSgn_eq, ← σ_xor]
    congr 1
    simp only [treeOf_comp, comp_fst, treeOf_mcompR, mcompR_fst]
    have hy : Fintype.card B = (treeOf y).arity := by rw [treeOf_arity]; exact y.2.2.symm
    have hz' : Fintype.card D = (treeOf z).arity := by rw [treeOf_arity]; exact z.2.2.symm
    rcases x.1.total i k hik with h | h
    · rw [LinOrd.rank_comp_inl_of_gt _ _ _ _ h, LinOrd.rank_comp_inl_of_lt _ _ _ _ h, hy,
        Bool.xor_assoc (Tree.tpar gp (treeOf y) && Tree.tpar gp (treeOf z))]
      exact Tree.mSgn_graft_before μ gp hμ (x.1.rank_lt_rank h) (rank_lt_arity x k) hz
    · rw [LinOrd.rank_comp_inl_of_lt _ _ _ _ h, LinOrd.rank_comp_inl_of_gt _ _ _ _ h, hz',
        Bool.xor_assoc (Tree.tpar gp (treeOf y) && Tree.tpar gp (treeOf z))]
      exact Tree.mSgn_graft_after μ gp (x.1.rank_lt_rank h) (rank_lt_arity x i)
  · have hz : (treeOf z).isLeaf = true := by simpa using hz
    rw [mcomp_bas_of_right μ _ hz, mcomp_bas_of_right μ _ hz, smul_zero, map_zero,
      LinearMap.map_zero₂, smul_zero]

/-- **Merging into the inner factor of a composite**, on basis elements:
`(x ∘ᵢ y) ⊛ⱼ z = (-1)^{|x|} x ∘ᵢ (y ⊛ⱼ z)`. -/
theorem mcomp_comp_inner_bas (hμ : MergeFn.Odd gp μ) (i : A) (j : B)
    (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) (z : Reg (TreeOfArity T) D)
    (hy : (treeOf y).isLeaf = false) :
    GrOperad.map (R := R) (seqEquiv i j D)
        (mcomp μ gp R (Sum.inr j)
          (GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y))
          (SgnLin.bas (treeSgn gp) R z))
      = σ R (Tree.tpar gp (treeOf x)) •
          GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R x)
            (mcomp μ gp R j (SgnLin.bas (treeSgn gp) R y) (SgnLin.bas (treeSgn gp) R z)) := by
  rw [comp_bas_eq, map_smul, LinearMap.smul_apply]
  by_cases hz : (treeOf z).isLeaf = false
  · have hxy : (treeOf (SetOperad.comp i x y)).isLeaf = false := by
      rw [treeOf_comp]
      exact Tree.isLeaf_graft hy
    rw [mcomp_bas_of μ hxy hz, mcomp_bas_of μ hy hz, map_smul, map_smul, SgnLin.map_bas,
      mcompR_comp_inner μ i j x y z hy, map_smul, comp_bas_eq, smul_smul, smul_smul, smul_smul]
    congr 1
    simp only [mcompSgn_eq, ← σ_xor]
    congr 1
    simp only [treeOf_comp, comp_fst, treeOf_mcompR, LinOrd.rank_comp_inr]
    rw [Bool.xor_assoc (Tree.tpar gp (treeOf x))]
    exact Tree.mSgn_graft_inner μ gp hμ (rank_lt_arity x i) (rank_lt_arity y j) hy hz
  · have hz : (treeOf z).isLeaf = true := by simpa using hz
    rw [mcomp_bas_of_right μ _ hz, mcomp_bas_of_right μ _ hz, smul_zero, map_zero, map_zero,
      smul_zero]

/-- **Composing into a merge-composite at an input of its inner factor**, on basis elements:
`(x ⊛ᵢ y) ∘ⱼ z = x ⊛ᵢ (y ∘ⱼ z)`. -/
theorem comp_mcomp_outer_bas (i : A) (j : B) (x : Reg (TreeOfArity T) A)
    (y : Reg (TreeOfArity T) B) (z : Reg (TreeOfArity T) D) (hy : (treeOf y).isLeaf = false) :
    GrOperad.map (R := R) (seqEquiv i j D)
        (GrOperad.comp (R := R) (Sum.inr j)
          (mcomp μ gp R i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y))
          (SgnLin.bas (treeSgn gp) R z))
      = mcomp μ gp R i (SgnLin.bas (treeSgn gp) R x)
          (GrOperad.comp (R := R) j (SgnLin.bas (treeSgn gp) R y)
            (SgnLin.bas (treeSgn gp) R z)) := by
  rw [comp_bas_eq (i := j), map_smul]
  by_cases hx : (treeOf x).isLeaf = false
  · have hyz : (treeOf (SetOperad.comp j y z)).isLeaf = false := by
      rw [treeOf_comp]
      exact Tree.isLeaf_graft_left hy _ _
    rw [mcomp_bas_of μ hx hy, mcomp_bas_of μ hx hyz, map_smul, LinearMap.smul_apply,
      comp_bas_eq, map_smul, map_smul, SgnLin.map_bas, comp_mcompR_outer μ i j x y z hy,
      smul_smul, smul_smul]
    congr 1
    simp only [mcompSgn_eq, ← σ_xor]
    congr 1
    simp only [treeOf_comp, treeOf_mcompR, mcompR_fst, comp_fst, LinOrd.rank_comp_inr]
    exact Tree.mSgn_graft_outer μ gp (rank_lt_arity x i) (rank_lt_arity y j) hy
  · have hx : (treeOf x).isLeaf = true := by simpa using hx
    rw [mcomp_bas_of_left μ _ hx, mcomp_bas_of_left μ _ hx, LinearMap.map_zero₂, map_zero,
      smul_zero]

/-! ### The unit component -/

variable (gp R) in
/-- **The coefficient of the unit tree.** -/
noncomputable def unitCoeff (A : Type) [Fintype A] [DecidableEq A] : FreeGr R gp A →ₗ[R] R :=
  Finsupp.linearCombination R fun x : Reg (TreeOfArity T) A => if (treeOf x).isLeaf then 1 else 0

lemma unitCoeff_bas (x : Reg (TreeOfArity T) A) :
    unitCoeff gp R A (SgnLin.bas (treeSgn gp) R x) = if (treeOf x).isLeaf then 1 else 0 :=
  (Finsupp.linearCombination_single R _ _).trans (one_smul R _)

lemma bas_eq_single (x : Reg (TreeOfArity T) A) (c : R) :
    (Finsupp.single x c : FreeGr R gp A) = c • SgnLin.bas (treeSgn gp) R x :=
  (Finsupp.smul_single_one x c).symm

lemma par_bas_eq (b : Bool) (x : Reg (TreeOfArity T) A) :
    GrOperad.par (R := R) b (SgnLin.bas (treeSgn gp) R x)
      = if Tree.tpar gp (treeOf x) = b then SgnLin.bas (treeSgn gp) R x else 0 :=
  SgnLin.parT_single b x 1

lemma isLeaf_graft_iff {s : Tree T} {r : ℕ} (hr : r < s.arity) (t : Tree T) :
    (s.graft r t).isLeaf = (s.isLeaf && t.isLeaf) := by
  cases s with
  | leaf =>
    obtain rfl : r = 0 := by simpa using hr
    rfl
  | node e f => rfl

/-- **The unit coefficient is multiplicative.** -/
lemma unitCoeff_comp (i : A) (x : FreeGr R gp A) (y : FreeGr R gp B) :
    unitCoeff gp R _ (GrOperad.comp (R := R) i x y) = unitCoeff gp R A x * unitCoeff gp R B y := by
  have h : (GrOperad.comp (R := R) (P := FreeGr R gp) (B := B) i).compr₂ (unitCoeff gp R _)
      = (LinearMap.mul R R).compl₁₂ (unitCoeff gp R A) (unitCoeff gp R B) := by
    refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring
      (Finsupp.lhom_ext' fun t => LinearMap.ext_ring ?_)
    show unitCoeff gp R _ (GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R s)
        (SgnLin.bas (treeSgn gp) R t))
      = unitCoeff gp R A (SgnLin.bas (treeSgn gp) R s) * unitCoeff gp R B
          (SgnLin.bas (treeSgn gp) R t)
    rw [comp_bas_eq, map_smul, unitCoeff_bas, unitCoeff_bas, unitCoeff_bas, treeOf_comp,
      isLeaf_graft_iff (rank_lt_arity s i)]
    by_cases hs : (treeOf s).isLeaf = true <;> by_cases ht : (treeOf t).isLeaf = true
    · rw [Tree.eq_leaf_of_isLeaf ht]
      simp [hs]
    · simp [hs, ht]
    · simp [hs, ht]
    · simp [hs, ht]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

lemma unitCoeff_map {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (x : FreeGr R gp A) :
    unitCoeff gp R A' (GrOperad.map (R := R) e x) = unitCoeff gp R A x := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity T))
    (unitCoeff gp R A' ∘ₗ GrOperad.map (R := R) (P := FreeGr R gp) e) (unitCoeff gp R A)
    (fun s => ?_) x
  · simpa using h
  show unitCoeff gp R A' (GrOperad.map (R := R) e (SgnLin.bas (treeSgn gp) R s))
    = unitCoeff gp R A (SgnLin.bas (treeSgn gp) R s)
  rw [SgnLin.map_bas, unitCoeff_bas, unitCoeff_bas, treeOf_map]

lemma unitCoeff_par (b : Bool) (x : FreeGr R gp A) :
    unitCoeff gp R A (GrOperad.par (R := R) b x) = if b then 0 else unitCoeff gp R A x := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity T))
    (unitCoeff gp R A ∘ₗ GrOperad.par (R := R) (P := FreeGr R gp) b)
    (if b then 0 else unitCoeff gp R A) (fun s => ?_) x
  · exact h.trans (by split_ifs <;> rfl)
  show unitCoeff gp R A (GrOperad.par (R := R) b (SgnLin.bas (treeSgn gp) R s))
    = (if b then 0 else unitCoeff gp R A) (SgnLin.bas (treeSgn gp) R s)
  rw [par_bas_eq]
  by_cases hs : (treeOf s).isLeaf = true
  · have h0 : Tree.tpar gp (treeOf s) = false := by
      rw [Tree.eq_leaf_of_isLeaf hs]; rfl
    cases b <;> simp [h0, unitCoeff_bas, hs]
  · split_ifs <;> simp [unitCoeff_bas, hs]

variable (gp R) in
/-- **The operations without unit component form an ideal.** -/
noncomputable def noUnitIdeal : GrOperadIdeal R (FreeGr R gp) where
  sub A _ _ := LinearMap.ker (unitCoeff gp R A)
  par_mem b x hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [unitCoeff_par, hx, ite_self]
  map_mem e x hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [unitCoeff_map, hx]
  comp_mem_left i x y hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [unitCoeff_comp, hx, zero_mul]
  comp_mem_right i x y hy := by
    rw [LinearMap.mem_ker] at hy ⊢
    rw [unitCoeff_comp, hy, mul_zero]

/-- There is at most one unit tree with given inputs. -/
lemma eq_of_isLeaf {x y : Reg (TreeOfArity T) A} (hx : (treeOf x).isLeaf = true)
    (hy : (treeOf y).isLeaf = true) : x = y := by
  have h1 := treeOf_arity x
  rw [Tree.eq_leaf_of_isLeaf hx, Tree.arity_leaf, x.2.2] at h1
  haveI : Subsingleton A := Fintype.card_le_one_iff_subsingleton.1 h1.symm.le
  exact reg_ext (LinOrd.eq_of_subsingleton _ _)
    ((Tree.eq_leaf_of_isLeaf hx).trans (Tree.eq_leaf_of_isLeaf hy).symm)

/-- **An operation without unit component is a combination of trees with vertices.** -/
lemma eq_sum_nonleaf (y : Reg (TreeOfArity T) A →₀ R) (hy : unitCoeff gp R A y = 0) :
    (y : FreeGr R gp A) = ∑ t ∈ y.support.filter (fun t => (treeOf t).isLeaf = false),
      y t • SgnLin.bas (treeSgn gp) R t := by
  have hsum : (y : FreeGr R gp A) = ∑ t ∈ y.support, y t • SgnLin.bas (treeSgn gp) R t := by
    conv_lhs => rw [← Finsupp.sum_single y]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact (Finsupp.smul_single_one t (y t)).symm
  have hu : unitCoeff gp R A y = ∑ t ∈ y.support.filter (fun t => (treeOf t).isLeaf = true),
      y t := by
    conv_lhs => rw [hsum]
    rw [map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_smul, unitCoeff_bas, smul_eq_mul]
    split_ifs <;> simp
  rw [← Finset.sum_filter_add_sum_filter_not y.support (fun t => (treeOf t).isLeaf = true)] at hsum
  have h0 : ∑ t ∈ y.support.filter (fun t => (treeOf t).isLeaf = true),
      y t • SgnLin.bas (treeSgn gp) R t = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have hfil : y.support.filter (fun t => (treeOf t).isLeaf = true) = {t} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨ht, fun t' ht' => ?_⟩
      exact eq_of_isLeaf (Finset.mem_filter.1 ht').2 (Finset.mem_filter.1 ht).2
    rw [hfil, Finset.sum_singleton] at hu
    rw [← hu, hy, zero_smul]
  rw [h0, zero_add] at hsum
  conv_lhs => rw [hsum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext t
  simp

/-! ### General operations -/

/-- **Induction on the operations of the free graded operad**: combinations of trees. -/
theorem induction_bas {motive : FreeGr R gp A → Prop} (x : FreeGr R gp A) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (bas : ∀ (c : R) (s : Reg (TreeOfArity T) A), motive (c • SgnLin.bas (treeSgn gp) R s)) :
    motive x :=
  Finsupp.induction_linear (motive := motive) x zero add fun s c => by
    have h := bas c s
    rwa [← bas_eq_single] at h

lemma tw_bas (x : Reg (TreeOfArity T) A) :
    GrSpecies.tw (R := R) (V := FreeGr R gp) true (SgnLin.bas (treeSgn gp) R x)
      = σ R (Tree.tpar gp (treeOf x)) • SgnLin.bas (treeSgn gp) R x :=
  (GrSpecies.tw_hom true (SgnLin.par_bas x)).trans (by rw [Bool.true_and]; rfl)

/-- **Merging at an input other than the one composed at**:
`(x ∘ᵢ y) ⊛ₖ z = (-1)^{|y||z|} (x ⊛ₖ z) ∘ᵢ y` for homogeneous `y`, `z`. -/
theorem mcomp_comp_par (hμ : MergeFn.Odd gp μ) {i k : A} (hik : i ≠ k) (x : FreeGr R gp A)
    {q r : Bool} {y : FreeGr R gp B} {z : FreeGr R gp D} (hy : GrOperad.par (R := R) q y = y)
    (hz : GrOperad.par (R := R) r z = z) :
    GrOperad.map (R := R) (parEquiv hik B D)
        (mcomp μ gp R (Sum.inl ⟨k, Ne.symm hik⟩) (GrOperad.comp (R := R) i x y) z)
      = σ R (q && r) • GrOperad.comp (R := R) (Sum.inl ⟨i, hik⟩) (mcomp μ gp R k x z) y := by
  rw [← hy, ← hz]
  clear hy hz
  induction x using induction_bas with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', smul_add]
  | bas c s =>
    induction y using induction_bas with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy', smul_add]
    | bas c' t =>
      induction z using induction_bas with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz', smul_add]
      | bas c'' u =>
        simp only [map_smul, LinearMap.smul_apply, par_bas_eq]
        by_cases h1 : Tree.tpar gp (treeOf t) = q
        · by_cases h2 : Tree.tpar gp (treeOf u) = r
          · rw [if_pos h1, if_pos h2, mcomp_comp_par_bas μ hμ hik s t u, h1, h2]
            module
          · rw [if_neg h2]
            simp
        · rw [if_neg h1]
          simp

/-- **Merging into the inner factor of a composite**: `(x ∘ᵢ y) ⊛ⱼ z = (-1)^{|x|} x ∘ᵢ (y ⊛ⱼ z)`,
for `y` without unit component. -/
theorem mcomp_comp_inner (hμ : MergeFn.Odd gp μ) (i : A) (j : B) (x : FreeGr R gp A)
    (y : FreeGr R gp B) (z : FreeGr R gp D) (hy : unitCoeff gp R B y = 0) :
    GrOperad.map (R := R) (seqEquiv i j D)
        (mcomp μ gp R (Sum.inr j) (GrOperad.comp (R := R) i x y) z)
      = GrOperad.comp (R := R) i (GrSpecies.tw (R := R) (V := FreeGr R gp) true x)
          (mcomp μ gp R j y z) := by
  have key : ∀ t : Reg (TreeOfArity T) B, (treeOf t).isLeaf = false →
      GrOperad.map (R := R) (seqEquiv i j D) (mcomp μ gp R (Sum.inr j)
          (GrOperad.comp (R := R) i x (SgnLin.bas (treeSgn gp) R t)) z)
        = GrOperad.comp (R := R) i (GrSpecies.tw (R := R) (V := FreeGr R gp) true x)
          (mcomp μ gp R j (SgnLin.bas (treeSgn gp) R t) z) := by
    intro t ht
    induction x using induction_bas with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | bas c s =>
      induction z using induction_bas with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | bas c'' u =>
        simp only [map_smul, LinearMap.smul_apply, tw_bas]
        rw [mcomp_comp_inner_bas μ hμ i j s t u ht]
  rw [eq_sum_nonleaf (y : Reg (TreeOfArity T) B →₀ R) hy]
  simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [key t (Finset.mem_filter.1 ht).2]

/-- **Composing into a merge-composite at an input of its inner factor**:
`(x ⊛ᵢ y) ∘ⱼ z = x ⊛ᵢ (y ∘ⱼ z)`, for `y` without unit component. -/
theorem comp_mcomp_outer (i : A) (j : B) (x : FreeGr R gp A) (y : FreeGr R gp B)
    (z : FreeGr R gp D) (hy : unitCoeff gp R B y = 0) :
    GrOperad.map (R := R) (seqEquiv i j D)
        (GrOperad.comp (R := R) (Sum.inr j) (mcomp μ gp R i x y) z)
      = mcomp μ gp R i x (GrOperad.comp (R := R) j y z) := by
  have key : ∀ t : Reg (TreeOfArity T) B, (treeOf t).isLeaf = false →
      GrOperad.map (R := R) (seqEquiv i j D)
          (GrOperad.comp (R := R) (Sum.inr j) (mcomp μ gp R i x (SgnLin.bas (treeSgn gp) R t)) z)
        = mcomp μ gp R i x (GrOperad.comp (R := R) j (SgnLin.bas (treeSgn gp) R t) z) := by
    intro t ht
    induction x using induction_bas with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | bas c s =>
      induction z using induction_bas with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | bas c'' u =>
        simp only [map_smul, LinearMap.smul_apply]
        rw [comp_mcomp_outer_bas μ i j s t u ht]
  rw [eq_sum_nonleaf (y : Reg (TreeOfArity T) B →₀ R) hy]
  simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [key t (Finset.mem_filter.1 ht).2]

/-- **Merge-composition adds the parities, plus one.** -/
theorem par_mcomp (hμ : MergeFn.Odd gp μ) (c a b : Bool) (i : A) (x : FreeGr R gp A)
    (y : FreeGr R gp B) :
    GrOperad.par (R := R) c (mcomp μ gp R i (GrOperad.par (R := R) a x)
        (GrOperad.par (R := R) b y))
      = if c = !(xor a b) then mcomp μ gp R i (GrOperad.par (R := R) a x)
          (GrOperad.par (R := R) b y) else 0 := by
  induction x using induction_bas with
  | zero => simp
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx']
    split_ifs <;> simp
  | bas c₁ s =>
    induction y using induction_bas with
    | zero => simp
    | add y y' hy hy' =>
      simp only [map_add, hy, hy']
      split_ifs <;> simp
    | bas c₂ t =>
      simp only [map_smul, LinearMap.smul_apply, par_bas_eq]
      by_cases h1 : Tree.tpar gp (treeOf s) = a
      · by_cases h2 : Tree.tpar gp (treeOf t) = b
        · rw [if_pos h1, if_pos h2]
          by_cases hs : (treeOf s).isLeaf = false
          · by_cases ht : (treeOf t).isLeaf = false
            · rw [mcomp_bas_of μ hs ht]
              simp only [map_smul, par_bas_eq, treeOf_mcompR,
                Tree.tpar_mgraft μ gp hμ _ _ _ (rank_lt_arity s i) hs ht, h1, h2]
              split_ifs <;> simp_all
            · rw [mcomp_bas_of_right μ _ (by simpa using ht)]
              simp
          · rw [mcomp_bas_of_left μ _ (by simpa using hs)]
            simp
        · rw [if_neg h2]
          simp
      · rw [if_neg h1]
        simp

end Laws

/-! ## Merging corollas -/

lemma isDirect_leaves : ∀ {k : ℕ} (p : ℕ), p < k →
    (TreeOfArity.leaves (E := T) k).isDirect p = true
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, p, h => by
    rw [TreeOfArity.leaves, Forest.isDirect]
    split_ifs with hp
    · rfl
    · exact isDirect_leaves (p - Tree.arity (Tree.leaf : Tree T)) (by simp at hp ⊢; omega)

lemma childIdx_leaves : ∀ {k : ℕ} (p : ℕ), p < k →
    (TreeOfArity.leaves (E := T) k).childIdx p = p
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, p, h => by
    rw [TreeOfArity.leaves, Forest.childIdx]
    split_ifs with hp
    · simp at hp; omega
    · rw [childIdx_leaves (p - Tree.arity (Tree.leaf : Tree T)) (by simp at hp ⊢; omega)]
      simp at hp ⊢
      omega

lemma append_leaves (k : ℕ) : ∀ l : ℕ,
    Forest.append (TreeOfArity.leaves (E := T) l) (TreeOfArity.leaves k)
      = TreeOfArity.leaves (k + l)
  | 0 => rfl
  | l + 1 => by
    show Forest.cons Tree.leaf (Forest.append (TreeOfArity.leaves l) (TreeOfArity.leaves k)) = _
    rw [append_leaves k l]
    rfl

lemma splice_leaves : ∀ (k j l : ℕ),
    (TreeOfArity.leaves (E := T) k).splice j (TreeOfArity.leaves l)
      = TreeOfArity.leaves (Forest.spliceLen k j l)
  | 0, _, _ => rfl
  | k + 1, 0, l => append_leaves k l
  | k + 1, j + 1, l => by
    show Forest.cons Tree.leaf ((TreeOfArity.leaves k).splice j (TreeOfArity.leaves l)) = _
    rw [splice_leaves k j l]
    rfl

lemma spliceLen_eq : ∀ {k j : ℕ} (l : ℕ), j < k → Forest.spliceLen k j l + 1 = k + l
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, 0, l, _ => by simp [Forest.spliceLen]; omega
  | k + 1, j + 1, l, h => by
    have := spliceLen_eq (k := k) (j := j) l (by omega)
    simp only [Forest.spliceLen]
    omega

lemma aparF_leaves (gp : ∀ k, T k → Bool) : ∀ (k p : ℕ),
    Forest.aparF gp (TreeOfArity.leaves (E := T) k) p = false
  | 0, _ => rfl
  | k + 1, p => by
    rw [TreeOfArity.leaves, Forest.aparF]
    split_ifs
    · rw [Tree.tparF_leaves]
      rfl
    · exact aparF_leaves gp k _

/-- **Merge-grafting corollas** gives the corolla of the merged label. -/
lemma corolla_mgraft {k l : ℕ} (g : T k) (h : T l) {i : ℕ} (hi : i < k) :
    (Tree.node g (TreeOfArity.leaves k)).mgraft μ i (Tree.node h (TreeOfArity.leaves l))
      = Tree.node (μ k l g i h (Forest.spliceLen k i l))
          (TreeOfArity.leaves (Forest.spliceLen k i l)) := by
  rw [Tree.mgraft_node, if_pos (isDirect_leaves i hi)]
  show Tree.mergeRoot μ g _ _ h _ = _
  rw [Tree.mergeRoot, childIdx_leaves i hi, splice_leaves]

/-- **The sign of merge-grafting corollas** is trivial. -/
lemma mSgn_corolla (gp : ∀ k, T k → Bool) {k l : ℕ} (g : T k) (h : T l) {i : ℕ} (hi : i < k) :
    Tree.mSgn gp (Tree.node g (TreeOfArity.leaves k)) i (Tree.node h (TreeOfArity.leaves l))
      = false := by
  simp only [Tree.mSgn, Tree.mgSgn, Tree.apar, Tree.lpar_node, Tree.mpar_node,
    if_pos (isDirect_leaves (T := T) i hi), aparF_leaves, Tree.tparF_leaves, Bool.and_false,
    Bool.xor_false]

end FreeGr

end Operad
