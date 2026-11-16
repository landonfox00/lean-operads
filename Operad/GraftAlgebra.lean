/-
# The grafting pre-Lie algebra of rooted trees

On the free module on the rooted trees with vertices labelled by finite subsets of `A`, **the
grafting product** (`RootedTree.graftMul`) of two trees is the sum of the graftings of the second
at the vertices of the first, when their vertex sets are disjoint, and zero otherwise
(`RootedTree.graftProd`).

* **The associator of the grafting product** is the sum of the graftings of the second and third
  trees at two vertices of the first, when the three vertex sets are pairwise disjoint, and zero
  otherwise (`RootedTree.graft_assoc`); it is symmetric in the last two trees
  (`RootedTree.graft_assoc_symm`). So **the grafting product is right pre-Lie**
  (`RootedTree.graft_preLie`), and the free module is an algebra over the pre-Lie operad
  (`RootedTree.graftPreLie`, `RootedTree.graftAlg`).
* `EndOp.ofBilin` is the binary operation of a bilinear map.
-/
import Operad.RootedTree
import Operad.BinaryQuadratic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace Operad

open Sym

/-- **The binary operation of a bilinear map.** -/
def EndOp.ofBilin {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    (m : V →ₗ[R] V →ₗ[R] V) : EndOp R V (Fin 2) where
  toFun v := m (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i
    · simp
    · simp
  map_update_smul' v i c x := by
    fin_cases i
    · simp
    · simp

@[simp] lemma EndOp.ofBilin_apply {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V]
    [Module R V] (m : V →ₗ[R] V →ₗ[R] V) (x y : V) : EndOp.ofBilin m ![x, y] = m x y := rfl

namespace RootedTree

variable (R : Type*) [CommRing R] {A : Type*} [DecidableEq A]

/-- **The grafting product of two trees**: the sum of the graftings of `U` at the vertices of
`T`, when their vertex sets are disjoint, and zero otherwise. -/
noncomputable def graftProd (T U : RootedTree A) : RootedTree A →₀ R :=
  if Disjoint T.S U.S then ∑ v ∈ T.S, Finsupp.single (graft T U v) 1 else 0

/-- **The grafting product**, bilinear. -/
noncomputable def graftMul :
    (RootedTree A →₀ R) →ₗ[R] (RootedTree A →₀ R) →ₗ[R] (RootedTree A →₀ R) :=
  Finsupp.linearCombination R fun T => Finsupp.linearCombination R (graftProd R T)

variable {R}

lemma graftMul_single (T U : RootedTree A) :
    graftMul R (Finsupp.single T 1) (Finsupp.single U 1) = graftProd R T U := by
  simp [graftMul, Finsupp.linearCombination_single]

lemma graftMul_single_left (T : RootedTree A) (y : RootedTree A →₀ R) :
    graftMul R (Finsupp.single T 1) y = Finsupp.linearCombination R (graftProd R T) y := by
  simp [graftMul, Finsupp.linearCombination_single]

lemma graftMul_sum_left {ι : Type*} (s : Finset ι) (f : ι → RootedTree A) (y : RootedTree A →₀ R) :
    graftMul R (∑ i ∈ s, Finsupp.single (f i) (1 : R)) y
      = ∑ i ∈ s, graftMul R (Finsupp.single (f i) 1) y := by
  rw [map_sum, LinearMap.sum_apply]

/-- The value of the product on a grafted tree. -/
lemma graftProd_graft {T U W : RootedTree A} {v : A} (hTU : Disjoint T.S U.S) (hv : v ∈ T.S) :
    graftProd R (graft T U v) W
      = if Disjoint (T.S ∪ U.S) W.S then
          ∑ w ∈ T.S ∪ U.S, Finsupp.single (graft (graft T U v) W w) 1 else 0 := by
  unfold graftProd
  rw [graft_S hTU hv]

/-- **The associator of the grafting product on trees.** -/
theorem graft_assoc (T U W : RootedTree A) :
    graftMul R (graftMul R (Finsupp.single T 1) (Finsupp.single U 1)) (Finsupp.single W 1)
      - graftMul R (Finsupp.single T 1) (graftMul R (Finsupp.single U 1) (Finsupp.single W 1))
      = if Disjoint T.S U.S ∧ Disjoint T.S W.S ∧ Disjoint U.S W.S then
          ∑ v ∈ T.S, ∑ w ∈ T.S, Finsupp.single (graft (graft T U v) W w) 1 else 0 := by
  rw [graftMul_single, graftMul_single]
  by_cases hTU : Disjoint T.S U.S
  · by_cases hTW : Disjoint T.S W.S
    · by_cases hUW : Disjoint U.S W.S
      · rw [if_pos ⟨hTU, hTW, hUW⟩]
        have h1 : graftMul R (graftProd R T U) (Finsupp.single W 1)
            = ∑ v ∈ T.S, ∑ w ∈ T.S ∪ U.S, Finsupp.single (graft (graft T U v) W w) (1 : R) := by
          unfold graftProd
          rw [if_pos hTU, graftMul_sum_left]
          refine Finset.sum_congr rfl fun v hv => ?_
          rw [graftMul_single, graftProd_graft hTU hv,
            if_pos (Finset.disjoint_union_left.2 ⟨hTW, hUW⟩)]
        have h2 : graftMul R (Finsupp.single T 1) (graftProd R U W)
            = ∑ w ∈ U.S, ∑ v ∈ T.S, Finsupp.single (graft (graft T U v) W w) (1 : R) := by
          unfold graftProd
          rw [if_pos hUW, map_sum]
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [graftMul_single]
          unfold graftProd
          rw [graft_S hUW hw, if_pos (Finset.disjoint_union_right.2 ⟨hTU, hTW⟩)]
          refine Finset.sum_congr rfl fun v hv => ?_
          rw [graft_graft_assoc hTU hTW hUW hv hw]
        rw [h1, h2, Finset.sum_comm (s := U.S), ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_union hTU, add_sub_cancel_right]
      · have h1 : graftMul R (graftProd R T U) (Finsupp.single W 1) = 0 := by
          unfold graftProd
          rw [if_pos hTU, graftMul_sum_left]
          refine Finset.sum_eq_zero fun v hv => ?_
          rw [graftMul_single, graftProd_graft hTU hv, if_neg fun h => hUW
            (Finset.disjoint_of_subset_left Finset.subset_union_right h)]
        have h2 : graftProd R U W = 0 := by unfold graftProd; rw [if_neg hUW]
        rw [h1, h2, map_zero, sub_zero, if_neg fun h => hUW h.2.2]
    · have h1 : graftMul R (graftProd R T U) (Finsupp.single W 1) = 0 := by
        unfold graftProd
        rw [if_pos hTU, graftMul_sum_left]
        refine Finset.sum_eq_zero fun v hv => ?_
        rw [graftMul_single, graftProd_graft hTU hv, if_neg fun h => hTW
          (Finset.disjoint_of_subset_left Finset.subset_union_left h)]
      have h2 : graftMul R (Finsupp.single T 1) (graftProd R U W) = 0 := by
        unfold graftProd
        split_ifs with hUW
        · rw [map_sum]
          refine Finset.sum_eq_zero fun w hw => ?_
          rw [graftMul_single]
          unfold graftProd
          rw [graft_S hUW hw, if_neg fun h => hTW
            (Finset.disjoint_of_subset_right Finset.subset_union_right h)]
        · exact map_zero _
      rw [h1, h2, sub_zero, if_neg fun h => hTW h.2.1]
  · have h1 : graftProd R T U = 0 := by unfold graftProd; rw [if_neg hTU]
    have h2 : graftMul R (Finsupp.single T 1) (graftProd R U W) = 0 := by
      unfold graftProd
      split_ifs with hUW
      · rw [map_sum]
        refine Finset.sum_eq_zero fun w hw => ?_
        rw [graftMul_single]
        unfold graftProd
        rw [graft_S hUW hw, if_neg fun h => hTU
          (Finset.disjoint_of_subset_right Finset.subset_union_left h)]
      · exact map_zero _
    rw [h1, h2, map_zero, LinearMap.zero_apply, sub_zero, if_neg fun h => hTU h.1]

/-- The associator of the grafting product is symmetric on trees. -/
theorem graft_assoc_symm (T U W : RootedTree A) :
    graftMul R (graftMul R (Finsupp.single T 1) (Finsupp.single U 1)) (Finsupp.single W 1)
      - graftMul R (Finsupp.single T 1) (graftMul R (Finsupp.single U 1) (Finsupp.single W 1))
      = graftMul R (graftMul R (Finsupp.single T 1) (Finsupp.single W 1)) (Finsupp.single U 1)
      - graftMul R (Finsupp.single T 1) (graftMul R (Finsupp.single W 1) (Finsupp.single U 1))
    := by
  rw [graft_assoc, graft_assoc]
  by_cases h : Disjoint T.S U.S ∧ Disjoint T.S W.S ∧ Disjoint U.S W.S
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun v hv => ?_
    rw [graft_graft_comm h.1 h.2.1 h.2.2 hv hw]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩]

variable (R) in
/-- The defect of the pre-Lie identity. -/
noncomputable def preLieDefect (x y z : RootedTree A →₀ R) : RootedTree A →₀ R :=
  (graftMul R (graftMul R x y) z - graftMul R x (graftMul R y z))
    - (graftMul R (graftMul R x z) y - graftMul R x (graftMul R z y))

lemma preLieDefect_add₁ (x x' y z : RootedTree A →₀ R) :
    preLieDefect R (x + x') y z = preLieDefect R x y z + preLieDefect R x' y z := by
  simp only [preLieDefect, map_add, LinearMap.add_apply]
  abel

lemma preLieDefect_add₂ (x y y' z : RootedTree A →₀ R) :
    preLieDefect R x (y + y') z = preLieDefect R x y z + preLieDefect R x y' z := by
  simp only [preLieDefect, map_add, LinearMap.add_apply]
  abel

lemma preLieDefect_add₃ (x y z z' : RootedTree A →₀ R) :
    preLieDefect R x y (z + z') = preLieDefect R x y z + preLieDefect R x y z' := by
  simp only [preLieDefect, map_add, LinearMap.add_apply]
  abel

lemma preLieDefect_smul₁ (c : R) (x y z : RootedTree A →₀ R) :
    preLieDefect R (c • x) y z = c • preLieDefect R x y z := by
  simp only [preLieDefect, map_smul, LinearMap.smul_apply, smul_sub]

lemma preLieDefect_smul₂ (c : R) (x y z : RootedTree A →₀ R) :
    preLieDefect R x (c • y) z = c • preLieDefect R x y z := by
  simp only [preLieDefect, map_smul, LinearMap.smul_apply, smul_sub]

lemma preLieDefect_smul₃ (c : R) (x y z : RootedTree A →₀ R) :
    preLieDefect R x y (c • z) = c • preLieDefect R x y z := by
  simp only [preLieDefect, map_smul, LinearMap.smul_apply, smul_sub]

lemma preLieDefect_eq_zero (x y z : RootedTree A →₀ R) : preLieDefect R x y z = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp [preLieDefect]
  | add x x' hx hx' => rw [preLieDefect_add₁, hx, hx', add_zero]
  | single T a =>
    induction y using Finsupp.induction_linear with
    | zero => simp [preLieDefect]
    | add y y' hy hy' => rw [preLieDefect_add₂, hy, hy', add_zero]
    | single U b =>
      induction z using Finsupp.induction_linear with
      | zero => simp [preLieDefect]
      | add z z' hz hz' => rw [preLieDefect_add₃, hz, hz', add_zero]
      | single W c =>
        rw [← Finsupp.smul_single_one T a, ← Finsupp.smul_single_one U b,
          ← Finsupp.smul_single_one W c, preLieDefect_smul₁, preLieDefect_smul₂,
          preLieDefect_smul₃]
        unfold preLieDefect
        rw [graft_assoc_symm, sub_self, smul_zero, smul_zero, smul_zero]

/-- **The grafting product is right pre-Lie.** -/
theorem graft_preLie (x y z : RootedTree A →₀ R) :
    graftMul R (graftMul R x y) z - graftMul R x (graftMul R y z)
      = graftMul R (graftMul R x z) y - graftMul R x (graftMul R z y) :=
  sub_eq_zero.1 (preLieDefect_eq_zero x y z)

variable (R A) in
/-- **The grafting pre-Lie algebra of rooted trees.** -/
noncomputable def graftPreLie : PreLieAlg R (RootedTree A →₀ R) where
  mul := EndOp.ofBilin (graftMul R)
  preLie x y z := by
    simp only [EndOp.ofBilin_apply]
    exact graft_preLie x y z

variable (R A) in
/-- **The grafting algebra of rooted trees**, an algebra over the pre-Lie operad. -/
noncomputable def graftAlg : SymAlgebra R (PreLie R) (RootedTree A →₀ R) :=
  PreLie.algebraEquiv.symm (graftPreLie R A)

end RootedTree

end Operad
