/-
# The vertex derivation of the free graded operad

A map of generators `g` flipping their parities gives **the vertex derivation** `D` of the free
graded operad `FreeGr R gp`: the signed sum of the relabellings of the vertices of a tree, one at a
time, the sign that of the vertices before the relabelled one in the preorder (`FreeGr.vD`).

* **`D` is an odd derivation and a coderivation** (`FreeGr.vD_comp`, `FreeGr.par_vD`,
  `FreeGr.decomp_vD`): the vertices of a composite are those of its factors, and a factorization of
  a tree with a vertex relabelled is a factorization of the tree with the vertex relabelled in one
  factor, in exactly one way (`Tree.graft_eq_relabelAt`).
* **The anticommutator with the bar differential** `[d, D] = d D + D d` satisfies
  `[d, D] (x ∘ᵢ y) = [d, D] x ∘ᵢ y + x ∘ᵢ [d, D] y + Γᵢ (x, y)`, where `Γ` is the defect of `D` on
  merge-composites (`FreeGr.anti_comp`, `FreeGr.gam`). By the laws of merge-composition, `Γ` on two
  trees reduces to `Γ` on two corollas (`FreeGr.gam_comp_right`, `FreeGr.gam_comp_inner`,
  `FreeGr.gam_comp_par`), so **`[d, D]` lies in every ideal containing `Γ` on pairs of corollas**
  (`FreeGr.anti_mem`).
-/
import Operad.TreeVertex
import Operad.BarDescent

universe u v

namespace Operad

open Sym GerBV TreeOfArity
open scoped TensorProduct

/-- Splitting the vertices of a graft, numbered from zero: those of the outer tree, the outer
ones after the graft point shifted by the grafted tree, and those of the grafted tree. -/
lemma sum_range_graft {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n m v : ℕ} (hv : v ≤ n) :
    ∑ k ∈ Finset.range (n + m), f k
      = ∑ k ∈ Finset.range n, f (k + if v ≤ k then m else 0)
        + ∑ k ∈ Finset.range m, f (v + k) := by
  have h1 : n + m = v + (m + (n - v)) := by omega
  have h2 : n = v + (n - v) := by omega
  rw [h1, Finset.sum_range_add, Finset.sum_range_add]
  conv_rhs => rw [h2, Finset.sum_range_add]
  have e1 : ∑ k ∈ Finset.range v, f (k + if v ≤ k then m else 0) = ∑ k ∈ Finset.range v, f k :=
    Finset.sum_congr rfl fun k hk => by
      rw [Finset.mem_range] at hk
      rw [if_neg (by omega), Nat.add_zero]
  have e2 : ∑ k ∈ Finset.range (n - v), f (v + k + if v ≤ v + k then m else 0)
      = ∑ k ∈ Finset.range (n - v), f (v + (m + k)) :=
    Finset.sum_congr rfl fun k _ => by
      rw [if_pos (by omega)]
      congr 1
      omega
  rw [e1, e2]
  abel

namespace FreeGr

variable {T : ℕ → Type v} (g : ∀ k, T k → T k)
variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **Relabelling the vertex `k`** of a planar tree with its leaves labelled. -/
def relabelAtR (x : Reg (TreeOfArity T) A) (k : ℕ) : Reg (TreeOfArity T) A :=
  (x.1, ⟨⟨x.2.1.1, ⟨(treeOf x).relabelAt g k,
    (Tree.arity_relabelAt g _ k).trans (treeOf_arity x)⟩⟩, x.2.2⟩)

@[simp] lemma relabelAtR_fst (x : Reg (TreeOfArity T) A) (k : ℕ) : (relabelAtR g x k).1 = x.1 :=
  rfl

@[simp] lemma treeOf_relabelAtR (x : Reg (TreeOfArity T) A) (k : ℕ) :
    treeOf (relabelAtR g x k) = (treeOf x).relabelAt g k := rfl

lemma relabelAtR_comp_outer (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B)
    {k : ℕ} (hk : k < (treeOf x).weight) :
    relabelAtR g (SetOperad.comp i x y)
        (k + if (treeOf x).vb (x.1.rank i) ≤ k then (treeOf y).weight else 0)
      = SetOperad.comp i (relabelAtR g x k) y :=
  reg_ext rfl (by
    rw [treeOf_relabelAtR, treeOf_comp, treeOf_comp, treeOf_relabelAtR, relabelAtR_fst,
      Tree.relabelAt_graft_outer g _ _ _ _ (rank_lt_arity x i) hk])

lemma relabelAtR_comp_inner (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B)
    {k : ℕ} (hk : k < (treeOf y).weight) :
    relabelAtR g (SetOperad.comp i x y) ((treeOf x).vb (x.1.rank i) + k)
      = SetOperad.comp i x (relabelAtR g y k) :=
  reg_ext rfl (by
    rw [treeOf_relabelAtR, treeOf_comp, treeOf_comp, treeOf_relabelAtR,
      Tree.relabelAt_graft_inner g _ _ _ _ (rank_lt_arity x i) hk])

variable (gp : ∀ k, T k → Bool) (R : Type u) [CommRing R]

/-- **The vertex derivation**: the signed sum of the relabellings of the vertices of a tree, the
sign that of the vertices before the relabelled one. -/
noncomputable def vD (A : Type) [Fintype A] [DecidableEq A] : FreeGr R gp A →ₗ[R] FreeGr R gp A :=
  Finsupp.linearCombination R fun x : Reg (TreeOfArity T) A =>
    (∑ k ∈ Finset.range (treeOf x).weight,
      σ R (Tree.bpar gp (treeOf x) k) • SgnLin.bas (treeSgn gp) R (relabelAtR g x k) :
        FreeGr R gp A)

lemma vD_bas (x : Reg (TreeOfArity T) A) :
    vD g gp R A (SgnLin.bas (treeSgn gp) R x)
      = ∑ k ∈ Finset.range (treeOf x).weight,
          σ R (Tree.bpar gp (treeOf x) k) • SgnLin.bas (treeSgn gp) R (relabelAtR g x k) := by
  unfold vD
  exact (Finsupp.linearCombination_single R _ _).trans (one_smul R _)

variable {g gp R}

/-- **The vertex derivation is a derivation**, on basis elements. -/
theorem vD_comp_bas (hg : ∀ k e, gp k (g k e) = !gp k e) (i : A) (x : Reg (TreeOfArity T) A)
    (y : Reg (TreeOfArity T) B) :
    vD g gp R _ (GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R x)
        (SgnLin.bas (treeSgn gp) R y))
      = GrOperad.comp (R := R) i (vD g gp R A (SgnLin.bas (treeSgn gp) R x))
          (SgnLin.bas (treeSgn gp) R y)
        + σ R (Tree.tpar gp (treeOf x)) • GrOperad.comp (R := R) i
            (SgnLin.bas (treeSgn gp) R x) (vD g gp R B (SgnLin.bas (treeSgn gp) R y)) := by
  have hi := rank_lt_arity x i
  set p := x.1.rank i
  rw [comp_bas_eq, map_smul, vD_bas, treeOf_comp, Tree.weight_graft _ _ _ hi,
    sum_range_graft _ (Tree.vb_le_weight (treeOf x) p), smul_add, vD_bas, vD_bas,
    map_sum, LinearMap.sum_apply, map_sum, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [← treeOf_comp, relabelAtR_comp_outer g i x y hk, map_smul, LinearMap.smul_apply,
      comp_bas_eq, smul_smul, smul_smul, treeOf_comp,
      Tree.bpar_graft_outer gp _ _ _ _ hi hk, treeOf_relabelAtR, relabelAtR_fst,
      Tree.apar_relabelAt gp hg _ _ _ hi]
    simp only [hk, and_true]
    congr 1
    cases Tree.tpar gp (treeOf y) <;> cases Tree.apar gp (treeOf x) p <;>
      cases Tree.bpar gp (treeOf x) k <;> cases decide ((treeOf x).vb p ≤ k) <;> simp [σ]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [← treeOf_comp, relabelAtR_comp_inner g i x y hk, map_smul, comp_bas_eq, smul_smul,
      smul_smul, smul_smul, treeOf_comp, Tree.bpar_graft_inner gp _ _ _ _ hi hk,
      treeOf_relabelAtR, Tree.tpar_relabelAt gp hg, decide_eq_true hk]
    congr 1
    have hb := Tree.bpar_vb_xor_apar gp (treeOf x) p hi
    rw [← hb]
    cases Tree.tpar gp (treeOf y) <;> cases Tree.apar gp (treeOf x) p <;>
      cases Tree.bpar gp (treeOf x) ((treeOf x).vb p) <;> cases Tree.bpar gp (treeOf y) k <;>
      simp [σ]

/-- **The vertex derivation is a derivation**: `D (x ∘ᵢ y) = D x ∘ᵢ y + (-1)^|x| x ∘ᵢ D y`. -/
theorem vD_comp (hg : ∀ k e, gp k (g k e) = !gp k e) (i : A) (x : FreeGr R gp A)
    (y : FreeGr R gp B) :
    vD g gp R _ (GrOperad.comp (R := R) i x y)
      = GrOperad.comp (R := R) i (vD g gp R A x) y
        + GrOperad.comp (R := R) i (GrSpecies.tw (R := R) (V := FreeGr R gp) true x)
            (vD g gp R B y) := by
  have h : (GrOperad.comp (R := R) (P := FreeGr R gp) (B := B) i).compr₂ (vD g gp R _)
      = (GrOperad.comp (R := R) (P := FreeGr R gp) (B := B) i).comp (vD g gp R A)
        + ((GrOperad.comp (R := R) (P := FreeGr R gp) (B := B) i).comp
            (GrSpecies.tw (R := R) (V := FreeGr R gp) true)).compl₂ (vD g gp R B) := by
    refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring
      (Finsupp.lhom_ext' fun t => LinearMap.ext_ring ?_)
    have e := vD_comp_bas (R := R) hg i s t
    show vD g gp R _ (GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R s)
        (SgnLin.bas (treeSgn gp) R t))
      = GrOperad.comp (R := R) i (vD g gp R A (SgnLin.bas (treeSgn gp) R s))
          (SgnLin.bas (treeSgn gp) R t)
        + GrOperad.comp (R := R) i (GrSpecies.tw (R := R) (V := FreeGr R gp) true
            (SgnLin.bas (treeSgn gp) R s)) (vD g gp R B (SgnLin.bas (treeSgn gp) R t))
    rw [tw_bas, map_smul, LinearMap.smul_apply]
    exact e
  have := LinearMap.congr_fun (LinearMap.congr_fun h x) y
  simpa using this

/-- **The vertex derivation is odd.** -/
theorem par_vD (hg : ∀ k e, gp k (g k e) = !gp k e) (b : Bool) (x : FreeGr R gp A) :
    GrOperad.par (R := R) b (vD g gp R A x) = vD g gp R A (GrOperad.par (R := R) (!b) x) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity T)) (GrOperad.par (R := R) b ∘ₗ vD g gp R A)
    (vD g gp R A ∘ₗ GrOperad.par (R := R) (P := FreeGr R gp) (A := A) (!b)) (fun s => ?_) x
  · simpa using h
  show GrOperad.par (R := R) b (vD g gp R A (SgnLin.bas (treeSgn gp) R s))
    = vD g gp R A (GrOperad.par (R := R) (!b) (SgnLin.bas (treeSgn gp) R s))
  have hp : ∀ (c : Bool) (t : Reg (TreeOfArity T) A),
      GrOperad.par (R := R) c (SgnLin.bas (treeSgn gp) R t)
        = if Tree.tpar gp (treeOf t) = c then SgnLin.bas (treeSgn gp) R t else 0 :=
    fun c t => SgnLin.parT_single c t 1
  rw [hp, vD_bas, map_sum]
  simp only [map_smul, hp, treeOf_relabelAtR]
  by_cases hs : Tree.tpar gp (treeOf s) = !b
  · rw [if_pos hs, vD_bas]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [if_pos (by rw [Tree.tpar_relabelAt gp hg, hs, decide_eq_true hk]; cases b <;> rfl)]
  · rw [if_neg hs, map_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [if_neg (fun h => hs (by
      rw [Tree.tpar_relabelAt gp hg, decide_eq_true hk] at h
      rw [← h]
      cases Tree.tpar gp (treeOf s) <;> rfl)), smul_zero]

/-- **The vertex derivation commutes with relabellings.** -/
theorem map_vD {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (x : FreeGr R gp A) :
    GrOperad.map (R := R) e (vD g gp R A x) = vD g gp R A' (GrOperad.map (R := R) e x) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity T)) (GrOperad.map (R := R) e ∘ₗ vD g gp R A)
    (vD g gp R A' ∘ₗ GrOperad.map (R := R) (P := FreeGr R gp) e) (fun s => ?_) x
  · simpa using h
  show GrOperad.map (R := R) e (vD g gp R A (SgnLin.bas (treeSgn gp) R s))
    = vD g gp R A' (GrOperad.map (R := R) e (SgnLin.bas (treeSgn gp) R s))
  rw [SgnLin.map_bas, vD_bas, vD_bas, map_sum]
  simp only [map_smul, SgnLin.map_bas]
  rfl

/-- **The vertex derivation kills the counit.** -/
theorem counit_vD (x : FreeGr R gp Unit) :
    GrCooperad.counit (R := R) (C := FreeGr R gp) (vD g gp R Unit x) = 0 := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity T))
    (GrCooperad.counit (R := R) (C := FreeGr R gp) ∘ₗ vD g gp R Unit) 0 (fun s => ?_) x
  · simpa using h
  show GrCooperad.counit (R := R) (C := FreeGr R gp)
      (vD g gp R Unit (SgnLin.bas (treeSgn gp) R s)) = 0
  rw [vD_bas, map_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [map_smul]
  have hne : relabelAtR g s k ≠ SetOperad.one := fun h => by
    have := congrArg (fun x => (treeOf x).weight) h
    simp only [treeOf_relabelAtR, Tree.weight_relabelAt] at this
    have h1 : (treeOf (SetOperad.one : Reg (TreeOfArity T) Unit)).weight = 0 := rfl
    omega
  show σ R _ • (Finsupp.single (relabelAtR g s k) (1 : R)) SetOperad.one = 0
  rw [Finsupp.single_eq_of_ne hne.symm, smul_zero]

/-- The vertex derivation of a tree without vertices vanishes. -/
theorem vD_bas_of_weight {x : Reg (TreeOfArity T) A} (hx : (treeOf x).weight = 0) :
    vD g gp R A (SgnLin.bas (treeSgn gp) R x) = 0 := by
  rw [vD_bas, hx, Finset.range_zero, Finset.sum_empty]

/-- **The vertex derivation relabels the generators.** -/
theorem vD_gen {k : ℕ} (e : T k) :
    vD g gp R (Fin k) (FreeGr.gen (R := R) (gp := gp) e) = FreeGr.gen (g k e) := by
  rw [FreeGr.gen, vD_bas]
  have h : (treeOf (Reg.std (corolla e) : Reg (TreeOfArity T) (Fin k))).weight = 1 := by
    show (Tree.node e (TreeOfArity.leaves k)).weight = 1
    rw [Tree.weight_node, weightF_leaves]
  rw [h, Finset.sum_range_one]
  show σ R (Tree.bpar gp (Tree.node e (TreeOfArity.leaves k)) 0) • _ = _
  rw [Tree.bpar_node_zero, σ_false, one_smul]
  rfl

/-! ## The vertex derivation is a coderivation -/

variable (gp R) in
/-- The terms of the decomposition of the vertex derivation of a basis element, indexed by a
vertex and a factorization of the relabelled tree. -/
noncomputable def vdTermL (i : A) (s : Reg (TreeOfArity T) (Without A i ⊕ B))
    (x : (_ : ℕ) × (Reg (TreeOfArity T) A × Reg (TreeOfArity T) B)) :
    FreeGr R gp A ⊗[R] FreeGr R gp B :=
  (σ R (Tree.bpar gp (treeOf s) x.1) * σ R (cSgn gp i x.2.1 x.2.2)) •
    (SgnLin.bas (treeSgn gp) R x.2.1 ⊗ₜ[R] SgnLin.bas (treeSgn gp) R x.2.2)

variable (g gp R) in
/-- The terms of the vertex derivation of the outer factors of the decomposition. -/
noncomputable def vdTermO (i : A)
    (y : (_ : Reg (TreeOfArity T) A × Reg (TreeOfArity T) B) × ℕ) :
    FreeGr R gp A ⊗[R] FreeGr R gp B :=
  (σ R (cSgn gp i y.1.1 y.1.2) * σ R (Tree.bpar gp (treeOf y.1.1) y.2)) •
    (SgnLin.bas (treeSgn gp) R (relabelAtR g y.1.1 y.2) ⊗ₜ[R] SgnLin.bas (treeSgn gp) R y.1.2)

variable (g gp R) in
/-- The terms of the vertex derivation of the inner factors of the decomposition. -/
noncomputable def vdTermI (i : A)
    (y : (_ : Reg (TreeOfArity T) A × Reg (TreeOfArity T) B) × ℕ) :
    FreeGr R gp A ⊗[R] FreeGr R gp B :=
  (σ R (cSgn gp i y.1.1 y.1.2) *
      (σ R (Tree.tpar gp (treeOf y.1.1)) * σ R (Tree.bpar gp (treeOf y.1.2) y.2))) •
    (SgnLin.bas (treeSgn gp) R y.1.1 ⊗ₜ[R] SgnLin.bas (treeSgn gp) R (relabelAtR g y.1.2 y.2))

lemma decomp_vD_bas_eq (i : A) (s : Reg (TreeOfArity T) (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := FreeGr R gp) i (vD g gp R _ (SgnLin.bas (treeSgn gp) R s))
      = ∑ x ∈ (Finset.range (treeOf s).weight).sigma
          (fun k => (SetOperad.FiniteFact.finite i (relabelAtR g s k)).toFinset),
          vdTermL gp R i s x := by
  rw [vD_bas, map_sum, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, decomp_bas, Finset.smul_sum]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [smul_smul]
  rfl

lemma map_vD_id_decomp_bas (i : A) (s : Reg (TreeOfArity T) (Without A i ⊕ B)) :
    TensorProduct.map (vD g gp R A) LinearMap.id
        (GrCooperad.decomp (R := R) (C := FreeGr R gp) i (SgnLin.bas (treeSgn gp) R s))
      = ∑ y ∈ (SetOperad.FiniteFact.finite i s).toFinset.sigma
          (fun pq => Finset.range (treeOf pq.1).weight), vdTermO g gp R i y := by
  rw [decomp_bas, map_sum, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [map_smul, TensorProduct.map_tmul, LinearMap.id_apply, vD_bas, TensorProduct.sum_tmul,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.smul_tmul', smul_smul]
  rfl

lemma map_tw_vD_decomp_bas (i : A) (s : Reg (TreeOfArity T) (Without A i ⊕ B)) :
    TensorProduct.map (GrSpecies.tw (R := R) (V := FreeGr R gp) true) (vD g gp R B)
        (GrCooperad.decomp (R := R) (C := FreeGr R gp) i (SgnLin.bas (treeSgn gp) R s))
      = ∑ y ∈ (SetOperad.FiniteFact.finite i s).toFinset.sigma
          (fun pq => Finset.range (treeOf pq.2).weight), vdTermI g gp R i y := by
  rw [decomp_bas, map_sum, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [map_smul, TensorProduct.map_tmul, tw_bas, vD_bas, TensorProduct.tmul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [vdTermI, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  congr 1
  ring_nf

variable (g) in
/-- The vertex of a composite, and the factorization of the relabelled tree, given by a vertex of a
factor of a factorization. -/
noncomputable def liftV (i : A) :
    ((_ : Reg (TreeOfArity T) A × Reg (TreeOfArity T) B) × ℕ) ⊕
        ((_ : Reg (TreeOfArity T) A × Reg (TreeOfArity T) B) × ℕ) →
      (_ : ℕ) × (Reg (TreeOfArity T) A × Reg (TreeOfArity T) B) :=
  Sum.elim
    (fun y => ⟨y.2 + if (treeOf y.1.1).vb (y.1.1.1.rank i) ≤ y.2 then (treeOf y.1.2).weight
      else 0, (relabelAtR g y.1.1 y.2, y.1.2)⟩)
    (fun y => ⟨(treeOf y.1.1).vb (y.1.1.1.rank i) + y.2, (y.1.1, relabelAtR g y.1.2 y.2)⟩)

/-- **The vertex derivation is a coderivation**, on basis elements:
`Δᵢ (D x) = (D ⊗ 1) (Δᵢ x) + ((-1)^• ⊗ D) (Δᵢ x)`. A factorization of a tree with a vertex
relabelled is a factorization of the tree with the vertex relabelled in one of its factors, in
exactly one way. -/
theorem decomp_vD_bas (hg : ∀ k e, gp k (g k e) = !gp k e) (i : A)
    (s : Reg (TreeOfArity T) (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := FreeGr R gp) i
        (vD g gp R _ (SgnLin.bas (treeSgn gp) R s))
      = TensorProduct.map (vD g gp R A) LinearMap.id
          (GrCooperad.decomp (R := R) (C := FreeGr R gp) i (SgnLin.bas (treeSgn gp) R s))
        + TensorProduct.map (GrSpecies.tw (R := R) (V := FreeGr R gp) true) (vD g gp R B)
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
  rw [decomp_vD_bas_eq, map_vD_id_decomp_bas, map_tw_vD_decomp_bas, ← Finset.sum_sumElim]
  symm
  refine Finset.sum_bij (fun z _ => liftV g i z) ?_ ?_ ?_ ?_
  · -- the images are vertices and factorizations of the relabelled trees
    rintro (⟨⟨p, q⟩, k⟩ | ⟨⟨p, q⟩, k⟩) hz
    · rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range] at hz
      dsimp only at hz
      obtain ⟨hpq, hk⟩ := hz
      obtain ⟨-, hw, -⟩ := hfac hpq
      subst hpq
      simp only [liftV, Sum.elim_inl, Finset.mem_sigma, Finset.mem_range, mem_fib]
      refine ⟨by rw [hw]; split_ifs <;> omega, ?_⟩
      exact (relabelAtR_comp_outer g i p q hk).symm
    · rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range] at hz
      dsimp only at hz
      obtain ⟨hpq, hk⟩ := hz
      obtain ⟨-, hw, -⟩ := hfac hpq
      subst hpq
      have := Tree.vb_le_weight (treeOf p) (p.1.rank i)
      simp only [liftV, Sum.elim_inr, Finset.mem_sigma, Finset.mem_range, mem_fib]
      refine ⟨by rw [hw]; omega, ?_⟩
      exact (relabelAtR_comp_inner g i p q hk).symm
  · -- the map is injective
    rintro (⟨⟨p, q⟩, k⟩ | ⟨⟨p, q⟩, k⟩) h₁ (⟨⟨p', q'⟩, k'⟩ | ⟨⟨p', q'⟩, k'⟩) h₂ heq
    · rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range] at h₁ h₂
      dsimp only at h₁ h₂
      simp only [liftV, Sum.elim_inl, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at heq
      obtain ⟨hi, hc, rfl⟩ := heq
      obtain ⟨ht, -, -⟩ := hfac h₁.1
      obtain ⟨ht', -, -⟩ := hfac h₂.1
      have h1 : p.1 = p'.1 := by rw [← relabelAtR_fst g p k, hc, relabelAtR_fst]
      rw [← h1] at ht' hi
      have hsh : Tree.shape (treeOf p) = Tree.shape (treeOf p') := by
        rw [← Tree.shape_relabelAt g (treeOf p) k, ← Tree.shape_relabelAt g (treeOf p') k',
          ← treeOf_relabelAtR, ← treeOf_relabelAtR, hc]
      obtain ⟨e1, -⟩ := Tree.graft_cancel (fun _ _ => PUnit.unit) (treeOf p) (treeOf p')
        (treeOf q) (treeOf q) (p.1.rank i) (rank_lt_arity p i) (ht.symm.trans ht') hsh
      have e : p = p' := reg_ext h1 e1
      subst e
      have : k = k' := by split_ifs at hi <;> omega
      rw [this]
    · rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range] at h₁
      rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range] at h₂
      dsimp only at h₁ h₂
      simp only [liftV, Sum.elim_inl, Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq,
        Prod.mk.injEq] at heq
      obtain ⟨hi, hc, hc'⟩ := heq
      exfalso
      have hv : (treeOf p').vb (p'.1.rank i) = (treeOf p).vb (p.1.rank i) := by
        rw [← hc, treeOf_relabelAtR, relabelAtR_fst, Tree.vb_relabelAt]
      have hw : (treeOf q).weight = (treeOf q').weight := by
        rw [hc', treeOf_relabelAtR, Tree.weight_relabelAt]
      rw [hv] at hi
      have := h₂.2
      split_ifs at hi <;> omega
    · rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range] at h₁
      rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range] at h₂
      dsimp only at h₁ h₂
      simp only [liftV, Sum.elim_inl, Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq,
        Prod.mk.injEq] at heq
      obtain ⟨hi, hc, hc'⟩ := heq
      exfalso
      have hv : (treeOf p).vb (p.1.rank i) = (treeOf p').vb (p'.1.rank i) := by
        rw [hc, treeOf_relabelAtR, relabelAtR_fst, Tree.vb_relabelAt]
      have hw : (treeOf q').weight = (treeOf q).weight := by
        rw [← hc', treeOf_relabelAtR, Tree.weight_relabelAt]
      rw [hv] at hi
      have := h₁.2
      split_ifs at hi <;> omega
    · rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range] at h₁ h₂
      dsimp only at h₁ h₂
      simp only [liftV, Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at heq
      obtain ⟨hi, rfl, hc⟩ := heq
      obtain ⟨ht, -, -⟩ := hfac h₁.1
      obtain ⟨ht', -, -⟩ := hfac h₂.1
      have h1 : q.1 = q'.1 := by rw [← relabelAtR_fst g q k, hc, relabelAtR_fst]
      obtain ⟨-, e2⟩ := Tree.graft_cancel (fun _ _ => PUnit.unit) (treeOf p) (treeOf p)
        (treeOf q) (treeOf q') (p.1.rank i) (rank_lt_arity p i) (ht.symm.trans ht') rfl
      have e : q = q' := reg_ext h1 e2
      subst e
      have e3 : k = k' := by omega
      subst e3
      rfl
  · -- the map is surjective
    rintro ⟨k, ⟨p, q⟩⟩ hx
    rw [Finset.mem_sigma, Finset.mem_range, mem_fib] at hx
    dsimp only at hx
    obtain ⟨hk, hpq⟩ := hx
    have hr := rank_lt_arity p i
    have hst : (treeOf p).graft (p.1.rank i) (treeOf q) = (treeOf s).relabelAt g k := by
      rw [← treeOf_relabelAtR, ← hpq, treeOf_comp]
    have hord : LinOrd.comp i p.1 q.1 = s.1 := by
      rw [← comp_fst, hpq, relabelAtR_fst]
    obtain ⟨s₀, u₀, hsu, hr₀, hc⟩ := Tree.graft_eq_relabelAt g hr hk hst
    have hw0 : (treeOf s).weight = s₀.weight + u₀.weight := by
      rw [← hsu, Tree.weight_graft _ _ _ hr₀]
    have hv0 := Tree.vb_le_weight s₀ (p.1.rank i)
    rcases hc with ⟨hin1, hin2, hps, hqu⟩ | ⟨hout, hps, hqu⟩
    · have hbr : u₀.arity = (treeOf q).arity := by rw [hqu, Tree.arity_relabelAt]
      refine ⟨Sum.inr ⟨(p, withTree q u₀ hbr), k - s₀.vb (p.1.rank i)⟩, ?_, ?_⟩
      · rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range]
        refine ⟨comp_eq_iff.2 ⟨by rw [withTree_fst, hord], by rw [treeOf_withTree, hps, hsu]⟩,
          by rw [treeOf_withTree]; exact Nat.sub_lt_left_of_lt_add hin1 hin2⟩
      · simp only [liftV, Sum.elim_inr]
        rw [hps, show s₀.vb (p.1.rank i) + (k - s₀.vb (p.1.rank i)) = k by omega]
        congr 1
        exact Prod.ext rfl (reg_ext rfl (by rw [treeOf_relabelAtR, treeOf_withTree, hqu]))
    · set k₀ := k - if s₀.vb (p.1.rank i) ≤ k then u₀.weight else 0 with hk₀
      have hk0 : k₀ < s₀.weight := by rw [hk₀]; split_ifs <;> omega
      have har : s₀.arity = (treeOf p).arity := by rw [hps, Tree.arity_relabelAt]
      refine ⟨Sum.inl ⟨(withTree p s₀ har, q), k₀⟩, ?_, ?_⟩
      · rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range]
        exact ⟨comp_eq_iff.2 ⟨hord, by rw [treeOf_withTree, withTree_fst, hqu, hsu]⟩,
          by rw [treeOf_withTree]; exact hk0⟩
      · simp only [liftV, Sum.elim_inl, treeOf_withTree, withTree_fst]
        have hwq : (treeOf q).weight = u₀.weight := by rw [hqu]
        have hkk : (k₀ + if s₀.vb (p.1.rank i) ≤ k₀ then u₀.weight else 0) = k := by
          rw [hk₀]
          by_cases h1 : s₀.vb (p.1.rank i) ≤ k
          · simp only [h1, if_true, show s₀.vb (p.1.rank i) ≤ k - u₀.weight by omega]
            omega
          · simp only [h1, if_false, Nat.sub_zero, Nat.add_zero]
        rw [hwq, hkk]
        congr 1
        exact Prod.ext (reg_ext rfl (by rw [treeOf_relabelAtR, treeOf_withTree, hps])) rfl
  · -- the terms agree
    rintro (⟨⟨p, q⟩, k⟩ | ⟨⟨p, q⟩, k⟩) hz
    · rw [Finset.inl_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range] at hz
      dsimp only at hz
      obtain ⟨hpq, hk⟩ := hz
      obtain ⟨ht, -, -⟩ := hfac hpq
      simp only [liftV, Sum.elim_inl, vdTermO, vdTermL, cSgn, relabelAtR_fst, treeOf_relabelAtR]
      rw [ht, Tree.bpar_graft_outer gp _ _ _ _ (rank_lt_arity p i) hk,
        Tree.apar_relabelAt gp hg _ _ _ (rank_lt_arity p i)]
      simp only [hk, and_true]
      congr 1
      cases Tree.tpar gp (treeOf q) <;> cases Tree.apar gp (treeOf p) (p.1.rank i) <;>
        cases Tree.bpar gp (treeOf p) k <;> cases decide ((treeOf p).vb (p.1.rank i) ≤ k) <;>
        simp [σ]
    · rw [Finset.inr_mem_disjSum, Finset.mem_sigma, mem_fib, Finset.mem_range] at hz
      dsimp only at hz
      obtain ⟨hpq, hk⟩ := hz
      obtain ⟨ht, -, -⟩ := hfac hpq
      simp only [liftV, Sum.elim_inr, vdTermI, vdTermL, cSgn, treeOf_relabelAtR]
      rw [ht, Tree.bpar_graft_inner gp _ _ _ _ (rank_lt_arity p i) hk,
        Tree.tpar_relabelAt gp hg, decide_eq_true hk]
      congr 1
      have hb := Tree.bpar_vb_xor_apar gp (treeOf p) (p.1.rank i) (rank_lt_arity p i)
      rw [← hb]
      cases Tree.tpar gp (treeOf q) <;> cases Tree.apar gp (treeOf p) (p.1.rank i) <;>
        cases Tree.bpar gp (treeOf p) ((treeOf p).vb (p.1.rank i)) <;>
        cases Tree.bpar gp (treeOf q) k <;> simp [σ]

/-- **The vertex derivation is a coderivation**:
`Δᵢ ∘ D = (D ⊗ 1 + (-1)^• ⊗ D) ∘ Δᵢ`, the Koszul sign of `D` passing the outer factor. -/
theorem decomp_vD (hg : ∀ k e, gp k (g k e) = !gp k e) (i : A)
    (x : FreeGr R gp (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := FreeGr R gp) i (vD g gp R _ x)
      = TensorProduct.map (vD g gp R A) LinearMap.id
          (GrCooperad.decomp (R := R) (C := FreeGr R gp) i x)
        + TensorProduct.map (GrSpecies.tw (R := R) (V := FreeGr R gp) true) (vD g gp R B)
          (GrCooperad.decomp (R := R) (C := FreeGr R gp) i x) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity T))
    (GrCooperad.decomp (R := R) (C := FreeGr R gp) (B := B) i ∘ₗ vD g gp R _)
    (TensorProduct.map (vD g gp R A) LinearMap.id ∘ₗ
        GrCooperad.decomp (R := R) (C := FreeGr R gp) (B := B) i +
      TensorProduct.map (GrSpecies.tw (R := R) (V := FreeGr R gp) true) (vD g gp R B) ∘ₗ
        GrCooperad.decomp (R := R) (C := FreeGr R gp) (B := B) i)
    (fun s => decomp_vD_bas hg i s) x
  simpa using h

/-! ## The vertex derivation and the bar differential -/

section Anti

variable (μ : MergeFn T)

omit [Fintype B] [DecidableEq B] in
/-- An odd operator anticommutes with the sign twist. -/
lemma tw_odd {f : FreeGr R gp A →ₗ[R] FreeGr R gp A}
    (hf : ∀ b x, GrOperad.par (R := R) b (f x) = f (GrOperad.par (R := R) (!b) x))
    (x : FreeGr R gp A) :
    GrSpecies.tw (R := R) (V := FreeGr R gp) true (f x)
      = -f (GrSpecies.tw (R := R) (V := FreeGr R gp) true x) := by
  rw [GrSpecies.tw_apply, GrSpecies.tw_apply]
  show GrOperad.par (R := R) false (f x) + σ R true • GrOperad.par (R := R) true (f x)
    = -f (GrOperad.par (R := R) false x + σ R true • GrOperad.par (R := R) true x)
  rw [hf, hf, σ_true, neg_one_smul, neg_one_smul, map_add, map_neg, neg_add, neg_neg,
    Bool.not_false, Bool.not_true, add_comm]

omit [Fintype B] [DecidableEq B] in
lemma tw_tw_true (x : FreeGr R gp A) :
    GrSpecies.tw (R := R) (V := FreeGr R gp) true (GrSpecies.tw (R := R) (V := FreeGr R gp) true x)
      = x := by
  rw [GrSpecies.tw_tw, Bool.xor_self, GrSpecies.tw_false]

variable (g gp R) in
/-- **The defect of the vertex derivation on merge-composites**:
`D (x ⊛ᵢ y) + D x ⊛ᵢ y + (-1)^|x| x ⊛ᵢ D y`. -/
noncomputable def gam (i : A) (x : FreeGr R gp A) (y : FreeGr R gp B) :
    FreeGr R gp (Without A i ⊕ B) :=
  vD g gp R _ (mcomp μ gp R i x y) + mcomp μ gp R i (vD g gp R A x) y
    + mcomp μ gp R i (GrSpecies.tw (R := R) (V := FreeGr R gp) true x) (vD g gp R B y)

variable (g gp R) in
/-- **The anticommutator of the bar differential and the vertex derivation.** -/
noncomputable def anti (A : Type) [Fintype A] [DecidableEq A] (x : FreeGr R gp A) :
    FreeGr R gp A :=
  barD μ gp R A (vD g gp R A x) + vD g gp R A (barD μ gp R A x)

/-- **The anticommutator on a composite**:
`[d, D] (x ∘ᵢ y) = [d, D] x ∘ᵢ y + x ∘ᵢ [d, D] y + Γ (x, y)`. -/
theorem anti_comp (hμ : MergeFn.Odd gp μ) (hg : ∀ k e, gp k (g k e) = !gp k e) (i : A)
    (x : FreeGr R gp A) (y : FreeGr R gp B) :
    anti g gp R μ _ (GrOperad.comp (R := R) i x y)
      = GrOperad.comp (R := R) i (anti g gp R μ A x) y
        + GrOperad.comp (R := R) i x (anti g gp R μ B y) + gam g gp R μ i x y := by
  have tv : ∀ {C : Type} [Fintype C] [DecidableEq C] (z : FreeGr R gp C),
      GrSpecies.tw (R := R) (V := FreeGr R gp) true (vD g gp R C z)
        = -vD g gp R C (GrSpecies.tw (R := R) (V := FreeGr R gp) true z) :=
    fun z => tw_odd (fun b z => par_vD hg b z) z
  have tb : ∀ {C : Type} [Fintype C] [DecidableEq C] (z : FreeGr R gp C),
      GrSpecies.tw (R := R) (V := FreeGr R gp) true (barD μ gp R C z)
        = -barD μ gp R C (GrSpecies.tw (R := R) (V := FreeGr R gp) true z) :=
    fun z => tw_odd (fun b z => par_barD hμ b z) z
  unfold anti gam
  rw [vD_comp hg, map_add, barD_comp hμ, barD_comp hμ, barD_comp hμ, map_add, map_add,
    vD_comp hg, vD_comp hg, tv, tb, tw_tw_true]
  simp only [map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply]
  abel

end Anti

/-! ## The defect on merge-composites lies in an ideal -/

section Gam

variable (μ : MergeFn T)

omit [Fintype B] [DecidableEq B] in
/-- **The vertex derivation has no unit component.** -/
lemma unitCoeff_vD (x : FreeGr R gp A) : unitCoeff gp R A (vD g gp R A x) = 0 := by
  induction x using induction_bas with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | bas c s =>
    rw [map_smul, map_smul, vD_bas, map_sum, Finset.sum_eq_zero (fun k hk => ?_), smul_zero]
    rw [Finset.mem_range] at hk
    rw [map_smul, unitCoeff_bas, treeOf_relabelAtR,
      Tree.isLeaf_of_weight (by rw [Tree.weight_relabelAt]; omega)]
    simp

/-- **The sign twist is multiplicative.** -/
lemma tw_comp' (i : A) (x : FreeGr R gp A) (y : FreeGr R gp B) :
    GrSpecies.tw (R := R) (V := FreeGr R gp) true (GrOperad.comp (R := R) i x y)
      = GrOperad.comp (R := R) i (GrSpecies.tw (R := R) (V := FreeGr R gp) true x)
          (GrSpecies.tw (R := R) (V := FreeGr R gp) true y) :=
  GrOperad.tw_comp true i x y

/-- **The sign twist of a merge-composite**: `(x ⊛ᵢ y)` has the parities of `x` and `y`, plus
one. -/
lemma tw_mcomp (hμ : MergeFn.Odd gp μ) (i : A) (x : FreeGr R gp A) (y : FreeGr R gp B) :
    GrSpecies.tw (R := R) (V := FreeGr R gp) true (mcomp μ gp R i x y)
      = -mcomp μ gp R i (GrSpecies.tw (R := R) (V := FreeGr R gp) true x)
          (GrSpecies.tw (R := R) (V := FreeGr R gp) true y) := by
  induction x using induction_bas with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', neg_add]
  | bas c s =>
    induction y using induction_bas with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy', neg_add]
    | bas c' t =>
      simp only [map_smul, LinearMap.smul_apply, tw_bas]
      by_cases hs : (treeOf s).isLeaf = false
      · by_cases ht : (treeOf t).isLeaf = false
        · rw [mcomp_bas_of μ hs ht, map_smul, tw_bas, treeOf_mcompR,
            Tree.tpar_mgraft μ gp hμ _ _ _ (rank_lt_arity s i) hs ht]
          cases Tree.tpar gp (treeOf s) <;> cases Tree.tpar gp (treeOf t) <;>
            cases mcompSgn gp i s t <;> simp [σ]
        · rw [mcomp_bas_of_right μ _ (by simpa using ht)]
          simp
      · rw [mcomp_bas_of_left μ _ (by simpa using hs)]
        simp

/-- **The defect commutes with relabellings.** -/
lemma gam_map {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (σ' : A ≃ A') (τ : B ≃ B') (i : A) (x : FreeGr R gp A) (y : FreeGr R gp B) :
    gam g gp R μ (σ' i) (GrOperad.map (R := R) σ' x) (GrOperad.map (R := R) τ y)
      = GrOperad.map (R := R) (compEquiv σ' τ i) (gam g gp R μ i x y) := by
  unfold gam
  rw [← map_vD σ' x, ← map_vD τ y,
    show GrSpecies.tw (R := R) (V := FreeGr R gp) true (GrOperad.map (R := R) σ' x)
      = GrOperad.map (R := R) σ' (GrSpecies.tw (R := R) (V := FreeGr R gp) true x) from
      (GrSpecies.map_tw true σ' x).symm,
    mcomp_map, mcomp_map, mcomp_map, ← map_vD, map_add, map_add]

omit [Fintype B] [DecidableEq B] in
lemma unitCoeff_tw (z : FreeGr R gp A) :
    unitCoeff gp R A (GrSpecies.tw (R := R) (V := FreeGr R gp) true z) = unitCoeff gp R A z := by
  induction z using induction_bas with
  | zero => simp
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add]
  | bas c s =>
    rw [map_smul, map_smul, tw_bas, map_smul, map_smul, unitCoeff_bas]
    split_ifs with h
    · rw [Tree.eq_leaf_of_isLeaf h, Tree.tpar_leaf, σ_false, one_smul]
    · simp

/-- **The defect on a composite at the right**:
`Γᵢ (x, y ∘ⱼ z) = Γᵢ (x, y) ∘ⱼ z`, for `y` without unit component. -/
theorem gam_comp_right (hμ : MergeFn.Odd gp μ) (hg : ∀ k e, gp k (g k e) = !gp k e)
    {D : Type} [Fintype D] [DecidableEq D] (i : A) (j : B) (x : FreeGr R gp A)
    (y : FreeGr R gp B) (z : FreeGr R gp D) (hy : unitCoeff gp R B y = 0) :
    gam g gp R μ i x (GrOperad.comp (R := R) j y z)
      = GrOperad.map (R := R) (seqEquiv i j D)
          (GrOperad.comp (R := R) (Sum.inr j) (gam g gp R μ i x y) z) := by
  have hy' : unitCoeff gp R B (vD g gp R B y) = 0 := unitCoeff_vD y
  have hy'' : unitCoeff gp R B (GrSpecies.tw (R := R) (V := FreeGr R gp) true y) = 0 := by
    rw [unitCoeff_tw, hy]
  unfold gam
  rw [vD_comp hg, map_add]
  rw [← comp_mcomp_outer μ i j x y z hy, ← comp_mcomp_outer μ i j _ y z hy,
    ← comp_mcomp_outer μ i j _ _ z hy', ← comp_mcomp_outer μ i j _ _ _ hy'', ← map_vD,
    vD_comp hg, tw_mcomp μ hμ]
  simp only [map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply]
  abel

/-- **The defect at an input of the inner factor of a composite**:
`Γ_{j} (x ∘ᵢ y, z) = x ∘ᵢ Γⱼ (y, z)`, for `y` without unit component. -/
theorem gam_comp_inner (hμ : MergeFn.Odd gp μ) (hg : ∀ k e, gp k (g k e) = !gp k e)
    {D : Type} [Fintype D] [DecidableEq D] (i : A) (j : B) (x : FreeGr R gp A)
    (y : FreeGr R gp B) (z : FreeGr R gp D) (hy : unitCoeff gp R B y = 0) :
    GrOperad.map (R := R) (seqEquiv i j D)
        (gam g gp R μ (Sum.inr j) (GrOperad.comp (R := R) i x y) z)
      = GrOperad.comp (R := R) i x (gam g gp R μ j y z) := by
  have hy' : unitCoeff gp R B (vD g gp R B y) = 0 := unitCoeff_vD y
  have hy'' : unitCoeff gp R B (GrSpecies.tw (R := R) (V := FreeGr R gp) true y) = 0 := by
    rw [unitCoeff_tw, hy]
  have tv : ∀ {C : Type} [Fintype C] [DecidableEq C] (w : FreeGr R gp C),
      GrSpecies.tw (R := R) (V := FreeGr R gp) true (vD g gp R C w)
        = -vD g gp R C (GrSpecies.tw (R := R) (V := FreeGr R gp) true w) :=
    fun w => tw_odd (fun b w => par_vD hg b w) w
  unfold gam
  rw [vD_comp hg, tw_comp']
  simp only [map_add, LinearMap.add_apply]
  rw [map_vD, mcomp_comp_inner μ hμ i j x y z hy, mcomp_comp_inner μ hμ i j _ y z hy,
    mcomp_comp_inner μ hμ i j _ _ z hy', mcomp_comp_inner μ hμ i j _ _ _ hy'', vD_comp hg,
    tv, tw_tw_true]
  simp only [map_neg, LinearMap.neg_apply]
  abel

/-- **The defect at an input of the outer factor of a composite**:
`Γₖ (x ∘ᵢ y, z) = (-1)^{|y||z|} Γₖ (x, z) ∘ᵢ y`, for homogeneous `y`, `z`. -/
theorem gam_comp_par (hμ : MergeFn.Odd gp μ) (hg : ∀ k e, gp k (g k e) = !gp k e)
    {D : Type} [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (x : FreeGr R gp A)
    {q r : Bool} {y : FreeGr R gp B} {z : FreeGr R gp D} (hy : GrOperad.par (R := R) q y = y)
    (hz : GrOperad.par (R := R) r z = z) :
    GrOperad.map (R := R) (parEquiv hik B D)
        (gam g gp R μ (Sum.inl ⟨k, Ne.symm hik⟩) (GrOperad.comp (R := R) i x y) z)
      = σ R (q && r) • GrOperad.comp (R := R) (Sum.inl ⟨i, hik⟩) (gam g gp R μ k x z) y := by
  have hvy : GrOperad.par (R := R) (!q) (vD g gp R B y) = vD g gp R B y := by
    rw [par_vD hg, Bool.not_not, hy]
  have hvz : GrOperad.par (R := R) (!r) (vD g gp R D z) = vD g gp R D z := by
    rw [par_vD hg, Bool.not_not, hz]
  have hty : GrSpecies.tw (R := R) (V := FreeGr R gp) true y = σ R q • y := by
    rw [GrSpecies.tw_hom true hy, Bool.true_and]
  have htz : GrSpecies.tw (R := R) (V := FreeGr R gp) true z = σ R r • z := by
    rw [GrSpecies.tw_hom true hz, Bool.true_and]
  have hpty : GrOperad.par (R := R) q (σ R q • y) = σ R q • y := by rw [map_smul, hy]
  unfold gam
  rw [vD_comp hg, tw_comp', hty]
  simp only [map_add, LinearMap.add_apply]
  rw [map_vD, mcomp_comp_par μ hμ hik x hy hz, mcomp_comp_par μ hμ hik _ hy hz,
    mcomp_comp_par μ hμ hik _ hvy hz, mcomp_comp_par μ hμ hik _ hpty hvz, map_smul, vD_comp hg,
    tw_mcomp μ hμ, htz]
  simp only [map_smul, LinearMap.smul_apply, map_neg, LinearMap.neg_apply, smul_add,
    smul_neg, smul_smul]
  cases q <;> cases r <;> simp [σ] <;> abel

end Gam

/-! ### Induction on trees -/

section GamMem

variable {μ} (hμ : MergeFn.Odd gp μ) (hg : ∀ k e, gp k (g k e) = !gp k e)
  (I : GrOperadIdeal R (FreeGr R gp))

lemma gam_smul_left (i : A) (c : R) (x : FreeGr R gp A) (y : FreeGr R gp B) :
    gam g gp R μ i (c • x) y = c • gam g gp R μ i x y := by
  unfold gam
  simp only [map_smul, LinearMap.smul_apply, smul_add]

lemma gam_smul_right (i : A) (c : R) (x : FreeGr R gp A) (y : FreeGr R gp B) :
    gam g gp R μ i x (c • y) = c • gam g gp R μ i x y := by
  unfold gam
  simp only [map_smul, smul_add]

lemma gam_add_left (i : A) (x x' : FreeGr R gp A) (y : FreeGr R gp B) :
    gam g gp R μ i (x + x') y = gam g gp R μ i x y + gam g gp R μ i x' y := by
  unfold gam
  simp only [map_add, LinearMap.add_apply]
  abel

lemma gam_add_right (i : A) (x : FreeGr R gp A) (y y' : FreeGr R gp B) :
    gam g gp R μ i x (y + y') = gam g gp R μ i x y + gam g gp R μ i x y' := by
  unfold gam
  simp only [map_add]
  abel

variable {I}

include hμ hg in
/-- **The defect on a corolla and any tree** lies in an ideal containing the defects on pairs of
corollas. -/
theorem gam_gen_mem
    (hcor : ∀ {k l : ℕ} (a : T k) (b : T l) (j : Fin k),
      gam g gp R μ j (gen a) (gen b) ∈ I.sub (Without (Fin k) j ⊕ Fin l))
    (y : Reg (TreeOfArity T) B) {k : ℕ} (a : T k) (j : Fin k) :
    gam g gp R μ j (gen a) (SgnLin.bas (treeSgn gp) R y) ∈ I.sub (Without (Fin k) j ⊕ B) := by
  have hmap : ∀ {B B' : Type} [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
      (τ : B ≃ B') (w : FreeGr R gp B),
      (∀ {k : ℕ} (a : T k) (j : Fin k), gam g gp R μ j (gen a) w ∈ I.sub _) →
      ∀ {k : ℕ} (a : T k) (j : Fin k),
        gam g gp R μ j (gen a) (GrOperad.map (R := R) τ w) ∈ I.sub _ := by
    intro B B' _ _ _ _ τ w h k a j
    have e := gam_map (μ := μ) (g := g) (Equiv.refl (Fin k)) τ j (gen (R := R) (gp := gp) a) w
    rw [GrOperad.map_refl] at e
    rw [show j = (Equiv.refl (Fin k)) j from rfl, e]
    exact I.map_mem _ (h a j)
  revert k
  refine FreeReg.induction (P := fun B _ _ y => ∀ {k : ℕ} (a : T k) (j : Fin k),
      gam g gp R μ j (gen a) (SgnLin.bas (treeSgn gp) R y) ∈ I.sub (Without (Fin k) j ⊕ B))
    ?_ ?_ ?_ ?_ y
  · intro B B' _ _ _ _ τ y hy k a j
    rw [← SgnLin.map_bas]
    exact hmap τ _ (fun a j => hy a j) a j
  · intro k a j
    have h0 : gam g gp R μ j (gen a) (SgnLin.bas (treeSgn gp) R
        (SetOperad.one : Reg (TreeOfArity T) Unit)) = 0 := by
      unfold gam
      rw [mcomp_leaf_right μ rfl _ _, mcomp_leaf_right μ rfl _ _,
        vD_bas_of_weight (x := (SetOperad.one : Reg (TreeOfArity T) Unit)) rfl]
      simp
    rw [h0]
    exact zero_mem _
  · intro B₁ B₂ _ _ _ _ i' y₁ y₂ h₁ h₂ k a j
    rw [bas_comp, gam_smul_right]
    refine Submodule.smul_mem _ _ ?_
    by_cases hl : (treeOf y₁).isLeaf = true
    · obtain ⟨E, hE⟩ := comp_leaf_bas (R := R) (gp := gp) hl i' (SgnLin.bas (treeSgn gp) R y₂)
      rw [hE]
      exact hmap E _ (fun a j => h₂ a j) a j
    · have hu : unitCoeff gp R B₁ (SgnLin.bas (treeSgn gp) R y₁) = 0 := by
        rw [unitCoeff_bas, if_neg hl]
      rw [gam_comp_right μ hμ hg j i' _ _ _ hu]
      exact I.map_mem _ (I.comp_mem_left _ _ (h₁ a j))
  · intro l b k a j
    exact hcor a b j

include hμ hg in
/-- **The defect on any two trees** lies in an ideal containing the defects on pairs of
corollas. -/
theorem gam_bas_mem
    (hcor : ∀ {k l : ℕ} (a : T k) (b : T l) (j : Fin k),
      gam g gp R μ j (gen a) (gen b) ∈ I.sub (Without (Fin k) j ⊕ Fin l))
    (x : Reg (TreeOfArity T) A) {D : Type} [Fintype D] [DecidableEq D]
    (y : Reg (TreeOfArity T) D) (i : A) :
    gam g gp R μ i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y)
      ∈ I.sub (Without A i ⊕ D) := by
  have hmap : ∀ {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
      (e : A ≃ A') (w : FreeGr R gp A),
      (∀ (i : A), gam g gp R μ i w (SgnLin.bas (treeSgn gp) R y) ∈ I.sub _) →
      ∀ (i : A'), gam g gp R μ i (GrOperad.map (R := R) e w) (SgnLin.bas (treeSgn gp) R y)
        ∈ I.sub _ := by
    intro A A' _ _ _ _ e w h i
    obtain ⟨i0, rfl⟩ := e.surjective i
    have ee := gam_map (μ := μ) (g := g) e (Equiv.refl D) i0 w (SgnLin.bas (treeSgn gp) R y)
    rw [GrOperad.map_refl] at ee
    rw [ee]
    exact I.map_mem _ (h _)
  revert i
  refine FreeReg.induction (P := fun A _ _ x => ∀ (i : A),
      gam g gp R μ i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y)
        ∈ I.sub (Without A i ⊕ D)) ?_ ?_ ?_ ?_ x
  · intro A A' _ _ _ _ e x hx i
    rw [← SgnLin.map_bas]
    exact hmap e _ hx i
  · intro i
    have h0 : gam g gp R μ i (SgnLin.bas (treeSgn gp) R (SetOperad.one : Reg (TreeOfArity T) Unit))
        (SgnLin.bas (treeSgn gp) R y) = 0 := by
      unfold gam
      rw [mcomp_leaf_left μ rfl _ _, tw_bas, map_smul, LinearMap.smul_apply,
        mcomp_leaf_left μ rfl _ _,
        vD_bas_of_weight (x := (SetOperad.one : Reg (TreeOfArity T) Unit))
        rfl]
      simp
    rw [h0]
    exact zero_mem _
  · intro A₁ B₁ _ _ _ _ j x₁ x₂ h₁ h₂ i
    rw [bas_comp, gam_smul_left]
    refine Submodule.smul_mem _ _ ?_
    rcases i with ⟨k, hk⟩ | b
    · have e := gam_comp_par (g := g) (μ := μ) hμ hg (Ne.symm hk) (SgnLin.bas (treeSgn gp) R x₁)
        (SgnLin.par_bas (δ := treeSgn gp) (R := R) x₂)
        (SgnLin.par_bas (δ := treeSgn gp) (R := R) y)
      refine mem_of_map_mem I (parEquiv (Ne.symm hk) B₁ D) ?_
      rw [e]
      exact Submodule.smul_mem _ _ (I.comp_mem_left _ _ (h₁ k))
    · by_cases hl : (treeOf x₂).isLeaf = true
      · obtain ⟨E, hE⟩ := comp_bas_leaf (R := R) (gp := gp) j (SgnLin.bas (treeSgn gp) R x₁) hl
        rw [hE]
        exact hmap E _ h₁ _
      · have hu : unitCoeff gp R B₁ (SgnLin.bas (treeSgn gp) R x₂) = 0 := by
          rw [unitCoeff_bas, if_neg hl]
        refine mem_of_map_mem I (seqEquiv j b D) ?_
        rw [gam_comp_inner μ hμ hg j b _ _ _ hu]
        exact I.comp_mem_right _ _ (h₂ b)
  · intro k a i
    exact gam_gen_mem hμ hg hcor y a i

include hμ hg in
/-- **The defect lies in an ideal containing the defects on pairs of corollas.** -/
theorem gam_mem
    (hcor : ∀ {k l : ℕ} (a : T k) (b : T l) (j : Fin k),
      gam g gp R μ j (gen a) (gen b) ∈ I.sub (Without (Fin k) j ⊕ Fin l))
    (i : A) (x : FreeGr R gp A) (y : FreeGr R gp B) :
    gam g gp R μ i x y ∈ I.sub (Without A i ⊕ B) := by
  induction x using induction_bas with
  | zero =>
    unfold gam
    simp
  | add x x' hx hx' =>
    rw [gam_add_left]
    exact add_mem hx hx'
  | bas c s =>
    rw [gam_smul_left]
    refine Submodule.smul_mem _ _ ?_
    induction y using induction_bas with
    | zero =>
      unfold gam
      simp
    | add y y' hy hy' =>
      rw [gam_add_right]
      exact add_mem hy hy'
    | bas c' t =>
      rw [gam_smul_right]
      exact Submodule.smul_mem _ _ (gam_bas_mem hμ hg hcor s t i)

include hμ hg in
/-- **The anticommutator of the bar differential and the vertex derivation** lies in an ideal
containing the defects on pairs of corollas. -/
theorem anti_mem
    (hcor : ∀ {k l : ℕ} (a : T k) (b : T l) (j : Fin k),
      gam g gp R μ j (gen a) (gen b) ∈ I.sub (Without (Fin k) j ⊕ Fin l))
    (x : FreeGr R gp A) : anti g gp R μ A x ∈ I.sub A := by
  induction x using induction_bas with
  | zero =>
    unfold anti
    simp
  | add x x' hx hx' =>
    unfold anti at hx hx' ⊢
    simp only [map_add]
    convert add_mem hx hx' using 1
    abel
  | bas c s =>
    unfold anti
    simp only [map_smul, ← smul_add]
    refine Submodule.smul_mem _ _ ?_
    refine FreeReg.induction (P := fun A _ _ s => barD μ gp R A (vD g gp R A
        (SgnLin.bas (treeSgn gp) R s)) + vD g gp R A (barD μ gp R A (SgnLin.bas (treeSgn gp) R s))
        ∈ I.sub A) ?_ ?_ ?_ ?_ s
    · intro A A' _ _ _ _ e s hs
      rw [← SgnLin.map_bas, ← map_vD, ← map_barD, ← map_barD, ← map_vD, ← map_add]
      exact I.map_mem e hs
    · dsimp only
      rw [vD_bas_of_weight (x := (SetOperad.one : Reg (TreeOfArity T) Unit)) rfl,
        barD_bas_of_isLeaf (x := (SetOperad.one : Reg (TreeOfArity T) Unit)) rfl]
      simp
    · intro A₁ B₁ _ _ _ _ j x₁ x₂ h₁ h₂
      rw [bas_comp, map_smul, map_smul, map_smul, map_smul, ← smul_add]
      refine Submodule.smul_mem _ _ ?_
      have e := anti_comp μ hμ hg j (SgnLin.bas (treeSgn gp) R x₁) (SgnLin.bas (treeSgn gp) R x₂)
      unfold anti at e
      rw [e]
      exact add_mem (add_mem (I.comp_mem_left _ _ h₁) (I.comp_mem_right _ _ h₂))
        (gam_mem hμ hg hcor j _ _)
    · intro k e
      show barD μ gp R _ (vD g gp R _ (gen e)) + vD g gp R _ (barD μ gp R _ (gen e)) ∈ _
      rw [vD_gen, barD_gen, barD_gen, map_zero, add_zero]
      exact zero_mem _

end GamMem

end FreeGr

end Operad
