/-
# Descent of the bar differential

Let `S` be relations in the free graded operad `FreeGr R gp`: homogeneous, without unit component,
killed by the bar differential, and whose merge-composites with generators, on either side, lie in
the ideal `J` they generate (`FreeGr.RelHyp`). Then:

* **merge-composites with elements of `J` lie in `J`** (`FreeGr.mcomp_mem_left`,
  `FreeGr.mcomp_mem_right`): the elements of `J` merge-composing into `J` form an ideal containing
  the relations, by the laws of merge-composition, and merge-composing a relation with any tree
  lands in `J`, by induction on the tree;
* **the bar differential preserves `J`** (`FreeGr.barD_mem`): the elements of `J` with their bar
  differential in `J` form an ideal, by the Leibniz rule up to merge-composition.
-/
import Operad.BarMerge

universe u v

namespace Operad

open Sym GerBV TreeOfArity
open scoped TensorProduct

namespace FreeGr

variable {T : ℕ → Type v} (μ : MergeFn T) {gp : ∀ k, T k → Bool} {R : Type u} [CommRing R]
variable {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype D] [DecidableEq D]

/-! ## Composing with units -/

/-- A unit tree is a relabelling of the unit. -/
lemma eq_map_one_of_isLeaf {t : Reg (TreeOfArity T) B} (ht : (treeOf t).isLeaf = true) :
    ∃ e : Unit ≃ B, t = SetOperad.map e SetOperad.one := by
  have h1 := treeOf_arity t
  rw [Tree.eq_leaf_of_isLeaf ht, Tree.arity_leaf, t.2.2] at h1
  obtain ⟨b, hb⟩ := Fintype.card_eq_one_iff.1 h1.symm
  let e : Unit ≃ B := ⟨fun _ => b, fun _ => (), fun _ => rfl, fun b' => (hb b').symm⟩
  exact ⟨e, eq_of_isLeaf ht rfl⟩

lemma comp_one_eq (j : A) (z : FreeGr R gp A) :
    GrOperad.comp (R := R) j z (GrOperad.one (R := R) (P := FreeGr R gp))
      = GrOperad.map (R := R) (rightUnitEquiv j).symm z := by
  conv_rhs => rw [← GrOperad.comp_one (R := R) j z]
  rw [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]

lemma one_comp_eq (z : FreeGr R gp D) :
    GrOperad.comp (R := R) () (GrOperad.one (R := R) (P := FreeGr R gp)) z
      = GrOperad.map (R := R) (leftUnitEquiv D).symm z := by
  conv_rhs => rw [← GrOperad.one_comp (R := R) z]
  rw [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]

/-- Composing with a unit tree is a relabelling. -/
lemma comp_bas_leaf (j : A) (z : FreeGr R gp A) {t : Reg (TreeOfArity T) B}
    (ht : (treeOf t).isLeaf = true) :
    ∃ E : A ≃ Without A j ⊕ B,
      GrOperad.comp (R := R) j z (SgnLin.bas (treeSgn gp) R t) = GrOperad.map (R := R) E z := by
  obtain ⟨e, rfl⟩ := eq_map_one_of_isLeaf ht
  refine ⟨(rightUnitEquiv j).symm.trans (compEquiv (Equiv.refl A) e j), ?_⟩
  have h := GrOperad.map_comp (R := R) (P := FreeGr R gp) (Equiv.refl A) e j z
    (GrOperad.one (R := R))
  rw [GrOperad.map_refl] at h
  rw [← SgnLin.map_bas]
  refine (h.symm.trans ?_)
  rw [comp_one_eq, GrOperad.map_trans]
  rfl

/-- Composing into a unit tree is a relabelling. -/
lemma comp_leaf_bas {t : Reg (TreeOfArity T) B} (ht : (treeOf t).isLeaf = true) (j : B)
    (z : FreeGr R gp D) :
    ∃ E : D ≃ Without B j ⊕ D,
      GrOperad.comp (R := R) j (SgnLin.bas (treeSgn gp) R t) z = GrOperad.map (R := R) E z := by
  obtain ⟨e, rfl⟩ := eq_map_one_of_isLeaf ht
  obtain ⟨u, rfl⟩ := e.surjective j
  cases u
  refine ⟨(leftUnitEquiv D).symm.trans (compEquiv e (Equiv.refl D) ()), ?_⟩
  have h := GrOperad.map_comp (R := R) (P := FreeGr R gp) e (Equiv.refl D) ()
    (GrOperad.one (R := R)) z
  rw [GrOperad.map_refl] at h
  rw [← SgnLin.map_bas]
  refine (h.symm.trans ?_)
  rw [one_comp_eq, GrOperad.map_trans]

lemma mcomp_map_left {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (i : A)
    (x : FreeGr R gp A) (y : FreeGr R gp B) :
    mcomp μ gp R (e i) (GrOperad.map (R := R) e x) y
      = GrOperad.map (R := R) (compEquiv e (Equiv.refl B) i) (mcomp μ gp R i x y) := by
  rw [← mcomp_map μ e (Equiv.refl B) i x y, GrOperad.map_refl]

lemma mcomp_map_right {B' : Type} [Fintype B'] [DecidableEq B'] (e : B ≃ B') (i : A)
    (x : FreeGr R gp A) (y : FreeGr R gp B) :
    mcomp μ gp R i x (GrOperad.map (R := R) e y)
      = GrOperad.map (R := R) (compEquiv (Equiv.refl A) e i) (mcomp μ gp R i x y) := by
  rw [← mcomp_map μ (Equiv.refl A) e i x y, GrOperad.map_refl]
  rfl

lemma mcomp_leaf_left {x : Reg (TreeOfArity T) A} (hx : (treeOf x).isLeaf = true) (i : A)
    (y : FreeGr R gp B) : mcomp μ gp R i (SgnLin.bas (treeSgn gp) R x) y = 0 := by
  induction y using induction_bas with
  | zero => simp
  | add y y' hy hy' => rw [map_add, hy, hy', add_zero]
  | bas c t => rw [map_smul, mcomp_bas_of_left μ _ hx, smul_zero]

lemma mcomp_leaf_right {y : Reg (TreeOfArity T) B} (hy : (treeOf y).isLeaf = true) (i : A)
    (x : FreeGr R gp A) : mcomp μ gp R i x (SgnLin.bas (treeSgn gp) R y) = 0 := by
  induction x using induction_bas with
  | zero => simp
  | add x x' hx hx' => rw [map_add, LinearMap.add_apply, hx, hx', add_zero]
  | bas c s => rw [map_smul, LinearMap.smul_apply, mcomp_bas_of_right μ _ hy, smul_zero]

lemma bas_comp (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    SgnLin.bas (treeSgn gp) R (SetOperad.comp i x y)
      = σ R (Tree.tpar gp (treeOf y) && Tree.apar gp (treeOf x) (x.1.rank i)) •
          GrOperad.comp (R := R) i (SgnLin.bas (treeSgn gp) R x) (SgnLin.bas (treeSgn gp) R y) := by
  rw [comp_bas_eq, smul_smul, σ_mul_self, one_smul]

lemma par_bas_self (x : Reg (TreeOfArity T) A) :
    GrOperad.par (R := R) (Tree.tpar gp (treeOf x)) (SgnLin.bas (treeSgn gp) R x)
      = SgnLin.bas (treeSgn gp) R x :=
  SgnLin.par_bas x

lemma unitCoeff_bas_of {x : Reg (TreeOfArity T) A} (hx : (treeOf x).isLeaf = false) :
    unitCoeff gp R A (SgnLin.bas (treeSgn gp) R x) = 0 := by
  rw [unitCoeff_bas, hx]
  rfl

/-! ## Membership in an ideal -/

section Mem

variable (I : GrOperadIdeal R (FreeGr R gp))

lemma mem_of_map_mem {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') {x : FreeGr R gp A}
    (h : GrOperad.map (R := R) e x ∈ I.sub A') : x ∈ I.sub A := by
  have := I.map_mem e.symm h
  rwa [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl] at this

lemma tw_mem {x : FreeGr R gp A} (h : x ∈ I.sub A) (e : Bool) :
    GrSpecies.tw (R := R) (V := FreeGr R gp) e x ∈ I.sub A := by
  rw [GrSpecies.tw_apply]
  exact add_mem (I.par_mem false h) (Submodule.smul_mem _ _ (I.par_mem true h))

lemma mcomp_map_left_mem {A' : Type} [Fintype A'] [DecidableEq A'] (E : A ≃ A')
    {z : FreeGr R gp A} {y : FreeGr R gp B}
    (h : ∀ a, mcomp μ gp R a z y ∈ I.sub (Without A a ⊕ B)) (i : A') :
    mcomp μ gp R i (GrOperad.map (R := R) E z) y ∈ I.sub _ := by
  obtain ⟨a, rfl⟩ := E.surjective i
  rw [mcomp_map_left]
  exact I.map_mem _ (h a)

lemma mcomp_map_right_mem {B' : Type} [Fintype B'] [DecidableEq B'] (E : B ≃ B') (i : A)
    {x : FreeGr R gp A} {z : FreeGr R gp B} (h : mcomp μ gp R i x z ∈ I.sub _) :
    mcomp μ gp R i x (GrOperad.map (R := R) E z) ∈ I.sub _ := by
  rw [mcomp_map_right]
  exact I.map_mem _ h

variable (hμ : MergeFn.Odd gp μ)
include hμ

lemma mcomp_par_right (i : A) (c a : Bool) (x : FreeGr R gp A) (z : FreeGr R gp B) :
    mcomp μ gp R i (GrOperad.par (R := R) a x) (GrOperad.par (R := R) c z)
      = GrOperad.par (R := R) (!(xor a c)) (mcomp μ gp R i (GrOperad.par (R := R) a x) z) := by
  conv_rhs => rw [← GrOperad.par_add (R := R) z]
  rw [map_add, map_add, par_mcomp μ hμ, par_mcomp μ hμ]
  cases a <;> cases c <;> simp

lemma mcomp_par_left (i : A) (c a : Bool) (z : FreeGr R gp A) (y : FreeGr R gp B) :
    mcomp μ gp R i (GrOperad.par (R := R) c z) (GrOperad.par (R := R) a y)
      = GrOperad.par (R := R) (!(xor c a)) (mcomp μ gp R i z (GrOperad.par (R := R) a y)) := by
  conv_rhs => rw [← GrOperad.par_add (R := R) z]
  rw [map_add, LinearMap.add_apply, map_add, par_mcomp μ hμ, par_mcomp μ hμ]
  cases a <;> cases c <;> simp

/-- Merging with the parts of an element of the ideal. -/
lemma mcomp_par_mem_right {z : FreeGr R gp B} (i : A)
    (h : ∀ x : FreeGr R gp A, mcomp μ gp R i x z ∈ I.sub _) (c : Bool) (x : FreeGr R gp A) :
    mcomp μ gp R i x (GrOperad.par (R := R) c z) ∈ I.sub _ := by
  rw [← GrOperad.par_add (R := R) x, map_add, LinearMap.add_apply, mcomp_par_right μ hμ,
    mcomp_par_right μ hμ]
  exact add_mem (I.par_mem _ (h _)) (I.par_mem _ (h _))

lemma mcomp_par_mem_left {z : FreeGr R gp A} (i : A)
    (h : ∀ y : FreeGr R gp B, mcomp μ gp R i z y ∈ I.sub _) (c : Bool) (y : FreeGr R gp B) :
    mcomp μ gp R i (GrOperad.par (R := R) c z) y ∈ I.sub _ := by
  rw [← GrOperad.par_add (R := R) y, map_add, mcomp_par_left μ hμ, mcomp_par_left μ hμ]
  exact add_mem (I.par_mem _ (h _)) (I.par_mem _ (h _))

end Mem

/-! ## Merging with the ideal generated by relations -/

section Descent

variable (S : ∀ n : ℕ, Set (FreeGr R gp (Fin n)))

variable (gp R) in
/-- **Relations for the bar differential**: killed by it, without unit component, homogeneous,
and whose merge-composites with generators lie in the ideal they generate. -/
structure RelHyp : Prop where
  barD_eq : ∀ n, ∀ r ∈ S n, barD μ gp R (Fin n) r = 0
  unitCoeff_eq : ∀ n, ∀ r ∈ S n, unitCoeff gp R (Fin n) r = 0
  homog : ∀ n, ∀ r ∈ S n, ∃ b, GrOperad.par (R := R) b r = r
  gen_left : ∀ n, ∀ r ∈ S n, ∀ (k : ℕ) (c : T k) (i : Fin k),
    mcomp μ gp R i (gen (R := R) (gp := gp) c) r ∈ (GrOperadIdeal.span R S).sub _
  gen_right : ∀ n, ∀ r ∈ S n, ∀ (k : ℕ) (c : T k) (i : Fin n),
    mcomp μ gp R i r (gen (R := R) (gp := gp) c) ∈ (GrOperadIdeal.span R S).sub _

variable {S} (hμ : MergeFn.Odd gp μ) (hS : RelHyp μ gp R S)

local notation "𝒥" => GrOperadIdeal.span R S

include hS in
lemma unitCoeff_of_mem {z : FreeGr R gp A} (hz : z ∈ (𝒥).sub A) : unitCoeff gp R A z = 0 :=
  LinearMap.mem_ker.1 ((GrOperadIdeal.span_le (I := noUnitIdeal gp R)).2
    (fun n r hr => LinearMap.mem_ker.2 (hS.unitCoeff_eq n r hr)) A hz)

/-- The elements of the ideal whose merge-composites with anything lie in the ideal. -/
abbrev MergeMem (A : Type) [Fintype A] [DecidableEq A] (z : FreeGr R gp A) : Prop :=
  z ∈ (𝒥).sub A ∧
    (∀ (B : Type) [Fintype B] [DecidableEq B] (x : FreeGr R gp B) (i : B),
      mcomp μ gp R i x z ∈ (𝒥).sub _) ∧
    (∀ (B : Type) [Fintype B] [DecidableEq B] (y : FreeGr R gp B) (i : A),
      mcomp μ gp R i z y ∈ (𝒥).sub _)

include hμ hS in
/-- **The elements merging into the ideal form an ideal.** -/
noncomputable def mergeIdeal : GrOperadIdeal R (FreeGr R gp) where
  sub A _ _ :=
    { carrier := {z | MergeMem μ (S := S) A z}
      add_mem' := by
        intro x y hx hy
        refine ⟨add_mem hx.1 hy.1, fun B _ _ w i => ?_, fun B _ _ w i => ?_⟩
        · rw [map_add]
          exact add_mem (hx.2.1 B w i) (hy.2.1 B w i)
        · rw [map_add, LinearMap.add_apply]
          exact add_mem (hx.2.2 B w i) (hy.2.2 B w i)
      zero_mem' := by
        refine ⟨zero_mem _, fun B _ _ w i => ?_, fun B _ _ w i => ?_⟩
        · rw [map_zero]
          exact zero_mem _
        · rw [map_zero, LinearMap.zero_apply]
          exact zero_mem _
      smul_mem' := by
        intro c x hx
        refine ⟨Submodule.smul_mem _ c hx.1, fun B _ _ w i => ?_, fun B _ _ w i => ?_⟩
        · rw [map_smul]
          exact Submodule.smul_mem _ c (hx.2.1 B w i)
        · rw [map_smul, LinearMap.smul_apply]
          exact Submodule.smul_mem _ c (hx.2.2 B w i) }
  par_mem := by
    intro A _ _ b z hz
    exact ⟨(𝒥).par_mem b hz.1, fun B _ _ x i => mcomp_par_mem_right μ 𝒥 hμ i (hz.2.1 B · i) b x,
      fun B _ _ y i => mcomp_par_mem_left μ 𝒥 hμ i (hz.2.2 B · i) b y⟩
  map_mem := by
    intro A A' _ _ _ _ e z hz
    exact ⟨(𝒥).map_mem e hz.1, fun B _ _ x i => mcomp_map_right_mem μ 𝒥 e i (hz.2.1 B x i),
      fun B _ _ y i => mcomp_map_left_mem μ 𝒥 e (fun a => hz.2.2 B y a) i⟩
  comp_mem_left := by
    intro A B _ _ _ _ j z w hz
    have hu := unitCoeff_of_mem μ hS hz.1
    refine ⟨(𝒥).comp_mem_left j w hz.1, fun B' _ _ x i => ?_, fun B' _ _ y i => ?_⟩
    · rw [← comp_mcomp_outer μ i j x z w hu]
      exact (𝒥).map_mem _ ((𝒥).comp_mem_left _ _ (hz.2.1 B' x i))
    · rcases i with i₀ | b
      · rw [← GrOperad.par_add (R := R) w, ← GrOperad.par_add (R := R) y]
        simp only [map_add, LinearMap.add_apply]
        refine add_mem (add_mem ?_ ?_) (add_mem ?_ ?_) <;>
        · refine mem_of_map_mem 𝒥 (parEquiv (Ne.symm i₀.2) B B') ?_
          rw [mcomp_comp_par μ hμ (Ne.symm i₀.2) z (GrOperad.par_par_self _ _)
            (GrOperad.par_par_self _ _)]
          exact Submodule.smul_mem _ _ ((𝒥).comp_mem_left _ _ (hz.2.2 B' _ i₀.1))
      · induction w using induction_bas with
        | zero => rw [map_zero, map_zero, LinearMap.zero_apply]; exact zero_mem _
        | add w w' hw hw' => rw [map_add, map_add, LinearMap.add_apply]; exact add_mem hw hw'
        | bas c t =>
          rw [map_smul, map_smul, LinearMap.smul_apply]
          refine Submodule.smul_mem _ c ?_
          by_cases ht : (treeOf t).isLeaf = true
          · obtain ⟨E, hE⟩ := comp_bas_leaf j z ht
            rw [hE]
            exact mcomp_map_left_mem μ 𝒥 E (fun a => hz.2.2 B' y a) _
          · refine mem_of_map_mem 𝒥 (seqEquiv j b B') ?_
            rw [mcomp_comp_inner μ hμ j b z _ y (unitCoeff_bas_of (by simpa using ht))]
            exact (𝒥).comp_mem_left _ _ (tw_mem 𝒥 hz.1 true)
  comp_mem_right := by
    intro A B _ _ _ _ j w z hz
    have hu := unitCoeff_of_mem μ hS hz.1
    refine ⟨(𝒥).comp_mem_right j w hz.1, fun B' _ _ x i => ?_, fun B' _ _ y i => ?_⟩
    · induction w using induction_bas with
      | zero => rw [map_zero, LinearMap.zero_apply, map_zero]; exact zero_mem _
      | add w w' hw hw' => rw [map_add, LinearMap.add_apply, map_add]; exact add_mem hw hw'
      | bas c t =>
        rw [map_smul, LinearMap.smul_apply, map_smul]
        refine Submodule.smul_mem _ c ?_
        by_cases ht : (treeOf t).isLeaf = true
        · obtain ⟨E, hE⟩ := comp_leaf_bas ht j z
          rw [hE]
          exact mcomp_map_right_mem μ 𝒥 E i (hz.2.1 B' x i)
        · rw [← comp_mcomp_outer μ i j x _ z (unitCoeff_bas_of (by simpa using ht))]
          exact (𝒥).map_mem _ ((𝒥).comp_mem_right _ _ hz.1)
    · rcases i with i₀ | b
      · rw [← GrOperad.par_add (R := R) z, ← GrOperad.par_add (R := R) y]
        simp only [map_add, LinearMap.add_apply]
        refine add_mem (add_mem ?_ ?_) (add_mem ?_ ?_) <;>
        · refine mem_of_map_mem 𝒥 (parEquiv (Ne.symm i₀.2) B B') ?_
          rw [mcomp_comp_par μ hμ (Ne.symm i₀.2) w (GrOperad.par_par_self _ _)
            (GrOperad.par_par_self _ _)]
          exact Submodule.smul_mem _ _ ((𝒥).comp_mem_right _ _ ((𝒥).par_mem _ hz.1))
      · refine mem_of_map_mem 𝒥 (seqEquiv j b B') ?_
        rw [mcomp_comp_inner μ hμ j b w z y hu]
        exact (𝒥).comp_mem_right _ _ (hz.2.2 B' y b)

include hμ hS in
/-- Merge-composing a tree into a relation lands in the ideal. -/
lemma mcomp_rel_left {n : ℕ} {r : FreeGr R gp (Fin n)} (hr : r ∈ S n)
    (x : Reg (TreeOfArity T) A) (i : A) :
    mcomp μ gp R i (SgnLin.bas (treeSgn gp) R x) r ∈ (𝒥).sub _ := by
  obtain ⟨b, hb⟩ := hS.homog n r hr
  revert i
  refine FreeReg.induction (P := fun A _ _ x => ∀ i : A,
    mcomp μ gp R i (SgnLin.bas (treeSgn gp) R x) r ∈ (𝒥).sub _) ?_ ?_ ?_ ?_ x
  · intro A B _ _ _ _ e x hx i
    rw [← SgnLin.map_bas]
    exact mcomp_map_left_mem μ 𝒥 e hx i
  · intro i
    rw [mcomp_leaf_left μ rfl]
    exact zero_mem _
  · intro A B _ _ _ _ q x y hx hy i
    rw [bas_comp, map_smul, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    rcases i with i₀ | j
    · refine mem_of_map_mem 𝒥 (parEquiv (Ne.symm i₀.2) B (Fin n)) ?_
      rw [mcomp_comp_par μ hμ (Ne.symm i₀.2) _ (par_bas_self y) hb]
      exact Submodule.smul_mem _ _ ((𝒥).comp_mem_left _ _ (hx i₀.1))
    · by_cases hy0 : (treeOf y).isLeaf = true
      · obtain ⟨E, hE⟩ := comp_bas_leaf q (SgnLin.bas (treeSgn gp) R x) hy0
        rw [hE]
        exact mcomp_map_left_mem μ 𝒥 E hx _
      · refine mem_of_map_mem 𝒥 (seqEquiv q j (Fin n)) ?_
        rw [mcomp_comp_inner μ hμ q j _ _ r (unitCoeff_bas_of (by simpa using hy0))]
        exact (𝒥).comp_mem_right _ _ (hy j)
  · intro k c i
    exact hS.gen_left n r hr k c i

include hS in
/-- Merge-composing a relation into a tree lands in the ideal. -/
lemma mcomp_rel_right {n : ℕ} {r : FreeGr R gp (Fin n)} (hr : r ∈ S n)
    (y : Reg (TreeOfArity T) B) (i : Fin n) :
    mcomp μ gp R i r (SgnLin.bas (treeSgn gp) R y) ∈ (𝒥).sub _ := by
  refine FreeReg.induction (P := fun B _ _ y =>
    mcomp μ gp R i r (SgnLin.bas (treeSgn gp) R y) ∈ (𝒥).sub _) ?_ ?_ ?_ ?_ y
  · intro A B _ _ _ _ e y hy
    rw [← SgnLin.map_bas]
    exact mcomp_map_right_mem μ 𝒥 e i hy
  · show mcomp μ gp R i r (SgnLin.bas (treeSgn gp) R (SetOperad.one : Reg (TreeOfArity T) Unit))
      ∈ (𝒥).sub _
    rw [mcomp_leaf_right μ (y := (SetOperad.one : Reg (TreeOfArity T) Unit)) rfl]
    exact zero_mem _
  · intro A B _ _ _ _ q y₁ y₂ h1 h2
    rw [bas_comp, map_smul]
    refine Submodule.smul_mem _ _ ?_
    by_cases hy1 : (treeOf y₁).isLeaf = true
    · obtain ⟨E, hE⟩ := comp_leaf_bas hy1 q (SgnLin.bas (treeSgn gp) R y₂)
      rw [hE]
      exact mcomp_map_right_mem μ 𝒥 E i h2
    · rw [← comp_mcomp_outer μ i q r _ _ (unitCoeff_bas_of (by simpa using hy1))]
      exact (𝒥).map_mem _ ((𝒥).comp_mem_left _ _ h1)
  · intro k c
    exact hS.gen_right n r hr k c i

include hμ hS in
lemma span_le_mergeIdeal : GrOperadIdeal.span R S ≤ mergeIdeal μ hμ hS := by
  refine GrOperadIdeal.span_le.2 fun n r hr =>
    ⟨GrOperadIdeal.subset_span n hr, fun B _ _ x i => ?_, fun B _ _ y i => ?_⟩
  · induction x using induction_bas with
    | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
    | add x x' hx hx' => rw [map_add, LinearMap.add_apply]; exact add_mem hx hx'
    | bas c s =>
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ c (mcomp_rel_left μ hμ hS hr s i)
  · induction y using induction_bas with
    | zero => rw [map_zero]; exact zero_mem _
    | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'
    | bas c t =>
      rw [map_smul]
      exact Submodule.smul_mem _ c (mcomp_rel_right μ hS hr t i)

include hμ hS in
/-- **Merge-composing into the ideal generated by the relations lands in it.** -/
theorem mcomp_mem_right (x : FreeGr R gp A) {z : FreeGr R gp B} (hz : z ∈ (𝒥).sub B) (i : A) :
    mcomp μ gp R i x z ∈ (𝒥).sub _ :=
  (span_le_mergeIdeal μ hμ hS B hz).2.1 A x i

include hμ hS in
/-- **Merge-composing an element of the ideal generated by the relations lands in it.** -/
theorem mcomp_mem_left {z : FreeGr R gp A} (hz : z ∈ (𝒥).sub A) (y : FreeGr R gp B) (i : A) :
    mcomp μ gp R i z y ∈ (𝒥).sub _ :=
  (span_le_mergeIdeal μ hμ hS A hz).2.2 B y i

include hμ hS in
/-- The elements of the ideal with their bar differential in the ideal form an ideal. -/
noncomputable def barDIdeal : GrOperadIdeal R (FreeGr R gp) where
  sub A _ _ := (𝒥).sub A ⊓ ((𝒥).sub A).comap (barD μ gp R A)
  par_mem := by
    intro A _ _ b z hz
    refine ⟨(𝒥).par_mem b hz.1, ?_⟩
    show barD μ gp R A (GrOperad.par (R := R) b z) ∈ (𝒥).sub A
    have h := par_barD hμ (!b) z
    rw [Bool.not_not] at h
    rw [← h]
    exact (𝒥).par_mem _ hz.2
  map_mem := by
    intro A A' _ _ _ _ e z hz
    refine ⟨(𝒥).map_mem e hz.1, ?_⟩
    show barD μ gp R A' (GrOperad.map (R := R) e z) ∈ (𝒥).sub A'
    rw [← map_barD]
    exact (𝒥).map_mem e hz.2
  comp_mem_left := by
    intro A B _ _ _ _ i z y hz
    refine ⟨(𝒥).comp_mem_left i y hz.1, ?_⟩
    show barD μ gp R _ (GrOperad.comp (R := R) i z y) ∈ (𝒥).sub _
    rw [barD_comp hμ]
    exact add_mem (add_mem ((𝒥).comp_mem_left _ _ hz.2)
      ((𝒥).comp_mem_left _ _ (tw_mem 𝒥 hz.1 true))) (mcomp_mem_left μ hμ hS hz.1 y i)
  comp_mem_right := by
    intro A B _ _ _ _ i x z hz
    refine ⟨(𝒥).comp_mem_right i x hz.1, ?_⟩
    show barD μ gp R _ (GrOperad.comp (R := R) i x z) ∈ (𝒥).sub _
    rw [barD_comp hμ]
    exact add_mem (add_mem ((𝒥).comp_mem_right _ _ hz.1) ((𝒥).comp_mem_right _ _ hz.2))
      (mcomp_mem_right μ hμ hS x hz.1 i)

include hμ hS in
/-- **The bar differential preserves the ideal generated by the relations.** -/
theorem barD_mem {z : FreeGr R gp A} (hz : z ∈ (𝒥).sub A) : barD μ gp R A z ∈ (𝒥).sub A :=
  ((GrOperadIdeal.span_le (I := barDIdeal μ hμ hS)).2 (fun n r hr =>
    ⟨GrOperadIdeal.subset_span n hr, by
      show barD μ gp R (Fin n) r ∈ (𝒥).sub (Fin n)
      rw [hS.barD_eq n r hr]
      exact zero_mem _⟩) A hz).2

end Descent

end FreeGr

end Operad
