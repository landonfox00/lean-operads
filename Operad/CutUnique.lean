/-
# Morphisms into the cut cooperad on any species

Let `V` be a graded linear species, possibly with elements without inputs. **Two morphisms of
graded cooperads `C → T^c(V)` with the same coefficient of the generators agree**, over a
`ℚ`-algebra (`FreeGrL.app_eq_of_genCoef_any`). `Operad/CutCofree.lean` proves this for `V`
without elements without inputs, through the convolution square `ι ⋆ ι` of the cobar
construction, a sum over the nonempty sets of inputs, which does not see the cuts whose inner
part has no inputs.

* **The cuts of a tree are its vertices other than the root** (`FreeGr.card_cuts`): the
  factorizations `t = e·(p ∘ q)` into two nontrivial parts, at all the splittings of the inputs,
  the empty set of inputs included, correspond to the vertices of `t` other than the root. With
  an inner part without inputs, the composite order no longer determines the outer order, but it
  does with the rank of the slot (`Sym.LinOrd.comp_cancel_of_rank`), which the vertex gives.
* **Grafting the cuts** (`FreeGrL.euler`, `FreeGrL.euler_eq`): composing the two parts without
  unit component of the decomposition at every splitting of the inputs multiplies a tree with
  `n ≥ 1` vertices by `n - 1`; so this operator is `E - (1 - ε)`, for `E` the derivation counting
  the vertices.
* **Uniqueness.** The difference of two morphisms with the same coefficient of the generators
  has values with at least two vertices, and if its values have at least `k ≥ 2` vertices, their
  cuts graft to trees with at least `k + 1` vertices; so the values have at least `k + 1`
  vertices (`FreeGrL.mem_vxGe_succ_of_euler`), and an element of `T^c(V)` is a finite sum of
  trees.

So **the universal property of the cut cooperad holds for a species with elements without
inputs**: for a conilpotent coaugmented graded cooperad `C` such that in each arity the reduced
cooperations or the elements of `V` form a projective module, the coaugmented morphisms
`C → T^c(V)` are the morphisms `C̄ → V` (`FreeGrL.cofreeHomEquivConilAny`,
`FreeGrL.existsUnique_liftConilAny`); existence is `FreeGrL.liftConil`, which has no hypothesis
on the elements without inputs. Without projectivity, existence for a species with elements
without inputs is not treated: `Operad/CutLift.lean` goes through the cobar construction.
-/
import Operad.CutStar
import Operad.CutCofreeConil
import Operad.CobarContraction
import Operad.BarWeights

universe u v w

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

/-! ## Composite orders -/

namespace Sym.LinOrd

variable {A B : Type} [DecidableEq A] [Fintype A] [Fintype B]

/-- **A composite order and the rank of the slot determine the factors**, the inner order
possibly empty. -/
lemma comp_cancel_of_rank {i : A} {P P' : LinOrd A} {Q Q' : LinOrd B}
    (hr : P.rank i = P'.rank i) (h : LinOrd.comp i P Q = LinOrd.comp i P' Q') :
    P = P' ∧ Q = Q' := by
  have hl : ∀ w w', compLt P.lt Q.lt i w w' ↔ compLt P'.lt Q'.lt i w w' := fun w w' => by
    have := congrArg LinOrd.lt h
    exact Iff.of_eq (congrFun (congrFun this w) w')
  have key : ∀ (P P' : LinOrd A) (Q Q' : LinOrd B), P.rank i = P'.rank i →
      LinOrd.comp i P Q = LinOrd.comp i P' Q' → ∀ a : Without A i, P.lt a.1 i → P'.lt a.1 i := by
    intro P P' Q Q' hr h a hlt
    by_contra hn
    have hgt : P'.lt i a.1 := (P'.total a.1 i a.2).resolve_left hn
    have e : (LinOrd.comp i P Q).rank (Sum.inl a) = (LinOrd.comp i P' Q').rank (Sum.inl a) := by
      rw [h]
    rw [rank_comp_inl_of_lt i P Q a hlt, rank_comp_inl_of_gt i P' Q' a hgt] at e
    have h1 := P.rank_lt_rank hlt
    have h2 := P'.rank_lt_rank hgt
    omega
  have hlt : ∀ a : Without A i, P.lt a.1 i ↔ P'.lt a.1 i := fun a =>
    ⟨key P P' Q Q' hr h a, key P' P Q' Q hr.symm h.symm a⟩
  have hgt : ∀ a : Without A i, P.lt i a.1 ↔ P'.lt i a.1 := fun a => by
    constructor
    · intro h1
      refine (P'.total a.1 i a.2).resolve_left fun h2 => ?_
      exact P.irrefl _ (P.trans _ _ _ ((hlt a).2 h2) h1)
    · intro h1
      refine (P.total a.1 i a.2).resolve_left fun h2 => ?_
      exact P'.irrefl _ (P'.trans _ _ _ ((hlt a).1 h2) h1)
  refine ⟨LinOrd.ext fun a a' => ?_, LinOrd.ext fun b b' => hl (Sum.inr b) (Sum.inr b')⟩
  by_cases ha : a = i <;> by_cases ha' : a' = i
  · rw [ha, ha']
    exact ⟨fun h => absurd h (P.irrefl _), fun h => absurd h (P'.irrefl _)⟩
  · rw [ha]
    exact hgt ⟨a', ha'⟩
  · rw [ha']
    exact hlt ⟨a, ha⟩
  · exact hl (Sum.inl ⟨a, ha⟩) (Sum.inl ⟨a', ha'⟩)

end Sym.LinOrd

/-! ## The cuts of a tree -/

namespace FreeGr

variable {T : ℕ → Type v} {X : Type} [Fintype X] [DecidableEq X]

/-- **The cuts of a labelled tree**: its factorizations into two nontrivial parts, at all the
splittings of its inputs. -/
noncomputable def cuts (t : Reg (TreeOfArity T) X) :
    Finset (Σ S : Finset X, Reg (TreeOfArity T) (SOut S) × Reg (TreeOfArity T) (SIn S)) :=
  ((Finset.univ : Finset (Finset X)).sigma fun S =>
    (SetOperad.FiniteFact.finite none (SetOperad.map (splitEquiv S).symm t)).toFinset).filter
    fun x => (treeOf x.2.1).isLeaf = false ∧ (treeOf x.2.2).isLeaf = false

lemma mem_cuts {t : Reg (TreeOfArity T) X}
    {x : Σ S : Finset X, Reg (TreeOfArity T) (SOut S) × Reg (TreeOfArity T) (SIn S)} :
    x ∈ cuts t ↔ SetOperad.map (splitEquiv x.1) (SetOperad.comp none x.2.1 x.2.2) = t
      ∧ (treeOf x.2.1).isLeaf = false ∧ (treeOf x.2.2).isLeaf = false := by
  obtain ⟨S, p, q⟩ := x
  rw [cuts, Finset.mem_filter, Finset.mem_sigma]
  refine and_congr_left fun _ => ?_
  show Finset.univ.val.Mem S ∧ (p, q) ∈ _ ↔ _
  rw [mem_fib]
  constructor
  · rintro ⟨-, h⟩
    show SetOperad.map (splitEquiv S) (SetOperad.comp none p q) = t
    rw [h, SetOperad.map_map_symm]
  · intro h
    refine ⟨Finset.mem_univ S, ?_⟩
    show SetOperad.comp none p q = SetOperad.map (splitEquiv S).symm t
    rw [← h, SetOperad.map_symm_map]

/-- **The cuts of a tree correspond to its vertices other than the root.** -/
theorem card_cuts (t : Reg (TreeOfArity T) X) : (cuts t).card = (treeOf t).weight - 1 := by
  rw [← Nat.card_Ico 1 (treeOf t).weight]
  refine Finset.card_bij (fun x _ => vert none x.2.1) ?_ ?_ ?_
  · rintro ⟨S, p, q⟩ hx
    obtain ⟨hrep, hp, hq⟩ := mem_cuts.1 hx
    exact vert_mem hrep hp hq
  · rintro ⟨S₁, p₁, q₁⟩ hx₁ ⟨S₂, p₂, q₂⟩ hx₂ hv
    obtain ⟨hrep₁, -, hq₁⟩ := mem_cuts.1 hx₁
    obtain ⟨hrep₂, -, hq₂⟩ := mem_cuts.1 hx₂
    have c1 := cutV_vert hrep₁ hq₁
    have c2 := cutV_vert hrep₂ hq₂
    dsimp only at hv hrep₁ hrep₂ c1 c2
    rw [hv, c2] at c1
    simp only [Prod.mk.injEq] at c1
    obtain ⟨hp, hq, hr⟩ := c1
    have hS : S₁ = S₂ := by
      ext a
      rw [mem_of_rep hrep₁, mem_of_rep hrep₂, hr, hq]
    subst hS
    have hc : SetOperad.comp none p₁ q₁ = SetOperad.comp none p₂ q₂ :=
      SetOperad.map_injective (splitEquiv S₁) (hrep₁.trans hrep₂.symm)
    have ho := LinOrd.comp_cancel_of_rank hr.symm (congrArg Prod.fst hc)
    rw [reg_ext ho.1 hp.symm, reg_ext ho.2 hq.symm]
  · intro v hv
    rw [Finset.mem_Ico] at hv
    obtain ⟨e, he⟩ := exists_rep t hv.2
    obtain ⟨S, hSdef⟩ : ∃ S : Finset X, S = Finset.univ.map ⟨fun b => e (Sum.inr b),
        fun b b' h => by simpa using e.injective h⟩ := ⟨_, rfl⟩
    have hS : ∀ x, x ∈ S ↔ ∃ b, e (Sum.inr b) = x := fun x => by simp [hSdef]
    have hcanon := map_comp_canon_reg e S hS (stdT ((treeOf t).cutV v).1)
      (stdT ((treeOf t).cutV v).2.1)
    rw [he] at hcanon
    refine ⟨⟨S, SetOperad.map (GrOperad.canonOut e S hS) (stdT ((treeOf t).cutV v).1),
      SetOperad.map (GrOperad.canonIn e S hS) (stdT ((treeOf t).cutV v).2.1)⟩, ?_, ?_⟩
    · exact mem_cuts.2 ⟨hcanon.symm, Tree.isLeaf_cutV_fst hv.1 hv.2 rfl,
        Tree.isLeaf_cutV _ _ hv.2⟩
    · show (treeOf (SetOperad.map (GrOperad.canonOut e S hS) (stdT _))).vb
        ((SetOperad.map (GrOperad.canonOut e S hS) (stdT _)).1.rank none) = v
      rw [treeOf_map, treeOf_stdT, map_fst, LinOrd.rank_map]
      have hsymm : (GrOperad.canonOut e S hS).symm none
          = ⟨((treeOf t).cutV v).2.2, Tree.lt_arity_cutV _ v hv.2⟩ := by
        rw [Equiv.symm_apply_eq, GrOperad.canonOut_self]
      rw [hsymm, rank_stdT]
      exact Tree.vb_cutV _ _ hv.2

end FreeGr

/-! ## Grafting the cuts -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B X : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype X]
  [DecidableEq X]

local notation "𝒞" => FreeGrL R V
local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R V)) R

variable (R V) in
/-- The term of `FreeGrL.euler` at a set of inputs. -/
noncomputable def eulerAt (S : Finset X) : 𝒞 X →ₗ[R] 𝒞 X :=
  GrOperad.map (R := R) (splitEquiv S) ∘ₗ ConvOp.mu (R := R) (P := FreeGrL R V) none ∘ₗ
    TensorProduct.map (secC R V (SOut S)) (secC R V (SIn S)) ∘ₗ
    GrCooperad.decomp (R := R) (C := FreeGrL R V) none ∘ₗ
    GrOperad.map (R := R) (splitEquiv S).symm

variable (R V) in
/-- **Grafting the cuts**: the composite of the two parts without unit component of the
decomposition, at every splitting of the inputs. -/
noncomputable def euler (X : Type) [Fintype X] [DecidableEq X] : 𝒞 X →ₗ[R] 𝒞 X :=
  ∑ S : Finset X, eulerAt R V S

/-- The part without unit component of a basis tree. -/
lemma secC_proj_bas (p : Reg (TreeOfArity (GrGen R V)) A) :
    secC R V A ((𝒥).proj A (𝔟 p))
      = if (treeOf p).isLeaf = false then (𝒥).proj A (𝔟 p) else 0 := by
  by_cases hp : (treeOf p).isLeaf = false
  · rw [if_pos hp, secC_of_unitCoeff (unitCoeffL_proj_bas hp)]
  · rw [if_neg hp]
    obtain ⟨e, he⟩ := proj_bas_leaf (Bool.eq_true_of_not_eq_false hp)
    rw [he, secC_unit]

/-- **The term of a basis tree at a set of inputs**: the tree, once for each of its cuts there. -/
lemma eulerAt_proj_bas (S : Finset X) (t : Reg (TreeOfArity (GrGen R V)) X) :
    eulerAt R V S ((𝒥).proj X (𝔟 t))
      = ∑ pq ∈ (SetOperad.FiniteFact.finite none (SetOperad.map (splitEquiv S).symm t)).toFinset,
          if (treeOf pq.1).isLeaf = false ∧ (treeOf pq.2).isLeaf = false
            then (𝒥).proj X (𝔟 t) else 0 := by
  have hd := LinearMap.congr_fun ((projHom R V).decomp_app (A := SOut S) (B := SIn S) none)
    (𝔟 (SetOperad.map (splitEquiv S).symm t))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, FreeGr.decomp_bas] at hd
  have h1 : GrOperad.map (R := R) (splitEquiv S).symm ((𝒥).proj X (𝔟 t))
      = (projHom R V).app _ (𝔟 (SetOperad.map (splitEquiv S).symm t)) :=
    (proj_bas_map _ t).symm
  rw [eulerAt, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, h1, hd, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun pq hpq => ?_
  have hc := FreeGr.mem_fib.1 hpq
  rw [map_smul, TensorProduct.map_tmul, map_smul, TensorProduct.map_tmul, map_smul,
    ConvOp.mu_tmul, map_smul]
  show _ • GrOperad.map (R := R) (splitEquiv S) (GrOperad.comp (R := R) none
    (secC R V _ ((𝒥).proj _ (𝔟 pq.1))) (secC R V _ ((𝒥).proj _ (𝔟 pq.2)))) = _
  rw [secC_proj_bas, secC_proj_bas]
  by_cases hp : (treeOf pq.1).isLeaf = false
  · by_cases hq : (treeOf pq.2).isLeaf = false
    · rw [if_pos hp, if_pos hq, if_pos ⟨hp, hq⟩]
      have h2 : GrOperad.comp (R := R) none ((𝒥).proj _ (𝔟 pq.1)) ((𝒥).proj _ (𝔟 pq.2))
          = (𝒥).proj _ (GrOperad.comp (R := R) none (𝔟 pq.1) (𝔟 pq.2)) := rfl
      rw [h2, FreeGr.comp_bas_eq, hc, map_smul, proj_bas_map, map_smul,
        ← GrOperad.map_trans, Equiv.symm_trans_self, GrOperad.map_refl, smul_smul, σ_mul_self,
        one_smul]
    · rw [if_pos hp, if_neg hq, if_neg (show ¬((treeOf pq.1).isLeaf = false
        ∧ (treeOf pq.2).isLeaf = false) from fun h => hq h.2), map_zero, map_zero, smul_zero]
  · rw [if_neg hp, if_neg (show ¬((treeOf pq.1).isLeaf = false
      ∧ (treeOf pq.2).isLeaf = false) from fun h => hp h.1), LinearMap.map_zero₂, map_zero,
      smul_zero]

/-- **Grafting the cuts of a basis tree** multiplies it by the number of its vertices other than
the root. -/
lemma euler_proj_bas (t : Reg (TreeOfArity (GrGen R V)) X) :
    euler R V X ((𝒥).proj X (𝔟 t)) = ((treeOf t).weight - 1) • (𝒥).proj X (𝔟 t) := by
  rw [euler, LinearMap.sum_apply, ← FreeGr.card_cuts t, ← Finset.sum_const, FreeGr.cuts,
    Finset.sum_filter, Finset.sum_sigma]
  exact Finset.sum_congr rfl fun S _ => eulerAt_proj_bas S t

/-- **Grafting the cuts is `E - (1 - ε)`**, for `E` the derivation counting the vertices. -/
theorem euler_eq (y : 𝒞 X) : euler R V X y = (wtD R V).app X y - secC R V X y := by
  obtain ⟨w, rfl⟩ := (𝒥).proj_surjective X y
  refine Lin.induction₁ (S := Reg (TreeOfArity (GrGen R V))) (euler R V X ∘ₗ (𝒥).proj X)
    (((wtD R V).app X - secC R V X) ∘ₗ (𝒥).proj X) (fun t => ?_) w
  show euler R V X ((𝒥).proj X (𝔟 t))
    = (wtD R V).app X ((𝒥).proj X (𝔟 t)) - secC R V X ((𝒥).proj X (𝔟 t))
  rw [euler_proj_bas, wtD_proj_bas, secC_proj_bas]
  by_cases ht : (treeOf t).isLeaf = false
  · have h1 := Tree.one_le_weight ht
    rw [if_pos ht, ← Nat.cast_smul_eq_nsmul R, Nat.cast_sub h1, Nat.cast_one, sub_smul, one_smul]
  · rw [if_neg ht, Tree.eq_leaf_of_isLeaf (Bool.eq_true_of_not_eq_false ht), Tree.weight_leaf,
      Nat.zero_sub, zero_smul, Nat.cast_zero, zero_smul, sub_zero]

/-! ## Vertices -/

lemma map_mem_vxGe (e : A ≃ B) {p : ℕ} {y : 𝒞 A} (hy : y ∈ vxGe R V p A) :
    GrOperad.map (R := R) e y ∈ vxGe R V p B :=
  Submodule.iSup_induction _ (motive := fun y => GrOperad.map (R := R) e y ∈ vxGe R V p B) hy
    (fun k y hy => Submodule.mem_iSup_of_mem k (map_mem_eig e hy))
    (by beta_reduce; rw [map_zero]; exact zero_mem _)
    (fun y y' hy hy' => by beta_reduce at hy hy' ⊢; rw [map_add]; exact add_mem hy hy')

/-- **The numbers of vertices add under composition.** -/
lemma comp_mem_vxGe (i : A) {a b : ℕ} {x : 𝒞 A} {y : 𝒞 B} (hx : x ∈ vxGe R V a A)
    (hy : y ∈ vxGe R V b B) : GrOperad.comp (R := R) i x y ∈ vxGe R V (a + b) _ :=
  comp_mem_of_iSup i (fun k l x hx y hy => mem_vxGe (by have := k.2; have := l.2; omega)
    (comp_mem_eig i hx hy)) hx hy

/-- The derivation counting the vertices, minus the identity, preserves the trees with at least
`p` vertices. -/
lemma wtD_sub_mem_vxGe {p : ℕ} {y : 𝒞 A} (hy : y ∈ vxGe R V p A) :
    (wtD R V).app A y - y ∈ vxGe R V p A :=
  Submodule.iSup_induction _ (motive := fun y => (wtD R V).app A y - y ∈ vxGe R V p A) hy
    (fun k y hy => by
      show (wtD R V).app A y - y ∈ vxGe R V p A
      rw [Cobar.wtD_eq_derSp, mem_eig.1 hy]
      exact Submodule.mem_iSup_of_mem k (sub_mem (Submodule.smul_mem _ _ hy) hy))
    (by beta_reduce; rw [map_zero, sub_zero]; exact zero_mem _)
    (fun y y' hy hy' => by
      beta_reduce at hy hy' ⊢
      rw [map_add, add_sub_add_comm]
      exact add_mem hy hy')

/-- An operation without unit component is a combination of trees with vertices. -/
lemma mem_vxGe_one_of_unitCoeffL [Algebra ℚ R] {z : 𝒞 A} (hz : unitCoeffL R V A z = 0) :
    z ∈ vxGe R V 1 A := by
  have h := vxGe_anti (R := R) (V := V) (A := A) (show 1 ≤ 2 by omega) (sub_ι_genCoef_mem hz)
  have h1 := mem_vxGe (R := R) (p := 1) le_rfl (ι_mem_vx (R := R) (genCoef R V A z))
  have := add_mem h h1
  rwa [sub_add_cancel] at this

/-- The trees with vertices have no unit component. -/
lemma unitCoeffL_of_mem_vxGe_one [Algebra ℚ R] {z : 𝒞 A} (hz : z ∈ vxGe R V 1 A) :
    unitCoeffL R V A z = 0 := by
  have key : ∀ w : 𝒞 A, unitCoeffL R V A ((wtD R V).app A w) = 0 := by
    intro w
    obtain ⟨y, rfl⟩ := (𝒥).proj_surjective A w
    refine Lin.induction₁ (S := Reg (TreeOfArity (GrGen R V)))
      (unitCoeffL R V A ∘ₗ (wtD R V).app A ∘ₗ (𝒥).proj A) 0 (fun t => ?_) y
    show unitCoeffL R V A ((wtD R V).app A ((𝒥).proj A (𝔟 t))) = 0
    rw [wtD_proj_bas, map_smul]
    by_cases ht : (treeOf t).isLeaf = false
    · rw [unitCoeffL_proj_bas ht, smul_zero]
    · rw [Tree.eq_leaf_of_isLeaf (Bool.eq_true_of_not_eq_false ht), Tree.weight_leaf,
        Nat.cast_zero, zero_smul]
  refine Submodule.iSup_induction _ (motive := fun z => unitCoeffL R V A z = 0) hz
    (fun k y hy => ?_) (map_zero _) (fun y y' hy hy' => by
      beta_reduce at hy hy' ⊢
      rw [map_add, hy, hy', add_zero])
  have h := key y
  rw [Cobar.wtD_eq_derSp, mem_eig.1 hy, map_smul] at h
  exact (isUnit_natCast_of_ne_zero (R := R) (show k.1 ≠ 0 by have := k.2; omega)).smul_left_cancel.1
    (h.trans (smul_zero _).symm)

/-- **An element with at least `k ≥ 2` vertices whose cuts graft to trees with at least `k + 1`
vertices has at least `k + 1` vertices.** -/
theorem mem_vxGe_succ_of_euler [Algebra ℚ R] {k : ℕ} (hk : 2 ≤ k) {y : 𝒞 A}
    (hy : y ∈ vxGe R V k A) (he : euler R V A y ∈ vxGe R V (k + 1) A) :
    y ∈ vxGe R V (k + 1) A := by
  have hu : unitCoeffL R V A y = 0 :=
    unitCoeffL_of_mem_vxGe_one (vxGe_anti (show 1 ≤ k by omega) hy)
  rw [euler_eq, secC_of_unitCoeff hu] at he
  rw [vxGe_eq k] at hy
  obtain ⟨z, hz, y', hy', rfl⟩ := Submodule.mem_sup.1 hy
  have h1 : ((k : R) - 1) • z ∈ vxGe R V (k + 1) A := by
    have h2 := sub_mem he (wtD_sub_mem_vxGe hy')
    rw [map_add, add_sub_add_comm, add_sub_cancel_right, Cobar.wtD_eq_derSp, mem_eig.1 hz] at h2
    rwa [sub_smul, one_smul]
  have hle : vxGe R V (k + 1) A ≤ ⨆ (i : ℕ) (_ : i ≠ k), vx R V i A :=
    iSup_le fun j => le_iSup₂_of_le (f := fun (i : ℕ) (_ : i ≠ k) => vx R V i A) j.1
      (by have := j.2; omega) le_rfl
  have h0 : ((k : R) - 1) • z = 0 :=
    Submodule.disjoint_def.1
      (iSupIndep_eigenspace_nat ((derSp (GrSpEnd.id R V)).app A) k) _
      (Submodule.smul_mem _ _ hz) (hle h1)
  have hunit := isUnit_natCast_sub (R := R) (show k ≠ 1 by omega)
  rw [Nat.cast_one] at hunit
  rw [hunit.smul_left_cancel.1 (h0.trans (smul_zero _).symm), zero_add]
  exact hy'

/-! ## Uniqueness -/

variable {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]

omit [GrCooperad R C] in
/-- The difference of two tensor products of linear maps. -/
lemma map_sub_map {M N P Q : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (a a' : M →ₗ[R] P)
    (b b' : N →ₗ[R] Q) (t : M ⊗[R] N) :
    TensorProduct.map a b t - TensorProduct.map a' b' t
      = TensorProduct.map (a - a') b t + TensorProduct.map a' (b - b') t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_zero, add_zero]
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.sub_apply, TensorProduct.sub_tmul,
      TensorProduct.tmul_sub]
    abel
  | add t t' ht ht' =>
    rw [map_add, map_add, map_add, map_add, add_sub_add_comm, ht, ht']
    abel

omit [GrCooperad R C] in
/-- The composite of the values of two families with at least `m` and `n` vertices has at least
`m + n` vertices. -/
lemma mu_map_mem_vxGe (i : A) {m n : ℕ} (u : C A →ₗ[R] 𝒞 A) (v : C B →ₗ[R] 𝒞 B)
    (hu : ∀ a, u a ∈ vxGe R V m A) (hv : ∀ b, v b ∈ vxGe R V n B) (t : C A ⊗[R] C B) :
    ConvOp.mu (R := R) (P := FreeGrL R V) i (TensorProduct.map u v t) ∈ vxGe R V (m + n) _ := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact zero_mem _
  | tmul a b =>
    rw [TensorProduct.map_tmul, ConvOp.mu_tmul]
    exact comp_mem_vxGe i (hu a) (hv b)
  | add t t' ht ht' =>
    rw [map_add, map_add]
    exact add_mem ht ht'

/-- **The cuts of the difference of two morphisms graft to trees with one more vertex**: when
all the differences of two morphisms into the cut cooperad have at least `k` vertices and no unit
component, grafting their cuts gives trees with at least `k + 1` vertices. -/
lemma euler_sub_mem [Algebra ℚ R] {f f' : GrCooperadHom R C 𝒞} {k : ℕ}
    (hk : ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      f.app A' x' - f'.app A' x' ∈ vxGe R V k A')
    (hu : ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      unitCoeffL R V A' (f.app A' x' - f'.app A' x') = 0) (x : C X) :
    euler R V X (f.app X x - f'.app X x) ∈ vxGe R V (k + 1) X := by
  rw [euler, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun S _ => ?_
  -- the decompositions of the two values
  have hf : ∀ g : GrCooperadHom R C 𝒞,
      GrCooperad.decomp (R := R) (C := 𝒞) none
        (GrOperad.map (R := R) (splitEquiv S).symm (g.app X x))
      = TensorProduct.map (g.app (SOut S)) (g.app (SIn S))
          (GrCooperad.decomp (R := R) (C := C) none
            (SymSpecies.map (R := R) (splitEquiv S).symm x)) := fun g => by
    rw [← symMap_eq, ← g.app_map]
    exact LinearMap.congr_fun (g.decomp_app (A := SOut S) (B := SIn S) none) _
  generalize hT : GrCooperad.decomp (R := R) (C := C) (A := SOut S) (B := SIn S) none
    (SymSpecies.map (R := R) (splitEquiv S).symm x) = t at hf
  -- the parts without unit component
  have hd : ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (a : C A'),
      (secC R V A' ∘ₗ f.app A' - secC R V A' ∘ₗ f'.app A') a ∈ vxGe R V k A' := fun A' _ _ a => by
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_sub,
      secC_of_unitCoeff (hu A' a)]
    exact hk A' a
  have h1 : ∀ (g : GrCooperadHom R C 𝒞) (A' : Type) [Fintype A'] [DecidableEq A'] (a : C A'),
      (secC R V A' ∘ₗ g.app A') a ∈ vxGe R V 1 A' := fun g A' _ _ a =>
    mem_vxGe_one_of_unitCoeffL (unitCoeffL_secC _)
  have e : TensorProduct.map (secC R V (SOut S)) (secC R V (SIn S))
      (GrCooperad.decomp (R := R) (C := 𝒞) none
        (GrOperad.map (R := R) (splitEquiv S).symm (f.app X x - f'.app X x)))
      = TensorProduct.map (secC R V (SOut S) ∘ₗ f.app (SOut S)
            - secC R V (SOut S) ∘ₗ f'.app (SOut S)) (secC R V (SIn S) ∘ₗ f.app (SIn S)) t
        + TensorProduct.map (secC R V (SOut S) ∘ₗ f'.app (SOut S))
            (secC R V (SIn S) ∘ₗ f.app (SIn S) - secC R V (SIn S) ∘ₗ f'.app (SIn S)) t := by
    rw [map_sub, map_sub, hf f, hf f', map_sub, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, ← TensorProduct.map_comp]
    exact map_sub_map _ _ _ _ t
  rw [eulerAt, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, e, map_add, map_add]
  refine add_mem (map_mem_vxGe _ (mu_map_mem_vxGe none _ _ (hd _) (h1 f _) t)) ?_
  have h2 := map_mem_vxGe (splitEquiv S) (mu_map_mem_vxGe none _ _ (h1 f' (SOut S)) (hd (SIn S)) t)
  rwa [Nat.add_comm] at h2

/-- **Morphisms into the cut cooperad are determined by their cogenerator parts, for any
species**: two morphisms of graded cooperads into the cut cooperad on a graded linear species,
possibly with elements without inputs, with the same coefficient of the generators, agree, over a
`ℚ`-algebra. The cooperad need not be conilpotent. -/
theorem app_eq_of_genCoef_any [Algebra ℚ R] {f f' : GrCooperadHom R C 𝒞}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      genCoef R V A (f.app A x) = genCoef R V A (f'.app A x))
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) : f.app A x = f'.app A x := by
  have hu : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      unitCoeffL R V A (f.app A x - f'.app A x) = 0 := by
    intro A _ _ x
    by_cases hA : Nonempty (Unit ≃ A)
    · obtain ⟨e⟩ := hA
      have hx : x = SymSpecies.map (R := R) e (SymSpecies.map (R := R) e.symm x) :=
        (SymSpecies.map_map_symm e x).symm
      rw [hx, f.app_map, f'.app_map, ← map_sub]
      show unitCoeffL R V A (GrOperad.map (R := R) e _) = 0
      rw [unitCoeffL_map, ← counit_eq_unitCoeffL, map_sub,
        ← LinearMap.comp_apply (GrCooperad.counit (R := R) (C := 𝒞)),
        ← LinearMap.comp_apply (GrCooperad.counit (R := R) (C := 𝒞)), f.counit_app,
        f'.counit_app, sub_self]
    · exact unitCoeffL_eq_zero (not_nonempty_iff.1 hA) _
  have key : ∀ k, 2 ≤ k → ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      f.app A' x' - f'.app A' x' ∈ vxGe R V k A' := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro A' _ _ x'
      have := sub_ι_genCoef_mem (hu A' x')
      rwa [map_sub, h, sub_self, map_zero, sub_zero] at this
    | succ k hk ih =>
      exact fun A' _ _ x' => mem_vxGe_succ_of_euler hk (ih A' x') (euler_sub_mem ih hu x')
  exact sub_eq_zero.1 (eq_zero_of_forall_mem_vxGe fun p =>
    vxGe_anti (le_max_left p 2) (key _ (le_max_right p 2) A x))

/-! ## The universal property -/

variable [GrCooperad.Coaug R C] [Algebra ℚ R]

local notation "𝟙" => GrCooperad.Coaug.one (R := R) (C := C)

/-- **The universal property of the cut cooperad on any graded linear species**: over a
`ℚ`-algebra, for a graded linear species `V`, possibly with elements without inputs, and a
conilpotent coaugmented graded cooperad `C` such that in each arity the reduced cooperations or
the elements of `V` form a projective module, the coaugmented morphisms of graded cooperads
`C → T^c(V)` are the morphisms of graded linear species `C̄ → V` from the reduced part. -/
noncomputable def cofreeHomEquivConilAny (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (V (Fin k))) :
    {f : GrCooperadHom R C (FreeGrL R V) //
      f.app Unit 𝟙 = GrCooperad.Coaug.one (R := R) (C := FreeGrL R V)} ≃
    GrSpeciesHom R (GrCooperad.Red R C) V where
  toFun f := redLift ((genCoefHom R V).comp f.1.toGrSpeciesHom)
    fun _ _ _ => genCoef_app_unitSpan f.1 f.2
  invFun ψ := ⟨liftConil hC ψ hproj, liftConil_app_one hC ψ hproj⟩
  left_inv f := Subtype.ext (GrCooperadHom.ext (app_eq_of_genCoef_any
    fun _ _ _ x => genCoef_liftConil hC _ hproj x))
  right_inv ψ := GrSpeciesHom.ext fun A _ _ X => by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective A X
    exact genCoef_liftConil hC ψ hproj x

/-- **The cofree property of the cut cooperad on any graded linear species**: on a conilpotent
coaugmented graded cooperad, every morphism of graded linear species into `V` killing the
coaugmentation lifts uniquely to a morphism of graded cooperads into `T^c(V)`, over a
`ℚ`-algebra, when in each arity the reduced cooperations or the elements of `V` form a projective
module. -/
theorem existsUnique_liftConilAny (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (V (Fin k))) {φ : GrSpeciesHom R C V}
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A],
      GrCooperad.unitSpan R C A ≤ LinearMap.ker (φ.app A)) :
    ∃! f : GrCooperadHom R C (FreeGrL R V), ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      genCoef R V A (f.app A x) = φ.app A x :=
  ⟨liftConil hC (redLift φ hφ) hproj, fun _ _ _ x => genCoef_liftConil hC (redLift φ hφ) hproj x,
    fun _ hf => GrCooperadHom.ext (app_eq_of_genCoef_any fun A _ _ x =>
      (hf A x).trans (genCoef_liftConil hC (redLift φ hφ) hproj x).symm)⟩

end FreeGrL

end Operad
