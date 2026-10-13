/-
# The coefficient of the generators in a free graded operad

The free graded operad `T(V)` on a graded linear species contains `V` through its generators:
**the coefficient of the generators** `T(V)(A) → V A` (`FreeGrL.genCoef`) reads the decoration of
a tree with one vertex, relabelled along the order of its leaves, and vanishes on the other trees.
It kills the linearity relations, which are combinations of trees with one vertex, and the trees
without vertices are a complement of an ideal: the elements without unit component killed by it
form an ideal. So **the generators embed**: `genCoef ∘ ι = 1` (`FreeGrL.genCoef_ι`,
`FreeGrL.ι_injective`), commuting with the relabellings (`FreeGrL.genCoef_map`).
-/
import Operad.FreeGrArity

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

namespace FreeGrL

/-! ## On planar trees -/

variable (R V) in
/-- The decoration of a tree with one vertex with `n` inputs, zero otherwise. -/
noncomputable def coefT : Tree (GrGen R V) → (n : ℕ) → V (Fin n)
  | .leaf, _ => 0
  | .node (k := k) g fo, n =>
      if h : k = n ∧ (Tree.node g fo).weight = 1 then
        SymSpecies.map (R := R) (finCongr h.1) g.1.1 else 0

lemma coefT_of_weight_ne {t : Tree (GrGen R V)} (ht : t.weight ≠ 1) (n : ℕ) :
    coefT R V t n = 0 := by
  cases t with
  | leaf => rfl
  | node g fo => exact dif_neg fun h => ht h.2

lemma coefT_congr (t : Tree (GrGen R V)) {n n' : ℕ} (h : n = n') :
    coefT R V t n' = SymSpecies.map (R := R) (finCongr h) (coefT R V t n) := by
  subst h
  rw [show finCongr (rfl : n = n) = Equiv.refl _ from Equiv.ext fun _ => rfl,
    SymSpecies.map_refl]

lemma coefT_corolla {k : ℕ} (g : GrGen R V k) :
    coefT R V (Tree.node g (TreeOfArity.leaves k)) k = g.1.1 := by
  have hw : (Tree.node g (TreeOfArity.leaves k)).weight = 1 := by
    rw [Tree.weight_node, weightF_leaves]
  show (if h : k = k ∧ (Tree.node g (TreeOfArity.leaves k)).weight = 1 then
      SymSpecies.map (R := R) (finCongr h.1) g.1.1 else 0) = g.1.1
  rw [dif_pos ⟨rfl, hw⟩, show finCongr (rfl : k = k) = Equiv.refl _ from Equiv.ext fun _ => rfl,
    SymSpecies.map_refl]

variable (R V) in
/-- The decoration of a labelled tree with one vertex, relabelled along the order of its
leaves. -/
noncomputable def coefReg {A : Type} [Fintype A] [DecidableEq A]
    (x : Reg (TreeOfArity (GrGen R V)) A) : V A :=
  SymSpecies.map (R := R) x.1.toRank.symm (coefT R V (treeOf x) (Fintype.card A))

lemma coefReg_of_weight_ne {A : Type} [Fintype A] [DecidableEq A]
    {x : Reg (TreeOfArity (GrGen R V)) A} (hx : (treeOf x).weight ≠ 1) : coefReg R V x = 0 := by
  rw [coefReg, coefT_of_weight_ne hx, map_zero]

/-- The ranking of a relabelled order. -/
lemma toRank_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ' : A ≃ B) (L : LinOrd A) :
    (LinOrd.map σ' L).toRank = σ'.symm.trans (L.toRank.trans (finCongr (Fintype.card_congr σ'))) :=
  Equiv.ext fun b => Fin.ext (by
    rw [LinOrd.toRank_apply, LinOrd.rank_map]
    rfl)

lemma coefReg_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ' : A ≃ B) (x : Reg (TreeOfArity (GrGen R V)) A) :
    coefReg R V (SetOperad.map σ' x) = SymSpecies.map (R := R) σ' (coefReg R V x) := by
  rw [coefReg, coefReg, treeOf_map, map_fst, toRank_map,
    coefT_congr (treeOf x) (Fintype.card_congr σ'), ← SymSpecies.map_trans,
    ← SymSpecies.map_trans]
  congr 1

lemma coefReg_std_corolla {k : ℕ} (g : GrGen R V k) :
    coefReg R V (Reg.std (corolla g)) = g.1.1 := by
  have hk : k = Fintype.card (Fin k) := (Fintype.card_fin k).symm
  rw [coefReg, coefT_congr _ hk]
  have h1 : treeOf (Reg.std (corolla g) : Reg (TreeOfArity (GrGen R V)) (Fin k))
      = Tree.node g (TreeOfArity.leaves k) := rfl
  rw [h1, coefT_corolla, ← SymSpecies.map_trans]
  have h2 : (finCongr hk).trans
      (Reg.std (corolla g) : Reg (TreeOfArity (GrGen R V)) (Fin k)).1.toRank.symm
      = Equiv.refl _ := Equiv.ext fun i => by
    rw [Equiv.trans_apply, Equiv.symm_apply_eq]
    exact Fin.ext (by
      rw [LinOrd.toRank_apply]
      exact (LinOrd.rank_std k i).symm)
  rw [h2, SymSpecies.map_refl]

/-! ## On the free graded operad on the homogeneous elements -/

local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R V)) R
local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)

variable (R V) in
/-- The coefficient of the generators, on linear combinations of labelled trees. -/
noncomputable def genCoefF (A : Type) [Fintype A] [DecidableEq A] :
    FreeGr R (grGenPar R V) A →ₗ[R] V A :=
  Finsupp.linearCombination R (coefReg R V (A := A))

lemma genCoefF_bas {A : Type} [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity (GrGen R V)) A) :
    genCoefF R V A (𝔟 x) = coefReg R V x :=
  (Finsupp.linearCombination_single R _ _).trans (one_smul R _)

lemma genCoefF_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ' : A ≃ B) (y : FreeGr R (grGenPar R V) A) :
    genCoefF R V B (GrOperad.map (R := R) σ' y)
      = SymSpecies.map (R := R) σ' (genCoefF R V A y) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity (GrGen R V)))
    (genCoefF R V B ∘ₗ GrOperad.map (R := R) (P := FreeGr R (grGenPar R V)) σ')
    (SymSpecies.map (R := R) σ' ∘ₗ genCoefF R V A) (fun s => ?_) y
  · simpa using h
  show genCoefF R V B (GrOperad.map (R := R) σ' (𝔟 s))
    = SymSpecies.map (R := R) σ' (genCoefF R V A (𝔟 s))
  rw [SgnLin.map_bas, genCoefF_bas, genCoefF_bas, coefReg_map]

lemma coefReg_par {A : Type} [Fintype A] [DecidableEq A] (b : Bool)
    (x : Reg (TreeOfArity (GrGen R V)) A) :
    GrSpecies.par (R := R) b (coefReg R V x)
      = if Tree.tpar (grGenPar R V) (treeOf x) = b then coefReg R V x else 0 := by
  by_cases hw : (treeOf x).weight = 1
  · obtain ⟨k, g, hg⟩ := eq_corolla_of_weight hw
    have hk : k = Fintype.card A := by
      have := treeOf_arity x
      rw [hg, x.2.2] at this
      simpa using this
    have hc : coefReg R V x = SymSpecies.map (R := R) x.1.toRank.symm
        (SymSpecies.map (R := R) (finCongr hk) g.1.1) := by
      rw [coefReg, hg, coefT_congr _ hk, coefT_corolla]
    have ht : Tree.tpar (grGenPar R V) (treeOf x) = g.1.2 := by
      rw [hg]
      exact tpar_corolla' g
    have hgv : GrSpecies.par (R := R) b g.1.1 = if g.1.2 = b then g.1.1 else 0 := by
      conv_lhs => rw [← g.2]
      rw [GrSpecies.par_par]
      by_cases hb : g.1.2 = b
      · rw [if_pos hb.symm, if_pos hb, g.2]
      · rw [if_neg (Ne.symm hb), if_neg hb]
    rw [ht, hc, ← GrSpecies.map_par, ← GrSpecies.map_par, hgv]
    split_ifs
    · rfl
    · rw [map_zero, map_zero]
  · rw [coefReg_of_weight_ne hw, map_zero, ite_self]

lemma genCoefF_par {A : Type} [Fintype A] [DecidableEq A] (b : Bool)
    (y : FreeGr R (grGenPar R V) A) :
    genCoefF R V A (GrOperad.par (R := R) b y) = GrSpecies.par (R := R) b (genCoefF R V A y) := by
  have h := Lin.induction₁ (S := Reg (TreeOfArity (GrGen R V)))
    (genCoefF R V A ∘ₗ GrOperad.par (R := R) (P := FreeGr R (grGenPar R V)) b)
    (GrSpecies.par (R := R) b ∘ₗ genCoefF R V A) (fun s => ?_) y
  · simpa using h
  show genCoefF R V A (GrOperad.par (R := R) b (𝔟 s))
    = GrSpecies.par (R := R) b (genCoefF R V A (𝔟 s))
  rw [par_bas_eq, genCoefF_bas, coefReg_par]
  rcases eq_or_ne (Tree.tpar (grGenPar R V) (treeOf s)) b with hb | hb
  · rw [if_pos (show ((treeSgn (grGenPar R V)).app A s).tot = b from hb), if_pos hb,
      genCoefF_bas]
  · rw [if_neg (show ¬((treeSgn (grGenPar R V)).app A s).tot = b from hb), if_neg hb, map_zero]

/-- **A tree with two vertices has no generator coefficient.** -/
lemma genCoefF_comp_bas {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) {p : Reg (TreeOfArity (GrGen R V)) A} {q : Reg (TreeOfArity (GrGen R V)) B}
    (hp : (treeOf p).isLeaf = false) (hq : (treeOf q).isLeaf = false) :
    genCoefF R V _ (GrOperad.comp (R := R) i (𝔟 p) (𝔟 q)) = 0 := by
  have hw : (treeOf (SetOperad.comp i p q)).weight ≠ 1 := by
    rw [treeOf_comp, Tree.weight_graft _ _ _ (rank_lt_arity p i)]
    have := Tree.one_le_weight hp
    have := Tree.one_le_weight hq
    omega
  rw [comp_bas_eq, map_smul, genCoefF_bas, coefReg_of_weight_ne hw, smul_zero]

/-- A linear map killing the trees with vertices kills the elements without unit component. -/
lemma eq_zero_of_unitCoeff {A : Type} [Fintype A] [DecidableEq A] {M : Type*} [AddCommGroup M]
    [Module R M] (L : FreeGr R (grGenPar R V) A →ₗ[R] M)
    (hL : ∀ p : Reg (TreeOfArity (GrGen R V)) A, (treeOf p).isLeaf = false → L (𝔟 p) = 0)
    {x : Reg (TreeOfArity (GrGen R V)) A →₀ R} (hx : unitCoeff (grGenPar R V) R A x = 0) :
    L x = 0 := by
  have hxs : x = x.sum fun p c => c • 𝔟 p := by
    conv_lhs => rw [← Finsupp.sum_single x]
    exact Finsupp.sum_congr fun p _ => (Finsupp.smul_single_one p _).symm
  rw [hxs, map_finsuppSum]
  refine Finset.sum_eq_zero fun p hp => ?_
  by_cases hl : (treeOf p).isLeaf = true
  · have hcoef : unitCoeff (grGenPar R V) R A x = x p := by
      conv_lhs => rw [hxs]
      rw [map_finsuppSum, Finsupp.sum, Finset.sum_eq_single p (fun p' _ hne => by
          rw [map_smul, unitCoeff_bas, if_neg (fun h => hne (eq_of_isLeaf h hl)), smul_zero])
          (fun h => absurd hp h), map_smul, unitCoeff_bas, if_pos hl, smul_eq_mul, mul_one]
    exact absurd (hcoef.symm.trans hx) (Finsupp.mem_support_iff.1 hp)
  · show L (x p • 𝔟 p) = 0
    rw [map_smul, hL p (by simpa using hl), smul_zero]

variable (R V) in
/-- **The elements without unit component killed by the coefficient of the generators form an
ideal.** -/
noncomputable def genIdeal : GrOperadIdeal R (FreeGr R (grGenPar R V)) where
  sub A _ _ := LinearMap.ker (genCoefF R V A) ⊓ LinearMap.ker (unitCoeff (grGenPar R V) R A)
  par_mem b x hx := Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by
      rw [genCoefF_par, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).1, map_zero]),
    LinearMap.mem_ker.2 (by rw [unitCoeff_par, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).2,
      ite_self])⟩
  map_mem e x hx := Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by
      rw [genCoefF_map, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).1, map_zero]),
    LinearMap.mem_ker.2 (by rw [unitCoeff_map, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).2])⟩
  comp_mem_left {A B} _ _ _ _ i x y hx := by
    have hx1 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).1
    have hx2 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).2
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_,
      LinearMap.mem_ker.2 (by rw [unitCoeff_comp, hx2, zero_mul])⟩
    have h := Lin.induction₁ (S := Reg (TreeOfArity (GrGen R V)))
      (genCoefF R V _ ∘ₗ GrOperad.comp (R := R) (P := FreeGr R (grGenPar R V)) (B := B) i x) 0
      (fun q => ?_) y
    · simpa using h
    show genCoefF R V _ (GrOperad.comp (R := R) i x (𝔟 q)) = 0
    cases hq : (treeOf q).isLeaf with
    | true =>
      obtain ⟨E, hE⟩ := comp_bas_leaf i x hq
      rw [hE, genCoefF_map, hx1, map_zero]
    | false =>
      exact eq_zero_of_unitCoeff
        (genCoefF R V _ ∘ₗ (GrOperad.comp (R := R) (P := FreeGr R (grGenPar R V)) i).flip (𝔟 q))
        (fun p hp => genCoefF_comp_bas i hp hq) hx2
  comp_mem_right {A B} _ _ _ _ i x y hy := by
    have hy1 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hy).1
    have hy2 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hy).2
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_,
      LinearMap.mem_ker.2 (by rw [unitCoeff_comp, hy2, mul_zero])⟩
    have h := Lin.induction₁ (S := Reg (TreeOfArity (GrGen R V)))
      (genCoefF R V _ ∘ₗ (GrOperad.comp (R := R) (P := FreeGr R (grGenPar R V)) (B := B) i).flip y)
      0 (fun p => ?_) x
    · simpa using h
    show genCoefF R V _ (GrOperad.comp (R := R) i (𝔟 p) y) = 0
    cases hp : (treeOf p).isLeaf with
    | true =>
      obtain ⟨E, hE⟩ := comp_leaf_bas hp i y
      rw [hE, genCoefF_map, hy1, map_zero]
    | false =>
      exact eq_zero_of_unitCoeff (genCoefF R V _ ∘ₗ GrOperad.comp (R := R) i (𝔟 p))
        (fun q hq => genCoefF_comp_bas i hp hq) hy2

lemma genCoefF_lgen {n : ℕ} (v : V (Fin n)) (b : Bool) (h : GrSpecies.par (R := R) b v = v) :
    genCoefF R V (Fin n) (lgen v b h) = v :=
  (genCoefF_bas _).trans (coefReg_std_corolla _)

/-- **The linearity relations lie in the ideal.** -/
lemma span_le_genIdeal : 𝒥 ≤ genIdeal R V := by
  refine (GrOperadIdeal.span_le (I := genIdeal R V)).2 fun n x hx => ?_
  refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, LinearMap.mem_ker.2 (unitCoeff_of_linRel hx)⟩
  rcases hx with (⟨b, v, w, hv, hw, rfl⟩ | ⟨b, c, v, hv, rfl⟩) | ⟨b, σ', v, hv, rfl⟩
  · rw [map_sub, map_sub, genCoefF_lgen, genCoefF_lgen, genCoefF_lgen]
    abel
  · rw [map_sub, map_smul, genCoefF_lgen, genCoefF_lgen, sub_self]
  · rw [map_sub, genCoefF_map, genCoefF_lgen, genCoefF_lgen, sub_self]

/-! ## The coefficient of the generators -/

variable (R V) in
/-- **The coefficient of the generators** in the free graded operad on a graded linear species. -/
noncomputable def genCoef (A : Type) [Fintype A] [DecidableEq A] : FreeGrL R V A →ₗ[R] V A :=
  Submodule.liftQ _ (genCoefF R V A) fun _ hz => (Submodule.mem_inf.1 (span_le_genIdeal A hz)).1

lemma genCoef_proj {A : Type} [Fintype A] [DecidableEq A] (y : FreeGr R (grGenPar R V) A) :
    genCoef R V A ((𝒥).proj A y) = genCoefF R V A y := rfl

lemma genCoef_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ' : A ≃ B) (x : FreeGrL R V A) :
    genCoef R V B (GrOperad.map (R := R) σ' x) = SymSpecies.map (R := R) σ' (genCoef R V A x) := by
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective A x
  exact genCoefF_map σ' y

/-- **The coefficient of the generators of a generator is itself.** -/
theorem genCoef_ι {A : Type} [Fintype A] [DecidableEq A] (v : V A) :
    genCoef R V A ((ι R V).app A v) = v := by
  have hfin : ∀ (n : ℕ) (w : V (Fin n)), genCoef R V (Fin n) ((ι R V).app (Fin n) w) = w := by
    intro n w
    rw [ι_app_fin, map_add]
    exact (congrArg₂ (· + ·) (genCoefF_bas _ |>.trans (coefReg_std_corolla _))
      (genCoefF_bas _ |>.trans (coefReg_std_corolla _))).trans (GrSpecies.par_add w)
  rw [GrSpeciesHom.app_eq_chart (ι R V) (Fintype.equivFin A).symm]
  exact (genCoef_map _ _).trans ((congrArg _ (hfin _ _)).trans (SymSpecies.map_map_symm _ _))

/-- **The generators embed into the free graded operad.** -/
theorem ι_injective {A : Type} [Fintype A] [DecidableEq A] :
    Function.Injective ((ι R V).app A) :=
  Function.LeftInverse.injective (g := genCoef R V A) genCoef_ι

/-! ## The trees with one vertex -/

section OneVertex

variable {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V] in
/-- Composing with a relabelled unit is a relabelling. -/
lemma _root_.Operad.GrOperad.comp_map_one {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (i : A) (x : P A) (e : Unit ≃ B) :
    ∃ E : A ≃ Without A i ⊕ B,
      GrOperad.comp (R := R) i x (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := P)))
        = GrOperad.map (R := R) E x := by
  refine ⟨(rightUnitEquiv i).symm.trans (compEquiv (Equiv.refl A) e i), ?_⟩
  have h := GrOperad.map_comp (R := R) (P := P) (Equiv.refl A) e i x (GrOperad.one (R := R))
  rw [GrOperad.map_refl] at h
  refine h.symm.trans ?_
  have h1 : GrOperad.comp (R := R) i x (GrOperad.one (R := R) (P := P))
      = GrOperad.map (R := R) (rightUnitEquiv i).symm x := by
    conv_rhs => rw [← GrOperad.comp_one (R := R) i x]
    rw [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]
  rw [h1, ← GrOperad.map_trans]
  rfl

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V] in
/-- Composing into a relabelled unit is a relabelling. -/
lemma _root_.Operad.GrOperad.map_one_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (e : Unit ≃ A) (i : A) (y : P B) :
    ∃ E : B ≃ Without A i ⊕ B,
      GrOperad.comp (R := R) i (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := P))) y
        = GrOperad.map (R := R) E y := by
  obtain ⟨u, rfl⟩ := e.surjective i
  cases u
  refine ⟨(leftUnitEquiv B).symm.trans (compEquiv e (Equiv.refl B) ()), ?_⟩
  have h := GrOperad.map_comp (R := R) (P := P) e (Equiv.refl B) () (GrOperad.one (R := R)) y
  rw [GrOperad.map_refl] at h
  refine h.symm.trans ?_
  have h1 : GrOperad.comp (R := R) () (GrOperad.one (R := R) (P := P)) y
      = GrOperad.map (R := R) (leftUnitEquiv B).symm y := by
    conv_rhs => rw [← GrOperad.one_comp (R := R) y]
    rw [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]
  rw [h1, ← GrOperad.map_trans]

end OneVertex

variable (R V) in
/-- The span of the relabelled units. -/
noncomputable abbrev unitsL (A : Type) [Fintype A] [DecidableEq A] : Submodule R (FreeGrL R V A) :=
  Submodule.span R (Set.range fun e : Unit ≃ A =>
    GrOperad.map (R := R) e (GrOperad.one (R := R) (P := FreeGrL R V)))

lemma map_mem_unitsL {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ' : A ≃ B) {x : FreeGrL R V A} (hx : x ∈ unitsL R V A) :
    GrOperad.map (R := R) σ' x ∈ unitsL R V B := by
  refine Submodule.span_induction (p := fun x _ => GrOperad.map (R := R) σ' x ∈ unitsL R V B)
    ?_ (by beta_reduce; rw [map_zero]; exact zero_mem _)
    (fun x y _ _ hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
    (fun c x _ hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ c hx) hx
  rintro _ ⟨e, rfl⟩
  beta_reduce
  rw [← GrOperad.map_trans]
  exact Submodule.subset_span ⟨e.trans σ', rfl⟩

lemma unitsL_le_eig {a : GrSpEnd R V false} {A : Type} [Fintype A] [DecidableEq A] :
    unitsL R V A ≤ eig R V a 0 A :=
  Submodule.span_le.2 (by rintro _ ⟨e, rfl⟩; exact unit_mem_eig e)

/-- **The trees with one vertex are the generators**, over a `ℚ`-algebra. -/
theorem eq_ι_genCoef [Algebra ℚ R] {A : Type} [Fintype A] [DecidableEq A] {x : FreeGrL R V A}
    (hx : x ∈ eig R V (GrSpEnd.id R V) 1 A) : x = (ι R V).app A (genCoef R V A x) := by
  set N := GrSpEnd.id R V
  -- everything is units, generators, or of at least two vertices
  have hpos : ∀ (A : Type) [Fintype A] [DecidableEq A],
      LinearMap.range ((ι R V).app A) ⊔ (⨆ j : ℕ, eig R V N (j + 2) A)
        ≤ ⨆ j : ℕ, eig R V N (j + 1) A := fun A _ _ =>
    sup_le (by
      rintro _ ⟨v, rfl⟩
      exact Submodule.mem_iSup_of_mem 0 (mem_eig.2 (by
        rw [derSp_ι, Nat.cast_one, one_smul]
        rfl)))
      (iSup_le fun j => le_iSup_of_le (j + 1) le_rfl)
  have key := submodule_eq_top (R := R) (V := V)
    (fun A _ _ => unitsL R V A ⊔ (LinearMap.range ((ι R V).app A) ⊔ ⨆ j : ℕ, eig R V N (j + 2) A))
    (fun A _ _ e => Submodule.mem_sup_left (Submodule.subset_span ⟨e, rfl⟩))
    (fun n v => Submodule.mem_sup_right (Submodule.mem_sup_left ⟨v, rfl⟩))
    (fun A B _ _ _ _ σ' x hx => by
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨g, hg, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
      rw [map_add, map_add]
      refine add_mem (Submodule.mem_sup_left (map_mem_unitsL σ' hu))
        (Submodule.mem_sup_right (add_mem (Submodule.mem_sup_left ?_)
          (Submodule.mem_sup_right (map_mem_iSup (a := N) σ' (fun j => j + 2) hz))))
      obtain ⟨v, rfl⟩ := hg
      exact ⟨SymSpecies.map (R := R) σ' v, (ι R V).app_map σ' v⟩)
    (fun A B _ _ _ _ r x y hx hy => by
      -- relabelled units compose by relabelling
      have hS : ∀ (X : Type) [Fintype X] [DecidableEq X] (Y : Type) [Fintype Y] [DecidableEq Y]
          (E : X ≃ Y) (z : FreeGrL R V X),
          z ∈ unitsL R V X ⊔ (LinearMap.range ((ι R V).app X) ⊔ ⨆ j : ℕ, eig R V N (j + 2) X) →
          GrOperad.map (R := R) E z ∈ unitsL R V Y ⊔
            (LinearMap.range ((ι R V).app Y) ⊔ ⨆ j : ℕ, eig R V N (j + 2) Y) := by
        intro X _ _ Y _ _ E z₀ hz₀
        obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hz₀
        obtain ⟨g, hg, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
        rw [map_add, map_add]
        refine add_mem (Submodule.mem_sup_left (map_mem_unitsL E hu))
          (Submodule.mem_sup_right (add_mem (Submodule.mem_sup_left ?_)
            (Submodule.mem_sup_right (map_mem_iSup (a := N) E (fun j => j + 2) hz))))
        obtain ⟨v, rfl⟩ := hg
        exact ⟨SymSpecies.map (R := R) E v, (ι R V).app_map E v⟩
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      rw [LinearMap.map_add₂]
      refine add_mem ?_ ?_
      · -- a unit on the left
        refine Submodule.span_induction
          (p := fun u _ => GrOperad.comp (R := R) r u y ∈ unitsL R V _ ⊔
            (LinearMap.range ((ι R V).app _) ⊔ ⨆ j : ℕ, eig R V N (j + 2) _)) ?_
          (by beta_reduce; rw [LinearMap.map_zero₂]; exact zero_mem _)
          (fun a b _ _ ha hb => by
            beta_reduce at ha hb ⊢; rw [LinearMap.map_add₂]; exact add_mem ha hb)
          (fun c a _ ha => by
            beta_reduce at ha ⊢; rw [LinearMap.map_smul₂]; exact Submodule.smul_mem _ c ha) hu
        rintro _ ⟨e, rfl⟩
        obtain ⟨E, hE⟩ := GrOperad.map_one_comp (R := R) (P := FreeGrL R V) e r y
        beta_reduce
        rw [hE]
        exact hS _ _ E y hy
      · obtain ⟨u', hu', w', hw', rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add]
        refine add_mem ?_ ?_
        · -- a unit on the right
          refine Submodule.span_induction
            (p := fun u _ => GrOperad.comp (R := R) r w u ∈ unitsL R V _ ⊔
              (LinearMap.range ((ι R V).app _) ⊔ ⨆ j : ℕ, eig R V N (j + 2) _)) ?_
            (by beta_reduce; rw [map_zero]; exact zero_mem _)
            (fun a b _ _ ha hb => by beta_reduce at ha hb ⊢; rw [map_add]; exact add_mem ha hb)
            (fun c a _ ha => by beta_reduce at ha ⊢; rw [map_smul]; exact Submodule.smul_mem _ c ha)
            hu'
          rintro _ ⟨e, rfl⟩
          obtain ⟨E, hE⟩ := GrOperad.comp_map_one (R := R) (P := FreeGrL R V) r w e
          beta_reduce
          rw [hE]
          exact hS _ _ E w (Submodule.mem_sup_right hw)
        · -- two factors with vertices
          refine Submodule.mem_sup_right (Submodule.mem_sup_right
            (comp_mem_of_iSup r (fun i k x hx y hy => Submodule.mem_iSup_of_mem (i + k) ?_)
              (hpos A hw) (hpos B hw')))
          have := comp_mem_eig r hx hy
          rwa [show i + 1 + (k + 1) = i + k + 2 by omega] at this) A
  have hxt : x ∈ (⊤ : Submodule R (FreeGrL R V A)) := Submodule.mem_top
  rw [← key] at hxt
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hxt
  obtain ⟨g, ⟨v, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
  have hg1 : (ι R V).app A v ∈ eig R V N 1 A := mem_eig.2 (by
    rw [derSp_ι, Nat.cast_one, one_smul]
    rfl)
  have h0 : u + z ∈ eig R V N 1 A := by
    have := sub_mem hx hg1
    rwa [show u + ((ι R V).app A v + z) - (ι R V).app A v = u + z by abel] at this
  have h1 : u + z ∈ ⨆ (j : ℕ) (_ : j ≠ 1), eig R V N j A :=
    add_mem (le_iSup₂_of_le (f := fun (j : ℕ) (_ : j ≠ 1) => eig R V N j A) 0 (by omega)
      unitsL_le_eig hu)
      ((iSup_le fun j => le_iSup₂_of_le (f := fun (i : ℕ) (_ : i ≠ 1) => eig R V N i A) (j + 2)
        (by omega) le_rfl) hz)
  have huz := Submodule.disjoint_def.1 (iSupIndep_eigenspace_nat _ 1) _ h0 h1
  have : u + ((ι R V).app A v + z) = (ι R V).app A v := by
    rw [add_left_comm, huz, add_zero]
  rw [this, genCoef_ι]

end FreeGrL

end Operad
