/-
# The contraction identity of the cobar construction of a cut cooperad

For the cobar construction `ΩC` of the cut cooperad `C = FreeGrL R V`, with its differential `d`,
the bar differential `h` of the merge structure on its generators (`Cobar.hM`), and the even
derivation `E` counting the vertices of the trees decorating the generators (`Cobar.wtΩ`):
**`d h + h d = E - (1 - ε)`** (`Cobar.dh_hd`), `1 - ε` removing the unit component, when there are
no generators without inputs. On a generator it is the count of the edges of its tree
(`Cobar.hM_d_ιL_bas`), and on a composite the commutator of `d` and the merge is the composite of
the parts without unit component (`Cobar.xiM_eq`).
-/
import Operad.CobarHomotopy

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

/-! ## The weight derivation of a free graded operad on a graded linear species -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R V)) R

lemma isShift_ι : IsShift (ι R V).toSymSpeciesHom false := by
  intro A _ _ c v
  rw [Bool.xor_false]
  exact (ι R V).app_par c v

variable (R V) in
/-- **The weight derivation**: the even derivation fixing the generators, counting the vertices of
the trees. -/
noncomputable def wtD : GrDer (GrOperadHom.id R (FreeGrL R V)) false :=
  derOf (GrOperadHom.id R (FreeGrL R V)) (ι R V).toSymSpeciesHom isShift_ι

lemma wtD_ι (v : V A) : (wtD R V).app A ((ι R V).app A v) = (ι R V).app A v :=
  derOf_ι _ _ _ v

lemma wtD_unit (e : Unit ≃ A) :
    (wtD R V).app A (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := FreeGrL R V))) = 0 := by
  rw [GrDer.app_map, GrDer.app_one, map_zero]

/-- **The weight derivation on a tree** multiplies it by its number of vertices. -/
theorem wtD_proj_bas (x : Reg (TreeOfArity (GrGen R V)) A) :
    (wtD R V).app A ((𝒥).proj A (𝔟 x)) = ((treeOf x).weight : R) • (𝒥).proj A (𝔟 x) := by
  refine tree_induction (motive := fun A _ _ x =>
    (wtD R V).app A ((𝒥).proj A (𝔟 x)) = ((treeOf x).weight : R) • (𝒥).proj A (𝔟 x))
    ?_ ?_ ?_ A x
  · intro X _ _ x hl
    obtain ⟨e, he⟩ := proj_bas_leaf hl
    rw [he, wtD_unit, Tree.eq_leaf_of_isLeaf hl, Tree.weight_leaf, Nat.cast_zero, zero_smul]
  · intro X _ _ k g e
    have hw : (treeOf (SetOperad.map e (Reg.std (corolla g)))).weight = 1 := by
      show (Tree.node g (TreeOfArity.leaves k)).weight = 1
      rw [Tree.weight_node, weightF_leaves]
    rw [hw, Nat.cast_one, one_smul, proj_bas_map, proj_bas_corolla, GrDer.app_map]
    exact congrArg (GrOperad.map (R := R) e) (wtD_ι g.1.1)
  · intro X A B _ _ _ _ _ _ r p q e _ _ hp hq
    have hw : (treeOf (SetOperad.map e (SetOperad.comp r p q))).weight
        = (treeOf p).weight + (treeOf q).weight := by
      rw [treeOf_map, treeOf_comp, Tree.weight_graft _ _ _ (rank_lt_arity p r)]
    rw [hw, proj_bas_map, proj_bas_comp, GrDer.app_map, map_smul, GrDer.app_comp, hp,
      GrOperadHom.id_app, GrOperadHom.id_app, GrOperad.tw_false, hq, LinearMap.map_smul₂,
      map_smul (GrOperad.comp (R := R) r ((𝒥).proj A (𝔟 p))), ← add_smul, smul_comm, map_smul,
      Nat.cast_add]

/-- The relabellings of the linear species underlying the graded operad. -/
lemma symMap_eq (e : A ≃ B) (x : FreeGrL R V A) :
    SymSpecies.map (R := R) e x = GrOperad.map (R := R) e x := by
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective A x
  rfl

/-- The parity projections of the graded linear species underlying the graded operad. -/
lemma grPar_eq (c : Bool) (x : FreeGrL R V A) :
    GrSpecies.par (R := R) c x = GrOperad.par (R := R) c x := by
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective A x
  rfl

end FreeGrL

/-! ## Linear algebra for the contraction identity -/

section Helpers

variable {R : Type u} [CommRing R] {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The commutator `d h + h d` on a composite, from the Leibniz rules of `d` and `h`. -/
private lemma alg_kM (dM hM' tM : M →ₗ[R] M) (dN hN : N →ₗ[R] N) (dP hP : P →ₗ[R] P)
    (c m : M →ₗ[R] N →ₗ[R] P)
    (hcd : ∀ x y, dP (c x y) = c (dM x) y + c (tM x) (dN y))
    (hch : ∀ x y, hP (c x y) = c (hM' x) y + c (tM x) (hN y) + m x y)
    (hdt : ∀ x, dM (tM x) = -tM (dM x)) (hht : ∀ x, hM' (tM x) = -tM (hM' x))
    (htt : ∀ x, tM (tM x) = x) (x : M) (y : N) :
    dP (hP (c x y)) + hP (dP (c x y))
      = c (dM (hM' x) + hM' (dM x)) y + c x (dN (hN y) + hN (dN y))
        + (dP (m x y) + m (dM x) y + m (tM x) (dN y)) := by
  simp only [hch, hcd, map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply, hdt, hht, htt]
  abel

/-- The contraction identity on a composite, from those on the factors. -/
private lemma alg_ct (c : M →ₗ[R] N →ₗ[R] P) {x Kx Ex : M} {y Ky Ey : N} {Kxy Exy Sxy Xi : P}
    (hK : Kxy = c Kx y + c x Ky + Xi) (hx : Kx = Ex - x) (hy : Ky = Ey - y) (hXi : Xi = c x y)
    (hE : Exy = c Ex y + c x Ey) (hS : Sxy = c x y) : Kxy = Exy - Sxy := by
  rw [hK, hx, hy, hXi, hE, hS]
  simp only [map_sub, LinearMap.sub_apply]
  abel

private lemma alg_map {M' : Type*} [AddCommGroup M'] [Module R M'] (φ : M →ₗ[R] M')
    (K E S : M →ₗ[R] M) (K' E' S' : M' →ₗ[R] M') (hK : ∀ z, K' (φ z) = φ (K z))
    (hE : ∀ z, E' (φ z) = φ (E z)) (hS : ∀ z, S' (φ z) = φ (S z)) {z : M}
    (hz : K z = E z - S z) : K' (φ z) = E' (φ z) - S' (φ z) := by
  rw [hK, hE, hS, hz, map_sub]

private lemma alg_smul (K E S : M →ₗ[R] M) (a : R) {z : M} (hz : K z = E z - S z) :
    K (a • z) = E (a • z) - S (a • z) := by
  rw [map_smul, map_smul, map_smul, hz, smul_sub]

/-- Two linear maps after a linear map out of a free module agree as soon as they agree on the
basis elements. -/
private lemma lin_eq_of_single {α : Type*} (F G : M →ₗ[R] N) (f : (α →₀ R) →ₗ[R] M)
    (h : ∀ a, F (f (Finsupp.single a 1)) = G (f (Finsupp.single a 1))) (x : α →₀ R) :
    F (f x) = G (f x) :=
  LinearMap.congr_fun (Finsupp.lhom_ext' fun a => LinearMap.ext_ring (h a) :
    F.comp f = G.comp f) x

private lemma nsmul_pred {w : ℕ} (hw : 1 ≤ w) (z : M) : (w - 1) • z = (w : R) • z - z := by
  rw [Nat.cast_smul_eq_nsmul, eq_sub_iff_add_eq, ← succ_nsmul, Nat.sub_add_cancel hw]

end Helpers

/-! ## The weight derivation of the cobar construction -/

section Generators

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
  [DecidableEq D]

local notation "𝒞" => FreeGrL R V
local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)
local notation "𝒥Ω" => GrOperadIdeal.span R (grLinRel R (CobarGen R 𝒞))
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R V)) R
local notation "𝔅" => SgnLin.bas (treeSgn (grGenPar R (CobarGen R 𝒞))) R

namespace Cobar

/-- The weight derivation kills the coaugmentation. -/
lemma wtD_unitSpan {x : 𝒞 A} (hx : x ∈ GrCooperad.unitSpan R 𝒞 A) :
    (FreeGrL.wtD R V).app A x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨e, rfl⟩ := hy
    exact (congrArg ((FreeGrL.wtD R V).app A) (FreeGrL.symMap_eq e _)).trans
      (FreeGrL.wtD_unit e)
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

variable (R V) in
/-- The generator values of the weight derivation of the cobar construction:
`s⁻¹ c̄ ↦ s⁻¹ (E c)‾`. -/
noncomputable def genE (A : Type) [Fintype A] [DecidableEq A] :
    CobarGen R 𝒞 A →ₗ[R] CobarGr R 𝒞 A :=
  Submodule.liftQ (GrCooperad.unitSpan R 𝒞 A) (Cobar.ιL R 𝒞 A ∘ₗ (FreeGrL.wtD R V).app A)
    fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, wtD_unitSpan hx, map_zero]

lemma genE_proj (x : 𝒞 A) :
    genE R V A (GrCooperad.Red.proj R 𝒞 A x) = Cobar.ιL R 𝒞 A ((FreeGrL.wtD R V).app A x) :=
  rfl

variable (R V) in
/-- The generator values, as a morphism of linear species. -/
noncomputable def genESp : SymSpeciesHom R (CobarGen R 𝒞) (CobarGr R 𝒞) where
  app A _ _ := genE R V A
  app_map {A B} _ _ _ _ e v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := 𝒞) A v
    show genE R V B (GrCooperad.Red.proj R 𝒞 B (SymSpecies.map (R := R) e x))
      = GrOperad.map (R := R) e (genE R V A (GrCooperad.Red.proj R 𝒞 A x))
    exact (congrArg (fun z => Cobar.ιL R 𝒞 B ((FreeGrL.wtD R V).app B z))
      (FreeGrL.symMap_eq e x)).trans ((congrArg (Cobar.ιL R 𝒞 B)
        ((FreeGrL.wtD R V).app_map e x)).trans (ιL_map' e _))

lemma isShift_genE : FreeGrL.IsShift (genESp R V) false := by
  intro A _ _ c v
  obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := 𝒞) A v
  show genE R V A (GrCooperad.Red.proj R 𝒞 A (GrSpecies.par (R := R) (!c) x))
    = GrOperad.par (R := R) (xor c false) (genE R V A (GrCooperad.Red.proj R 𝒞 A x))
  have h1 := (congrArg (fun z => Cobar.ιL R 𝒞 A ((FreeGrL.wtD R V).app A z))
    (FreeGrL.grPar_eq (!c) x)).trans (congrArg (Cobar.ιL R 𝒞 A)
      ((FreeGrL.wtD R V).app_par (!c) x))
  refine h1.trans ?_
  rw [Bool.xor_false, Bool.xor_false, ← FreeGrL.grPar_eq, Cobar.ιL_par, Bool.not_not]
  rfl

variable (R V) in
/-- **The weight derivation of the cobar construction**: the even derivation counting the vertices
of the trees decorating the generators. -/
noncomputable def wtΩ : GrDer (GrOperadHom.id R (CobarGr R 𝒞)) false :=
  FreeGrL.derOf (GrOperadHom.id R (CobarGr R 𝒞)) (genESp R V) isShift_genE

lemma wtΩ_ιL (c : 𝒞 A) :
    (wtΩ R V).app A (Cobar.ιL R 𝒞 A c) = Cobar.ιL R 𝒞 A ((FreeGrL.wtD R V).app A c) := by
  rw [Cobar.ιL_apply, wtΩ, FreeGrL.derOf_ι]
  rfl

/-! ### The commutator of the cobar differential and the bar differential of the merge -/

/-- **The bar differential of the merge vanishes on the units.** -/
lemma hM_unit (e : Unit ≃ A) :
    hM R V A (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) = 0 := by
  have h1 : hM R V Unit (GrOperad.one (R := R) (P := CobarGr R 𝒞)) = 0 :=
    ((cobarMerge R V).d_proj
      (𝔅 (SetOperad.one : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) Unit))).trans
      ((congrArg ((𝒥Ω).proj Unit) (barD_bas_of_isLeaf (μ := (cobarMerge R V).fn)
        (gp := grGenPar R (CobarGen R 𝒞)) (R := R)
        (x := (SetOperad.one : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) Unit)) rfl)).trans
        (map_zero _))
  exact ((cobarMerge R V).map_d e _).symm.trans
    ((congrArg (GrOperad.map (R := R) e) h1).trans (map_zero _))

/-- **The bar differential of the merge is odd**: `h ((-1)^{|x|} x) = -(-1)^{|h x|} h x`. -/
lemma hM_tw (X : CobarGr R 𝒞 A) :
    hM R V A (GrOperad.tw (R := R) true X) = -GrOperad.tw (R := R) true (hM R V A X) := by
  have h1 : hM R V A (GrOperad.par (R := R) false X)
      = GrOperad.par (R := R) true (hM R V A X) := ((cobarMerge R V).par_d true X).symm
  have h2 : hM R V A (GrOperad.par (R := R) true X)
      = GrOperad.par (R := R) false (hM R V A X) := ((cobarMerge R V).par_d false X).symm
  exact (congrArg (hM R V A) (GrOperad.tw_true X)).trans ((map_sub (hM R V A) _ _).trans
    ((congrArg₂ (· - ·) h1 h2).trans ((neg_sub _ _).symm.trans
      (congrArg Neg.neg (GrOperad.tw_true (hM R V A X)).symm))))

variable (R V) in
/-- **The commutator of the cobar differential and the bar differential of the merge**:
`d h + h d`. -/
noncomputable def kM (A : Type) [Fintype A] [DecidableEq A] :
    CobarGr R 𝒞 A →ₗ[R] CobarGr R 𝒞 A :=
  (Cobar.d R 𝒞).app A ∘ₗ hM R V A + hM R V A ∘ₗ (Cobar.d R 𝒞).app A

lemma kM_apply (X : CobarGr R 𝒞 A) :
    kM R V A X = (Cobar.d R 𝒞).app A (hM R V A X) + hM R V A ((Cobar.d R 𝒞).app A X) := rfl

/-- **The commutator `d h + h d` on a composite**: the composites with the commutators on the
factors, plus the commutator of `d` and the merge. -/
lemma kM_comp (r : A) (P : CobarGr R 𝒞 A) (Q : CobarGr R 𝒞 B) :
    kM R V _ (GrOperad.comp (R := R) r P Q)
      = GrOperad.comp (R := R) r (kM R V A P) Q + GrOperad.comp (R := R) r P (kM R V B Q)
        + xiM R V r P Q :=
  alg_kM ((Cobar.d R 𝒞).app A) (hM R V A) (GrOperad.tw (R := R) true) ((Cobar.d R 𝒞).app B)
    (hM R V B) ((Cobar.d R 𝒞).app _) (hM R V _) (GrOperad.comp (R := R) r) (mM R V r)
    (d_comp r) ((cobarMerge R V).d_comp r) d_tw hM_tw (GrOperad.tw_tw true) P Q

/-- **The commutator `d h + h d` commutes with relabellings.** -/
lemma kM_map {A' : Type} [Fintype A'] [DecidableEq A'] (e : A ≃ A') (X : CobarGr R 𝒞 A) :
    kM R V A' (GrOperad.map (R := R) e X) = GrOperad.map (R := R) e (kM R V A X) := by
  have h1 : (Cobar.d R 𝒞).app A' (hM R V A' (GrOperad.map (R := R) e X))
      = GrOperad.map (R := R) e ((Cobar.d R 𝒞).app A (hM R V A X)) :=
    (congrArg ((Cobar.d R 𝒞).app A') ((cobarMerge R V).map_d e X).symm).trans
      ((Cobar.d R 𝒞).app_map e _)
  have h2 : hM R V A' ((Cobar.d R 𝒞).app A' (GrOperad.map (R := R) e X))
      = GrOperad.map (R := R) e (hM R V A ((Cobar.d R 𝒞).app A X)) :=
    (congrArg (hM R V A') ((Cobar.d R 𝒞).app_map e X)).trans ((cobarMerge R V).map_d e _).symm
  exact (congrArg₂ (· + ·) h1 h2).trans (map_add (GrOperad.map (R := R) e) _ _).symm

/-! ### The contraction identity -/

private lemma kM_unit (e : Unit ≃ A) :
    kM R V A (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞)))
      = (wtΩ R V).app A (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞)))
        - FreeGrL.secC R (CobarGen R 𝒞) A
            (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) := by
  have h1 : kM R V A (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) = 0 :=
    (congrArg₂ (· + ·) ((congrArg ((Cobar.d R 𝒞).app A) (hM_unit e)).trans (map_zero _))
      ((congrArg (hM R V A) (d_unit e)).trans (map_zero _))).trans (add_zero 0)
  have h2 : (wtΩ R V).app A
      (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) = 0 :=
    ((wtΩ R V).app_map e _).trans
      ((congrArg (GrOperad.map (R := R) e) (wtΩ R V).app_one).trans (map_zero _))
  have h3 : FreeGrL.secC R (CobarGen R 𝒞) A
      (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) = 0 :=
    FreeGrL.secC_unit e
  exact h1.trans ((congrArg₂ (· - ·) h2 h3).trans (sub_zero 0)).symm

private lemma kM_zero {Z : CobarGr R 𝒞 A} (hZ : Z = 0) :
    kM R V A Z = (wtΩ R V).app A Z - FreeGrL.secC R (CobarGen R 𝒞) A Z := by
  subst hZ
  exact (map_zero (kM R V A)).trans (((congrArg₂ (· - ·) (map_zero ((wtΩ R V).app A))
    (map_zero (FreeGrL.secC R (CobarGen R 𝒞) A))).trans (sub_zero 0)).symm)

/-- **The contraction identity on a generator**: `d h + h d = E - 1` there. -/
private lemma kM_ιL_bas (hV0 : ∀ v : V (Fin 0), v = 0) (t : Reg (TreeOfArity (GrGen R V)) A) :
    kM R V A (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)))
      = (wtΩ R V).app A (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)))
        - FreeGrL.secC R (CobarGen R 𝒞) A (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t))) := by
  by_cases hl : (treeOf t).isLeaf = true
  · exact kM_zero (ιL_bas_leaf hl)
  by_cases hn : (treeOf t).NoNull
  swap
  · exact kM_zero (ιL_bas_null hV0 hn)
  have hw : 1 ≤ (treeOf t).weight := Tree.one_le_weight (by simpa using hl)
  have h1 : kM R V A (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)))
      = ((treeOf t).weight - 1) • Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)) :=
    (congrArg₂ (· + ·) ((congrArg ((Cobar.d R 𝒞).app A) (hM_ιL _)).trans (map_zero _))
      (hM_d_ιL_bas t hn)).trans (zero_add _)
  have h2 : (wtΩ R V).app A (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)))
      = ((treeOf t).weight : R) • Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)) :=
    (wtΩ_ιL _).trans ((congrArg (Cobar.ιL R 𝒞 A) (FreeGrL.wtD_proj_bas t)).trans
      (map_smul _ _ _))
  have h3 : FreeGrL.secC R (CobarGen R 𝒞) A (Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)))
      = Cobar.ιL R 𝒞 A ((𝒥).proj A (𝔟 t)) :=
    FreeGrL.secC_of_unitCoeff (unitCoeffL_ιL _)
  rw [h1, h2, h3]
  exact nsmul_pred hw _

private lemma kM_ιL (hV0 : ∀ v : V (Fin 0), v = 0) (y : FreeGr R (grGenPar R V) A) :
    kM R V A (Cobar.ιL R 𝒞 A ((𝒥).proj A y))
      = (wtΩ R V).app A (Cobar.ιL R 𝒞 A ((𝒥).proj A y))
        - FreeGrL.secC R (CobarGen R 𝒞) A (Cobar.ιL R 𝒞 A ((𝒥).proj A y)) :=
  lin_eq_of_single (kM R V A) ((wtΩ R V).app A - FreeGrL.secC R (CobarGen R 𝒞) A)
    ((Cobar.ιL R 𝒞 A).comp ((𝒥).proj A)) (fun t => kM_ιL_bas hV0 t) y

private lemma kM_comp_ct (hV0 : ∀ v : V (Fin 0), v = 0) (r : A) {P : CobarGr R 𝒞 A}
    {Q : CobarGr R 𝒞 B} (hP0 : FreeGrL.unitCoeffL R (CobarGen R 𝒞) A P = 0)
    (hQ0 : FreeGrL.unitCoeffL R (CobarGen R 𝒞) B Q = 0)
    (hP : kM R V A P = (wtΩ R V).app A P - FreeGrL.secC R (CobarGen R 𝒞) A P)
    (hQ : kM R V B Q = (wtΩ R V).app B Q - FreeGrL.secC R (CobarGen R 𝒞) B Q) :
    kM R V _ (GrOperad.comp (R := R) r P Q)
      = (wtΩ R V).app _ (GrOperad.comp (R := R) r P Q)
        - FreeGrL.secC R (CobarGen R 𝒞) _ (GrOperad.comp (R := R) r P Q) := by
  have sP : FreeGrL.secC R (CobarGen R 𝒞) A P = P := FreeGrL.secC_of_unitCoeff hP0
  have sQ : FreeGrL.secC R (CobarGen R 𝒞) B Q = Q := FreeGrL.secC_of_unitCoeff hQ0
  have hE : (wtΩ R V).app _ (GrOperad.comp (R := R) r P Q)
      = GrOperad.comp (R := R) r ((wtΩ R V).app A P) Q
        + GrOperad.comp (R := R) r P ((wtΩ R V).app B Q) :=
    ((wtΩ R V).app_comp r P Q).trans (congrArg (fun z => GrOperad.comp (R := R) r
      ((wtΩ R V).app A P) Q + GrOperad.comp (R := R) r z ((wtΩ R V).app B Q))
        (GrOperad.tw_false P))
  exact alg_ct (GrOperad.comp (R := R) r) (kM_comp r P Q)
    (hP.trans (congrArg (fun z => (wtΩ R V).app A P - z) sP))
    (hQ.trans (congrArg (fun z => (wtΩ R V).app B Q - z) sQ))
    ((xiM_eq hV0 r P Q).trans (congrArg₂ (fun a b => GrOperad.comp (R := R) r a b) sP sQ))
    hE (FreeGrL.secC_comp hP0 Q)

private lemma kM_bas_leaf {x : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) A} (e : Unit ≃ A)
    (he : (𝒥Ω).proj A (𝔅 x) = GrOperad.map (R := R) e (GrOperad.one (R := R))) :
    kM R V A ((𝒥Ω).proj A (𝔅 x)) = (wtΩ R V).app A ((𝒥Ω).proj A (𝔅 x))
      - FreeGrL.secC R (CobarGen R 𝒞) A ((𝒥Ω).proj A (𝔅 x)) := by
  rw [he]
  exact kM_unit e

private lemma kM_bas_corolla (hV0 : ∀ v : V (Fin 0), v = 0) {k : ℕ}
    (g : GrGen R (CobarGen R 𝒞) k) (e : Fin k ≃ A) :
    kM R V A ((𝒥Ω).proj A (𝔅 (SetOperad.map e (Reg.std (corolla g)))))
      = (wtΩ R V).app A ((𝒥Ω).proj A (𝔅 (SetOperad.map e (Reg.std (corolla g)))))
        - FreeGrL.secC R (CobarGen R 𝒞) A
            ((𝒥Ω).proj A (𝔅 (SetOperad.map e (Reg.std (corolla g))))) := by
  obtain ⟨y, hy⟩ := exists_ιL_eq (R := R) (V := V) g.1.1
  have hZ : (𝒥Ω).proj A (𝔅 (SetOperad.map e (Reg.std (corolla g))))
      = GrOperad.map (R := R) e (Cobar.ιL R 𝒞 (Fin k) ((𝒥).proj (Fin k) y)) :=
    (FreeGrL.proj_bas_map e _).trans (congrArg (GrOperad.map (R := R) e)
      ((FreeGrL.proj_bas_corolla g).trans hy.symm))
  rw [hZ]
  exact alg_map (GrOperad.map (R := R) e) _ _ _ _ _ _ (kM_map e)
    (fun z => (wtΩ R V).app_map e z) (fun z => FreeGrL.secC_map e z) (kM_ιL hV0 y)

private lemma kM_bas_comp (hV0 : ∀ v : V (Fin 0), v = 0) {A₁ B₁ : Type} [Fintype A₁]
    [DecidableEq A₁] [Fintype B₁] [DecidableEq B₁] (r : A₁)
    (p : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) A₁)
    (q : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) B₁) (e : Without A₁ r ⊕ B₁ ≃ A)
    (hpl : (treeOf p).isLeaf = false) (hql : (treeOf q).isLeaf = false)
    (hp : kM R V A₁ ((𝒥Ω).proj A₁ (𝔅 p)) = (wtΩ R V).app A₁ ((𝒥Ω).proj A₁ (𝔅 p))
      - FreeGrL.secC R (CobarGen R 𝒞) A₁ ((𝒥Ω).proj A₁ (𝔅 p)))
    (hq : kM R V B₁ ((𝒥Ω).proj B₁ (𝔅 q)) = (wtΩ R V).app B₁ ((𝒥Ω).proj B₁ (𝔅 q))
      - FreeGrL.secC R (CobarGen R 𝒞) B₁ ((𝒥Ω).proj B₁ (𝔅 q))) :
    kM R V A ((𝒥Ω).proj A (𝔅 (SetOperad.map e (SetOperad.comp r p q))))
      = (wtΩ R V).app A ((𝒥Ω).proj A (𝔅 (SetOperad.map e (SetOperad.comp r p q))))
        - FreeGrL.secC R (CobarGen R 𝒞) A
            ((𝒥Ω).proj A (𝔅 (SetOperad.map e (SetOperad.comp r p q)))) := by
  have hX : (𝒥Ω).proj A (𝔅 (SetOperad.map e (SetOperad.comp r p q)))
      = GrOperad.map (R := R) e (σ R (cSgn (grGenPar R (CobarGen R 𝒞)) r p q) •
          GrOperad.comp (R := R) r ((𝒥Ω).proj A₁ (𝔅 p)) ((𝒥Ω).proj B₁ (𝔅 q))) :=
    (FreeGrL.proj_bas_map e _).trans (congrArg (GrOperad.map (R := R) e)
      (FreeGrL.proj_bas_comp r p q))
  rw [hX]
  exact alg_map (GrOperad.map (R := R) e) _ _ _ _ _ _ (kM_map e)
    (fun z => (wtΩ R V).app_map e z) (fun z => FreeGrL.secC_map e z)
    (alg_smul _ _ _ _ (kM_comp_ct hV0 r (FreeGrL.unitCoeffL_proj_bas hpl)
      (FreeGrL.unitCoeffL_proj_bas hql) hp hq))

/-- **The contraction identity on a tree.** -/
private theorem kM_bas (hV0 : ∀ v : V (Fin 0), v = 0)
    (x : Reg (TreeOfArity (GrGen R (CobarGen R 𝒞))) A) :
    kM R V A ((𝒥Ω).proj A (𝔅 x)) = (wtΩ R V).app A ((𝒥Ω).proj A (𝔅 x))
      - FreeGrL.secC R (CobarGen R 𝒞) A ((𝒥Ω).proj A (𝔅 x)) :=
  tree_induction (motive := fun A _ _ x => kM R V A ((𝒥Ω).proj A (𝔅 x))
      = (wtΩ R V).app A ((𝒥Ω).proj A (𝔅 x))
        - FreeGrL.secC R (CobarGen R 𝒞) A ((𝒥Ω).proj A (𝔅 x)))
    (fun _ _ _ _ hl => (FreeGrL.proj_bas_leaf hl).elim fun e he => kM_bas_leaf e he)
    (fun _ _ _ _ g e => kM_bas_corolla hV0 g e)
    (fun _ _ _ _ _ _ _ _ _ r p q e hpl hql hp hq => kM_bas_comp hV0 r p q e hpl hql hp hq) A x

/-- **The contraction identity**: `d h + h d = E - (1 - ε)` on the cobar construction of the cut
cooperad, `E` counting the vertices of the trees decorating the generators and `1 - ε` removing
the unit component, when there are no generators without inputs. -/
theorem dh_hd (hV0 : ∀ v : V (Fin 0), v = 0) (Y : CobarGr R 𝒞 A) :
    (Cobar.d R 𝒞).app A (hM R V A Y) + hM R V A ((Cobar.d R 𝒞).app A Y)
      = (wtΩ R V).app A Y - FreeGrL.secC R (CobarGen R 𝒞) A Y := by
  have hy := Function.surjInv_eq ((𝒥Ω).proj_surjective A) Y
  rw [← hy]
  exact lin_eq_of_single (kM R V A) ((wtΩ R V).app A - FreeGrL.secC R (CobarGen R 𝒞) A)
    ((𝒥Ω).proj A) (fun x => kM_bas hV0 x) _

end Cobar

end Generators

end Operad
