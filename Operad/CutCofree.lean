/-
# The universal property of the cut cooperad

Let `V` be a reduced graded linear species, without elements with at most one input, and `C` a
graded cooperad, over a `ℚ`-algebra `R`. **The morphisms of graded cooperads `C → T^c(V)` into the
cut cooperad `T^c(V) = FreeGrL R V` are the morphisms of graded linear species `C → V`**, by
composition with the coefficient of the generators, when the modules `C (Fin k)` are projective,
as over a field (`FreeGrL.cofreeHomEquiv`, `FreeGrL.existsUnique_lift`), and more generally when
in each arity `k ≥ 2` the module `C (Fin k)` or the module `V (Fin k)` is projective
(`FreeGrL.cofreeHomEquiv'`, `FreeGrL.existsUnique_lift'`). For a coaugmented `C` they are the
morphisms `C̄ → V` from the reduced part (`FreeGrL.cofreeHomEquivRed`,
`FreeGrL.cofreeHomEquivRed'`).

* **Uniqueness** (`FreeGrL.app_eq_of_genCoef₀`, for any `V` without elements without inputs and
  any `C`). The difference `δ = f - f'` of two morphisms with
  the same coefficient of the generators has no unit component and no trees with one vertex
  (`FreeGrL.sub_ι_genCoef_mem`), and `(ι ⋆ ι) ∘ δ = (ι δ) ⋆ (ι f) + (ι f') ⋆ (ι δ)`
  (`FreeGrL.star_sub_star_mem`), so if the values of `δ` have at least `k ≥ 2` vertices they have
  at least `k + 1` (`Cobar.mem_vxGe_succ`); an element of `T^c(V)` is a finite sum of trees
  (`FreeGrL.eq_zero_of_forall_mem_vxGe`).
* **Transposition.** A morphism of graded operads `Ψ` from a free graded operad on generators to
  the scalar-valued convolution operad `ConvOp R C (ScalarOp R)` gives each tree `t` the
  functional `c ↦ σ(C(n, 2)) Ψ(t)(c)` on the cooperations, `n` the number of odd vertices of `t`
  (`FreeGr.coefF`). The binomial sign makes up for the Koszul sign of the convolution product:
  the coefficient of a composite is the pairing of the coefficients with the decomposition, with
  the sign of the composite (`FreeGr.coefF_comp`). When every cooperation has finitely many trees
  with a nonzero coefficient, `c ↦ ∑ₜ coefF t c · t` is a morphism of graded cooperads into the
  free graded operad (`FreeGr.ofCoef`).
* **Existence.** A morphism `φ : C → V` lifts through the combinations of homogeneous
  generators, parity by parity, `C (Fin k)` or `V (Fin k)` being projective
  (`FreeGrL.exists_genLift`, `FreeGrL.exists_genLift_of`, `FreeGrL.liftLOf`).
  Weighting the generators with `k` inputs by `1 / k!` defines `Ψ` (`FreeGrL.liftOp`), whose
  coefficients are locally finite by induction on the number of inputs (`FreeGrL.coefFinite`,
  with the shapes of trees `FreeGr.shapeR`). Its image in the cut cooperad (`FreeGrL.lift`) has
  for trees with one vertex the corollas `e · g`, whose values add up to `e · φ(e⁻¹ c) / k!` for
  each of the `k!` numberings `e` of the inputs, that is to `φ(c)` (`FreeGrL.genCoef_lift`).

Conilpotence of `C` is not needed: `V` being reduced, the trees with `|A|` inputs have fewer than
`|A|` vertices. Species with elements of one input, over a conilpotent `C`, are treated in
`Operad/CutCofreeConil.lean`. Existence with neither side projective is open: the transposition
detects a cooperation only through scalar functionals, and over a general `ℚ`-algebra a module
`C (Fin k)` may have no nonzero functional while mapping nontrivially to `V`.
-/
import Operad.KoszulBar
import Operad.FreeGrRoot

universe u v w

namespace Operad

open Sym GerBV TreeOfArity FreeGr FreeReg
open scoped TensorProduct

/-! ## The scalar operad -/

set_option linter.unusedVariables false in
/-- **The scalar operad**: the scalars in every arity, even, composed by multiplication. -/
@[nolint unusedArguments]
def ScalarOp (R : Type u) [CommRing R] (A : Type) [Fintype A] [DecidableEq A] : Type u := R

namespace ScalarOp

variable {R : Type u} [CommRing R]

instance (A : Type) [Fintype A] [DecidableEq A] : CommRing (ScalarOp R A) :=
  inferInstanceAs (CommRing R)

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (ScalarOp R A) :=
  inferInstanceAs (Module R R)

/-- An element of the scalar operad, as a scalar. -/
def val {A : Type} [Fintype A] [DecidableEq A] (x : ScalarOp R A) : R := x

/-- A scalar, in the scalar operad. -/
def of (A : Type) [Fintype A] [DecidableEq A] : R ≃ₗ[R] ScalarOp R A := LinearEquiv.refl R R

/-- The parity projections: everything is even. -/
def parS (A : Type) [Fintype A] [DecidableEq A] (b : Bool) : ScalarOp R A →ₗ[R] ScalarOp R A :=
  if b then 0 else LinearMap.id

lemma parS_apply {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (x : ScalarOp R A) :
    parS A b x = if b then 0 else x := by
  cases b <;> rfl

/-- **The scalar operad is a graded operad.** -/
instance instGrOperad : GrOperad R (ScalarOp R) where
  par b := parS _ b
  par_add x := by simp [parS_apply]
  par_par b b' x := by cases b <;> cases b' <;> simp [parS_apply]
  map _ := LinearMap.id
  map_refl _ := rfl
  map_trans _ _ _ := rfl
  map_par _ _ _ := rfl
  one := (1 : R)
  par_one := rfl
  comp _ := LinearMap.mul R R
  comp_par _ p q x y := by
    cases p <;> cases q <;> simp [parS_apply]
  map_comp _ _ _ _ _ := rfl
  comp_one _ x := mul_one (val x)
  one_comp y := one_mul (val y)
  comp_assoc_seq _ _ x y z := mul_assoc (val x) (val y) (val z)
  comp_assoc_par _ x q r y z hy hz := by
    show val x * val y * val z = σ R (q && r) * (val x * val z * val y)
    cases q <;> cases r
    · simp [mul_right_comm]
    · simp [mul_right_comm]
    · simp [mul_right_comm]
    · rw [← hy]
      simp only [parS_apply, if_true]
      show val x * 0 * val z = σ R (true && true) * (val x * val z * 0)
      ring

@[simp] lemma par_apply {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (x : ScalarOp R A) :
    GrOperad.par (R := R) b x = if b then 0 else x :=
  parS_apply b x

@[simp] lemma map_apply {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (x : ScalarOp R A) : val (GrOperad.map (R := R) e x) = val x := rfl

lemma comp_apply {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) (x : ScalarOp R A) (y : ScalarOp R B) :
    val (GrOperad.comp (R := R) i x y) = val x * val y := rfl

lemma one_eq : val (GrOperad.one (R := R) (P := ScalarOp R)) = 1 := rfl

lemma tw_apply {A : Type} [Fintype A] [DecidableEq A] (e : Bool) (x : ScalarOp R A) :
    GrOperad.tw (R := R) e x = x := by
  rw [GrOperad.tw_apply]
  simp

end ScalarOp

namespace GrCooperadHom

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {D : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (D A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (D A)] [GrCooperad R D]

/-- **Morphisms of graded cooperads agree when their components do.** -/
@[ext] lemma ext {f g : GrCooperadHom R C D}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), f.app A x = g.app A x) : f = g := by
  obtain ⟨f', _, _⟩ := f
  obtain ⟨g', _, _⟩ := g
  have : f' = g' := GrSpeciesHom.ext h
  subst this
  rfl

end GrCooperadHom

/-! ## The binomial sign of a tree -/

lemma choose_two_add (a : ℕ) : ∀ b : ℕ, (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b
  | 0 => by simp
  | b + 1 => by
    rw [← add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, choose_two_add a b,
      Nat.choose_succ_succ, Nat.choose_one_right]
    ring

namespace FreeGr

variable {T : ℕ → Type v} (gp : ∀ k, T k → Bool)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The number of odd vertices** of a tree. -/
def oddCnt (x : Reg (TreeOfArity T) A) : ℕ := cntR (fun k e => if gp k e then 1 else 0) x

/-- **The parity of a tree is the parity of its number of odd vertices.** -/
lemma tot_eq_bodd (x : Reg (TreeOfArity T) A) :
    ((treeSgn gp).app A x).tot = (oddCnt gp x).bodd := by
  refine FreeReg.induction (P := fun A _ _ x => ((treeSgn gp).app A x).tot = (oddCnt gp x).bodd)
    ?_ ?_ ?_ ?_ x
  · intro A B _ _ _ _ e x hx
    rw [(treeSgn gp).app_map, SgnData.map_def, SgnData.map_tot, oddCnt, cntR_map]
    exact hx
  · beta_reduce
    rw [(treeSgn gp).app_one, SgnData.one_def, SgnData.one_tot, oddCnt, cntR_one]
    rfl
  · intro A B _ _ _ _ i x y hx hy
    rw [(treeSgn gp).app_comp, SgnData.comp_def, SgnData.comp_tot, oddCnt, cntR_comp,
      Nat.bodd_add, hx, hy]
    rfl
  · intro k e
    rw [treeSgn_tot, oddCnt, cntR_std]
    cases gp k e <;> rfl

variable (R : Type u) [CommRing R]

/-- **The binomial sign** of a tree: `σ(C(n, 2))` for `n` odd vertices. -/
def bsgn (x : Reg (TreeOfArity T) A) : R := σ R ((oddCnt gp x).choose 2).bodd

variable {gp R}

lemma bsgn_map (e : A ≃ B) (x : Reg (TreeOfArity T) A) :
    bsgn gp R (SetOperad.map e x) = bsgn gp R x := rfl

lemma bsgn_one : bsgn gp R (SetOperad.one : Reg (TreeOfArity T) Unit) = 1 := by
  rw [bsgn, oddCnt, cntR_one]
  rfl

lemma bsgn_mul_self (x : Reg (TreeOfArity T) A) : bsgn gp R x * bsgn gp R x = 1 :=
  σ_mul_self R _

/-- **The binomial sign is a cocycle for the Koszul sign of exchanging two trees.** -/
lemma bsgn_comp (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    bsgn gp R (SetOperad.comp i x y) = bsgn gp R x * bsgn gp R y *
      σ R (((treeSgn gp).app A x).tot && ((treeSgn gp).app B y).tot) := by
  rw [bsgn, oddCnt, cntR_comp, ← oddCnt, ← oddCnt, choose_two_add, Nat.bodd_add, Nat.bodd_add,
    σ_xor, σ_xor, Nat.bodd_mul, tot_eq_bodd, tot_eq_bodd]
  rfl

end FreeGr

/-! ## Coefficients of trees -/

namespace ConvOp

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- A homogeneous scalar-valued map vanishes off its parity. -/
lemma val_toLin_par {α : Bool} {f : ConvOp R C (ScalarOp R) A} (hf : IsParC α f) (b : Bool)
    (c : C A) :
    ScalarOp.val (toLin f (GrSpecies.par (R := R) b c))
      = if α = b then ScalarOp.val (toLin f c) else 0 := by
  rw [hf b c, ScalarOp.par_apply]
  cases α <;> cases b <;> rfl

/-- **The composite of scalar-valued maps is a pairing with the decomposition**, up to the Koszul
sign of the parities. -/
lemma val_toLin_compC {α β : Bool} (i : A) {f : ConvOp R C (ScalarOp R) A}
    {g : ConvOp R C (ScalarOp R) B} (hf : IsParC α f) (hg : IsParC β g)
    (c : C (Without A i ⊕ B)) :
    ScalarOp.val (toLin (compC i f g) c)
      = σ R (α && β) * SymCooperad.pair ((ScalarOp.of A).symm.toLinearMap ∘ₗ toLin f)
          ((ScalarOp.of B).symm.toLinearMap ∘ₗ toLin g) (GrCooperad.decomp (R := R) i c) := by
  rw [toLin_compC, LinearMap.comp_apply, LinearMap.comp_apply]
  induction GrCooperad.decomp (R := R) (C := C) (B := B) i c using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero, mul_zero]
    rfl
  | tmul x y =>
    rw [kap_tmul f hg, mu_tmul, ScalarOp.comp_apply, SymCooperad.pair_tmul,
      ← LinearMap.comp_apply (toLin f), toLin_comp_tw hf, LinearMap.smul_apply,
      LinearMap.comp_apply, ScalarOp.tw_apply, Bool.and_comm]
    show σ R (α && β) * ScalarOp.val (toLin f x) * ScalarOp.val (toLin g y) = _
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [mul_assoc]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add, mul_add, ← hx, ← hy]
    rfl

end ConvOp

namespace FreeGr

variable {R : Type u} [CommRing R] {T : ℕ → Type v} {gp : ∀ k, T k → Bool}
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  (Ψ : GrOperadHom R (FreeGr R gp) (ConvOp R C (ScalarOp R)))
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝔟" => SgnLin.bas (treeSgn gp) R

/-- **The coefficient of a tree** under a morphism into the scalar-valued convolution operad: the
functional `c ↦ σ(C(n, 2)) Ψ(t)(c)`, `n` the number of odd vertices of `t`. -/
noncomputable def coefF (x : Reg (TreeOfArity T) A) : Module.Dual R (C A) :=
  bsgn gp R x • ((ScalarOp.of A).symm.toLinearMap ∘ₗ ConvOp.toLin (Ψ.app A (𝔟 x)))

lemma coefF_apply (x : Reg (TreeOfArity T) A) (c : C A) :
    coefF Ψ x c = bsgn gp R x * ScalarOp.val (ConvOp.toLin (Ψ.app A (𝔟 x)) c) := rfl

/-- The image of a tree has the parity of the tree. -/
lemma isParC_app_bas (x : Reg (TreeOfArity T) A) :
    ConvOp.IsParC ((treeSgn gp).app A x).tot (Ψ.app A (𝔟 x)) :=
  ConvOp.parC_eq_self_iff.1 (by rw [← ConvOp.par_def, ← Ψ.app_par, SgnLin.par_bas])

/-- **A tree only sees the cooperations of its parity.** -/
lemma coefF_par (x : Reg (TreeOfArity T) A) (b : Bool) (c : C A) :
    coefF Ψ x (GrSpecies.par (R := R) b c)
      = if ((treeSgn gp).app A x).tot = b then coefF Ψ x c else 0 := by
  rw [coefF_apply, ConvOp.val_toLin_par (isParC_app_bas Ψ x)]
  split_ifs
  · rfl
  · exact mul_zero _

lemma coefF_map (e : A ≃ B) (x : Reg (TreeOfArity T) A) (c : C B) :
    coefF Ψ (SetOperad.map e x) c = coefF Ψ x (SymSpecies.map (R := R) e.symm c) := by
  rw [coefF_apply, coefF_apply, bsgn_map, ← SgnLin.map_bas, Ψ.app_map, ConvOp.map_def,
    ConvOp.mapC_apply, ScalarOp.map_apply]

lemma coefF_one (c : C Unit) :
    coefF Ψ (SetOperad.one : Reg (TreeOfArity T) Unit) c = GrCooperad.counit (R := R) c := by
  rw [coefF_apply, bsgn_one, one_mul]
  show ScalarOp.val (ConvOp.toLin (Ψ.app Unit (GrOperad.one (R := R))) c) = _
  rw [Ψ.app_one, ConvOp.one_def, ConvOp.oneC_apply]
  show GrCooperad.counit (R := R) c * 1 = _
  exact mul_one _

/-- **The coefficient of a composite is the pairing of the coefficients with the
decomposition**, with the sign of the composite. -/
lemma coefF_comp (i : A) (p : Reg (TreeOfArity T) A) (q : Reg (TreeOfArity T) B)
    (c : C (Without A i ⊕ B)) :
    coefF Ψ (SetOperad.comp i p q) c
      = σ R (SgnData.sgn i ((treeSgn gp).app A p) ((treeSgn gp).app B q)) *
          SymCooperad.pair (coefF Ψ p) (coefF Ψ q) (GrCooperad.decomp (R := R) i c) := by
  rw [coefF_apply, app_bas_comp, ConvOp.toLin_smul, LinearMap.smul_apply, ConvOp.comp_def]
  have hval : ScalarOp.val (σ R (SgnData.sgn i ((treeSgn gp).app A p) ((treeSgn gp).app B q)) •
      ConvOp.toLin (ConvOp.compC i (Ψ.app A (𝔟 p)) (Ψ.app B (𝔟 q))) c)
      = σ R (SgnData.sgn i ((treeSgn gp).app A p) ((treeSgn gp).app B q)) *
        ScalarOp.val (ConvOp.toLin (ConvOp.compC i (Ψ.app A (𝔟 p)) (Ψ.app B (𝔟 q))) c) := rfl
  rw [hval, ConvOp.val_toLin_compC i (isParC_app_bas Ψ p) (isParC_app_bas Ψ q), coefF, coefF,
    bsgn_comp]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have h := σ_mul_self R (((treeSgn gp).app A p).tot && ((treeSgn gp).app B q).tot)
  linear_combination (bsgn gp R p * bsgn gp R q *
    σ R (SgnData.sgn i ((treeSgn gp).app A p) ((treeSgn gp).app B q)) *
    SymCooperad.pair ((ScalarOp.of A).symm.toLinearMap ∘ₗ ConvOp.toLin (Ψ.app A (𝔟 p)))
      ((ScalarOp.of B).symm.toLinearMap ∘ₗ ConvOp.toLin (Ψ.app B (𝔟 q)))
      (GrCooperad.decomp (R := R) i c)) * h

/-- The coefficients are **locally finite** when every cooperation has finitely many trees with
nonzero coefficient. -/
def CoefFinite : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (c : C A),
    (Function.support fun x : Reg (TreeOfArity T) A => coefF Ψ x c).Finite

/-- The linear maps of the morphism with given locally finite coefficients. -/
noncomputable def ofCoefL (hΨ : CoefFinite Ψ) (A : Type) [Fintype A] [DecidableEq A] :
    C A →ₗ[R] FreeGr R gp A where
  toFun c := Finsupp.ofSupportFinite (fun x => coefF Ψ x c) (hΨ A c)
  map_add' c c' := Finsupp.ext fun x => by
    show coefF Ψ x (c + c') = (Finsupp.ofSupportFinite (fun x => coefF Ψ x c) (hΨ A c)
      + Finsupp.ofSupportFinite (fun x => coefF Ψ x c') (hΨ A c') :
        Reg (TreeOfArity T) A →₀ R) x
    rw [Finsupp.add_apply, Finsupp.ofSupportFinite_coe, Finsupp.ofSupportFinite_coe, map_add]
  map_smul' r c := Finsupp.ext fun x => by
    show coefF Ψ x (r • c) = (r • Finsupp.ofSupportFinite (fun x => coefF Ψ x c) (hΨ A c) :
        Reg (TreeOfArity T) A →₀ R) x
    rw [Finsupp.smul_apply, Finsupp.ofSupportFinite_coe, map_smul]

lemma ofCoefL_apply (hΨ : CoefFinite Ψ) (c : C A) (x : Reg (TreeOfArity T) A) :
    (show Reg (TreeOfArity T) A →₀ R from ofCoefL Ψ hΨ A c) x = coefF Ψ x c :=
  rfl

lemma lapply_comp_ofCoefL (hΨ : CoefFinite Ψ) (x : Reg (TreeOfArity T) A) :
    Finsupp.lapply x ∘ₗ ofCoefL Ψ hΨ A = coefF Ψ x :=
  LinearMap.ext fun _ => rfl

/-- **The morphism of graded cooperads with given locally finite coefficients**: a cooperation
`c` goes to `∑ₜ coefF t c · t`. -/
noncomputable def ofCoef (hΨ : CoefFinite Ψ) : GrCooperadHom R C (FreeGr R gp) where
  app A _ _ := ofCoefL Ψ hΨ A
  app_map {A B} _ _ _ _ e c := Finsupp.ext fun x => by
    show coefF Ψ x (SymSpecies.map (R := R) e c) = Lin.mapL R e (ofCoefL Ψ hΨ A c) x
    rw [Lin.mapL_apply, ofCoefL_apply, coefF_map, Equiv.symm_symm]
  app_par {A} _ _ b c := Finsupp.ext fun x => by
    show coefF Ψ x (GrSpecies.par (R := R) b c)
      = SgnLin.parT R (treeSgn gp) b (ofCoefL Ψ hΨ A c) x
    rw [SgnLin.parT_apply, ofCoefL_apply, coefF_par]
  counit_app := LinearMap.ext fun c => by
    show coefF Ψ SetOperad.one c = GrCooperad.counit (R := R) c
    exact coefF_one Ψ c
  decomp_app {A B} _ _ _ _ i := LinearMap.ext fun c =>
    (tens R (Reg (TreeOfArity T) A) (Reg (TreeOfArity T) B)).injective
      (Finsupp.ext fun ⟨p, q⟩ => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply]
        show tens R _ _ (SgnLin.decompT R (treeSgn gp) i (ofCoefL Ψ hΨ _ c)) (p, q)
          = tens R _ _ (TensorProduct.map (ofCoefL Ψ hΨ A) (ofCoefL Ψ hΨ B)
            (GrCooperad.decomp (R := R) i c)) (p, q)
        have h := LinearMap.congr_fun (SymCooperad.pair_map (R := R) (Finsupp.lapply p)
          (Finsupp.lapply q) (ofCoefL Ψ hΨ A) (ofCoefL Ψ hΨ B)) (GrCooperad.decomp (R := R) i c)
        rw [LinearMap.comp_apply, lapply_comp_ofCoefL, lapply_comp_ofCoefL] at h
        rw [SgnLin.decompT_apply, tens_apply_eq_pair]
        refine Eq.trans ?_ h.symm
        show _ * coefF Ψ (SetOperad.comp i p q) c = _
        rw [coefF_comp, ← mul_assoc, σ_mul_self, one_mul])

@[simp] lemma ofCoef_app (hΨ : CoefFinite Ψ) :
    (ofCoef Ψ hΨ).app A = ofCoefL Ψ hΨ A :=
  rfl

end FreeGr

/-! ## The shape of a labelled planar tree -/

namespace FreeGr

variable {T : ℕ → Type v} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The number of vertices** of a labelled planar tree. -/
abbrev vcnt (x : Reg (TreeOfArity T) A) : ℕ := cntR (fun _ _ => 1) x

lemma vcnt_map (e : A ≃ B) (x : Reg (TreeOfArity T) A) : vcnt (SetOperad.map e x) = vcnt x :=
  rfl

lemma vcnt_comp (i : A) (x : Reg (TreeOfArity T) A) (y : Reg (TreeOfArity T) B) :
    vcnt (SetOperad.comp i x y) = vcnt x + vcnt y :=
  cntR_comp _ i x y

lemma vcnt_one : vcnt (SetOperad.one : Reg (TreeOfArity T) Unit) = 0 :=
  rfl

lemma vcnt_std {k : ℕ} (e : T k) : vcnt (Reg.std (corolla e)) = 1 :=
  cntR_std _ e

/-- A tree without vertices is a relabelled unit. -/
lemma eq_map_one_of_vcnt {x : Reg (TreeOfArity T) A} (hx : vcnt x = 0) :
    ∃ e : Unit ≃ A, x = SetOperad.map e SetOperad.one := by
  refine eq_map_one_of_leaf x ?_
  cases h : treeOf x with
  | leaf => rfl
  | node e fo =>
    have : vcnt x = 1 + Forest.cntF (fun _ _ => 1) fo := by
      show Tree.cnt _ (treeOf x) = _
      rw [h, Tree.cnt_node]
    omega

/-- **The shapes of labelled planar trees**: a relabelled unit, a relabelled corolla, or a
relabelled composite of two trees with vertices. -/
def ShapeR (t : Reg (TreeOfArity T) A) : Prop :=
  (∃ e : Unit ≃ A, t = SetOperad.map e SetOperad.one) ∨
  (∃ (k : ℕ) (g : T k) (e : Fin k ≃ A), t = SetOperad.map e (Reg.std (corolla g))) ∨
  (∃ (a b : ℕ) (i : Fin a) (p : Reg (TreeOfArity T) (Fin a)) (q : Reg (TreeOfArity T) (Fin b))
    (e : Without (Fin a) i ⊕ Fin b ≃ A), vcnt p ≠ 0 ∧ vcnt q ≠ 0 ∧
      t = SetOperad.map e (SetOperad.comp i p q))

lemma ShapeR.map {t : Reg (TreeOfArity T) A} (h : ShapeR t) (E : A ≃ B) :
    ShapeR (SetOperad.map E t) := by
  rcases h with ⟨e, rfl⟩ | ⟨k, g, e, rfl⟩ | ⟨a, b, i, p, q, e, hp, hq, rfl⟩
  · exact Or.inl ⟨e.trans E, (SetOperad.map_trans _ _ _).symm⟩
  · exact Or.inr (Or.inl ⟨k, g, e.trans E, (SetOperad.map_trans _ _ _).symm⟩)
  · exact Or.inr (Or.inr ⟨a, b, i, p, q, e.trans E, hp, hq, (SetOperad.map_trans _ _ _).symm⟩)

/-- **Every labelled planar tree has a shape.** -/
theorem shapeR (t : Reg (TreeOfArity T) A) : ShapeR t := by
  refine FreeReg.induction (P := fun A _ _ t => ShapeR t) ?_ ?_ ?_ ?_ t
  · intro A B _ _ _ _ e x hx
    exact hx.map e
  · exact Or.inl ⟨Equiv.refl _, (SetOperad.map_refl _).symm⟩
  · intro A₁ B₁ _ _ _ _ i x y hx hy
    by_cases h1 : vcnt x = 0
    · obtain ⟨e₁, rfl⟩ := eq_map_one_of_vcnt h1
      obtain ⟨E, hE⟩ := SetOperad.comp_unit_left i e₁ y
      rw [hE]
      exact hy.map E
    by_cases h2 : vcnt y = 0
    · obtain ⟨e₂, rfl⟩ := eq_map_one_of_vcnt h2
      obtain ⟨E, hE⟩ := SetOperad.comp_unit_right i x e₂
      rw [hE]
      exact hx.map E
    let σ' := Fintype.equivFin A₁
    let τ := Fintype.equivFin B₁
    refine Or.inr (Or.inr ⟨_, _, σ' i, SetOperad.map σ' x, SetOperad.map τ y,
      (compEquiv σ' τ i).symm, h1, h2, ?_⟩)
    rw [← SetOperad.map_comp, SetOperad.map_symm_map]
  · intro k g
    exact Or.inr (Or.inl ⟨k, g, Equiv.refl _, (SetOperad.map_refl _).symm⟩)

end FreeGr

/-! ## Pairings of tensors with families of functionals -/

lemma SymCooperad.finite_support_pair_all {R : Type u} [CommRing R] {X Y : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] {PX PY : Type*}
    (F : PX → Module.Dual R X) (G : PY → Module.Dual R Y)
    (hF : ∀ x, (Function.support fun p => F p x).Finite)
    (hG : ∀ y, (Function.support fun q => G q y).Finite) (t : X ⊗[R] Y) :
    (Function.support fun pq : PX × PY => SymCooperad.pair (F pq.1) (G pq.2) t).Finite := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    refine ((hF x).prod (hG y)).subset fun pq hpq => ?_
    simp only [Function.mem_support, SymCooperad.pair_tmul] at hpq
    exact ⟨left_ne_zero_of_mul hpq, right_ne_zero_of_mul hpq⟩
  | add x y hx hy =>
    refine (hx.union hy).subset fun pq hpq => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
    exact hpq (by show SymCooperad.pair (F pq.1) (G pq.2) (x + y) = 0
                  rw [map_add, hc.1, hc.2, add_zero])

/-! ## Lifting to the homogeneous generators -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R V)) R

/-- **A lift of a morphism of graded linear species to the homogeneous generators**: linear maps
sending a cooperation with `k` inputs to a combination of generators of its parity whose value
is its image. -/
structure GenLift₀ (φ : GrSpeciesHom R C V) where
  /-- The lift in arity `k`. -/
  L (k : ℕ) : C (Fin k) →ₗ[R] (GrGen R V k →₀ R)
  lc (k : ℕ) (x : C (Fin k)) :
    Finsupp.linearCombination R (fun g : GrGen R V k => g.1.1) (L k x) = φ.app (Fin k) x
  par (k : ℕ) (b : Bool) (x : C (Fin k)) (g : GrGen R V k) :
    L k (GrSpecies.par (R := R) b x) g = if g.1.2 = b then L k x g else 0

/-- **A lift to the homogeneous generators vanishing for `k ≤ 1`**, as for a reduced graded
linear species. -/
structure GenLift (φ : GrSpeciesHom R C V) extends GenLift₀ φ where
  low (k : ℕ) : k ≤ 1 → L k = 0

variable (R) in
/-- The weight `1 / k!` of the generators with `k` inputs. -/
noncomputable def wk [Algebra ℚ R] (k : ℕ) : R := algebraMap ℚ R (k.factorial : ℚ)⁻¹

lemma factorial_mul_wk [Algebra ℚ R] (k : ℕ) : (k.factorial : R) * wk R k = 1 := by
  rw [wk, ← map_natCast (algebraMap ℚ R), ← map_mul, mul_inv_cancel₀ (by positivity), map_one]

variable [Algebra ℚ R] {φ : GrSpeciesHom R C V}

/-- The values on the generators: the coefficient of a generator in the lift, weighted by
`1 / k!`. -/
noncomputable def liftVal (ℓ : GenLift₀ φ) :
    FreeGr.GenVal R (grGenPar R V) (ConvOp R C (ScalarOp R)) :=
  ⟨fun k g => ConvOp.of ((ScalarOp.of (Fin k)).toLinearMap ∘ₗ
      (wk R k • (Finsupp.lapply g ∘ₗ ℓ.L k))), fun k g => by
    rw [ConvOp.par_def, ConvOp.parC_eq_self_iff]
    intro c x
    simp only [ConvOp.toLin_of, LinearMap.comp_apply, LinearMap.smul_apply,
      Finsupp.lapply_apply, ℓ.par, ScalarOp.par_apply]
    show _ = if xor c g.1.2 = true then 0 else _
    cases c <;> cases h : g.1.2 <;> simp⟩

/-- **The transposed morphism**: the morphism of graded operads from the free graded operad on
the homogeneous generators to the scalar-valued convolution operad given by the lift. -/
noncomputable def liftOp (ℓ : GenLift₀ φ) :
    GrOperadHom R (FreeGr R (grGenPar R V)) (ConvOp R C (ScalarOp R)) :=
  FreeGr.homEquiv.symm (liftVal ℓ)

lemma liftOp_gen (ℓ : GenLift₀ φ) {k : ℕ} (g : GrGen R V k) :
    (liftOp ℓ).app (Fin k) (𝔟 (Reg.std (corolla g))) = (liftVal ℓ).1 k g :=
  FreeGr.homEquiv_symm_gen _ g

omit [Algebra ℚ R] in
lemma bsgn_std {k : ℕ} (g : GrGen R V k) :
    FreeGr.bsgn (grGenPar R V) R (Reg.std (corolla g) : Reg (TreeOfArity (GrGen R V)) (Fin k))
      = 1 := by
  rw [FreeGr.bsgn, FreeGr.oddCnt, cntR_std]
  cases grGenPar R V k g <;> rfl

/-- **The coefficient of a corolla** is the weighted coefficient of the generator in the lift. -/
lemma coefF_std (ℓ : GenLift₀ φ) {k : ℕ} (g : GrGen R V k) (c : C (Fin k)) :
    FreeGr.coefF (liftOp ℓ) (Reg.std (corolla g)) c = wk R k * ℓ.L k c g := by
  rw [FreeGr.coefF_apply, bsgn_std, one_mul, liftOp_gen]
  rfl

/-- **A tree with a nonzero image has fewer vertices than inputs.** -/
lemma liftOp_bas (ℓ : GenLift φ) (x : Reg (TreeOfArity (GrGen R V)) A) :
    (liftOp ℓ.toGenLift₀).app A (𝔟 x) = 0 ∨ FreeGr.vcnt x + 1 ≤ Fintype.card A := by
  refine FreeReg.induction (P := fun A _ _ x => (liftOp ℓ.toGenLift₀).app A (𝔟 x) = 0 ∨
    FreeGr.vcnt x + 1 ≤ Fintype.card A) ?_ ?_ ?_ ?_ x
  · intro A B _ _ _ _ e x hx
    rcases hx with h | h
    · left
      rw [← SgnLin.map_bas, (liftOp ℓ.toGenLift₀).app_map, h, map_zero]
    · right
      rw [FreeGr.vcnt_map, ← Fintype.card_congr e]
      exact h
  · right
    rw [FreeGr.vcnt_one]
    rfl
  · intro A B _ _ _ _ i x y hx hy
    rcases hx with h | hx
    · left
      rw [app_bas_comp, h, map_zero, LinearMap.zero_apply, smul_zero]
    rcases hy with h | hy
    · left
      rw [app_bas_comp, h, map_zero, smul_zero]
    right
    have hA : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨i⟩
    rw [FreeGr.vcnt_comp, Fintype.card_sum, Reg.card_without]
    omega
  · intro k g
    by_cases hk : k ≤ 1
    · left
      rw [liftOp_gen]
      refine LinearMap.ext fun c => ?_
      show wk R k • ℓ.L k c g = 0
      rw [ℓ.low k hk, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply, smul_zero]
    · right
      rw [FreeGr.vcnt_std, Fintype.card_fin]
      omega

lemma coefF_ne_zero (ℓ : GenLift φ) {x : Reg (TreeOfArity (GrGen R V)) A} {c : C A}
    (h : FreeGr.coefF (liftOp ℓ.toGenLift₀) x c ≠ 0) :
    FreeGr.vcnt x + 1 ≤ Fintype.card A := by
  rcases liftOp_bas ℓ x with h0 | h0
  · refine absurd ?_ h
    rw [FreeGr.coefF_apply, h0]
    exact mul_zero _
  · exact h0

omit [Algebra ℚ R] in
lemma ne_zero_of_pair_ne_zero {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] {f : Module.Dual R X} {g : Module.Dual R Y} {t : X ⊗[R] Y}
    (h : SymCooperad.pair f g t ≠ 0) : f ≠ 0 ∧ g ≠ 0 := by
  refine ⟨fun hf => h ?_, fun hg => h ?_⟩
  · rw [hf, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
  · rw [hg, map_zero, LinearMap.zero_apply]

lemma two_le_of_coefF (ℓ : GenLift φ) {x : Reg (TreeOfArity (GrGen R V)) A}
    (hx : FreeGr.vcnt x ≠ 0) (h : FreeGr.coefF (liftOp ℓ.toGenLift₀) x ≠ 0) :
    2 ≤ Fintype.card A := by
  obtain ⟨c, hc⟩ : ∃ c, FreeGr.coefF (liftOp ℓ.toGenLift₀) x c ≠ 0 := by
    by_contra hn
    exact h (LinearMap.ext fun c => not_not.1 fun hc => hn ⟨c, hc⟩)
  have := coefF_ne_zero ℓ hc
  omega

/-- **The coefficients of the lift are locally finite**: a cooperation has finitely many trees
with nonzero coefficient, by induction on the number of inputs, a composite of two trees with
vertices and nonzero coefficients having more inputs than each. -/
theorem coefFinite (ℓ : GenLift φ) : FreeGr.CoefFinite (liftOp ℓ.toGenLift₀) := by
  suffices h : ∀ n (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = n → ∀ c : C A,
      (Function.support fun x : Reg (TreeOfArity (GrGen R V)) A =>
        FreeGr.coefF (liftOp ℓ.toGenLift₀) x c).Finite from fun A _ _ c => h _ A rfl c
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ hn c
  have hV : ∀ (a b : ℕ) (i : Fin a) (e : Without (Fin a) i ⊕ Fin b ≃ A),
      {pq : Reg (TreeOfArity (GrGen R V)) (Fin a) × Reg (TreeOfArity (GrGen R V)) (Fin b) |
        FreeGr.vcnt pq.1 ≠ 0 ∧ FreeGr.vcnt pq.2 ≠ 0 ∧
        SymCooperad.pair (FreeGr.coefF (liftOp ℓ.toGenLift₀) pq.1)
          (FreeGr.coefF (liftOp ℓ.toGenLift₀) pq.2)
          (GrCooperad.decomp (R := R) i (SymSpecies.map (R := R) e.symm c)) ≠ 0}.Finite := by
    intro a b i e
    have hcard := Fintype.card_congr e
    rw [Fintype.card_sum, Reg.card_without, Fintype.card_fin, Fintype.card_fin] at hcard
    have ha := i.pos
    by_cases hab : 2 ≤ a ∧ 2 ≤ b
    · refine (SymCooperad.finite_support_pair_all
        (fun p => FreeGr.coefF (liftOp ℓ.toGenLift₀) p)
        (fun q => FreeGr.coefF (liftOp ℓ.toGenLift₀) q) (fun x => ih a (by omega) (Fin a)
          (Fintype.card_fin a) x) (fun y => ih b (by omega) (Fin b) (Fintype.card_fin b) y)
        _).subset fun pq hpq => hpq.2.2
    · refine Set.finite_empty.subset fun pq ⟨hp, hq, hne⟩ => absurd ?_ hab
      obtain ⟨h1, h2⟩ := ne_zero_of_pair_ne_zero hne
      have := two_le_of_coefF ℓ hp h1
      have := two_le_of_coefF ℓ hq h2
      rw [Fintype.card_fin] at *
      exact ⟨by assumption, by assumption⟩
  let U₀ : Set (Reg (TreeOfArity (GrGen R V)) A) :=
    Set.range fun e : Unit ≃ A => SetOperad.map e SetOperad.one
  let U₁ : Set (Reg (TreeOfArity (GrGen R V)) A) := ⋃ e : Fin (Fintype.card A) ≃ A,
    (fun g => SetOperad.map e (Reg.std (corolla g))) ''
      ↑(ℓ.L (Fintype.card A) (SymSpecies.map (R := R) e.symm c)).support
  let U₂ : Set (Reg (TreeOfArity (GrGen R V)) A) := ⋃ a ∈ Finset.range (Fintype.card A + 2),
    ⋃ b ∈ Finset.range (Fintype.card A + 1), ⋃ i : Fin a, ⋃ e : Without (Fin a) i ⊕ Fin b ≃ A,
      (fun pq : Reg (TreeOfArity (GrGen R V)) (Fin a) × Reg (TreeOfArity (GrGen R V)) (Fin b) =>
        SetOperad.map e (SetOperad.comp i pq.1 pq.2)) ''
        {pq | FreeGr.vcnt pq.1 ≠ 0 ∧ FreeGr.vcnt pq.2 ≠ 0 ∧
          SymCooperad.pair (FreeGr.coefF (liftOp ℓ.toGenLift₀) pq.1)
            (FreeGr.coefF (liftOp ℓ.toGenLift₀) pq.2)
            (GrCooperad.decomp (R := R) i (SymSpecies.map (R := R) e.symm c)) ≠ 0}
  have h₀ : U₀.Finite := Set.finite_range _
  have h₁ : U₁.Finite := Set.finite_iUnion fun e => (Finset.finite_toSet _).image _
  have h₂ : U₂.Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun a _ =>
      Set.Finite.biUnion (Finset.finite_toSet _) fun b _ =>
        Set.finite_iUnion fun i => Set.finite_iUnion fun e => (hV _ _ i e).image _
  refine ((h₀.union h₁).union h₂).subset fun t ht => ?_
  rw [Function.mem_support] at ht
  rcases FreeGr.shapeR t with ⟨e, rfl⟩ | ⟨k, g, e, rfl⟩ | ⟨a, b, i, p, q, e, hp, hq, rfl⟩
  · exact Or.inl (Or.inl ⟨e, rfl⟩)
  · obtain rfl : k = Fintype.card A := by simpa using Fintype.card_congr e
    rw [FreeGr.coefF_map, coefF_std ℓ.toGenLift₀] at ht
    refine Or.inl (Or.inr (Set.mem_iUnion.2 ⟨e, g, Finsupp.mem_support_iff.2 ?_, rfl⟩))
    exact right_ne_zero_of_mul ht
  · have hcard := Fintype.card_congr e
    rw [Fintype.card_sum, Reg.card_without, Fintype.card_fin, Fintype.card_fin] at hcard
    have ha := i.pos
    rw [FreeGr.coefF_map, FreeGr.coefF_comp] at ht
    refine Or.inr (Set.mem_iUnion₂.2 ⟨a, ?_, Set.mem_iUnion₂.2 ⟨b, ?_, Set.mem_iUnion.2 ⟨i,
      Set.mem_iUnion.2 ⟨e, ⟨(p, q), ⟨hp, hq, right_ne_zero_of_mul ht⟩, rfl⟩⟩⟩⟩⟩)
    · exact Finset.mem_coe.2 (Finset.mem_range.2 (by omega))
    · exact Finset.mem_coe.2 (Finset.mem_range.2 (by omega))

/-- **The morphism of graded cooperads given by a lift with locally finite coefficients**: the
transposed morphism into the free graded operad on the homogeneous generators, followed by the
projection to the cut cooperad. -/
noncomputable def liftOf (ℓ : GenLift₀ φ) (hΨ : FreeGr.CoefFinite (liftOp ℓ)) :
    GrCooperadHom R C (FreeGrL R V) :=
  (projHom R V).comp (FreeGr.ofCoef (liftOp ℓ) hΨ)

/-- **The morphism of graded cooperads given by a lift**: the transposed morphism into the free
graded operad on the homogeneous generators, followed by the projection to the cut cooperad. -/
noncomputable def lift (ℓ : GenLift φ) : GrCooperadHom R C (FreeGrL R V) :=
  liftOf ℓ.toGenLift₀ (coefFinite ℓ)

omit [Algebra ℚ R] in
/-- Relabelled corollas determine their relabelling and their label. -/
lemma map_std_injective {k : ℕ} :
    Function.Injective (fun x : (Σ _ : Fin k ≃ A, GrGen R V k) =>
      (SetOperad.map x.1 (Reg.std (corolla x.2)) : Reg (TreeOfArity (GrGen R V)) A)) := by
  rintro ⟨e, g⟩ ⟨e', g'⟩ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg FreeGr.treeOf h
  simp only [FreeGr.map_fst, FreeGr.treeOf_map] at h1 h2
  have he : e = e' := by
    refine Equiv.symm_bijective.injective (Equiv.ext fun a => Fin.ext ?_)
    have hs : ∀ g'' : GrGen R V k,
        (Reg.std (corolla g'') : Reg (TreeOfArity (GrGen R V)) (Fin k)).1 = LinOrd.std k :=
      fun _ => rfl
    have := congrArg (fun L : LinOrd A => L.rank a) h1
    beta_reduce at this
    rwa [LinOrd.rank_map, LinOrd.rank_map, hs g, hs g', LinOrd.rank_std, LinOrd.rank_std] at this
  subst he
  have hg : g = g' := by
    have h3 : Tree.node g (TreeOfArity.leaves k) = Tree.node g' (TreeOfArity.leaves k) := h2
    simpa using h3
  rw [hg]

omit [Algebra ℚ R] in
lemma weight_ne_zero {T : ℕ → Type v} {x : Reg (TreeOfArity T) A} (hx : FreeGr.vcnt x ≠ 0) :
    (FreeGr.treeOf x).weight ≠ 0 := by
  intro h
  apply hx
  cases ht : FreeGr.treeOf x with
  | leaf =>
    show Tree.cnt _ (FreeGr.treeOf x) = 0
    rw [ht]
    rfl
  | node e fo =>
    rw [ht, Tree.weight_node] at h
    omega

omit [Algebra ℚ R] in
/-- The trees with one vertex are the relabelled corollas. -/
lemma eq_std_of_weight {t : Reg (TreeOfArity (GrGen R V)) A}
    (ht : (FreeGr.treeOf t).weight = 1) :
    ∃ (e : Fin (Fintype.card A) ≃ A) (g : GrGen R V (Fintype.card A)),
      t = SetOperad.map e (Reg.std (corolla g)) := by
  rcases FreeGr.shapeR t with ⟨e, rfl⟩ | ⟨k, g, e, rfl⟩ | ⟨a, b, i, p, q, e, hp, hq, rfl⟩
  · exact absurd ht (by rw [FreeGr.treeOf_map]; exact Nat.zero_ne_one)
  · obtain rfl : k = Fintype.card A := by simpa using Fintype.card_congr e
    exact ⟨e, g, rfl⟩
  · rw [FreeGr.treeOf_map, FreeGr.treeOf_comp, Tree.weight_graft _ _ _
      (FreeGr.rank_lt_arity p i)] at ht
    have := weight_ne_zero hp
    have := weight_ne_zero hq
    omega

/-- **The cogenerator part of the lift is the given morphism**: the trees with one vertex of the
image of `c` are the corollas `e · g`, with coefficient `L(e⁻¹ c)(g) / k!`, whose values add up to
`e · φ(e⁻¹ c) / k! = φ(c) / k!` for each of the `k!` numberings `e` of the inputs. -/
theorem genCoef_liftOf (ℓ : GenLift₀ φ) (hΨ : FreeGr.CoefFinite (liftOp ℓ)) (c : C A) :
    genCoef R V A ((liftOf ℓ hΨ).app A c) = φ.app A c := by
  haveI : DecidableEq (Reg (TreeOfArity (GrGen R V)) A) := Classical.decEq _
  set k := Fintype.card A with hk
  set y : Reg (TreeOfArity (GrGen R V)) A →₀ R :=
    FreeGr.ofCoefL (liftOp ℓ) hΨ A c with hy
  let f : Reg (TreeOfArity (GrGen R V)) A → V A := fun t =>
    FreeGr.coefF (liftOp ℓ) t c • coefReg R V t
  have h1 : genCoef R V A ((liftOf ℓ hΨ).app A c) = ∑ t ∈ y.support, f t := by
    show genCoefF R V A y = _
    rw [genCoefF]
    erw [Finsupp.linearCombination_apply]
    rfl
  let ι : (Σ _ : Fin k ≃ A, GrGen R V k) → Reg (TreeOfArity (GrGen R V)) A :=
    fun x => SetOperad.map x.1 (Reg.std (corolla x.2))
  let G : Finset (Σ _ : Fin k ≃ A, GrGen R V k) :=
    Finset.univ.sigma fun e => (ℓ.L k (SymSpecies.map (R := R) e.symm c)).support
  have hf : ∀ x : Σ _ : Fin k ≃ A, GrGen R V k, f (ι x) =
      (wk R k * ℓ.L k (SymSpecies.map (R := R) x.1.symm c) x.2) •
        SymSpecies.map (R := R) x.1 x.2.1.1 := by
    rintro ⟨e, g⟩
    show FreeGr.coefF (liftOp ℓ) (SetOperad.map e (Reg.std (corolla g))) c •
      coefReg R V (SetOperad.map e (Reg.std (corolla g))) = _
    rw [FreeGr.coefF_map, coefF_std, coefReg_map, coefReg_std_corolla]
  have h2 : ∑ x ∈ G, f (ι x) = φ.app A c := by
    rw [Finset.sum_sigma]
    have he : ∀ e : Fin k ≃ A,
        ∑ g ∈ (ℓ.L k (SymSpecies.map (R := R) e.symm c)).support, f (ι ⟨e, g⟩)
          = wk R k • φ.app A c := by
      intro e
      rw [φ.app_eq_chart e c, ← ℓ.lc, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hf, map_smul, smul_smul]
    rw [Finset.sum_congr rfl fun e _ => he e, Finset.sum_const, Finset.card_univ,
      Fintype.card_equiv (Fintype.equivFin A).symm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul R,
      smul_smul, factorial_mul_wk, one_smul]
  rw [h1, ← h2, ← Finset.sum_image (fun x _ x' _ h => map_std_injective h)]
  have hsub1 : y.support ⊆ y.support ∪ G.image ι := Finset.subset_union_left
  have hsub2 : G.image ι ⊆ y.support ∪ G.image ι := Finset.subset_union_right
  rw [Finset.sum_subset hsub1 (fun t _ ht => ?_), ← Finset.sum_subset hsub2 (fun t _ ht => ?_)]
  · by_cases hw : (FreeGr.treeOf t).weight = 1
    · obtain ⟨e, g, rfl⟩ := eq_std_of_weight hw
      have hg : g ∉ (ℓ.L k (SymSpecies.map (R := R) e.symm c)).support := fun hg =>
        ht (Finset.mem_image.2 ⟨(⟨e, g⟩ : Σ _ : Fin k ≃ A, GrGen R V k),
          Finset.mem_sigma.2 ⟨Finset.mem_univ _, hg⟩, rfl⟩)
      show f (ι (⟨e, g⟩ : Σ _ : Fin k ≃ A, GrGen R V k)) = 0
      rw [hf, Finsupp.notMem_support_iff.1 hg, mul_zero, zero_smul]
    · show FreeGr.coefF (liftOp ℓ) t c • coefReg R V t = 0
      rw [coefReg_of_weight_ne hw, smul_zero]
  · show FreeGr.coefF (liftOp ℓ) t c • coefReg R V t = 0
    rw [show FreeGr.coefF (liftOp ℓ) t c = y t from rfl, Finsupp.notMem_support_iff.1 ht,
      zero_smul]

/-- **The cogenerator part of the lift is the given morphism.** -/
theorem genCoef_lift (ℓ : GenLift φ) (c : C A) :
    genCoef R V A ((lift ℓ).app A c) = φ.app A c :=
  genCoef_liftOf ℓ.toGenLift₀ (coefFinite ℓ) c

/-! ## Existence of lifts -/

section Exists

omit [Algebra ℚ R]

variable (R V) in
/-- The generators of parity `b` with `k` inputs. -/
abbrev GenOf (k : ℕ) (b : Bool) : Type v := {g : GrGen R V k // g.1.2 = b}

lemma genOf_mem (k : ℕ) (b : Bool) (g : GenOf R V k b) :
    g.1.1.1 ∈ LinearMap.range (GrSpecies.par (R := R) (V := V) (A := Fin k) b) :=
  ⟨g.1.1.1, by have h := g.1.2; rwa [g.2] at h⟩

variable (R V) in
/-- **The value map** from the generators of parity `b` onto the elements of parity `b`. -/
noncomputable def parValMap (k : ℕ) (b : Bool) :
    (GenOf R V k b →₀ R) →ₗ[R] LinearMap.range (GrSpecies.par (R := R) (V := V) (A := Fin k) b) :=
  Finsupp.linearCombination R fun g => ⟨g.1.1.1, genOf_mem k b g⟩

lemma parValMap_surjective (k : ℕ) (b : Bool) : Function.Surjective (parValMap R V k b) := by
  rintro ⟨v, w, hw⟩
  have hv : GrSpecies.par (R := R) b v = v := by rw [← hw, GrSpecies.par_par_self]
  refine ⟨Finsupp.single ⟨⟨(v, b), hv⟩, rfl⟩ 1, ?_⟩
  rw [parValMap, Finsupp.linearCombination_single, one_smul]

lemma coe_parValMap (k : ℕ) (b : Bool) (F : GenOf R V k b →₀ R) :
    (parValMap R V k b F : V (Fin k))
      = Finsupp.linearCombination R (fun g : GrGen R V k => g.1.1)
          (Finsupp.mapDomain Subtype.val F) := by
  rw [Finsupp.linearCombination_mapDomain, parValMap, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, Submodule.coe_sum]
  rfl

variable {X : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (X A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (X A)] [GrSpecies R X]

/-- The part of parity `b` of the image, onto the elements of parity `b`. -/
noncomputable def parImg (φ : GrSpeciesHom R X V) (k : ℕ) (b : Bool) :
    X (Fin k) →ₗ[R] LinearMap.range (GrSpecies.par (R := R) (V := V) (A := Fin k) b) :=
  LinearMap.codRestrict _ (GrSpecies.par (R := R) b ∘ₗ φ.app (Fin k)) fun c =>
    ⟨φ.app (Fin k) c, rfl⟩

lemma mapDomain_val_apply {k : ℕ} {b : Bool} (F : GenOf R V k b →₀ R) (g : GrGen R V k) :
    Finsupp.mapDomain Subtype.val F g = if h : g.1.2 = b then F ⟨g, h⟩ else 0 := by
  split_ifs with h
  · exact Finsupp.mapDomain_apply Subtype.val_injective F ⟨g, h⟩
  · exact Finsupp.mapDomain_notin_range F g fun ⟨g', hg'⟩ => h (hg' ▸ g'.2)

/-- **Lifts to the generators of each parity**, through the surjective value maps, when `X (Fin k)`
or `V (Fin k)` is projective. In the second case the lift factors through `φ`. -/
lemma exists_lift_par_of (φ : GrSpeciesHom R X V) (k : ℕ) (b : Bool)
    (hk : Module.Projective R (X (Fin k)) ∨ Module.Projective R (V (Fin k))) :
    ∃ h : X (Fin k) →ₗ[R] (GenOf R V k b →₀ R), parValMap R V k b ∘ₗ h = parImg φ k b := by
  rcases hk with hk | hk
  · exact Module.projective_lifting_property _ _ (parValMap_surjective k b)
  · obtain ⟨s, hs⟩ := Module.projective_lifting_property (parValMap R V k b)
      (LinearMap.codRestrict _ (GrSpecies.par (R := R) (V := V) (A := Fin k) b) fun v => ⟨v, rfl⟩)
      (parValMap_surjective k b)
    refine ⟨s ∘ₗ φ.app (Fin k), LinearMap.ext fun x => ?_⟩
    rw [← LinearMap.comp_assoc, hs]
    rfl

/-- The chosen lift to the generators of each parity, `X (Fin k)` or `V (Fin k)` being
projective. -/
noncomputable def liftParOf (φ : GrSpeciesHom R X V) (k : ℕ) (b : Bool)
    (hk : Module.Projective R (X (Fin k)) ∨ Module.Projective R (V (Fin k))) :
    X (Fin k) →ₗ[R] (GenOf R V k b →₀ R) :=
  Classical.choose (exists_lift_par_of φ k b hk)

lemma parValMap_liftParOf (φ : GrSpeciesHom R X V) (k : ℕ) (b : Bool)
    (hk : Module.Projective R (X (Fin k)) ∨ Module.Projective R (V (Fin k))) (x : X (Fin k)) :
    (parValMap R V k b (liftParOf φ k b hk x) : V (Fin k))
      = GrSpecies.par (R := R) b (φ.app (Fin k) x) :=
  congrArg Subtype.val
    (LinearMap.congr_fun (Classical.choose_spec (exists_lift_par_of φ k b hk)) x)

/-- **The lift in arity `k`**: the parts of each parity lifted, `X (Fin k)` or `V (Fin k)` being
projective. -/
noncomputable def liftLOf (φ : GrSpeciesHom R X V) (k : ℕ)
    (hk : Module.Projective R (X (Fin k)) ∨ Module.Projective R (V (Fin k))) :
    X (Fin k) →ₗ[R] (GrGen R V k →₀ R) :=
  ∑ b : Bool, Finsupp.lmapDomain R R Subtype.val ∘ₗ liftParOf φ k b hk ∘ₗ
    GrSpecies.par (R := R) b

lemma liftLOf_apply (φ : GrSpeciesHom R X V) {k : ℕ}
    (hk : Module.Projective R (X (Fin k)) ∨ Module.Projective R (V (Fin k))) (x : X (Fin k))
    (g : GrGen R V k) :
    liftLOf φ k hk x g = liftParOf φ k g.1.2 hk (GrSpecies.par (R := R) g.1.2 x) ⟨g, rfl⟩ := by
  rw [liftLOf, LinearMap.coe_sum, Finset.sum_apply, Finsupp.finsetSum_apply, Fintype.sum_bool]
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, mapDomain_val_apply]
  obtain ⟨⟨v, c⟩, hv⟩ := g
  cases c <;> simp

/-- **The value of the lift is the image.** -/
lemma lc_liftLOf (φ : GrSpeciesHom R X V) {k : ℕ}
    (hk : Module.Projective R (X (Fin k)) ∨ Module.Projective R (V (Fin k))) (x : X (Fin k)) :
    Finsupp.linearCombination R (fun g : GrGen R V k => g.1.1) (liftLOf φ k hk x)
      = φ.app (Fin k) x := by
  rw [liftLOf, LinearMap.coe_sum, Finset.sum_apply, map_sum, Fintype.sum_bool]
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, ← coe_parValMap,
    parValMap_liftParOf, ← φ.app_par, GrSpecies.par_par_self]
  rw [add_comm, ← map_add, GrSpecies.par_add]

/-- **The lift sees only the generators of the parity of a homogeneous element.** -/
lemma liftLOf_par (φ : GrSpeciesHom R X V) {k : ℕ}
    (hk : Module.Projective R (X (Fin k)) ∨ Module.Projective R (V (Fin k))) (b : Bool)
    (x : X (Fin k)) (g : GrGen R V k) :
    liftLOf φ k hk (GrSpecies.par (R := R) b x) g
      = if g.1.2 = b then liftLOf φ k hk x g else 0 := by
  obtain ⟨⟨v, c⟩, hv⟩ := g
  rw [liftLOf_apply φ hk, liftLOf_apply φ hk]
  show liftParOf φ k c hk (GrSpecies.par (R := R) c (GrSpecies.par (R := R) b x)) _
    = if c = b then liftParOf φ k c hk (GrSpecies.par (R := R) c x) _ else 0
  by_cases h : c = b
  · subst h
    rw [GrSpecies.par_par_self, if_pos rfl]
  · rw [GrSpecies.par_par_ne h, map_zero, if_neg h]
    rfl

/-- **Every morphism into a reduced graded linear species lifts to the homogeneous generators**
when, in each arity `k ≥ 2`, the cooperations or the elements of `V` form a projective module. -/
theorem exists_genLift_of
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    (hproj : ∀ k, 2 ≤ k → Module.Projective R (C (Fin k)) ∨ Module.Projective R (V (Fin k)))
    (φ : GrSpeciesHom R C V) : Nonempty (GenLift φ) := by
  refine ⟨⟨⟨fun k => if h : 2 ≤ k then liftLOf φ k (hproj k h) else 0, fun k x => ?_,
    fun k b x g => ?_⟩, fun k hk => ?_⟩⟩
  · beta_reduce
    by_cases hk : 2 ≤ k
    · rw [dif_pos hk]
      exact lc_liftLOf φ _ x
    · rw [dif_neg hk]
      exact (hred (Fin k) (by rw [Fintype.card_fin]; omega) _).trans
        (hred (Fin k) (by rw [Fintype.card_fin]; omega) _).symm
  · by_cases hk : 2 ≤ k
    · simp only [dif_pos hk]
      exact liftLOf_par φ _ b x g
    · simp only [dif_neg hk, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply, ite_self]
  · exact dif_neg (by omega)

variable [hC : ∀ k : ℕ, Module.Projective R (C (Fin k))]

/-- **Lifts to the generators of each parity**, through the surjective value maps, `C (Fin k)`
being projective. -/
lemma exists_lift_par (φ : GrSpeciesHom R C V) (k : ℕ) (b : Bool) :
    ∃ h : C (Fin k) →ₗ[R] (GenOf R V k b →₀ R), parValMap R V k b ∘ₗ h = parImg φ k b :=
  Module.projective_lifting_property _ _ (parValMap_surjective k b)

/-- The chosen lift to the generators of each parity. -/
noncomputable def liftPar (φ : GrSpeciesHom R C V) (k : ℕ) (b : Bool) :
    C (Fin k) →ₗ[R] (GenOf R V k b →₀ R) :=
  Classical.choose (exists_lift_par φ k b)

lemma parValMap_liftPar (φ : GrSpeciesHom R C V) (k : ℕ) (b : Bool) (x : C (Fin k)) :
    (parValMap R V k b (liftPar φ k b x) : V (Fin k))
      = GrSpecies.par (R := R) b (φ.app (Fin k) x) :=
  congrArg Subtype.val (LinearMap.congr_fun (Classical.choose_spec (exists_lift_par φ k b)) x)

/-- The lift in arity `k`: the parts of each parity lifted, vanishing for `k ≤ 1`. -/
noncomputable def liftL (φ : GrSpeciesHom R C V) (k : ℕ) : C (Fin k) →ₗ[R] (GrGen R V k →₀ R) :=
  if 2 ≤ k then ∑ b : Bool, Finsupp.lmapDomain R R Subtype.val ∘ₗ liftPar φ k b ∘ₗ
    GrSpecies.par (R := R) b else 0

lemma liftL_apply (φ : GrSpeciesHom R C V) {k : ℕ} (hk : 2 ≤ k) (x : C (Fin k))
    (g : GrGen R V k) :
    liftL φ k x g = liftPar φ k g.1.2 (GrSpecies.par (R := R) g.1.2 x) ⟨g, rfl⟩ := by
  rw [liftL, if_pos hk, LinearMap.coe_sum, Finset.sum_apply, Finsupp.finsetSum_apply,
    Fintype.sum_bool]
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, mapDomain_val_apply]
  obtain ⟨⟨v, c⟩, hv⟩ := g
  cases c <;> simp

/-- **Every morphism into a reduced graded linear species lifts to the homogeneous generators**,
on a cooperad of projective modules. -/
theorem exists_genLift
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    (φ : GrSpeciesHom R C V) : Nonempty (GenLift φ) := by
  refine ⟨⟨⟨liftL φ, fun k x => ?_, fun k b x g => ?_⟩, fun k hk => ?_⟩⟩
  · by_cases hk : 2 ≤ k
    · rw [liftL, if_pos hk, LinearMap.coe_sum, Finset.sum_apply, map_sum, Fintype.sum_bool]
      simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, ← coe_parValMap, parValMap_liftPar,
        ← φ.app_par, GrSpecies.par_par_self]
      rw [add_comm, ← map_add, GrSpecies.par_add]
    · exact (hred (Fin k) (by rw [Fintype.card_fin]; omega) _).trans
        (hred (Fin k) (by rw [Fintype.card_fin]; omega) _).symm
  · by_cases hk : 2 ≤ k
    · obtain ⟨⟨v, c⟩, hv⟩ := g
      rw [liftL_apply φ hk, liftL_apply φ hk]
      show liftPar φ k c (GrSpecies.par (R := R) c (GrSpecies.par (R := R) b x)) _
        = if c = b then liftPar φ k c (GrSpecies.par (R := R) c x) _ else 0
      by_cases h : c = b
      · subst h
        rw [GrSpecies.par_par_self, if_pos rfl]
      · rw [GrSpecies.par_par_ne h, map_zero, if_neg h]
        rfl
    · rw [liftL, if_neg hk]
      simp
  · show liftL φ k = 0
    rw [liftL, if_neg (by omega)]

end Exists

/-! ## Uniqueness -/

section Unique

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)
local notation "𝒞" => FreeGrL R V

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C] [Algebra ℚ R] in
/-- **On one input, the counit of the cut cooperad is the coefficient of the unit tree.** -/
lemma counit_eq_unitCoeffL (z : FreeGrL R V Unit) :
    GrCooperad.counit (R := R) z = unitCoeffL R V Unit z := by
  obtain ⟨w, rfl⟩ := (𝒥).proj_surjective Unit z
  refine Lin.induction₁ (S := Reg (TreeOfArity (GrGen R V)))
    (GrCooperad.counit (R := R) (C := FreeGrL R V) ∘ₗ (𝒥).proj Unit)
    (unitCoeffL R V Unit ∘ₗ (𝒥).proj Unit) (fun t => ?_) w
  show (Finsupp.single t (1 : R)) SetOperad.one
    = FreeGr.unitCoeff (grGenPar R V) R Unit (𝔟 t)
  rw [FreeGr.unitCoeff_bas]
  by_cases ht : (FreeGr.treeOf t).isLeaf = true
  · rw [if_pos ht, FreeGr.eq_of_isLeaf ht (rfl : (FreeGr.treeOf
      (SetOperad.one : Reg (TreeOfArity (GrGen R V)) Unit)).isLeaf = true),
      Finsupp.single_eq_same]
  · rw [if_neg ht, Finsupp.single_eq_of_ne]
    rintro rfl
    exact ht rfl

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C] in
/-- **An operation without unit component differs from the generator of its coefficient of the
generators by trees with at least two vertices.** -/
lemma sub_ι_genCoef_mem {z : FreeGrL R V A} (hz : unitCoeffL R V A z = 0) :
    z - (ι R V).app A (genCoef R V A z) ∈ vxGe R V 2 A := by
  obtain ⟨w, rfl⟩ := (𝒥).proj_surjective A z
  let L : FreeGr R (grGenPar R V) A →ₗ[R] (FreeGrL R V A ⧸ vxGe R V 2 A) :=
    (vxGe R V 2 A).mkQ ∘ₗ ((𝒥).proj A - (ι R V).app A ∘ₗ genCoef R V A ∘ₗ (𝒥).proj A)
  have h := eq_zero_of_unitCoeff L (fun p hp => ?_) hz
  · rwa [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  show (vxGe R V 2 A).mkQ ((𝒥).proj A (𝔟 p)
    - (ι R V).app A (genCoef R V A ((𝒥).proj A (𝔟 p)))) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hmem : (𝒥).proj A (𝔟 p) ∈ vx R V (FreeGr.treeOf p).weight A :=
    mem_eig.2 (by rw [← Cobar.wtD_eq_derSp, wtD_proj_bas])
  by_cases hw : (FreeGr.treeOf p).weight = 1
  · rw [hw] at hmem
    rw [← eq_ι_genCoef hmem, sub_self]
    exact zero_mem _
  · have h1 := Tree.one_le_weight hp
    rw [genCoef_proj, genCoefF_bas, coefReg_of_weight_ne hw, map_zero, sub_zero]
    exact mem_vxGe (by omega) hmem

omit [Algebra ℚ R] in
/-- The universal twisting morphism after a morphism into the cut cooperad. -/
lemma toLin_appHom_ι (f : GrCooperadHom R C 𝒞) (x : C A) :
    ConvOp.toLin ((GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f)
      (Cobar.ι R 𝒞)).1 A) x = Cobar.ιL R 𝒞 A (f.app A x) := rfl

omit [Algebra ℚ R] in
lemma toLin_ιι_app (f : GrCooperadHom R C 𝒞) (x : C A) :
    ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) (f.app A x)
      = ConvOp.toLin ((GrOperad.Inv.star R _
        (GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f) (Cobar.ι R 𝒞))
        (GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f) (Cobar.ι R 𝒞))).1 A) x := by
  have h := congrArg (fun q : GrOperad.Inv R (ConvOp R C (CobarGr R 𝒞)) => ConvOp.toLin (q.1 A) x)
    (GrOperad.Inv.appHom_star (ConvOp.preHom (P := CobarGr R 𝒞) f) (Cobar.ι R 𝒞) (Cobar.ι R 𝒞))
  simp only [GrOperad.Inv.appHom_apply, ConvOp.preHom_app, LinearMap.comp_apply] at h
  exact h

omit [Algebra ℚ R] in
lemma toLin_sub_inv (q q' : GrOperad.Inv R (ConvOp R C (CobarGr R 𝒞))) (x : C A) :
    ConvOp.toLin ((q - q').1 A) x = ConvOp.toLin (q.1 A) x - ConvOp.toLin (q'.1 A) x :=
  rfl

omit [Algebra ℚ R] in
/-- **The square is a quadratic form**: for invariant families `q, q'` with values of weight at
least one whose difference has values of weight at least `k`, the difference of their squares has
values of weight at least `k + 1`. -/
lemma star_sub_star_mem {q q' : GrOperad.Inv R (ConvOp R C (CobarGr R 𝒞))} {k : ℕ}
    (hd : ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      ConvOp.toLin ((q - q').1 A') x' ∈ Cobar.wtGe (V := V) k A')
    (h1 : ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      ConvOp.toLin (q.1 A') x' ∈ Cobar.wtGe (V := V) 1 A')
    (h1' : ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      ConvOp.toLin (q'.1 A') x' ∈ Cobar.wtGe (V := V) 1 A')
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ q q - GrOperad.Inv.star R _ q' q').1 A) x
      ∈ Cobar.wtGe (V := V) (k + 1) A := by
  have hs : GrOperad.Inv.star R _ q q - GrOperad.Inv.star R _ q' q'
      = GrOperad.Inv.star R _ (q - q') q + GrOperad.Inv.star R _ q' (q - q') := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  refine (congrArg (fun y => y ∈ Cobar.wtGe (V := V) (k + 1) A)
    (congrArg (fun r : GrOperad.Inv R (ConvOp R C (CobarGr R 𝒞)) =>
      ConvOp.toLin (r.1 A) x) hs)).mpr ?_
  exact add_mem
    (ConvOp.toLin_star_mem (F := fun A _ _ => Cobar.wtGe (V := V) k A)
      (G := fun A _ _ => Cobar.wtGe (V := V) 1 A) (H := fun A _ _ => Cobar.wtGe (V := V) (k + 1) A)
      (Cobar.wtGe_par_all 1) (Cobar.wtGe_map_all (k + 1))
      (Cobar.wtGe_comp_all k 1 (k + 1) le_rfl) hd h1 A x)
    (ConvOp.toLin_star_mem (F := fun A _ _ => Cobar.wtGe (V := V) 1 A)
      (G := fun A _ _ => Cobar.wtGe (V := V) k A) (H := fun A _ _ => Cobar.wtGe (V := V) (k + 1) A)
      (Cobar.wtGe_par_all k) (Cobar.wtGe_map_all (k + 1))
      (Cobar.wtGe_comp_all 1 k (k + 1) (by omega)) h1' hd A x)

omit [Algebra ℚ R] in
lemma toLin_ιι_sub (f f' : GrCooperadHom R C 𝒞) (x : C A) :
    ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) (f.app A x - f'.app A x)
      = ConvOp.toLin ((GrOperad.Inv.star R _
          (GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f) (Cobar.ι R 𝒞))
          (GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f) (Cobar.ι R 𝒞))
        - GrOperad.Inv.star R _
          (GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f') (Cobar.ι R 𝒞))
          (GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f') (Cobar.ι R 𝒞))).1 A) x :=
  (map_sub (ConvOp.toLin ((Cobar.ιι R 𝒞).1 A)) _ _).trans
    ((congrArg₂ (· - ·) (toLin_ιι_app f x) (toLin_ιι_app f' x)).trans
      (toLin_sub_inv _ _ x).symm)

omit [Algebra ℚ R] in
lemma toLin_sub_appHom_mem (f f' : GrCooperadHom R C 𝒞) {k : ℕ}
    (hk : ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      f.app A' x' - f'.app A' x' ∈ vxGe R V k A') (A' : Type) [Fintype A'] [DecidableEq A']
    (x' : C A') :
    ConvOp.toLin ((GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f) (Cobar.ι R 𝒞)
      - GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f') (Cobar.ι R 𝒞)).1 A') x'
      ∈ Cobar.wtGe (V := V) k A' :=
  (congrArg (fun y => y ∈ Cobar.wtGe (V := V) k A')
      ((toLin_sub_inv (GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f) (Cobar.ι R 𝒞))
        (GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f') (Cobar.ι R 𝒞)) x').trans
        (map_sub (Cobar.ιL R 𝒞 A') (f.app A' x') (f'.app A' x')).symm)).mpr
      (Cobar.ιL_mem_wtGe (hk A' x'))

lemma toLin_appHom_ι_mem (g : GrCooperadHom R C 𝒞) (A' : Type) [Fintype A'] [DecidableEq A']
    (x' : C A') :
    ConvOp.toLin ((GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) g)
      (Cobar.ι R 𝒞)).1 A') x' ∈ Cobar.wtGe (V := V) 1 A' :=
  Cobar.ιL_mem_wtGe_one _

/-- **The difference of two morphisms is a coderivation**: when all the differences of two
morphisms into the cut cooperad have at least `k` vertices, their convolution squares have
weight at least `k + 1`. -/
lemma ιι_sub_mem {f f' : GrCooperadHom R C 𝒞} {k : ℕ}
    (hk : ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      f.app A' x' - f'.app A' x' ∈ vxGe R V k A') (A : Type) [Fintype A] [DecidableEq A]
    (x : C A) :
    ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) (f.app A x - f'.app A x)
      ∈ Cobar.wtGe (V := V) (k + 1) A :=
  (congrArg (fun y => y ∈ Cobar.wtGe (V := V) (k + 1) A) (toLin_ιι_sub f f' x)).mpr
    (star_sub_star_mem
      (q := GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f) (Cobar.ι R 𝒞))
      (q' := GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R 𝒞) f') (Cobar.ι R 𝒞))
      (toLin_sub_appHom_mem f f' hk) (toLin_appHom_ι_mem f) (toLin_appHom_ι_mem f') A x)

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C] in
/-- **An element with arbitrarily many vertices vanishes**: it is a finite sum of trees. -/
lemma eq_zero_of_forall_mem_vxGe {z : FreeGrL R V A} (hz : ∀ p, z ∈ vxGe R V p A) : z = 0 := by
  have htop : z ∈ ⨆ j : ℕ, vx R V j A := by
    rw [iSup_vx]
    exact Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 htop
  have hst : Disjoint (s : Set ℕ) (Set.Ici (s.sup id + 1)) := by
    refine Set.disjoint_left.2 fun j hj hj' => ?_
    have h1 : j ≤ s.sup id := Finset.le_sup (f := id) (Finset.mem_coe.1 hj)
    have h2 : s.sup id + 1 ≤ j := hj'
    omega
  have hd := (iSupIndep_eigenspace_nat ((derSp (GrSpEnd.id R V)).app A)).disjoint_biSup_biSup hst
  refine Submodule.disjoint_def.1 hd z (by simpa only [Finset.mem_coe] using hs) ?_
  refine (iSup_le fun k => ?_ : vxGe R V (s.sup id + 1) A ≤ ⨆ i ∈ Set.Ici (s.sup id + 1),
    vx R V i A) (hz _)
  exact le_biSup (fun j => vx R V j A) (Set.mem_Ici.2 k.2)

/-- **Morphisms into the cut cooperad are determined by their cogenerator parts**: two morphisms
of graded cooperads into the cut cooperad on a graded linear species without elements without
inputs, with the same coefficient of the generators, agree, over a `ℚ`-algebra. The species may
have elements with one input, and the cooperad need not be conilpotent. -/
theorem app_eq_of_genCoef₀ (hV0 : ∀ v : V (Fin 0), v = 0) {f f' : GrCooperadHom R C 𝒞}
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
      exact fun A' _ _ x' => Cobar.mem_vxGe_succ hV0 hk (ih A' x') (ιι_sub_mem ih A' x')
  exact sub_eq_zero.1 (eq_zero_of_forall_mem_vxGe fun p =>
    vxGe_anti (le_max_left p 2) (key _ (le_max_right p 2) A x))

/-- **Morphisms into the cut cooperad are determined by their cogenerator parts**: two morphisms
of graded cooperads into the cut cooperad on a reduced graded linear species with the same
coefficient of the generators agree, over a `ℚ`-algebra. -/
theorem app_eq_of_genCoef
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    {f f' : GrCooperadHom R C 𝒞}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      genCoef R V A (f.app A x) = genCoef R V A (f'.app A x))
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) : f.app A x = f'.app A x :=
  app_eq_of_genCoef₀ (hred (Fin 0) (by simp)) h A x

end Unique

/-! ## The universal property -/

section Universal

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C] [Algebra ℚ R] in
variable (R V) in
/-- **The projection onto the cogenerators** `T^c(V) → V`: the coefficient of the generators, a
morphism of graded linear species. -/
noncomputable def genCoefHom : GrSpeciesHom R (FreeGrL R V) V where
  app := genCoef R V
  app_map e x := genCoef_map e x
  app_par b x := by
    obtain ⟨y, rfl⟩ := (𝒥).proj_surjective _ x
    exact genCoefF_par b y

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C] [Algebra ℚ R] in
@[simp] lemma genCoefHom_app (x : FreeGrL R V A) : (genCoefHom R V).app A x = genCoef R V A x :=
  rfl

/-- **The universal property of the cut cooperad, with projectivity on either side**: over a
`ℚ`-algebra, for a reduced graded linear species `V` and a graded cooperad `C` such that in each
arity `k ≥ 2` the cooperations `C (Fin k)` or the elements `V (Fin k)` form a projective module,
the morphisms of graded cooperads `C → T^c(V)` are the morphisms of graded linear species
`C → V`, by composition with the projection onto the cogenerators. -/
noncomputable def cofreeHomEquiv'
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    (hproj : ∀ k, 2 ≤ k → Module.Projective R (C (Fin k)) ∨ Module.Projective R (V (Fin k))) :
    GrCooperadHom R C (FreeGrL R V) ≃ GrSpeciesHom R C V where
  toFun f := (genCoefHom R V).comp f.toGrSpeciesHom
  invFun φ := lift (Classical.choice (exists_genLift_of hred hproj φ))
  left_inv _ := GrCooperadHom.ext (app_eq_of_genCoef hred fun _ _ _ x => genCoef_lift _ x)
  right_inv _ := GrSpeciesHom.ext fun _ _ _ x => genCoef_lift _ x

@[simp] lemma cofreeHomEquiv'_apply
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    (hproj : ∀ k, 2 ≤ k → Module.Projective R (C (Fin k)) ∨ Module.Projective R (V (Fin k)))
    (f : GrCooperadHom R C (FreeGrL R V)) (x : C A) :
    (cofreeHomEquiv' hred hproj f).app A x = genCoef R V A (f.app A x) :=
  rfl

/-- **The cofree property of the cut cooperad, with projectivity on either side**: every
morphism of graded linear species into a reduced graded linear species `V` lifts uniquely to a
morphism of graded cooperads into `T^c(V)`, over a `ℚ`-algebra, when in each arity `k ≥ 2` the
cooperations or the elements of `V` form a projective module. -/
theorem existsUnique_lift'
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    (hproj : ∀ k, 2 ≤ k → Module.Projective R (C (Fin k)) ∨ Module.Projective R (V (Fin k)))
    (φ : GrSpeciesHom R C V) :
    ∃! f : GrCooperadHom R C (FreeGrL R V), ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      genCoef R V A (f.app A x) = φ.app A x :=
  ⟨lift (Classical.choice (exists_genLift_of hred hproj φ)), fun _ _ _ x => genCoef_lift _ x,
    fun _ hf => GrCooperadHom.ext (app_eq_of_genCoef hred fun A _ _ x =>
      (hf A x).trans (genCoef_lift _ x).symm)⟩

variable [∀ k : ℕ, Module.Projective R (C (Fin k))]

/-- **The universal property of the cut cooperad**: over a `ℚ`-algebra, for a reduced graded
linear species `V` and a graded cooperad `C` of projective modules, the morphisms of graded
cooperads `C → T^c(V)` are the morphisms of graded linear species `C → V`, by composition with
the projection onto the cogenerators. -/
noncomputable def cofreeHomEquiv
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0) :
    GrCooperadHom R C (FreeGrL R V) ≃ GrSpeciesHom R C V where
  toFun f := (genCoefHom R V).comp f.toGrSpeciesHom
  invFun φ := lift (Classical.choice (exists_genLift hred φ))
  left_inv _ := GrCooperadHom.ext (app_eq_of_genCoef hred fun _ _ _ x => genCoef_lift _ x)
  right_inv _ := GrSpeciesHom.ext fun _ _ _ x => genCoef_lift _ x

@[simp] lemma cofreeHomEquiv_apply
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    (f : GrCooperadHom R C (FreeGrL R V)) (x : C A) :
    (cofreeHomEquiv hred f).app A x = genCoef R V A (f.app A x) :=
  rfl

/-- **The cofree property of the cut cooperad**: every morphism of graded linear species into a
reduced graded linear species `V` lifts uniquely to a morphism of graded cooperads into
`T^c(V)`, over a `ℚ`-algebra, from a graded cooperad of projective modules. -/
theorem existsUnique_lift
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    (φ : GrSpeciesHom R C V) :
    ∃! f : GrCooperadHom R C (FreeGrL R V), ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      genCoef R V A (f.app A x) = φ.app A x :=
  ⟨lift (Classical.choice (exists_genLift hred φ)), fun _ _ _ x => genCoef_lift _ x,
    fun _ hf => GrCooperadHom.ext (app_eq_of_genCoef hred fun A _ _ x =>
      (hf A x).trans (genCoef_lift _ x).symm)⟩

/-! ### From the reduced part -/

variable [GrCooperad.Coaug R C]

omit [∀ k : ℕ, Module.Projective R (C (Fin k))] [Algebra ℚ R] in
variable (R C) in
/-- The projection onto the reduced part, a morphism of graded linear species. -/
def redProjHom : GrSpeciesHom R C (GrCooperad.Red R C) where
  app := GrCooperad.Red.proj R C
  app_map e x := (GrCooperad.Red.map_proj e x).symm
  app_par b x := (GrCooperad.Red.par_proj b x).symm

omit [∀ k : ℕ, Module.Projective R (C (Fin k))] [Algebra ℚ R] in
/-- A morphism into a reduced graded linear species kills the coaugmentation. -/
lemma unitSpan_le_ker
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    (φ : GrSpeciesHom R C V) (A : Type) [Fintype A] [DecidableEq A] :
    GrCooperad.unitSpan R C A ≤ LinearMap.ker (φ.app A) :=
  Submodule.span_le.2 fun _ ⟨e, he⟩ => LinearMap.mem_ker.2
    (hred A (by rw [← Fintype.card_congr e, Fintype.card_unit]) _)

omit [∀ k : ℕ, Module.Projective R (C (Fin k))] [Algebra ℚ R] in
/-- **Morphisms into a reduced graded linear species are morphisms out of the reduced part.** -/
noncomputable def redHomEquiv
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0) :
    GrSpeciesHom R C V ≃ GrSpeciesHom R (GrCooperad.Red R C) V where
  toFun φ :=
    { app := fun A _ _ => (GrCooperad.unitSpan R C A).liftQ (φ.app A) (unitSpan_le_ker hred φ A)
      app_map := fun {A B} _ _ _ _ e X => by
        obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective A X
        exact φ.app_map e x
      app_par := fun {A} _ _ b X => by
        obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective A X
        exact φ.app_par b x }
  invFun ψ := ψ.comp (redProjHom R C)
  left_inv _ := GrSpeciesHom.ext fun _ _ _ _ => rfl
  right_inv ψ := GrSpeciesHom.ext fun A _ _ X => by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective A X
    rfl

/-- **The universal property of the cut cooperad, from the reduced part**: over a `ℚ`-algebra,
for a reduced graded linear species `V` and a coaugmented graded cooperad `C` of projective
modules, the morphisms of graded cooperads `C → T^c(V)` are the morphisms of graded linear
species `C̄ → V` from the reduced part, by composition with the projection onto the
cogenerators. -/
noncomputable def cofreeHomEquivRed
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0) :
    GrCooperadHom R C (FreeGrL R V) ≃ GrSpeciesHom R (GrCooperad.Red R C) V :=
  (cofreeHomEquiv hred).trans (redHomEquiv hred)

omit [∀ k : ℕ, Module.Projective R (C (Fin k))] in
/-- **The universal property of the cut cooperad from the reduced part, with projectivity on
either side**: the morphisms of graded cooperads `C → T^c(V)` are the morphisms of graded linear
species `C̄ → V`, when in each arity `k ≥ 2` the cooperations or the elements of `V` form a
projective module. -/
noncomputable def cofreeHomEquivRed'
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    (hproj : ∀ k, 2 ≤ k → Module.Projective R (C (Fin k)) ∨ Module.Projective R (V (Fin k))) :
    GrCooperadHom R C (FreeGrL R V) ≃ GrSpeciesHom R (GrCooperad.Red R C) V :=
  (cofreeHomEquiv' hred hproj).trans (redHomEquiv hred)

lemma cofreeHomEquivRed_apply
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    (f : GrCooperadHom R C (FreeGrL R V)) (x : C A) :
    (cofreeHomEquivRed hred f).app A (GrCooperad.Red.proj R C A x)
      = genCoef R V A (f.app A x) := by
  rw [cofreeHomEquivRed, Equiv.trans_apply]
  rfl

end Universal

end FreeGrL

end Operad
