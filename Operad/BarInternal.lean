/-
# The bar construction of a dg operad

For a dg operad `P` and an ideal `I` stable under its differential `∂`, **the bar construction
`B(P, I)` is a dg cooperad** with the sum of the bar differential and **the internal
differential**, `∂` applied to the vertices of a tree one at a time (`Bar.dInt`,
`Bar.dgCooperad`).

* The internal differential is the derivation of the free graded operad on `sI` extending `∂` on
  the generators (`Bar.dGen`, `FreeGrL.derSp`). Modulo the linearity relations it is the vertex
  derivation of the free graded operad on the homogeneous elements (`FreeGrL.proj_vD`, through
  `FreeGr.der_ext`), so **it is a coderivation** (`Bar.decomp_dInt`) and **it squares to zero**
  (`Bar.dInt_dInt`).
* **It anticommutes with the bar differential** (`Bar.d_dInt`). On two merged generators the
  defect is the Leibniz rule of `∂` through the merge `s a ⊛ s b = (-1)^{|a|} s (a ∘ b)`
  (`Bar.d_barVal`, `Bar.gam_gen_mem`), and `FreeGr.anti_mem` reduces every tree to that case.
-/
import Operad.FreeGrVertex
import Operad.BarMap

universe u v w

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

/-! ## The vertex derivation as a derivation -/

namespace FreeGr

variable {T : ℕ → Type v} {g : ∀ k, T k → T k} {gp : ∀ k, T k → Bool} {R : Type u} [CommRing R]

variable (g gp R) in
/-- **The vertex derivation, as an odd derivation of the free graded operad.** -/
noncomputable def vDer (hg : ∀ k e, gp k (g k e) = !gp k e) :
    GrDer (GrOperadHom.id R (FreeGr R gp)) true where
  app A _ _ := vD g gp R A
  app_par c x := by
    show vD g gp R _ (GrOperad.par (R := R) c x)
      = GrOperad.par (R := R) (xor c true) (vD g gp R _ x)
    rw [par_vD hg, Bool.xor_true, Bool.not_not]
  app_map σ' x := (map_vD σ' x).symm
  app_one := vD_bas_of_weight (x := (SetOperad.one : Reg (TreeOfArity T) Unit)) rfl
  app_comp i x y := by
    show vD g gp R _ (GrOperad.comp (R := R) i x y) = _
    rw [vD_comp hg]
    rfl

@[simp] lemma vDer_app (hg : ∀ k e, gp k (g k e) = !gp k e) {A : Type} [Fintype A]
    [DecidableEq A] (x : FreeGr R gp A) : (vDer g gp R hg).app A x = vD g gp R A x := rfl

variable {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **Derivations out of the free graded operad agree when they agree on the generators.** -/
theorem der_ext {f : GrOperadHom R (FreeGr R gp) Q} {e : Bool} {D D' : GrDer f e}
    (h : ∀ k (t : T k), D.app (Fin k) (gen t) = D'.app (Fin k) (gen t)) : D = D' := by
  have hh : D.toHom = D'.toHom := FreeGr.hom_ext fun k t => DualExt.ext rfl (h k t)
  ext A _ _ x
  have := congrArg (fun Φ : GrOperadHom R (FreeGr R gp) (DualExt R Q e) =>
    DualExt.snd (Φ.app A x)) hh
  simpa using this

end FreeGr

/-! ## On the free graded operad on a graded linear species -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)

variable (φ : GrSpEnd R V true)

/-- **An odd endomorphism on the homogeneous generators.** -/
def genD (k : ℕ) (x : GrGen R V k) : GrGen R V k :=
  ⟨(φ.app (Fin k) x.1.1, !x.1.2), by
    show GrSpecies.par (R := R) (!x.1.2) (φ.app (Fin k) x.1.1) = φ.app (Fin k) x.1.1
    conv_rhs => rw [← x.2]
    rw [φ.app_par, Bool.xor_true]⟩

lemma genD_par (k : ℕ) (x : GrGen R V k) :
    grGenPar R V k (genD φ k x) = !grGenPar R V k x := rfl

/-- **The vertex derivation descends to the derivation extending `φ`.** -/
theorem proj_vD (x : FreeGr R (grGenPar R V) A) :
    (𝒥).proj A (vD (genD φ) (grGenPar R V) R A x) = (derSp φ).app A ((𝒥).proj A x) := by
  have h : GrDer.homComp (𝒥).projHom (vDer (genD φ) (grGenPar R V) R (genD_par φ))
      = (derSp φ).compHom (𝒥).projHom := FreeGr.der_ext fun k t => by
    obtain ⟨⟨v, b⟩, hv⟩ := t
    show (𝒥).proj (Fin k) (vD (genD φ) (grGenPar R V) R (Fin k) (gen _))
      = (derSp φ).app (Fin k) ((𝒥).proj (Fin k) (gen _))
    rw [vD_gen]
    show FreeGr.presGen (grLinRel R V) _
      = (derSp φ).app (Fin k) (FreeGr.presGen (grLinRel R V) _)
    rw [← ι_app_hom hv, derSp_ι]
    exact (ι_app_hom (genD φ k ⟨(v, b), hv⟩).2).symm
  exact congrArg (fun D : GrDer (𝒥).projHom true => D.app A x) h

end FreeGrL

/-! ## The internal differential of the bar construction -/

section Internal

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]
  (I : GrOperadIdeal R P)
  (hI : ∀ {A : Type} [Fintype A] [DecidableEq A] {x : P A}, x ∈ I.sub A →
    DGOperad.d (R := R) x ∈ I.sub A)

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R (BarGen I))

namespace Bar

/-- **The differential of the operad on the generators** of the bar construction. -/
def dGen : GrSpEnd R (BarGen I) true where
  app A _ _ := (DGOperad.d (R := R) (P := P) (A := A)).restrict fun _ hx => hI hx
  app_map σ' x := Subtype.ext (DGOperad.map_d σ' (x : I.sub _).1).symm
  app_par c x := Subtype.ext (by
    show DGOperad.d (R := R) (GrOperad.par (R := R) (!c) (x : I.sub _).1)
      = GrOperad.par (R := R) (!(xor c true)) (DGOperad.d (R := R) (x : I.sub _).1)
    rw [DGOperad.d_par, Bool.xor_true])

lemma genD_val {k : ℕ} (x : BarT I k) :
    BarT.val (FreeGrL.genD (dGen I hI) k x) = DGOperad.d (R := R) x.val := rfl

lemma genD_par {k : ℕ} (x : BarT I k) : (FreeGrL.genD (dGen I hI) k x).1.2 = !x.1.2 := rfl

/-- **The Leibniz rule on merged decorations**:
`∂ (s a ⊛ s b) = -(s ∂a ⊛ s b) - (-1)^|sa| (s a ⊛ s ∂b)`. -/
lemma d_barVal {k l : ℕ} (a : BarT I k) (q : Fin k) (b : BarT I l) (m : ℕ) (h : m + 1 = k + l) :
    DGOperad.d (R := R) (barVal I a q b m h)
      = (-1 : R) • barVal I (FreeGrL.genD (dGen I hI) k a) q b m h
        + (-σ R a.1.2) • barVal I a q (FreeGrL.genD (dGen I hI) l b) m h := by
  unfold barVal
  rw [genD_val, genD_val, genD_par, map_smul, ← DGOperad.map_d, DGOperad.d_comp, map_add,
    smul_add]
  have ha : GrOperad.par (R := R) false a.val - GrOperad.par (R := R) true a.val
      = σ R (!a.1.2) • a.val := by
    have h1 := GrOperad.tw_hom (R := R) true a.par_val
    rw [GrOperad.tw_apply, σ_true, neg_one_smul, ← sub_eq_add_neg, Bool.true_and] at h1
    exact h1
  rw [ha, map_smul, LinearMap.smul_apply, map_smul, smul_smul, smul_smul, smul_smul,
    Bool.not_not]
  cases a.1.2 <;> simp [σ]

/-- **The defect of the internal differential on two merged generators** lies in the ideal of the
linearity relations. -/
theorem gam_gen_mem {k l : ℕ} (a : BarT I k) (b : BarT I l) (j : Fin k) :
    FreeGr.gam (FreeGrL.genD (dGen I hI)) (grGenPar R (BarGen I)) R (barMerge I) j
      (gen (R := R) (gp := grGenPar R (BarGen I)) a) (gen b) ∈ (𝒥).sub _ := by
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = k + l := ⟨k + l - 1, by have := j.2; omega⟩
  have hj : (j : ℕ) < k ∧ m + 1 = k + l := ⟨j.2, hm⟩
  unfold FreeGr.gam
  rw [FreeGr.vD_gen, FreeGr.vD_gen, GrSpecies.tw_hom true (FreeGr.par_gen a), map_smul,
    LinearMap.smul_apply, mcomp_gen_bar a j b m hm, mcomp_gen_bar _ j b m hm,
    mcomp_gen_bar a j _ m hm, ← FreeGr.map_vD, FreeGr.vD_gen, ← map_smul, ← map_add, ← map_add]
  refine (𝒥).map_mem _ ?_
  set x := FreeGrL.genD (dGen I hI) m (barMerge I k l a j b m)
  set y := barMerge I k l (FreeGrL.genD (dGen I hI) k a) j b m
  set z := barMerge I k l a j (FreeGrL.genD (dGen I hI) l b) m
  have hpy : y.1.2 = x.1.2 := by
    simp only [x, y, barMerge_par, genD_par]
    cases a.1.2 <;> cases b.1.2 <;> rfl
  have hpz : z.1.2 = x.1.2 := by
    simp only [x, z, barMerge_par, genD_par]
    cases a.1.2 <;> cases b.1.2 <;> rfl
  let u : BarT I m := ⟨((-1 : R) • y.1.1, y.1.2), by
    show GrSpecies.par (R := R) y.1.2 ((-1 : R) • y.1.1) = (-1 : R) • y.1.1
    rw [map_smul, y.2]⟩
  let w : BarT I m := ⟨((-σ R a.1.2) • z.1.1, z.1.2), by
    show GrSpecies.par (R := R) z.1.2 ((-σ R a.1.2) • z.1.1) = (-σ R a.1.2) • z.1.1
    rw [map_smul, z.2]⟩
  have h1 : gen (R := R) (gp := grGenPar R (BarGen I)) x - gen u - gen w ∈ (𝒥).sub _ := by
    refine gen_sub_mem_add x u w hpy hpz (BarT.eq_add ?_)
    show BarT.val x = (-1 : R) • BarT.val y + (-σ R a.1.2) • BarT.val z
    rw [genD_val, barMerge_val _ _ hj, d_barVal I hI a ⟨j, hj.1⟩ b m hm, barMerge_val _ _ hj,
      barMerge_val _ _ hj]
  have h2 : gen (R := R) (gp := grGenPar R (BarGen I)) u - (-1 : R) • gen y ∈ (𝒥).sub _ :=
    gen_sub_mem_smul u y (-1) rfl rfl
  have h3 : gen (R := R) (gp := grGenPar R (BarGen I)) w - (-σ R a.1.2) • gen z ∈ (𝒥).sub _ :=
    gen_sub_mem_smul w z (-σ R a.1.2) rfl rfl
  have := add_mem (add_mem h1 h2) h3
  convert this using 1
  simp only [neg_smul, one_smul]
  abel

variable {I}

/-- **The internal differential of the bar construction**: the differential of the operad applied
to the vertices one at a time, an odd derivation of the free graded operad. -/
noncomputable def dInt : GrDer (GrOperadHom.id R (FreeGrL R (BarGen I))) true :=
  FreeGrL.derSp (dGen I hI)

lemma dInt_proj {A : Type} [Fintype A] [DecidableEq A]
    (x : FreeGr R (grGenPar R (BarGen I)) A) :
    (dInt hI).app A ((𝒥).proj A x)
      = (𝒥).proj A (FreeGr.vD (FreeGrL.genD (dGen I hI)) (grGenPar R (BarGen I)) R A x) :=
  (FreeGrL.proj_vD _ x).symm

/-- **The internal differential squares to zero.** -/
theorem dInt_dInt {A : Type} [Fintype A] [DecidableEq A] (X : FreeGrL R (BarGen I) A) :
    (dInt hI).app A ((dInt hI).app A X) = 0 :=
  FreeGrL.sq_eq_zero (fun A _ _ v => by
    rw [dInt, FreeGrL.derSp_ι, FreeGrL.derSp_ι]
    have : (dGen I hI).app A ((dGen I hI).app A v) = 0 :=
      Subtype.ext (DGOperad.d_d (R := R) (v : I.sub A).1)
    rw [this, map_zero]) X

/-- **The internal differential anticommutes with the bar differential.** -/
theorem d_dInt {A : Type} [Fintype A] [DecidableEq A] (X : FreeGrL R (BarGen I) A) :
    Bar.d I A ((dInt hI).app A X) + (dInt hI).app A (Bar.d I A X) = 0 := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  rw [dInt_proj, Bar.d_proj, Bar.d_proj, dInt_proj, ← map_add]
  have h := FreeGr.anti_mem (g := FreeGrL.genD (dGen I hI)) (gp := grGenPar R (BarGen I))
    (μ := barMerge I) (I := 𝒥) barMerge_odd (FreeGrL.genD_par _)
    (fun a b j => gam_gen_mem I hI a b j) x
  exact ((𝒥).proj_eq_zero_iff _).2 h

/-- **The internal differential is a coderivation.** -/
theorem decomp_dInt {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (X : FreeGrL R (BarGen I) (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := FreeGrL R (BarGen I)) i ((dInt hI).app _ X)
      = TensorProduct.map ((dInt hI).app A) LinearMap.id
          (GrCooperad.decomp (R := R) (C := FreeGrL R (BarGen I)) i X)
        + TensorProduct.map
            (GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) false
              - GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) true)
            ((dInt hI).app B)
          (GrCooperad.decomp (R := R) (C := FreeGrL R (BarGen I)) i X) := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective _ X
  rw [dInt_proj]
  have key : TensorProduct.map ((𝒥).proj A) ((𝒥).proj B) (GrCooperad.decomp (R := R) i
        (FreeGr.vD (FreeGrL.genD (dGen I hI)) (grGenPar R (BarGen I)) R _ x))
      = TensorProduct.map ((dInt hI).app A) LinearMap.id
          (TensorProduct.map ((𝒥).proj A) ((𝒥).proj B) (GrCooperad.decomp (R := R) i x))
        + TensorProduct.map
            (GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) false
              - GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) true)
            ((dInt hI).app B)
          (TensorProduct.map ((𝒥).proj A) ((𝒥).proj B) (GrCooperad.decomp (R := R) i x)) := by
    rw [FreeGr.decomp_vD (FreeGrL.genD_par _)]
    have hlin : (TensorProduct.map ((𝒥).proj A) ((𝒥).proj B)).comp
          (TensorProduct.map (FreeGr.vD (FreeGrL.genD (dGen I hI)) (grGenPar R (BarGen I)) R A)
              LinearMap.id
            + TensorProduct.map (GrSpecies.tw (R := R) (V := FreeGr R (grGenPar R (BarGen I))) true)
              (FreeGr.vD (FreeGrL.genD (dGen I hI)) (grGenPar R (BarGen I)) R B))
        = (TensorProduct.map ((dInt hI).app A) LinearMap.id
            + TensorProduct.map
              (GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) false
                - GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) true)
              ((dInt hI).app B)).comp (TensorProduct.map ((𝒥).proj A) ((𝒥).proj B)) :=
      TensorProduct.ext' fun a b => by
        simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, TensorProduct.map_tmul,
          LinearMap.id_apply, dInt_proj]
        rw [LinearMap.sub_apply, tw_proj]
    exact LinearMap.congr_fun hlin _
  exact key

omit [DGOperad R P] in
lemma map_add_pair {MA MB : Type*} [AddCommGroup MA] [Module R MA] [AddCommGroup MB] [Module R MB]
    (fA gA t : MA →ₗ[R] MA) (fB gB : MB →ₗ[R] MB) (z : MA ⊗[R] MB) :
    TensorProduct.map (fA + gA) LinearMap.id z + TensorProduct.map t (fB + gB) z
      = (TensorProduct.map fA LinearMap.id z + TensorProduct.map t fB z)
        + (TensorProduct.map gA LinearMap.id z + TensorProduct.map t gB z) := by
  rw [TensorProduct.map_add_left, TensorProduct.map_add_right, LinearMap.add_apply,
    LinearMap.add_apply]
  abel

/-- **The bar construction of a dg operad is a dg cooperad**, with the sum of the bar differential
and the internal differential. -/
@[reducible] noncomputable def dgCooperad : DGCooperad R (BarCoop I) :=
  { (inferInstance : GrCooperad R (FreeGrL R (BarGen I))) with
    d := fun {A} _ _ => Bar.d I A + (dInt hI).app A
    d_d := fun {A} _ _ X => by
      show (Bar.d I A + (dInt hI).app A) ((Bar.d I A + (dInt hI).app A) X) = 0
      simp only [LinearMap.add_apply, map_add]
      rw [Bar.d_d, dInt_dInt, zero_add, add_zero, add_comm]
      exact d_dInt hI X
    d_par := fun {A} _ _ b X => by
      show (Bar.d I A + (dInt hI).app A) (GrOperad.par (R := R) b X)
        = GrOperad.par (R := R) (!b) ((Bar.d I A + (dInt hI).app A) X)
      have h1 : Bar.d I A (GrOperad.par (R := R) b X) = GrOperad.par (R := R) (!b) (Bar.d I A X) :=
        (instDGCooperad I).d_par b X
      rw [LinearMap.add_apply, LinearMap.add_apply, map_add, h1, (dInt hI).app_par,
        Bool.xor_true]
    map_d := fun {A B} _ _ _ _ e X => by
      show GrOperad.map (R := R) e ((Bar.d I A + (dInt hI).app A) X)
        = (Bar.d I B + (dInt hI).app B) (GrOperad.map (R := R) e X)
      have h1 : GrOperad.map (R := R) e (Bar.d I A X) = Bar.d I B (GrOperad.map (R := R) e X) :=
        (instDGCooperad I).map_d e X
      rw [LinearMap.add_apply, LinearMap.add_apply, map_add, h1, (dInt hI).app_map]
    counit_d := fun X => by
      show GrCooperad.counit (R := R) (C := FreeGrL R (BarGen I))
        ((Bar.d I Unit + (dInt hI).app Unit) X) = 0
      have h1 : GrCooperad.counit (R := R) (C := FreeGrL R (BarGen I)) (Bar.d I Unit X) = 0 :=
        (instDGCooperad I).counit_d X
      rw [LinearMap.add_apply, map_add, h1, zero_add]
      obtain ⟨x, rfl⟩ := (𝒥).proj_surjective Unit X
      rw [dInt_proj]
      exact FreeGr.counit_vD x
    decomp_d := fun {A B} _ _ _ _ i X => by
      show GrCooperad.decomp (R := R) (C := FreeGrL R (BarGen I)) i
          ((Bar.d I (Without A i ⊕ B) + (dInt hI).app (Without A i ⊕ B)) X)
        = TensorProduct.map (Bar.d I A + (dInt hI).app A) LinearMap.id
            (GrCooperad.decomp (R := R) (C := FreeGrL R (BarGen I)) i X)
          + TensorProduct.map
              (GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) false
                - GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) true)
              (Bar.d I B + (dInt hI).app B)
            (GrCooperad.decomp (R := R) (C := FreeGrL R (BarGen I)) i X)
      have h1 : GrCooperad.decomp (R := R) (C := FreeGrL R (BarGen I)) i (Bar.d I _ X)
          = TensorProduct.map (Bar.d I A) LinearMap.id
              (GrCooperad.decomp (R := R) (C := FreeGrL R (BarGen I)) i X)
            + TensorProduct.map
                (GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) false
                  - GrOperad.par (R := R) (P := FreeGrL R (BarGen I)) (A := A) true)
                (Bar.d I B) (GrCooperad.decomp (R := R) (C := FreeGrL R (BarGen I)) i X) :=
        (instDGCooperad I).decomp_d i X
      rw [LinearMap.add_apply, map_add, h1, decomp_dInt hI i X, map_add_pair] }

/-- **The differential of the bar construction of a dg operad kills the coaugmentation.** -/
theorem dgCooperad_d_one :
    (Bar.d I Unit + (dInt hI).app Unit) (GrCooperad.Coaug.one (R := R) (C := BarCoop I)) = 0 := by
  have h1 : Bar.d I Unit (GrCooperad.Coaug.one (R := R) (C := BarCoop I)) = 0 := Bar.d_one
  have h2 : (dInt hI).app Unit (GrCooperad.Coaug.one (R := R) (C := BarCoop I)) = 0 :=
    (dInt hI).app_one
  rw [LinearMap.add_apply, h1, h2, add_zero]

end Bar

end Internal

end Operad
