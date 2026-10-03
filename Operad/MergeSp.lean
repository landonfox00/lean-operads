/-
# Merge structures on graded linear species

A **merge structure** on a graded linear species `W` (`MergeSp`) composes an element `x` of
`W (Fin k)`, homogeneous of parity `b`, with an element `y` of `W (Fin l)` at an input `q`, as an
element of `W (Fin m)` for `m + 1 = k + l`: bilinearly, equivariantly in both arguments, and adding
the parities plus one. Its value may depend on the parity `b` of `x`.

It gives an odd merge function on the homogeneous elements (`MergeSp.fn`) compatible with the
linearity relations of the free graded operad on `W` (`MergeSp.relHyp`), so that its bar
differential (`MergeSp.d`) and its merge-composition (`MergeSp.mc`) descend to `FreeGrL R W`.
-/
import Operad.Bar

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

/-! ## The unit component of operations of a free graded operad on a linear species -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)

/-- The ideal of the linearity relations has no unit component. -/
lemma span_le_noUnit : 𝒥 ≤ noUnitIdeal (gp := grGenPar R V) (R := R) :=
  (GrOperadIdeal.span_le (I := noUnitIdeal (gp := grGenPar R V) (R := R))).2
    fun _ _ hr => unitCoeff_of_linRel hr

variable (R V) in
/-- **The coefficient of the unit tree**, on the free graded operad on a graded linear species. -/
noncomputable def unitCoeffL (A : Type) [Fintype A] [DecidableEq A] : FreeGrL R V A →ₗ[R] R :=
  Submodule.liftQ _ (unitCoeff (grGenPar R V) R A) fun _ hz => span_le_noUnit A hz

lemma unitCoeffL_proj (x : FreeGr R (grGenPar R V) A) :
    unitCoeffL R V A ((𝒥).proj A x) = unitCoeff (grGenPar R V) R A x := rfl

variable (R V) in
/-- **The unit**, in every arity: the sum of the relabellings of the identity, zero outside the
arities of one element. -/
noncomputable def unitL (A : Type) [Fintype A] [DecidableEq A] : FreeGrL R V A :=
  ∑ e : Unit ≃ A, GrOperad.map (R := R) e (GrOperad.one (R := R) (P := FreeGrL R V))

lemma unitL_eq (e : Unit ≃ A) :
    unitL R V A = GrOperad.map (R := R) e (GrOperad.one (R := R) (P := FreeGrL R V)) := by
  haveI : Subsingleton (Unit ≃ A) := ⟨fun e₁ e₂ => Equiv.ext fun u => by
    have hA : ∀ a a' : A, a = a' := fun a a' => by
      rw [← e.apply_symm_apply a, ← e.apply_symm_apply a']
    exact hA _ _⟩
  rw [unitL, Fintype.sum_subsingleton _ e]

lemma map_unitL (σ' : A ≃ B) :
    GrOperad.map (R := R) σ' (unitL R V A) = unitL R V B := by
  rw [unitL, unitL, map_sum]
  refine Fintype.sum_equiv (Equiv.mk (fun e => e.trans σ') (fun e => e.trans σ'.symm)
    (fun e => by ext; simp) (fun e => by ext; simp)) _ _ fun e => ?_
  rw [← GrOperad.map_trans]
  rfl

lemma par_unitL (b : Bool) :
    GrOperad.par (R := R) b (unitL R V A) = if b then 0 else unitL R V A := by
  rw [unitL, map_sum]
  cases b
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [← GrOperad.map_par, GrOperad.par_one]
  · rw [if_pos rfl]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [← GrOperad.map_par, ← GrOperad.par_one (R := R) (P := FreeGrL R V), GrOperad.par_par,
      if_neg (by decide), map_zero]

lemma unitCoeffL_one : unitCoeffL R V Unit (GrOperad.one (R := R) (P := FreeGrL R V)) = 1 := by
  show unitCoeff (grGenPar R V) R Unit (SgnLin.bas (treeSgn (grGenPar R V)) R SetOperad.one) = 1
  rw [unitCoeff_bas, if_pos (by rfl)]

lemma unitCoeffL_map (σ' : A ≃ B) (x : FreeGrL R V A) :
    unitCoeffL R V B (GrOperad.map (R := R) σ' x) = unitCoeffL R V A x := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A x
  exact unitCoeff_map σ' x

lemma unitCoeffL_par (b : Bool) (x : FreeGrL R V A) :
    unitCoeffL R V A (GrOperad.par (R := R) b x) = if b then 0 else unitCoeffL R V A x := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A x
  exact unitCoeff_par b x

variable (R V) in
/-- **The part without unit component** of an operation. -/
noncomputable def secC (A : Type) [Fintype A] [DecidableEq A] : FreeGrL R V A →ₗ[R] FreeGrL R V A :=
  LinearMap.id - (unitCoeffL R V A).smulRight (unitL R V A)

lemma secC_apply (x : FreeGrL R V A) :
    secC R V A x = x - unitCoeffL R V A x • unitL R V A := rfl

lemma secC_map (σ' : A ≃ B) (x : FreeGrL R V A) :
    secC R V B (GrOperad.map (R := R) σ' x) = GrOperad.map (R := R) σ' (secC R V A x) := by
  rw [secC_apply, secC_apply, map_sub, map_smul, unitCoeffL_map, map_unitL]

lemma secC_par (b : Bool) (x : FreeGrL R V A) :
    secC R V A (GrOperad.par (R := R) b x) = GrOperad.par (R := R) b (secC R V A x) := by
  rw [secC_apply, secC_apply, map_sub, map_smul, unitCoeffL_par, par_unitL]
  cases b <;> simp

lemma secC_unit (e : Unit ≃ A) :
    secC R V A (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := FreeGrL R V))) = 0 := by
  rw [secC_apply, unitCoeffL_map, unitCoeffL_one, one_smul, ← unitL_eq, sub_self]

lemma secC_of_unitCoeff {x : FreeGrL R V A} (hx : unitCoeffL R V A x = 0) : secC R V A x = x := by
  rw [secC_apply, hx, zero_smul, sub_zero]

lemma unitCoeffL_secC (x : FreeGrL R V A) : unitCoeffL R V A (secC R V A x) = 0 := by
  rw [secC_apply, map_sub, map_smul]
  by_cases h : Nonempty (Unit ≃ A)
  · obtain ⟨e⟩ := h
    rw [unitL_eq e, unitCoeffL_map, unitCoeffL_one, smul_eq_mul, mul_one, sub_self]
  · have h0 : unitL R V A = 0 := by
      rw [unitL]
      exact Finset.sum_eq_zero fun e _ => absurd ⟨e⟩ h
    rw [h0, map_zero, smul_zero, sub_zero]
    -- an operation in an arity other than one has no unit component
    obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A x
    show unitCoeff (grGenPar R V) R A x = 0
    induction x using induction_bas with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
    | bas c t =>
      rw [map_smul, unitCoeff_bas]
      split_ifs with ht
      · obtain ⟨e, -⟩ := eq_map_one_of_isLeaf ht
        exact absurd ⟨e⟩ h
      · exact smul_zero c

end FreeGrL

/-! ## Merge structures -/

variable (R : Type u) [CommRing R] (W : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]

/-- **A merge structure on a graded linear species**: bilinear, equivariant compositions of
homogeneous elements at an input, adding the parities plus one. -/
structure MergeSp where
  /-- The merge of `x`, of parity `b`, with `y` at the input `q`, in the positions `Fin m`. -/
  val {k l : ℕ} (b : Bool) (x : W (Fin k)) (q : Fin k) (y : W (Fin l)) (m : ℕ)
    (h : m + 1 = k + l) : W (Fin m)
  add_left {k l : ℕ} (b : Bool) (x x' : W (Fin k)) (q : Fin k) (y : W (Fin l)) (m : ℕ)
    (h : m + 1 = k + l) : val b (x + x') q y m h = val b x q y m h + val b x' q y m h
  smul_left {k l : ℕ} (b : Bool) (c : R) (x : W (Fin k)) (q : Fin k) (y : W (Fin l)) (m : ℕ)
    (h : m + 1 = k + l) : val b (c • x) q y m h = c • val b x q y m h
  add_right {k l : ℕ} (b : Bool) (x : W (Fin k)) (q : Fin k) (y y' : W (Fin l)) (m : ℕ)
    (h : m + 1 = k + l) : val b x q (y + y') m h = val b x q y m h + val b x q y' m h
  smul_right {k l : ℕ} (b : Bool) (c : R) (x : W (Fin k)) (q : Fin k) (y : W (Fin l)) (m : ℕ)
    (h : m + 1 = k + l) : val b x q (c • y) m h = c • val b x q y m h
  map_right {k l : ℕ} (b : Bool) (x : W (Fin k)) (q : Fin k) (τ : Fin l ≃ Fin l) (y : W (Fin l))
    (m : ℕ) (h : m + 1 = k + l) :
    val b x q (SymSpecies.map (R := R) τ y) m h
      = SymSpecies.map (R := R) ((posEquivF q l m h).symm.trans
          ((compEquiv (Equiv.refl (Fin k)) τ q).trans (posEquivF q l m h))) (val b x q y m h)
  map_left {k l : ℕ} (b : Bool) (τ : Fin k ≃ Fin k) (x : W (Fin k)) (q : Fin k) (y : W (Fin l))
    (m : ℕ) (h : m + 1 = k + l) :
    val b (SymSpecies.map (R := R) τ x) (τ q) y m h
      = SymSpecies.map (R := R) ((posEquivF q l m h).symm.trans
          ((compEquiv τ (Equiv.refl (Fin l)) q).trans (posEquivF (τ q) l m h))) (val b x q y m h)
  par {k l : ℕ} (b b' : Bool) (x : W (Fin k)) (q : Fin k) (y : W (Fin l)) (m : ℕ)
    (h : m + 1 = k + l) : GrSpecies.par (R := R) b x = x → GrSpecies.par (R := R) b' y = y →
    GrSpecies.par (R := R) (!(xor b b')) (val b x q y m h) = val b x q y m h

namespace MergeSp

variable {R W} (M : MergeSp R W)

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R W)

/-- **The merge function of a merge structure**, on the homogeneous elements. -/
noncomputable def fn : MergeFn (GrGen R W) := fun k l x j y m =>
  if h : j < k ∧ m + 1 = k + l then
    ⟨(M.val x.1.2 x.1.1 ⟨j, h.1⟩ y.1.1 m h.2, !(xor x.1.2 y.1.2)),
      M.par _ _ _ _ _ _ _ x.2 y.2⟩
  else ⟨(0, !(xor x.1.2 y.1.2)), map_zero _⟩

/-- **The merge function is odd.** -/
lemma fn_odd : MergeFn.Odd (grGenPar R W) M.fn := by
  intro k l x j y m
  unfold fn
  split_ifs <;> rfl

lemma fn_val {k l j m : ℕ} (x : GrGen R W k) (y : GrGen R W l) (h : j < k ∧ m + 1 = k + l) :
    (M.fn k l x j y m).1.1 = M.val x.1.2 x.1.1 ⟨j, h.1⟩ y.1.1 m h.2 := by
  unfold fn
  rw [dif_pos h]

lemma fn_par {k l j m : ℕ} (x : GrGen R W k) (y : GrGen R W l) :
    (M.fn k l x j y m).1.2 = !(xor x.1.2 y.1.2) := by
  unfold fn
  split_ifs <;> rfl

/-- **Merge-composing two generators.** -/
lemma mcomp_gen {k l : ℕ} (c : GrGen R W k) (i : Fin k) (g : GrGen R W l) (m : ℕ)
    (h : m + 1 = k + l) :
    mcomp M.fn (grGenPar R W) R i (gen (R := R) (gp := grGenPar R W) c) (gen g)
      = GrOperad.map (R := R) (posEquivF i l m h).symm (gen (M.fn k l c i g m)) :=
  mcomp_gen_gen M.fn c i g m h

/-- **Merging a generator with a linearity relation** lands in the ideal of the linearity
relations. -/
lemma gen_left {n : ℕ} {r : FreeGr R (grGenPar R W) (Fin n)} (hr : r ∈ grLinRel R W n) {k : ℕ}
    (c : GrGen R W k) (i : Fin k) :
    mcomp M.fn (grGenPar R W) R i (gen (R := R) (gp := grGenPar R W) c) r ∈ (𝒥).sub _ := by
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = k + n := ⟨k + n - 1, by have := i.2; omega⟩
  have hi : (i : ℕ) < k ∧ m + 1 = k + n := ⟨i.2, hm⟩
  rcases hr with (⟨b, v, w, hv, hw, rfl⟩ | ⟨b, a, v, hv, rfl⟩) | ⟨b, τ, v, hv, rfl⟩
  · simp only [map_sub, lgen, M.mcomp_gen c i _ m hm]
    rw [← map_sub, ← map_sub]
    refine (𝒥).map_mem _ (gen_sub_mem_add _ _ _ (by simp only [fn_par])
      (by simp only [fn_par]) ?_)
    rw [M.fn_val _ _ hi, M.fn_val _ _ hi, M.fn_val _ _ hi]
    exact M.add_right _ _ _ _ _ _ _
  · simp only [map_sub, map_smul, lgen, M.mcomp_gen c i _ m hm]
    rw [← map_smul, ← map_sub]
    refine (𝒥).map_mem _ (gen_sub_mem_smul _ _ a (by simp only [fn_par]) ?_)
    rw [M.fn_val _ _ hi, M.fn_val _ _ hi]
    exact M.smul_right _ _ _ _ _ _ _
  · rw [map_sub, mcomp_map_right]
    simp only [lgen, M.mcomp_gen c i _ m hm]
    have hρ : (posEquivF i n m hm).symm.trans (compEquiv (Equiv.refl (Fin k)) τ i)
        = ((posEquivF i n m hm).symm.trans ((compEquiv (Equiv.refl (Fin k)) τ i).trans
            (posEquivF i n m hm))).trans (posEquivF i n m hm).symm := by
      ext t
      exact (Equiv.symm_apply_apply (posEquivF i n m hm)
        (compEquiv (Equiv.refl (Fin k)) τ i ((posEquivF i n m hm).symm t))).symm
    have key : ∀ X : FreeGr R (grGenPar R W) (Fin m),
        GrOperad.map (R := R) (compEquiv (Equiv.refl (Fin k)) τ i)
            (GrOperad.map (R := R) (posEquivF i n m hm).symm X)
          = GrOperad.map (R := R) (posEquivF i n m hm).symm (GrOperad.map (R := R)
              ((posEquivF i n m hm).symm.trans ((compEquiv (Equiv.refl (Fin k)) τ i).trans
                (posEquivF i n m hm))) X) := by
      intro X
      rw [← GrOperad.map_trans, ← GrOperad.map_trans, hρ]
      rfl
    rw [key, ← map_sub]
    refine (𝒥).map_mem _ (map_gen_sub_mem _ _ _ (by simp only [fn_par]) ?_)
    rw [M.fn_val _ _ hi, M.fn_val _ _ hi]
    exact M.map_right _ _ _ _ _ _ _

/-- **Merging a linearity relation with a generator** lands in the ideal of the linearity
relations. -/
lemma gen_right {n : ℕ} {r : FreeGr R (grGenPar R W) (Fin n)} (hr : r ∈ grLinRel R W n)
    {k : ℕ} (c : GrGen R W k) (i : Fin n) :
    mcomp M.fn (grGenPar R W) R i r (gen (R := R) (gp := grGenPar R W) c) ∈ (𝒥).sub _ := by
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = n + k := ⟨n + k - 1, by have := i.2; omega⟩
  rcases hr with (⟨b, v, w, hv, hw, rfl⟩ | ⟨b, a, v, hv, rfl⟩) | ⟨b, τ, v, hv, rfl⟩
  · have hi : (i : ℕ) < n ∧ m + 1 = n + k := ⟨i.2, hm⟩
    simp only [map_sub, LinearMap.sub_apply, lgen, M.mcomp_gen _ i c m hm]
    rw [← map_sub, ← map_sub]
    refine (𝒥).map_mem _ (gen_sub_mem_add _ _ _ (by simp only [fn_par])
      (by simp only [fn_par]) ?_)
    rw [M.fn_val _ _ hi, M.fn_val _ _ hi, M.fn_val _ _ hi]
    exact M.add_left _ _ _ _ _ _ _
  · have hi : (i : ℕ) < n ∧ m + 1 = n + k := ⟨i.2, hm⟩
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, lgen,
      M.mcomp_gen _ i c m hm]
    rw [← map_smul, ← map_sub]
    refine (𝒥).map_mem _ (gen_sub_mem_smul _ _ a (by simp only [fn_par]) ?_)
    rw [M.fn_val _ _ hi, M.fn_val _ _ hi]
    exact M.smul_left _ _ _ _ _ _ _
  · obtain ⟨i', rfl⟩ := τ.surjective i
    have hi : ((τ i' : Fin n) : ℕ) < n ∧ m + 1 = n + k := ⟨(τ i').2, hm⟩
    have hi' : (i' : ℕ) < n ∧ m + 1 = n + k := ⟨i'.2, hm⟩
    rw [map_sub, LinearMap.sub_apply, mcomp_map_left]
    simp only [lgen, M.mcomp_gen _ _ c m hm]
    have key : ∀ X : FreeGr R (grGenPar R W) (Fin m),
        GrOperad.map (R := R) (compEquiv τ (Equiv.refl (Fin k)) i')
            (GrOperad.map (R := R) (posEquivF i' k m hm).symm X)
          = GrOperad.map (R := R) (posEquivF (τ i') k m hm).symm (GrOperad.map (R := R)
              ((posEquivF i' k m hm).symm.trans ((compEquiv τ (Equiv.refl (Fin k)) i').trans
                (posEquivF (τ i') k m hm))) X) := by
      intro X
      rw [← GrOperad.map_trans, ← GrOperad.map_trans]
      congr 2
      ext t
      simp
    rw [key, ← map_sub]
    refine (𝒥).map_mem _ (map_gen_sub_mem _ _ _ (by simp only [fn_par]) ?_)
    rw [M.fn_val _ _ hi, M.fn_val _ _ hi']
    exact M.map_left _ _ _ _ _ _ _

/-- **A merge structure is compatible with the linearity relations.** -/
theorem relHyp : RelHyp M.fn (grGenPar R W) R (grLinRel R W) where
  barD_eq _ _ hr := barD_of_linRel _ hr
  unitCoeff_eq _ _ hr := unitCoeff_of_linRel hr
  homog _ _ hr := par_of_linRel hr
  gen_left _ _ hr _ c i := M.gen_left hr c i
  gen_right _ _ hr _ c i := M.gen_right hr c i

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The bar differential of a merge structure**, descended to the free graded operad on `W`:
the signed sum of the contractions of the edges of a tree, merging the decorations. -/
noncomputable def d (A : Type) [Fintype A] [DecidableEq A] : FreeGrL R W A →ₗ[R] FreeGrL R W A :=
  Submodule.mapQ _ _ (barD M.fn (grGenPar R W) R A) fun _ hz =>
    barD_mem M.fn M.fn_odd M.relHyp hz

lemma d_proj (x : FreeGr R (grGenPar R W) A) :
    M.d A ((𝒥).proj A x) = (𝒥).proj A (barD M.fn (grGenPar R W) R A x) := rfl

/-- Merge-composition with a fixed outer operation, descended. -/
noncomputable def mcRight (i : A) (x : FreeGr R (grGenPar R W) A) :
    FreeGrL R W B →ₗ[R] FreeGrL R W (Without A i ⊕ B) :=
  Submodule.mapQ _ _ (mcomp M.fn (grGenPar R W) R i x) fun _ hz =>
    mcomp_mem_right M.fn M.fn_odd M.relHyp x hz i

lemma mcRight_proj (i : A) (x : FreeGr R (grGenPar R W) A) (y : FreeGr R (grGenPar R W) B) :
    M.mcRight i x ((𝒥).proj B y) = (𝒥).proj _ (mcomp M.fn (grGenPar R W) R i x y) := rfl

/-- **Merge-composition of a merge structure**, descended to the free graded operad on `W`: the
root of the second tree merged into the vertex of the first carrying the input. -/
noncomputable def mc (i : A) :
    FreeGrL R W A →ₗ[R] FreeGrL R W B →ₗ[R] FreeGrL R W (Without A i ⊕ B) :=
  Submodule.liftQ _
    { toFun := fun x => M.mcRight i x
      map_add' := fun x x' => by
        refine LinearMap.ext fun z => ?_
        obtain ⟨y, rfl⟩ := (𝒥).proj_surjective B z
        simp only [mcRight_proj, LinearMap.add_apply, map_add]
      map_smul' := fun r x => by
        refine LinearMap.ext fun z => ?_
        obtain ⟨y, rfl⟩ := (𝒥).proj_surjective B z
        simp only [mcRight_proj, LinearMap.smul_apply, RingHom.id_apply, map_smul] }
    (by
      intro x hx
      refine LinearMap.ext fun z => ?_
      obtain ⟨y, rfl⟩ := (𝒥).proj_surjective B z
      show (𝒥).proj _ (mcomp M.fn (grGenPar R W) R i x y) = 0
      exact ((𝒥).proj_eq_zero_iff _).2 (mcomp_mem_left M.fn M.fn_odd M.relHyp hx y i))

lemma mc_proj (i : A) (x : FreeGr R (grGenPar R W) A) (y : FreeGr R (grGenPar R W) B) :
    M.mc i ((𝒥).proj A x) ((𝒥).proj B y) = (𝒥).proj _ (mcomp M.fn (grGenPar R W) R i x y) :=
  rfl

/-! ## Laws of the descended operations -/

variable {D : Type} [Fintype D] [DecidableEq D]

lemma proj_comp' (i : A) (x : FreeGr R (grGenPar R W) A) (y : FreeGr R (grGenPar R W) B) :
    (𝒥).proj _ (GrOperad.comp (R := R) i x y)
      = GrOperad.comp (R := R) i ((𝒥).proj A x) ((𝒥).proj B y) := rfl

lemma proj_map'' (e : A ≃ B) (x : FreeGr R (grGenPar R W) A) :
    (𝒥).proj B (GrOperad.map (R := R) e x) = GrOperad.map (R := R) e ((𝒥).proj A x) := rfl

lemma proj_par' (b : Bool) (x : FreeGr R (grGenPar R W) A) :
    (𝒥).proj A (GrOperad.par (R := R) b x) = GrOperad.par (R := R) b ((𝒥).proj A x) := rfl

lemma proj_tw' (e : Bool) (x : FreeGr R (grGenPar R W) A) :
    (𝒥).proj A (GrSpecies.tw (R := R) (V := FreeGr R (grGenPar R W)) e x)
      = GrOperad.tw (R := R) e ((𝒥).proj A x) := by
  rw [GrSpecies.tw_apply, GrOperad.tw_apply, map_add, map_smul]
  rfl

/-- **The bar differential of a composite**:
`d (x ∘ᵢ y) = d x ∘ᵢ y + (-1)^|x| x ∘ᵢ d y + x ⊛ᵢ y`. -/
theorem d_comp (i : A) (X : FreeGrL R W A) (Y : FreeGrL R W B) :
    M.d _ (GrOperad.comp (R := R) i X Y)
      = GrOperad.comp (R := R) i (M.d A X) Y
        + GrOperad.comp (R := R) i (GrOperad.tw (R := R) true X) (M.d B Y) + M.mc i X Y := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective B Y
  rw [← proj_comp', d_proj, barD_comp M.fn_odd, map_add, map_add, ← proj_tw']
  rfl

/-- **The bar differential vanishes on the generators.** -/
theorem d_gen {k : ℕ} (g : GrGen R W k) :
    M.d (Fin k) ((𝒥).proj _ (gen (R := R) (gp := grGenPar R W) g)) = 0 := by
  rw [d_proj, barD_gen, map_zero]

/-- **The bar differential commutes with relabellings.** -/
theorem map_d (e : A ≃ B) (X : FreeGrL R W A) :
    GrOperad.map (R := R) e (M.d A X) = M.d B (GrOperad.map (R := R) e X) := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  rw [d_proj, ← proj_map'', map_barD, ← proj_map'', d_proj]

/-- **The bar differential is odd.** -/
theorem par_d (b : Bool) (X : FreeGrL R W A) :
    GrOperad.par (R := R) b (M.d A X) = M.d A (GrOperad.par (R := R) (!b) X) := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  rw [d_proj, ← proj_par', par_barD M.fn_odd, ← proj_par', d_proj]

/-- **Merge-composition commutes with relabellings.** -/
theorem mc_map {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (σ' : A ≃ A') (τ : B ≃ B') (i : A) (X : FreeGrL R W A) (Y : FreeGrL R W B) :
    M.mc (σ' i) (GrOperad.map (R := R) σ' X) (GrOperad.map (R := R) τ Y)
      = GrOperad.map (R := R) (compEquiv σ' τ i) (M.mc i X Y) := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective B Y
  rw [← proj_map'', ← proj_map'', mc_proj, mc_proj, mcomp_map, proj_map'']

/-- **Merging at an input other than the one composed at**:
`(x ∘ᵢ y) ⊛ₖ z = (-1)^{|y||z|} (x ⊛ₖ z) ∘ᵢ y`. -/
theorem mc_comp_par {i k : A} (hik : i ≠ k) (X : FreeGrL R W A) {q r : Bool}
    {Y : FreeGrL R W B} {Z : FreeGrL R W D} (hY : GrOperad.par (R := R) q Y = Y)
    (hZ : GrOperad.par (R := R) r Z = Z) :
    GrOperad.map (R := R) (parEquiv hik B D)
        (M.mc (Sum.inl ⟨k, Ne.symm hik⟩) (GrOperad.comp (R := R) i X Y) Z)
      = σ R (q && r) • GrOperad.comp (R := R) (Sum.inl ⟨i, hik⟩) (M.mc k X Z) Y := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective B Y
  obtain ⟨z, rfl⟩ := (𝒥).proj_surjective D Z
  rw [← hY, ← hZ, ← proj_par', ← proj_par', ← proj_comp', mc_proj, ← proj_map'',
    mcomp_comp_par M.fn M.fn_odd hik x (GrOperad.par_par_self (R := R) q y)
      (GrOperad.par_par_self (R := R) r z), map_smul]
  rfl

/-- **Merging into the inner factor of a composite**: `(x ∘ᵢ y) ⊛ⱼ z = (-1)^{|x|} x ∘ᵢ (y ⊛ⱼ z)`,
for `y` without unit component. -/
theorem mc_comp_inner (i : A) (j : B) (X : FreeGrL R W A) {Y : FreeGrL R W B}
    (hY : FreeGrL.unitCoeffL R W B Y = 0) (Z : FreeGrL R W D) :
    GrOperad.map (R := R) (seqEquiv i j D)
        (M.mc (Sum.inr j) (GrOperad.comp (R := R) i X Y) Z)
      = GrOperad.comp (R := R) i (GrOperad.tw (R := R) true X) (M.mc j Y Z) := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective B Y
  obtain ⟨z, rfl⟩ := (𝒥).proj_surjective D Z
  rw [← proj_comp', mc_proj, ← proj_map'', mcomp_comp_inner M.fn M.fn_odd i j x y z hY,
    ← proj_tw']
  rfl

/-- **Composing into a merge-composite at an input of its inner factor**:
`(x ⊛ᵢ y) ∘ⱼ z = x ⊛ᵢ (y ∘ⱼ z)`, for `y` without unit component. -/
theorem comp_mc_outer (i : A) (j : B) (X : FreeGrL R W A) {Y : FreeGrL R W B}
    (hY : FreeGrL.unitCoeffL R W B Y = 0) (Z : FreeGrL R W D) :
    GrOperad.map (R := R) (seqEquiv i j D)
        (GrOperad.comp (R := R) (Sum.inr j) (M.mc i X Y) Z)
      = M.mc i X (GrOperad.comp (R := R) j Y Z) := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective B Y
  obtain ⟨z, rfl⟩ := (𝒥).proj_surjective D Z
  rw [mc_proj, ← proj_comp', ← proj_map'', comp_mcomp_outer M.fn i j x y z hY, ← proj_comp',
    mc_proj]

/-- **Merge-composing two generators** merges them. -/
theorem mc_gen {k l : ℕ} (c : GrGen R W k) (i : Fin k) (g : GrGen R W l) (m : ℕ)
    (h : m + 1 = k + l) :
    M.mc i ((𝒥).proj _ (gen (R := R) (gp := grGenPar R W) c))
        ((𝒥).proj _ (gen (R := R) (gp := grGenPar R W) g))
      = GrOperad.map (R := R) (posEquivF i l m h).symm
          ((𝒥).proj _ (gen (R := R) (gp := grGenPar R W) (M.fn k l c i g m))) := by
  rw [mc_proj, M.mcomp_gen c i g m h, proj_map'']

/-- **Merge-composing with a unit** vanishes. -/
theorem mc_unit_left (e : Unit ≃ A) (i : A) (Y : FreeGrL R W B) :
    M.mc i (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := FreeGrL R W))) Y = 0 := by
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective B Y
  show (𝒥).proj _ (mcomp M.fn (grGenPar R W) R i (GrOperad.map (R := R) e
    (SgnLin.bas (treeSgn (grGenPar R W)) R SetOperad.one)) y) = 0
  rw [SgnLin.map_bas, mcomp_leaf_left M.fn (by rfl) i y, map_zero]

theorem mc_unit_right (e : Unit ≃ B) (i : A) (X : FreeGrL R W A) :
    M.mc i X (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := FreeGrL R W))) = 0 := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  show (𝒥).proj _ (mcomp M.fn (grGenPar R W) R i x (GrOperad.map (R := R) e
    (SgnLin.bas (treeSgn (grGenPar R W)) R SetOperad.one))) = 0
  rw [SgnLin.map_bas, mcomp_leaf_right M.fn (by rfl) i x, map_zero]

end MergeSp

end Operad
