/-
# The universal property of the cut cooperad without projectivity

Let `V` be a graded linear species without elements without inputs and `C` a conilpotent
coaugmented graded cooperad, over a `ℚ`-algebra `R`. **Every morphism `ψ : C̄ → V` lifts to a
coaugmented morphism of graded cooperads `C → T^c(V)`** (`FreeGrL.liftCut`), with no projectivity
hypothesis; so the coaugmented morphisms `C → T^c(V)` are the morphisms `C̄ → V`
(`FreeGrL.cofreeHomEquivCut`, `FreeGrL.existsUnique_liftCut`). `Operad/CutCofreeConil.lean` proves
this when in each arity the reduced cooperations or the elements of `V` form a projective module,
by transposition through scalar functionals; here the lift is built in `T^c(V)` itself.

* **The components.** `f₁` is `ψ` followed by the generators, and `(n - 1) fₙ = ∑ fₐ ⋆ f_b` over
  `a + b = n` in the convolution operad of `C` and the free graded operad on `V`
  (`CutLift.fN`): the equation the components of a morphism satisfy, grafting the two parts of
  the `n - 1` cuts of a tree with `n` vertices.
* **The Maurer–Cartan equation in the cobar construction.** With `τₙ = ι ∘ fₙ` into `Ω T^c(V)`,
  `d τₙ = -∑ τₐ ⋆ τ_b` over `a + b = n` (`CutLift.appDer_τ`), by induction on `n`. The right
  side `X` is a cycle (`CutLift.dL_X`): the associator of the odd family `∑ τₘ` vanishes, weight
  by weight (`CutLift.W_eq_zero`). The merge `h` of two adjacent vertices sends `X` to
  `-(n - 1) τₙ` (`CutLift.hL_X`), and the contraction `d h + h d = n - 1` of the bar–cobar
  resolution in weight `n` gives the equation.
* **Finiteness.** `fₙ` vanishes on the stage `k` of the coradical filtration for `n > 2^k`
  (`CutLift.fN_filt`), so the sum `f̄ = ∑ fₙ` is a linear map (`CutLift.fbarL`), and it satisfies
  `(ι ⋆ ι) ∘ f̄ = (ι f̄) ⋆ (ι f̄)` as sums of trees with two vertices over the nonempty sets of
  inputs (`CutLift.jj_fbar`).
* **The decompositions.** A sum of trees with two vertices of the cobar construction determines
  its terms up to unit components (`CutCobar.tw2_inj`), so `f̄` respects the decompositions at
  the nonempty sets of inputs up to unit components (`CutLift.secC_decomp_fbar`). The lift is
  `f = ε · 1 + f̄` (`CutLift.liftL`). Its unit components are given by the counit laws of the two
  cooperads (`CutLift.rTensor_unitCoeffL_decomp`, `CutLift.lTensor_unitCoeffL_decomp`), a
  tensor with vanishing reduced part and unit coefficients vanishes (`CutLift.tensor_eq_zero`),
  and there are no trees without inputs; so `f` respects the decompositions at the splittings
  (`CutLift.decomp_liftL_split`), hence all of them (`GrCooperad.decomp_app_of_split`).

Species with elements without inputs are not treated.
-/
import Operad.CutCobar
import Operad.CutCofreeConil
import Operad.FreeGrGraft
import Operad.GrCooperadSplit

universe u v w

namespace Operad

open Sym GerBV FreeGrL FreeGr
open scoped TensorProduct

namespace CutLift

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒞" => FreeGrL R V
local notation "Ω" => CutCobar.Om R V

/-! ## The components -/

variable (ψ : GrSpeciesHom R (GrCooperad.Red R C) V)

/-- **The component with one vertex**: `ψ` on the reduced part, as generators. -/
noncomputable def f1 : GrOperad.Inv R (ConvOp R C 𝒞) :=
  ⟨fun A _ _ => ConvOp.of ((FreeGrL.ι R V).app A ∘ₗ ψ.app A ∘ₗ GrCooperad.Red.proj R C A),
    fun A B _ _ _ _ e => by
      show ConvOp.mapC e (ConvOp.of _) = ConvOp.of _
      ext x
      rw [ConvOp.mapC_apply]
      show GrOperad.map (R := R) e ((FreeGrL.ι R V).app A (ψ.app A (GrCooperad.Red.proj R C A
          (SymSpecies.map (R := R) e.symm x)))) = (FreeGrL.ι R V).app B (ψ.app B
          (GrCooperad.Red.proj R C B x))
      rw [show GrCooperad.Red.proj R C A (SymSpecies.map (R := R) e.symm x)
          = SymSpecies.map (R := R) e.symm (GrCooperad.Red.proj R C B x) from rfl,
        ψ.app_map, (FreeGrL.ι R V).app_map]
      show GrOperad.map (R := R) e (GrOperad.map (R := R) e.symm _) = _
      rw [← GrOperad.map_trans, Equiv.symm_trans_self, GrOperad.map_refl]⟩

lemma f1_apply (x : C A) :
    ConvOp.toLin ((f1 ψ).1 A) x = (FreeGrL.ι R V).app A (ψ.app A (GrCooperad.Red.proj R C A x)) :=
  rfl

variable [Algebra ℚ R]

/-- **The components** `fₙ`: `f₁`, and `(n - 1) fₙ = ∑_{a + b = n} fₐ ⋆ f_b`. -/
noncomputable def fN : ℕ → GrOperad.Inv R (ConvOp R C 𝒞)
  | 0 => 0
  | 1 => f1 ψ
  | n + 2 => algebraMap ℚ R ((n + 1 : ℚ)⁻¹) •
      ∑ a : Fin (n + 1), GrOperad.Inv.star R _ (fN (a.1 + 1)) (fN (n + 1 - a.1))
termination_by n => n
decreasing_by
  all_goals have := a.isLt
  all_goals omega

lemma fN_zero : fN ψ 0 = 0 := by rw [fN]

lemma fN_one : fN ψ 1 = f1 ψ := by rw [fN]

lemma fN_add_two (n : ℕ) :
    fN ψ (n + 2) = algebraMap ℚ R ((n + 1 : ℚ)⁻¹) •
      ∑ a : Fin (n + 1), GrOperad.Inv.star R _ (fN ψ (a.1 + 1)) (fN ψ (n + 1 - a.1)) := by
  rw [fN]

/-- **The recursion** `(n + 1) f_{n+2} = ∑ f_{a+1} ⋆ f_{n+1-a}`. -/
lemma smul_fN_add_two (n : ℕ) :
    ((n + 1 : ℕ) : R) • fN ψ (n + 2)
      = ∑ a : Fin (n + 1), GrOperad.Inv.star R _ (fN ψ (a.1 + 1)) (fN ψ (n + 1 - a.1)) := by
  rw [fN_add_two, smul_smul]
  have h : ((n + 1 : ℕ) : R) * algebraMap ℚ R ((n + 1 : ℚ)⁻¹) = 1 := by
    rw [show ((n + 1 : ℕ) : R) = algebraMap ℚ R ((n + 1 : ℕ) : ℚ) from (map_natCast _ _).symm,
      ← map_mul, Nat.cast_succ, mul_inv_cancel₀ (by positivity), map_one]
  rw [h, one_smul]

/-! ## Weights and parities of the components -/

omit [Algebra ℚ R] in
/-- **The numbers of vertices add under composition.** -/
lemma comp_mem_vx (r : A) {i j : ℕ} {x : 𝒞 A} {y : 𝒞 B} (hx : x ∈ vx R V i A)
    (hy : y ∈ vx R V j B) : GrOperad.comp (R := R) r x y ∈ vx R V (i + j) _ := by
  refine mem_eig.2 ?_
  have h : (derSp (GrSpEnd.id R V)).app _ (GrOperad.comp (R := R) r x y)
      = GrOperad.comp (R := R) r ((derSp (GrSpEnd.id R V)).app A x) y
        + GrOperad.comp (R := R) r x ((derSp (GrSpEnd.id R V)).app B y) :=
    ((derSp (GrSpEnd.id R V)).app_comp r x y).trans (congrArg (fun z => GrOperad.comp (R := R) r
      ((derSp (GrSpEnd.id R V)).app A x) y + GrOperad.comp (R := R) r z
        ((derSp (GrSpEnd.id R V)).app B y)) (GrOperad.tw_false x))
  rw [h, mem_eig.1 hx, mem_eig.1 hy, LinearMap.map_smul₂, map_smul, ← add_smul, Nat.cast_add]

omit [Algebra ℚ R] in
lemma par_mem_vx (b : Bool) {i : ℕ} {x : 𝒞 A} (hx : x ∈ vx R V i A) :
    GrOperad.par (R := R) b x ∈ vx R V i A :=
  mem_eig.2 (((derSp (GrSpEnd.id R V)).app_par b x).trans (by
    rw [Bool.xor_false, mem_eig.1 hx, map_smul]))

omit [Algebra ℚ R] in
lemma map_mem_vx (e : A ≃ B) {i : ℕ} {x : 𝒞 A} (hx : x ∈ vx R V i A) :
    GrOperad.map (R := R) e x ∈ vx R V i B :=
  mem_eig.2 (((derSp (GrSpEnd.id R V)).app_map e x).trans (by
    rw [mem_eig.1 hx, map_smul]))

omit [Algebra ℚ R] in
lemma f1_mem (x : C A) : ConvOp.toLin ((f1 ψ).1 A) x ∈ vx R V 1 A :=
  ι_mem_vx _

omit [Algebra ℚ R] in
lemma isPar_f1 : GrOperad.Inv.IsPar false (f1 ψ) := by
  intro A _ _
  show ConvOp.parC false ((f1 ψ).1 A) = (f1 ψ).1 A
  rw [ConvOp.parC_eq_self_iff]
  intro c x
  rw [Bool.xor_false]
  show (FreeGrL.ι R V).app A (ψ.app A (GrCooperad.Red.proj R C A (GrSpecies.par (R := R) c x)))
    = GrOperad.par (R := R) c ((FreeGrL.ι R V).app A (ψ.app A (GrCooperad.Red.proj R C A x)))
  rw [← GrCooperad.Red.par_proj, ψ.app_par, (FreeGrL.ι R V).app_par]
  rfl

omit [Algebra ℚ R] in
lemma isPar_sum {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {ι' : Type}
    (s : Finset ι') {b : Bool} {q : ι' → GrOperad.Inv R Q}
    (hq : ∀ i ∈ s, GrOperad.Inv.IsPar b (q i)) : GrOperad.Inv.IsPar b (∑ i ∈ s, q i) := by
  classical
  intro A _ _
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    show GrOperad.par (R := R) b ((q j).1 A + (∑ i ∈ s, q i).1 A) = (q j).1 A + (∑ i ∈ s, q i).1 A
    rw [map_add, hq j (Finset.mem_insert_self j s) A,
      ih (fun i hi => hq i (Finset.mem_insert_of_mem hi))]

omit [Algebra ℚ R] in
lemma isPar_smul {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {b : Bool}
    (c : R) {q : GrOperad.Inv R Q} (hq : GrOperad.Inv.IsPar b q) :
    GrOperad.Inv.IsPar b (c • q) := fun A _ _ => by
  show GrOperad.par (R := R) b (c • q.1 A) = c • q.1 A
  rw [map_smul, hq A]

omit [Algebra ℚ R] in
lemma inv_sum_apply {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {ι' : Type}
    (s : Finset ι') (q : ι' → GrOperad.Inv R Q) (A : Type) [Fintype A] [DecidableEq A] :
    (∑ i ∈ s, q i).1 A = ∑ i ∈ s, (q i).1 A := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    rfl

/-- **The components are even.** -/
lemma isPar_fN (n : ℕ) : GrOperad.Inv.IsPar false (fN ψ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [fN_zero]; exact fun A _ _ => map_zero _
    | 1, _ => rw [fN_one]; exact isPar_f1 ψ
    | n + 2, ih =>
      rw [fN_add_two]
      refine isPar_smul _ (isPar_sum _ fun a _ => ?_)
      have h := GrOperad.Inv.isPar_star (ih (a.1 + 1) (by omega)) (ih (n + 1 - a.1) (by omega))
      rwa [Bool.xor_false] at h

/-- **The component `fₙ` has values with `n` vertices.** -/
lemma fN_mem (n : ℕ) (hn : 1 ≤ n) (x : C A) : ConvOp.toLin ((fN ψ n).1 A) x ∈ vx R V n A := by
  induction n using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    match n, ih, hn with
    | 0, _, hn => omega
    | 1, _, _ => rw [fN_one]; exact f1_mem ψ x
    | n + 2, ih, _ =>
      rw [fN_add_two]
      show algebraMap ℚ R ((n + 1 : ℚ)⁻¹) • ConvOp.toLin ((∑ a : Fin (n + 1),
        GrOperad.Inv.star R _ (fN ψ (a.1 + 1)) (fN ψ (n + 1 - a.1))).1 A) x ∈ vx R V (n + 2) A
      refine Submodule.smul_mem _ _ ?_
      rw [inv_sum_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
      refine Submodule.sum_mem _ fun a _ => ?_
      have ha := a.isLt
      exact ConvOp.toLin_star_mem (F := fun A _ _ => vx R V (a.1 + 1) A)
        (G := fun A _ _ => vx R V (n + 1 - a.1) A) (H := fun A _ _ => vx R V (n + 2) A)
        (fun _ _ _ b _ hy => par_mem_vx b hy) (fun _ _ _ _ _ _ e _ hy => map_mem_vx e hy)
        (fun _ _ _ _ _ _ i _ _ hy hz => by
          have := comp_mem_vx i hy hz
          rwa [show a.1 + 1 + (n + 1 - a.1) = n + 2 by omega] at this)
        (fun A _ _ x => ih (a.1 + 1) (by omega) (by omega) x)
        (fun A _ _ x => ih (n + 1 - a.1) (by omega) (by omega) x) A x

/-! ## In the cobar construction -/

omit [Algebra ℚ R] in
/-- **Composing with the universal twisting morphism** of the cobar construction. -/
noncomputable def postι (q : GrOperad.Inv R (ConvOp R C 𝒞)) :
    GrOperad.Inv R (ConvOp R C Ω) :=
  ⟨fun A _ _ => ConvOp.of (CutCobar.jL R V A ∘ₗ ConvOp.toLin (q.1 A)), fun A B _ _ _ _ e => by
    show ConvOp.mapC e (ConvOp.of _) = ConvOp.of _
    ext x
    rw [ConvOp.mapC_apply]
    show GrOperad.map (R := R) e (CutCobar.jL R V A (ConvOp.toLin (q.1 A)
      (SymSpecies.map (R := R) e.symm x))) = CutCobar.jL R V B (ConvOp.toLin (q.1 B) x)
    rw [← CutCobar.jL_map]
    exact congrArg (CutCobar.jL R V B) (congrArg (fun f => ConvOp.toLin f x) (q.2 A B e))⟩

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
lemma postι_apply (q : GrOperad.Inv R (ConvOp R C 𝒞)) (x : C A) :
    ConvOp.toLin ((postι q).1 A) x = CutCobar.jL R V A (ConvOp.toLin (q.1 A) x) := rfl

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
/-- **Composing with `ι` changes the parity.** -/
lemma isPar_postι {q : GrOperad.Inv R (ConvOp R C 𝒞)} (hq : GrOperad.Inv.IsPar false q) :
    GrOperad.Inv.IsPar true (postι q) := by
  intro A _ _
  show ConvOp.parC true ((postι q).1 A) = (postι q).1 A
  rw [ConvOp.parC_eq_self_iff]
  intro c x
  have h := ConvOp.parC_eq_self_iff.1 (show ConvOp.parC false (q.1 A) = q.1 A from hq A) c x
  rw [postι_apply, postι_apply, h, Bool.xor_false, Bool.xor_true]
  exact CutCobar.jL_par c _

/-- **The components in the cobar construction**, `τₙ = ι ∘ fₙ`. -/
noncomputable abbrev τ (n : ℕ) : GrOperad.Inv R (ConvOp R C Ω) := postι (fN ψ n)

lemma isPar_τ (n : ℕ) : GrOperad.Inv.IsPar true (τ ψ n) := isPar_postι (isPar_fN ψ n)

lemma τ_mem (n : ℕ) (hn : 1 ≤ n) (x : C A) : ConvOp.toLin ((τ ψ n).1 A) x ∈ CutCobar.wt R V n A :=
  CutCobar.jL_mem_wt (fN_mem ψ n hn x)

/-- **The convolution squares of the components with `n` vertices in all**:
`Xₙ = ∑_{a + b = n} τₐ ⋆ τ_b`. -/
noncomputable def X (n : ℕ) : GrOperad.Inv R (ConvOp R C Ω) :=
  ∑ p ∈ Finset.antidiagonal n, GrOperad.Inv.star R _ (τ ψ p.1) (τ ψ p.2)

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
lemma postι_zero : postι (0 : GrOperad.Inv R (ConvOp R C 𝒞)) = 0 :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => by
    show ConvOp.of (CutCobar.jL R V A ∘ₗ ConvOp.toLin (0 : ConvOp R C 𝒞 A)) = 0
    ext x
    show CutCobar.jL R V A 0 = 0
    exact map_zero _)

lemma τ_zero : τ ψ 0 = 0 :=
  (congrArg postι (fN_zero ψ)).trans postι_zero

/-! ## Merging the two vertices of a convolution square -/

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
/-- An even family has homogeneous values on homogeneous elements. -/
lemma par_par_even {f : GrOperad.Inv R (ConvOp R C 𝒞)} (hf : GrOperad.Inv.IsPar false f)
    (b : Bool) (a : C A) :
    GrOperad.par (R := R) b (ConvOp.toLin (f.1 A) (GrSpecies.par (R := R) b a))
      = ConvOp.toLin (f.1 A) (GrSpecies.par (R := R) b a) := by
  have h := ConvOp.parC_eq_self_iff.1 (show ConvOp.parC false (f.1 A) = f.1 A from hf A) b a
  rw [Bool.xor_false] at h
  rw [h, GrOperad.par_par, if_pos rfl]

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
lemma isParC_of_isPar {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {b : Bool}
    {f : GrOperad.Inv R (ConvOp R C Q)} (hf : GrOperad.Inv.IsPar b f) (A : Type) [Fintype A]
    [DecidableEq A] : ConvOp.IsParC b (f.1 A) :=
  ConvOp.parC_eq_self_iff.1 (hf A)

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
/-- **Merging the two vertices of the terms of a convolution square**:
`h ((ι f) ⋆ (ι g)) = -ι (f ⋆ g)` for even `f`, `g` without unit components. -/
lemma hM_star {f g : GrOperad.Inv R (ConvOp R C 𝒞)} (hf : GrOperad.Inv.IsPar false f)
    (hg : GrOperad.Inv.IsPar false g)
    (hf0 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      unitCoeffL R V A (ConvOp.toLin (f.1 A) x) = 0)
    (hg0 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      unitCoeffL R V A (ConvOp.toLin (g.1 A) x) = 0) (x : C A) :
    CutCobar.hL R V A (ConvOp.toLin ((GrOperad.Inv.star R _ (postι f) (postι g)).1 A) x)
      = -CutCobar.jL R V A (ConvOp.toLin ((GrOperad.Inv.star R _ f g).1 A) x) := by
  rw [GrOperad.Inv.star_apply, GrOperad.Inv.star_apply, ConvOp.toLin_sum, ConvOp.toLin_sum,
    LinearMap.coe_sum, LinearMap.coe_sum, Finset.sum_apply, Finset.sum_apply, map_sum, map_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  show CutCobar.hL R V A (ConvOp.toLin (ConvOp.mapC (splitEquiv S)
      (ConvOp.compC none ((postι f).1 (SOut S)) ((postι g).1 (SIn S)))) x)
    = -CutCobar.jL R V A (ConvOp.toLin (ConvOp.mapC (splitEquiv S)
      (ConvOp.compC none (f.1 (SOut S)) (g.1 (SIn S)))) x)
  rw [ConvOp.mapC_apply, ConvOp.mapC_apply, CutCobar.hL_map, CutCobar.jL_map, ← map_neg]
  congr 1
  show CutCobar.hL R V _ (ConvOp.mu none (ConvOp.kap ((postι f).1 (SOut S)) ((postι g).1 (SIn S))
      (GrCooperad.decomp (R := R) none _)))
    = -CutCobar.jL R V _ (ConvOp.mu none (ConvOp.kap (f.1 (SOut S)) (g.1 (SIn S))
      (GrCooperad.decomp (R := R) none _)))
  rw [ConvOp.kap_hom _ (isParC_of_isPar (isPar_postι hg) (SIn S)),
    ConvOp.kap_hom _ (isParC_of_isPar hg (SIn S))]
  generalize GrCooperad.decomp (R := R) (C := C) (A := SOut S) (B := SIn S) none _ = t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul, ConvOp.mu_tmul, LinearMap.comp_apply, postι_apply,
      GrSpecies.tw_false]
    have e1 := CutCobar.hL_comp_jL (par_par_even hf false a) none (ConvOp.toLin (g.1 _) b)
    have e2 := CutCobar.hL_comp_jL (par_par_even hf true a) none (ConvOp.toLin (g.1 _) b)
    rw [secC_of_unitCoeff (hf0 _ _), secC_of_unitCoeff (hg0 _ b)] at e1
    rw [secC_of_unitCoeff (hf0 _ _), secC_of_unitCoeff (hg0 _ b)] at e2
    conv_rhs => rw [← GrSpecies.par_add (R := R) a]
    simp only [GrSpecies.tw_apply, map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply,
      e1, e2, σ_true, σ_false, Bool.not_false, Bool.not_true, one_smul, neg_smul, neg_add]
  | add u u' hu hu' => simp only [map_add, hu, hu', neg_add]

/-! ## Weights in the cobar construction -/

lemma τ_mem' (n : ℕ) (x : C A) : ConvOp.toLin ((τ ψ n).1 A) x ∈ CutCobar.wt R V n A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [τ_zero]
    exact zero_mem _
  · exact τ_mem ψ n hn x

/-- **The products of components have the sums of their weights.** -/
lemma star_τ_mem (p q : ℕ) (x : C A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (τ ψ p) (τ ψ q)).1 A) x ∈ CutCobar.wt R V (p + q) A :=
  ConvOp.toLin_star_mem (F := fun A _ _ => CutCobar.wt R V p A)
    (G := fun A _ _ => CutCobar.wt R V q A) (H := fun A _ _ => CutCobar.wt R V (p + q) A)
    (fun _ _ _ b _ hy => CutCobar.par_mem_wt b hy)
    (fun _ _ _ _ _ _ e _ hy => CutCobar.map_mem_wt e hy)
    (fun _ _ _ _ _ _ i _ _ hy hz => CutCobar.comp_mem_wt i hy hz)
    (fun _ _ _ x => τ_mem' ψ p x) (fun _ _ _ x => τ_mem' ψ q x) A x

lemma X_mem (n : ℕ) (x : C A) : ConvOp.toLin ((X ψ n).1 A) x ∈ CutCobar.wt R V n A := by
  rw [X, inv_sum_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun p hp => ?_
  have := star_τ_mem ψ (p.1) (p.2) x
  rwa [Finset.mem_antidiagonal.1 hp] at this

/-! ## Unit components -/

/-- **The components have no unit component.** -/
lemma fN_unit (n : ℕ) (x : C A) : unitCoeffL R V A (ConvOp.toLin ((fN ψ n).1 A) x) = 0 := by
  induction n using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [fN_zero]; exact map_zero _
    | 1, _ => rw [fN_one, f1_apply]; exact FreeGrL.unitCoeffL_ι _
    | n + 2, ih =>
      rw [fN_add_two]
      show unitCoeffL R V A (algebraMap ℚ R ((n + 1 : ℚ)⁻¹) • ConvOp.toLin ((∑ a : Fin (n + 1),
        GrOperad.Inv.star R _ (fN ψ (a.1 + 1)) (fN ψ (n + 1 - a.1))).1 A) x) = 0
      rw [map_smul, inv_sum_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply, map_sum]
      refine (congrArg _ (Finset.sum_eq_zero fun a _ => ?_)).trans (smul_zero _)
      have h := ConvOp.toLin_star_mem
        (F := fun A _ _ => LinearMap.ker (unitCoeffL R V A))
        (G := fun A _ _ => LinearMap.ker (unitCoeffL R V A))
        (H := fun A _ _ => LinearMap.ker (unitCoeffL R V A))
        (fun _ _ _ b y hy => by
          rw [LinearMap.mem_ker] at hy ⊢
          rw [unitCoeffL_par, hy]
          split_ifs <;> rfl)
        (fun _ _ _ _ _ _ e y hy => by
          rw [LinearMap.mem_ker] at hy ⊢
          rw [unitCoeffL_map, hy])
        (fun _ _ _ _ _ _ i y z hy hz => by
          rw [LinearMap.mem_ker] at hy ⊢
          rw [FreeGrL.unitCoeffL_comp, hy, zero_mul])
        (f := fN ψ (a.1 + 1)) (g := fN ψ (n + 1 - a.1))
        (fun A _ _ x => ih (a.1 + 1) (by omega) x) (fun A _ _ x => ih _ (by omega) x) A x
      exact h

/-- **The products of components have no unit component.** -/
lemma X_unit (n : ℕ) (x : C A) : ConvOp.toLin ((X ψ n).1 A) x ∈ CutCobar.nu R V A := by
  rw [X, inv_sum_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun p _ => ?_
  exact ConvOp.toLin_star_mem (F := fun A _ _ => CutCobar.nu R V A)
    (G := fun A _ _ => CutCobar.nu R V A) (H := fun A _ _ => CutCobar.nu R V A)
    (fun _ _ _ b _ hy => CutCobar.par_mem_nu b hy)
    (fun _ _ _ _ _ _ e _ hy => CutCobar.map_mem_nu e hy)
    (fun _ _ _ _ _ _ i _ z hy _ => CutCobar.comp_mem_nu i hy z)
    (f := τ ψ p.1) (g := τ ψ p.2)
    (fun A _ _ x => CutCobar.jL_mem_nu _) (fun A _ _ x => CutCobar.jL_mem_nu _) A x

/-! ## Weights and the associator -/

omit [Algebra ℚ R] in
/-- **Reindexing a sum over the triples with sum `n`**, grouping the first two. -/
lemma sum_antidiag_left {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → ℕ → ℕ → M) :
    ∑ cr ∈ Finset.antidiagonal n, ∑ pq ∈ Finset.antidiagonal cr.1, F pq.1 pq.2 cr.2
      = ∑ t ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun t => t.1 + t.2.1 + t.2.2 = n), F t.1 t.2.1 t.2.2 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => (x.2.1, x.2.2, x.1.2))
    (fun t => ⟨(t.1 + t.2.1, t.2.2), (t.1, t.2.1)⟩) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨⟨c, r⟩, ⟨p, q⟩⟩ h
    obtain ⟨h1, h2⟩ := Finset.mem_sigma.1 h
    have h1' : c + r = n := Finset.mem_antidiagonal.1 h1
    have h2' : p + q = c := Finset.mem_antidiagonal.1 h2
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 ?_,
      Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩⟩, ?_⟩
    · show p < n + 1
      omega
    · show q < n + 1
      omega
    · show r < n + 1
      omega
    · show p + q + r = n
      omega
  · rintro ⟨p, q, r⟩ h
    have h3 : p + q + r = n := (Finset.mem_filter.1 h).2
    exact Finset.mem_sigma.2 ⟨Finset.mem_antidiagonal.2 h3, Finset.mem_antidiagonal.2 rfl⟩
  · rintro ⟨⟨c, r⟩, ⟨p, q⟩⟩ h
    have h2' : p + q = c := Finset.mem_antidiagonal.1 (Finset.mem_sigma.1 h).2
    subst h2'
    rfl
  · rintro ⟨p, q, r⟩ _
    rfl

omit [Algebra ℚ R] in
/-- **Reindexing a sum over the triples with sum `n`**, grouping the last two. -/
lemma sum_antidiag_right {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → ℕ → ℕ → M) :
    ∑ pc ∈ Finset.antidiagonal n, ∑ qr ∈ Finset.antidiagonal pc.2, F pc.1 qr.1 qr.2
      = ∑ t ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun t => t.1 + t.2.1 + t.2.2 = n), F t.1 t.2.1 t.2.2 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => (x.1.1, x.2.1, x.2.2))
    (fun t => ⟨(t.1, t.2.1 + t.2.2), (t.2.1, t.2.2)⟩) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨⟨p, c⟩, ⟨q, r⟩⟩ h
    obtain ⟨h1, h2⟩ := Finset.mem_sigma.1 h
    have h1' : p + c = n := Finset.mem_antidiagonal.1 h1
    have h2' : q + r = c := Finset.mem_antidiagonal.1 h2
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 ?_,
      Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩⟩, ?_⟩
    · show p < n + 1
      omega
    · show q < n + 1
      omega
    · show r < n + 1
      omega
    · show p + q + r = n
      omega
  · rintro ⟨p, q, r⟩ h
    have h3 : p + q + r = n := (Finset.mem_filter.1 h).2
    exact Finset.mem_sigma.2 ⟨Finset.mem_antidiagonal.2 (by show p + (q + r) = n; omega),
      Finset.mem_antidiagonal.2 rfl⟩
  · rintro ⟨⟨p, c⟩, ⟨q, r⟩⟩ h
    have h2' : q + r = c := Finset.mem_antidiagonal.1 (Finset.mem_sigma.1 h).2
    subst h2'
    rfl
  · rintro ⟨p, q, r⟩ _
    rfl

omit [Algebra ℚ R] in
/-- **The interior of an antidiagonal**: a sum over the pairs with sum `m + 2` of terms vanishing
when an index is zero. -/
lemma sum_antidiag_interior {M : Type*} [AddCommMonoid M] (m : ℕ) (F : ℕ → ℕ → M)
    (h0 : ∀ b, F 0 b = 0) (h0' : ∀ a, F a 0 = 0) :
    ∑ p ∈ Finset.antidiagonal (m + 2), F p.1 p.2
      = ∑ a : Fin (m + 1), F (a.1 + 1) (m + 1 - a.1) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ', h0, add_zero,
    Finset.sum_range_succ, show m + 2 - (m + 1 + 1) = 0 by omega, h0', add_zero,
    Fin.sum_univ_eq_sum_range (fun a => F (a + 1) (m + 1 - a)) (m + 1)]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  rw [show m + 2 - (a + 1) = m + 1 - a by omega]

/-- **The part of a given weight of a vanishing sum vanishes.** -/
lemma sum_filter_wt_eq_zero (s : Finset (ℕ × ℕ × ℕ)) (w : ℕ × ℕ × ℕ → Ω A)
    (hw : ∀ t ∈ s, w t ∈ CutCobar.wt R V (t.1 + t.2.1 + t.2.2) A) (h0 : ∑ t ∈ s, w t = 0)
    (n : ℕ) : ∑ t ∈ s.filter (fun t => t.1 + t.2.1 + t.2.2 = n), w t = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ × ℕ × ℕ → ℕ, ∀ t, g t = t.1 + t.2.1 + t.2.2 := ⟨_, fun _ => rfl⟩
  obtain ⟨v, hv'⟩ : ∃ v : ℕ → Ω A, ∀ j, v j = ∑ t ∈ s.filter (fun t => g t = j), w t :=
    ⟨_, fun _ => rfl⟩
  have hv : ∀ j ∈ s.image g, v j ∈ CutCobar.wt R V j A := fun j _ => by
    rw [hv']
    refine Submodule.sum_mem _ fun t ht => ?_
    have h := hw t (Finset.mem_filter.1 ht).1
    rwa [← hg, (Finset.mem_filter.1 ht).2] at h
  have hsum : ∑ j ∈ s.image g, v j = 0 := by
    rw [← h0]
    simp only [hv']
    exact Finset.sum_fiberwise_of_maps_to (fun t ht => Finset.mem_image_of_mem g ht) w
  have hz := ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1
    (CutCobar.iSupIndep_wt A)) (s.image g) v hv hsum
  have e : s.filter (fun t => t.1 + t.2.1 + t.2.2 = n) = s.filter (fun t => g t = n) :=
    Finset.filter_congr fun t _ => by rw [hg]
  rw [e, ← hv']
  by_cases hn : n ∈ s.image g
  · exact hz n hn
  · rw [hv']
    refine Finset.sum_eq_zero fun t ht => absurd ?_ hn
    rw [← (Finset.mem_filter.1 ht).2]
    exact Finset.mem_image_of_mem g (Finset.mem_filter.1 ht).1

omit [Algebra ℚ R] in
lemma star_sum_left {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {ι' : Type}
    (s : Finset ι') (q : ι' → GrOperad.Inv R Q) (q' : GrOperad.Inv R Q) :
    GrOperad.Inv.star R Q (∑ i ∈ s, q i) q' = ∑ i ∈ s, GrOperad.Inv.star R Q (q i) q' := by
  rw [map_sum, LinearMap.coe_sum, Finset.sum_apply]

omit [Algebra ℚ R] in
lemma star_sum_right {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {ι' : Type}
    (q' : GrOperad.Inv R Q) (s : Finset ι') (q : ι' → GrOperad.Inv R Q) :
    GrOperad.Inv.star R Q q' (∑ i ∈ s, q i) = ∑ i ∈ s, GrOperad.Inv.star R Q q' (q i) :=
  map_sum _ _ _

omit [Algebra ℚ R] in
/-- **The associators of a sum of odd families add up to zero.** -/
lemma sum_assoc_eq_zero {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    (s : Finset ℕ) (q : ℕ → GrOperad.Inv R Q) (hq : ∀ m, GrOperad.Inv.IsPar true (q m)) :
    ∑ t ∈ s ×ˢ s ×ˢ s,
        (GrOperad.Inv.star R Q (GrOperad.Inv.star R Q (q t.1) (q t.2.1)) (q t.2.2)
          - GrOperad.Inv.star R Q (q t.1) (GrOperad.Inv.star R Q (q t.2.1) (q t.2.2))) = 0 := by
  have hT : GrOperad.Inv.IsPar true (∑ m ∈ s, q m) := isPar_sum _ fun m _ => hq m
  have hassoc := GrOperad.Inv.assoc_odd (∑ m ∈ s, q m) (∑ m ∈ s, q m) hT
  have e1 : GrOperad.Inv.star R Q (GrOperad.Inv.star R Q (∑ m ∈ s, q m) (∑ m ∈ s, q m))
      (∑ m ∈ s, q m) = ∑ t ∈ s ×ˢ s ×ˢ s,
        GrOperad.Inv.star R Q (GrOperad.Inv.star R Q (q t.1) (q t.2.1)) (q t.2.2) := by
    rw [Finset.sum_product, star_sum_left s q (∑ m ∈ s, q m), star_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product, star_sum_right (q a) s q, star_sum_left]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_sum_right]
  have e2 : GrOperad.Inv.star R Q (∑ m ∈ s, q m)
      (GrOperad.Inv.star R Q (∑ m ∈ s, q m) (∑ m ∈ s, q m)) = ∑ t ∈ s ×ˢ s ×ˢ s,
        GrOperad.Inv.star R Q (q t.1) (GrOperad.Inv.star R Q (q t.2.1) (q t.2.2)) := by
    rw [Finset.sum_product, star_sum_left s q]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product, star_sum_left s q (∑ m ∈ s, q m), star_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_sum_right, star_sum_right]
  rw [Finset.sum_sub_distrib, ← e1, ← e2, hassoc, sub_self]

/-- The associator of three components. -/
noncomputable def assocτ (t : ℕ × ℕ × ℕ) : GrOperad.Inv R (ConvOp R C Ω) :=
  GrOperad.Inv.star R _ (GrOperad.Inv.star R _ (τ ψ t.1) (τ ψ t.2.1)) (τ ψ t.2.2)
    - GrOperad.Inv.star R _ (τ ψ t.1) (GrOperad.Inv.star R _ (τ ψ t.2.1) (τ ψ t.2.2))

lemma assocτ_mem (t : ℕ × ℕ × ℕ) (x : C A) :
    ConvOp.toLin ((assocτ ψ t).1 A) x ∈ CutCobar.wt R V (t.1 + t.2.1 + t.2.2) A := by
  have h1 := ConvOp.toLin_star_mem (F := fun A _ _ => CutCobar.wt R V (t.1 + t.2.1) A)
    (G := fun A _ _ => CutCobar.wt R V t.2.2 A)
    (H := fun A _ _ => CutCobar.wt R V (t.1 + t.2.1 + t.2.2) A)
    (fun _ _ _ b _ hy => CutCobar.par_mem_wt b hy)
    (fun _ _ _ _ _ _ e _ hy => CutCobar.map_mem_wt e hy)
    (fun _ _ _ _ _ _ i _ _ hy hz => CutCobar.comp_mem_wt i hy hz)
    (f := GrOperad.Inv.star R _ (τ ψ t.1) (τ ψ t.2.1)) (g := τ ψ t.2.2)
    (fun A _ _ x => star_τ_mem ψ _ _ x) (fun A _ _ x => τ_mem' ψ _ x) A x
  have h2 := ConvOp.toLin_star_mem (F := fun A _ _ => CutCobar.wt R V t.1 A)
    (G := fun A _ _ => CutCobar.wt R V (t.2.1 + t.2.2) A)
    (H := fun A _ _ => CutCobar.wt R V (t.1 + t.2.1 + t.2.2) A)
    (fun _ _ _ b _ hy => CutCobar.par_mem_wt b hy)
    (fun _ _ _ _ _ _ e _ hy => CutCobar.map_mem_wt e hy)
    (fun _ _ _ _ _ _ i _ _ hy hz => by
      have := CutCobar.comp_mem_wt i hy hz
      rwa [← Nat.add_assoc] at this)
    (f := τ ψ t.1) (g := GrOperad.Inv.star R _ (τ ψ t.2.1) (τ ψ t.2.2))
    (fun A _ _ x => τ_mem' ψ _ x) (fun A _ _ x => star_τ_mem ψ _ _ x) A x
  exact sub_mem h1 h2

/-- **The associators of the components with `n` vertices in all**, in terms of the convolution
squares. -/
lemma sum_assocτ_filter (n : ℕ) :
    ∑ t ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun t => t.1 + t.2.1 + t.2.2 = n), assocτ ψ t
      = ∑ p ∈ Finset.antidiagonal n, (GrOperad.Inv.star R _ (X ψ p.1) (τ ψ p.2)
          - GrOperad.Inv.star R _ (τ ψ p.1) (X ψ p.2)) := by
  have e1 := sum_antidiag_left n (fun p q r => GrOperad.Inv.star R _
    (GrOperad.Inv.star R _ (τ ψ p) (τ ψ q)) (τ ψ r))
  have e2 := sum_antidiag_right n (fun p q r => GrOperad.Inv.star R _ (τ ψ p)
    (GrOperad.Inv.star R _ (τ ψ q) (τ ψ r)))
  have e3 : ∀ t : ℕ × ℕ × ℕ, assocτ ψ t
      = GrOperad.Inv.star R _ (GrOperad.Inv.star R _ (τ ψ t.1) (τ ψ t.2.1)) (τ ψ t.2.2)
        - GrOperad.Inv.star R _ (τ ψ t.1) (GrOperad.Inv.star R _ (τ ψ t.2.1) (τ ψ t.2.2)) :=
    fun _ => rfl
  have a1 : ∑ cr ∈ Finset.antidiagonal n, ∑ pq ∈ Finset.antidiagonal cr.1,
      GrOperad.Inv.star R _ (GrOperad.Inv.star R _ (τ ψ pq.1) (τ ψ pq.2)) (τ ψ cr.2)
        = ∑ p ∈ Finset.antidiagonal n, GrOperad.Inv.star R _ (X ψ p.1) (τ ψ p.2) :=
    Finset.sum_congr rfl fun p _ => by rw [X, star_sum_left]
  have a2 : ∑ pc ∈ Finset.antidiagonal n, ∑ qr ∈ Finset.antidiagonal pc.2,
      GrOperad.Inv.star R _ (τ ψ pc.1) (GrOperad.Inv.star R _ (τ ψ qr.1) (τ ψ qr.2))
        = ∑ p ∈ Finset.antidiagonal n, GrOperad.Inv.star R _ (τ ψ p.1) (X ψ p.2) :=
    Finset.sum_congr rfl fun p _ => by rw [X, star_sum_right]
  simp only [e3]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← a1, ← a2]
  exact congrArg₂ (· - ·) e1.symm e2.symm

/-- **The associator of the components vanishes in each weight**:
`∑_{a + b = n} (Xₐ ⋆ τ_b - τₐ ⋆ X_b) = 0`. -/
lemma W_eq_zero (n : ℕ) (x : C A) :
    ConvOp.toLin ((∑ p ∈ Finset.antidiagonal n, (GrOperad.Inv.star R _ (X ψ p.1) (τ ψ p.2)
      - GrOperad.Inv.star R _ (τ ψ p.1) (X ψ p.2))).1 A) x = 0 := by
  have h0 : ∑ t ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      ConvOp.toLin ((assocτ ψ t).1 A) x = 0 := by
    have h := congrArg (fun q : GrOperad.Inv R (ConvOp R C Ω) => ConvOp.toLin (q.1 A) x)
      (sum_assoc_eq_zero (Finset.range (n + 1)) (fun m => τ ψ m) (fun m => isPar_τ ψ m))
    simp only [inv_sum_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply] at h
    exact h
  have hn := sum_filter_wt_eq_zero _ (fun t => ConvOp.toLin ((assocτ ψ t).1 A) x)
    (fun t _ => assocτ_mem ψ t x) h0 n
  rw [← sum_assocτ_filter, inv_sum_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  exact hn

/-! ## The Maurer–Cartan equation of the components -/

/-- The derivation of the convolution operad given by the cobar differential. -/
noncomputable abbrev Dc : GrDer (GrOperadHom.id R (ConvOp R C Ω)) true :=
  ConvOp.postDer (C := C) (CutCobar.dL R V)

lemma Dc_τ_apply (n : ℕ) (x : C A) :
    ConvOp.toLin ((GrOperad.Inv.appDer (Dc (C := C) (R := R) (V := V)) (τ ψ n)).1 A) x
      = (CutCobar.dL R V).app A (CutCobar.jL R V A (ConvOp.toLin ((fN ψ n).1 A) x)) :=
  rfl

/-- **The differential of the convolution squares**, from the Maurer–Cartan equation of the
components with fewer vertices. -/
lemma appDer_X (n : ℕ)
    (ih : ∀ m < n, GrOperad.Inv.appDer (Dc (C := C) (R := R) (V := V)) (τ ψ m) = -X ψ m) :
    GrOperad.Inv.appDer (Dc (C := C) (R := R) (V := V)) (X ψ n)
      = -∑ p ∈ Finset.antidiagonal n, (GrOperad.Inv.star R _ (X ψ p.1) (τ ψ p.2)
          - GrOperad.Inv.star R _ (τ ψ p.1) (X ψ p.2)) := by
  rw [X, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  have h1 : GrOperad.Inv.star R _ (GrOperad.Inv.appDer Dc (τ ψ p.1)) (τ ψ p.2)
      = -GrOperad.Inv.star R _ (X ψ p.1) (τ ψ p.2) := by
    rcases Nat.eq_zero_or_pos p.2 with h | h
    · rw [h, τ_zero, map_zero, map_zero, neg_zero]
    · rw [ih p.1 (by omega), map_neg, LinearMap.neg_apply]
  have h2 : GrOperad.Inv.star R _ (τ ψ p.1) (GrOperad.Inv.appDer Dc (τ ψ p.2))
      = -GrOperad.Inv.star R _ (τ ψ p.1) (X ψ p.2) := by
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h, τ_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply, neg_zero]
    · rw [ih p.2 (by omega), map_neg]
  have h3 := GrOperad.Inv.appDer_star (Dc (C := C) (R := R) (V := V)) (isPar_τ ψ p.1) (τ ψ p.2)
  rw [Bool.and_self, σ_true, GrOperad.Inv.neg_one_smul_inv, h1, h2] at h3
  rw [h3, neg_sub, sub_eq_add_neg, add_comm, neg_neg]

/-- **The convolution squares are cycles**, given the Maurer–Cartan equation of the components
with fewer vertices. -/
lemma dL_X (n : ℕ)
    (ih : ∀ m < n, GrOperad.Inv.appDer (Dc (C := C) (R := R) (V := V)) (τ ψ m) = -X ψ m)
    (x : C A) : (CutCobar.dL R V).app A (ConvOp.toLin ((X ψ n).1 A) x) = 0 := by
  have e : (CutCobar.dL R V).app A (ConvOp.toLin ((X ψ n).1 A) x)
      = ConvOp.toLin ((GrOperad.Inv.appDer (Dc (C := C) (R := R) (V := V)) (X ψ n)).1 A) x :=
    rfl
  rw [e, appDer_X ψ n ih]
  show -ConvOp.toLin ((∑ p ∈ Finset.antidiagonal n, (GrOperad.Inv.star R _ (X ψ p.1) (τ ψ p.2)
      - GrOperad.Inv.star R _ (τ ψ p.1) (X ψ p.2))).1 A) x = 0
  rw [W_eq_zero ψ n x, neg_zero]

/-- **The recursion on the pairs**: `∑_{a + b = m + 2} fₐ ⋆ f_b = (m + 1) f_{m+2}`. -/
lemma sum_antidiag_fN (m : ℕ) :
    ∑ p ∈ Finset.antidiagonal (m + 2), GrOperad.Inv.star R _ (fN ψ p.1) (fN ψ p.2)
      = ((m + 1 : ℕ) : R) • fN ψ (m + 2) := by
  rw [smul_fN_add_two]
  exact sum_antidiag_interior m (fun a b => GrOperad.Inv.star R _ (fN ψ a) (fN ψ b))
    (fun b => by
      show GrOperad.Inv.star R _ (fN ψ 0) (fN ψ b) = 0
      rw [fN_zero, map_zero, LinearMap.zero_apply])
    (fun a => by
      show GrOperad.Inv.star R _ (fN ψ a) (fN ψ 0) = 0
      rw [fN_zero, map_zero])

/-- **Merging the two vertices of the convolution squares** gives the next component. -/
lemma hL_X (m : ℕ) (x : C A) :
    CutCobar.hL R V A (ConvOp.toLin ((X ψ (m + 2)).1 A) x)
      = -(((m + 1 : ℕ) : R) • CutCobar.jL R V A (ConvOp.toLin ((fN ψ (m + 2)).1 A) x)) := by
  have e1 : CutCobar.hL R V A (ConvOp.toLin ((X ψ (m + 2)).1 A) x)
      = -CutCobar.jL R V A (ConvOp.toLin ((∑ p ∈ Finset.antidiagonal (m + 2),
          GrOperad.Inv.star R _ (fN ψ p.1) (fN ψ p.2)).1 A) x) := by
    rw [X, inv_sum_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply, map_sum,
      inv_sum_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply, map_sum,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => hM_star (isPar_fN ψ _) (isPar_fN ψ _)
      (fun A _ _ x => fN_unit ψ _ x) (fun A _ _ x => fN_unit ψ _ x) x
  have e3 : ConvOp.toLin ((((m + 1 : ℕ) : R) • fN ψ (m + 2)).1 A) x
      = ((m + 1 : ℕ) : R) • ConvOp.toLin ((fN ψ (m + 2)).1 A) x := rfl
  rw [e1, sum_antidiag_fN, e3, map_smul]

/-- **The Maurer–Cartan equation of the components**: `d τₙ = -∑_{a + b = n} τₐ ⋆ τ_b`. -/
theorem appDer_τ (hV0 : ∀ v : V (Fin 0), v = 0) (n : ℕ) :
    GrOperad.Inv.appDer (Dc (C := C) (R := R) (V := V)) (τ ψ n) = -X ψ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ?_)
  ext x
  show ConvOp.toLin ((GrOperad.Inv.appDer Dc (τ ψ n)).1 A) x = -ConvOp.toLin ((X ψ n).1 A) x
  rw [Dc_τ_apply]
  match n, ih with
  | 0, _ =>
    have hX : X ψ 0 = 0 := by
      rw [X, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, τ_zero, map_zero]
    rw [hX, fN_zero]
    show (CutCobar.dL R V).app A (CutCobar.jL R V A 0) = -0
    rw [map_zero, map_zero, neg_zero]
  | 1, _ =>
    have hX : X ψ 1 = 0 := by
      rw [X]
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      rcases Nat.eq_zero_or_pos p.1 with h | h
      · rw [h, τ_zero, map_zero, LinearMap.zero_apply]
      · rw [show p.2 = 0 by omega, τ_zero, map_zero]
    rw [hX, fN_one, CutCobar.dL_jL_of_vx_one hV0 (f1_mem ψ x)]
    exact neg_zero.symm
  | m + 2, ih =>
    have hdY := dL_X ψ (m + 2) ih x
    have hc := CutCobar.contraction hV0 (X_mem ψ (m + 2) x) (X_unit ψ (m + 2) x)
    have e : ((m + 2 : ℕ) : R) = ((m + 1 : ℕ) : R) + 1 := by
      push_cast
      ring
    rw [hdY, map_zero, add_zero, hL_X, map_neg, map_smul, e, add_smul, one_smul,
      add_sub_cancel_right] at hc
    have hc' : ((m + 1 : ℕ) : R) • ((CutCobar.dL R V).app A
        (CutCobar.jL R V A (ConvOp.toLin ((fN ψ (m + 2)).1 A) x))
          + ConvOp.toLin ((X ψ (m + 2)).1 A) x) = 0 := by
      rw [smul_add, ← hc, add_neg_cancel]
    have := (isUnit_natCast_of_ne_zero (R := R)
      (show m + 1 ≠ 0 by omega)).smul_left_cancel.1 (hc'.trans (smul_zero _).symm)
    exact eq_neg_of_add_eq_zero_left this

/-! ## Finiteness on a conilpotent cooperad -/

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
/-- A homogeneous family killing a cooperation kills its sign twists. -/
lemma toLin_tw_eq_zero {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {p : Bool}
    {f : GrOperad.Inv R (ConvOp R C Q)} (hf : GrOperad.Inv.IsPar p f) (q : Bool) {a : C A}
    (ha : ConvOp.toLin (f.1 A) a = 0) :
    ConvOp.toLin (f.1 A) (GrSpecies.tw (R := R) q a) = 0 := by
  have h : ∀ (c : Bool) (y : C A), ConvOp.toLin (f.1 A) (GrSpecies.par (R := R) c y)
      = GrOperad.par (R := R) (xor c p) (ConvOp.toLin (f.1 A) y) :=
    fun c y => isParC_of_isPar hf A c y
  rw [GrSpecies.tw_apply, map_add, map_smul, h, h, ha]
  simp only [map_zero, smul_zero, add_zero]

omit [Algebra ℚ R] in
/-- **A convolution product kills one more stage of the coradical filtration**: if both factors
kill the coaugmentation and one of them kills `F_k`, the product kills `F_{k+1}`. -/
lemma star_filt_eq_zero {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {p q : Bool}
    {f g : GrOperad.Inv R (ConvOp R C Q)} (hf : GrOperad.Inv.IsPar p f)
    (hg : GrOperad.Inv.IsPar q g) (k : ℕ)
    (hf0 : ∀ (A : Type) [Fintype A] [DecidableEq A], ∀ x ∈ GrCooperad.unitSpan R C A,
      ConvOp.toLin (f.1 A) x = 0)
    (hg0 : ∀ (A : Type) [Fintype A] [DecidableEq A], ∀ x ∈ GrCooperad.unitSpan R C A,
      ConvOp.toLin (g.1 A) x = 0)
    (hk : (∀ (A : Type) [Fintype A] [DecidableEq A], ∀ x ∈ GrCooperad.filt R C k A,
        ConvOp.toLin (f.1 A) x = 0) ∨
      ∀ (A : Type) [Fintype A] [DecidableEq A], ∀ x ∈ GrCooperad.filt R C k A,
        ConvOp.toLin (g.1 A) x = 0)
    {x : C A} (hx : x ∈ GrCooperad.filt R C (k + 1) A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ f g).1 A) x = 0 := by
  rw [GrOperad.Inv.star_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun S _ => ?_
  show ConvOp.toLin (ConvOp.mapC (splitEquiv S)
    (ConvOp.compC none (f.1 (SOut S)) (g.1 (SIn S)))) x = 0
  rw [ConvOp.mapC_apply, ConvOp.toLin_compC, LinearMap.comp_apply, LinearMap.comp_apply,
    ConvOp.kap_hom _ (isParC_of_isPar hg _)]
  have ht := GrCooperad.mem_filt_succ.1 hx (SOut S) (SIn S) none (splitEquiv S)
  have hle : GrCooperad.filtTarget R C (GrCooperad.filt R C k) (SOut S) (SIn S) ≤
      LinearMap.ker (TensorProduct.map (ConvOp.toLin (f.1 (SOut S)) ∘ₗ
        GrSpecies.tw (R := R) q) (ConvOp.toLin (g.1 (SIn S)))) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> refine Submodule.map₂_le.2 fun a ha b hb => ?_ <;>
      rw [LinearMap.mem_ker, TensorProduct.mk_apply, TensorProduct.map_tmul, LinearMap.comp_apply]
    · rw [toLin_tw_eq_zero hf q (hf0 _ a ha), TensorProduct.zero_tmul]
    · rw [hg0 _ b hb, TensorProduct.tmul_zero]
    · rcases hk with h | h
      · rw [toLin_tw_eq_zero hf q (h _ a ha), TensorProduct.zero_tmul]
      · rw [h _ b hb, TensorProduct.tmul_zero]
  rw [LinearMap.mem_ker.1 (hle ht), map_zero, map_zero]

/-- **The components kill the coaugmentation.** -/
lemma fN_unitSpan (n : ℕ) {x : C A} (hx : x ∈ GrCooperad.unitSpan R C A) :
    ConvOp.toLin ((fN ψ n).1 A) x = 0 := by
  induction n using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      rw [fN_zero]
      rfl
    | 1, _ =>
      have h0 : GrCooperad.Red.proj R C A x = 0 := (Submodule.Quotient.mk_eq_zero _).2 hx
      rw [fN_one, f1_apply, h0, map_zero, map_zero]
    | n + 2, ih =>
      rw [fN_add_two]
      show algebraMap ℚ R ((n + 1 : ℚ)⁻¹) • ConvOp.toLin ((∑ a : Fin (n + 1),
        GrOperad.Inv.star R _ (fN ψ (a.1 + 1)) (fN ψ (n + 1 - a.1))).1 A) x = 0
      rw [inv_sum_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
      refine (congrArg _ (Finset.sum_eq_zero fun a _ => ?_)).trans (smul_zero _)
      have ha := a.isLt
      exact star_filt_eq_zero (isPar_fN ψ _) (isPar_fN ψ _) 0
        (fun B _ _ y hy => ih _ (by omega) hy) (fun B _ _ y hy => ih _ (by omega) hy)
        (Or.inl fun B _ _ y hy => ih _ (by omega) hy) (GrCooperad.unitSpan_le_filt 1 A hx)

/-- **The components vanish high up the coradical filtration**: `fₙ` kills `F_k` for
`n > 2^k`. -/
lemma fN_filt (k : ℕ) : ∀ (n : ℕ), 2 ^ k < n → ∀ (A : Type) [Fintype A] [DecidableEq A],
    ∀ x ∈ GrCooperad.filt R C k A, ConvOp.toLin ((fN ψ n).1 A) x = 0 := by
  induction k with
  | zero => exact fun n _ A _ _ x hx => fN_unitSpan ψ n hx
  | succ k ih =>
    intro n hn A _ _ x hx
    have h2 := Nat.one_le_two_pow (n := k)
    rw [pow_succ] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [fN_add_two]
    show algebraMap ℚ R ((m + 1 : ℚ)⁻¹) • ConvOp.toLin ((∑ a : Fin (m + 1),
      GrOperad.Inv.star R _ (fN ψ (a.1 + 1)) (fN ψ (m + 1 - a.1))).1 A) x = 0
    rw [inv_sum_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
    refine (congrArg _ (Finset.sum_eq_zero fun a _ => ?_)).trans (smul_zero _)
    have ha := a.isLt
    refine star_filt_eq_zero (isPar_fN ψ _) (isPar_fN ψ _) k
      (fun B _ _ y hy => fN_unitSpan ψ _ hy) (fun B _ _ y hy => fN_unitSpan ψ _ hy) ?_ hx
    by_cases h : 2 ^ k < a.1 + 1
    · exact Or.inl fun B _ _ y hy => ih _ h B y hy
    · exact Or.inr fun B _ _ y hy => ih _ (by omega) B y hy

/-! ## The sum of the components -/

variable (hC : GrCooperad.Conilpotent R C)

omit [Algebra ℚ R] in
lemma filt_mono' {k l : ℕ} (h : k ≤ l) : GrCooperad.filt R C k A ≤ GrCooperad.filt R C l A :=
  monotone_nat_of_le_succ (f := fun n => GrCooperad.filt R C n A)
    (fun n => GrCooperad.filt_mono n A) h

omit [Algebra ℚ R] in
/-- The first stage of the coradical filtration containing a cooperation. -/
noncomputable def stg (x : C A) : ℕ := @Nat.find _ (Classical.decPred _) (hC A x)

omit [Algebra ℚ R] in
lemma mem_filt_stg (x : C A) : x ∈ GrCooperad.filt R C (stg hC x) A :=
  @Nat.find_spec _ (Classical.decPred _) (hC A x)

/-- **The sum of the components** on a cooperation: only finitely many are nonzero. -/
noncomputable def fbarFun (x : C A) : 𝒞 A :=
  ∑ n ∈ Finset.range (2 ^ stg hC x + 1), ConvOp.toLin ((fN ψ n).1 A) x

lemma sum_range_fN_eq {k N N' : ℕ} {x : C A} (hx : x ∈ GrCooperad.filt R C k A)
    (hN : 2 ^ k ≤ N) (hN' : N ≤ N') :
    ∑ n ∈ Finset.range (N + 1), ConvOp.toLin ((fN ψ n).1 A) x
      = ∑ n ∈ Finset.range (N' + 1), ConvOp.toLin ((fN ψ n).1 A) x := by
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun n hn hn' => ?_
  rw [Finset.mem_range] at hn hn'
  exact fN_filt ψ k n (by omega) A x hx

/-- **The sum of the components is any long enough partial sum.** -/
lemma fbarFun_eq {N : ℕ} {x : C A} (hN : 2 ^ stg hC x ≤ N) :
    fbarFun ψ hC x = ∑ n ∈ Finset.range (N + 1), ConvOp.toLin ((fN ψ n).1 A) x :=
  sum_range_fN_eq ψ (mem_filt_stg hC x) le_rfl hN

lemma fbarFun_eq_of_mem {k N : ℕ} {x : C A} (hx : x ∈ GrCooperad.filt R C k A)
    (hN : 2 ^ k ≤ N) :
    fbarFun ψ hC x = ∑ n ∈ Finset.range (N + 1), ConvOp.toLin ((fN ψ n).1 A) x := by
  rw [fbarFun_eq ψ hC (le_max_left (2 ^ stg hC x) N)]
  exact (sum_range_fN_eq ψ hx hN (le_max_right _ _)).symm

/-- **The sum of the components**, as a linear map. -/
noncomputable def fbarL (A : Type) [Fintype A] [DecidableEq A] : C A →ₗ[R] 𝒞 A where
  toFun := fbarFun ψ hC
  map_add' x y := by
    have hx := filt_mono' (A := A) (Nat.le_add_right (stg hC x) (stg hC y)) (mem_filt_stg hC x)
    have hy := filt_mono' (A := A) (Nat.le_add_left (stg hC y) (stg hC x)) (mem_filt_stg hC y)
    rw [fbarFun_eq_of_mem ψ hC (add_mem hx hy) le_rfl, fbarFun_eq_of_mem ψ hC hx le_rfl,
      fbarFun_eq_of_mem ψ hC hy le_rfl, ← Finset.sum_add_distrib]
    simp only [map_add]
  map_smul' r x := by
    have hx := mem_filt_stg hC x
    rw [fbarFun_eq_of_mem ψ hC (Submodule.smul_mem _ r hx) le_rfl,
      fbarFun_eq_of_mem ψ hC hx le_rfl, Finset.smul_sum]
    simp only [map_smul, RingHom.id_apply]

lemma fbarL_apply (x : C A) : fbarL ψ hC A x = fbarFun ψ hC x := rfl

lemma fbarL_unitSpan {x : C A} (hx : x ∈ GrCooperad.unitSpan R C A) : fbarL ψ hC A x = 0 := by
  rw [fbarL_apply, fbarFun_eq_of_mem ψ hC (k := 0) hx le_rfl]
  exact Finset.sum_eq_zero fun n _ => fN_unitSpan ψ n hx

/-! ## The Maurer–Cartan equation of the sum -/

omit [Algebra ℚ R] in
/-- **A sum over the antidiagonals of terms vanishing outside a square** is the sum over the
square, once the antidiagonals cover it. -/
lemma sum_antidiag_range_eq {M : Type*} [AddCommMonoid M] (K N : ℕ) (hKN : 2 * K ≤ N)
    (g : ℕ → ℕ → M) (hg1 : ∀ a b, K < a → g a b = 0) (hg2 : ∀ a b, K < b → g a b = 0) :
    ∑ n ∈ Finset.range (N + 1), ∑ p ∈ Finset.antidiagonal n, g p.1 p.2
      = ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1), g a b := by
  classical
  rw [Finset.sum_sigma', ← Finset.sum_product']
  refine Finset.sum_bij_ne_zero (fun x _ _ => (x.2.1, x.2.2)) ?_ ?_ ?_ (fun _ _ _ => rfl)
  · rintro ⟨n, a, b⟩ _ h0
    refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩
    · show a < K + 1
      by_contra h
      exact h0 (hg1 a b (by omega))
    · show b < K + 1
      by_contra h
      exact h0 (hg2 a b (by omega))
  · rintro ⟨n, a, b⟩ h1 _ ⟨n', a', b'⟩ h1' _ h
    obtain ⟨-, h2⟩ := Finset.mem_sigma.1 h1
    obtain ⟨-, h2'⟩ := Finset.mem_sigma.1 h1'
    have e1 : a + b = n := Finset.mem_antidiagonal.1 h2
    have e2 : a' + b' = n' := Finset.mem_antidiagonal.1 h2'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    subst e1
    subst e2
    rfl
  · rintro ⟨a, b⟩ hab h0
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hab
    rw [Finset.mem_range] at ha hb
    exact ⟨⟨a + b, a, b⟩, Finset.mem_sigma.2 ⟨Finset.mem_range.2 (show a + b < N + 1 by omega),
      Finset.mem_antidiagonal.2 rfl⟩, h0, rfl⟩

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
/-- An even family commutes with the sign twists. -/
lemma toLin_tw {f : GrOperad.Inv R (ConvOp R C 𝒞)} (hf : GrOperad.Inv.IsPar false f) (a : C A) :
    ConvOp.toLin (f.1 A) (GrSpecies.tw (R := R) true a)
      = CutCobar.twC R V A (ConvOp.toLin (f.1 A) a) := by
  have h : ∀ (c : Bool) (y : C A), ConvOp.toLin (f.1 A) (GrSpecies.par (R := R) c y)
      = GrOperad.par (R := R) (xor c false) (ConvOp.toLin (f.1 A) y) :=
    fun c y => isParC_of_isPar hf A c y
  rw [GrSpecies.tw_apply, map_add, map_smul, h, h, CutCobar.twC_apply, σ_true, neg_one_smul,
    Bool.xor_false, Bool.xor_false, sub_eq_add_neg]

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
/-- **The convolution product of two even families composed with `ι`**, as a sum of trees with
two vertices over the nonempty sets of inputs. -/
lemma star_postι_apply {f g : GrOperad.Inv R (ConvOp R C 𝒞)}
    (hf : GrOperad.Inv.IsPar false f) (hg : GrOperad.Inv.IsPar false g) (x : C A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (postι f) (postι g)).1 A) x
      = ∑ S ∈ nonempties A, CutCobar.tw2 R V S
          (TensorProduct.map (ConvOp.toLin (f.1 (SOut S))) (ConvOp.toLin (g.1 (SIn S)))
            (GrCooperad.decomp (R := R) (C := C) none
              (SymSpecies.map (R := R) (splitEquiv S).symm x))) := by
  rw [GrOperad.Inv.star_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun S _ => ?_
  show GrOperad.map (R := R) (splitEquiv S) (ConvOp.mu none
      (ConvOp.kap ((postι f).1 (SOut S)) ((postι g).1 (SIn S))
        (GrCooperad.decomp (R := R) (C := C) none
          (SymSpecies.map (R := R) (splitEquiv S).symm x)))) = _
  rw [ConvOp.kap_hom _ (isParC_of_isPar (isPar_postι hg) (SIn S))]
  generalize GrCooperad.decomp (R := R) (C := C) (A := SOut S) (B := SIn S) none _ = t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, ConvOp.mu_tmul, CutCobar.tw2_tmul,
      LinearMap.comp_apply, postι_apply, postι_apply, toLin_tw hf]
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- **The products of the components on the decompositions of a stage of the coradical
filtration** add up to the product of the sums. -/
lemma sum_fN_tensor_eq (k N : ℕ) (hN : 2 ^ (k + 1) ≤ N) {t : C A ⊗[R] C B}
    (ht : t ∈ GrCooperad.filtTarget R C (GrCooperad.filt R C k) A B) :
    ∑ n ∈ Finset.range (N + 1), ∑ p ∈ Finset.antidiagonal n,
        TensorProduct.map (ConvOp.toLin ((fN ψ p.1).1 A)) (ConvOp.toLin ((fN ψ p.2).1 B)) t
      = TensorProduct.map (fbarL ψ hC A) (fbarL ψ hC B) t := by
  have key : GrCooperad.filtTarget R C (GrCooperad.filt R C k) A B ≤ LinearMap.eqLocus
      (∑ n ∈ Finset.range (N + 1), ∑ p ∈ Finset.antidiagonal n,
        TensorProduct.map (ConvOp.toLin ((fN ψ p.1).1 A)) (ConvOp.toLin ((fN ψ p.2).1 B)))
      (TensorProduct.map (fbarL ψ hC A) (fbarL ψ hC B)) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> refine Submodule.map₂_le.2 fun a ha b hb => ?_ <;>
      simp only [LinearMap.mem_eqLocus, TensorProduct.mk_apply, LinearMap.coe_sum,
        Finset.sum_apply, TensorProduct.map_tmul]
    · rw [fbarL_unitSpan ψ hC ha, TensorProduct.zero_tmul]
      exact Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun p _ => by
        rw [fN_unitSpan ψ p.1 ha, TensorProduct.zero_tmul]
    · rw [fbarL_unitSpan ψ hC hb, TensorProduct.tmul_zero]
      exact Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun p _ => by
        rw [fN_unitSpan ψ p.2 hb, TensorProduct.tmul_zero]
    · rw [fbarL_apply, fbarL_apply, fbarFun_eq_of_mem ψ hC ha le_rfl,
        fbarFun_eq_of_mem ψ hC hb le_rfl, TensorProduct.sum_tmul]
      simp only [TensorProduct.tmul_sum]
      refine sum_antidiag_range_eq (2 ^ k) N (by rw [pow_succ] at hN; omega)
        (fun i j => ConvOp.toLin ((fN ψ i).1 A) a ⊗ₜ[R] ConvOp.toLin ((fN ψ j).1 B) b)
        (fun i j hi => ?_) (fun i j hj => ?_)
      · show ConvOp.toLin ((fN ψ i).1 A) a ⊗ₜ[R] ConvOp.toLin ((fN ψ j).1 B) b = 0
        rw [fN_filt ψ k i hi A a ha, TensorProduct.zero_tmul]
      · show ConvOp.toLin ((fN ψ i).1 A) a ⊗ₜ[R] ConvOp.toLin ((fN ψ j).1 B) b = 0
        rw [fN_filt ψ k j hj B b hb, TensorProduct.tmul_zero]
  have h := LinearMap.mem_eqLocus.1 (key ht)
  simp only [LinearMap.coe_sum, Finset.sum_apply] at h
  exact h

/-- **The Maurer–Cartan equation of the sum of the components**: the convolution square of the
universal twisting morphism on the sum is the convolution square of the sum, as trees with two
vertices. -/
theorem jj_fbar (hV0 : ∀ v : V (Fin 0), v = 0) (x : C A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (CutCobar.j R V) (CutCobar.j R V)).1 A)
        (fbarL ψ hC A x)
      = ∑ S ∈ nonempties A, CutCobar.tw2 R V S
          (TensorProduct.map (fbarL ψ hC (SOut S)) (fbarL ψ hC (SIn S))
            (GrCooperad.decomp (R := R) (C := C) none
              (SymSpecies.map (R := R) (splitEquiv S).symm x))) := by
  obtain ⟨k, hk⟩ := hC A x
  have hx : x ∈ GrCooperad.filt R C (k + 1) A := GrCooperad.filt_mono k A hk
  have hf : fbarL ψ hC A x
      = ∑ n ∈ Finset.range (2 ^ (k + 1) + 1), ConvOp.toLin ((fN ψ n).1 A) x :=
    fbarFun_eq_of_mem ψ hC hx le_rfl
  have h1 := CutCobar.dL_jL (R := R) (V := V) (fbarL ψ hC A x)
  have h2 : (CutCobar.dL R V).app A (CutCobar.jL R V A (fbarL ψ hC A x))
      = -∑ n ∈ Finset.range (2 ^ (k + 1) + 1), ConvOp.toLin ((X ψ n).1 A) x := by
    rw [hf, map_sum, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact congrArg (fun q : GrOperad.Inv R (ConvOp R C Ω) => ConvOp.toLin (q.1 A) x)
      (appDer_τ ψ hV0 n)
  rw [neg_inj.1 (h1.symm.trans h2)]
  have h3 : ∀ n, ConvOp.toLin ((X ψ n).1 A) x
      = ∑ p ∈ Finset.antidiagonal n, ∑ S ∈ nonempties A, CutCobar.tw2 R V S
          (TensorProduct.map (ConvOp.toLin ((fN ψ p.1).1 (SOut S)))
            (ConvOp.toLin ((fN ψ p.2).1 (SIn S)))
            (GrCooperad.decomp (R := R) (C := C) none
              (SymSpecies.map (R := R) (splitEquiv S).symm x))) := fun n => by
    rw [X, inv_sum_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun p _ => star_postι_apply (isPar_fN ψ p.1) (isPar_fN ψ p.2) x
  simp only [h3]
  refine (Finset.sum_congr rfl fun n _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← sum_fN_tensor_eq ψ hC k (2 ^ (k + 1)) le_rfl
    (GrCooperad.mem_filt_succ.1 hx (SOut S) (SIn S) none (splitEquiv S))]
  simp only [map_sum]

/-- **The sum of the components respects the decompositions at the nonempty sets of inputs**, up
to the unit components of the two factors. -/
theorem secC_decomp_fbar (hV0 : ∀ v : V (Fin 0), v = 0) (x : C A) {S : Finset A}
    (hS : S ∈ nonempties A) :
    TensorProduct.map (FreeGrL.secC R V (SOut S)) (FreeGrL.secC R V (SIn S))
      (GrCooperad.decomp (R := R) (C := 𝒞) none
          (SymSpecies.map (R := R) (splitEquiv S).symm (fbarL ψ hC A x))
        - TensorProduct.map (fbarL ψ hC (SOut S)) (fbarL ψ hC (SIn S))
            (GrCooperad.decomp (R := R) (C := C) none
              (SymSpecies.map (R := R) (splitEquiv S).symm x))) = 0 := by
  refine CutCobar.tw2_inj (fun S => GrCooperad.decomp (R := R) (C := 𝒞) none
      (SymSpecies.map (R := R) (splitEquiv S).symm (fbarL ψ hC A x))
    - TensorProduct.map (fbarL ψ hC (SOut S)) (fbarL ψ hC (SIn S))
        (GrCooperad.decomp (R := R) (C := C) none
          (SymSpecies.map (R := R) (splitEquiv S).symm x))) ?_ hS
  simp only [map_sub, Finset.sum_sub_distrib]
  rw [← CutCobar.jj_apply, ← jj_fbar ψ hC hV0 x, sub_self]

/-! ## The lift -/

variable (R C) in
/-- **The unit coefficient of a cooperation**: its counit, in the arities of one element. -/
noncomputable def cuC (A : Type) [Fintype A] [DecidableEq A] : C A →ₗ[R] R :=
  ∑ e : Unit ≃ A, GrCooperad.counit (R := R) (C := C) ∘ₗ SymSpecies.map (R := R) e.symm

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
lemma cuC_eq (e : Unit ≃ A) (x : C A) :
    cuC R C A x = GrCooperad.counit (R := R) (C := C) (SymSpecies.map (R := R) e.symm x) := by
  haveI : Subsingleton (Unit ≃ A) := ⟨fun e₁ e₂ => Equiv.ext fun u =>
    (e₂.apply_symm_apply (e₁ u)).symm.trans (congrArg e₂ (Subsingleton.elim _ _))⟩
  rw [cuC, LinearMap.sum_apply, Fintype.sum_subsingleton _ e]
  rfl

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
lemma cuC_eq_zero (h : IsEmpty (Unit ≃ A)) (x : C A) : cuC R C A x = 0 := by
  rw [cuC, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun e _ => (h.false e).elim

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
lemma cuC_map (σ : A ≃ B) (x : C A) :
    cuC R C B (SymSpecies.map (R := R) σ x) = cuC R C A x := by
  by_cases h : Nonempty (Unit ≃ A)
  · obtain ⟨e⟩ := h
    rw [cuC_eq (e.trans σ), cuC_eq e]
    show GrCooperad.counit (R := R) (C := C) (SymSpecies.map (R := R) (σ.symm.trans e.symm)
      (SymSpecies.map (R := R) σ x)) = _
    rw [SymSpecies.map_trans, SymSpecies.map_symm_map]
  · rw [cuC_eq_zero (not_nonempty_iff.1 h),
      cuC_eq_zero ⟨fun e' => h ⟨e'.trans σ.symm⟩⟩]

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
lemma cuC_par (b : Bool) (x : C A) :
    cuC R C A (GrSpecies.par (R := R) b x) = if b then 0 else cuC R C A x := by
  by_cases h : Nonempty (Unit ≃ A)
  · obtain ⟨e⟩ := h
    rw [cuC_eq e, cuC_eq e, GrSpecies.map_par]
    have h1 := LinearMap.congr_fun (GrCooperad.counit_par (R := R) (C := C))
      (SymSpecies.map (R := R) e.symm x)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at h1
    cases b
    · have h2 := congrArg (GrCooperad.counit (R := R) (C := C))
        (GrSpecies.par_add (R := R) (SymSpecies.map (R := R) e.symm x))
      rw [map_add, h1, add_zero] at h2
      simpa using h2
    · simpa using h1
  · rw [cuC_eq_zero (not_nonempty_iff.1 h), cuC_eq_zero (not_nonempty_iff.1 h), ite_self]

omit [Algebra ℚ R] [GrCooperad.Coaug R C] in
/-- **An invariant family of the convolution operad commutes with relabellings.** -/
lemma inv_toLin_map {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    (q : GrOperad.Inv R (ConvOp R C Q)) (e : A ≃ B) (y : C A) :
    ConvOp.toLin (q.1 B) (SymSpecies.map (R := R) e y)
      = GrOperad.map (R := R) e (ConvOp.toLin (q.1 A) y) := by
  have h : ConvOp.mapC e (q.1 A) = q.1 B := q.2 A B e
  rw [← h, ConvOp.mapC_apply, SymSpecies.map_symm_map]

lemma fbarL_map (σ : A ≃ B) (x : C A) :
    fbarL ψ hC B (SymSpecies.map (R := R) σ x) = GrOperad.map (R := R) σ (fbarL ψ hC A x) := by
  rw [fbarL_apply, fbarL_apply,
    fbarFun_eq ψ hC (le_max_right (2 ^ stg hC x) (2 ^ stg hC (SymSpecies.map (R := R) σ x))),
    fbarFun_eq ψ hC (le_max_left (2 ^ stg hC x) (2 ^ stg hC (SymSpecies.map (R := R) σ x))),
    map_sum]
  exact Finset.sum_congr rfl fun n _ => inv_toLin_map (fN ψ n) σ x

lemma fbarL_par (b : Bool) (x : C A) :
    fbarL ψ hC A (GrSpecies.par (R := R) b x) = GrOperad.par (R := R) b (fbarL ψ hC A x) := by
  rw [fbarL_apply, fbarL_apply,
    fbarFun_eq ψ hC (le_max_right (2 ^ stg hC x) (2 ^ stg hC (GrSpecies.par (R := R) b x))),
    fbarFun_eq ψ hC (le_max_left (2 ^ stg hC x) (2 ^ stg hC (GrSpecies.par (R := R) b x))),
    map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h := isParC_of_isPar (isPar_fN ψ n) A b x
  rwa [Bool.xor_false] at h

lemma unitCoeffL_fbarL (x : C A) : unitCoeffL R V A (fbarL ψ hC A x) = 0 := by
  rw [fbarL_apply, fbarFun, map_sum]
  exact Finset.sum_eq_zero fun n _ => fN_unit ψ n x

/-- **The lift**: the coaugmentation on the unit coefficient, plus the sum of the components. -/
noncomputable def liftL (A : Type) [Fintype A] [DecidableEq A] : C A →ₗ[R] 𝒞 A :=
  (cuC R C A).smulRight (FreeGrL.unitL R V A) + fbarL ψ hC A

lemma liftL_apply (x : C A) :
    liftL ψ hC A x = cuC R C A x • FreeGrL.unitL R V A + fbarL ψ hC A x := rfl

lemma unitCoeffL_liftL (x : C A) : unitCoeffL R V A (liftL ψ hC A x) = cuC R C A x := by
  by_cases h : Nonempty (Unit ≃ A)
  · obtain ⟨e⟩ := h
    rw [liftL_apply, map_add, map_smul, unitCoeffL_fbarL, add_zero, FreeGrL.unitL_eq e,
      unitCoeffL_map, unitCoeffL_one, smul_eq_mul, mul_one]
  · rw [cuC_eq_zero (not_nonempty_iff.1 h), FreeGrL.unitCoeffL_eq_zero (not_nonempty_iff.1 h)]

/-- The part without unit component of the lift is the sum of the components. -/
lemma secC_liftL (x : C A) : FreeGrL.secC R V A (liftL ψ hC A x) = fbarL ψ hC A x := by
  rw [FreeGrL.secC_apply, unitCoeffL_liftL, liftL_apply, add_sub_cancel_left]

lemma liftL_map (σ : A ≃ B) (x : C A) :
    liftL ψ hC B (SymSpecies.map (R := R) σ x) = GrOperad.map (R := R) σ (liftL ψ hC A x) := by
  rw [liftL_apply, liftL_apply, cuC_map, map_add, map_smul, FreeGrL.map_unitL, fbarL_map]

lemma liftL_symMap (σ : A ≃ B) (x : C A) :
    liftL ψ hC B (SymSpecies.map (R := R) σ x)
      = SymSpecies.map (R := R) σ (liftL ψ hC A x) := by
  rw [liftL_map, FreeGrL.symMap_eq]

lemma liftL_par (b : Bool) (x : C A) :
    liftL ψ hC A (GrSpecies.par (R := R) b x) = GrSpecies.par (R := R) b (liftL ψ hC A x) := by
  rw [FreeGrL.grPar_eq, liftL_apply, liftL_apply, cuC_par, map_add, map_smul,
    FreeGrL.par_unitL, fbarL_par]
  cases b <;> simp

/-- **The lift is coaugmented.** -/
lemma liftL_one :
    liftL ψ hC Unit (GrCooperad.Coaug.one (R := R) (C := C))
      = GrCooperad.Coaug.one (R := R) (C := 𝒞) := by
  have h1 : cuC R C Unit (GrCooperad.Coaug.one (R := R) (C := C)) = 1 := by
    rw [cuC_eq (Equiv.refl Unit)]
    show GrCooperad.counit (R := R) (C := C) (SymSpecies.map (R := R) (Equiv.refl Unit) _) = 1
    rw [SymSpecies.map_refl]
    exact GrCooperad.Coaug.counit_one
  have h2 : GrCooperad.Coaug.one (R := R) (C := C) ∈ GrCooperad.unitSpan R C Unit := by
    have h := GrCooperad.map_one_mem (R := R) (C := C) (Equiv.refl Unit)
    rwa [SymSpecies.map_refl] at h
  rw [liftL_apply, h1, one_smul, fbarL_unitSpan ψ hC h2, add_zero,
    FreeGrL.unitL_eq (Equiv.refl Unit), GrOperad.map_refl]
  rfl

omit [GrCooperad.Coaug R C] in
/-- **The coefficient of the generators kills the trees without exactly one vertex.** -/
lemma genCoef_of_mem_vx {n : ℕ} (hn : n ≠ 1) {z : 𝒞 A} (hz : z ∈ vx R V n A) :
    genCoef R V A z = 0 := by
  have key : ∀ w : 𝒞 A, genCoef R V A ((FreeGrL.wtD R V).app A w) = genCoef R V A w := by
    intro w
    obtain ⟨y, rfl⟩ := (GrOperadIdeal.span R (grLinRel R V)).proj_surjective A w
    refine Lin.induction₁ (S := Reg (TreeOfArity (GrGen R V)))
      (genCoef R V A ∘ₗ (FreeGrL.wtD R V).app A ∘ₗ (GrOperadIdeal.span R (grLinRel R V)).proj A)
      (genCoef R V A ∘ₗ (GrOperadIdeal.span R (grLinRel R V)).proj A) (fun t => ?_) y
    show genCoef R V A ((FreeGrL.wtD R V).app A ((GrOperadIdeal.span R (grLinRel R V)).proj A
        (SgnLin.bas (treeSgn (grGenPar R V)) R t)))
      = genCoef R V A ((GrOperadIdeal.span R (grLinRel R V)).proj A
        (SgnLin.bas (treeSgn (grGenPar R V)) R t))
    rw [wtD_proj_bas, map_smul, genCoef_proj, genCoefF_bas]
    by_cases hw : (FreeGr.treeOf t).weight = 1
    · rw [hw, Nat.cast_one, one_smul]
    · rw [coefReg_of_weight_ne hw, smul_zero]
  have h := key z
  rw [Cobar.wtD_eq_derSp, mem_eig.1 hz, map_smul] at h
  have h' : ((n : R) - 1) • genCoef R V A z = 0 := by
    rw [sub_smul, one_smul, h, sub_self]
  have hu := isUnit_natCast_sub (R := R) hn
  rw [Nat.cast_one] at hu
  exact hu.smul_left_cancel.1 (h'.trans (smul_zero _).symm)

/-- **The coefficient of the generators of the lift is the given morphism.** -/
lemma genCoef_liftL (x : C A) :
    genCoef R V A (liftL ψ hC A x) = ψ.app A (GrCooperad.Red.proj R C A x) := by
  have h1 : genCoef R V A (FreeGrL.unitL R V A) = 0 := by
    rw [FreeGrL.unitL, map_sum]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [FreeGrL.genCoef_map]
    exact (congrArg _ FreeGrL.genCoef_one).trans (map_zero _)
  have h2 : genCoef R V A (fbarL ψ hC A x) = ψ.app A (GrCooperad.Red.proj R C A x) := by
    rw [fbarL_apply, fbarFun, map_sum, Finset.sum_eq_single 1]
    · rw [fN_one, f1_apply, FreeGrL.genCoef_ι]
    · intro n _ hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · rw [fN_zero]
        exact map_zero _
      · exact genCoef_of_mem_vx hn (fN_mem ψ n hpos x)
    · intro h
      exact absurd (Finset.mem_range.2 (by have := Nat.one_le_two_pow (n := stg hC x); omega)) h
  rw [liftL_apply, map_add, map_smul, h1, smul_zero, zero_add, h2]

/-! ## The lift respects the decompositions -/

omit [Algebra ℚ R] in
/-- A tensor with vanishing reduced part and vanishing unit coefficients on both sides
vanishes. -/
lemma tensor_eq_zero {t : 𝒞 A ⊗[R] 𝒞 B}
    (h1 : TensorProduct.map (FreeGrL.secC R V A) (FreeGrL.secC R V B) t = 0)
    (h2 : LinearMap.rTensor (𝒞 B) (unitCoeffL R V A) t = 0)
    (h3 : LinearMap.lTensor (𝒞 A) (unitCoeffL R V B) t = 0) : t = 0 := by
  have eA : (LinearMap.id : 𝒞 A →ₗ[R] 𝒞 A) = FreeGrL.secC R V A
      + LinearMap.toSpanSingleton R (𝒞 A) (FreeGrL.unitL R V A) ∘ₗ unitCoeffL R V A :=
    LinearMap.ext fun y => by
      rw [LinearMap.add_apply, FreeGrL.secC_apply, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, sub_add_cancel]
      rfl
  have eB : (LinearMap.id : 𝒞 B →ₗ[R] 𝒞 B) = FreeGrL.secC R V B
      + LinearMap.toSpanSingleton R (𝒞 B) (FreeGrL.unitL R V B) ∘ₗ unitCoeffL R V B :=
    LinearMap.ext fun y => by
      rw [LinearMap.add_apply, FreeGrL.secC_apply, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, sub_add_cancel]
      rfl
  have p1 : TensorProduct.map (LinearMap.toSpanSingleton R (𝒞 A) (FreeGrL.unitL R V A)
      ∘ₗ unitCoeffL R V A) (LinearMap.id : 𝒞 B →ₗ[R] 𝒞 B) t = 0 := by
    have e : TensorProduct.map (LinearMap.toSpanSingleton R (𝒞 A) (FreeGrL.unitL R V A)
        ∘ₗ unitCoeffL R V A) (LinearMap.id : 𝒞 B →ₗ[R] 𝒞 B)
        = TensorProduct.map (LinearMap.toSpanSingleton R (𝒞 A) (FreeGrL.unitL R V A))
            LinearMap.id ∘ₗ LinearMap.rTensor (𝒞 B) (unitCoeffL R V A) := by
      show _ = TensorProduct.map _ LinearMap.id ∘ₗ TensorProduct.map _ LinearMap.id
      rw [← TensorProduct.map_comp, LinearMap.id_comp]
    rw [e, LinearMap.comp_apply, h2, map_zero]
  have p2 : TensorProduct.map (FreeGrL.secC R V A)
      (LinearMap.toSpanSingleton R (𝒞 B) (FreeGrL.unitL R V B) ∘ₗ unitCoeffL R V B) t = 0 := by
    have e : TensorProduct.map (FreeGrL.secC R V A)
        (LinearMap.toSpanSingleton R (𝒞 B) (FreeGrL.unitL R V B) ∘ₗ unitCoeffL R V B)
        = TensorProduct.map (FreeGrL.secC R V A)
            (LinearMap.toSpanSingleton R (𝒞 B) (FreeGrL.unitL R V B))
          ∘ₗ LinearMap.lTensor (𝒞 A) (unitCoeffL R V B) := by
      show _ = TensorProduct.map _ _ ∘ₗ TensorProduct.map LinearMap.id _
      rw [← TensorProduct.map_comp, LinearMap.comp_id]
    rw [e, LinearMap.comp_apply, h3, map_zero]
  have key : TensorProduct.map (FreeGrL.secC R V A
      + LinearMap.toSpanSingleton R (𝒞 A) (FreeGrL.unitL R V A) ∘ₗ unitCoeffL R V A)
      (LinearMap.id : 𝒞 B →ₗ[R] 𝒞 B) t = t := by
    rw [← eA, TensorProduct.map_id, LinearMap.id_apply]
  rw [TensorProduct.map_add_left, LinearMap.add_apply, p1, add_zero] at key
  have key2 : TensorProduct.map (FreeGrL.secC R V A) (FreeGrL.secC R V B
      + LinearMap.toSpanSingleton R (𝒞 B) (FreeGrL.unitL R V B) ∘ₗ unitCoeffL R V B) t = t := by
    rw [← eB]
    exact key
  rw [TensorProduct.map_add_right, LinearMap.add_apply, h1, p2, add_zero] at key2
  exact key2.symm

/-- The unit coefficient of the lift, as a counit. -/
lemma counit_liftL (e : Unit ≃ A) (a : C A) :
    GrCooperad.counit (R := R) (C := 𝒞) (SymSpecies.map (R := R) e.symm (liftL ψ hC A a))
      = GrCooperad.counit (R := R) (C := C) (SymSpecies.map (R := R) e.symm a) := by
  rw [FreeGrL.counit_eq_unitCoeffL, FreeGrL.symMap_eq, unitCoeffL_map, unitCoeffL_liftL,
    cuC_eq e]

/-- **The lift respects the unit coefficient of the outer factor of a decomposition.** -/
lemma rTensor_unitCoeffL_decomp (i : A) (x : C (Without A i ⊕ B)) :
    LinearMap.rTensor (𝒞 B) (unitCoeffL R V A)
        (GrCooperad.decomp (R := R) (C := 𝒞) i (liftL ψ hC _ x))
      = LinearMap.rTensor (𝒞 B) (unitCoeffL R V A)
          (TensorProduct.map (liftL ψ hC A) (liftL ψ hC B)
            (GrCooperad.decomp (R := R) (C := C) i x)) := by
  by_cases h : Nonempty (Unit ≃ A)
  · obtain ⟨e⟩ := h
    have hA : ∀ a : A, a = i := fun a =>
      (e.apply_symm_apply a).symm.trans ((congrArg e (Subsingleton.elim _ _)).trans
        (e.apply_symm_apply i))
    have hu : unitCoeffL R V A = GrCooperad.counit (R := R) (C := 𝒞)
        ∘ₗ SymSpecies.map (R := R) (GrCooperad.unitTo i hA).symm := LinearMap.ext fun y => by
      rw [LinearMap.comp_apply, FreeGrL.counit_eq_unitCoeffL, FreeGrL.symMap_eq, unitCoeffL_map]
    have hR : ∀ t : C A ⊗[R] C B, TensorProduct.lid R (𝒞 B) (LinearMap.rTensor (𝒞 B)
        (GrCooperad.counit (R := R) (C := 𝒞)
          ∘ₗ SymSpecies.map (R := R) (GrCooperad.unitTo i hA).symm)
        (TensorProduct.map (liftL ψ hC A) (liftL ψ hC B) t))
        = liftL ψ hC B (TensorProduct.lid R (C B) (LinearMap.rTensor (C B)
          (GrCooperad.counit (R := R) (C := C)
            ∘ₗ SymSpecies.map (R := R) (GrCooperad.unitTo i hA).symm) t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a b =>
        simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
          TensorProduct.lid_tmul, map_smul, counit_liftL]
      | add t t' ht ht' => simp only [map_add, ht, ht']
    apply (TensorProduct.lid R (𝒞 B)).injective
    rw [hu, GrCooperad.lid_counit_decomp i hA, hR, GrCooperad.lid_counit_decomp i hA,
      liftL_symMap]
  · have hu : unitCoeffL R V A = 0 := LinearMap.ext fun y =>
      FreeGrL.unitCoeffL_eq_zero (not_nonempty_iff.1 h) y
    rw [hu, LinearMap.rTensor_zero, LinearMap.zero_apply, LinearMap.zero_apply]

/-- **The lift respects the unit coefficient of the inner factor of a decomposition.** -/
lemma lTensor_unitCoeffL_decomp (i : A) (x : C (Without A i ⊕ B)) :
    LinearMap.lTensor (𝒞 A) (unitCoeffL R V B)
        (GrCooperad.decomp (R := R) (C := 𝒞) i (liftL ψ hC _ x))
      = LinearMap.lTensor (𝒞 A) (unitCoeffL R V B)
          (TensorProduct.map (liftL ψ hC A) (liftL ψ hC B)
            (GrCooperad.decomp (R := R) (C := C) i x)) := by
  by_cases h : Nonempty (Unit ≃ B)
  · obtain ⟨e⟩ := h
    have hB : ∀ b : B, b = e () := fun b =>
      (e.apply_symm_apply b).symm.trans (congrArg e (Subsingleton.elim _ _))
    have hu : unitCoeffL R V B = GrCooperad.counit (R := R) (C := 𝒞)
        ∘ₗ SymSpecies.map (R := R) (GrCooperad.unitTo (e ()) hB).symm :=
      LinearMap.ext fun y => by
        rw [LinearMap.comp_apply, FreeGrL.counit_eq_unitCoeffL, FreeGrL.symMap_eq,
          unitCoeffL_map]
    have hR : ∀ t : C A ⊗[R] C B, TensorProduct.rid R (𝒞 A) (LinearMap.lTensor (𝒞 A)
        (GrCooperad.counit (R := R) (C := 𝒞)
          ∘ₗ SymSpecies.map (R := R) (GrCooperad.unitTo (e ()) hB).symm)
        (TensorProduct.map (liftL ψ hC A) (liftL ψ hC B) t))
        = liftL ψ hC A (TensorProduct.rid R (C A) (LinearMap.lTensor (C A)
          (GrCooperad.counit (R := R) (C := C)
            ∘ₗ SymSpecies.map (R := R) (GrCooperad.unitTo (e ()) hB).symm) t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a b =>
        simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.comp_apply,
          TensorProduct.rid_tmul, map_smul, counit_liftL]
      | add t t' ht ht' => simp only [map_add, ht, ht']
    apply (TensorProduct.rid R (𝒞 A)).injective
    rw [hu, GrCooperad.rid_counit_decomp i (e ()) hB, hR,
      GrCooperad.rid_counit_decomp i (e ()) hB, liftL_symMap]
  · have hu : unitCoeffL R V B = 0 := LinearMap.ext fun y =>
      FreeGrL.unitCoeffL_eq_zero (not_nonempty_iff.1 h) y
    rw [hu, LinearMap.lTensor_zero, LinearMap.zero_apply, LinearMap.zero_apply]

omit [Algebra ℚ R] in
/-- The part without unit component kills the coaugmentation of the cut cooperad. -/
lemma secC_of_mem_unitSpan {a : 𝒞 A} (ha : a ∈ GrCooperad.unitSpan R 𝒞 A) :
    FreeGrL.secC R V A a = 0 := by
  have h0 : GrCooperad.Red.proj R 𝒞 A a = 0 := (Submodule.Quotient.mk_eq_zero _).2 ha
  rw [← FreeGrL.secR_proj, h0, map_zero]

omit [Algebra ℚ R] in
lemma unitL_mem_unitSpan : FreeGrL.unitL R V A ∈ GrCooperad.unitSpan R 𝒞 A := by
  rw [FreeGrL.unitL]
  refine Submodule.sum_mem _ fun e _ => ?_
  have h := GrCooperad.map_one_mem (R := R) (C := 𝒞) e
  rwa [FreeGrL.symMap_eq] at h

/-- **The lift respects the decompositions at the splittings of the inputs.** -/
theorem decomp_liftL_split (hV0 : ∀ v : V (Fin 0), v = 0) (S : Finset A)
    (x : C (Without (SOut S) none ⊕ SIn S)) :
    GrCooperad.decomp (R := R) (C := 𝒞) none (liftL ψ hC _ x)
      = TensorProduct.map (liftL ψ hC (SOut S)) (liftL ψ hC (SIn S))
          (GrCooperad.decomp (R := R) (C := C) none x) := by
  by_cases hS : S.Nonempty
  · refine sub_eq_zero.1 (tensor_eq_zero ?_ ?_ ?_)
    · -- the reduced parts
      have hx : x = SymSpecies.map (R := R) (splitEquiv S).symm
          (SymSpecies.map (R := R) (splitEquiv S) x) := (SymSpecies.map_symm_map _ x).symm
      have h1 := secC_decomp_fbar ψ hC hV0 (SymSpecies.map (R := R) (splitEquiv S) x)
        (Finset.mem_filter.2 ⟨Finset.mem_univ S, hS⟩)
      rw [FreeGrL.symMap_eq, ← fbarL_map, ← hx] at h1
      have h2 : TensorProduct.map (FreeGrL.secC R V (SOut S)) (FreeGrL.secC R V (SIn S))
          (GrCooperad.decomp (R := R) (C := 𝒞) none (liftL ψ hC _ x))
          = TensorProduct.map (FreeGrL.secC R V (SOut S)) (FreeGrL.secC R V (SIn S))
            (GrCooperad.decomp (R := R) (C := 𝒞) none (fbarL ψ hC _ x)) := by
        rw [liftL_apply, map_add, map_add, map_smul, map_smul]
        have hu := GrCooperad.decomp_mem_unitSpan (R := R) (C := 𝒞) (A := SOut S) (B := SIn S)
          none (unitL_mem_unitSpan (R := R) (V := V))
        have hle : SymCooperad.tensSub R (GrCooperad.unitSpan R 𝒞 (SOut S))
            (GrCooperad.unitSpan R 𝒞 (SIn S)) ≤ LinearMap.ker (TensorProduct.map
              (FreeGrL.secC R V (SOut S)) (FreeGrL.secC R V (SIn S))) :=
          Submodule.map₂_le.2 fun a ha b _ => by
            rw [LinearMap.mem_ker, TensorProduct.mk_apply, TensorProduct.map_tmul,
              secC_of_mem_unitSpan ha, TensorProduct.zero_tmul]
        rw [LinearMap.mem_ker.1 (hle hu), smul_zero, zero_add]
      have h3 : TensorProduct.map (FreeGrL.secC R V (SOut S)) (FreeGrL.secC R V (SIn S))
          (TensorProduct.map (liftL ψ hC (SOut S)) (liftL ψ hC (SIn S))
            (GrCooperad.decomp (R := R) (C := C) none x))
          = TensorProduct.map (fbarL ψ hC (SOut S)) (fbarL ψ hC (SIn S))
            (GrCooperad.decomp (R := R) (C := C) none x) := by
        rw [← LinearMap.comp_apply, ← TensorProduct.map_comp,
          show FreeGrL.secC R V (SOut S) ∘ₗ liftL ψ hC (SOut S) = fbarL ψ hC (SOut S) from
            LinearMap.ext (secC_liftL ψ hC),
          show FreeGrL.secC R V (SIn S) ∘ₗ liftL ψ hC (SIn S) = fbarL ψ hC (SIn S) from
            LinearMap.ext (secC_liftL ψ hC)]
      have h4 : TensorProduct.map (FreeGrL.secC R V (SOut S)) (FreeGrL.secC R V (SIn S))
          (TensorProduct.map (fbarL ψ hC (SOut S)) (fbarL ψ hC (SIn S))
            (GrCooperad.decomp (R := R) (C := C) none x))
          = TensorProduct.map (fbarL ψ hC (SOut S)) (fbarL ψ hC (SIn S))
            (GrCooperad.decomp (R := R) (C := C) none x) := by
        rw [← LinearMap.comp_apply, ← TensorProduct.map_comp,
          show FreeGrL.secC R V (SOut S) ∘ₗ fbarL ψ hC (SOut S) = fbarL ψ hC (SOut S) from
            LinearMap.ext fun y => FreeGrL.secC_of_unitCoeff (unitCoeffL_fbarL ψ hC y),
          show FreeGrL.secC R V (SIn S) ∘ₗ fbarL ψ hC (SIn S) = fbarL ψ hC (SIn S) from
            LinearMap.ext fun y => FreeGrL.secC_of_unitCoeff (unitCoeffL_fbarL ψ hC y)]
      rw [map_sub, h4] at h1
      rw [map_sub, h2, h3]
      exact h1
    · rw [map_sub, rTensor_unitCoeffL_decomp, sub_self]
    · rw [map_sub, lTensor_unitCoeffL_decomp, sub_self]
  · haveI : IsEmpty (SIn S) := ⟨fun b => hS ⟨b.1, b.2⟩⟩
    have hz : ∀ t : 𝒞 (SOut S) ⊗[R] 𝒞 (SIn S), t = 0 := fun t => by
      induction t using TensorProduct.induction_on with
      | zero => rfl
      | tmul a b => rw [CutCobar.eq_zero_of_isEmpty hV0 b, TensorProduct.tmul_zero]
      | add t t' ht ht' => rw [ht, ht', add_zero]
    rw [hz (GrCooperad.decomp (R := R) (C := 𝒞) none (liftL ψ hC _ x)),
      hz (TensorProduct.map _ _ _)]

/-- **The lift, as a morphism of graded cooperads.** -/
noncomputable def liftHom (hV0 : ∀ v : V (Fin 0), v = 0) : GrCooperadHom R C 𝒞 where
  app := liftL ψ hC
  app_map e x := liftL_symMap ψ hC e x
  app_par b x := liftL_par ψ hC b x
  counit_app := LinearMap.ext fun x => by
    have h := counit_liftL ψ hC (Equiv.refl Unit) x
    rw [show (Equiv.refl Unit).symm = Equiv.refl Unit from rfl, SymSpecies.map_refl,
      SymSpecies.map_refl] at h
    exact h
  decomp_app i := LinearMap.ext fun x =>
    GrCooperad.decomp_app_of_split (K := C) (D := 𝒞)
      ⟨liftL ψ hC, fun e x => liftL_symMap ψ hC e x⟩
      (fun _ _ _ S x => decomp_liftL_split ψ hC hV0 S x) i x

lemma liftHom_app (hV0 : ∀ v : V (Fin 0), v = 0) (x : C A) :
    (liftHom ψ hC hV0).app A x = liftL ψ hC A x := rfl

end CutLift

/-! ## The universal property -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {A : Type} [Fintype A] [DecidableEq A] [Algebra ℚ R]

local notation "𝟙" => GrCooperad.Coaug.one (R := R) (C := C)

/-- **The coaugmented morphism into the cut cooperad given by a morphism from the reduced part**,
on a conilpotent cooperad: no projectivity is assumed. -/
noncomputable def liftCut (hV0 : ∀ v : V (Fin 0), v = 0) (hC : GrCooperad.Conilpotent R C)
    (ψ : GrSpeciesHom R (GrCooperad.Red R C) V) : GrCooperadHom R C (FreeGrL R V) :=
  CutLift.liftHom ψ hC hV0

lemma liftCut_app_one (hV0 : ∀ v : V (Fin 0), v = 0) (hC : GrCooperad.Conilpotent R C)
    (ψ : GrSpeciesHom R (GrCooperad.Red R C) V) :
    (liftCut hV0 hC ψ).app Unit 𝟙 = GrCooperad.Coaug.one (R := R) (C := FreeGrL R V) :=
  CutLift.liftL_one ψ hC

/-- **The cogenerator part of the lift is the given morphism.** -/
lemma genCoef_liftCut (hV0 : ∀ v : V (Fin 0), v = 0) (hC : GrCooperad.Conilpotent R C)
    (ψ : GrSpeciesHom R (GrCooperad.Red R C) V) (x : C A) :
    genCoef R V A ((liftCut hV0 hC ψ).app A x) = ψ.app A (GrCooperad.Red.proj R C A x) :=
  CutLift.genCoef_liftL ψ hC x

/-- **The universal property of the cut cooperad on a species with elements of one input, without
projectivity**: over a `ℚ`-algebra, for a graded linear species `V` without elements without
inputs and a conilpotent coaugmented graded cooperad `C`, the coaugmented morphisms of graded
cooperads `C → T^c(V)` are the morphisms of graded linear species `C̄ → V` from the reduced part,
by composition with the projection onto the cogenerators. -/
noncomputable def cofreeHomEquivCut (hV0 : ∀ v : V (Fin 0), v = 0)
    (hC : GrCooperad.Conilpotent R C) :
    {f : GrCooperadHom R C (FreeGrL R V) //
      f.app Unit 𝟙 = GrCooperad.Coaug.one (R := R) (C := FreeGrL R V)} ≃
    GrSpeciesHom R (GrCooperad.Red R C) V where
  toFun f := redLift ((genCoefHom R V).comp f.1.toGrSpeciesHom)
    fun _ _ _ => genCoef_app_unitSpan f.1 f.2
  invFun ψ := ⟨liftCut hV0 hC ψ, liftCut_app_one hV0 hC ψ⟩
  left_inv f := Subtype.ext (GrCooperadHom.ext (app_eq_of_genCoef₀ hV0
    fun _ _ _ x => genCoef_liftCut hV0 hC _ x))
  right_inv ψ := GrSpeciesHom.ext fun A _ _ X => by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective A X
    exact genCoef_liftCut hV0 hC ψ x

lemma cofreeHomEquivCut_apply (hV0 : ∀ v : V (Fin 0), v = 0)
    (hC : GrCooperad.Conilpotent R C)
    (f : {f : GrCooperadHom R C (FreeGrL R V) //
      f.app Unit 𝟙 = GrCooperad.Coaug.one (R := R) (C := FreeGrL R V)}) (x : C A) :
    (cofreeHomEquivCut hV0 hC f).app A (GrCooperad.Red.proj R C A x)
      = genCoef R V A (f.1.app A x) :=
  rfl

/-- **The cofree property of the cut cooperad on a species with elements of one input, without
projectivity**: on a conilpotent coaugmented graded cooperad, every morphism of graded linear
species into a graded linear species `V` without elements without inputs killing the
coaugmentation lifts uniquely to a morphism of graded cooperads into `T^c(V)`, over a
`ℚ`-algebra. The lift is coaugmented (`FreeGrL.liftCut_app_one`). -/
theorem existsUnique_liftCut (hV0 : ∀ v : V (Fin 0), v = 0)
    (hC : GrCooperad.Conilpotent R C) {φ : GrSpeciesHom R C V}
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A],
      GrCooperad.unitSpan R C A ≤ LinearMap.ker (φ.app A)) :
    ∃! f : GrCooperadHom R C (FreeGrL R V), ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      genCoef R V A (f.app A x) = φ.app A x :=
  ⟨liftCut hV0 hC (redLift φ hφ), fun _ _ _ x => genCoef_liftCut hV0 hC (redLift φ hφ) x,
    fun _ hf => GrCooperadHom.ext (app_eq_of_genCoef₀ hV0 fun A _ _ x =>
      (hf A x).trans (genCoef_liftCut hV0 hC (redLift φ hφ) x).symm)⟩

end FreeGrL

end Operad
