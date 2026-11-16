/-
# Coefficients of convolution products

A **system of coefficients** up to order `n` from a graded operad `O` to a graded operad `Q`
(`CoefSys`) is a sequence of linear maps `cₖ : O A → Q A` commuting with the parity projections
and the relabellings, with `cₘ (z ∘ᵢ w) = ∑_{a+b=m} cₐ z ∘ᵢ c_b w` for `m ≤ n`. The coefficients
of the truncated polynomials `Q[t]/tⁿ⁺¹` are one (`TruncOp.coefSys`, in `DeformationLift.lean`).

For a graded cooperad `C`, composing with `cₖ` takes the invariant families of the convolution
operad `Hom(C, O)` to those of `Hom(C, Q)` (`CoefSys.coefI`), preserving parities
(`CoefSys.isPar_coefI`), and **the coefficients of a convolution product are the Cauchy product
of the coefficients** (`CoefSys.coefI_star`): `cₘ (X ⋆ Y) = ∑_{a+b=m} cₐ X ⋆ c_b Y` for `m ≤ n`.
-/
import Operad.InvLie
import Mathlib.Algebra.BigOperators.NatAntidiagonal

universe u v w

namespace Operad

open Sym GerBV Finset
open scoped TensorProduct

/-- **A system of coefficients up to order `n`** from a graded operad `O` to a graded operad
`Q`: linear maps `cₖ : O → Q` commuting with the parity projections and the relabellings, with
the Cauchy rule `cₖ (z ∘ᵢ w) = ∑_{a+b=k} cₐ z ∘ᵢ c_b w` for `k ≤ n`. -/
structure CoefSys (R : Type u) [CommRing R]
    (O : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (O A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (O A)] [GrOperad R O]
    (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] (n : ℕ) where
  /-- The coefficient of order `k`. -/
  c (k : ℕ) (A : Type) [Fintype A] [DecidableEq A] : O A →ₗ[R] Q A
  c_par (k : ℕ) {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (z : O A) :
    c k A (GrOperad.par (R := R) b z) = GrOperad.par (R := R) b (c k A z)
  c_map (k : ℕ) {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (z : O A) : c k B (GrOperad.map (R := R) e z) = GrOperad.map (R := R) e (c k A z)
  c_comp {k : ℕ} (hk : k ≤ n) {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (i : A) (z : O A) (w : O B) :
    c k _ (GrOperad.comp (R := R) i z w)
      = ∑ p ∈ antidiagonal k, GrOperad.comp (R := R) i (c p.1 A z) (c p.2 B w)

namespace CoefSys

variable {R : Type u} [CommRing R]
  {O : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (O A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (O A)] [GrOperad R O]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {n : ℕ}
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  (S : CoefSys R O Q n)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

open ConvOp

/-- Taking a coefficient commutes with the parity projections of the convolution operad. -/
lemma postL_parC (k : ℕ) (q : Bool) (g : ConvOp R C O A) :
    postL (S.c k A) (parC q g) = parC q (postL (C := C) (S.c k A) g) := by
  ext x
  simp only [toLin_postL, LinearMap.comp_apply, parC_apply, map_sum, S.c_par]

/-- Taking a coefficient commutes with the relabellings of the convolution operad. -/
lemma postL_mapC (k : ℕ) (e : A ≃ B) (g : ConvOp R C O A) :
    postL (S.c k B) (mapC e g) = mapC e (postL (C := C) (S.c k A) g) := by
  ext x
  simp only [toLin_postL, LinearMap.comp_apply, mapC_apply, S.c_map]

/-- **The coefficients of a composite in the convolution operad are the Cauchy product of the
coefficients.** -/
theorem c_compC {m : ℕ} (hm : m ≤ n) (i : A) (f : ConvOp R C O A) (g : ConvOp R C O B)
    (x : C (Without A i ⊕ B)) :
    S.c m _ (toLin (compC i f g) x)
      = ∑ p ∈ antidiagonal m,
          toLin (compC i (postL (C := C) (S.c p.1 A) f) (postL (C := C) (S.c p.2 B) g)) x := by
  simp only [toLin_compC, LinearMap.comp_apply]
  induction GrCooperad.decomp (R := R) (C := C) i x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [kap, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
      LinearMap.comp_apply, mu_tmul, S.c_comp hm, ← S.postL_parC, toLin_postL]
    exact Finset.sum_comm
  | add a b ha hb =>
    simp only [map_add, ha, hb, Finset.sum_add_distrib]

/-- **The coefficient of an invariant family of the convolution operad.** -/
def coefI (k : ℕ) : GrOperad.Inv R (ConvOp R C O) →ₗ[R] GrOperad.Inv R (ConvOp R C Q) where
  toFun X := ⟨fun A _ _ => postL (S.c k A) (X.1 A), fun A B _ _ _ _ e => by
    show mapC e (postL (S.c k A) (X.1 A)) = postL (S.c k B) (X.1 B)
    rw [← S.postL_mapC]
    exact congrArg (postL (S.c k B)) (X.2 A B e)⟩
  map_add' X Y := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_add (postL (C := C) (S.c k A)) _ _)
  map_smul' a X := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_smul (postL (C := C) (S.c k A)) _ _)

lemma coefI_apply (k : ℕ) (X : GrOperad.Inv R (ConvOp R C O)) (x : C A) :
    toLin ((S.coefI k X).1 A) x = S.c k A (toLin (X.1 A) x) := rfl

/-- Coefficients preserve parities. -/
lemma isPar_coefI (k : ℕ) {p : Bool} {X : GrOperad.Inv R (ConvOp R C O)}
    (hX : GrOperad.Inv.IsPar p X) : GrOperad.Inv.IsPar p (S.coefI k X) := fun A _ _ => by
  show parC p (postL (S.c k A) (X.1 A)) = postL (S.c k A) (X.1 A)
  rw [← S.postL_parC]
  exact congrArg (postL (S.c k A)) (hX A)

/-- **The coefficients of a convolution product are the Cauchy product of the coefficients**:
`cₘ (X ⋆ Y) = ∑_{a+b=m} cₐ X ⋆ c_b Y` for `m ≤ n`. -/
theorem coefI_star {m : ℕ} (hm : m ≤ n) (X Y : GrOperad.Inv R (ConvOp R C O)) :
    S.coefI m (GrOperad.Inv.star R _ X Y)
      = ∑ p ∈ antidiagonal m, GrOperad.Inv.star R _ (S.coefI p.1 X) (S.coefI p.2 Y) := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun x => ?_)
  have hR : ∀ (s : Finset (ℕ × ℕ)),
      toLin ((∑ p ∈ s, GrOperad.Inv.star R _ (S.coefI p.1 X) (S.coefI p.2 Y)).1 A) x
        = ∑ p ∈ s, toLin ((GrOperad.Inv.star R _ (S.coefI p.1 X) (S.coefI p.2 Y)).1 A) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      rfl
  rw [hR, coefI_apply, GrOperad.Inv.star_apply, toLin_sum, LinearMap.sum_apply, map_sum]
  simp only [GrOperad.Inv.star_apply, toLin_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  show S.c m A (toLin (mapC (splitEquiv T)
      (compC none (X.1 (SOut T)) (Y.1 (SIn T)))) x)
    = ∑ p ∈ antidiagonal m, toLin (mapC (splitEquiv T)
        (compC none (postL (S.c p.1 _) (X.1 (SOut T)))
          (postL (S.c p.2 _) (Y.1 (SIn T))))) x
  simp only [mapC_apply]
  rw [S.c_map, S.c_compC hm, map_sum]

end CoefSys

end Operad
