/-
# The Rees operad of a weighted set operad

`Operad.Rees` builds, for a weight `W` on a set operad `S`, the twisted linearizations
`TwLin R W h`: the Rees family at `h = X` over `R[X]`, the linearization at `h = 1`, the
associated graded `Gr R W` at `h = 0`. This file identifies that family with the Rees operad
(`Operad.PolyOperad`, `Operad.ReesFiber`) of the weight filtration `W.filtration R` of `Lin R S`.

* **The Rees family is the Rees operad** (`SetOperadWeight.reesIso`): `TwLin R[X] W X ≅ Rees`, an
  isomorphism of operads over `R[X]`, the basis element `s` going to `X^(w s) s`
  (`SetOperadWeight.reesGen`). The coefficient of `ħⁿ` at `s` of the image of `x` is the
  coefficient of `X^(n - w s)` of `x s` (`SetOperadWeight.toRees_coeff`), which gives
  injectivity; `ħⁿ s` with `w s ≤ n` is the image of `X^(n - w s) s`, which gives surjectivity.
* **The fibers** (`SetOperadWeight.reesModIso`): `Rees / (ħ - c) ≅ TwLin R W c` over `R`, through
  the specialization of `Operad.Rees` (`TwLin.specializeHom`). At `c = 0`, **the associated
  graded operad of the weight filtration is `Gr R W`** (`SetOperadWeight.grIso`).
-/
import Operad.Rees
import Operad.ReesFiber

universe u v

namespace PolynomialModule

open Polynomial

variable {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

lemma X_pow_smul_single (d p : ℕ) (m : M) :
    (X : R[X]) ^ d • single R p m = single R (d + p) m := by
  rw [← Polynomial.monomial_one_right_eq_X_pow, monomial_smul_single, one_smul]

end PolynomialModule

namespace Operad

open Polynomial

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  (R : Type u) [CommRing R] (W : SetOperadWeight S)

namespace SetOperadWeight

/-- **The monomial `X^(w s) s`** of the Rees operad of the weight filtration. -/
noncomputable def reesGen (A : Type) [Fintype A] [DecidableEq A] (s : S A) :
    (W.filtration R).Rees A :=
  ⟨PolyOp.single (R := R) (W.w A s) (Finsupp.single s (1 : R) : Lin R S A),
    (W.filtration R).single_mem_reesSub
      (Finsupp.single_mem_supported R (1 : R) (by
        show W.w A s ≤ W.w A s
        exact le_refl _))⟩

lemma reesGen_val {A : Type} [Fintype A] [DecidableEq A] (s : S A) :
    (W.reesGen R A s).1 =
      PolyOp.single (R := R) (W.w A s) (Finsupp.single s (1 : R) : Lin R S A) := rfl

/-- **The Rees family of a weighted set operad maps to the Rees operad of its weight
filtration**: the basis element `s` goes to `X^(w s) s`. -/
noncomputable def toRees : SymOperadHom R[X] (TwLin R[X] W X) (W.filtration R).Rees :=
  TwLin.liftHom W X (fun A _ _ s => W.reesGen R A s)
    (fun e s => Subtype.ext (by
      show PolyOp.single (R := R) _ _ = SymOperad.map (R := R[X]) e (PolyOp.single (R := R) _ _)
      rw [PolyOp.map_single, W.w_map]
      exact congrArg _ (Lin.mapL_single (R := R) e s 1).symm))
    (Subtype.ext (by
      show PolyOp.single (R := R) _ _ = PolyOp.single (R := R) 0 _
      rw [W.w_one]
      rfl))
    (fun i s t => Subtype.ext (by
      show (X : R[X]) ^ W.defect i s t • PolynomialModule.single R _ _ =
        SymOperad.comp (R := R[X]) i (PolyOp.single (R := R) _ _) (PolyOp.single (R := R) _ _)
      rw [PolynomialModule.X_pow_smul_single, PolyOp.comp_single, add_comm,
        W.w_comp_add_defect]
      refine congrArg _ ?_
      show _ = Lin.compL R i (Finsupp.single s 1) (Finsupp.single t 1)
      rw [Lin.compL_single, mul_one]))

lemma toRees_single {A : Type} [Fintype A] [DecidableEq A] (s : S A) (q : R[X]) :
    (W.toRees R).app A (TwLin.single W X s q) = q • W.reesGen R A s :=
  TwLin.liftHom_single W X _ _ _ _ s q

/-- **The coefficients of the image**: the coefficient of `ħⁿ` at `s` is the coefficient of
`X^(n - w s)` of the coefficient of `s`. -/
theorem toRees_coeff {A : Type} [Fintype A] [DecidableEq A] (x : TwLin R[X] W X A) (n : ℕ)
    (s : S A) :
    (show S A →₀ R from PolyOp.coeff ((W.toRees R).app A x).1 n) s =
      if W.w A s ≤ n then ((show S A →₀ R[X] from x) s).coeff (n - W.w A s) else 0 := by
  induction x using TwLin.induction with
  | h0 =>
    rw [map_zero]
    show (0 : R) = if W.w A s ≤ n then ((0 : S A →₀ R[X]) s).coeff (n - W.w A s) else 0
    rw [Finsupp.zero_apply, Polynomial.coeff_zero, ite_self]
  | hadd x y hx hy =>
    rw [map_add]
    show (show S A →₀ R from PolyOp.coeff ((W.toRees R).app A x).1 n) s +
      (show S A →₀ R from PolyOp.coeff ((W.toRees R).app A y).1 n) s = _
    rw [hx, hy]
    show _ = if W.w A s ≤ n then (((show S A →₀ R[X] from x) s) +
      ((show S A →₀ R[X] from y) s)).coeff (n - W.w A s) else 0
    split_ifs
    · rw [Polynomial.coeff_add]
    · rw [add_zero]
  | hsingle s' q =>
    rw [toRees_single]
    show (show S A →₀ R from (q • PolynomialModule.single R (W.w A s')
      (Finsupp.single s' (1 : R) : Lin R S A)) n) s =
      if W.w A s ≤ n then ((Finsupp.single s' q : S A →₀ R[X]) s).coeff (n - W.w A s) else 0
    rw [PolynomialModule.smul_single_apply]
    by_cases hs : s' = s
    · subst hs
      rw [Finsupp.single_eq_same]
      split_ifs
      · show (q.coeff (n - W.w A s') • (Finsupp.single s' (1 : R) : S A →₀ R)) s' = _
        rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
      · rfl
    · rw [Finsupp.single_eq_of_ne' hs, Polynomial.coeff_zero, ite_self]
      split_ifs
      · show (q.coeff (n - W.w A s') • (Finsupp.single s' (1 : R) : S A →₀ R)) s = 0
        rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne' hs, smul_zero]
      · rfl

/-- **The comparison is injective.** -/
theorem toRees_injective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective ((W.toRees R).app A) :=
  (injective_iff_map_eq_zero _).2 fun x hx => by
    refine Finsupp.ext fun s => Polynomial.ext fun k => ?_
    have h := W.toRees_coeff R x (k + W.w A s) s
    rw [hx, if_pos (Nat.le_add_left _ _), Nat.add_sub_cancel] at h
    exact h.symm

/-- **The comparison is surjective**: `ħⁿ s` with `w s ≤ n` is the image of `X^(n - w s) s`. -/
theorem toRees_surjective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Surjective ((W.toRees R).app A) := by
  intro f
  have key : ∀ (n : ℕ) (s : S A) (a : R) (h : W.w A s ≤ n),
      (⟨PolyOp.single (R := R) n (Finsupp.single s a : Lin R S A),
        (W.filtration R).single_mem_reesSub (Finsupp.single_mem_supported R a h)⟩ :
        (W.filtration R).Rees A) ∈ LinearMap.range ((W.toRees R).app A) := fun n s a h => by
    refine ⟨TwLin.single W X s (Polynomial.monomial (n - W.w A s) a), ?_⟩
    rw [toRees_single]
    refine Subtype.ext ?_
    show Polynomial.monomial (n - W.w A s) a • PolynomialModule.single R (W.w A s)
      (Finsupp.single s (1 : R) : Lin R S A) = PolynomialModule.single R n _
    rw [PolynomialModule.monomial_smul_single, Nat.sub_add_cancel h]
    refine congrArg _ ?_
    show a • (Finsupp.single s (1 : R) : S A →₀ R) = Finsupp.single s a
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  suffices h : f ∈ LinearMap.range ((W.toRees R).app A) from h
  obtain ⟨t, ht⟩ := PolyOp.sum_single f.1
  have hf : f = ∑ n ∈ t, (⟨PolyOp.single (R := R) n (PolyOp.coeff f.1 n),
      (W.filtration R).single_mem_reesSub (f.2 n)⟩ : (W.filtration R).Rees A) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sum]
    exact ht
  rw [hf]
  refine Submodule.sum_mem _ fun n _ => ?_
  have hm : (show S A →₀ R from PolyOp.coeff f.1 n) ∈
      Finsupp.supported R R {s | W.w A s ≤ n} := f.2 n
  have hsum : (⟨PolyOp.single (R := R) n (PolyOp.coeff f.1 n),
      (W.filtration R).single_mem_reesSub (f.2 n)⟩ : (W.filtration R).Rees A) =
      ∑ s ∈ (show S A →₀ R from PolyOp.coeff f.1 n).support.attach,
        (⟨PolyOp.single (R := R) n
          (Finsupp.single s.1 ((show S A →₀ R from PolyOp.coeff f.1 n) s.1) : Lin R S A),
          (W.filtration R).single_mem_reesSub (Finsupp.single_mem_supported R _
            ((Finsupp.mem_supported R _).1 hm s.2))⟩ : (W.filtration R).Rees A) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sum]
    show PolynomialModule.single R n (PolyOp.coeff f.1 n) =
      ∑ s ∈ (show S A →₀ R from PolyOp.coeff f.1 n).support.attach,
        PolynomialModule.single R n
          (Finsupp.single s.1 ((show S A →₀ R from PolyOp.coeff f.1 n) s.1) : Lin R S A)
    rw [← map_sum (PolynomialModule.single R n : Lin R S A →+ PolynomialModule R (Lin R S A))]
    refine congrArg _ ?_
    rw [Finset.sum_attach _ (fun s => (Finsupp.single s
      ((show S A →₀ R from PolyOp.coeff f.1 n) s) : S A →₀ R))]
    exact (Finsupp.sum_single (show S A →₀ R from PolyOp.coeff f.1 n)).symm
  rw [hsum]
  exact Submodule.sum_mem _ fun s _ => key n s.1 _ ((Finsupp.mem_supported R _).1 hm s.2)

/-- **The Rees family of a weighted set operad is the Rees operad of its weight filtration**:
`TwLin R[X] W X ≅ Rees`, an isomorphism of operads over `R[X]`. -/
noncomputable def reesIso : SymOperadIso R[X] (TwLin R[X] W X) (W.filtration R).Rees :=
  SymOperadIso.ofBijective (W.toRees R) fun A _ _ =>
    ⟨W.toRees_injective R A, W.toRees_surjective R A⟩

end SetOperadWeight

/-! ## The fibers -/

namespace TwLin

variable {R} (c : R)

/-- **Specialization of the Rees family at `X = c`**, as a morphism of operads over `R`. -/
noncomputable def specializeHom :
    SymOperadHom R (ResOp R R[X] (TwLin R[X] W X)) (TwLin R W c) where
  app A _ _ :=
    { toFun := specializeL W c A
      map_add' := map_add (specializeL W c A)
      map_smul' := fun r x => by
        show specializeL W c A (algebraMap R R[X] r • (show TwLin R[X] W X A from x)) = _
        rw [specializeL_smul, ← Polynomial.C_eq_algebraMap, Polynomial.eval_C]
        rfl }
  app_map e x := (specialize W c).app_map e x
  app_one := (specialize W c).app_one
  app_comp i x y := (specialize W c).app_comp i x y

lemma specializeHom_app {A : Type} [Fintype A] [DecidableEq A] (x : TwLin R[X] W X A) :
    (specializeHom W c).app A x = specializeL W c A x := rfl

end TwLin

namespace SetOperadWeight

variable {R}

/-- **Specialization of the Rees operad of the weight filtration** at `ħ = c`, onto the twisted
linearization at `c`. -/
noncomputable def reesSpecialize (c : R) :
    SymOperadHom R (ResOp R R[X] (W.filtration R).Rees) (TwLin R W c) :=
  (TwLin.specializeHom W c).comp ((W.reesIso R).inv.res R)

lemma reesSpecialize_surjective (c : R) (A : Type) [Fintype A] [DecidableEq A] :
    Function.Surjective ((W.reesSpecialize c).app A) := fun y => by
  obtain ⟨x, hx⟩ := TwLin.specializeL_surjective W c (A := A) y
  exact ⟨(W.reesIso R).hom.app A x, by
    show TwLin.specializeL W c A ((W.reesIso R).inv.app A ((W.reesIso R).hom.app A x)) = y
    rw [SymOperadIso.inv_hom_apply, hx]⟩

/-- **The kernel of the specialization at `ħ = c`** is `(ħ - c)` times the Rees operad. -/
theorem reesSpecialize_eq_zero_iff (c : R) {q : R[X]} (hq : q = X - C c) {A : Type} [Fintype A]
    [DecidableEq A] (f : (W.filtration R).Rees A) :
    (W.reesSpecialize c).app A f = 0 ↔ f ∈ ((W.filtration R).reesIdeal q).sub A := by
  subst hq
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (TwLin.specializeL_eq_zero_iff W c ((W.reesIso R).inv.app A f)).1 h
    refine (W.filtration R).mem_reesIdeal.2 ⟨(W.reesIso R).hom.app A y, ?_⟩
    rw [← map_smul, ← hy, SymOperadIso.hom_inv_apply]
  · intro h
    obtain ⟨g, rfl⟩ := (W.filtration R).mem_reesIdeal.1 h
    refine (TwLin.specializeL_eq_zero_iff W c _).2 ⟨(W.reesIso R).inv.app A g, ?_⟩
    exact map_smul ((W.reesIso R).inv.app A) _ g

/-- **The fibers of the Rees operad of the weight filtration are the twisted linearizations**:
`Rees / (ħ - c) ≅ TwLin R W c`, an isomorphism of operads over `R`. -/
noncomputable def reesModIso (c : R) (q : R[X]) (hq : q = X - C c) :
    SymOperadIso R ((W.filtration R).ReesMod q) (TwLin R W c) :=
  SymOperadIso.ofBijective
    (((W.filtration R).reesIdeal q).liftHom (W.reesSpecialize c)
      fun _ _ _ f hf => (W.reesSpecialize_eq_zero_iff c hq f).2 hf)
    fun A _ _ => ⟨(injective_iff_map_eq_zero _).2 fun z hz => by
        obtain ⟨f, rfl⟩ := ((W.filtration R).reesIdeal q).proj_surjective A z
        exact (((W.filtration R).reesIdeal q).proj_eq_zero_iff f).2
          ((W.reesSpecialize_eq_zero_iff c hq f).1 hz),
      fun y => by
        obtain ⟨f, hf⟩ := W.reesSpecialize_surjective c A y
        exact ⟨((W.filtration R).reesIdeal q).proj A f, hf⟩⟩

/-- **The associated graded operad of the weight filtration is the associated graded of the
weighted set operad**: `Gr ≅ Operad.Gr R W`, the twisted linearization at `0`. -/
noncomputable def grIso : SymOperadIso R (W.filtration R).Gr (Gr R W) :=
  W.reesModIso 0 X (by rw [Polynomial.C_0, sub_zero])

end SetOperadWeight

end Operad
