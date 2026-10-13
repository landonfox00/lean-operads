/-
# The Koszul criterion

For quadratic data `(E, r)` without generators with at most one input, presenting
`P = T(E)/(r)` over a field of characteristic zero, and an ideal `I` of `P` containing the
generators, complementing the units, without operations with at most one input:

* the Koszul dual cooperad `P^¡` and the bar construction `B(P, I)` are **reduced**
  (`Koszul.dual_mem_unitSpan`, `Koszul.bar_mem_unitSpan`): the trees on generators with at least
  two inputs in arity at most one are the units (`FreeGrL.mem_unitSpan_of_card_le`);
* **the morphism `ΩP^¡ → P` factors as `ΩP^¡ → ΩB(P, I) → P`**, the counit after `Ωi`
  (`Koszul.counit_comp`), both being determined by `π ∘ i = κ` on the generators
  (`Bar.counit_comp_map`).

The counit is a quasi-isomorphism (Theorem A, `Bar.counit_bijective`), so `ΩP^¡ → P` is one iff
`Ωi` is (`Homology.bijective_comp_iff`), and `Ωi` is one iff `i` is one in the arities at least
two, `P^¡` having the zero differential and `d_B ∘ i = 0` (`CobarZero.map_bijective_iff`). So:

* **the Koszul criterion**: `P` is Koszul iff `P^¡ → B(P, I)` is a quasi-isomorphism in the
  arities at least two (`Koszul.isKoszul_iff`).
-/
import Operad.KoszulBar
import Operad.CobarQIso

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Homology -/

/-- Equal chain maps between equal differentials induce simultaneously bijective maps. -/
lemma Homology.map_bijective_congr {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {dV dV' : M →ₗ[R] M} {dW : N →ₗ[R] N}
    {F F' : M →ₗ[R] N} (hd : dV = dV') (hFF : F = F') (hF : ∀ v, F (dV v) = dW (F v))
    (hF' : ∀ v, F' (dV' v) = dW (F' v)) :
    Function.Bijective (Homology.map (dV := dV) F hF)
      ↔ Function.Bijective (Homology.map (dV := dV') F' hF') := by
  subst hd hFF
  rfl

/-- **A chain map is a quasi-isomorphism iff its composite with a quasi-isomorphism is.** -/
lemma Homology.bijective_comp_iff {R : Type*} [CommRing R] {M N Q : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q] {dM : M →ₗ[R] M}
    {dN : N →ₗ[R] N} {dQ : Q →ₗ[R] Q} {F : M →ₗ[R] N} {G : N →ₗ[R] Q} {H : M →ₗ[R] Q}
    (hH : H = G ∘ₗ F) (hF : ∀ v, F (dM v) = dN (F v)) (hG : ∀ v, G (dN v) = dQ (G v))
    (hHc : ∀ v, H (dM v) = dQ (H v)) (hGb : Function.Bijective (Homology.map G hG)) :
    Function.Bijective (Homology.map H hHc) ↔ Function.Bijective (Homology.map F hF) := by
  subst hH
  rw [Homology.map_comp F hF G hG, LinearMap.coe_comp]
  exact hGb.of_comp_iff' _

/-! ## Reduced cut cooperads -/

namespace FreeGrL

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

/-- **In the arities at most one, the trees on generators with at least two inputs are the
units.** -/
theorem mem_unitSpan_of_card_le
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : V B, v = 0)
    {A : Type} [Fintype A] [DecidableEq A] (hA : Fintype.card A ≤ 1) (x : FreeGrL R V A) :
    x ∈ GrCooperad.unitSpan R (FreeGrL R V) A := by
  have hx : x ∈ ⨆ j : ℕ, vx R V j A := (iSup_vx (R := R) (V := V) A).symm ▸ Submodule.mem_top
  refine (iSup_le (fun j z hz => ?_) : (⨆ j : ℕ, vx R V j A)
    ≤ GrCooperad.unitSpan R (FreeGrL R V) A) hx
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    have h3 := Cobar.ιL_vx_zero hz
    rw [Cobar.ιL_apply, ← map_zero ((FreeGrL.ι R (CobarGen R (FreeGrL R V))).app A)] at h3
    exact (Submodule.Quotient.mk_eq_zero _).1 (FreeGrL.ι_injective h3)
  · rw [eig_card_eq_bot hred (by omega) hz]
    exact zero_mem _

end FreeGrL

/-! ## The counit after a morphism into the bar construction -/

namespace Bar

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P} {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]

/-- **A morphism out of `ΩC` desuspending the cogenerators after `f : C → B(P, I)` is the counit
after `Ωf`.** -/
theorem counit_comp_map (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (f : GrCooperadHom R C (BarCoop I))
    (hf : f.app Unit (GrCooperad.Coaug.one (R := R) (C := C))
      = GrCooperad.Coaug.one (R := R) (C := BarCoop I))
    (φ : GrOperadHom R (CobarGr R C) (ZeroDG R P))
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      φ.app A (Cobar.ιL R C A x) = piL I A (f.app A x)) :
    (counit I hI0).1.comp (CobarMap.map f hf) = φ :=
  FreeGrL.hom_ext fun A _ _ v => by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    show (counit I hI0).1.app A ((CobarMap.map f hf).app A (Cobar.ιL R C A x))
      = φ.app A (Cobar.ιL R C A x)
    rw [CobarMap.map_ιL, counit_ιL, hφ]

end Bar

namespace Koszul

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))}

/-- **The Koszul dual cooperad is reduced**, for generators with at least two inputs. -/
theorem dual_mem_unitSpan
    (hEred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : E B, v = 0)
    {A : Type} [Fintype A] [DecidableEq A] (hA : Fintype.card A ≤ 1) (x : Dual R E r A) :
    x ∈ GrCooperad.unitSpan R (Dual R E r) A := by
  have hx := FreeGrL.mem_unitSpan_of_card_le (R := R) (V := GrSpecies.Shift E R)
    (fun B _ _ hB v => hEred B hB v) hA ((dualSub R E r).incl A x)
  have h : Submodule.map ((dualSub R E r).incl A) (GrCooperad.unitSpan R (Dual R E r) A)
      = GrCooperad.unitSpan R (Cut R E) A := by
    rw [GrCooperad.unitSpan, GrCooperad.unitSpanOf, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← h] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rwa [(dualSub R E r).incl_injective A hxy] at hy

variable (I : GrOperadIdeal R (Pres R E r))
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)
  (hI1 : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ y ∈ I.sub B, y = 0)

include hI1 in
/-- **The bar construction is reduced**, for an ideal without operations with at most one
input. -/
theorem bar_mem_unitSpan {A : Type} [Fintype A] [DecidableEq A] (hA : Fintype.card A ≤ 1)
    (x : BarCoop I A) : x ∈ GrCooperad.unitSpan R (BarCoop I) A :=
  FreeGrL.mem_unitSpan_of_card_le (R := R) (V := BarGen I)
    (fun B _ _ hB v => IdealSp.ext I (hI1 B hB _ (IdealSp.mem I v))) hA x

section Criterion

omit [CharZero R] in
/-- The comparison morphism preserves the coaugmentations. -/
lemma toBar_one : (toBar I hE).app Unit (GrCooperad.Coaug.one (R := R) (C := Dual R E r))
    = GrCooperad.Coaug.one (R := R) (C := BarCoop I) :=
  (FreeGrL.mapSp (barGen I hE)).app_one

omit [CharZero R] in
/-- **The morphism `ΩP^¡ → P` is the counit `ΩB(P, I) → P` after `Ωi`.** -/
theorem counit_comp (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) :
    (Bar.counit I hI0).1.comp (CobarMap.map (toBar I hE) (toBar_one I hE)) = (cobarMor R E r).1 :=
  Bar.counit_comp_map hI0 (toBar I hE) (toBar_one I hE) _ fun _ _ _ x =>
    (Cobar.homOf_ιL _ _ _ x).trans ((kappa_apply r x).trans (piL_mapSp I hE _).symm)

include hI1 in
/-- **The Koszul criterion.** Over a field of characteristic zero, for quadratic data without
generators with at most one input and an ideal `I` of `P` containing the generators,
complementing the units, without operations with at most one input, with a free unit: **`P` is
Koszul iff the comparison morphism `P^¡ → B(P, I)` is a quasi-isomorphism in the arities at least
two**, `P^¡` having the zero differential. -/
theorem isKoszul_iff
    (hEred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ v : E B, v = 0)
    (hcompl : ∀ (A : Type) [Fintype A] [DecidableEq A],
      IsCompl (Bar.unitsP (Pres R E r) A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := Pres R E r) = 0 → a = 0) :
    IsKoszul R E r ↔ ∀ (B : Type) [Fintype B] [DecidableEq B], 2 ≤ Fintype.card B →
      Function.Bijective (Homology.map (dV := (0 : Dual R E r B →ₗ[R] Dual R E r B))
        (dW := DGCooperad.d (R := R) (C := BarCoop I) (A := B)) ((toBar I hE).app B)
          fun x => by rw [LinearMap.zero_apply, map_zero, d_toBar I hE hI1]) := by
  have hI0 : ∀ y ∈ I.sub (Fin 0), y = 0 := hI1 (Fin 0) (by simp)
  refine Iff.trans ?_ (CobarZero.map_bijective_iff (toBar I hE) (toBar_one I hE)
    (fun A _ _ x => d_toBar I hE hI1 x) (fun B _ _ hB x => dual_mem_unitSpan hEred hB x)
    (fun B _ _ hB x => bar_mem_unitSpan I hI1 hB x)).symm
  refine forall_congr' fun A => forall_congr' fun _ => forall_congr' fun _ => ?_
  exact Homology.bijective_comp_iff
    (congrArg (fun φ : GrOperadHom R (CobarGr R (Dual R E r)) (ZeroDG R (Pres R E r)) =>
      φ.app A) (counit_comp I hE hI0)).symm _ ((Bar.counit I hI0).2 A) _
    (Bar.counit_bijective (I := I) (A := A) hI0 (hcompl A) hone)

end Criterion

end Koszul

end Operad
