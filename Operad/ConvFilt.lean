/-
# Filtrations and convolution products; square-zero extensions

* **The convolution product of families with values in submodules** `F` and `G` takes values in
  any family `H` stable under the relabellings with `F ∘ᵢ G ⊆ H`, `G` being stable under the
  parity projections (`ConvOp.toLin_star_mem`).
* **Square-zero extensions are functorial** (`DualExt.mapHom`), and the derivation `x + ε x' ↦
  ε x'` counts the parameter (`DualExt.epsDer`). So a morphism `Ψ` from a free graded operad into
  a square-zero extension sending the generators to multiples of the parameter intertwines the
  vertex count with it: **the parameter part of `Ψ` vanishes on the trees with `j ≠ 1` vertices**
  (`FreeGrL.snd_eq_zero_of_vx`), over a `ℚ`-algebra.
-/
import Operad.CofreeVanish

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Convolution products of filtered families -/

namespace ConvOp

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]

/-- **The convolution product of families with values in `F` and `G` has values in `H`**, when
`F ∘ᵢ G ⊆ H`, `G` is stable under the parity projections and `H` under the relabellings. -/
theorem toLin_star_mem {F G H : ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (P A)}
    (hG : ∀ (A : Type) [Fintype A] [DecidableEq A] (b : Bool) (y : P A), y ∈ G A →
      GrOperad.par (R := R) b y ∈ G A)
    (hH : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (y : P A), y ∈ H A → GrOperad.map (R := R) e y ∈ H B)
    (hFG : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (y : P A) (z : P B), y ∈ F A → z ∈ G B → GrOperad.comp (R := R) i y z ∈ H _)
    {f g : GrOperad.Inv R (ConvOp R C P)}
    (hf : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), toLin (f.1 A) x ∈ F A)
    (hg : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), toLin (g.1 A) x ∈ G A)
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) :
    toLin ((GrOperad.Inv.star R _ f g).1 A) x ∈ H A := by
  rw [GrOperad.Inv.star_apply, toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun S _ => ?_
  show toLin (mapC (splitEquiv S) (compC none (f.1 (SOut S)) (g.1 (SIn S)))) x ∈ H A
  rw [mapC_apply, toLin_compC, LinearMap.comp_apply, LinearMap.comp_apply]
  refine hH _ _ _ _ ?_
  generalize GrCooperad.decomp (R := R) (C := C) (B := SIn S) (none : SOut S) _ = t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul a b =>
    simp only [kap, LinearMap.coe_sum, Finset.sum_apply, TensorProduct.map_tmul, map_sum,
      LinearMap.comp_apply, mu_tmul]
    refine Submodule.sum_mem _ fun q _ => hFG _ _ _ _ _ (hf _ _) ?_
    rw [parC_apply]
    exact Submodule.sum_mem _ fun c _ => hG _ _ _ (hg _ _)
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb

end ConvOp

/-! ## Square-zero extensions -/

namespace DualExt

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {Q' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q' A)] [GrOperad R Q'] {e : Bool}

/-- **Square-zero extensions are functorial**: `x + ε x' ↦ φ x + ε φ x'`. -/
def mapHom (φ : GrOperadHom R Q Q') : GrOperadHom R (DualExt R Q e) (DualExt R Q' e) where
  app A _ _ := LinearMap.prodMap (φ.app A) (φ.app A)
  app_par c X := Prod.ext (φ.app_par c X.1) (φ.app_par _ X.2)
  app_map σ' X := Prod.ext (φ.app_map σ' X.1) (φ.app_map σ' X.2)
  app_one := Prod.ext φ.app_one (by
    show φ.app Unit 0 = 0
    exact map_zero _)
  app_comp i X Y := Prod.ext (φ.app_comp i X.1 Y.1) (by
    show φ.app _ (GrOperad.comp (R := R) i X.2 Y.1
        + GrOperad.comp (R := R) i (GrOperad.tw (R := R) e X.1) Y.2)
      = GrOperad.comp (R := R) i (φ.app _ X.2) (φ.app _ Y.1)
        + GrOperad.comp (R := R) i (GrOperad.tw (R := R) e (φ.app _ X.1)) (φ.app _ Y.2)
    rw [map_add, φ.app_comp, φ.app_comp, GrOperadHom.app_tw])

lemma snd_mapHom (φ : GrOperadHom R Q Q') {A : Type} [Fintype A] [DecidableEq A]
    (X : DualExt R Q e A) :
    snd (R := R) (e := e) ((mapHom φ).app A X) = φ.app A (snd (R := R) (e := e) X) := rfl

variable (R Q e) in
/-- **The derivation counting the parameter**: `x + ε x' ↦ ε x'`. -/
def epsDer : GrDer (GrOperadHom.id R (DualExt R Q e)) false where
  app A _ _ := LinearMap.prodMap 0 LinearMap.id
  app_par c X := Prod.ext (by
    show (0 : Q _) = GrOperad.par (R := R) (xor c false) 0
    rw [map_zero]) (by
    show GrOperad.par (R := R) (xor c e) X.2 = GrOperad.par (R := R) (xor (xor c false) e) X.2
    rw [Bool.xor_false])
  app_map σ' X := Prod.ext (by
    show (0 : Q _) = GrOperad.map (R := R) σ' 0
    rw [map_zero]) rfl
  app_one := rfl
  app_comp i X Y := by
    rw [GrOperadHom.id_app, GrOperadHom.id_app, GrOperad.tw_false]
    refine DualExt.ext ?_ ?_
    · show (0 : Q _) = fst (compE i (LinearMap.prodMap 0 LinearMap.id X) Y
        + compE i X (LinearMap.prodMap 0 LinearMap.id Y))
      rw [map_add, fst_compE, fst_compE]
      show (0 : Q _) = GrOperad.comp (R := R) i 0 _ + GrOperad.comp (R := R) i _ 0
      rw [LinearMap.map_zero₂, map_zero, add_zero]
    · show snd (compE i X Y) = snd (compE i (LinearMap.prodMap 0 LinearMap.id X) Y
        + compE i X (LinearMap.prodMap 0 LinearMap.id Y))
      rw [map_add, snd_compE, snd_compE, snd_compE]
      show _ = GrOperad.comp (R := R) i X.2 Y.1
          + GrOperad.comp (R := R) i (GrOperad.tw (R := R) e 0) Y.2
        + (GrOperad.comp (R := R) i X.2 0
          + GrOperad.comp (R := R) i (GrOperad.tw (R := R) e X.1) Y.2)
      rw [map_zero, LinearMap.map_zero₂, map_zero, add_zero, zero_add]
      rfl

@[simp] lemma fst_epsDer {A : Type} [Fintype A] [DecidableEq A] (X : DualExt R Q e A) :
    fst ((epsDer R Q e).app A X) = 0 := rfl

@[simp] lemma snd_epsDer {A : Type} [Fintype A] [DecidableEq A] (X : DualExt R Q e A) :
    snd ((epsDer R Q e).app A X) = snd X := rfl

end DualExt

/-! ## Morphisms into square-zero extensions -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {e : Bool}
  (Ψ : GrOperadHom R (FreeGrL R V) (DualExt R Q e))
  (hΨ : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A),
    DualExt.fst (Ψ.app A ((ι R V).app A v)) = 0)
include hΨ

/-- **A morphism sending the generators to multiples of the parameter intertwines the vertex
count with the parameter count.** -/
lemma epsDer_app {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (DualExt.epsDer R Q e).app A (Ψ.app A x) = Ψ.app A ((derSp (GrSpEnd.id R V)).app A x) := by
  have h : (DualExt.epsDer R Q e).compHom Ψ = GrDer.homComp Ψ (derSp (GrSpEnd.id R V)) :=
    der_ext fun A _ _ v => by
      rw [GrDer.compHom_app, GrDer.homComp_app, derSp_ι, GrSpEnd.id_app]
      exact DualExt.ext (((DualExt.fst_epsDer _).trans (hΨ A v).symm)) rfl
  exact congrArg (fun D : GrDer Ψ false => D.app A x) h

/-- **The parameter part vanishes on the trees with `j ≠ 1` vertices**, over a `ℚ`-algebra. -/
lemma snd_eq_zero_of_vx [Algebra ℚ R] {A : Type} [Fintype A] [DecidableEq A] {j : ℕ}
    (hj : j ≠ 1) {x : FreeGrL R V A} (hx : x ∈ vx R V j A) : DualExt.snd (Ψ.app A x) = 0 := by
  have h := congrArg DualExt.snd (epsDer_app Ψ hΨ x)
  rw [DualExt.snd_epsDer, mem_eig.1 hx, map_smul] at h
  have h' : ((j : R) - 1) • DualExt.snd (Ψ.app A x) = 0 := by
    rw [sub_smul, one_smul, ← map_smul, ← h, sub_self]
  rcases Nat.lt_or_gt_of_ne hj with hl | hl
  · have : j = 0 := by omega
    subst this
    simpa using h'
  · rw [show ((j : R) - 1) = ((j - 1 : ℕ) : R) by rw [Nat.cast_sub (by omega), Nat.cast_one]]
      at h'
    exact (isUnit_natCast_of_ne_zero (show j - 1 ≠ 0 by omega)).smul_left_cancel.1
      (h'.trans (smul_zero _).symm)

end FreeGrL

end Operad
