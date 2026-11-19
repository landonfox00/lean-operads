/-
# The cobar construction of the cut cooperad, as one constant

The cobar construction `Ω T^c(V)` of the cut cooperad on a graded linear species is a free graded
operad on a species built from `T^c(V)`, and the terms of its instances are large. This file
names it once (`CutCobar.Om`), with one constant for each of its instances, and restates what
the lift into the cut cooperad uses in these terms:

* the generators `j : T^c(V) → Ω T^c(V)` (`CutCobar.jL`), odd and equivariant;
* the merge `h` of two adjacent vertices (`CutCobar.hL`), with
  `h (j c ∘ᵢ j c') = ± j (c ∘ᵢ c')` on trees without unit component (`CutCobar.hL_comp_jL`);
* the cobar differential `d` (`CutCobar.dL`), which kills the generators of the trees with one
  vertex (`CutCobar.dL_jL_of_vx_one`) and is `-(ι ⋆ ι)` on the generators (`CutCobar.dL_jL`);
* the weights (`CutCobar.wt`), independent over a `ℚ`-algebra, and the operations without unit
  component (`CutCobar.nu`);
* the contraction identity `d h + h d = n - 1` in weight `n`, on the operations without unit
  component (`CutCobar.contraction`);
* the trees with two vertices `± j a ∘_S j b` at a set of inputs `S` (`CutCobar.tw2`), which are
  the terms of the convolution square of the universal twisting morphism (`CutCobar.jj_apply`).

These restate `Operad/Cobar.lean`, `Operad/CobarContraction.lean`, `Operad/BarCobarRes.lean` and
`Operad/CofreeVanish.lean`. Two statements are new. **Without generators without inputs, the cut
cooperad has no operations without inputs** (`CutCobar.eq_zero_of_isEmpty`). **A vanishing sum of
trees with two vertices over the nonempty sets of inputs has vanishing terms, up to the unit
components of the two decorations** (`CutCobar.tw2_inj`): the generators of the cobar
construction are the trees modulo the units, and the coefficients of the cuts of a free graded
operad read its trees with two vertices (`Operad/FreeGrTwoVertex.lean`).
-/
import Operad.CofreeVanish
import Operad.BarWeights
import Operad.FreeGrTwoVertex

universe u v w

namespace Operad

open Sym GerBV FreeGrL FreeGr TreeOfArity
open scoped TensorProduct

namespace CutCobar

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒞" => FreeGrL R V

variable (R V) in
/-- **The cobar construction of the cut cooperad**, as one constant. -/
def Om (A : Type) [Fintype A] [DecidableEq A] : Type (max u v) := CobarGr R (FreeGrL R V) A

noncomputable instance instAddCommGroup (A : Type) [Fintype A] [DecidableEq A] :
    AddCommGroup (Om R V A) :=
  inferInstanceAs (AddCommGroup (CobarGr R (FreeGrL R V) A))

noncomputable instance instModule (A : Type) [Fintype A] [DecidableEq A] :
    Module R (Om R V A) :=
  inferInstanceAs (Module R (CobarGr R (FreeGrL R V) A))

noncomputable instance instGrOperad : GrOperad R (Om R V) :=
  inferInstanceAs (GrOperad R (CobarGr R (FreeGrL R V)))

/-! ## The generators -/

variable (R V) in
/-- **The generators** `T^c(V) → Ω T^c(V)`. -/
noncomputable def jL (A : Type) [Fintype A] [DecidableEq A] : 𝒞 A →ₗ[R] Om R V A :=
  Cobar.ιL R 𝒞 A

/-- The generators are odd. -/
lemma jL_par (c : Bool) (y : 𝒞 A) :
    jL R V A (GrOperad.par (R := R) c y) = GrOperad.par (R := R) (!c) (jL R V A y) :=
  (congrArg (Cobar.ιL R 𝒞 A) (FreeGrL.grPar_eq c y).symm).trans (Cobar.ιL_par R 𝒞 c y)

/-- The generators are equivariant. -/
lemma jL_map (e : A ≃ B) (y : 𝒞 A) :
    jL R V B (GrOperad.map (R := R) e y) = GrOperad.map (R := R) e (jL R V A y) :=
  Cobar.ιL_map' e y

variable (R V) in
/-- **The universal twisting morphism** `ι : T^c(V) → Ω T^c(V)`. -/
noncomputable def j : GrOperad.Inv R (ConvOp R 𝒞 (Om R V)) := Cobar.ι R 𝒞

lemma j_apply (y : 𝒞 A) : ConvOp.toLin ((j R V).1 A) y = jL R V A y := rfl

lemma isPar_j : GrOperad.Inv.IsPar true (j R V) := Cobar.isPar_ι R 𝒞

/-! ## The merge -/

variable (R V) in
/-- **The merge of two adjacent vertices.** -/
noncomputable def hL (A : Type) [Fintype A] [DecidableEq A] : Om R V A →ₗ[R] Om R V A :=
  Cobar.hM R V A

lemma hL_map (e : A ≃ B) (Y : Om R V A) :
    hL R V B (GrOperad.map (R := R) e Y) = GrOperad.map (R := R) e (hL R V A Y) :=
  ((cobarMerge R V).map_d e Y).symm

lemma hL_comp_jL_fin {k l : ℕ} {c : 𝒞 (Fin k)} {pa : Bool}
    (hc : GrOperad.par (R := R) pa c = c) (i : Fin k) (c' : 𝒞 (Fin l)) :
    hL R V _ (GrOperad.comp (R := R) i (jL R V (Fin k) c) (jL R V (Fin l) c'))
      = σ R (!pa) • jL R V _ (GrOperad.comp (R := R) i (FreeGrL.secC R V (Fin k) c)
          (FreeGrL.secC R V (Fin l) c')) :=
  Cobar.hM_comp_ιL hc i c'

/-- **Merging the two generators of a composite**, at any finite types. -/
lemma hL_comp_jL {c : 𝒞 A} {pa : Bool} (hc : GrOperad.par (R := R) pa c = c) (i : A)
    (c' : 𝒞 B) :
    hL R V _ (GrOperad.comp (R := R) i (jL R V A c) (jL R V B c'))
      = σ R (!pa) • jL R V _ (GrOperad.comp (R := R) i (FreeGrL.secC R V A c)
          (FreeGrL.secC R V B c')) := by
  obtain ⟨eA⟩ : Nonempty (A ≃ Fin (Fintype.card A)) := ⟨Fintype.equivFin A⟩
  obtain ⟨eB⟩ : Nonempty (B ≃ Fin (Fintype.card B)) := ⟨Fintype.equivFin B⟩
  have k1 : ∀ (X : Om R V A) (Y : Om R V B), GrOperad.comp (R := R) i X Y
      = GrOperad.map (R := R) (compEquiv eA eB i).symm (GrOperad.comp (R := R) (eA i)
          (GrOperad.map (R := R) eA X) (GrOperad.map (R := R) eB Y)) := fun X Y => by
    rw [← GrOperad.map_comp, ← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]
  have k2 : ∀ (X : 𝒞 A) (Y : 𝒞 B), GrOperad.comp (R := R) i X Y
      = GrOperad.map (R := R) (compEquiv eA eB i).symm (GrOperad.comp (R := R) (eA i)
          (GrOperad.map (R := R) eA X) (GrOperad.map (R := R) eB Y)) := fun X Y => by
    rw [← GrOperad.map_comp, ← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]
  have hc' : GrOperad.par (R := R) pa (GrOperad.map (R := R) eA c)
      = GrOperad.map (R := R) eA c := by
    rw [← GrOperad.map_par, hc]
  rw [k1, hL_map, ← jL_map, ← jL_map, hL_comp_jL_fin hc', map_smul, k2, secC_map, secC_map,
    jL_map]

/-! ## The differential -/

variable (R V) in
/-- **The cobar differential.** -/
noncomputable def dL : GrDer (GrOperadHom.id R (Om R V)) true := Cobar.d R 𝒞

/-- **The cobar differential on the generators** is minus the convolution square of the universal
twisting morphism. -/
lemma dL_jL (y : 𝒞 A) :
    (dL R V).app A (jL R V A y)
      = -ConvOp.toLin ((GrOperad.Inv.star R _ (j R V) (j R V)).1 A) y :=
  Cobar.d_ιL R 𝒞 y

/-! ## The weights -/

variable (R V) in
/-- **The operations of weight `n`**: the number of vertices of the trees decorating the
generators. -/
noncomputable def wt (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] : Submodule R (Om R V A) :=
  Cobar.wt R V n A

lemma jL_mem_wt {n : ℕ} {y : 𝒞 A} (hy : y ∈ vx R V n A) : jL R V A y ∈ wt R V n A :=
  Cobar.ιL_mem_wt hy

lemma comp_mem_wt (r : A) {m n : ℕ} {P : Om R V A} {Q : Om R V B} (hP : P ∈ wt R V m A)
    (hQ : Q ∈ wt R V n B) : GrOperad.comp (R := R) r P Q ∈ wt R V (m + n) _ :=
  Cobar.comp_mem_wt r hP hQ

lemma par_mem_wt (b : Bool) {n : ℕ} {Y : Om R V A} (hY : Y ∈ wt R V n A) :
    GrOperad.par (R := R) b Y ∈ wt R V n A :=
  Cobar.par_mem_wt b hY

lemma map_mem_wt (e : A ≃ B) {n : ℕ} {Y : Om R V A} (hY : Y ∈ wt R V n A) :
    GrOperad.map (R := R) e Y ∈ wt R V n B :=
  Cobar.map_mem_wt e hY

/-- **The weights are independent**, over a `ℚ`-algebra. -/
lemma iSupIndep_wt [Algebra ℚ R] (A : Type) [Fintype A] [DecidableEq A] :
    iSupIndep fun n : ℕ => wt R V n A :=
  iSupIndep_eigenspace_nat ((Cobar.wtΩ R V).app A)

/-- **The cobar differential kills the generators of the trees with one vertex**, when there are
no generators without inputs: `ι ⋆ ι` preserves the weights and has values of weight at least
two. -/
lemma dL_jL_of_vx_one [Algebra ℚ R] (hV0 : ∀ v : V (Fin 0), v = 0) {y : 𝒞 A}
    (hy : y ∈ vx R V 1 A) : (dL R V).app A (jL R V A y) = 0 := by
  have h1 : ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) y ∈ Cobar.wt R V 1 A := Cobar.ιι_mem_wt hV0 hy
  have h2 : ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) y ∈ Cobar.wtGe (V := V) 2 A :=
    ConvOp.toLin_star_mem (C := 𝒞) (F := fun A _ _ => Cobar.wtGe (V := V) 1 A)
      (G := fun A _ _ => Cobar.wtGe (V := V) 1 A) (H := fun A _ _ => Cobar.wtGe (V := V) 2 A)
      (Cobar.wtGe_par_all 1) (Cobar.wtGe_map_all 2) (Cobar.wtGe_comp_all 1 1 2 le_rfl)
      (f := Cobar.ι R 𝒞) (g := Cobar.ι R 𝒞)
      (fun A _ _ y => Cobar.ιL_mem_wtGe_one y) (fun A _ _ y => Cobar.ιL_mem_wtGe_one y) A y
  have h0 : ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) y = 0 := by
    refine Submodule.disjoint_def.1 ((iSupIndep_eigenspace_nat ((Cobar.wtΩ R V).app A)) 1)
      _ h1 ?_
    refine (iSup_le fun i => ?_ : Cobar.wtGe (V := V) 2 A ≤ ⨆ (i : ℕ) (_ : i ≠ 1),
      Cobar.wt R V i A) h2
    exact le_iSup₂_of_le (f := fun (i : ℕ) (_ : i ≠ 1) => Cobar.wt R V i A) i.1
      (by have := i.2; omega) le_rfl
  exact (Cobar.d_ιL R 𝒞 y).trans ((congrArg Neg.neg h0).trans neg_zero)

/-! ## The operations without unit component -/

variable (R V) in
/-- **The operations without unit component.** -/
noncomputable def nu (A : Type) [Fintype A] [DecidableEq A] : Submodule R (Om R V A) :=
  LinearMap.ker (FreeGrL.unitCoeffL R (CobarGen R 𝒞) A)

lemma jL_mem_nu (y : 𝒞 A) : jL R V A y ∈ nu R V A :=
  LinearMap.mem_ker.2 (Cobar.unitCoeffL_ιL y)

lemma comp_mem_nu (i : A) {Y : Om R V A} (hY : Y ∈ nu R V A) (Z : Om R V B) :
    GrOperad.comp (R := R) i Y Z ∈ nu R V _ :=
  LinearMap.mem_ker.2 ((FreeGrL.unitCoeffL_comp i (Y : CobarGr R 𝒞 A) Z).trans
    (by
      have h0 : FreeGrL.unitCoeffL R (CobarGen R 𝒞) A (Y : CobarGr R 𝒞 A) = 0 :=
        LinearMap.mem_ker.1 hY
      rw [h0, zero_mul]))

lemma par_mem_nu (b : Bool) {Y : Om R V A} (hY : Y ∈ nu R V A) :
    GrOperad.par (R := R) b Y ∈ nu R V A :=
  LinearMap.mem_ker.2 ((FreeGrL.unitCoeffL_par b (Y : CobarGr R 𝒞 A)).trans
    (by
      have h0 : FreeGrL.unitCoeffL R (CobarGen R 𝒞) A (Y : CobarGr R 𝒞 A) = 0 :=
        LinearMap.mem_ker.1 hY
      rw [h0, ite_self]))

lemma map_mem_nu (e : A ≃ B) {Y : Om R V A} (hY : Y ∈ nu R V A) :
    GrOperad.map (R := R) e Y ∈ nu R V B :=
  LinearMap.mem_ker.2 ((FreeGrL.unitCoeffL_map e (Y : CobarGr R 𝒞 A)).trans
    (LinearMap.mem_ker.1 hY))

/-! ## The contraction -/

/-- **The contraction identity in weight `n`**, on the operations without unit component:
`d h + h d = n - 1`, when there are no generators without inputs. -/
theorem contraction (hV0 : ∀ v : V (Fin 0), v = 0) {n : ℕ} {Y : Om R V A}
    (hY : Y ∈ wt R V n A) (hu : Y ∈ nu R V A) :
    (dL R V).app A (hL R V A Y) + hL R V A ((dL R V).app A Y) = (n : R) • Y - Y := by
  have h := Cobar.dh_hd hV0 (Y : CobarGr R 𝒞 A)
  rw [Cobar.mem_wt.1 hY, FreeGrL.secC_of_unitCoeff (LinearMap.mem_ker.1 hu)] at h
  exact h

/-! ## Operations without inputs -/

/-- **Without generators without inputs, the cut cooperad has no operations without inputs.** -/
lemma eq_zero_of_isEmpty (hV0 : ∀ v : V (Fin 0), v = 0) [IsEmpty A] (x : 𝒞 A) : x = 0 := by
  obtain ⟨y, rfl⟩ := (GrOperadIdeal.span R (grLinRel R V)).proj_surjective A x
  have key : ∀ (A : Type) [Fintype A] [DecidableEq A] (t : Reg (TreeOfArity (GrGen R V)) A),
      IsEmpty A → (GrOperadIdeal.span R (grLinRel R V)).proj A
        (SgnLin.bas (treeSgn (grGenPar R V)) R t) = 0 := by
    intro A _ _ t
    refine FreeReg.induction (P := fun A _ _ t => IsEmpty A →
      (GrOperadIdeal.span R (grLinRel R V)).proj A
        (SgnLin.bas (treeSgn (grGenPar R V)) R t) = 0) ?_ ?_ ?_ ?_ t
    · intro A B _ _ _ _ e x ih hB
      rw [← SgnLin.map_bas]
      show GrOperad.map (R := R) e ((GrOperadIdeal.span R (grLinRel R V)).proj A _) = 0
      rw [ih ⟨fun a => hB.elim (e a)⟩, map_zero]
    · intro h
      exact (h.false ()).elim
    · intro A B _ _ _ _ i x y _ ihy h
      rw [FreeGr.bas_comp_eq, map_smul]
      show _ • GrOperad.comp (R := R) i ((GrOperadIdeal.span R (grLinRel R V)).proj A _)
        ((GrOperadIdeal.span R (grLinRel R V)).proj B _) = 0
      rw [ihy ⟨fun b => h.elim (Sum.inr b)⟩, map_zero, smul_zero]
    · intro k g h
      obtain rfl : k = 0 := by
        by_contra hk
        exact h.elim ⟨0, Nat.pos_of_ne_zero hk⟩
      exact (FreeGrL.ι_app_hom g.2).symm.trans (by rw [hV0 g.1.1, map_zero])
  refine FreeGr.induction_bas (motive := fun y =>
    (GrOperadIdeal.span R (grLinRel R V)).proj A y = 0) y (map_zero _) ?_ ?_
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]
  · intro c t
    rw [map_smul, key A t inferInstance, smul_zero]

/-! ## The trees with two vertices -/

variable (R V) in
/-- The sign twist of the cut cooperad. -/
noncomputable def twC (A : Type) [Fintype A] [DecidableEq A] : 𝒞 A →ₗ[R] 𝒞 A :=
  GrSpecies.tw (R := R) (V := FreeGrL R V) true

lemma twC_apply (y : 𝒞 A) :
    twC R V A y = GrOperad.par (R := R) false y - GrOperad.par (R := R) true y := by
  rw [twC, GrSpecies.tw_apply, σ_true, neg_one_smul, ← sub_eq_add_neg, FreeGrL.grPar_eq,
    FreeGrL.grPar_eq]

lemma twC_twC (y : 𝒞 A) : twC R V A (twC R V A y) = y := by
  rw [twC, GrSpecies.tw_tw, Bool.xor_self, GrSpecies.tw_false]

lemma twC_secC (y : 𝒞 A) :
    twC R V A (FreeGrL.secC R V A y) = FreeGrL.secC R V A (twC R V A y) := by
  rw [twC_apply, twC_apply, map_sub, FreeGrL.secC_par, FreeGrL.secC_par]

variable (R V) in
/-- **The trees with two vertices of the cobar construction**, at a set of inputs `S`:
`a ⊗ b ↦ ± j a ∘_S j b`, the terms of the convolution square of the universal twisting
morphism. -/
noncomputable def tw2 (S : Finset A) : 𝒞 (SOut S) ⊗[R] 𝒞 (SIn S) →ₗ[R] Om R V A :=
  GrOperad.map (R := R) (splitEquiv S) ∘ₗ ConvOp.mu (R := R) (P := Om R V) none ∘ₗ
    ConvOp.kap ((j R V).1 (SOut S)) ((j R V).1 (SIn S))

lemma tw2_tmul (S : Finset A) (a : 𝒞 (SOut S)) (b : 𝒞 (SIn S)) :
    tw2 R V S (a ⊗ₜ[R] b) = GrOperad.map (R := R) (splitEquiv S)
      (GrOperad.comp (R := R) none (jL R V (SOut S) (twC R V (SOut S) a))
        (jL R V (SIn S) b)) := by
  have hg : ConvOp.IsParC true ((j R V).1 (SIn S)) :=
    ConvOp.parC_eq_self_iff.1 (isPar_j (SIn S))
  rw [tw2, LinearMap.comp_apply, LinearMap.comp_apply, ConvOp.kap_tmul _ hg, ConvOp.mu_tmul]
  rfl

/-- **The convolution square of the universal twisting morphism**, as a sum of trees with two
vertices over the nonempty sets of inputs. -/
lemma jj_apply (y : 𝒞 A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (j R V) (j R V)).1 A) y
      = ∑ S ∈ nonempties A, tw2 R V S (GrCooperad.decomp (R := R) (C := 𝒞) none
          (SymSpecies.map (R := R) (splitEquiv S).symm y)) := by
  rw [GrOperad.Inv.star_apply, ConvOp.toLin_sum, LinearMap.coe_sum, Finset.sum_apply]
  rfl

variable (R V) in
/-- The generators of the cobar construction, on the cut cooperad. -/
noncomputable def sL (A : Type) [Fintype A] [DecidableEq A] : 𝒞 A →ₗ[R] CobarGen R 𝒞 A :=
  (GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R 𝒞) A).toLinearMap ∘ₗ
    GrCooperad.Red.proj R 𝒞 A

variable (R V) in
/-- A retraction of the generators onto the trees without unit component. -/
noncomputable def rL (A : Type) [Fintype A] [DecidableEq A] : CobarGen R 𝒞 A →ₗ[R] 𝒞 A :=
  FreeGrL.secR R V A ∘ₗ
    (GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R 𝒞) A).symm.toLinearMap

lemma rL_sL (y : 𝒞 A) : rL R V A (sL R V A y) = FreeGrL.secC R V A y := by
  show FreeGrL.secR R V A ((GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R 𝒞) A).symm
    ((GrSpecies.Shift.of (R := R) (V := GrCooperad.Red R 𝒞) A)
      (GrCooperad.Red.proj R 𝒞 A y))) = _
  rw [LinearEquiv.symm_apply_apply, FreeGrL.secR_proj]

/-- The trees with two vertices of the cobar construction are those of the free graded operad
on its generators. -/
lemma tw2_eq (S : Finset A) (t : 𝒞 (SOut S) ⊗[R] 𝒞 (SIn S)) :
    tw2 R V S t = FreeGrL.twoVertexT R (CobarGen R 𝒞) S
      (TensorProduct.map (sL R V (SOut S) ∘ₗ twC R V (SOut S)) (sL R V (SIn S)) t) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    rfl
  | tmul a b =>
    rw [tw2_tmul, TensorProduct.map_tmul, FreeGrL.twoVertexT_tmul]
    rfl
  | add t t' ht ht' =>
    simp only [map_add, ht, ht']
    rfl

/-- **A vanishing sum of trees with two vertices over the nonempty sets of inputs has vanishing
terms**, up to the unit components of the two decorations. -/
theorem tw2_inj (z : ∀ S : Finset A, 𝒞 (SOut S) ⊗[R] 𝒞 (SIn S))
    (h : ∑ S ∈ nonempties A, tw2 R V S (z S) = 0) {S : Finset A} (hS : S ∈ nonempties A) :
    TensorProduct.map (FreeGrL.secC R V (SOut S)) (FreeGrL.secC R V (SIn S)) (z S) = 0 := by
  have h' := FreeGrL.cutCoef_sum_twoVertex (R := R) (W := CobarGen R 𝒞)
    (fun S' => TensorProduct.map (sL R V (SOut S') ∘ₗ twC R V (SOut S')) (sL R V (SIn S'))
      (z S')) hS
  have h0 : (∑ S' ∈ nonempties A, FreeGrL.twoVertexT R (CobarGen R 𝒞) S'
      (TensorProduct.map (sL R V (SOut S') ∘ₗ twC R V (SOut S')) (sL R V (SIn S')) (z S')) :
        CobarGr R 𝒞 A) = 0 :=
    (Finset.sum_congr rfl fun S' _ => (tw2_eq S' (z S')).symm).trans h
  rw [h0, map_zero] at h'
  have e1 : (twC R V (SOut S) ∘ₗ rL R V (SOut S)) ∘ₗ (sL R V (SOut S) ∘ₗ twC R V (SOut S))
      = FreeGrL.secC R V (SOut S) := LinearMap.ext fun y => by
    show twC R V _ (rL R V _ (sL R V _ (twC R V _ y))) = _
    rw [rL_sL, twC_secC, twC_twC]
  have e2 : rL R V (SIn S) ∘ₗ sL R V (SIn S) = FreeGrL.secC R V (SIn S) :=
    LinearMap.ext rL_sL
  have hρ := congrArg (TensorProduct.map (twC R V (SOut S) ∘ₗ rL R V (SOut S))
    (rL R V (SIn S))) h'.symm
  rw [map_zero, ← LinearMap.comp_apply, ← TensorProduct.map_comp, e1, e2] at hρ
  exact hρ

end CutCobar

end Operad
