/-
# The cooperad of signed linear orders in the Koszul dual cooperad of `Ass`

`OrdCo K` is the cooperad of signed linear orders, the twisted linearization of the nonempty
linear orders with the sign data of the planar binary trees (`Operad/OrdCooperad.lean`).

* **The comparison** (`OrdCo.toCut`). The orders on two inputs are the shifted generators of
  `Ass` (`OrdCo.gen`), and by the universal property of the cut cooperad this projection lifts to
  a morphism of graded cooperads `OrdCo K → T^c(sE)`, over a field of characteristic zero.
* **The desuspension map is the coefficient of the generators, desuspended**
  (`Koszul.kapL_eq_genCoef`).
* **The image satisfies the corelations of `Ass`** (`OrdCo.star_kapO_mem_ideal`). The convolution
  square of the desuspension map, pulled back to `OrdCo K`, is computed on a standard order by
  `NOrd.star_std`: its planar terms vanish except for the two terms of two inner inputs in two
  outer inputs on three inputs, which are `(xy)z` and `-x(yz)` in the model of `Ass` in the free
  associative algebra (`OrdCo.sgEv_plT`). The relators of `Ass` are the operations of arity three
  vanishing in that model, so the square lands in their ideal.
* **Morphisms into a subcooperad** (`GrCooperadHom.rangeSub`, `GrSubCooperad.liftHom`), and
  **the morphism `OrdCo K → Ass^¡`** (`OrdCo.toDual`), by the universal property of the Koszul
  dual cooperad (`Koszul.le_dualSub`).
-/
import Operad.OrdStar
import Operad.SymPresAss
import Operad.CutCofree
import Operad.CutLift
import Operad.KoszulQuadratic

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-- **The cooperad of signed linear orders**: the twisted linearization of the nonempty linear
orders, with the sign data of the planar binary trees. -/
abbrev OrdCo (K : Type u) [CommRing K] : (A : Type) → [Fintype A] → [DecidableEq A] → Type u :=
  SgnLin K NOrd.sgnD

namespace OrdCo

variable (K : Type u) [Field K] {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B]

/-- The order of a numbering of two inputs. -/
def ord2 (τ : Fin 2 ≃ A) : NOrd A := SetOperad.map τ (NOrd.std 2 (by decide))

/-- The coefficients of the orders on two inputs, as an element of the shifted regular
representation. -/
noncomputable def genApp (A : Type) [Fintype A] [DecidableEq A] :
    OrdCo K A →ₗ[K] GrSpecies.Shift (SymPresB.Reg2 K) K A :=
  (LinearMap.pi fun τ : Fin 2 ≃ A => Finsupp.lapply (ord2 τ) :
    (NOrd A →₀ K) →ₗ[K] ((Fin 2 ≃ A) → K))

lemma genApp_apply (x : OrdCo K A) (τ : Fin 2 ≃ A) :
    (genApp K A x : (Fin 2 ≃ A) → K) τ = (show NOrd A →₀ K from x) (ord2 τ) := rfl

/-- A vector of the shifted regular representation on other than two inputs is zero. -/
lemma shift_eq_zero (h : Fintype.card B ≠ 2) (v : GrSpecies.Shift (SymPresB.Reg2 K) K B) :
    v = 0 :=
  show (v : (Fin 2 ≃ B) → K) = 0 from
    funext fun τ => absurd ((Fintype.card_congr τ).symm.trans (Fintype.card_fin 2)) h

/-- **The projection onto the orders on two inputs**, a morphism of graded linear species onto
the shifted generators of `Ass`. -/
noncomputable def gen : GrSpeciesHom K (OrdCo K) (GrSpecies.Shift (SymPresB.Reg2 K) K) where
  app A _ _ := genApp K A
  app_map {A B} _ _ _ _ e x :=
    show (genApp K B (SymSpecies.map (R := K) e x) : (Fin 2 ≃ B) → K)
      = (SymSpecies.map (R := K) (V := SymPresB.Reg2 K) e (genApp K A x) : (Fin 2 ≃ B) → K) from
    funext fun τ => by
      show Lin.mapL K e x (ord2 τ) = (show NOrd A →₀ K from x) (ord2 (τ.trans e.symm))
      rw [Lin.mapL_apply, ord2, ord2, ← SetOperad.map_trans]
  app_par {A} _ _ b x :=
    show (genApp K A (GrSpecies.par (R := K) b x) : (Fin 2 ≃ A) → K)
      = (GrSpecies.par (R := K) (V := SymPresB.Reg2 K) (!b) (genApp K A x) : (Fin 2 ≃ A) → K) from
    funext fun τ => by
      have hc : Fintype.card A = 2 := (Fintype.card_congr τ).symm.trans (Fintype.card_fin 2)
      have ht : (NOrd.sgnD.app A (ord2 τ)).tot = true := by
        show (Fintype.card A + 1).bodd = true
        rw [hc]
        rfl
      show SgnLin.parT K NOrd.sgnD b x (ord2 τ) = _
      rw [SgnLin.parT_apply, ht]
      cases b
      · rfl
      · rfl

/-- The shifted generators of `Ass` have no vectors on at most one input. -/
lemma hred (B : Type) [Fintype B] [DecidableEq B] (hB : Fintype.card B ≤ 1)
    (v : GrSpecies.Shift (SymPresB.Reg2 K) K B) : v = 0 :=
  shift_eq_zero K (by omega) v

variable [CharZero K]

/-- **The cooperad of signed linear orders in the cut cooperad** on the shifted generators of
`Ass`: the morphism of graded cooperads lifting the projection onto the orders on two inputs. -/
noncomputable def toCut : GrCooperadHom K (OrdCo K) (Koszul.Cut K (SymPresB.Reg2 K)) :=
  (FreeGrL.cofreeHomEquiv (R := K) (C := OrdCo K) (V := GrSpecies.Shift (SymPresB.Reg2 K) K)
    (hred K)).symm (gen K)

lemma genCoef_toCut (x : OrdCo K A) :
    FreeGrL.genCoef K (GrSpecies.Shift (SymPresB.Reg2 K) K) A ((toCut K).app A x)
      = (gen K).app A x := by
  have h := (FreeGrL.cofreeHomEquiv (R := K) (C := OrdCo K)
    (V := GrSpecies.Shift (SymPresB.Reg2 K) K) (hred K)).apply_symm_apply (gen K)
  exact congrArg (fun φ : GrSpeciesHom K (OrdCo K) (GrSpecies.Shift (SymPresB.Reg2 K) K) =>
    φ.app A x) h

end OrdCo

/-! ## The desuspension map through the coefficient of the generators -/

namespace Koszul

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {A : Type} [Fintype A] [DecidableEq A]

/-- **The desuspension map is the coefficient of the generators, desuspended.** -/
lemma kapL_eq_genCoef (z : Cut R E A) :
    kapL R E A z = (FreeGrL.ι R E).app A
      ((GrSpecies.Shift.of A).symm (FreeGrL.genCoef R (GrSpecies.Shift E R) A z)) := by
  have hz : z ∈ ⨆ j : ℕ, FreeGrL.vx R (GrSpecies.Shift E R) j A :=
    (FreeGrL.iSup_vx (R := R) (V := GrSpecies.Shift E R) A).symm ▸ Submodule.mem_top
  have hle : (⨆ j : ℕ, FreeGrL.vx R (GrSpecies.Shift E R) j A)
      ≤ LinearMap.eqLocus (kapL R E A)
        ((FreeGrL.ι R E).app A ∘ₗ (GrSpecies.Shift.of (V := E) (R := R) A).symm.toLinearMap ∘ₗ
          FreeGrL.genCoef R (GrSpecies.Shift E R) A) := by
    refine iSup_le fun j x hx => ?_
    show kapL R E A x = (FreeGrL.ι R E).app A
      ((GrSpecies.Shift.of A).symm (FreeGrL.genCoef R (GrSpecies.Shift E R) A x))
    by_cases hj : j = 1
    · subst hj
      obtain ⟨w, rfl⟩ : ∃ w : E A,
          (FreeGrL.ι R (GrSpecies.Shift E R)).app A (GrSpecies.Shift.of A w) = x :=
        ⟨(GrSpecies.Shift.of A).symm (FreeGrL.genCoef R (GrSpecies.Shift E R) A x), by
          rw [LinearEquiv.apply_symm_apply]
          exact (FreeGrL.eq_ι_genCoef hx).symm⟩
      rw [kapL_ι, FreeGrL.genCoef_ι, LinearEquiv.symm_apply_apply]
    · rw [kapL_vx hj hx, CutLift.genCoef_of_mem_vx hj hx, map_zero, map_zero]
  exact hle hz

end Koszul

/-! ## The signed linear orders satisfy the corelations of `Ass` -/

namespace OrdCo

variable (K : Type u) [Field K] [CharZero K] {A B : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

local notation "𝔼" => SymPresB.Reg2 K

/-- **The desuspension map on the signed linear orders**: the desuspension map of the cut
cooperad after `toCut`. -/
noncomputable def kapO : GrOperad.Inv K (ConvOp K (OrdCo K) (FreeGrL K 𝔼)) :=
  GrOperad.Inv.appHom (ConvOp.preHom (toCut K)) (Koszul.kapT K 𝔼)

lemma kapO_apply (y : OrdCo K A) :
    ConvOp.toLin ((kapO K).1 A) y = Koszul.kapL K 𝔼 A ((toCut K).app A y) := rfl

/-- The convolution square of the desuspension map, on the image of the signed linear orders. -/
lemma star_toCut (y : OrdCo K A) :
    ConvOp.toLin ((GrOperad.Inv.star K _ (Koszul.kapT K 𝔼) (Koszul.kapT K 𝔼)).1 A)
        ((toCut K).app A y)
      = ConvOp.toLin ((GrOperad.Inv.star K _ (kapO K) (kapO K)).1 A) y := by
  have h := congrArg (fun q : GrOperad.Inv K (ConvOp K (OrdCo K) (FreeGrL K 𝔼)) =>
      ConvOp.toLin (q.1 A) y)
    (GrOperad.Inv.appHom_star (ConvOp.preHom (P := FreeGrL K 𝔼) (toCut K)) (Koszul.kapT K 𝔼)
      (Koszul.kapT K 𝔼))
  exact h

lemma isParC_kapO (B : Type) [Fintype B] [DecidableEq B] :
    ConvOp.IsParC true ((kapO K).1 B) := by
  intro c x
  show Koszul.kapL K 𝔼 B ((toCut K).app B (GrSpecies.par (R := K) c x))
    = GrOperad.par (R := K) (xor c true) (Koszul.kapL K 𝔼 B ((toCut K).app B x))
  rw [(toCut K).app_par, Bool.xor_true]
  exact Koszul.kapL_par c _

/-- The desuspension map vanishes on the orders on other than two inputs. -/
lemma kapO_eq_zero (h : Fintype.card A ≠ 2) (y : OrdCo K A) :
    ConvOp.toLin ((kapO K).1 A) y = 0 := by
  rw [kapO_apply, Koszul.kapL_eq_genCoef, genCoef_toCut, shift_eq_zero K h ((gen K).app A y),
    map_zero, map_zero]

/-- **The generator of `Ass`** read on the standard order on two inputs: the indicator of the
identity numbering. -/
noncomputable def mu0 : 𝔼 (Fin 2) :=
  (GrSpecies.Shift.of (Fin 2)).symm
    ((gen K).app (Fin 2) (SgnLin.bas NOrd.sgnD K (NOrd.std 2 (by decide))))

lemma kapO_std2 :
    ConvOp.toLin ((kapO K).1 (Fin 2)) (SgnLin.bas NOrd.sgnD K (NOrd.std 2 (by decide)))
      = (FreeGrL.ι K 𝔼).app (Fin 2) (mu0 K) := by
  rw [kapO_apply, Koszul.kapL_eq_genCoef, genCoef_toCut]
  rfl

omit [CharZero K] in
lemma mu0_val (τ : Fin 2 ≃ Fin 2) : (mu0 K).val τ = if τ = Equiv.refl _ then 1 else 0 := by
  classical
  show (Finsupp.single (NOrd.std 2 (by decide)) (1 : K) : NOrd (Fin 2) →₀ K) (ord2 τ) = _
  rw [Finsupp.single_apply]
  have hiff : NOrd.std 2 (by decide) = ord2 τ ↔ τ = Equiv.refl _ := by
    constructor
    · intro h
      have h' : LinOrd.map (Equiv.refl (Fin 2)) (LinOrd.std 2) = LinOrd.map τ (LinOrd.std 2) :=
        (LinOrd.ext fun a b => Iff.rfl : LinOrd.map (Equiv.refl (Fin 2)) (LinOrd.std 2)
          = LinOrd.std 2).trans (congrArg Subtype.val h)
      exact (LinOrd.eq_of_map_eq h').symm
    · rintro rfl
      exact (SetOperad.map_refl (S := NOrd) _).symm
  by_cases h : τ = Equiv.refl _
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg fun h' => h (hiff.1 h'), if_neg h]

/-- The planar terms of the square of the desuspension map vanish, except those of two inner
inputs in two outer inputs. -/
lemma plTN_kapO_eq_zero {N : ℕ} {x : ℕ × ℕ} (h : x.1 ≠ 1 ∨ N ≠ 3) :
    NOrd.plTN (kapO K) (kapO K) N x = 0 := by
  rw [NOrd.plTN]
  split_ifs with hc
  · rw [NOrd.plT, SgnLin.repW]
    by_cases h1 : x.1 = 1
    · rw [kapO_eq_zero K (A := Fin (N - x.1)) (by rw [Fintype.card_fin]; omega), map_zero,
        smul_zero, map_zero]
    · rw [kapO_eq_zero K (A := Fin (x.1 + 1)) (by rw [Fintype.card_fin]; omega),
        LinearMap.map_zero₂, smul_zero, map_zero]
  · rfl

local notation "φ" => SymPresAss.φ K

omit [CharZero K] in
/-- The model of the generator: the product of the two inputs. -/
lemma sgEv_mu0 (w : Fin 2 → SymPresAss.V K) :
    SymPresB.sgEv ((φ).app (Fin 2) ((FreeGrL.ι K 𝔼).app (Fin 2) (mu0 K))) w = w 0 * w 1 := by
  rw [SymPresAss.φ, SymPresB.model, FreeGrL.homEquiv_symm_ι]
  show SymPresB.sgEv (SymPresB.modelApp _ (Fin 2) (mu0 K)) w = _
  rw [SymPresB.sgEv_modelApp]
  simp only [mu0_val, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ (Equiv.refl (Fin 2)), if_pos (Finset.mem_univ _)]
  rfl

/-- The model of a planar term of two inner inputs in two outer inputs. -/
lemma sgEv_plT (i : Fin 2) (h : 3 + 1 = 2 + 2) (hl : 0 < 2) (w : Fin 3 → SymPresAss.V K) :
    SymPresB.sgEv ((φ).app (Fin 3) (NOrd.plT (kapO K) (kapO K) i 2 3 h hl)) w
      = (σ K (NOrd.aftN (LinOrd.std 2) i).bodd * -1) •
          SymPresB.sgEv ((φ).app (Fin 2) ((FreeGrL.ι K 𝔼).app (Fin 2) (mu0 K)))
            (feed i (w ∘ posEquivF i 2 3 h)
              (SymPresB.sgEv ((φ).app (Fin 2) ((FreeGrL.ι K 𝔼).app (Fin 2) (mu0 K)))
                fun b => w (posEquivF i 2 3 h (Sum.inr b)))) := by
  have htw : GrSpecies.tw (R := K) true (SgnLin.bas NOrd.sgnD K (NOrd.std 2 (Fin.pos i)))
      = (-1 : K) • SgnLin.bas NOrd.sgnD K (NOrd.std 2 (Fin.pos i)) :=
    (GrSpecies.tw_hom true (SgnLin.par_bas (R := K) (δ := NOrd.sgnD)
      (NOrd.std 2 (Fin.pos i)))).trans rfl
  have h1 : ConvOp.toLin ((kapO K).1 (Fin 2))
      ((-1 : K) • SgnLin.bas NOrd.sgnD K (NOrd.std 2 (Fin.pos i)))
      = (-1 : K) • (FreeGrL.ι K 𝔼).app (Fin 2) (mu0 K) := by
    rw [map_smul]
    exact congrArg _ (kapO_std2 K)
  have h2 : ConvOp.toLin ((kapO K).1 (Fin 2)) (SgnLin.bas NOrd.sgnD K (NOrd.std 2 hl))
      = (FreeGrL.ι K 𝔼).app (Fin 2) (mu0 K) := kapO_std2 K
  have hsgn : SgnData.sgn i (NOrd.sgnD.app (Fin 2) (NOrd.std 2 (Fin.pos i)))
      (NOrd.sgnD.app (Fin 2) (NOrd.std 2 hl)) = (NOrd.aftN (LinOrd.std 2) i).bodd := by
    show ((Fintype.card (Fin 2) + 1).bodd && (NOrd.aftN (LinOrd.std 2) i).bodd) = _
    rw [Fintype.card_fin]
    rfl
  rw [NOrd.plT, SgnLin.repW, htw, h1, h2, hsgn, (φ).app_map, SymPresB.sgEv_map, map_smul,
    SymPresB.sgEv_smul, (φ).app_comp, map_smul, LinearMap.map_smul₂, SymPresB.sgEv_smul,
    SymPresB.sgEv_comp, smul_smul]
  rfl

/-- **The square of the desuspension map on a standard order is a relation of `Ass`.** -/
theorem star_kapO_mem (N : ℕ) (hN : 0 < N) :
    ConvOp.toLin ((GrOperad.Inv.star K _ (kapO K) (kapO K)).1 (Fin N))
        (SgnLin.bas NOrd.sgnD K (NOrd.std N hN))
      ∈ (GrOperadIdeal.span K (SymPresAss.rel K)).sub (Fin N) := by
  rw [NOrd.star_std _ _ (isParC_kapO K) N hN]
  by_cases h3 : N = 3
  swap
  · rw [Finset.sum_eq_zero fun x _ => plTN_kapO_eq_zero K (Or.inr h3)]
    exact zero_mem _
  subst h3
  refine GrOperadIdeal.subset_span 3 ⟨rfl, ?_⟩
  have hsub : ({(1, 0), (1, 1)} : Finset (ℕ × ℕ)) ⊆ NOrd.idx 3 := fun x hx => by
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact NOrd.mem_idx.2 (by decide)
  rw [← Finset.sum_subset hsub fun x hx hx' => plTN_kapO_eq_zero K (Or.inl fun h1 => hx' (by
      obtain ⟨j, i⟩ := x
      have hm := NOrd.mem_idx.1 hx
      simp only at h1 hm
      subst h1
      rw [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk.injEq]
      omega)),
    Finset.sum_pair (by decide)]
  refine (SymPresB.eq_zero_iff _).2 fun w => ?_
  show SymPresB.sgEv ((φ).app (Fin 3)
    (NOrd.plT (kapO K) (kapO K) (0 : Fin 2) 2 3 rfl (by decide)
      + NOrd.plT (kapO K) (kapO K) (1 : Fin 2) 2 3 rfl (by decide))) w = 0
  rw [map_add, SymPresB.sgEv_add, sgEv_plT, sgEv_plT, sgEv_mu0, sgEv_mu0, sgEv_mu0, sgEv_mu0]
  have e0 : ∀ j : Fin 2, posEquivF (0 : Fin 2) 2 3 rfl (Sum.inr j) = ⟨j, by omega⟩ := fun j =>
    Fin.ext (by rw [posEquivF_inr]; simp)
  have e1 : ∀ j : Fin 2, posEquivF (1 : Fin 2) 2 3 rfl (Sum.inr j) = ⟨1 + j, by omega⟩ :=
    fun j => Fin.ext (by rw [posEquivF_inr]; rfl)
  have e0l : posEquivF (0 : Fin 2) 2 3 rfl (Sum.inl ⟨1, by decide⟩) = 2 :=
    Fin.ext (by
      have := posEquivF_inl_of_gt (0 : Fin 2) (show 3 + 1 = 2 + 2 from rfl) ⟨1, by decide⟩
        (by decide)
      simp only [Fin.val_one] at this
      show _ = 2
      omega)
  have e1l : posEquivF (1 : Fin 2) 2 3 rfl (Sum.inl ⟨0, by decide⟩) = 0 :=
    Fin.ext (posEquivF_inl_of_lt (1 : Fin 2) (show 3 + 1 = 2 + 2 from rfl) ⟨0, by decide⟩
      (by decide))
  have a0 : (NOrd.aftN (LinOrd.std 2) (0 : Fin 2)).bodd = true := by
    rw [NOrd.aftN, Fin.sum_univ_two, if_neg ((LinOrd.std 2).irrefl 0),
      if_pos (show (LinOrd.std 2).lt 0 1 from (by decide : (0 : Fin 2) < 1))]
    rfl
  have a1 : (NOrd.aftN (LinOrd.std 2) (1 : Fin 2)).bodd = false := by
    rw [NOrd.aftN, Fin.sum_univ_two,
      if_neg (show ¬ (LinOrd.std 2).lt 1 0 from (by decide : ¬ (1 : Fin 2) < 0)),
      if_neg ((LinOrd.std 2).irrefl 1)]
    rfl
  rw [a0, a1, feed_self, feed_self,
    feed_of_ne (show (1 : Fin 2) ≠ 0 by decide), feed_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  simp only [Function.comp_apply, e0, e1, e0l, e1l, σ_true, σ_false]
  show ((-1 : K) * -1) • ((w 0 * w 1) * w 2) + ((1 : K) * -1) • (w 0 * (w 1 * w 2)) = 0
  rw [mul_assoc]
  simp

/-- **The square of the desuspension map on the signed linear orders lands in the relations of
`Ass`.** -/
theorem star_kapO_mem_ideal (y : OrdCo K A) :
    ConvOp.toLin ((GrOperad.Inv.star K _ (kapO K) (kapO K)).1 A) y
      ∈ (GrOperadIdeal.span K (SymPresAss.rel K)).sub A := by
  have key : ∀ y : NOrd A →₀ K,
      ConvOp.toLin ((GrOperad.Inv.star K _ (kapO K) (kapO K)).1 A) (show OrdCo K A from y)
        ∈ (GrOperadIdeal.span K (SymPresAss.rel K)).sub A := by
    intro y
    refine Finsupp.induction_linear y ?_ (fun x y hx hy => ?_) (fun L c => ?_)
    · exact (congrArg (· ∈ (GrOperadIdeal.span K (SymPresAss.rel K)).sub A)
        (LinearMap.map_zero _)).mpr (zero_mem _)
    · exact (congrArg (· ∈ (GrOperadIdeal.span K (SymPresAss.rel K)).sub A)
        (LinearMap.map_add _ _ _)).mpr (add_mem hx hy)
    · obtain ⟨a₀⟩ := L.2
      have hN : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨a₀⟩
      obtain ⟨e, he⟩ := LinOrd.exists_map_eq (LinOrd.std (Fintype.card A)) L.1
        (Fintype.card_fin _)
      have hL : SgnLin.bas NOrd.sgnD K L
          = GrOperad.map (R := K) e (SgnLin.bas NOrd.sgnD K (NOrd.std _ hN)) := by
        rw [SgnLin.map_bas]
        exact congrArg (SgnLin.bas NOrd.sgnD K) (Subtype.ext he.symm)
      have h1 : ConvOp.toLin ((GrOperad.Inv.star K _ (kapO K) (kapO K)).1 A)
          (SgnLin.bas NOrd.sgnD K L)
          = GrOperad.map (R := K) e (ConvOp.toLin
            ((GrOperad.Inv.star K _ (kapO K) (kapO K)).1 (Fin (Fintype.card A)))
            (SgnLin.bas NOrd.sgnD K (NOrd.std _ hN))) :=
        (congrArg _ hL).trans (SgnLin.inv_toLin_map _ e _)
      have h2 : ConvOp.toLin ((GrOperad.Inv.star K _ (kapO K) (kapO K)).1 A)
          (show OrdCo K A from Finsupp.single L c)
          = c • ConvOp.toLin ((GrOperad.Inv.star K _ (kapO K) (kapO K)).1 A)
            (SgnLin.bas NOrd.sgnD K L) :=
        (congrArg _ (Finsupp.smul_single_one L c).symm).trans (LinearMap.map_smul _ _ _)
      exact (congrArg (· ∈ (GrOperadIdeal.span K (SymPresAss.rel K)).sub A)
        (h2.trans (congrArg _ h1))).mpr (Submodule.smul_mem _ _
          ((GrOperadIdeal.span K (SymPresAss.rel K)).map_mem e (star_kapO_mem K _ hN)))
  exact key y

end OrdCo

/-! ## Morphisms into a subcooperad -/

namespace GrCooperadHom

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [GrCooperad R C']

/-- **The image of a morphism of graded cooperads** is a subcooperad. -/
def rangeSub (f : GrCooperadHom R C' C) : GrSubCooperad R C where
  sub A _ _ := LinearMap.range (f.app A)
  par_mem b := by
    rintro _ ⟨y, rfl⟩
    exact ⟨GrSpecies.par (R := R) b y, f.app_par b y⟩
  map_mem e := by
    rintro _ ⟨y, rfl⟩
    exact ⟨SymSpecies.map (R := R) e y, f.app_map e y⟩
  decomp_mem {A B} _ _ _ _ i := by
    rintro _ ⟨y, rfl⟩
    have h1 : GrCooperad.decomp (R := R) (C := C) (B := B) i (f.app _ y)
        = TensorProduct.map (f.app A) (f.app B) (GrCooperad.decomp (R := R) i y) :=
      LinearMap.congr_fun (f.decomp_app (B := B) i) y
    have h2 : TensorProduct.map (f.app A) (f.app B)
        = TensorProduct.map (LinearMap.range (f.app A)).subtype
            (LinearMap.range (f.app B)).subtype ∘ₗ
          TensorProduct.map (f.app A).rangeRestrict (f.app B).rangeRestrict := by
      rw [← TensorProduct.map_comp]
      rfl
    rw [h1, h2]
    exact ⟨_, rfl⟩

lemma mem_rangeSub (f : GrCooperadHom R C' C) {A : Type} [Fintype A] [DecidableEq A]
    (y : C' A) : f.app A y ∈ (rangeSub f).sub A := ⟨y, rfl⟩

end GrCooperadHom

namespace GrSubCooperad

variable {R : Type u} [Field R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [GrCooperad R C']
  (K : GrSubCooperad R C)

/-- **A morphism of graded cooperads with values in a subcooperad**, as a morphism into it. -/
noncomputable def liftHom (f : GrCooperadHom R C' C)
    (hf : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C' A), f.app A x ∈ K.sub A) :
    GrCooperadHom R C' K.Sub where
  app A _ _ := (f.app A).codRestrict (K.sub A) (hf A)
  app_map {A B} _ _ _ _ e x := K.incl_injective _ ((f.app_map e x).trans
    (K.incl_map e ((f.app A).codRestrict _ (hf A) x)).symm)
  app_par {A} _ _ b x := K.incl_injective _ ((f.app_par b x).trans
    (K.incl_par b ((f.app A).codRestrict _ (hf A) x)).symm)
  counit_app := LinearMap.ext fun x => LinearMap.congr_fun f.counit_app x
  decomp_app {A B} _ _ _ _ i := LinearMap.ext fun x => K.map_incl_injective (by
    have h1 := LinearMap.congr_fun (K.inclHom.decomp_app (B := B) i)
      ((f.app _).codRestrict _ (hf _) x)
    have h2 := LinearMap.congr_fun (f.decomp_app (B := B) i) x
    have h3 : TensorProduct.map (f.app A) (f.app B)
        = TensorProduct.map (K.incl A) (K.incl B) ∘ₗ
          TensorProduct.map ((f.app A).codRestrict _ (hf A))
            ((f.app B).codRestrict _ (hf B)) := by
      rw [← TensorProduct.map_comp]
      rfl
    exact h1.symm.trans (h2.trans (LinearMap.congr_fun h3 _)))

lemma incl_liftHom (f : GrCooperadHom R C' C)
    (hf : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C' A), f.app A x ∈ K.sub A)
    {A : Type} [Fintype A] [DecidableEq A] (x : C' A) :
    K.incl A ((K.liftHom f hf).app A x) = f.app A x := rfl

end GrSubCooperad

/-! ## The signed linear orders in the Koszul dual cooperad of `Ass` -/

namespace OrdCo

variable (K : Type u) [Field K] [CharZero K] {A B : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

local notation "𝔼" => SymPresB.Reg2 K

/-- **The image of the signed linear orders lies in the Koszul dual cooperad of `Ass`.** -/
theorem toCut_mem_dualSub (y : OrdCo K A) :
    (toCut K).app A y ∈ (Koszul.dualSub K 𝔼 (SymPresAss.rel K)).sub A := by
  have h : (toCut K).rangeSub ≤ Koszul.dualSub K 𝔼 (SymPresAss.rel K) :=
    Koszul.le_dualSub (SymPresAss.rel K) fun A _ _ x hx => by
      obtain ⟨y, rfl⟩ := hx
      rw [star_toCut]
      exact star_kapO_mem_ideal K y
  exact h A ((toCut K).mem_rangeSub y)

/-- **The signed linear orders in the Koszul dual cooperad of `Ass`.** -/
noncomputable def toDual :
    GrCooperadHom K (OrdCo K) (Koszul.Dual K 𝔼 (SymPresAss.rel K)) :=
  (Koszul.dualSub K 𝔼 (SymPresAss.rel K)).liftHom (toCut K)
    fun _ _ _ y => toCut_mem_dualSub K y

lemma incl_toDual (y : OrdCo K A) :
    (Koszul.dualSub K 𝔼 (SymPresAss.rel K)).incl A ((toDual K).app A y) = (toCut K).app A y :=
  rfl

end OrdCo

end Operad
