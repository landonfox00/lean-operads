/-
# `Ass∞`-algebras are `A∞`-algebras

Over a field `K` of characteristic zero, for a dg super module `V`: **the homotopy algebras over
the Koszul dual cooperad of `Ass` on `V` are the `A∞`-structures on `V`**
(`PInfAss.pinfEquiv`), where

* `Koszul.PInfAlgebra K E r V` is the type of the `Ass∞`-algebra structures, the algebras over
  `ΩAss^¡` for the presentation of `Ass` of `Operad/SymPresAss.lean`, on `V` with its
  differential;
* `PInfAss.AInfOver K V` is the type of the `A∞`-structures `b` in the bar convention
  (`AInf.IsAInf`) for the sign involution `-eps K V`, the sign involution of the parity shift of
  `V`, whose first operation `b 0` is the differential of `V`.

The equivalence composes `HoAlgebra.equivTwisting`, the identification of `Ass^¡` with the
cooperad of signed linear orders (`OrdCo.twEquiv`), and `PInfAss.twistingEquiv`: a twisting
morphism `α : OrdCo K → End_V` goes to the family of the décalages of its operations at the
standard orders, with the differential in arity one.

* **Parities** (`PInfAss.parML_iff_isHomog`): an operation has the parity of its arity iff its
  décalage is odd for the opposite sign involution; the converse uses that `2` is invertible.
* The first operation is the differential (`PInfAss.barFam_dInv_zero`), and the Maurer–Cartan
  equation is the `A∞` relation (`PInfAss.mc_iff_tstar`).

Signs: the operation of arity `n` of the `Ass∞`-structure and the operation `b (n - 1)` differ
on homogeneous inputs `x₁, …, xₙ` by the sign `(-1)^(∑ₖ (n - k) |xₖ|)`, with no other sign. The
identification is with the `A∞`-structures on the parity shift, not with a convention where the
operation of arity `n` has degree `n - 2` on `V` itself; the library has no such second
convention.
-/
import Operad.PInfAss

universe u v

namespace Operad

open Sym GerBV GrEnd
open scoped TensorProduct

namespace PInfAss

open OrdCo

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [SuperMod K V]

/-! ## Parities -/

/-- A vector with the sign of a parity lies in the part of that parity, away from
characteristic two. -/
lemma pr_eq_of_eps [CharZero K] {b : Bool} {y : V} (h : eps K V y = σ K b • y) :
    SuperMod.pr (R := K) b y = y := by
  have hadd := SuperMod.pr_add (R := K) y
  rw [eps, LinearMap.sub_apply] at h
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  cases b
  · rw [σ_false, one_smul] at h
    generalize SuperMod.pr (R := K) false y = p0 at hadd h ⊢
    generalize SuperMod.pr (R := K) true y = p1 at hadd h
    have h3 : (2 : K) • p1 = 0 := by
      rw [two_smul]
      calc p1 + p1 = (p0 + p1) - (p0 - p1) := by abel
        _ = 0 := sub_eq_zero.2 (hadd.trans h.symm)
    rw [(smul_eq_zero.1 h3).resolve_left h2, add_zero] at hadd
    exact hadd
  · rw [σ_true, neg_smul, one_smul] at h
    generalize SuperMod.pr (R := K) true y = p1 at hadd h ⊢
    generalize SuperMod.pr (R := K) false y = p0 at hadd h
    have h3 : (2 : K) • p0 = 0 := by
      rw [two_smul]
      calc p0 + p0 = (p0 - p1) + (p0 + p1) := by abel
        _ = -y + y := by rw [h, hadd]
        _ = 0 := neg_add_cancel y
    rw [(smul_eq_zero.1 h3).resolve_left h2, zero_add] at hadd
    exact hadd

/-- The product of the signs of the inputs for the opposite sign involution. -/
lemma prod_neg_σ {N : ℕ} (c : Fin N → Bool) :
    ∏ t : Fin N, -σ K (c t) = σ K (xor N.bodd (tot c)) := by
  have h1 : ∏ t : Fin N, -σ K (c t) = (∏ _t : Fin N, (-1 : K)) * ∏ t : Fin N, σ K (c t) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => by ring
  have h2 := σ_and_tot K true c
  simp only [Bool.true_and] at h2
  rw [h1, ← h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← σ_bodd, ← σ_xor]

/-- **An operation has the parity of its arity iff its décalage is odd for the opposite sign
involution.** -/
theorem parML_iff_isHomog [CharZero K] {N : ℕ} (F : EndOp K V (Fin N)) :
    parML K V N.bodd F = F ↔ End.IsHomog (-eps K V) 1 (dec N F) := by
  have hval : ∀ {c : Fin N → Bool} {x : Fin N → V}, IsHom (R := K) c x →
      (dec N F) (fun t => (-eps K V) (x t)) = (decφ K N c * σ K (xor N.bodd (tot c))) • F x :=
    fun {c x} hx => by
      have h1 : (fun t => (-eps K V) (x t)) = fun t => (-σ K (c t)) • x t := funext fun t => by
        rw [LinearMap.neg_apply, eps_apply_hom (hx t), neg_smul]
      rw [h1, MultilinearMap.map_smul_univ, dec_apply_hom hx, smul_smul, prod_neg_σ, mul_comm]
  constructor
  · intro hF v
    have key : (dec N F).compLinearMap (fun _ => -eps K V)
        = (-1 : K) ^ 1 • (-eps K V).compMultilinearMap (dec N F) :=
      ext_hom fun c x hx => by
        show (dec N F) (fun t => (-eps K V) (x t)) = (-1 : K) ^ 1 • (-eps K V) (dec N F x)
        have hFx : SuperMod.pr (R := K) (xor N.bodd (tot c)) (F x) = F x := by
          rw [← parML_apply_hom hx, hF]
        rw [hval hx, dec_apply_hom hx, pow_one, LinearMap.neg_apply, map_smul,
          eps_apply_hom hFx, neg_one_smul, neg_neg, smul_smul]
    exact congrArg (fun f : EndOp K V (Fin N) => f v) key
  · intro hF
    refine ext_hom fun c x hx => ?_
    rw [parML_apply_hom hx]
    refine pr_eq_of_eps ?_
    have h1 := hF x
    rw [hval hx, dec_apply_hom hx, pow_one, LinearMap.neg_apply, map_smul, neg_one_smul,
      neg_neg, mul_smul] at h1
    have hd : ∀ z : V, decφ K N c • decφ K N c • z = z := fun z => by
      rw [smul_smul, decφ_mul_self, one_smul]
    have h2 := congrArg (fun z => decφ K N c • z) h1
    simp only [hd] at h2
    exact h2.symm

/-! ## The equivalence -/

section Equiv

variable [DGSuperMod K V]

omit [DGSuperMod K V] in
/-- The décalage of an operation on one input is the operation. -/
lemma dec_one (f : EndOp K V (Fin 1)) : dec 1 f = f :=
  ext_hom fun c x hx => by
    rw [dec_apply_hom hx, decφ, Fin.prod_univ_one]
    show σ K (false && c 0) • f x = f x
    rw [Bool.false_and, σ_false, one_smul]

/-- The differential, at the standard order on one input. -/
lemma sv_D1 (v : Fin 1 → V) : EndGr.sv (D1 K V) v = DGSuperMod.d (R := K) (v 0) := by
  show EndOp.mapL K V unitFinOne
    ((EndGr.dE K V).fam (LinOrd.map unitFinOne.symm (LinOrd.std 1))) v = _
  rw [LinOrd.eq_of_subsingleton (LinOrd.map unitFinOne.symm (LinOrd.std 1)) LinOrd.one, EndGr.dE,
    EndGr.ofFam_fam, EndOp.mapL_apply, EndGr.dML_apply]
  rfl

/-- The family in the bar convention of the family of the differential starts with the
differential. -/
lemma barFam_dInv_zero (v : Fin 1 → V) :
    barFam (dInv K V) 0 v = DGSuperMod.d (R := K) (v 0) := by
  show dec 1 (EndGr.sv (famOf (dInv K V) 0)) v = _
  rw [dec_one, famOf_dInv_zero, sv_D1]

/-- **The operations of an `A∞`-structure, as operations of the endomorphism operad**: the
décalages, at the standard orders. -/
noncomputable def hatFam (b : AInf.Fam K V) : ∀ n : ℕ, EndGr K V (Fin (n + 1)) :=
  fun n => EndGr.ofFam (LinOrd.std (n + 1)) (dec (n + 1) (b n))

omit [DGSuperMod K V] in
lemma barFam_ofFam_hatFam (b : AInf.Fam K V) : barFam (ofFam (K := K) (hatFam b)) = b := by
  funext n
  have h := congrFun ((invEquiv (K := K) (Q := EndGr K V)).right_inv (hatFam b)) n
  show dec (n + 1) (EndGr.sv (famOf (ofFam (K := K) (hatFam b)) n)) = b n
  rw [show famOf (ofFam (K := K) (hatFam b)) n = hatFam b n from h]
  show dec (n + 1) ((EndGr.ofFam (LinOrd.std (n + 1)) (dec (n + 1) (b n))).fam
    (LinOrd.std (n + 1))) = b n
  rw [EndGr.ofFam_fam, dec_dec]

omit [DGSuperMod K V] in
lemma ofFam_hatFam_barFam (β : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V))) :
    ofFam (K := K) (hatFam (barFam β)) = β := by
  refine (invEquiv (K := K) (Q := EndGr K V)).injective (funext fun n => ?_)
  have h := congrFun ((invEquiv (K := K) (Q := EndGr K V)).right_inv (hatFam (barFam β))) n
  refine h.trans ?_
  show EndGr.ofFam (LinOrd.std (n + 1)) (dec (n + 1) (dec (n + 1) (EndGr.sv (famOf β n))))
    = famOf β n
  rw [dec_dec]
  exact EndGr.ofFam_eq _ _

omit [DGSuperMod K V] in
/-- An invariant family is odd iff its family in the bar convention is odd for the opposite
sign involution. -/
lemma isPar_iff_barFam [CharZero K] (β : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V))) :
    GrOperad.Inv.IsPar true β ↔ ∀ n, End.IsHomog (-eps K V) 1 (barFam β n) := by
  rw [isPar_iff]
  refine forall_congr' fun n => ?_
  exact ⟨fun h => (parML_iff_isHomog _).1 ((EndGr.sv_par _ _).symm.trans (congrArg EndGr.sv h)),
    fun h => EndGr.ext_sv ((EndGr.sv_par _ _).trans ((parML_iff_isHomog _).2 h))⟩

variable (K V) in
/-- **The `A∞`-structures of a dg super module**: the `A∞`-structures in the bar convention, for
the opposite sign involution, whose first operation is the differential. -/
def AInfOver : Type v :=
  {b : AInf.Fam K V // AInf.IsAInf (-eps K V) b ∧
    ∀ v : Fin 1 → V, b 0 v = DGSuperMod.d (R := K) (v 0)}

lemma isPar_add_dInv {α : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V))}
    (hα : GrOperad.Inv.IsPar true α) : GrOperad.Inv.IsPar true (α + dInv K V) := fun A _ _ => by
  show GrOperad.par (R := K) true (α.1 A + (dInv K V).1 A) = α.1 A + (dInv K V).1 A
  rw [map_add, hα A, isPar_dInv A]

/-- **Twisting morphisms from the signed linear orders to the endomorphism operad of a dg super
module are its `A∞`-structures.** -/
noncomputable def twistingEquiv [CharZero K] :
    Twisting K (OrdCo K) (EndGr K V) ≃ AInfOver K V where
  toFun α := ⟨barFam (α.1 + dInv K V),
    ⟨(isPar_iff_barFam _).1 (isPar_add_dInv α.2.1),
      (mc_iff_tstar α.1 α.2.1).1 ((mc_iff α.1 α.2.1).1 α.2.2.2)⟩, fun v => by
      have h0 : famOf α.1 0 = 0 := (killsUnit_iff α.1).1 α.2.2.1
      have h1 : barFam (α.1 + dInv K V) 0 = barFam (dInv K V) 0 := by
        show dec 1 (EndGr.sv (famOf α.1 0 + famOf (dInv K V) 0)) = _
        rw [h0, zero_add]
        rfl
      rw [h1]
      exact barFam_dInv_zero v⟩
  invFun b := by
    have hsum : ofFam (K := K) (fun n => hatFam b.1 n - famOf (dInv K V) n) + dInv K V
        = ofFam (K := K) (hatFam b.1) := by
      refine (invEquiv (K := K) (Q := EndGr K V)).injective (funext fun n => ?_)
      have h1 := congrFun ((invEquiv (K := K) (Q := EndGr K V)).right_inv
        (fun n => hatFam b.1 n - famOf (dInv K V) n)) n
      have h2 := congrFun ((invEquiv (K := K) (Q := EndGr K V)).right_inv (hatFam b.1)) n
      show famOf (ofFam (K := K) (fun n => hatFam b.1 n - famOf (dInv K V) n)) n
        + famOf (dInv K V) n = famOf (ofFam (K := K) (hatFam b.1)) n
      rw [show famOf (ofFam (K := K) (fun n => hatFam b.1 n - famOf (dInv K V) n)) n
        = hatFam b.1 n - famOf (dInv K V) n from h1,
        show famOf (ofFam (K := K) (hatFam b.1)) n = hatFam b.1 n from h2, sub_add_cancel]
    have hβ : GrOperad.Inv.IsPar true (ofFam (K := K) (hatFam b.1)) :=
      (isPar_iff_barFam _).2 (by
        rw [barFam_ofFam_hatFam]
        exact b.2.1.odd)
    have hα : GrOperad.Inv.IsPar true
        (ofFam (K := K) (fun n => hatFam b.1 n - famOf (dInv K V) n)) := fun A _ _ => by
      have h1 : (ofFam (K := K) (fun n => hatFam b.1 n - famOf (dInv K V) n)).1 A
          = (ofFam (K := K) (hatFam b.1)).1 A - (dInv K V).1 A := by
        rw [← hsum]
        exact (add_sub_cancel_right _ _).symm
      rw [h1, map_sub, hβ A, isPar_dInv A]
    refine ⟨ofFam (K := K) (fun n => hatFam b.1 n - famOf (dInv K V) n), hα, ?_, ?_⟩
    · refine (killsUnit_iff _).2 ?_
      have h1 := congrFun ((invEquiv (K := K) (Q := EndGr K V)).right_inv
        (fun n => hatFam b.1 n - famOf (dInv K V) n)) 0
      refine h1.trans (sub_eq_zero.2 ?_)
      rw [famOf_dInv_zero]
      refine EndGr.ext_sv (MultilinearMap.ext fun v => ?_)
      show (EndGr.ofFam (LinOrd.std 1) (dec 1 (b.1 0))).fam (LinOrd.std 1) v = _
      rw [EndGr.ofFam_fam, dec_one, sv_D1]
      exact b.2.2 v
    · refine (mc_iff _ hα).2 ((mc_iff_tstar _ hα).2 ?_)
      rw [hsum, barFam_ofFam_hatFam]
      exact b.2.1.mc
  left_inv α := Subtype.ext (by
    refine (invEquiv (K := K) (Q := EndGr K V)).injective (funext fun n => ?_)
    have h1 := congrFun ((invEquiv (K := K) (Q := EndGr K V)).right_inv
      (fun n => hatFam (barFam (α.1 + dInv K V)) n - famOf (dInv K V) n)) n
    have h2 := congrFun (congrArg famOf (ofFam_hatFam_barFam (α.1 + dInv K V))) n
    have h3 := congrFun ((invEquiv (K := K) (Q := EndGr K V)).right_inv
      (hatFam (barFam (α.1 + dInv K V)))) n
    refine h1.trans ?_
    rw [← show famOf (ofFam (K := K) (hatFam (barFam (α.1 + dInv K V)))) n
      = hatFam (barFam (α.1 + dInv K V)) n from h3, h2]
    exact add_sub_cancel_right _ _)
  right_inv b := Subtype.ext (by
    show barFam (ofFam (K := K) (fun n => hatFam b.1 n - famOf (dInv K V) n) + dInv K V) = b.1
    have hsum : ofFam (K := K) (fun n => hatFam b.1 n - famOf (dInv K V) n) + dInv K V
        = ofFam (K := K) (hatFam b.1) := by
      refine (invEquiv (K := K) (Q := EndGr K V)).injective (funext fun n => ?_)
      have h1 := congrFun ((invEquiv (K := K) (Q := EndGr K V)).right_inv
        (fun n => hatFam b.1 n - famOf (dInv K V) n)) n
      have h2 := congrFun ((invEquiv (K := K) (Q := EndGr K V)).right_inv (hatFam b.1)) n
      show famOf (ofFam (K := K) (fun n => hatFam b.1 n - famOf (dInv K V) n)) n
        + famOf (dInv K V) n = famOf (ofFam (K := K) (hatFam b.1)) n
      rw [show famOf (ofFam (K := K) (fun n => hatFam b.1 n - famOf (dInv K V) n)) n
        = hatFam b.1 n - famOf (dInv K V) n from h1,
        show famOf (ofFam (K := K) (hatFam b.1)) n = hatFam b.1 n from h2, sub_add_cancel]
    rw [hsum, barFam_ofFam_hatFam])

/-- **`Ass∞`-algebras are `A∞`-algebras**: over a field of characteristic zero, the homotopy
algebras over the Koszul dual cooperad of the presentation of `Ass`, on a dg super module `V`,
are the `A∞`-structures on `V` in the bar convention, for the opposite sign involution, whose
first operation is the differential. -/
noncomputable def pinfEquiv [CharZero K] :
    Koszul.PInfAlgebra K (SymPresB.Reg2 K) (SymPresAss.rel K) V ≃ AInfOver K V :=
  HoAlgebra.equivTwisting.trans ((OrdCo.twEquiv K).trans twistingEquiv)

end Equiv

end PInfAss

end Operad
