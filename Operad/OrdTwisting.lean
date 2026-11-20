/-
# Twisting morphisms out of the cooperad of signed linear orders

The symmetric groups act freely on the linear orders, so **the invariant families on `OrdCo K`
with values in a graded operad `Q` are the families of operations `a n : Q (Fin (n + 1))`**, one
of each positive arity (`OrdCo.invEquiv`, `OrdCo.famOf`, `OrdCo.ofFam`): the values at the
standard orders.

In these terms, an invariant family is odd iff `a n` has the parity of `n + 1`
(`OrdCo.isPar_iff`), it kills the coaugmentation iff `a 0 = 0` (`OrdCo.killsUnit_iff`), and for a
dg operad `Q` it satisfies the Maurer–Cartan equation iff, for every `n`, the differential of
`a n` and the planar terms of the convolution square at the standard order on `n + 1` inputs add
up to zero (`OrdCo.mc_iff`, with `NOrd.star_std`).
-/
import Operad.OrdCut
import Operad.Twisting

universe u w

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace OrdCo

variable {K : Type u} [CommRing K]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (Q A)]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "bs" => SgnLin.bas NOrd.sgnD K

/-- The standard order on `n + 1` inputs. -/
abbrev sd (n : ℕ) : NOrd (Fin (n + 1)) := NOrd.std (n + 1) n.succ_pos

/-- Linear maps out of the signed linear orders agree when they agree on the orders. -/
lemma hom_ext {M : Type*} [AddCommGroup M] [Module K M] {f g : OrdCo K A →ₗ[K] M}
    (h : ∀ L : NOrd A, f (bs L) = g (bs L)) : f = g :=
  Finsupp.lhom_ext fun L c => by
    have hs : (Finsupp.single L c : NOrd A →₀ K) = c • (bs L : OrdCo K A) :=
      (Finsupp.smul_single_one L c).symm
    exact (congrArg f hs).trans ((map_smul f c _).trans
      ((congrArg (c • ·) (h L)).trans ((map_smul g c _).symm.trans (congrArg g hs).symm)))

/-- **Every nonempty linear order is a relabelling of a standard order.** -/
lemma exists_std (L : NOrd A) : ∃ (n : ℕ) (e : Fin (n + 1) ≃ A), SetOperad.map e (sd n) = L := by
  obtain ⟨a₀⟩ := L.2
  have hpos : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨a₀⟩
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card A = n + 1 := ⟨Fintype.card A - 1, by omega⟩
  obtain ⟨e, he⟩ := LinOrd.exists_map_eq (LinOrd.std (n + 1)) L.1
    ((Fintype.card_fin _).trans hn.symm)
  exact ⟨n, e, Subtype.ext he⟩

variable (K) in
/-- The value of a family of operations at a signed linear order. -/
noncomputable def famVal (a : ∀ n : ℕ, Q (Fin (n + 1))) [GrOperad K Q] (L : NOrd A) : Q A :=
  GrOperad.map (R := K) (Classical.choose (Classical.choose_spec (exists_std L)))
    (a (Classical.choose (exists_std L)))

variable [GrOperad K Q]

omit [Fintype B] [DecidableEq B] in
lemma map_eq_of_std (a : ∀ n : ℕ, Q (Fin (n + 1))) {m n : ℕ} (e' : Fin (m + 1) ≃ A)
    (e : Fin (n + 1) ≃ A) (h : SetOperad.map e' (sd m) = SetOperad.map e (sd n)) :
    GrOperad.map (R := K) e' (a m) = GrOperad.map (R := K) e (a n) := by
  have hmn : m = n := by
    have h1 := Fintype.card_congr e
    have h2 := Fintype.card_congr e'
    rw [Fintype.card_fin] at h1 h2
    omega
  subst hmn
  rw [LinOrd.eq_of_map_eq (congrArg Subtype.val h)]

omit [Fintype B] [DecidableEq B] in
lemma famVal_map (a : ∀ n : ℕ, Q (Fin (n + 1))) {n : ℕ} (e : Fin (n + 1) ≃ A) :
    famVal K a (SetOperad.map e (sd n)) = GrOperad.map (R := K) e (a n) :=
  map_eq_of_std a _ e
    (Classical.choose_spec (Classical.choose_spec (exists_std (SetOperad.map e (sd n)))))

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
lemma lift_single_one {X : Type*} {M : Type*} [AddCommGroup M] [Module K M] (f : X → M)
    (x : X) : Finsupp.lift M K X f (Finsupp.single x 1) = f x := by
  rw [Finsupp.lift_apply, Finsupp.sum_single_index]
  · exact one_smul K _
  · exact zero_smul K _

/-- **The invariant family of a family of operations**, one for each standard order. -/
noncomputable def ofFam (a : ∀ n : ℕ, Q (Fin (n + 1))) :
    GrOperad.Inv K (ConvOp K (OrdCo K) Q) :=
  ⟨fun A _ _ => ConvOp.of (Finsupp.lift (Q A) K (NOrd A) fun L => famVal K a L),
    fun A B _ _ _ _ σ => by
      show ConvOp.mapC σ _ = _
      refine congrArg ConvOp.of (hom_ext fun L' => ?_)
      obtain ⟨n, e, rfl⟩ := exists_std L'
      show GrOperad.map (R := K) σ (Finsupp.lift (Q A) K (NOrd A) (fun L => famVal K a L)
        (GrOperad.map (R := K) σ.symm (bs (SetOperad.map e (sd n)))))
          = Finsupp.lift (Q B) K (NOrd B) (fun L => famVal K a L) (bs (SetOperad.map e (sd n)))
      rw [SgnLin.map_bas, ← SetOperad.map_trans]
      show GrOperad.map (R := K) σ (Finsupp.lift (Q A) K (NOrd A) (fun L => famVal K a L)
        (Finsupp.single _ 1)) = Finsupp.lift (Q B) K (NOrd B) (fun L => famVal K a L)
          (Finsupp.single _ 1)
      rw [lift_single_one, lift_single_one, famVal_map, famVal_map, ← GrOperad.map_trans]
      exact congrArg (fun E => GrOperad.map (R := K) E (a n)) (Equiv.ext fun x => by simp)⟩

lemma ofFam_bs (a : ∀ n : ℕ, Q (Fin (n + 1))) (L : NOrd A) :
    ConvOp.toLin ((ofFam (K := K) a).1 A) (bs L) = famVal K a L :=
  lift_single_one _ L

/-- **The family of operations of an invariant family**: its values at the standard orders. -/
noncomputable def famOf (α : GrOperad.Inv K (ConvOp K (OrdCo K) Q)) (n : ℕ) : Q (Fin (n + 1)) :=
  ConvOp.toLin (α.1 (Fin (n + 1))) (bs (sd n))

lemma toLin_bs_map (α : GrOperad.Inv K (ConvOp K (OrdCo K) Q)) {n : ℕ} (e : Fin (n + 1) ≃ A) :
    ConvOp.toLin (α.1 A) (bs (SetOperad.map e (sd n))) = GrOperad.map (R := K) e (famOf α n) := by
  rw [← SgnLin.map_bas]
  exact SgnLin.inv_toLin_map α e _

/-- **The invariant families on the signed linear orders are the families of operations**, one
of each positive arity: the symmetric groups act freely on the orders. -/
noncomputable def invEquiv :
    GrOperad.Inv K (ConvOp K (OrdCo K) Q) ≃ (∀ n : ℕ, Q (Fin (n + 1))) where
  toFun := famOf
  invFun := ofFam
  left_inv α := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    congrArg ConvOp.of (hom_ext fun L => by
      obtain ⟨n, e, rfl⟩ := exists_std L
      exact (ofFam_bs _ _).trans ((famVal_map _ e).trans (toLin_bs_map α e).symm)))
  right_inv a := funext fun n => by
    have h := (ofFam_bs (K := K) a (SetOperad.map (Equiv.refl _) (sd n))).trans
      (famVal_map (K := K) a (Equiv.refl _))
    rw [SetOperad.map_refl, GrOperad.map_refl] at h
    exact h

/-! ## Parity and units -/

omit [Fintype B] [DecidableEq B] in
lemma par_bs (L : NOrd A) (c : Bool) :
    GrSpecies.par (R := K) c (bs L : OrdCo K A)
      = if (Fintype.card A + 1).bodd = c then bs L else 0 :=
  SgnLin.parT_single (R := K) (δ := NOrd.sgnD) c L 1

omit [Fintype B] [DecidableEq B] in
/-- **An invariant family on the signed linear orders is odd** iff its operation of arity `n + 1`
has the parity of `n + 1`. -/
theorem isPar_iff (α : GrOperad.Inv K (ConvOp K (OrdCo K) Q)) :
    GrOperad.Inv.IsPar true α
      ↔ ∀ n, GrOperad.par (R := K) (n + 1).bodd (famOf α n) = famOf α n := by
  constructor
  · intro h n
    have hc := (ConvOp.parC_eq_self_iff.1 (h (Fin (n + 1)))) (n + 1 + 1).bodd (bs (sd n))
    rw [par_bs, Fintype.card_fin, if_pos rfl] at hc
    have hb : xor (n + 1 + 1).bodd true = (n + 1).bodd := by
      rw [Nat.bodd_succ (n + 1)]
      cases (n + 1).bodd <;> rfl
    rw [hb] at hc
    exact hc.symm
  · intro h A _ _
    refine ConvOp.parC_eq_self_iff.2 fun c x => ?_
    have key : ConvOp.toLin (α.1 A) ∘ₗ GrSpecies.par (R := K) c
        = GrOperad.par (R := K) (xor c true) ∘ₗ ConvOp.toLin (α.1 A) := hom_ext fun L => by
      obtain ⟨n, e, rfl⟩ := exists_std L
      have hA : Fintype.card A = n + 1 := (Fintype.card_congr e).symm.trans (Fintype.card_fin _)
      have hy : GrOperad.par (R := K) (n + 1).bodd
          (ConvOp.toLin (α.1 A) (bs (SetOperad.map e (sd n))))
          = ConvOp.toLin (α.1 A) (bs (SetOperad.map e (sd n))) := by
        rw [toLin_bs_map, ← GrOperad.map_par, h n]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, par_bs, hA, ← hy, GrOperad.par_par]
      have hb : (n + 1 + 1).bodd = !(n + 1).bodd := Nat.bodd_succ (n + 1)
      by_cases hc : (n + 1 + 1).bodd = c
      · rw [if_pos hc, if_pos (by rw [← hc, hb]; cases (n + 1).bodd <;> rfl), hy]
      · rw [if_neg hc, if_neg (by
          intro h'
          apply hc
          rw [hb, ← h']
          cases c <;> rfl), map_zero]
    exact LinearMap.congr_fun key x

omit [Fintype B] [DecidableEq B] in
/-- **An invariant family on the signed linear orders kills the coaugmentation** iff its
operation of arity one vanishes. -/
theorem killsUnit_iff (α : GrOperad.Inv K (ConvOp K (OrdCo K) Q)) :
    KillsUnit K (OrdCo K) Q α ↔ famOf α 0 = 0 := by
  haveI : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  have h1 : (bs (SetOperad.one : NOrd Unit) : OrdCo K Unit)
      = GrOperad.map (R := K) (Equiv.ofUnique (Fin 1) Unit) (bs (sd 0)) := by
    rw [SgnLin.map_bas]
    exact congrArg _ (Subtype.ext (LinOrd.eq_of_subsingleton _ _))
  have h2 : (bs (sd 0) : OrdCo K (Fin 1))
      = GrOperad.map (R := K) (Equiv.ofUnique Unit (Fin 1)) (bs (SetOperad.one : NOrd Unit)) := by
    rw [SgnLin.map_bas]
    exact congrArg _ (Subtype.ext (LinOrd.eq_of_subsingleton _ _))
  constructor
  · intro h
    exact h (Fin 1) (bs (sd 0)) (h2 ▸ Submodule.subset_span ⟨Equiv.ofUnique Unit (Fin 1), rfl⟩)
  · intro h A _ _ x hx
    refine (Submodule.span_le.2 ?_ : GrCooperad.unitSpan K (OrdCo K) A
      ≤ LinearMap.ker (ConvOp.toLin (α.1 A))) hx
    rintro _ ⟨e, rfl⟩
    show ConvOp.toLin (α.1 A) (GrOperad.map (R := K) e (bs (SetOperad.one : NOrd Unit))) = 0
    rw [h1, SgnLin.inv_toLin_map, SgnLin.inv_toLin_map]
    show GrOperad.map (R := K) e (GrOperad.map (R := K) _ (famOf α 0)) = 0
    rw [h, map_zero, map_zero]

end OrdCo

/-! ## The Maurer–Cartan equation -/

namespace OrdCo

variable {K : Type u} [CommRing K]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (Q A)] [DGOperad K Q]

local notation "bs" => SgnLin.bas NOrd.sgnD K

/-- **The Maurer–Cartan equation on the signed linear orders, in planar terms**: for an odd
invariant family, the equation holds iff at every standard order the differential of the
operation and the planar terms of the convolution square add up to zero. -/
theorem mc_iff (α : GrOperad.Inv K (ConvOp K (OrdCo K) Q)) (hα : GrOperad.Inv.IsPar true α) :
    GrOperad.Inv.appDer (ConvOp.postDer (C := OrdCo K) (DGOperad.toDer (R := K) (P := Q))) α
        + GrOperad.Inv.star K _ α α = 0
      ↔ ∀ n, DGOperad.d (R := K) (famOf α n)
          + ∑ x ∈ NOrd.idx (n + 1), NOrd.plTN α α (n + 1) x = 0 := by
  have hodd : ∀ (B : Type) [Fintype B] [DecidableEq B], ConvOp.IsParC true (α.1 B) :=
    fun B _ _ => ConvOp.parC_eq_self_iff.1 (hα B)
  have hfam : ∀ n, famOf (GrOperad.Inv.appDer
      (ConvOp.postDer (C := OrdCo K) (DGOperad.toDer (R := K) (P := Q))) α
        + GrOperad.Inv.star K _ α α) n
      = DGOperad.d (R := K) (famOf α n)
        + ∑ x ∈ NOrd.idx (n + 1), NOrd.plTN α α (n + 1) x := fun n => by
    rw [← NOrd.star_std α α hodd (n + 1) n.succ_pos]
    rfl
  constructor
  · intro h n
    rw [← hfam n, h]
    rfl
  · intro h
    refine (invEquiv (K := K) (Q := Q)).injective (funext fun n => ?_)
    exact (hfam n).trans (h n)

end OrdCo

end Operad
