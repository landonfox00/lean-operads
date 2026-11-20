/-
# `Lie∞`-algebras are `L∞`-algebras

Over a field `K` of characteristic zero, for a dg super module `V`: **the homotopy algebras over
the Koszul dual cooperad of `Lie` on `V` are the `L∞`-structures on `V`**
(`PInfLie.pinfEquiv`), where

* `Koszul.PInfAlgebra K E r V` is the type of the `Lie∞`-algebra structures, the algebras over
  `ΩLie^¡` for the presentation of `Lie` of `Operad/SymPresComLie.lean`, on `V` with its
  differential;
* `PInfLie.LInfOver K V` is the type of the families `ℓ` of operations of every arity which are
  an `L∞`-structure in the bar convention (`LInf.IsLInf`) for the sign involution `-eps K V`,
  the sign involution of the parity shift of `V`, with `ℓ 0 = 0` and `ℓ 1` the differential of
  `V`.

The equivalence composes `HoAlgebra.equivTwisting` and `PInfLie.twistingEquiv`. The latter is
stated for any cooperad of alternating lines over the signed linear orders (`AltGen`) and applied
to `Lie^¡` (`LieDual.altGen`, `LieDual.toOrd`): a twisting morphism `α` goes to the family
`PInfLie.toL` of the décalages of its operations at the generators, with the differential added
in arity one.

* **The differential** (`PInfLie.appDer_eq_gen`, `PInfLie.mc_iff_star`): the differential of an
  odd family is its convolution commutator with the family of the differential, so the
  Maurer–Cartan equation says that the family with the family of the differential added squares
  to zero.
* **The Maurer–Cartan equation is the generalized Jacobi identity** (`PInfLie.star_eq_zero_iff`),
  by `AltGen.star_nu` and `PInfLie.dec_sv_sum`.
* Parity, units and graded symmetry: `PInfLie.isPar_iff_toL`, `PInfLie.killsUnit_iff_toL`,
  `PInfLie.toL_symm`; together, `PInfLie.isLInf_iff`.

Signs: the operation of arity `n` of the `Lie∞`-structure and `ℓ n` differ on homogeneous inputs
`x₁, …, xₙ` by the sign `(-1)^(∑ₖ (n - k) |xₖ|)`, as for `Ass` (`Operad/PInfAssEquiv.lean`), and
by no other sign. The identification is with the `L∞[1]`-structures of `Operad/LInfinity.lean`,
graded symmetric operations on the parity shift, the only `L∞` convention in the library.
`LInf.IsLInf` asks for the identities on homogeneous inputs only. The condition `ℓ 0 = 0` is part
of `LInfOver` because the generalized Jacobi expressions do not involve `ℓ 0`.
-/
import Operad.PInfLie

universe u v w

namespace Operad

open Sym GerBV GrEnd
open scoped TensorProduct

namespace PInfLie

open OrdCo PInfAss

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [SuperMod K V]

/-! ## Parities -/

/-- A vector of a parity has the opposite parity for the opposite sign involution. -/
lemma isPar_of_isHom {c : Bool} {x : V} (hx : SuperMod.pr (R := K) c x = x) :
    IsPar (-eps K V) (!c) x := by
  show (-eps K V) x = σ K (!c) • x
  rw [LinearMap.neg_apply, eps_apply_hom hx, LInf.σ_not, neg_smul]

lemma isHom_of_isPar [CharZero K] {p : Bool} {x : V} (hx : IsPar (-eps K V) p x) :
    SuperMod.pr (R := K) (!p) x = x := by
  refine pr_eq_of_eps ?_
  have h : (-eps K V) x = σ K p • x := hx
  rw [LinearMap.neg_apply] at h
  rw [LInf.σ_not, neg_smul, ← h, neg_neg]

variable [DGSuperMod K V]

/-! ## The family of the differential, on the signed linear orders -/

/-- **The differential of an odd family is its convolution commutator with the family of the
differential.** -/
theorem appDer_eq (β : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)))
    (hβ : GrOperad.Inv.IsPar true β) :
    GrOperad.Inv.appDer (ConvOp.postDer (C := OrdCo K) (DGOperad.toDer (R := K) (P := EndGr K V))) β
      = GrOperad.Inv.star K _ (dInv K V) β + GrOperad.Inv.star K _ β (dInv K V) := by
  refine (invEquiv (K := K) (Q := EndGr K V)).injective (funext fun n => ?_)
  exact d_famOf β hβ n

/-- The family of the differential squares to zero. -/
theorem star_dInv_self : GrOperad.Inv.star K _ (dInv K V) (dInv K V) = 0 := by
  refine (invEquiv (K := K) (Q := EndGr K V)).injective (funext fun n => ?_)
  exact star_dInv_dInv n

/-! ## Twisting morphisms out of a cooperad of alternating lines -/

section Gen

variable {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (C A)] [GrCooperad K C]
  [GrCooperad.Coaug K C] {ν : ∀ n : ℕ, C (Fin (n + 1))}
  (ψ : GrCooperadHom K C (OrdCo K))

variable (V) in
/-- **The family of the differential** on a cooperad over the signed linear orders. -/
noncomputable def delta : GrOperad.Inv K (ConvOp K C (EndGr K V)) :=
  GrOperad.Inv.appHom (ConvOp.preHom ψ) (dInv K V)

omit [GrCooperad.Coaug K C] in
lemma isPar_delta : GrOperad.Inv.IsPar true (delta V ψ) := fun A _ _ =>
  ((ConvOp.preHom (P := EndGr K V) ψ).app_par true _).symm.trans (congrArg _ (isPar_dInv A))

omit [GrCooperad.Coaug K C] in
theorem star_delta : GrOperad.Inv.star K _ (delta V ψ) (delta V ψ) = 0 :=
  (GrOperad.Inv.appHom_star (ConvOp.preHom ψ) (dInv K V) (dInv K V)).symm.trans (by
    rw [star_dInv_self, map_zero])

omit [GrCooperad.Coaug K C] in
lemma lam_delta (hψ : ∀ n, ψ.app (Fin (n + 1)) (ν n) = LieDual.alt K n) (n : ℕ) :
    AltGen.lam ν (delta V ψ) n = famOf (dInv K V) n := by
  rw [delta, AltGen.lam_appHom ψ hψ]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    rw [Fintype.sum_subsingleton _ (1 : Equiv.Perm (Fin (0 + 1))), Equiv.Perm.sign_one]
    show (((1 : ℤˣ) : ℤ) : K) • GrOperad.map (R := K) (Equiv.refl _) (famOf (dInv K V) 0) = _
    rw [GrOperad.map_refl]
    simp
  · rw [famOf_dInv_ne hn.ne']
    simp

omit [GrCooperad.Coaug K C] in
lemma lam_add_delta (hψ : ∀ n, ψ.app (Fin (n + 1)) (ν n) = LieDual.alt K n)
    (α : GrOperad.Inv K (ConvOp K C (EndGr K V))) (n : ℕ) :
    AltGen.lam ν (α + delta V ψ) n = AltGen.lam ν α n + famOf (dInv K V) n := by
  rw [← lam_delta ψ hψ n]
  rfl

/-- The family of operations of every arity of an invariant family: the family in the bar
convention of its operations on the signed linear orders, with the differential added. -/
noncomputable def toL (ν : ∀ n : ℕ, C (Fin (n + 1)))
    (α : GrOperad.Inv K (ConvOp K C (EndGr K V))) : LInf.LFam K V :=
  lfam K V (barFam (ofFam (K := K) (AltGen.lam ν (α + delta V ψ))))

variable [CharZero K] (H : AltGen K C ν)
  (hψ : ∀ n, ψ.app (Fin (n + 1)) (ν n) = LieDual.alt K n)

include H hψ

/-- **The differential of an odd family is its convolution commutator with the family of the
differential.** -/
theorem appDer_eq_gen (α : GrOperad.Inv K (ConvOp K C (EndGr K V)))
    (hα : GrOperad.Inv.IsPar true α) :
    GrOperad.Inv.appDer (ConvOp.postDer (C := C) (DGOperad.toDer (R := K) (P := EndGr K V))) α
      = GrOperad.Inv.star K _ (delta V ψ) α + GrOperad.Inv.star K _ α (delta V ψ) := by
  obtain ⟨β, hβdef⟩ : ∃ β : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)),
      β = ofFam (K := K) fun n => ((n + 1).factorial : K)⁻¹ • AltGen.lam ν α n := ⟨_, rfl⟩
  have hres : GrOperad.Inv.appHom (ConvOp.preHom ψ) β = α := H.inv_ext fun n => by
    rw [hβdef]
    exact congrFun (AltGen.exists_lam ψ hψ (AltGen.lam ν α) (H.map_lam α)) n
  have hβ : GrOperad.Inv.IsPar true β := (OrdCo.isPar_iff β).2 fun n => by
    rw [hβdef, AltGen.famOf_ofFam, LinearMap.map_smul, (H.isPar_iff α).1 hα n]
  have h := congrArg (GrOperad.Inv.appHom (ConvOp.preHom (P := EndGr K V) ψ)) (appDer_eq β hβ)
  subst hres
  rw [map_add, GrOperad.Inv.appHom_star, GrOperad.Inv.appHom_star] at h
  exact h

/-- **The Maurer–Cartan equation is a convolution square**: that of the family with the family
of the differential added. -/
theorem mc_iff_star (α : GrOperad.Inv K (ConvOp K C (EndGr K V)))
    (hα : GrOperad.Inv.IsPar true α) :
    GrOperad.Inv.appDer (ConvOp.postDer (C := C) (DGOperad.toDer (R := K) (P := EndGr K V))) α
        + GrOperad.Inv.star K _ α α = 0
      ↔ GrOperad.Inv.star K _ (α + delta V ψ) (α + delta V ψ) = 0 := by
  have h : GrOperad.Inv.star K _ (α + delta V ψ) (α + delta V ψ)
      = (GrOperad.Inv.star K _ α α + GrOperad.Inv.star K _ α (delta V ψ))
        + (GrOperad.Inv.star K _ (delta V ψ) α
          + GrOperad.Inv.star K _ (delta V ψ) (delta V ψ)) := by
    simp only [map_add, LinearMap.add_apply]
    abel
  rw [h, star_delta ψ, add_zero, appDer_eq_gen ψ H hψ α hα]
  constructor <;> intro h' <;> rw [← h'] <;> abel

omit [DGSuperMod K V] [CharZero K] hψ in
/-- **The convolution square of an odd family vanishes** iff the generalized Jacobi expressions
of its operations in the bar convention vanish on homogeneous inputs. -/
theorem star_eq_zero_iff (α' : GrOperad.Inv K (ConvOp K C (EndGr K V)))
    (hα' : GrOperad.Inv.IsPar true α') :
    GrOperad.Inv.star K _ α' α' = 0
      ↔ ∀ (n : ℕ) (c : Fin (n + 1) → Bool) (x : Fin (n + 1) → V), IsHom (R := K) c x →
          LInf.jac (lfam K V (barFam (ofFam (K := K) (AltGen.lam ν α'))))
            (fun a => !c a) x = 0 := by
  obtain ⟨γ, hγdef⟩ : ∃ γ : GrOperad.Inv K (ConvOp K (OrdCo K) (EndGr K V)),
      γ = ofFam (K := K) (AltGen.lam ν α') := ⟨_, rfl⟩
  rw [← hγdef]
  have hγ : GrOperad.Inv.IsPar true γ := (OrdCo.isPar_iff γ).2 fun n => by
    rw [hγdef, AltGen.famOf_ofFam]
    exact (H.isPar_iff α').1 hα' n
  have key : ∀ n, ConvOp.toLin ((GrOperad.Inv.star K _ α' α').1 (Fin (n + 1))) (ν n)
      = ∑ S ∈ nonempties (Fin (n + 1)), ((Equiv.Perm.sign (unsh S) : ℤ) : K) •
          GrOperad.map (R := K) (unsh S) (NOrd.plTN γ γ (n + 1) (n + 1 - S.card, 0)) := fun n => by
    rw [hγdef]
    exact H.star_nu α' α' hα' n unsh map_ini_unsh
  constructor
  · intro h n c x hx
    have h0 : ConvOp.toLin ((0 : GrOperad.Inv K (ConvOp K C (EndGr K V))).1 (Fin (n + 1))) (ν n)
        = 0 := rfl
    rw [← dec_sv_sum γ hγ n hx, ← key n, h, h0]
    show dec (n + 1) 0 x = 0
    rw [LinearMap.map_zero]
    rfl
  · intro h
    refine H.inv_ext (α' := 0) fun n => ?_
    show ConvOp.toLin ((GrOperad.Inv.star K _ α' α').1 (Fin (n + 1))) (ν n) = 0
    rw [key n]
    refine (EndGr.eq_zero_iff_sv _).2 (dec_eq_zero (ext_hom fun c x hx => ?_))
    rw [dec_sv_sum γ hγ n hx, h n c x hx]
    rfl

/-! ## Parity, units and symmetry of the operations of every arity -/

omit hψ in
/-- **An invariant family is odd** iff its operations of every arity are odd for the opposite
sign involution. -/
theorem isPar_iff_toL (α : GrOperad.Inv K (ConvOp K C (EndGr K V))) :
    GrOperad.Inv.IsPar true α ↔ ∀ k, End.IsHomog (-eps K V) 1 (toL ψ ν α k) := by
  have h1 : GrOperad.Inv.IsPar true α ↔ GrOperad.Inv.IsPar true (α + delta V ψ) :=
    ⟨fun h A _ _ => by
      show GrOperad.par (R := K) true (α.1 A + (delta V ψ).1 A) = α.1 A + (delta V ψ).1 A
      rw [map_add, h A, isPar_delta ψ A],
     fun h A _ _ => by
      have h2 : α.1 A = (α + delta V ψ).1 A - (delta V ψ).1 A := (add_sub_cancel_right _ _).symm
      rw [h2, map_sub, h A, isPar_delta ψ A]⟩
  have h2 : GrOperad.Inv.IsPar true (α + delta V ψ)
      ↔ GrOperad.Inv.IsPar true (ofFam (K := K) (AltGen.lam ν (α + delta V ψ))) := by
    rw [H.isPar_iff, OrdCo.isPar_iff]
    exact forall_congr' fun n => by rw [AltGen.famOf_ofFam]
  rw [h1, h2, isPar_iff_barFam]
  constructor
  · intro h k
    cases k with
    | zero => exact fun v => by simp [toL, lfam]
    | succ k => exact h k
  · exact fun h n => h (n + 1)

omit H [CharZero K] [GrCooperad.Coaug K C] in
/-- The operation of arity one is that of the family, plus the differential. -/
theorem toL_one (α : GrOperad.Inv K (ConvOp K C (EndGr K V))) (v : Fin 1 → V) :
    toL ψ ν α 1 v = EndGr.sv (AltGen.lam ν α 0) v + DGSuperMod.d (R := K) (v 0) := by
  show dec 1 (EndGr.sv (famOf (ofFam (K := K) (AltGen.lam ν (α + delta V ψ))) 0)) v = _
  rw [dec_one, AltGen.famOf_ofFam, lam_add_delta ψ hψ, famOf_dInv_zero, EndGr.sv_add,
    MultilinearMap.add_apply, sv_D1]

omit [CharZero K] in
/-- **An invariant family kills the coaugmentation** iff its operation of arity one, with the
differential added, is the differential. -/
theorem killsUnit_iff_toL (α : GrOperad.Inv K (ConvOp K C (EndGr K V))) :
    KillsUnit K C (EndGr K V) α
      ↔ ∀ v : Fin 1 → V, toL ψ ν α 1 v = DGSuperMod.d (R := K) (v 0) := by
  rw [H.killsUnit_iff]
  constructor
  · intro h v
    rw [toL_one ψ hψ, h]
    exact zero_add _
  · intro h
    refine (EndGr.eq_zero_iff_sv _).2 (MultilinearMap.ext fun v => ?_)
    have h1 := h v
    rw [toL_one ψ hψ] at h1
    exact add_eq_right.1 h1

omit hψ in
/-- **The operations of every arity of an invariant family are graded symmetric.** -/
theorem toL_symm (α : GrOperad.Inv K (ConvOp K C (EndGr K V))) (k : ℕ) (p : Fin k → Bool)
    (v : Fin k → V) (hv : ∀ a, IsPar (-eps K V) (p a) (v a)) (i : ℕ) (h : i + 1 < k) :
    toL ψ ν α k (v ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩)
      = σ K (p ⟨i, by omega⟩ && p ⟨i + 1, h⟩) • toL ψ ν α k v := by
  cases k with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ n =>
    have hG : ∀ τ : Equiv.Perm (Fin (n + 1)),
        GrOperad.map (R := K) τ (famOf (ofFam (K := K) (AltGen.lam ν (α + delta V ψ))) n)
          = ((Equiv.Perm.sign τ : ℤ) : K) •
            famOf (ofFam (K := K) (AltGen.lam ν (α + delta V ψ))) n := fun τ => by
      rw [AltGen.famOf_ofFam]
      exact H.map_lam (α + delta V ψ) n τ
    have hx : IsHom (R := K) (fun a => !p a) v := fun a => isHom_of_isPar (hv a)
    have key := dec_symm hG (Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩) hx
    rw [ks_swap] at key
    simp only [Bool.not_not] at key
    have key' : σ K (p ⟨i, by omega⟩ && p ⟨i + 1, h⟩) •
        barFam (ofFam (K := K) (AltGen.lam ν (α + delta V ψ))) n
          (v ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩)
        = barFam (ofFam (K := K) (AltGen.lam ν (α + delta V ψ))) n v := key
    show barFam (ofFam (K := K) (AltGen.lam ν (α + delta V ψ))) n
        (v ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩)
      = σ K (p ⟨i, by omega⟩ && p ⟨i + 1, h⟩) •
        barFam (ofFam (K := K) (AltGen.lam ν (α + delta V ψ))) n v
    rw [← key', smul_smul, LInf.σ_mul_self, one_smul]

/-- **Twisting morphisms are `L∞`-structures**: an invariant family is odd, kills the
coaugmentation and satisfies the Maurer–Cartan equation iff its operations of every arity, with
the differential added in arity one, are an `L∞`-structure in the bar convention for the opposite
sign involution, whose first operation is the differential. -/
theorem isLInf_iff (α : GrOperad.Inv K (ConvOp K C (EndGr K V))) :
    (GrOperad.Inv.IsPar true α ∧ KillsUnit K C (EndGr K V) α ∧
        GrOperad.Inv.appDer (ConvOp.postDer (C := C) (DGOperad.toDer (R := K) (P := EndGr K V)))
          α + GrOperad.Inv.star K _ α α = 0)
      ↔ (LInf.IsLInf (-eps K V) (toL ψ ν α)
          ∧ ∀ v : Fin 1 → V, toL ψ ν α 1 v = DGSuperMod.d (R := K) (v 0)) := by
  have hpar : GrOperad.Inv.IsPar true α → GrOperad.Inv.IsPar true (α + delta V ψ) :=
    fun h A _ _ => by
      show GrOperad.par (R := K) true (α.1 A + (delta V ψ).1 A) = α.1 A + (delta V ψ).1 A
      rw [map_add, h A, isPar_delta ψ A]
  constructor
  · rintro ⟨hα, hu, hmc⟩
    refine ⟨⟨(isPar_iff_toL ψ H α).1 hα, fun k p v hv i h => toL_symm ψ H α k p v hv i h, ?_⟩,
      (killsUnit_iff_toL ψ H hψ α).1 hu⟩
    intro n p v hv
    cases n with
    | zero => exact LInf.jac_zero _ p v
    | succ n =>
      have hx : IsHom (R := K) (fun a => !p a) v := fun a => isHom_of_isPar (hv a)
      have h := (star_eq_zero_iff H (α + delta V ψ) (hpar hα)).1
        ((mc_iff_star ψ H hψ α hα).1 hmc) n _ v hx
      simp only [Bool.not_not] at h
      exact h
  · rintro ⟨hL, hd⟩
    have hα := (isPar_iff_toL ψ H α).2 hL.odd
    exact ⟨hα, (killsUnit_iff_toL ψ H hψ α).2 hd, (mc_iff_star ψ H hψ α hα).2
      ((star_eq_zero_iff H _ (hpar hα)).2 fun n c x hx =>
        hL.jac (n + 1) _ x fun a => isPar_of_isHom (hx a))⟩

/-! ## The equivalence -/

omit H hψ [CharZero K] [GrCooperad K C] [GrCooperad.Coaug K C] in
variable (K V) in
/-- **The `L∞`-structures of a dg super module**: the `L∞`-structures in the bar convention, for
the opposite sign involution, with no operation of arity zero, whose first operation is the
differential. -/
def LInfOver : Type v :=
  {ℓ : LInf.LFam K V // LInf.IsLInf (-eps K V) ℓ ∧ ℓ 0 = 0 ∧
    ∀ v : Fin 1 → V, ℓ 1 v = DGSuperMod.d (R := K) (v 0)}

omit H hψ [CharZero K] in
/-- **The operations of an `L∞`-structure, as operations of the endomorphism operad**: the
décalages, with the differential removed in arity one. -/
noncomputable def ofL (ℓ : LInf.LFam K V) (n : ℕ) : EndGr K V (Fin (n + 1)) :=
  hatFam (fun k => ℓ (k + 1)) n - famOf (dInv K V) n

omit H hψ [CharZero K] in
lemma map_famOf_dInv (n : ℕ) (τ : Equiv.Perm (Fin (n + 1))) :
    GrOperad.map (R := K) τ (famOf (dInv K V) n)
      = ((Equiv.Perm.sign τ : ℤ) : K) • famOf (dInv K V) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    rw [Subsingleton.elim τ 1, Equiv.Perm.sign_one]
    show GrOperad.map (R := K) (Equiv.refl _) _ = _
    rw [GrOperad.map_refl]
    simp
  · rw [famOf_dInv_ne hn.ne', LinearMap.map_zero, smul_zero]

omit H hψ [CharZero K] in
/-- **The operations of an `L∞`-structure alternate**, as operations of the endomorphism
operad. -/
lemma map_ofL {ℓ : LInf.LFam K V} (hℓ : LInf.IsLInf (-eps K V) ℓ) (n : ℕ)
    (τ : Equiv.Perm (Fin (n + 1))) :
    GrOperad.map (R := K) τ (ofL ℓ n) = ((Equiv.Perm.sign τ : ℤ) : K) • ofL ℓ n := by
  rw [ofL, map_sub, smul_sub, map_famOf_dInv]
  congr 1
  refine map_of_dec_symm (fun i h c x hx => ?_) τ
  have hd : dec (n + 1) (EndGr.sv (hatFam (fun k => ℓ (k + 1)) n)) = ℓ (n + 1) := by
    show dec (n + 1) ((EndGr.ofFam (LinOrd.std (n + 1)) (dec (n + 1) (ℓ (n + 1)))).fam
      (LinOrd.std (n + 1))) = _
    rw [EndGr.ofFam_fam, dec_dec]
  rw [hd]
  exact hℓ.symm (n + 1) (fun a => !c a) x (fun a => isPar_of_isHom (hx a)) i h

omit H hψ [CharZero K] in
/-- The invariant family of an `L∞`-structure. -/
noncomputable def ofLInv (ℓ : LInf.LFam K V) : GrOperad.Inv K (ConvOp K C (EndGr K V)) :=
  GrOperad.Inv.appHom (ConvOp.preHom ψ)
    (ofFam (K := K) fun n => ((n + 1).factorial : K)⁻¹ • ofL ℓ n)

omit H [GrCooperad.Coaug K C] in
theorem toL_ofLInv {ℓ : LInf.LFam K V} (hℓ : LInf.IsLInf (-eps K V) ℓ) (h0 : ℓ 0 = 0) :
    toL ψ ν (ofLInv ψ ℓ) = ℓ := by
  have hlam : AltGen.lam ν (ofLInv ψ ℓ) = ofL ℓ :=
    AltGen.exists_lam ψ hψ (ofL ℓ) (map_ofL hℓ)
  have hfam : ofFam (K := K) (AltGen.lam ν (ofLInv ψ ℓ + delta V ψ))
      = ofFam (K := K) (hatFam fun k => ℓ (k + 1)) := by
    refine congrArg _ (funext fun n => ?_)
    rw [lam_add_delta ψ hψ, hlam, ofL, sub_add_cancel]
  funext k
  cases k with
  | zero => exact h0.symm
  | succ k =>
    show barFam (ofFam (K := K) (AltGen.lam ν (ofLInv ψ ℓ + delta V ψ))) k = ℓ (k + 1)
    rw [hfam, barFam_ofFam_hatFam]

/-- **Twisting morphisms from a cooperad of alternating lines over the signed linear orders to
the endomorphism operad of a dg super module are its `L∞`-structures.** -/
noncomputable def twistingEquiv : Twisting K C (EndGr K V) ≃ LInfOver K V where
  toFun α := ⟨toL ψ ν α.1, ((isLInf_iff ψ H hψ α.1).1 ⟨α.2.1, α.2.2.1, α.2.2.2⟩).1, rfl,
    ((isLInf_iff ψ H hψ α.1).1 ⟨α.2.1, α.2.2.1, α.2.2.2⟩).2⟩
  invFun ℓ := ⟨ofLInv ψ ℓ.1, (isLInf_iff ψ H hψ _).2 (by
    rw [toL_ofLInv ψ hψ ℓ.2.1 ℓ.2.2.1]
    exact ⟨ℓ.2.1, ℓ.2.2.2⟩)⟩
  left_inv α := Subtype.ext (H.inv_ext fun n => by
    have hL := ((isLInf_iff ψ H hψ α.1).1 ⟨α.2.1, α.2.2.1, α.2.2.2⟩).1
    have h1 : AltGen.lam ν (ofLInv ψ (toL ψ ν α.1)) n = ofL (toL ψ ν α.1) n :=
      congrFun (AltGen.exists_lam ψ hψ (ofL (toL ψ ν α.1)) (map_ofL hL)) n
    have h2 := congrFun (congrArg famOf (ofFam_hatFam_barFam
      (ofFam (K := K) (AltGen.lam ν (α.1 + delta V ψ))))) n
    rw [AltGen.famOf_ofFam, AltGen.famOf_ofFam, lam_add_delta ψ hψ] at h2
    refine h1.trans ?_
    show hatFam (barFam (ofFam (K := K) (AltGen.lam ν (α.1 + delta V ψ)))) n
      - famOf (dInv K V) n = AltGen.lam ν α.1 n
    rw [h2, add_sub_cancel_right])
  right_inv ℓ := Subtype.ext (toL_ofLInv ψ hψ ℓ.2.1 ℓ.2.2.1)

end Gen

/-- **`Lie∞`-algebras are `L∞`-algebras**: over a field of characteristic zero, the homotopy
algebras over the Koszul dual cooperad of the presentation of `Lie`, on a dg super module `V`,
are the `L∞`-structures on `V` in the bar convention, for the opposite sign involution, with no
operation of arity zero, whose first operation is the differential. -/
noncomputable def pinfEquiv [CharZero K] :
    Koszul.PInfAlgebra K (SymPresComLie.ELie K) (SymPresComLie.rLie K) V ≃ LInfOver K V :=
  HoAlgebra.equivTwisting.trans
    (twistingEquiv (LieDual.toOrd K) LieDual.altGen LieDual.toOrd_nu)

end PInfLie

end Operad
