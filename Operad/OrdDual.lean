/-
# The Koszul dual cooperad of `Ass` is the cooperad of signed linear orders

Over a field `K` of characteristic zero, **the comparison `OrdCo.toDual : OrdCo K → Ass^¡` is
bijective in every arity** (`OrdCo.toDual_bijective`, `OrdCo.dualEquiv`), where `Ass^¡` is the
Koszul dual cooperad `Koszul.Dual K E r` of the presentation of `Ass` of
`Operad/SymPresAss.lean`.

* **Injectivity** (`OrdCo.toCut_injective`). The decomposition of `OrdCo K` is the transpose of
  the composition of orders, so the coefficient of a composite order vanishes on an element
  killed by `toCut` when `toCut` is injective on the two factors
  (`OrdCo.coeff_eq_zero_of_fact`); an order on at least three inputs is a composite, the orders
  on two inputs are read by the coefficient of the generators, and the order on one input by the
  counit.
* **Surjectivity**, by dimensions: there are `n!` orders on `n ≥ 1` inputs
  (`OrdCo.finrank_ordCo`), and `dim Ass^¡(Fin n) ≤ n!` for `n ≥ 2` by
  `ShuffleBarSym.finrank_dual_le` and the dimension `n!` of the Koszul dual operad of `Ass` on
  the shuffle side (`AssBin.finrank_quotient_dualRel`). In arity one `Ass^¡` lies in the span of
  the unit, and in arity zero it vanishes.
* **Coaugmentations** (`OrdCo.toCut_one`, `OrdCo.toDual_one`), and hence **twisting morphisms**
  (`OrdCo.twEquiv`): the twisting morphisms `Ass^¡ → Q` are the twisting morphisms
  `OrdCo K → Q`, for every dg operad `Q`.
-/
import Operad.OrdCut
import Operad.KoszulDualKD
import Operad.ShuffleKoszulDuals
import Operad.KoszulCriterion
import Operad.CutCobar
import Operad.TwistingIso

universe u w

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace OrdCo

variable (K : Type u) [Field K] [CharZero K] {A A' B : Type} [Fintype A] [DecidableEq A]
  [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B]

omit [CharZero K] in
lemma σ_ne_zero (b : Bool) : σ K b ≠ 0 := by cases b <;> simp

/-- **The coefficient of a composite order vanishes** on an element killed by `toCut`, when
`toCut` is injective on the two factors: the decomposition is the transpose of the composition. -/
lemma coeff_eq_zero_of_fact (i : A') (e : Without A' i ⊕ B ≃ A) (p : NOrd A') (q : NOrd B)
    (hA' : Function.Injective ((toCut K).app A')) (hB : Function.Injective ((toCut K).app B))
    {y : OrdCo K A} (hy : (toCut K).app A y = 0) :
    (show NOrd A →₀ K from y) (SetOperad.map e (SetOperad.comp i p q)) = 0 := by
  have hx : (toCut K).app _ (SymSpecies.map (R := K) e.symm y) = 0 := by
    rw [(toCut K).app_map, hy, map_zero]
  have hd : GrCooperad.decomp (R := K) (C := OrdCo K) (B := B) i
      (SymSpecies.map (R := K) e.symm y) = 0 := by
    have h1 := LinearMap.congr_fun ((toCut K).decomp_app (B := B) i)
      (SymSpecies.map (R := K) e.symm y)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hx, map_zero] at h1
    exact TensorProduct.map_injective_of_flat_flat _ _ hA' hB (h1.symm.trans (map_zero _).symm)
  have h2 := SgnLin.decompT_apply (R := K) (δ := NOrd.sgnD) i
    (SymSpecies.map (R := K) e.symm y) (p, q)
  rw [show SgnLin.decompT K NOrd.sgnD i (SymSpecies.map (R := K) e.symm y) = 0 from hd,
    map_zero] at h2
  have h3 : (show NOrd _ →₀ K from SymSpecies.map (R := K) e.symm y) (SetOperad.comp i p q)
      = 0 := (mul_eq_zero.1 h2.symm).resolve_left (σ_ne_zero K _)
  rw [← h3]
  show _ = Lin.mapL K e.symm y (SetOperad.comp i p q)
  rw [Lin.mapL_apply, Equiv.symm_symm]

/-- **The signed linear orders embed in the cut cooperad.** -/
theorem toCut_injective : ∀ (n : ℕ) (A : Type) [Fintype A] [DecidableEq A],
    Fintype.card A = n → Function.Injective ((toCut K).app A) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ _ hA
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    refine Finsupp.ext fun L => ?_
    show (show NOrd A →₀ K from y) L = 0
    obtain ⟨a₀⟩ := L.2
    have hpos : 0 < n := hA ▸ Fintype.card_pos_iff.2 ⟨a₀⟩
    obtain ⟨e₀, he₀⟩ := LinOrd.exists_map_eq (LinOrd.std n) L.1
      ((Fintype.card_fin n).trans hA.symm)
    have hL : L = SetOperad.map e₀ (NOrd.std n hpos) := Subtype.ext he₀.symm
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · -- one input: the counit
        let e₁ : Unit ≃ A := (Equiv.ofUnique Unit (Fin 1)).trans e₀
        haveI : Subsingleton A := e₁.symm.subsingleton
        have hc := LinearMap.congr_fun (toCut K).counit_app (SymSpecies.map (R := K) e₁.symm y)
        rw [LinearMap.comp_apply, (toCut K).app_map, hy, map_zero, map_zero] at hc
        have h1 : Lin.mapL K e₁.symm y (SetOperad.one : NOrd Unit) = 0 := hc.symm
        rw [Lin.mapL_apply, Equiv.symm_symm] at h1
        exact (congrArg (show NOrd A →₀ K from y)
          (Subtype.ext (LinOrd.eq_of_subsingleton _ _))).trans h1
      · -- two inputs: the coefficient of the generators
        have hg := genCoef_toCut K y
        rw [hy, map_zero] at hg
        have h1 := congrFun (show ((gen K).app A y : (Fin 2 ≃ A) → K) = 0 from hg.symm) e₀
        rw [hL]
        exact h1
    · -- at least three inputs: a factorization
      have hfact : NOrd.std n hpos = SetOperad.map
          (posEquivF (⟨0, by omega⟩ : Fin (n - 1)) 2 n (by omega))
          (SetOperad.comp (⟨0, by omega⟩ : Fin (n - 1)) (NOrd.std (n - 1) (by omega))
            (NOrd.std 2 (by decide))) :=
        (Subtype.ext (map_posEquivF _ _)).symm
      rw [hL, hfact, ← SetOperad.map_trans]
      exact coeff_eq_zero_of_fact K _ _ _ _
        (ih (n - 1) (by omega) _ (Fintype.card_fin _)) (ih 2 (by omega) _ (Fintype.card_fin _)) hy

/-! ## The dimensions -/

local notation "𝔼" => SymPresB.Reg2 K
local notation "𝔻" => Koszul.dualSub K (SymPresB.Reg2 K) (SymPresAss.rel K)

omit [CharZero K] in
/-- **There are `n!` signed linear orders on `n ≥ 1` inputs.** -/
lemma finrank_ordCo {n : ℕ} (hn : 1 ≤ n) : Module.finrank K (OrdCo K (Fin n)) = n.factorial := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : Fintype (NOrd (Fin n)) := Fintype.ofFinite _
  have h1 : Module.finrank K (NOrd (Fin n) →₀ K) = Fintype.card (NOrd (Fin n)) :=
    Module.finrank_finsupp_self K
  have h2 : Fintype.card (NOrd (Fin n)) = n.factorial :=
    Nat.card_eq_fintype_card.symm.trans ((Nat.card_congr (Equiv.subtypeUnivEquiv
      fun _ : LinOrd (Fin n) => (inferInstance : Nonempty (Fin n)))).trans
        (LinOrd.card.trans (by rw [Fintype.card_fin])))
  exact h1.trans h2

/-- **The signed linear orders embed in the Koszul dual cooperad of `Ass`.** -/
lemma toDual_injective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective ((toDual K).app A) := fun _ _ h =>
  toCut_injective K _ A rfl (congrArg ((𝔻).incl A) h)

/-- **In every arity `n`, the Koszul dual cooperad of `Ass` is the space of signed linear
orders**: the comparison is injective, and the Koszul dual cooperad has at most `n!` dimensions,
those of the top homology of the shuffle bar complex of `Ass`. -/
theorem toDual_bijective_fin (n : ℕ) : Function.Bijective ((toDual K).app (Fin n)) := by
  refine ⟨toDual_injective K (Fin n), ?_⟩
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · interval_cases n
    · -- no inputs
      intro y
      have hy : y = 0 := (𝔻).incl_injective _
        ((CutCobar.eq_zero_of_isEmpty (fun v => shift_eq_zero K (by simp) v) _).trans
          (map_zero _).symm)
      exact ⟨0, (map_zero _).trans hy.symm⟩
    · -- one input: the relabellings of the unit
      obtain ⟨u, hu⟩ : ∃ u : Koszul.Cut K 𝔼 (Fin 1),
          GrCooperad.unitSpan K (Koszul.Cut K 𝔼) (Fin 1) ≤ K ∙ u := by
        refine ⟨SymSpecies.map (R := K) (Equiv.ofUnique Unit (Fin 1))
          (GrCooperad.Coaug.one (R := K) (C := Koszul.Cut K 𝔼)), Submodule.span_le.2 ?_⟩
        rintro _ ⟨e, rfl⟩
        rw [Subsingleton.elim e (Equiv.ofUnique Unit (Fin 1))]
        exact Submodule.mem_span_singleton_self _
      have hmem : ∀ y : Koszul.Dual K 𝔼 (SymPresAss.rel K) (Fin 1),
          (𝔻).incl (Fin 1) y ∈ K ∙ u := fun y =>
        hu (FreeGrL.mem_unitSpan_of_card_le (R := K) (V := GrSpecies.Shift 𝔼 K) (hred K)
          (A := Fin 1) (by simp) _)
      obtain ⟨f, hf⟩ : ∃ f : Koszul.Dual K 𝔼 (SymPresAss.rel K) (Fin 1) →ₗ[K] (K ∙ u),
          ∀ y, (f y).1 = (𝔻).incl (Fin 1) y :=
        ⟨((𝔻).incl (Fin 1)).codRestrict _ hmem, fun _ => rfl⟩
      have hfinj : Function.Injective f := fun x y h =>
        (𝔻).incl_injective _ ((hf x).symm.trans ((congrArg Subtype.val h).trans (hf y)))
      have h1 : Module.finrank K (K ∙ u) ≤ 1 :=
        finrank_le_one (⟨u, Submodule.mem_span_singleton_self u⟩ : K ∙ u) fun w => by
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 w.2
          exact ⟨a, Subtype.ext ha⟩
      haveI : IsNoetherian K (K ∙ u) := isNoetherian_of_isNoetherianRing_of_finite K (K ∙ u)
      haveI : Module.Finite K (Koszul.Dual K 𝔼 (SymPresAss.rel K) (Fin 1)) :=
        Module.Finite.of_injective f hfinj
      haveI : Module.Finite K (OrdCo K (Fin 1)) := Module.finite_of_finrank_pos (by
        rw [finrank_ordCo K le_rfl]
        decide)
      have heq : Module.finrank K (OrdCo K (Fin 1))
          = Module.finrank K (Koszul.Dual K 𝔼 (SymPresAss.rel K) (Fin 1)) :=
        le_antisymm (LinearMap.finrank_le_finrank_of_injective (toDual_injective K (Fin 1))) (by
          rw [finrank_ordCo K le_rfl]
          exact (LinearMap.finrank_le_finrank_of_injective hfinj).trans h1)
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1
        (toDual_injective K (Fin 1))
  · have hKD : Module.finrank K (ShuffleBar.KD K (ShuffleBarSym.Rsh (SymPresAss.c K)
        (SymPresAss.hc K) (SymPresAss.rel K)) n) = n.factorial := by
      rw [SymPresAss.Rsh_eq]
      exact (ShuffleBar.finrank_quotient_dualRel (AssBin.rel K) h2).symm.trans
        (AssBin.finrank_quotient_dualRel K (by omega))
    haveI : FiniteDimensional K (ShuffleBar.KD K (ShuffleBarSym.Rsh (SymPresAss.c K)
        (SymPresAss.hc K) (SymPresAss.rel K)) n) :=
      haveI : Module.Free K (ShuffleBar.KD K (ShuffleBarSym.Rsh (SymPresAss.c K)
          (SymPresAss.hc K) (SymPresAss.rel K)) n) :=
        Module.Free.of_divisionRing K (ShuffleBar.KD K (ShuffleBarSym.Rsh (SymPresAss.c K)
          (SymPresAss.hc K) (SymPresAss.rel K)) n)
      Module.finite_of_finrank_pos (by
        rw [hKD]
        exact Nat.factorial_pos n)
    obtain ⟨hfin, hle⟩ := ShuffleBarSym.finrank_dual_le (SymPresAss.c K) (SymPresAss.hc K)
      (SymPresAss.rel K) (fun m hm => SymPresB.kerRel_ne (SymPresAss.φ K) hm)
      (fun σ x hx => SymPresB.kerRel_perm (SymPresAss.φ K) σ x hx) h2
    haveI := hfin
    haveI : Module.Finite K (OrdCo K (Fin n)) := Module.finite_of_finrank_pos (by
      rw [finrank_ordCo K (by omega)]
      exact Nat.factorial_pos n)
    have heq : Module.finrank K (OrdCo K (Fin n))
        = Module.finrank K (Koszul.Dual K 𝔼 (SymPresAss.rel K) (Fin n)) :=
      le_antisymm (LinearMap.finrank_le_finrank_of_injective (toDual_injective K (Fin n))) (by
        rw [finrank_ordCo K (by omega), ← hKD]
        exact hle)
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1
      (toDual_injective K (Fin n))

/-- **The Koszul dual cooperad of `Ass` is the cooperad of signed linear orders**: the
comparison `toDual` is bijective in every arity. -/
theorem toDual_bijective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Bijective ((toDual K).app A) := by
  refine ⟨toDual_injective K A, fun y => ?_⟩
  obtain ⟨x, hx⟩ := (toDual_bijective_fin K (Fintype.card A)).2
    (SymSpecies.map (R := K) (Fintype.equivFin A) y)
  refine ⟨SymSpecies.map (R := K) (Fintype.equivFin A).symm x, ?_⟩
  rw [(toDual K).app_map, hx, SymSpecies.map_symm_map]

/-- The signed linear orders and the Koszul dual cooperad of `Ass`, arity by arity. -/
noncomputable def dualEquiv (A : Type) [Fintype A] [DecidableEq A] :
    OrdCo K A ≃ₗ[K] Koszul.Dual K 𝔼 (SymPresAss.rel K) A :=
  LinearEquiv.ofBijective ((toDual K).app A) (toDual_bijective K A)

/-! ## The coaugmentations, and twisting morphisms -/

/-- **The signed linear orders are coaugmented over the cut cooperad**: `toCut` sends the order
on one input to the trivial tree. -/
theorem toCut_one :
    (toCut K).app Unit (GrCooperad.Coaug.one (R := K) (C := OrdCo K))
      = GrCooperad.Coaug.one (R := K) (C := Koszul.Cut K 𝔼) := by
  have hmem := FreeGrL.mem_unitSpan_of_card_le (R := K) (V := GrSpecies.Shift 𝔼 K) (hred K)
    (A := Unit) (by simp) ((toCut K).app Unit (GrCooperad.Coaug.one (R := K) (C := OrdCo K)))
  have hle : GrCooperad.unitSpan K (Koszul.Cut K 𝔼) Unit
      ≤ K ∙ (GrCooperad.Coaug.one (R := K) (C := Koszul.Cut K 𝔼)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨e, rfl⟩
    rw [Subsingleton.elim e (Equiv.refl Unit)]
    show SymSpecies.map (R := K) (Equiv.refl Unit) _ ∈ _
    rw [SymSpecies.map_refl]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hle hmem)
  have hc := LinearMap.congr_fun (toCut K).counit_app
    (GrCooperad.Coaug.one (R := K) (C := OrdCo K))
  rw [LinearMap.comp_apply, ← ha, map_smul, GrCooperad.Coaug.counit_one,
    GrCooperad.Coaug.counit_one, smul_eq_mul, mul_one] at hc
  rw [← ha, hc, one_smul]

/-- `toDual` preserves the coaugmentations. -/
theorem toDual_one :
    (toDual K).app Unit (GrCooperad.Coaug.one (R := K) (C := OrdCo K))
      = GrCooperad.Coaug.one (R := K) (C := Koszul.Dual K 𝔼 (SymPresAss.rel K)) :=
  Subtype.ext (toCut_one K)

/-- **Twisting morphisms out of the Koszul dual cooperad of `Ass` are twisting morphisms out of
the cooperad of signed linear orders.** -/
noncomputable def twEquiv
    {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (Q A)] [DGOperad K Q] :
    Twisting K (Koszul.Dual K 𝔼 (SymPresAss.rel K)) Q ≃ Twisting K (OrdCo K) Q :=
  Twisting.congr (toDual K) (toDual_bijective K) (toDual_one K)

end OrdCo

end Operad
