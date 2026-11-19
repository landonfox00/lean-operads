/-
# The presented operad of quadratic data on generators of any arity, and the Koszul criterion

Step (2c) of the symmetric–shuffle bridge for generators of any arity, first part; the binary
case is `Operad.ShuffleBarQuot`. Setting as in `Operad.ShuffleAnySym`, with relators
`r n ⊆ T(E) (Fin n)`, `P = Koszul.Pres K E r` and `Ī_P = ShuffleAnySym.Ipres` its ideal of the
operations with at least two inputs.

* **The hypotheses of `Koszul.isKoszul_iff`**: no generators with at most one input
  (`ShuffleAnySym.hEred`), `Ī_P` contains the generators (`ShuffleAnySym.hE_pres`), the units
  complement `Ī_P` (`ShuffleAnySym.hcompl_pres`) and, for quadratic relators
  (`Koszul.IsQuadratic`) over a field of characteristic zero, the unit of `P` is free
  (`ShuffleAnySym.hone_pres`): the ideal of quadratic relators has no trees with fewer than two
  vertices (`ShuffleAnySym.span_le_sup`).
* **The retraction onto the generators**: the coefficient of the generators descends to `P`
  (`ShuffleAnySym.presCoef`) and retracts `sE → sĪ_P` (`ShuffleAnySym.barRet`), so `P^¡ →
  B(P, Ī_P)` is injective (`ShuffleAnySym.dualToBar_injective`).
* **The Koszul criterion**: `P` is Koszul iff `P^¡(n) → B(P, Ī_P)(n)` is a quasi-isomorphism for
  every `n ≥ 2` (`ShuffleAnySym.isKoszul_iff_toBar`, `ShuffleAnySym.isKoszul_iff_toBar_fin`).

For binary generators the arity determines the number of vertices and the criterion reads degree
by degree (`ShuffleBarSym.isKoszul_iff_cycles`); here two gradings are needed, and the criterion
is read in shuffle coordinates in `Operad.ShuffleAnyCrit`.
-/
import Operad.ShuffleAnySymExp
import Operad.ShuffleBarQuot
import Operad.KoszulQuadratic
import Operad.CutLift
import Operad.CofreeVanish

universe u

namespace Operad

open Function Sym GerBV GrComposite STree FreeGr Bar

namespace ShuffleAnySym

open ShuffleBarSym

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))

local notation "𝒥" => GrOperadIdeal.span K r

include c in
/-- **No generators with at most one input**, the hypothesis `hEred` of `Koszul.isKoszul_iff`. -/
lemma hEred (B : Type) [Fintype B] [DecidableEq B] (hB : Fintype.card B ≤ 1) (v : E B) :
    v = 0 := by
  let e : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  haveI : IsEmpty (T (Fintype.card B)) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hB with h | h <;> rw [h] <;> infer_instance
  have h0 : SymSpecies.map (R := K) (V := E) e v = 0 :=
    (c (Fintype.card B)).repr.injective (Subsingleton.elim _ _)
  have := congrArg (SymSpecies.map (R := K) (V := E) e.symm) h0
  rwa [← SymSpecies.map_trans, Equiv.self_trans_symm, SymSpecies.map_refl, map_zero] at this

omit [IsEmpty (T 1)] in
include hc in
/-- **The presented operad vanishes in arity zero.** -/
lemma pres_zero (y : Koszul.Pres K E r (Fin 0)) : y = 0 := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective (Fin 0) y
  rw [free_zero c hc x, map_zero]

variable (K E) in
/-- **The ideal `Ī_P` of the presented operad** of its operations with at least two inputs. -/
noncomputable abbrev Ipres : GrOperadIdeal K (Koszul.Pres K E r) :=
  GrOperadIdeal.atLeastTwo K (Koszul.Pres K E r) (pres_zero c hc r)

include c in
/-- **`Ī_P` contains the generators**, the hypothesis `hE` of `Koszul.toBar`. -/
lemma hE_pres (A : Type) [Fintype A] [DecidableEq A] (v : E A) :
    (𝒥).proj A ((FreeGrL.ι K E).app A v) ∈ (Ipres K E c hc r).sub A := by
  by_cases h : 2 ≤ Fintype.card A
  · rw [GrOperadIdeal.atLeastTwo_sub_of_le h]
    trivial
  · rw [hEred c A (by omega) v, map_zero, map_zero]
    exact zero_mem _

variable [CharZero K]

include c in
/-- In the arities at most one, the free operad is spanned by the relabellings of its unit. -/
lemma mem_units_free {A : Type} [Fintype A] [DecidableEq A] (hA : Fintype.card A ≤ 1)
    (x : FreeGrL K E A) : x ∈ Bar.unitsP (R := K) (FreeGrL K E) A :=
  FreeGrL.mem_unitSpan_of_card_le (R := K) (V := E) (hEred c) hA x

include hc in
/-- **The unit of the free operad is not zero.** -/
lemma one_ne_zero_free : GrOperad.one (R := K) (P := FreeGrL K E) ≠ 0 := by
  intro h0
  have hall : ∀ x : FreeGrL K E (Fin 1), x = 0 := by
    intro x
    have hx := mem_units_free c (by simp) x
    have hbot : Bar.unitsP (R := K) (FreeGrL K E) (Fin 1) = ⊥ := by
      rw [Bar.unitsP, Submodule.span_eq_bot]
      rintro _ ⟨e, rfl⟩
      dsimp only
      rw [h0]
      exact map_zero _
    rw [hbot, Submodule.mem_bot] at hx
    exact hx
  exact (tBasis c hc (Fin 1)).ne_zero ⟨.leaf 0, trivial, by rw [Fintype.card_fin]; rfl⟩ (hall _)

/-- **The units of the presented operad complement `Ī_P`**, the hypothesis `hcompl` of
`Koszul.isKoszul_iff`. -/
lemma hcompl_pres (A : Type) [Fintype A] [DecidableEq A] :
    IsCompl (Bar.unitsP (R := K) (Koszul.Pres K E r) A) ((Ipres K E c hc r).sub A) := by
  by_cases h : 2 ≤ Fintype.card A
  · rw [GrOperadIdeal.atLeastTwo_sub_of_le h]
    have hb : Bar.unitsP (R := K) (Koszul.Pres K E r) A = ⊥ := by
      rw [Bar.unitsP, Submodule.span_eq_bot]
      rintro _ ⟨e, rfl⟩
      have := Fintype.card_congr e
      rw [Fintype.card_unit] at this
      omega
    rw [hb]
    exact isCompl_bot_top
  · rw [GrOperadIdeal.atLeastTwo_sub_of_lt (by omega)]
    have ht : Bar.unitsP (R := K) (Koszul.Pres K E r) A = ⊤ := by
      refine eq_top_iff.2 fun y _ => ?_
      obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A y
      have hx := Submodule.mem_map_of_mem (f := (𝒥).proj A) (mem_units_free c (by omega) x)
      rw [Bar.unitsP, Submodule.map_span] at hx
      refine Submodule.span_mono ?_ hx
      rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
      refine ⟨e, ?_⟩
      rw [← (𝒥).projHom_app, (𝒥).projHom.app_map, (𝒥).projHom.app_one]
    rw [ht]
    exact isCompl_top_bot

/-! ### Quadratic relators -/

section Quadratic

variable (hq : Koszul.IsQuadratic K E r)

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
include hq in
/-- **The ideal of quadratic relators has no trees with fewer than two vertices**: it lies in the
relations plus the trees with at least three vertices (`Koszul.quadIdeal`). -/
lemma span_le_sup {A : Type} [Fintype A] [DecidableEq A] :
    (𝒥).sub A ≤ ⨆ i, ⨆ (_ : i ≠ 0 ∧ i ≠ 1), FreeGrL.vx K E i A := by
  have hJ : GrOperadIdeal.span K r ≤ Koszul.quadIdeal K E r hq :=
    GrOperadIdeal.span_le.2 fun n x hx => Submodule.mem_sup_left (Koszul.mem_relSp hx)
  refine (hJ A).trans (sup_le ?_ (iSup_le fun j => ?_))
  · exact (Koszul.relSp_le_vx hq).trans (le_iSup₂_of_le 2 ⟨by norm_num, by norm_num⟩ le_rfl)
  · exact le_iSup₂_of_le j.1 ⟨by have := j.2; omega, by have := j.2; omega⟩ le_rfl

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
include hq in
/-- An element of the ideal of quadratic relators without vertices vanishes. -/
lemma eq_zero_of_mem_vx_zero {A : Type} [Fintype A] [DecidableEq A] {x : FreeGrL K E A}
    (h0 : x ∈ FreeGrL.vx K E 0 A) (hx : x ∈ (𝒥).sub A) : x = 0 := by
  have hind := iSupIndep_def.1 (iSupIndep_eigenspace_nat
    ((FreeGrL.derSp (GrSpEnd.id K E)).app A)) 0
  refine Submodule.disjoint_def.1 hind x h0 ?_
  refine (iSup₂_le fun i hi => ?_ : (⨆ i, ⨆ (_ : i ≠ 0 ∧ i ≠ 1), FreeGrL.vx K E i A) ≤ _)
    (span_le_sup r hq hx)
  exact le_iSup₂_of_le i hi.1 le_rfl

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
include hq in
/-- **The coefficient of the generators kills the ideal of quadratic relators.** -/
lemma genCoef_eq_zero_of_mem_span {A : Type} [Fintype A] [DecidableEq A] {x : FreeGrL K E A}
    (hx : x ∈ (𝒥).sub A) : FreeGrL.genCoef K E A x = 0 := by
  have hle : (⨆ i, ⨆ (_ : i ≠ 0 ∧ i ≠ 1), FreeGrL.vx K E i A)
      ≤ LinearMap.ker (FreeGrL.genCoef K E A) :=
    iSup₂_le fun i hi y hy => LinearMap.mem_ker.2 (CutLift.genCoef_of_mem_vx hi.2 hy)
  exact LinearMap.mem_ker.1 (hle (span_le_sup r hq hx))

/-- **The coefficient of the generators of the presented operad**, for quadratic relators. -/
noncomputable def presCoef (A : Type) [Fintype A] [DecidableEq A] :
    Koszul.Pres K E r A →ₗ[K] E A :=
  Submodule.liftQ _ (FreeGrL.genCoef K E A) fun _ hx =>
    LinearMap.mem_ker.2 (genCoef_eq_zero_of_mem_span r hq hx)

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma presCoef_proj {A : Type} [Fintype A] [DecidableEq A] (y : FreeGrL K E A) :
    presCoef r hq A ((𝒥).proj A y) = FreeGrL.genCoef K E A y := rfl

/-- **The retraction of the suspended generators** `sĪ_P → sE`, the coefficient of the
generators. -/
noncomputable def barRet : GrSpeciesHom K (BarGen (Ipres K E c hc r)) (GrSpecies.Shift E K) where
  app A _ _ := presCoef r hq A ∘ₗ ((Ipres K E c hc r).sub A).subtype
  app_map {A B} _ _ _ _ σ' w := by
    show presCoef r hq B (GrOperad.map (R := K) σ' (IdealSp.val _ w))
      = SymSpecies.map (R := K) (V := E) σ' (presCoef r hq A (IdealSp.val _ w))
    obtain ⟨y, hy⟩ := (𝒥).proj_surjective A (IdealSp.val _ w)
    rw [← hy, ← (𝒥).projHom_app, ← (𝒥).projHom.app_map, (𝒥).projHom_app, (𝒥).projHom_app,
      presCoef_proj,
      presCoef_proj, FreeGrL.genCoef_map]
  app_par {A} _ _ b w := by
    show presCoef r hq A (GrOperad.par (R := K) (!b) (IdealSp.val _ w))
      = GrSpecies.par (R := K) (V := E) (!b) (presCoef r hq A (IdealSp.val _ w))
    obtain ⟨y, hy⟩ := (𝒥).proj_surjective A (IdealSp.val _ w)
    rw [← hy, ← (𝒥).projHom_app, ← (𝒥).projHom.app_par, (𝒥).projHom_app, (𝒥).projHom_app,
      presCoef_proj,
      presCoef_proj, FreeGrL.genCoef_par]

/-- **The retraction is a left inverse** of the suspended generators `sE → sĪ_P`. -/
lemma barRet_barGen {A : Type} [Fintype A] [DecidableEq A] (v : GrSpecies.Shift E K A) :
    (barRet c hc r hq).app A
      ((Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r)).app A v) = v :=
  FreeGrL.genCoef_ι (R := K) (V := E) v

/-- The retraction of `T^c(sE) → B(P, Ī_P)`. -/
lemma mapSp_barRet_barGen {A : Type} [Fintype A] [DecidableEq A] (z : Koszul.Cut K E A) :
    (FreeGrL.mapSp (barRet c hc r hq)).app A
      ((FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app A z) = z :=
  (FreeGrL.mapSp_comp _ _ z).trans ((FreeGrL.mapSp_congr
    (ψ := (GrSpEnd.id K (GrSpecies.Shift E K)).toHom)
    (fun _ _ _ v => barRet_barGen c hc r hq v) z).trans (FreeGrL.mapSp_id z))

include hq in
/-- **The comparison morphism `P^¡ → B(P, Ī_P)` is injective**, for quadratic relators. -/
theorem dualToBar_injective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective ((Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app A) := by
  intro x y hxy
  refine (Koszul.dualSub K E r).incl_injective A ?_
  refine ((mapSp_barRet_barGen c hc r hq _).symm.trans ?_).trans
    (mapSp_barRet_barGen c hc r hq _)
  exact congrArg ((FreeGrL.mapSp (barRet c hc r hq)).app A) hxy

include hq in
/-- **Quadratic relators generate an ideal of operations with at least two inputs.** -/
lemma span_le_atLeastTwo : 𝒥 ≤ Ibar K E c hc :=
  GrOperadIdeal.span_le.2 fun n x hx => by
    by_cases h : 2 ≤ n
    · rw [GrOperadIdeal.atLeastTwo_sub_of_le (by simpa using h)]
      trivial
    · have h0 : x ∈ FreeGrL.vx K E 0 (Fin n) :=
        Cobar.unitSpan_le_vx (mem_units_free c (by simp; omega) x)
      rw [eq_zero_of_mem_vx_zero r hq h0 (GrOperadIdeal.subset_span n hx)]
      exact zero_mem _

include c hc hq in
/-- **The unit of the presented operad is free**, for quadratic relators: the hypothesis `hone`
of `Koszul.isKoszul_iff`. -/
lemma hone_pres (a : K)
    (ha : a • GrOperad.one (R := K) (P := Koszul.Pres K E r) = 0) : a = 0 := by
  have h1 : (𝒥).proj Unit (a • GrOperad.one (R := K) (P := FreeGrL K E)) = 0 := by
    rw [map_smul]
    exact ha
  rw [GrOperadIdeal.proj_eq_zero_iff] at h1
  have h2 := span_le_atLeastTwo c hc r hq _ h1
  rw [GrOperadIdeal.atLeastTwo_sub_of_lt (by simp), Submodule.mem_bot, smul_eq_zero] at h2
  exact h2.resolve_right (one_ne_zero_free c hc)

include hq in
/-- **The Koszul criterion for quadratic data on generators of any arity**: `P = T(E)/(r)` is
Koszul iff the comparison morphism `P^¡ → B(P, Ī_P)` is a quasi-isomorphism in the arities at
least two, `Ī_P` the ideal of the operations with at least two inputs. -/
theorem isKoszul_iff_toBar :
    Koszul.IsKoszul K E r ↔ ∀ (B : Type) [Fintype B] [DecidableEq B], 2 ≤ Fintype.card B →
      Function.Bijective (Homology.map
        (dV := (0 : Koszul.Dual K E r B →ₗ[K] Koszul.Dual K E r B))
        (dW := DGCooperad.d (R := K) (C := BarCoop (Ipres K E c hc r)) (A := B))
        ((Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app B) fun x => by
          rw [LinearMap.zero_apply, map_zero,
            Koszul.d_toBar _ _ (GrOperadIdeal.atLeastTwo_hI1 (pres_zero c hc r)) x]) :=
  Koszul.isKoszul_iff (Ipres K E c hc r) (hE_pres c hc r)
    (GrOperadIdeal.atLeastTwo_hI1 (pres_zero c hc r)) (hEred c) (hcompl_pres c hc r)
    (hone_pres c hc r hq)

include hq in
/-- **The Koszul criterion on the inputs `0, …, n - 1`**: `P` is Koszul iff
`P^¡(n) → B(P, Ī_P)(n)` is a quasi-isomorphism for every `n ≥ 2`. -/
theorem isKoszul_iff_toBar_fin :
    Koszul.IsKoszul K E r ↔ ∀ n, 2 ≤ n →
      Function.Bijective (Homology.map
        (dV := (0 : Koszul.Dual K E r (Fin n) →ₗ[K] Koszul.Dual K E r (Fin n)))
        (dW := DGCooperad.d (R := K) (C := BarCoop (Ipres K E c hc r)) (A := Fin n))
        ((Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app (Fin n)) fun x => by
          rw [LinearMap.zero_apply, map_zero,
            Koszul.d_toBar _ _ (GrOperadIdeal.atLeastTwo_hI1 (pres_zero c hc r)) x]) := by
  rw [isKoszul_iff_toBar c hc r hq]
  refine ⟨fun h n hn => h (Fin n) (by simpa using hn), fun h B _ _ hB => ?_⟩
  have e : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  refine (Homology.map_bijective_iff_of_equiv (spMapEquiv e) (spMapEquiv e) (fun v => ?_)
    (fun w => DGCooperad.map_d e w) _ _ fun v => ?_).2 (h _ hB)
  · show SymSpecies.map (R := K) e 0 = 0
    exact map_zero _
  · exact (Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app_map e v

end Quadratic

end ShuffleAnySym

end Operad
