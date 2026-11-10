/-
# The presented operad of binary quadratic data, and the Koszul criterion

Step (2c) of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin), first part.
Let `E` be a graded linear species over a field `K` with an even basis `c k` of each
`E (Fin k)` indexed by `BinGen G k`, so concentrated in arity two, `T = FreeGrL K E`, relators
`r n ⊆ T (Fin n)`, and `P = Koszul.Pres K E r = T/(r)`.

* **The hypotheses of the Koszul criterion `Koszul.isKoszul_iff`** for `P` and its ideal
  `Ī_P = ShuffleBarSym.Ipres` of the operations with at least two inputs
  (`GrOperadIdeal.atLeastTwo`, defined since `P` vanishes in arity zero,
  `ShuffleBarSym.pres_zero`): there are no generators with at most one input
  (`ShuffleBarSym.hEred`, from `ShuffleBarSym.gen_eq_zero`); `Ī_P` contains the generators
  (`ShuffleBarSym.hE_pres`); the units of `P` complement `Ī_P` (`ShuffleBarSym.hcompl_pres`), as
  `T` is spanned by its units in the arities at most one; and, for relators of weight at least two
  (`r n = ∅` for `n < 2`), the unit of `P` is free (`ShuffleBarSym.hone_pres`), since then
  `(r) ⊆ Ī` (`ShuffleBarSym.span_le_atLeastTwo`) and the unit of `T` is not zero
  (`ShuffleBarSym.one_ne_zero_free`).
* **The Koszul criterion for binary quadratic data** (`ShuffleBarSym.isKoszul_iff_toBar`): over a
  field of characteristic zero, for relators of weight at least two, **`P` is Koszul iff
  `P^¡ → B(P, Ī_P)` is a quasi-isomorphism in the arities at least two**, and it suffices to
  check the inputs `0, …, n - 1` (`ShuffleBarSym.isKoszul_iff_toBar_fin`), conjugate chain maps
  being quasi-isomorphisms together (`Homology.map_bijective_iff_of_equiv`).

Open (the rest of step 2c, planned in the README): `B(P, Ī_P)(Fin n)` as the quotient of
`B(T, Ī)(Fin n) ≅ ShuffleBar.C` by the relator subcomplex `ShuffleBar.J` of the shuffle relators
of `r 3`, and `P^¡(n)` as the cycles of the top degree, which together turn
`Koszul.IsKoszul K E r` into `ShuffleBar.IsKoszul`.
-/
import Operad.ShuffleBarSymExp
import Operad.KoszulCriterion

universe u

namespace Operad

open Sym GerBV

/-! ## Homology and isomorphisms -/

section HomologyEquiv

variable {R : Type*} [CommRing R] {V W V' W' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']

/-- **An isomorphism of complexes is a quasi-isomorphism.** -/
lemma Homology.map_equiv_bijective {dV : V →ₗ[R] V} {dW : W →ₗ[R] W} (α : V ≃ₗ[R] W)
    (hα : ∀ v, α (dV v) = dW (α v)) : Function.Bijective (Homology.map (α : V →ₗ[R] W) hα) := by
  have hα' : ∀ w, α.symm (dW w) = dV (α.symm w) := fun w => by
    apply α.injective
    rw [hα, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  refine Function.bijective_iff_has_inverse.2
    ⟨Homology.map (α.symm : W →ₗ[R] V) hα', fun h => ?_, fun h => ?_⟩
  · obtain ⟨z, rfl⟩ := Homology.mk_surjective _ h
    rw [Homology.map_mk, Homology.map_mk]
    congr 1
    exact Subtype.ext (α.symm_apply_apply z.1)
  · obtain ⟨z, rfl⟩ := Homology.mk_surjective _ h
    rw [Homology.map_mk, Homology.map_mk]
    congr 1
    exact Subtype.ext (α.apply_symm_apply z.1)

/-- **Conjugate chain maps are quasi-isomorphisms together**: for isomorphisms of complexes
`α`, `β` with `f' ∘ α = β ∘ f`. -/
lemma Homology.map_bijective_iff_of_equiv {dV : V →ₗ[R] V} {dW : W →ₗ[R] W} {dV' : V' →ₗ[R] V'}
    {dW' : W' →ₗ[R] W'} (α : V ≃ₗ[R] V') (β : W ≃ₗ[R] W') (hα : ∀ v, α (dV v) = dV' (α v))
    (hβ : ∀ w, β (dW w) = dW' (β w)) {f : V →ₗ[R] W} {f' : V' →ₗ[R] W'}
    (hf : ∀ v, f (dV v) = dW (f v)) (hf' : ∀ v, f' (dV' v) = dW' (f' v))
    (hsq : ∀ v, f' (α v) = β (f v)) :
    Function.Bijective (Homology.map f hf) ↔ Function.Bijective (Homology.map f' hf') := by
  have hcomm : ⇑(Homology.map (β : W →ₗ[R] W') hβ) ∘ ⇑(Homology.map f hf)
      = ⇑(Homology.map f' hf') ∘ ⇑(Homology.map (α : V →ₗ[R] V') hα) := by
    funext h
    obtain ⟨z, rfl⟩ := Homology.mk_surjective _ h
    simp only [Function.comp_apply, Homology.map_mk]
    congr 1
    exact Subtype.ext (hsq z.1).symm
  rw [← (Homology.map_equiv_bijective β hβ).of_comp_iff' (Homology.map f hf), hcomm]
  exact (Homology.map_equiv_bijective α hα).of_comp_iff _

end HomologyEquiv

namespace ShuffleBarSym

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))

local notation "𝒥" => GrOperadIdeal.span K r

omit [Fintype G] [DecidableEq G] in
include c in
/-- **The generators vanish in the arities other than two.** -/
lemma gen_eq_zero {B : Type} [Fintype B] [DecidableEq B] (hB : Fintype.card B ≠ 2) (v : E B) :
    v = 0 := by
  let e : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  have hk : ∀ k, k ≠ 2 → IsEmpty (BinGen G k) := fun k hk => ⟨fun b => by cases b; exact hk rfl⟩
  haveI := hk _ hB
  have h0 : SymSpecies.map (R := K) (V := E) e v = 0 :=
    (c (Fintype.card B)).repr.injective (Subsingleton.elim _ _)
  have := congrArg (SymSpecies.map (R := K) (V := E) e.symm) h0
  rwa [← SymSpecies.map_trans, Equiv.self_trans_symm, SymSpecies.map_refl, map_zero] at this

omit [Fintype G] [DecidableEq G] in
include c in
/-- **No generators with at most one input**, the hypothesis `hEred` of `Koszul.isKoszul_iff`. -/
lemma hEred (B : Type) [Fintype B] [DecidableEq B] (hB : Fintype.card B ≤ 1) (v : E B) : v = 0 :=
  gen_eq_zero c (by omega) v

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

omit [Fintype G] [DecidableEq G] in
include c in
/-- In the arities at most one, the free operad is spanned by the relabellings of its unit. -/
lemma mem_units_free {A : Type} [Fintype A] [DecidableEq A] (hA : Fintype.card A ≤ 1)
    (x : FreeGrL K E A) : x ∈ Bar.unitsP (R := K) (FreeGrL K E) A :=
  FreeGrL.mem_unitSpan_of_card_le (R := K) (V := E) (hEred c) hA x

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

omit [CharZero K] in
include hc in
/-- **The relators of weight at least two generate an ideal of operations with at least two
inputs.** -/
lemma span_le_atLeastTwo (hr : ∀ n, n < 2 → r n = ∅) : 𝒥 ≤ Ibar K E c hc :=
  GrOperadIdeal.span_le.2 fun n x hx => by
    by_cases h : 2 ≤ n
    · rw [GrOperadIdeal.atLeastTwo_sub_of_le (by simpa using h)]
      trivial
    · rw [hr n (by omega)] at hx
      exact hx.elim

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
  have hm : LTree.leaf 0 ∈ LTree.monomials (E := G) (Fintype.card (Fin 1)) := by
    simp [LTree.monomials]
  exact (tBasis c hc (Fin 1)).ne_zero ⟨_, hm⟩ (hall _)

include c hc in
/-- **The unit of the presented operad is free**, for relators of weight at least two: the
hypothesis `hone` of `Koszul.isKoszul_iff`. -/
lemma hone_pres (hr : ∀ n, n < 2 → r n = ∅) (a : K)
    (ha : a • GrOperad.one (R := K) (P := Koszul.Pres K E r) = 0) : a = 0 := by
  have h1 : (𝒥).proj Unit (a • GrOperad.one (R := K) (P := FreeGrL K E)) = 0 := by
    rw [map_smul]
    exact ha
  rw [GrOperadIdeal.proj_eq_zero_iff] at h1
  have h2 := span_le_atLeastTwo c hc r hr _ h1
  rw [GrOperadIdeal.atLeastTwo_sub_of_lt (by simp), Submodule.mem_bot, smul_eq_zero] at h2
  exact h2.resolve_right (one_ne_zero_free c hc)

/-- **The Koszul criterion for binary quadratic data**: for relators of weight at least two,
`P = T(E)/(r)` is Koszul iff the comparison morphism `P^¡ → B(P, Ī_P)` is a quasi-isomorphism in
the arities at least two, `Ī_P` the ideal of the operations with at least two inputs. -/
theorem isKoszul_iff_toBar (hr : ∀ n, n < 2 → r n = ∅) :
    Koszul.IsKoszul K E r ↔ ∀ (B : Type) [Fintype B] [DecidableEq B], 2 ≤ Fintype.card B →
      Function.Bijective (Homology.map
        (dV := (0 : Koszul.Dual K E r B →ₗ[K] Koszul.Dual K E r B))
        (dW := DGCooperad.d (R := K) (C := BarCoop (Ipres K E c hc r)) (A := B))
        ((Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app B) fun x => by
          rw [LinearMap.zero_apply, map_zero,
            Koszul.d_toBar _ _ (GrOperadIdeal.atLeastTwo_hI1 (pres_zero c hc r)) x]) :=
  Koszul.isKoszul_iff (Ipres K E c hc r) (hE_pres c hc r)
    (GrOperadIdeal.atLeastTwo_hI1 (pres_zero c hc r)) (hEred c) (hcompl_pres c hc r)
    (hone_pres c hc r hr)

/-- Relabelling, as a linear equivalence of a linear species. -/
noncomputable def spMapEquiv {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (V A)] [SymSpecies K V]
    {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] (e : A ≃ A') :
    V A ≃ₗ[K] V A' :=
  LinearEquiv.ofLinear (SymSpecies.map (R := K) e) (SymSpecies.map (R := K) e.symm)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← SymSpecies.map_trans, Equiv.symm_trans_self,
        SymSpecies.map_refl]
      rfl)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← SymSpecies.map_trans, Equiv.self_trans_symm,
        SymSpecies.map_refl]
      rfl)

/-- **The Koszul criterion for binary quadratic data, on the inputs `0, …, n - 1`**: for
relators of weight at least two, `P` is Koszul iff `P^¡(n) → B(P, Ī_P)(n)` is a
quasi-isomorphism for every `n ≥ 2`. -/
theorem isKoszul_iff_toBar_fin (hr : ∀ n, n < 2 → r n = ∅) :
    Koszul.IsKoszul K E r ↔ ∀ n, 2 ≤ n →
      Function.Bijective (Homology.map
        (dV := (0 : Koszul.Dual K E r (Fin n) →ₗ[K] Koszul.Dual K E r (Fin n)))
        (dW := DGCooperad.d (R := K) (C := BarCoop (Ipres K E c hc r)) (A := Fin n))
        ((Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app (Fin n)) fun x => by
          rw [LinearMap.zero_apply, map_zero,
            Koszul.d_toBar _ _ (GrOperadIdeal.atLeastTwo_hI1 (pres_zero c hc r)) x]) := by
  rw [isKoszul_iff_toBar c hc r hr]
  refine ⟨fun h n hn => h (Fin n) (by simpa using hn), fun h B _ _ hB => ?_⟩
  have e : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  refine (Homology.map_bijective_iff_of_equiv (spMapEquiv e) (spMapEquiv e) (fun v => ?_)
    (fun w => DGCooperad.map_d e w) _ _ fun v => ?_).2 (h _ hB)
  · show SymSpecies.map (R := K) e 0 = 0
    exact map_zero _
  · exact (Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app_map e v

end ShuffleBarSym

end Operad
