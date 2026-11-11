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
* **Degree by degree** (`ShuffleBarSym.isKoszul_iff_deg`). On a species concentrated in arity two
  the trees on `A` have `|A| - 1` vertices (`FreeGrL.mem_vx_of_binary`), so `P^¡(n) → B(P, Ī_P)(n)`
  lands in the top degree `n - 1` (`ShuffleBarSym.toBar_mem_vx`). In any bar construction with an
  ideal without operations with at most one input, over a field of characteristic zero, the
  degrees of arity `n` are independent and below `n` (`Bar.eq_zero_of_mem_iSup_ne`,
  `Bar.vx_eq_zero`, `Bar.exists_decomp`) and the components of a cycle are cycles
  (`Bar.d_comp_eq_zero`); so a chain map from the zero differential into the top degree is a
  quasi-isomorphism iff it is injective, onto the cycles of the top degree, and every cycle of a
  lower degree is a boundary (`Bar.map_zero_bijective_iff_deg`, through
  `Homology.map_zero_bijective_iff`). Hence **`P` is Koszul iff for every `n ≥ 2`, `P^¡(n) →
  B(P, Ī_P)(n)` is injective onto the cycles with `n - 1` vertices and every cycle with `s + 1 < n`
  vertices is the boundary of one with `s + 1`**.
* **Injectivity.** For relators with at least three inputs (`r n = ∅` for `n < 3`), the ideal of
  the relators lies in the operations with at least three inputs (`GrOperadIdeal.atLeast`,
  `ShuffleBarSym.span_le_atLeast_three`), so the coefficient of the generators descends to `P`
  (`ShuffleBarSym.presCoef`) and gives a retraction `sĪ_P → sE` of the suspended generators
  (`ShuffleBarSym.barRet`, `ShuffleBarSym.barRet_barGen`); hence `P^¡ → B(P, Ī_P)` is injective
  (`ShuffleBarSym.dualToBar_injective`), and **`P` is Koszul iff for every `n ≥ 2` it maps onto
  the cycles with `n - 1` vertices and every cycle with `s + 1 < n` vertices is a boundary**
  (`ShuffleBarSym.isKoszul_iff_cycles`).

`ShuffleBarProj.lean` continues: `B(P, Ī_P)` is the quotient of `B(T, Ī)` by the ideal generated
by the suspended relators, and the Koszul criterion moves to `B(T, Ī)` modulo that ideal.
-/
import Operad.ShuffleBarSymExp
import Operad.KoszulCriterion

universe u v

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

section HomologyZero

variable {R : Type*} [CommRing R] {V W : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

/-- **A chain map out of a module with the zero differential is a quasi-isomorphism** iff it
meets the boundaries only in zero and every cycle is a value plus a boundary. -/
lemma Homology.map_zero_bijective_iff {dW : W →ₗ[R] W} (f : V →ₗ[R] W)
    (hf : ∀ v, f ((0 : V →ₗ[R] V) v) = dW (f v)) :
    Function.Bijective (Homology.map f hf) ↔
      (∀ v w, f v = dW w → v = 0) ∧ ∀ z, dW z = 0 → ∃ v w, z = f v + dW w := by
  have hmk : ∀ v : V, Homology.mk (0 : V →ₗ[R] V) ⟨v, by simp⟩ = 0 → v = 0 := fun v h => by
    rw [Homology.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨u, hu⟩ := h
    simpa using hu.symm
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun v w hvw => ?_, fun z hz => ?_⟩
    · have h0 : Homology.map f hf (Homology.mk _ ⟨v, by simp⟩) = 0 := by
        rw [Homology.map_mk, Homology.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨w, hvw.symm⟩
      rw [← map_zero (Homology.map f hf)] at h0
      exact hmk v (hinj h0)
    · obtain ⟨h, hh⟩ := hsurj (Homology.mk dW ⟨z, hz⟩)
      obtain ⟨⟨v, hv⟩, rfl⟩ := Homology.mk_surjective _ h
      rw [Homology.map_mk, Homology.mk_eq_mk_iff] at hh
      obtain ⟨w, hw⟩ := hh
      refine ⟨v, -w, ?_⟩
      have hw' : dW w = f v - z := hw
      rw [map_neg, hw']
      abel
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun h h' hh => ?_, fun h => ?_⟩
    · obtain ⟨⟨v, hv⟩, rfl⟩ := Homology.mk_surjective _ h
      obtain ⟨⟨v', hv'⟩, rfl⟩ := Homology.mk_surjective _ h'
      rw [Homology.map_mk, Homology.map_mk, Homology.mk_eq_mk_iff] at hh
      obtain ⟨w, hw⟩ := hh
      have hw' : f (v - v') = dW w := by
        rw [map_sub]
        exact hw.symm
      have := hinj _ _ hw'
      congr 1
      exact Subtype.ext (sub_eq_zero.1 this)
    · obtain ⟨⟨z, hz⟩, rfl⟩ := Homology.mk_surjective _ h
      obtain ⟨v, w, rfl⟩ := hsurj z hz
      refine ⟨Homology.mk _ ⟨v, by simp⟩, ?_⟩
      rw [Homology.map_mk, Homology.mk_eq_mk_iff]
      exact ⟨-w, by simp [Homology.cycleMap]⟩

end HomologyZero

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

/-- **On a species concentrated in arity two, the trees on `A` have `|A| - 1` vertices.** -/
theorem mem_vx_of_binary
    (hV : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≠ 2 → ∀ v : V B, v = 0)
    {A : Type} [Fintype A] [DecidableEq A] (hA : 1 ≤ Fintype.card A) (x : FreeGrL R V A) :
    x ∈ vx R V (Fintype.card A - 1) A := by
  rw [mem_eig, derSp_lin (GrSpEnd.scalar R V fun n => (n : R) - 1) (GrSpEnd.id R V)
    (GrSpEnd.id R V) 1 0 (fun B _ _ v => ?_) x, derSp_excess, Nat.cast_sub hA]
  · simp
  · by_cases hB : Fintype.card B = 2
    · rw [GrSpEnd.scalar_app, hB]
      norm_num
    · rw [hV B hB v]
      simp

end FreeGrL

namespace Bar

variable {K : Type u} [Field K] [CharZero K]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (P A)] [GrOperad K P]
  (I : GrOperadIdeal K P)
  (hI1 : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ y ∈ I.sub B, y = 0)

local notation "𝒱" => FreeGrL.vx K (BarGen I)

/-- The trees with `j` vertices, `j ≠ t + 1`, have their differentials off the degree `t`. -/
lemma d_mem_iSup_ne {n j t : ℕ} (hj : j ≠ t + 1) {y : FreeGrL K (BarGen I) (Fin n)}
    (hy : y ∈ 𝒱 j (Fin n)) : d I (Fin n) y ∈ ⨆ i, ⨆ (_ : i ≠ t), 𝒱 i (Fin n) := by
  rcases j with _ | j
  · rw [d_vx_zero hy]
    exact zero_mem _
  · exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (by omega) (d_vx_succ hy))

/-- **The degrees are independent.** -/
lemma eq_zero_of_mem_iSup_ne {n s : ℕ} {a : FreeGrL K (BarGen I) (Fin n)} (ha : a ∈ 𝒱 s (Fin n))
    (ha' : a ∈ ⨆ i, ⨆ (_ : i ≠ s), 𝒱 i (Fin n)) : a = 0 :=
  Submodule.disjoint_def.1 (iSupIndep_def.1 (iSupIndep_eigenspace_nat
    ((FreeGrL.derSp (GrSpEnd.id K (BarGen I))).app (Fin n))) s) a ha ha'

include hI1 in
/-- **No tree on `n` inputs has `n` vertices or more.** -/
lemma vx_eq_zero {n j : ℕ} (hj : n ≤ j) {y : FreeGrL K (BarGen I) (Fin n)}
    (hy : y ∈ 𝒱 j (Fin n)) : y = 0 :=
  FreeGrL.eig_card_eq_bot (R := K) (V := BarGen I)
    (fun B _ _ hB v => IdealSp.ext I (hI1 B hB _ (IdealSp.mem I v))) (by simpa using hj) hy

include hI1 in
/-- **The decomposition into degrees**, in arity `n`. -/
lemma exists_decomp {n : ℕ} (z : FreeGrL K (BarGen I) (Fin n)) :
    ∃ c : ℕ → FreeGrL K (BarGen I) (Fin n), (∀ j, c j ∈ 𝒱 j (Fin n)) ∧
      z = ∑ j ∈ Finset.range n, c j := by
  have hz : z ∈ ⨆ j : ℕ, 𝒱 j (Fin n) :=
    (FreeGrL.iSup_vx (R := K) (V := BarGen I) (Fin n)).symm ▸ Submodule.mem_top
  induction hz using Submodule.iSup_induction' with
  | mem j y hy =>
    by_cases hj : j < n
    · refine ⟨fun i => if i = j then y else 0, fun i => ?_, ?_⟩
      · dsimp only
        split_ifs with h
        · exact h ▸ hy
        · exact zero_mem _
      · rw [Finset.sum_ite_eq' (Finset.range n) j, if_pos (Finset.mem_range.2 hj)]
    · refine ⟨0, fun _ => zero_mem _, ?_⟩
      rw [vx_eq_zero I hI1 (by omega) hy]
      simp
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨c', hc', rfl⟩ := hy'
    exact ⟨c + c', fun j => add_mem (hc j) (hc' j), by simp [Finset.sum_add_distrib]⟩

include hI1 in
/-- Every boundary is, up to terms off the degree `s`, the boundary of a tree with `s + 1`
vertices. -/
lemma exists_d_sub {n : ℕ} (s : ℕ) (w : FreeGrL K (BarGen I) (Fin n)) :
    ∃ w' ∈ 𝒱 (s + 1) (Fin n), d I (Fin n) w - d I (Fin n) w'
      ∈ ⨆ i, ⨆ (_ : i ≠ s), 𝒱 i (Fin n) := by
  obtain ⟨c, hc, rfl⟩ := exists_decomp I hI1 w
  refine ⟨c (s + 1), hc _, ?_⟩
  rw [map_sum]
  by_cases hs : s + 1 ∈ Finset.range n
  · rw [← Finset.add_sum_erase _ _ hs, add_sub_cancel_left]
    exact Submodule.sum_mem _ fun j hj => d_mem_iSup_ne I (Finset.ne_of_mem_erase hj) (hc j)
  · rw [vx_eq_zero I hI1 (by simpa using hs) (hc (s + 1)), map_zero, sub_zero]
    exact Submodule.sum_mem _ fun j hj => d_mem_iSup_ne I (fun h => hs (h ▸ hj)) (hc j)

include hI1 in
/-- **The components of a cycle are cycles.** -/
lemma d_comp_eq_zero {n : ℕ} {c : ℕ → FreeGrL K (BarGen I) (Fin n)} (hc : ∀ j, c j ∈ 𝒱 j (Fin n))
    (hz : d I (Fin n) (∑ j ∈ Finset.range n, c j) = 0) (j : ℕ) : d I (Fin n) (c j) = 0 := by
  rcases j with _ | t
  · exact d_vx_zero (hc 0)
  by_cases ht : t + 1 ∈ Finset.range n
  · refine eq_zero_of_mem_iSup_ne I (s := t) (d_vx_succ (hc _)) ?_
    have h2 : d I (Fin n) (c (t + 1))
        = -∑ j ∈ (Finset.range n).erase (t + 1), d I (Fin n) (c j) := by
      rw [map_sum, ← Finset.add_sum_erase _ _ ht] at hz
      exact eq_neg_of_add_eq_zero_left hz
    rw [h2]
    exact neg_mem (Submodule.sum_mem _ fun j hj => d_mem_iSup_ne I (Finset.ne_of_mem_erase hj)
      (hc j))
  · rw [vx_eq_zero I hI1 (by simpa using ht) (hc _), map_zero]

include hI1 in
/-- **The homology of a map into the top degree, degree by degree**: in arity `n`, for a linear
map `f` into the trees with `n - 1` vertices, `f` meets the boundaries only in zero and every
cycle is a value plus a boundary iff `f` is injective, maps onto the cycles with `n - 1`
vertices, and every cycle with `s + 1 < n` vertices is the boundary of one with `s + 1`. -/
theorem elem_iff_deg {n : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] FreeGrL K (BarGen I) (Fin n)) (hfv : ∀ v, f v ∈ 𝒱 (n - 1) (Fin n)) :
    ((∀ v w, f v = d I (Fin n) w → v = 0) ∧
      ∀ z, d I (Fin n) z = 0 → ∃ v w, z = f v + d I (Fin n) w) ↔ Function.Injective f ∧
      (∀ z ∈ 𝒱 (n - 1) (Fin n), d I (Fin n) z = 0 → ∃ v, f v = z) ∧
      ∀ s, s + 1 < n → ∀ z ∈ 𝒱 s (Fin n), d I (Fin n) z = 0 →
        ∃ w ∈ 𝒱 (s + 1) (Fin n), d I (Fin n) w = z := by
  -- a boundary in the top degree vanishes
  have htopb : ∀ w, d I (Fin n) w ∈ 𝒱 (n - 1) (Fin n) → d I (Fin n) w = 0 := fun w hw => by
    obtain ⟨w', hw', hdiff⟩ := exists_d_sub I hI1 (n - 1) w
    rcases n with _ | m
    · exact vx_eq_zero I hI1 le_rfl hw
    · rw [vx_eq_zero I hI1 (by omega) hw', map_zero, sub_zero] at hdiff
      exact eq_zero_of_mem_iSup_ne I hw hdiff
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun v v' h => sub_eq_zero.1 (hinj (v - v') 0 (by rw [map_sub, h, sub_self,
      map_zero])), fun z hz hdz => ?_, fun s hs z hz hdz => ?_⟩
    · obtain ⟨v, w, rfl⟩ := hsurj z hdz
      have hw : d I (Fin n) w ∈ 𝒱 (n - 1) (Fin n) := by
        have := Submodule.sub_mem _ hz (hfv v)
        rwa [add_sub_cancel_left] at this
      exact ⟨v, by rw [htopb w hw, add_zero]⟩
    · obtain ⟨v, w, rfl⟩ := hsurj z hdz
      obtain ⟨w', hw', hdiff⟩ := exists_d_sub I hI1 s w
      refine ⟨w', hw', (sub_eq_zero.1 (eq_zero_of_mem_iSup_ne I (s := s)
        (Submodule.sub_mem _ hz (d_vx_succ hw')) ?_)).symm⟩
      have he : f v + d I (Fin n) w - d I (Fin n) w'
          = f v + (d I (Fin n) w - d I (Fin n) w') := by
        abel
      rw [he]
      exact add_mem (Submodule.mem_iSup_of_mem (n - 1)
        (Submodule.mem_iSup_of_mem (by omega) (hfv v))) hdiff
  · rintro ⟨hinj, htop, hlow⟩
    refine ⟨fun v w h => ?_, fun z hdz => ?_⟩
    · have h0 := htopb w (h ▸ hfv v)
      exact hinj (by rw [h, h0, map_zero])
    · obtain ⟨c, hc, rfl⟩ := exists_decomp I hI1 z
      have hcyc := d_comp_eq_zero I hI1 hc hdz
      have hj : ∀ j ∈ Finset.range n, ∃ v w, c j = f v + d I (Fin n) w := fun j hj => by
        rw [Finset.mem_range] at hj
        by_cases hjt : j + 1 = n
        · obtain ⟨v, hv⟩ := htop (c j) (by rw [show n - 1 = j by omega]; exact hc j) (hcyc j)
          exact ⟨v, 0, by rw [hv, map_zero, add_zero]⟩
        · obtain ⟨w, -, hw⟩ := hlow j (by omega) (c j) (hc j) (hcyc j)
          exact ⟨0, w, by rw [hw, map_zero, zero_add]⟩
      choose! v w hvw using hj
      refine ⟨∑ j ∈ Finset.range n, v j, ∑ j ∈ Finset.range n, w j, ?_⟩
      rw [map_sum, map_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hvw

include hI1 in
/-- **A chain map from the zero differential into the top degree is a quasi-isomorphism** iff it
is injective, maps onto the cycles of the top degree, and the homology vanishes below it: in arity
`n`, the top degree being `n - 1` vertices. -/
theorem map_zero_bijective_iff_deg {n : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] FreeGrL K (BarGen I) (Fin n))
    (hf : ∀ v, f ((0 : V →ₗ[K] V) v) = d I (Fin n) (f v))
    (hfv : ∀ v, f v ∈ 𝒱 (n - 1) (Fin n)) :
    Function.Bijective (Homology.map f hf) ↔ Function.Injective f ∧
      (∀ z ∈ 𝒱 (n - 1) (Fin n), d I (Fin n) z = 0 → ∃ v, f v = z) ∧
      ∀ s, s + 1 < n → ∀ z ∈ 𝒱 s (Fin n), d I (Fin n) z = 0 →
        ∃ w ∈ 𝒱 (s + 1) (Fin n), d I (Fin n) w = z := by
  rw [Homology.map_zero_bijective_iff]
  exact elem_iff_deg I hI1 f hfv

end Bar

namespace GrOperadIdeal

variable (R : Type u) [CommRing R] (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]

/-- **The ideal of the operations with at least `m` inputs**, for a graded operad without
operations in arity zero. -/
noncomputable def atLeast (m : ℕ) (h0 : ∀ y : P (Fin 0), y = 0) : GrOperadIdeal R P where
  sub A := if m ≤ Fintype.card A then ⊤ else ⊥
  par_mem b {A} _ _ {x} hx := by
    split_ifs at hx ⊢
    · trivial
    · rw [Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
  map_mem {A B} _ _ _ _ e {x} hx := by
    rw [Fintype.card_congr e.symm] at *
    split_ifs at hx ⊢
    · trivial
    · rw [Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
  comp_mem_left {A B} _ _ _ _ i {x} y hx := by
    split_ifs with h
    · trivial
    rw [Submodule.mem_bot]
    split_ifs at hx with hA
    · have hB : Fintype.card B = 0 := by
        rw [Fintype.card_sum, Reg.card_without] at h
        omega
      rw [eq_zero_of_card_eq_zero R P h0 hB y, map_zero]
    · rw [Submodule.mem_bot] at hx
      rw [hx, LinearMap.map_zero₂]
  comp_mem_right {A B} _ _ _ _ i x {y} hy := by
    split_ifs with h
    · trivial
    rw [Submodule.mem_bot]
    split_ifs at hy with hB
    · have hA : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨i⟩
      rw [Fintype.card_sum, Reg.card_without] at h
      omega
    · rw [Submodule.mem_bot] at hy
      rw [hy, map_zero]

variable {R P}

lemma atLeast_sub_of_le {m : ℕ} {h0 : ∀ y : P (Fin 0), y = 0} {A : Type} [Fintype A]
    [DecidableEq A] (h : m ≤ Fintype.card A) : (atLeast R P m h0).sub A = ⊤ :=
  if_pos h

lemma atLeast_sub_of_lt {m : ℕ} {h0 : ∀ y : P (Fin 0), y = 0} {A : Type} [Fintype A]
    [DecidableEq A] (h : Fintype.card A < m) : (atLeast R P m h0).sub A = ⊥ :=
  if_neg (by omega)

end GrOperadIdeal

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)

/-- **The coefficient of the generators commutes with the parities.** -/
lemma genCoef_par {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (x : FreeGrL R V A) :
    genCoef R V A (GrOperad.par (R := R) b x) = GrSpecies.par (R := R) b (genCoef R V A x) := by
  obtain ⟨y, rfl⟩ := (𝒥).proj_surjective A x
  exact genCoefF_par b y

end FreeGrL

namespace ShuffleBarSym

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))
  (hr2 : ∀ n, n < 3 → r n = ∅)

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

/-! ### Relators with at least three inputs: the comparison morphism is injective -/

include hc hr2 in
/-- **Relators with at least three inputs generate an ideal of operations with at least three
inputs.** -/
lemma span_le_atLeast_three :
    𝒥 ≤ GrOperadIdeal.atLeast K (FreeGrL K E) 3 (free_zero c hc) :=
  GrOperadIdeal.span_le.2 fun n x hx => by
    by_cases h : 3 ≤ n
    · rw [GrOperadIdeal.atLeast_sub_of_le (by simpa using h)]
      trivial
    · rw [hr2 n (by omega)] at hx
      exact hx.elim

include hc hr2 in
/-- **The ideal of the relators vanishes in the arities at most two.** -/
lemma eq_zero_of_mem_span {B : Type} [Fintype B] [DecidableEq B] (hB : Fintype.card B ≤ 2)
    {x : FreeGrL K E B} (hx : x ∈ (𝒥).sub B) : x = 0 := by
  have h := span_le_atLeast_three c hc r hr2 _ hx
  rwa [GrOperadIdeal.atLeast_sub_of_lt (by omega), Submodule.mem_bot] at h

/-- **The coefficient of the generators of the presented operad**, for relators with at least
three inputs. -/
noncomputable def presCoef (A : Type) [Fintype A] [DecidableEq A] :
    Koszul.Pres K E r A →ₗ[K] E A :=
  Submodule.liftQ _ (FreeGrL.genCoef K E A) fun x hx => by
    by_cases hA : Fintype.card A = 2
    · rw [LinearMap.mem_ker, eq_zero_of_mem_span c hc r hr2 hA.le hx, map_zero]
    · exact gen_eq_zero c hA _

lemma presCoef_proj {A : Type} [Fintype A] [DecidableEq A] (y : FreeGrL K E A) :
    presCoef c hc r hr2 A ((𝒥).proj A y) = FreeGrL.genCoef K E A y := rfl

/-- **The retraction of the suspended generators** `sĪ_P → sE`, the coefficient of the
generators. -/
noncomputable def barRet : GrSpeciesHom K (BarGen (Ipres K E c hc r)) (GrSpecies.Shift E K) where
  app A _ _ := presCoef c hc r hr2 A ∘ₗ ((Ipres K E c hc r).sub A).subtype
  app_map {A B} _ _ _ _ σ' w := by
    show presCoef c hc r hr2 B (GrOperad.map (R := K) σ' (IdealSp.val _ w))
      = SymSpecies.map (R := K) (V := E) σ' (presCoef c hc r hr2 A (IdealSp.val _ w))
    obtain ⟨y, hy⟩ := (𝒥).proj_surjective A (IdealSp.val _ w)
    rw [← hy, ← (𝒥).projHom_app, ← (𝒥).projHom.app_map, (𝒥).projHom_app, (𝒥).projHom_app,
      presCoef_proj,
      presCoef_proj, FreeGrL.genCoef_map]
  app_par {A} _ _ b w := by
    show presCoef c hc r hr2 A (GrOperad.par (R := K) (!b) (IdealSp.val _ w))
      = GrSpecies.par (R := K) (V := E) (!b) (presCoef c hc r hr2 A (IdealSp.val _ w))
    obtain ⟨y, hy⟩ := (𝒥).proj_surjective A (IdealSp.val _ w)
    rw [← hy, ← (𝒥).projHom_app, ← (𝒥).projHom.app_par, (𝒥).projHom_app, (𝒥).projHom_app,
      presCoef_proj,
      presCoef_proj, FreeGrL.genCoef_par]

/-- **The retraction is a left inverse** of the suspended generators `sE → sĪ_P`. -/
lemma barRet_barGen {A : Type} [Fintype A] [DecidableEq A] (v : GrSpecies.Shift E K A) :
    (barRet c hc r hr2).app A
      ((Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r)).app A v) = v :=
  FreeGrL.genCoef_ι (R := K) (V := E) v

include hr2 in
/-- **The comparison morphism `P^¡ → B(P, Ī_P)` is injective**, for relators with at least three
inputs. -/
theorem dualToBar_injective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective ((Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app A) := by
  intro x y hxy
  have hid : ∀ z : Koszul.Cut K E A, (FreeGrL.mapSp (barRet c hc r hr2)).app A
      ((FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app A z) = z :=
    fun z => (FreeGrL.mapSp_comp _ _ z).trans ((FreeGrL.mapSp_congr
      (ψ := (GrSpEnd.id K (GrSpecies.Shift E K)).toHom)
      (fun B _ _ v => barRet_barGen c hc r hr2 v) z).trans (FreeGrL.mapSp_id z))
  refine (Koszul.dualSub K E r).incl_injective A ?_
  refine ((hid _).symm.trans ?_).trans (hid _)
  exact congrArg ((FreeGrL.mapSp (barRet c hc r hr2)).app A) hxy

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

local notation "𝒱P" => FreeGrL.vx K (BarGen (Ipres K E c hc r))

omit [CharZero K] in
/-- **The comparison morphism lands in the top degree**: in arity `n ≥ 1`, the trees of `P^¡(n)`,
on binary generators, have `n - 1` vertices. -/
theorem toBar_mem_vx {n : ℕ} (hn : 1 ≤ n) (x : Koszul.Dual K E r (Fin n)) :
    (Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app (Fin n) x ∈ 𝒱P (n - 1) (Fin n) := by
  rw [Koszul.toBar_app]
  have h := FreeGrL.mem_vx_of_binary (R := K) (V := GrSpecies.Shift E K)
    (fun B _ _ hB v => gen_eq_zero c hB v) (by simpa using hn)
    ((Koszul.dualSub K E r).incl (Fin n) x)
  rw [Fintype.card_fin] at h
  exact FreeGrL.mapSp_mem_vx h

/-- **The Koszul criterion for binary quadratic data, degree by degree**: for relators of weight
at least two, over a field of characteristic zero, `P` is Koszul iff for every `n ≥ 2` the
comparison morphism `P^¡(n) → B(P, Ī_P)(n)` is injective onto the cycles with `n - 1` vertices,
and every cycle with `s + 1 < n` vertices is the boundary of one with `s + 1`. -/
theorem isKoszul_iff_deg (hr : ∀ n, n < 2 → r n = ∅) :
    Koszul.IsKoszul K E r ↔ ∀ n, 2 ≤ n →
      Function.Injective ((Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app (Fin n)) ∧
      (∀ z ∈ 𝒱P (n - 1) (Fin n), Bar.d (Ipres K E c hc r) (Fin n) z = 0 →
        ∃ x, (Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app (Fin n) x = z) ∧
      ∀ s, s + 1 < n → ∀ z ∈ 𝒱P s (Fin n), Bar.d (Ipres K E c hc r) (Fin n) z = 0 →
        ∃ w ∈ 𝒱P (s + 1) (Fin n), Bar.d (Ipres K E c hc r) (Fin n) w = z := by
  refine (isKoszul_iff_toBar_fin c hc r hr).trans (forall_congr' fun n =>
    imp_congr_right fun hn => (Homology.map_zero_bijective_iff _ _).trans ?_)
  exact Bar.elem_iff_deg (Ipres K E c hc r) (GrOperadIdeal.atLeastTwo_hI1 (pres_zero c hc r))
    ((Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app (Fin n))
    (toBar_mem_vx c hc r (by omega))

include hr2 in
/-- **The Koszul criterion for binary quadratic data, on the cycles**: for relators with at least
three inputs, over a field of characteristic zero, `P` is Koszul iff for every `n ≥ 2` the
comparison morphism `P^¡(n) → B(P, Ī_P)(n)` maps onto the cycles with `n - 1` vertices, and every
cycle with `s + 1 < n` vertices is the boundary of one with `s + 1`. -/
theorem isKoszul_iff_cycles :
    Koszul.IsKoszul K E r ↔ ∀ n, 2 ≤ n →
      (∀ z ∈ 𝒱P (n - 1) (Fin n), Bar.d (Ipres K E c hc r) (Fin n) z = 0 →
        ∃ x, (Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app (Fin n) x = z) ∧
      ∀ s, s + 1 < n → ∀ z ∈ 𝒱P s (Fin n), Bar.d (Ipres K E c hc r) (Fin n) z = 0 →
        ∃ w ∈ 𝒱P (s + 1) (Fin n), Bar.d (Ipres K E c hc r) (Fin n) w = z :=
  (isKoszul_iff_deg c hc r fun n hn => hr2 n (by omega)).trans (forall_congr' fun n =>
    imp_congr_right fun _ => and_iff_right (dualToBar_injective c hc r hr2 (Fin n)))

end ShuffleBarSym

end Operad
