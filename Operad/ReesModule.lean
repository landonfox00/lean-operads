/-
# The Rees module of a space filtered by weight

A weight `W` on a finite set `α` filters the functions `α → K` by weight (`Graded.IsBelowF`), and
a subspace `V` by `F_N V = {v ∈ V | v has no component of weight above N}`. **The Rees module** of
`V` (`Graded.rees`) is the `K[X]`-module `⊕_N F_N V · X^N`, realized inside `α → K[X]`: a function
`f` lies in it when, for every `N`, the vector of the coefficients of `X^{N - W a}` in the `f a`
lies in `V` (`Graded.coeffVec`). It contains the homogenizations `a ↦ X^{N - W a} v(a)` of the
`v ∈ F_N V` (`Graded.homog_mem_rees`) and every element is a sum of them (`Graded.eq_sum_homog`).

* **Its fibers** under the evaluations `X ↦ c` (`Graded.evalAt`): at `c = 1` the space `V` itself
  (`Graded.evalAt_rees_one`), at `c = 0` its associated graded (`Graded.evalAt_rees_zero`), and at
  `c ≠ 0` the space rescaled by `c^{-W}` (`Graded.evalAt_rees_of_ne_zero`).
* **It is flat**: an element vanishing at `X = c` is `(X - c)` times an element of the module, for
  every `c` (`Graded.exists_eq_smul_of_evalAt_eq_zero`), so the fiber of the module at `c` is its
  image; and it is a free `K[X]`-module (`Graded.free_rees`).
-/
import Operad.ShuffleGradedDual
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.LinearCombination

universe u

namespace Operad

namespace Graded

open Polynomial Module

section Rees

variable {α : Type*} [Fintype α] {K : Type u} [Field K] (W : α → ℕ)

/-- **The homogenization of `v` in degree `N`**: `a ↦ X^{N - W a} v(a)`. -/
noncomputable def homog (N : ℕ) (v : α → K) : α → K[X] := fun a => monomial (N - W a) (v a)

/-- **The coefficients of `X^{N - W a}`**, a function on `α`. -/
noncomputable def coeffVec (N : ℕ) (f : α → K[X]) : α → K :=
  fun a => if W a ≤ N then (f a).coeff (N - W a) else 0

omit [Fintype α] in
lemma coeffVec_isBelowF (N : ℕ) (f : α → K[X]) : IsBelowF K W N (coeffVec W N f) :=
  fun a ha => by simp [coeffVec, not_le.2 ha]

omit [Fintype α] in
lemma coeffVec_add (N : ℕ) (f g : α → K[X]) :
    coeffVec W N (f + g) = coeffVec W N f + coeffVec W N g := by
  funext a
  simp only [coeffVec, Pi.add_apply, coeff_add]
  split_ifs <;> simp

omit [Fintype α] in
lemma coeffVec_X_smul_succ (N : ℕ) (f : α → K[X]) :
    coeffVec W (N + 1) ((X : K[X]) • f) = coeffVec W N f := by
  funext a
  simp only [coeffVec, Pi.smul_apply, smul_eq_mul]
  by_cases h : W a ≤ N
  · rw [if_pos (by omega), if_pos h, show N + 1 - W a = (N - W a) + 1 by omega, coeff_X_mul]
  · by_cases h' : W a = N + 1
    · rw [if_pos (by omega), if_neg h, show N + 1 - W a = 0 by omega, mul_coeff_zero, coeff_X_zero,
        zero_mul]
    · rw [if_neg (by omega), if_neg h]

omit [Fintype α] in
lemma coeffVec_X_smul_zero (f : α → K[X]) : coeffVec W 0 ((X : K[X]) • f) = 0 := by
  funext a
  simp only [coeffVec, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  split_ifs
  · rw [show 0 - W a = 0 by omega, mul_coeff_zero, coeff_X_zero, zero_mul]
  · rfl

omit [Fintype α] in
lemma coeffVec_C_smul (N : ℕ) (c : K) (f : α → K[X]) :
    coeffVec W N (C c • f) = c • coeffVec W N f := by
  funext a
  simp only [coeffVec, Pi.smul_apply, smul_eq_mul, coeff_C_mul]
  split_ifs <;> simp

variable (K) in
/-- **The Rees module** of `V` for the filtration by weight: the functions `α → K[X]` whose
coefficient vectors `coeffVec N` lie in `V`. -/
noncomputable def rees (V : Submodule K (α → K)) : Submodule K[X] (α → K[X]) where
  carrier := {f | ∀ N, coeffVec W N f ∈ V}
  add_mem' {f g} hf hg N := by
    show coeffVec W N (f + g) ∈ V
    rw [coeffVec_add]
    exact add_mem (hf N) (hg N)
  zero_mem' N := by
    have : coeffVec W N (0 : α → K[X]) = 0 := by
      funext a
      simp [coeffVec]
    rw [this]
    exact zero_mem _
  smul_mem' p f hf := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      intro N
      rw [add_smul, coeffVec_add]
      exact add_mem (hp N) (hq N)
    | monomial k c =>
      have hX : ∀ (k : ℕ) (g : α → K[X]), (∀ N, coeffVec W N g ∈ V) →
          ∀ N, coeffVec W N ((X : K[X]) ^ k • g) ∈ V := by
        intro k
        induction k with
        | zero => intro g hg; simpa using hg
        | succ k ih =>
          intro g hg N
          rw [pow_succ', mul_smul]
          rcases N with _ | N
          · rw [coeffVec_X_smul_zero]
            exact zero_mem _
          · rw [coeffVec_X_smul_succ]
            exact ih g hg N
      intro N
      rw [← C_mul_X_pow_eq_monomial, mul_smul, coeffVec_C_smul]
      exact Submodule.smul_mem _ c (hX k f hf N)

variable {W}

omit [Fintype α] in
lemma mem_rees {V : Submodule K (α → K)} {f : α → K[X]} :
    f ∈ rees K W V ↔ ∀ N, coeffVec W N f ∈ V := Iff.rfl

omit [Fintype α] in
lemma coeffVec_homog {N M : ℕ} {v : α → K} (hv : IsBelowF K W N v) :
    coeffVec W M (homog W N v) = if M = N then v else 0 := by
  funext a
  have hva : ¬ W a ≤ N → v a = 0 := fun h => hv a (by omega)
  by_cases hMN : M = N
  · subst hMN
    simp only [coeffVec, homog, coeff_monomial, if_true]
    by_cases h : W a ≤ M
    · simp [h]
    · simp [h, hva h]
  · simp only [coeffVec, homog, coeff_monomial, if_neg hMN, Pi.zero_apply]
    by_cases h1 : W a ≤ M
    · rw [if_pos h1]
      by_cases h2 : N - W a = M - W a
      · rw [if_pos h2]
        exact hva (by omega)
      · rw [if_neg h2]
    · rw [if_neg h1]

omit [Fintype α] in
/-- **The homogenizations lie in the Rees module.** -/
lemma homog_mem_rees {V : Submodule K (α → K)} {N : ℕ} {v : α → K} (hvV : v ∈ V)
    (hv : IsBelowF K W N v) : homog W N v ∈ rees K W V := fun M => by
  rw [coeffVec_homog hv]
  split_ifs
  · exact hvV
  · exact zero_mem _

omit [Fintype α] in
/-- **Every element is the sum of its homogeneous components.** -/
lemma eq_sum_homog (f : α → K[X]) {T : ℕ} (hT : ∀ a, (f a).natDegree + W a ≤ T) :
    f = ∑ N ∈ Finset.range (T + 1), homog W N (coeffVec W N f) := by
  funext a
  ext k
  simp only [Finset.sum_apply, finsetSum_coeff, homog, coeff_monomial, coeffVec]
  rw [Finset.sum_eq_single (k + W a)]
  · simp
  · intro N _ hN
    by_cases h1 : N - W a = k
    · rw [if_pos h1]
      by_cases h2 : W a ≤ N
      · omega
      · rw [if_neg h2]
    · rw [if_neg h1]
  · intro hk
    rw [Finset.mem_range, not_lt] at hk
    have : (f a).natDegree < k := by have := hT a; omega
    simp [coeff_eq_zero_of_natDegree_lt this]

lemma exists_bound (f : α → K[X]) : ∃ T, ∀ a, (f a).natDegree + W a ≤ T :=
  ⟨Finset.univ.sup fun a => (f a).natDegree + W a, fun a =>
    Finset.le_sup (f := fun a => (f a).natDegree + W a) (Finset.mem_univ a)⟩

/-! ## The fibers -/

variable (K) in
/-- **The evaluation at `X = c`.** -/
noncomputable def evalAt (c : K) : (α → K[X]) →ₗ[K] (α → K) where
  toFun f a := (f a).eval c
  map_add' f g := by
    funext a
    simp
  map_smul' r f := by
    funext a
    simp

omit [Fintype α] in
lemma evalAt_apply (c : K) (f : α → K[X]) (a : α) : evalAt K c f a = (f a).eval c := rfl

omit [Fintype α] in
lemma evalAt_homog (c : K) (N : ℕ) (v : α → K) (a : α) :
    evalAt K c (homog W N v) a = c ^ (N - W a) * v a := by
  simp [evalAt_apply, homog, eval_monomial, mul_comm]

/-- The image of the Rees module under an evaluation. -/
noncomputable def fiber (V : Submodule K (α → K)) (c : K) : Submodule K (α → K) :=
  ((rees K W V).restrictScalars K).map (evalAt K c)

omit [Fintype α] in
lemma evalAt_eq_sum (c : K) (f : α → K[X]) {T : ℕ} (hT : ∀ a, (f a).natDegree + W a ≤ T) :
    evalAt K c f = ∑ N ∈ Finset.range (T + 1), evalAt K c (homog W N (coeffVec W N f)) := by
  conv_lhs => rw [eq_sum_homog f hT]
  rw [map_sum]

/-- **The fiber at `X = 1` is the space.** -/
theorem evalAt_rees_one (V : Submodule K (α → K)) : fiber (W := W) V 1 = V := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨T, hT⟩ := exists_bound (W := W) f
    rw [evalAt_eq_sum 1 f hT]
    refine Submodule.sum_mem _ fun N _ => ?_
    have : evalAt K 1 (homog W N (coeffVec W N f)) = coeffVec W N f := by
      funext a
      rw [evalAt_homog, one_pow, one_mul]
    rw [this]
    exact hf N
  · intro v hv
    refine ⟨homog W (Finset.univ.sup W) v,
      homog_mem_rees hv fun a ha => absurd (Finset.le_sup (Finset.mem_univ a)) (not_le.2 ha), ?_⟩
    funext a
    rw [evalAt_homog, one_pow, one_mul]

/-- **The fiber at `X = 0` is the associated graded.** -/
theorem evalAt_rees_zero (V : Submodule K (α → K)) : fiber (W := W) V 0 = grF K W V := by
  have hproj : ∀ (N : ℕ) (v : α → K), IsBelowF K W N v →
      evalAt K 0 (homog W N v) = projF K W N v := by
    intro N v hv
    funext a
    rw [evalAt_homog, projF_apply]
    by_cases ha : W a = N
    · rw [if_pos ha, show N - W a = 0 by omega, pow_zero, one_mul]
    · rw [if_neg ha]
      by_cases hlt : W a < N
      · rw [zero_pow (by omega), zero_mul]
      · rw [hv a (by omega), mul_zero]
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨T, hT⟩ := exists_bound (W := W) f
    rw [evalAt_eq_sum 0 f hT]
    refine Submodule.sum_mem _ fun N _ => ?_
    rw [hproj N _ (coeffVec_isBelowF W N f)]
    exact projF_mem_grF (hf N) (coeffVec_isBelowF W N f)
  · refine grF_le fun N v hv hN => ?_
    rw [← hproj N v hN]
    exact ⟨_, homog_mem_rees hv hN, rfl⟩

variable (W) in
/-- **The rescaling by `c^{-W}`.** -/
noncomputable def scaleInv (c : K) : (α → K) →ₗ[K] (α → K) where
  toFun v a := c⁻¹ ^ W a * v a
  map_add' v w := by
    funext a
    simp [mul_add]
  map_smul' r v := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- **The fiber at `X = c ≠ 0` is the space rescaled by `c^{-W}`.** -/
theorem evalAt_rees_of_ne_zero (V : Submodule K (α → K)) {c : K} (hc : c ≠ 0) :
    fiber (W := W) V c = V.map (scaleInv W c) := by
  have hscale : ∀ (N : ℕ) (v : α → K), IsBelowF K W N v →
      evalAt K c (homog W N v) = c ^ N • scaleInv W c v := by
    intro N v hv
    funext a
    rw [evalAt_homog, Pi.smul_apply, smul_eq_mul]
    show c ^ (N - W a) * v a = c ^ N * (c⁻¹ ^ W a * v a)
    by_cases ha : W a ≤ N
    · rw [pow_sub₀ c hc ha, inv_pow]
      ring
    · rw [hv a (by omega), mul_zero, mul_zero, mul_zero]
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨T, hT⟩ := exists_bound (W := W) f
    rw [evalAt_eq_sum c f hT]
    refine Submodule.sum_mem _ fun N _ => ?_
    rw [hscale N _ (coeffVec_isBelowF W N f)]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (hf N))
  · rintro _ ⟨v, hv, rfl⟩
    have hB : IsBelowF K W (Finset.univ.sup W) v := fun a ha =>
      absurd (Finset.le_sup (Finset.mem_univ a)) (not_le.2 ha)
    refine ⟨(c ^ Finset.univ.sup W)⁻¹ • homog W (Finset.univ.sup W) v,
      Submodule.smul_of_tower_mem _ _ (homog_mem_rees hv hB), ?_⟩
    rw [LinearMap.map_smul_of_tower, hscale _ v hB, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hc),
      one_smul]

/-! ## Flatness -/

omit [Fintype α] in
/-- Multiplying a homogenization by a power of `X` raises its degree. -/
lemma X_pow_smul_homog {N T : ℕ} (hNT : N ≤ T) {v : α → K} (hv : IsBelowF K W N v) :
    (X : K[X]) ^ (T - N) • homog W N v = homog W T v := by
  funext a
  simp only [Pi.smul_apply, smul_eq_mul, homog]
  by_cases ha : W a ≤ N
  · rw [X_pow_mul_monomial, show N - W a + (T - N) = T - W a by omega]
  · rw [hv a (by omega), monomial_zero_right, monomial_zero_right, mul_zero]

omit [Fintype α] in
lemma homog_add (N : ℕ) (v w : α → K) : homog W N (v + w) = homog W N v + homog W N w := by
  funext a
  simp [homog]

omit [Fintype α] in
lemma homog_smul (N : ℕ) (r : K) (v : α → K) : homog W N (r • v) = C r • homog W N v := by
  funext a
  simp [homog, C_mul_monomial]

omit [Fintype α] in
lemma homog_sum {ι : Type*} (s : Finset ι) (N : ℕ) (v : ι → α → K) :
    homog W N (∑ i ∈ s, v i) = ∑ i ∈ s, homog W N (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext a
    simp [homog]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, homog_add, ih]

omit [Fintype α] in
lemma scaleInv_injective {c : K} (hc : c ≠ 0) : Function.Injective (scaleInv W c) := by
  intro v w h
  funext a
  have := congrFun h a
  simp only [scaleInv, LinearMap.coe_mk, AddHom.coe_mk] at this
  exact mul_left_cancel₀ (pow_ne_zero _ (inv_ne_zero hc)) this

/-- **An element of the Rees module vanishing at `X = c` is `(X - c)` times an element of the
Rees module**: the Rees module is flat over `K[X]`, its fiber at `c` being its image. -/
theorem exists_eq_smul_of_evalAt_eq_zero {V : Submodule K (α → K)} {f : α → K[X]}
    (hf : f ∈ rees K W V) (c : K) (h0 : evalAt K c f = 0) :
    ∃ g ∈ rees K W V, f = (X - C c) • g := by
  by_cases hc : c = 0
  · subst hc
    have h0a : ∀ a, (f a).coeff 0 = 0 := fun a => by
      rw [coeff_zero_eq_eval_zero, ← evalAt_apply, h0]
      rfl
    refine ⟨fun a => (f a).divX, fun N => ?_, ?_⟩
    · have : coeffVec W N (fun a => (f a).divX) = coeffVec W (N + 1) f := by
        funext a
        simp only [coeffVec, coeff_divX]
        by_cases h : W a ≤ N
        · rw [if_pos h, if_pos (by omega), show N + 1 - W a = N - W a + 1 by omega]
        · by_cases h' : W a = N + 1
          · rw [if_neg h, if_pos (by omega), show N + 1 - W a = 0 by omega, h0a]
          · rw [if_neg h, if_neg (by omega)]
      rw [this]
      exact hf (N + 1)
    · funext a
      simp only [Pi.smul_apply, smul_eq_mul, map_zero, sub_zero]
      conv_lhs => rw [← X_mul_divX_add (f a), h0a, map_zero, add_zero]
  · obtain ⟨T, hT⟩ := exists_bound (W := W) f
    have hv : ∀ N, IsBelowF K W N (coeffVec W N f) := fun N => coeffVec_isBelowF W N f
    have hscale : ∀ (N : ℕ) (v : α → K), IsBelowF K W N v →
        evalAt K c (homog W N v) = c ^ N • scaleInv W c v := by
      intro N v hv
      funext a
      rw [evalAt_homog, Pi.smul_apply, smul_eq_mul]
      show c ^ (N - W a) * v a = c ^ N * (c⁻¹ ^ W a * v a)
      by_cases ha : W a ≤ N
      · rw [pow_sub₀ c hc ha, inv_pow]
        ring
      · rw [hv a (by omega), mul_zero, mul_zero, mul_zero]
    have hsum : ∑ N ∈ Finset.range (T + 1), c ^ N • coeffVec W N f = 0 := by
      have h1 := evalAt_eq_sum c f hT
      rw [h0] at h1
      rw [Finset.sum_congr rfl fun N _ => hscale N _ (hv N)] at h1
      apply scaleInv_injective (W := W) hc
      rw [map_sum, map_zero]
      simpa only [map_smul] using h1.symm
    -- the cofactor of each homogeneous component
    set q : ℕ → K[X] := fun N => -C (c ^ (T - N))⁻¹ *
      ∑ i ∈ Finset.range (T - N), X ^ i * C c ^ (T - N - 1 - i) with hq
    have hqX : ∀ N, (X - C c) * q N = 1 - C (c ^ (T - N))⁻¹ * X ^ (T - N) := by
      intro N
      have hg := geom_sum₂_mul (X : K[X]) (C c) (T - N)
      rw [mul_comm] at hg
      have hu : C (c ^ (T - N))⁻¹ * C c ^ (T - N) = (1 : K[X]) := by
        rw [← C_pow, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hc), C_1]
      rw [hq]
      dsimp only
      linear_combination (-C (c ^ (T - N))⁻¹) * hg + hu
    have hzero : ∑ N ∈ Finset.range (T + 1),
        C (c ^ (T - N))⁻¹ • (X : K[X]) ^ (T - N) • homog W N (coeffVec W N f) = 0 := by
      have : ∀ N ∈ Finset.range (T + 1),
          C (c ^ (T - N))⁻¹ • (X : K[X]) ^ (T - N) • homog W N (coeffVec W N f) =
            homog W T ((c ^ T)⁻¹ • c ^ N • coeffVec W N f) := by
        intro N hN
        rw [Finset.mem_range] at hN
        rw [X_pow_smul_homog (by omega) (hv N), ← homog_smul, smul_smul,
          pow_sub₀ c hc (by omega : N ≤ T), mul_inv, inv_inv]
      rw [Finset.sum_congr rfl this, ← homog_sum, ← Finset.smul_sum, hsum, smul_zero]
      funext a
      simp [homog]
    have hterm : ∀ N, (X - C c) • q N • homog W N (coeffVec W N f) = homog W N (coeffVec W N f) -
        C (c ^ (T - N))⁻¹ • (X : K[X]) ^ (T - N) • homog W N (coeffVec W N f) := by
      intro N
      rw [smul_smul, hqX, sub_smul, one_smul, mul_smul]
    refine ⟨∑ N ∈ Finset.range (T + 1), q N • homog W N (coeffVec W N f),
      Submodule.sum_mem _ fun N _ => Submodule.smul_mem _ _ (homog_mem_rees (hf N) (hv N)), ?_⟩
    rw [Finset.smul_sum, Finset.sum_congr rfl fun N _ => hterm N, Finset.sum_sub_distrib, hzero,
      sub_zero]
    exact eq_sum_homog f hT

/-! ## Freeness and rank -/

omit [Fintype α] in
lemma evalAt_smul (c : K) (p : K[X]) (f : α → K[X]) :
    evalAt K c (p • f) = p.eval c • evalAt K c f := by
  funext a
  simp [evalAt_apply]

/-- **The Rees module is a free `K[X]`-module.** -/
theorem free_rees (V : Submodule K (α → K)) : Module.Free K[X] (rees K W V) :=
  inferInstance

/-- **The rank of the Rees module is the dimension of each of its fibers**: the values at `X = c`
of a basis form a basis of the fiber at `c`. -/
theorem finrank_rees (V : Submodule K (α → K)) (c : K) :
    Module.finrank K[X] (rees K W V) = Module.finrank K (fiber (W := W) V c) := by
  set M := rees K W V
  let b := Module.finBasis K[X] M
  let v : Fin (Module.finrank K[X] M) → (α → K) := fun i => evalAt K c (b i : α → K[X])
  have hspan : Submodule.span K (Set.range v) = fiber (W := W) V c := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, (b i).2, rfl⟩
    · rintro _ ⟨f, hf, rfl⟩
      have hf' : f = ∑ i, b.repr ⟨f, hf⟩ i • (b i : α → K[X]) := by
        have h := congrArg Subtype.val (b.sum_repr ⟨f, hf⟩)
        rw [Submodule.coe_sum] at h
        simp only [Submodule.coe_smul] at h
        exact h.symm
      rw [hf', map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [evalAt_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hmem : (∑ i, C (a i) • (b i : α → K[X])) ∈ M :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2
    have h0 : evalAt K c (∑ i, C (a i) • (b i : α → K[X])) = 0 := by
      rw [map_sum]
      simpa [evalAt_smul, v] using ha
    obtain ⟨g, hg, hfg⟩ := exists_eq_smul_of_evalAt_eq_zero hmem c h0
    have hM : (∑ i, C (a i) • b i : M) = (X - C c) • (⟨g, hg⟩ : M) :=
      Subtype.ext (by simpa using hfg)
    have hrepr := congrArg (fun m => b.repr m i) hM
    simp only [b.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at hrepr
    simpa using congrArg (eval c) hrepr
  rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]

/-! ## Polynomial sections -/

variable (K) in
/-- **The polynomial sections of a family of subspaces** `U c ⊆ K^α`, `c ∈ K`: the functions
`α → K[X]` whose value at every `X = c` lies in `U c`. -/
noncomputable def sections (U : K → Submodule K (α → K)) : Submodule K[X] (α → K[X]) where
  carrier := {f | ∀ c, evalAt K c f ∈ U c}
  add_mem' hf hg c := by
    rw [map_add]
    exact add_mem (hf c) (hg c)
  zero_mem' c := by
    rw [map_zero]
    exact zero_mem _
  smul_mem' p f hf c := by
    rw [evalAt_smul]
    exact Submodule.smul_mem _ _ (hf c)

omit [Fintype α] in
lemma mem_sections {U : K → Submodule K (α → K)} {f : α → K[X]} :
    f ∈ sections K U ↔ ∀ c, evalAt K c f ∈ U c := Iff.rfl

/-- **A polynomial with coefficients in `K^α` whose values at infinitely many points lie in `V`
has its coefficients in `V`.** -/
lemma coeff_mem_of_evalAt_mem {V : Submodule K (α → K)} {g : α → K[X]} {S : Set K}
    (hS : S.Infinite) (h : ∀ c ∈ S, evalAt K c g ∈ V) (N : ℕ) :
    (fun a => (g a).coeff N) ∈ V := by
  classical
  by_contra hN
  obtain ⟨φ, hφ, hV⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hN inferInstance
  have hφV : ∀ v ∈ V, φ v = 0 := fun v hv => by
    have : φ v ∈ V.map φ := Submodule.mem_map_of_mem hv
    rwa [hV, Submodule.mem_bot] at this
  set P : K[X] := ∑ a, C (φ fun j => if a = j then 1 else 0) * g a with hP
  have hevalP : ∀ c, P.eval c = φ (evalAt K c g) := fun c => by
    rw [LinearMap.pi_apply_eq_sum_univ, hP, eval_finsetSum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [eval_mul, eval_C, evalAt_apply, smul_eq_mul, mul_comm]
  have hP0 : P = 0 := by
    refine eq_zero_of_infinite_isRoot P (hS.mono fun c hc => ?_)
    show P.eval c = 0
    rw [hevalP]
    exact hφV _ (h c hc)
  have hcoeffP : P.coeff N = φ (fun a => (g a).coeff N) := by
    rw [LinearMap.pi_apply_eq_sum_univ, hP, finsetSum_coeff]
    exact Finset.sum_congr rfl fun a _ => by rw [coeff_C_mul, smul_eq_mul, mul_comm]
  apply hφ
  rw [← hcoeffP, hP0, coeff_zero]

/-- **Membership in the Rees module is tested on the fibers away from `0`**, over an infinite
field. -/
theorem mem_rees_iff_evalAt [Infinite K] {V : Submodule K (α → K)} {f : α → K[X]} :
    f ∈ rees K W V ↔ ∀ c : K, c ≠ 0 → evalAt K c f ∈ V.map (scaleInv W c) := by
  constructor
  · intro hf c hc
    rw [← evalAt_rees_of_ne_zero V hc]
    exact ⟨f, hf, rfl⟩
  · intro h N
    have hcoeff : coeffVec W N f = fun a => ((X : K[X]) ^ W a * f a).coeff N := by
      funext a
      rw [coeff_X_pow_mul']
      rfl
    rw [hcoeff]
    refine coeff_mem_of_evalAt_mem (Set.finite_singleton (0 : K)).infinite_compl
      (fun c hc => ?_) N
    obtain ⟨v, hv, hvf⟩ := h c (Set.mem_compl_singleton_iff.1 hc)
    have hcg : evalAt K c (fun a => (X : K[X]) ^ W a * f a) = v := by
      funext a
      have h1 := congrFun hvf a
      simp only [scaleInv, LinearMap.coe_mk, AddHom.coe_mk] at h1
      rw [evalAt_apply, eval_mul, eval_pow, eval_X, ← evalAt_apply, ← h1, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ (Set.mem_compl_singleton_iff.1 hc), one_pow, one_mul]
    rw [hcg]
    exact hv

/-- **The Rees module is the module of polynomial sections of its family of fibers**, over an
infinite field. -/
theorem sections_fiber [Infinite K] (V : Submodule K (α → K)) :
    sections K (fun c => fiber (W := W) V c) = rees K W V := by
  ext f
  constructor
  · intro hf
    refine mem_rees_iff_evalAt.2 fun c hc => ?_
    rw [← evalAt_rees_of_ne_zero V hc]
    exact hf c
  · intro hf c
    exact ⟨f, hf, rfl⟩

end Rees

end Graded

end Operad
