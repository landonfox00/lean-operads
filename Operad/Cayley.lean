/-
# Counting rooted forests and rooted trees

A **rooted forest on `U` with root set `K`** (`Cayley.IsForest`) is an endofunction fixing
everything outside `U ∖ K`, mapping `U ∖ K` into `U`, with a depth function decreasing along it
on `U ∖ K`.

* **Removing the roots** (`Cayley.card_fiber`): the forests on `U` with root set `K` whose
  vertices sent into `K` are `J` are the maps `J → K` together with the forests on `U ∖ K` with
  root set `J`.
* **The forest numbers** (`Cayley.card_forests`): there are `k nⁿ⁻ᵏ⁻¹` rooted forests on `n`
  vertices with a given set of `k` roots, `1 ≤ k < n` (`Cayley.forestCount`), by induction on the
  vertices, through the identity `∑ⱼ C(m, j) kʲ c(m, j) = k (m + k)ᵐ⁻¹`
  (`Cayley.sum_choose_forestCount`), from `j C(m, j) = m C(m - 1, j - 1)` and the binomial
  theorem.
* **Cayley's formula for rooted trees** (`Cayley.card_sigma_forests`): summed over the roots,
  there are `nⁿ⁻¹` rooted trees on `n ≥ 1` vertices.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset

namespace Operad

namespace Cayley

/-! ## The binomial identity -/

/-- **The number of rooted forests on `n` labelled vertices with a given set of `k` roots**:
`k nⁿ⁻ᵏ⁻¹`, and `1` for no vertex or no non-root, `0` for no root on a nonempty set. -/
def forestCount (n k : ℕ) : ℕ :=
  if k = 0 then (if n = 0 then 1 else 0) else if k = n then 1 else k * n ^ (n - k - 1)

/-- **The recursion of the forest numbers**: removing the roots, with `k ≥ 1` roots and `m`
non-roots. -/
theorem sum_choose_forestCount (m k : ℕ) (hk : k ≠ 0) :
    ∑ j ∈ Finset.range (m + 1), m.choose j * (k ^ j * forestCount m j) = forestCount (m + k) k := by
  cases m with
  | zero =>
    simp [forestCount, hk]
  | succ m =>
    have hk' : k ≠ m + 1 + k := by omega
    rw [Finset.sum_range_succ', show forestCount (m + 1 + k) k = k * (m + 1 + k) ^ m by
      unfold forestCount
      rw [if_neg hk, if_neg hk']
      congr 2
      omega]
    have h0 : (m + 1).choose 0 * (k ^ 0 * forestCount (m + 1) 0) = 0 := by
      simp [forestCount]
    rw [h0, add_zero]
    have hterm : ∀ i ∈ Finset.range (m + 1),
        (m + 1).choose (i + 1) * (k ^ (i + 1) * forestCount (m + 1) (i + 1))
          = k * (k ^ i * (m + 1) ^ (m - i) * m.choose i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases him : i = m
      · subst him
        simp [forestCount, pow_succ]
        ring
      · have hlt : i < m := by omega
        have hf : forestCount (m + 1) (i + 1) = (i + 1) * (m + 1) ^ (m - i - 1) := by
          unfold forestCount
          rw [if_neg (by omega), if_neg (by omega)]
          congr 2
          omega
        rw [hf]
        have hc := Nat.add_one_mul_choose_eq m i
        have hp : (m + 1) ^ (m - i) = (m + 1) * (m + 1) ^ (m - i - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hp]
        calc (m + 1).choose (i + 1) * (k ^ (i + 1) * ((i + 1) * (m + 1) ^ (m - i - 1)))
            = ((m + 1).choose (i + 1) * (i + 1)) * (k ^ (i + 1) * (m + 1) ^ (m - i - 1)) := by
              ring
          _ = ((m + 1) * m.choose i) * (k ^ (i + 1) * (m + 1) ^ (m - i - 1)) := by
              rw [← hc]
          _ = k * (k ^ i * ((m + 1) * (m + 1) ^ (m - i - 1)) * m.choose i) := by ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    rw [show m + 1 + k = k + (m + 1) by ring, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Nat.cast_id]

/-! ## Forests -/

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **A rooted forest on `U` with root set `K`**: an endofunction fixing everything outside
`U ∖ K`, mapping `U ∖ K` into `U`, with a depth function decreasing along it on `U ∖ K`. -/
def IsForest (U K : Finset A) (f : A → A) : Prop :=
  (∀ a, a ∉ U \ K → f a = a) ∧ (∀ a ∈ U \ K, f a ∈ U) ∧ ∃ d : A → ℕ, ∀ a ∈ U \ K, d (f a) < d a

open Classical in
/-- The rooted forests on `U` with root set `K`. -/
noncomputable def forests (U K : Finset A) : Finset (A → A) :=
  Finset.univ.filter (IsForest U K)

lemma mem_forests {U K : Finset A} {f : A → A} : f ∈ forests U K ↔ IsForest U K f := by
  classical
  unfold forests
  simp

/-- The roots of the forest obtained by removing the roots: the vertices sent into `K`. -/
def firstLayer (U K : Finset A) (f : A → A) : Finset A := (U \ K).filter fun a => f a ∈ K

/-- **A forest on a nonempty set has a root.** -/
lemma forests_empty_roots {U : Finset A} (hU : U.Nonempty) : forests U ∅ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro f hf
  obtain ⟨-, hmem, d, hd⟩ := mem_forests.1 hf
  rw [Finset.sdiff_empty] at hmem hd
  obtain ⟨a, ha, hmin⟩ := U.exists_min_image d hU
  exact absurd (hmin _ (hmem a ha)) (not_le.2 (hd a ha))

lemma forests_empty_empty : forests (∅ : Finset A) ∅ = {id} := by
  ext f
  rw [mem_forests, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -, -⟩
    funext a
    exact h a (by simp)
  · rintro rfl
    exact ⟨fun _ _ => rfl, fun a ha => by simp at ha, ⟨fun _ => 0, fun a ha => by simp at ha⟩⟩

/-- **Removing the roots of a forest**: the forests on `U` with root set `K` whose vertices sent
into `K` are `J` are the maps `J → K` together with the forests on `U ∖ K` with root set `J`. -/
theorem card_fiber {U K J : Finset A} (hKU : K ⊆ U) (hJ : J ⊆ U \ K) :
    ((forests U K).filter fun f => firstLayer U K f = J).card
      = K.card ^ J.card * (forests (U \ K) J).card := by
  classical
  have hcard : ((Finset.univ : Finset (↥J → ↥K)) ×ˢ forests (U \ K) J).card
      = K.card ^ J.card * (forests (U \ K) J).card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_coe,
      Fintype.card_coe]
  have hfl : ∀ {f : A → A} {a : A}, a ∈ firstLayer U K f ↔ a ∈ U \ K ∧ f a ∈ K := fun {f a} =>
    Finset.mem_filter
  have hmemK : ∀ f ∈ (forests U K).filter (fun f => firstLayer U K f = J), ∀ a ∈ J, f a ∈ K := by
    intro f hf a ha
    have hf' := (Finset.mem_filter.1 hf).2
    exact (hfl.1 (hf' ▸ ha)).2
  rw [← hcard]
  refine Finset.card_bij
    (fun f hf => ((fun a => ⟨f a.1, hmemK f hf a.1 a.2⟩), fun a => if a ∈ J then a else f a))
    ?_ ?_ ?_
  · intro f hf
    obtain ⟨hfF, hfJ⟩ := Finset.mem_filter.1 hf
    obtain ⟨h1, h2, d, hd⟩ := mem_forests.1 hfF
    refine Finset.mem_product.2 ⟨Finset.mem_univ _, mem_forests.2 ⟨?_, ?_, d, ?_⟩⟩
    · intro a ha
      by_cases haJ : a ∈ J
      · simp only [haJ, if_true]
      · simp only [haJ, if_false]
        refine h1 a fun ha' => ha (Finset.mem_sdiff.2 ⟨ha', haJ⟩)
    · intro a ha
      obtain ⟨haUK, haJ⟩ := Finset.mem_sdiff.1 ha
      simp only [haJ, if_false]
      refine Finset.mem_sdiff.2 ⟨h2 a haUK, fun hK => haJ ?_⟩
      exact hfJ ▸ hfl.2 ⟨haUK, hK⟩
    · intro a ha
      obtain ⟨haUK, haJ⟩ := Finset.mem_sdiff.1 ha
      simp only [haJ, if_false]
      exact hd a haUK
  · intro f₁ hf₁ f₂ hf₂ h
    simp only [Prod.mk.injEq] at h
    funext a
    by_cases haJ : a ∈ J
    · have := congrArg (fun g : ↥J → ↥K => (g ⟨a, haJ⟩).1) h.1
      exact this
    · have := congrFun h.2 a
      simp only [haJ, if_false] at this
      exact this
  · rintro ⟨g, f'⟩ hgf
    obtain ⟨-, hf'⟩ := Finset.mem_product.1 hgf
    dsimp only at hf'
    obtain ⟨h1, h2, d, hd⟩ := mem_forests.1 hf'
    let f : A → A := fun a => if h : a ∈ J then (g ⟨a, h⟩).1 else f' a
    have hfJ : ∀ a (h : a ∈ J), f a = (g ⟨a, h⟩).1 := fun a h => dif_pos h
    have hfn : ∀ a, a ∉ J → f a = f' a := fun a h => dif_neg h
    have hf'J : ∀ a ∈ J, f' a = a := fun a ha =>
      h1 a fun h' => (Finset.mem_sdiff.1 h').2 ha
    have hF : f ∈ forests U K := by
      refine mem_forests.2 ⟨?_, ?_, fun a => if a ∈ K then 0 else d a + 1, ?_⟩
      · intro a ha
        have haJ : a ∉ J := fun h' => ha (hJ h')
        rw [hfn a haJ]
        exact h1 a fun h' => ha (Finset.mem_sdiff.1 h').1
      · intro a ha
        by_cases haJ : a ∈ J
        · rw [hfJ a haJ]
          exact hKU (g ⟨a, haJ⟩).2
        · rw [hfn a haJ]
          exact (Finset.mem_sdiff.1 (h2 a (Finset.mem_sdiff.2 ⟨ha, haJ⟩))).1
      · intro a ha
        have haK : a ∉ K := (Finset.mem_sdiff.1 ha).2
        by_cases haJ : a ∈ J
        · rw [hfJ a haJ]
          simp only [(g ⟨a, haJ⟩).2, if_true, haK, if_false]
          omega
        · rw [hfn a haJ]
          have hmem := h2 a (Finset.mem_sdiff.2 ⟨ha, haJ⟩)
          have hK' : f' a ∉ K := (Finset.mem_sdiff.1 hmem).2
          simp only [hK', if_false, haK]
          have := hd a (Finset.mem_sdiff.2 ⟨ha, haJ⟩)
          omega
    have hL : firstLayer U K f = J := by
      ext a
      rw [hfl]
      constructor
      · rintro ⟨ha, hK⟩
        by_contra haJ
        rw [hfn a haJ] at hK
        exact (Finset.mem_sdiff.1 (h2 a (Finset.mem_sdiff.2 ⟨ha, haJ⟩))).2 hK
      · intro haJ
        exact ⟨hJ haJ, by rw [hfJ a haJ]; exact (g ⟨a, haJ⟩).2⟩
    refine ⟨f, Finset.mem_filter.2 ⟨hF, hL⟩, ?_⟩
    simp only [Prod.mk.injEq]
    refine ⟨funext fun a => Subtype.ext (hfJ a.1 a.2), funext fun a => ?_⟩
    by_cases haJ : a ∈ J
    · simp only [haJ, if_true]
      exact (hf'J a haJ).symm
    · simp only [haJ, if_false]
      exact hfn a haJ

/-- **The number of rooted forests on `U` with root set `K`.** -/
theorem card_forests :
    ∀ (n : ℕ) (U K : Finset A), U.card = n → K ⊆ U →
      (forests U K).card = forestCount U.card K.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U K hn hKU
    classical
    rcases K.eq_empty_or_nonempty with rfl | hK
    · rcases U.eq_empty_or_nonempty with rfl | hU
      · rw [forests_empty_empty]
        simp [forestCount]
      · rw [forests_empty_roots hU, Finset.card_empty, Finset.card_empty]
        unfold forestCount
        rw [if_pos rfl, if_neg (Finset.card_ne_zero.2 hU)]
    · have hlt : (U \ K).card < n := by
        rw [Finset.card_sdiff_of_subset hKU, ← hn]
        have := Finset.card_pos.2 hK
        have := Finset.card_le_card hKU
        omega
      rw [Finset.card_eq_sum_card_fiberwise (f := firstLayer U K) (t := (U \ K).powerset)
        fun f _ => Finset.mem_powerset.2 (Finset.filter_subset _ _)]
      have hsum : ∀ J ∈ (U \ K).powerset,
          ((forests U K).filter fun f => firstLayer U K f = J).card
            = K.card ^ J.card * forestCount (U \ K).card J.card := by
        intro J hJ
        rw [card_fiber hKU (Finset.mem_powerset.1 hJ),
          ih _ hlt (U \ K) J rfl (Finset.mem_powerset.1 hJ)]
      rw [Finset.sum_congr rfl hsum, Finset.sum_powerset_apply_card
        (f := fun j => K.card ^ j * forestCount (U \ K).card j)]
      simp only [smul_eq_mul]
      rw [sum_choose_forestCount _ _ (Finset.card_ne_zero.2 hK),
        Finset.card_sdiff_of_subset hKU, Nat.sub_add_cancel (Finset.card_le_card hKU)]

/-- **Cayley's formula, for rooted trees**: the number of rooted forests on `n ≥ 1` vertices with
one root, summed over the roots, is `nⁿ⁻¹`. -/
theorem card_sigma_forests [Nonempty A] :
    (Finset.univ.sigma fun r : A => forests Finset.univ {r}).card
      = Fintype.card A ^ (Fintype.card A - 1) := by
  rw [Finset.card_sigma]
  have h : ∀ r ∈ (Finset.univ : Finset A), (forests Finset.univ {r}).card
      = forestCount (Fintype.card A) 1 := fun r _ => by
    rw [card_forests _ _ _ rfl (Finset.subset_univ _), Finset.card_univ, Finset.card_singleton]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hn := Fintype.card_pos (α := A)
  unfold forestCount
  rw [if_neg one_ne_zero]
  by_cases h1 : 1 = Fintype.card A
  · rw [if_pos h1, ← h1]
    norm_num
  · rw [if_neg h1, one_mul, ← pow_succ']
    congr 1
    omega

end Cayley

end Operad
