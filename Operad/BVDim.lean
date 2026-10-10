/-
# The BV operad has at most `2ⁿ n!` operations of arity `n`

Inserting the operator at the inputs of a list (`BVGer.Rl`) only depends on the set of inputs, up
to a scalar (`BVGer.Rl_perm`, `BVGer.Rl_toFinset`): the insertions anticommute and square to
zero. So every operation of `BV` is a sum over the subsets of the inputs of operations of `Ger`
with the operator at the inputs of the subset (`BVGer.spanMap_surjective`), and
`dim BV(n) ≤ 2ⁿ dim Ger(n) = 2ⁿ n!` (`BVGer.finite_finrank_le`).
-/
import Operad.BVGer
import Operad.GerModel

universe u

namespace Operad

namespace BVGer

open Sym GerBV GrOperad

/-! ## Reordering the operators at the inputs -/

section Reorder

variable {R : Type u} [CommRing R] {A : Type} [Fintype A] [DecidableEq A]

/-- **Reordering the inputs carrying the operator** changes the operation by a scalar. -/
lemma Rl_perm {l l' : List A} (h : l.Perm l') :
    ∃ c : R, ∀ x : BVOp R A, Rl R l x = c • Rl R l' x := by
  induction h with
  | nil => exact ⟨1, fun x => (one_smul _ _).symm⟩
  | cons a _ ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨c, fun x => by rw [Rl_cons, Rl_cons, hc, map_smul]⟩
  | swap a b l =>
    by_cases hab : b = a
    · subst hab
      exact ⟨1, fun x => (one_smul _ _).symm⟩
    · exact ⟨-1, fun x => by
        rw [Rl_cons, Rl_cons, Rl_cons, Rl_cons, rcomp_rcomp_ne _ (par_DB R) hab, neg_one_smul]⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨c₁, h₁⟩ := ih₁
    obtain ⟨c₂, h₂⟩ := ih₂
    exact ⟨c₁ * c₂, fun x => by rw [h₁, h₂, smul_smul]⟩

/-- **The operator at a list of inputs** is a multiple of the operator at the set of inputs: it
vanishes when an input repeats. -/
lemma Rl_toFinset : ∀ l : List A, ∃ c : R, ∀ x : BVOp R A, Rl R l x = c • Rl R l.toFinset.toList x
  | [] => ⟨1, fun x => by simp [Rl_nil]⟩
  | a :: l => by
    obtain ⟨c, hc⟩ := Rl_toFinset l
    by_cases ha : a ∈ l
    · have hm : a ∈ l.toFinset.toList := by simpa using ha
      obtain ⟨c', hc'⟩ := Rl_perm (R := R) (List.perm_cons_erase hm)
      refine ⟨0, fun x => ?_⟩
      rw [Rl_cons, hc, map_smul, hc', map_smul, Rl_cons,
        rcomp_rcomp_self _ (DB_DB R), smul_zero, smul_zero, zero_smul]
    · have hp : (a :: l.toFinset.toList).Perm (a :: l).toFinset.toList := by
        refine (List.perm_ext_iff_of_nodup ?_ (Finset.nodup_toList _)).2 fun b => ?_
        · exact List.nodup_cons.2 ⟨by simpa using ha, Finset.nodup_toList _⟩
        · simp
      obtain ⟨c', hc'⟩ := Rl_perm (R := R) hp
      exact ⟨c * c', fun x => by rw [Rl_cons, hc, map_smul, ← Rl_cons, hc', smul_smul]⟩

end Reorder

/-! ## The dimension -/

variable (K : Type u) [Field K] (A : Type) [Fintype A] [DecidableEq A]

/-- **The operations of `Ger` with the operator at the inputs of each subset.** -/
noncomputable def spanMap : (Finset A → GerOp K A) →ₗ[K] BVOp K A :=
  ∑ s : Finset A, (Rl K s.toList ∘ₗ (gerToBV K).app A) ∘ₗ LinearMap.proj s

lemma spanMap_single (s : Finset A) (q : GerOp K A) :
    spanMap K A (Pi.single s q) = Rl K s.toList ((gerToBV K).app A q) := by
  rw [spanMap, LinearMap.coe_sum, Finset.sum_apply, Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ s) h

/-- **Every operation of `BV` is a sum of operations of `Ger` with the operator at the inputs of
subsets.** -/
theorem spanMap_surjective : Function.Surjective (spanMap K A) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro x _
  refine (Submodule.span_le.2 ?_ : SB K A ≤ LinearMap.range (spanMap K A)) (mem_SB x)
  rintro _ ⟨l, q, -, -, rfl⟩
  obtain ⟨c, hc⟩ := Rl_toFinset (R := K) l
  refine ⟨Pi.single l.toFinset (c • q), ?_⟩
  rw [spanMap_single, map_smul, map_smul, hc]

/-- **The BV operad has at most `2ⁿ n!` operations of arity `n`.** -/
theorem finite_finrank_le [Nonempty A] :
    Module.Finite K (BVOp K A) ∧
      Module.finrank K (BVOp K A) ≤ 2 ^ Fintype.card A * (Fintype.card A).factorial := by
  haveI : Module.Finite K (GerOp K A) := Module.finite_of_finrank_pos (by
    rw [GerDim.finrank_ger_eq K A]
    exact Nat.factorial_pos _)
  haveI : Module.Finite K (BVOp K A) := Module.Finite.of_surjective _ (spanMap_surjective K A)
  refine ⟨inferInstance, ?_⟩
  have h := LinearMap.finrank_range_le (spanMap K A)
  rw [LinearMap.range_eq_top.2 (spanMap_surjective K A), finrank_top,
    Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_finset,
    GerDim.finrank_ger_eq K A, smul_eq_mul] at h
  exact h

end BVGer

end Operad
