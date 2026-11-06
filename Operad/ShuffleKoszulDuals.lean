/-
# The Koszul duals of `Com` and `Ass` on the binary shuffle side

`Operad.ShuffleBinCom` and `Operad.ShuffleBinAss` present `Com` and `Ass` as binary shuffle
operads, by relators `ComBin.rel` and `AssBin.rel` of arity three, and prove Koszul the operads of
their Koszul dual relators `Operad.ShuffleBar.dualRel`. This file identifies those dual relators,
and the operads presented on the binary side, arity by arity.

* **Rescaling the generators** by nonzero scalars `λ e` carries the ideal of `R` onto the ideal of
  the rescaled relators `R.map (rescale λ)` in every arity (`ShuffleBar.map_scaleMono_idealOf`),
  so the two presented operads are isomorphic in every arity (`ShuffleBar.quotRescaleEquiv`).
* **`Ass` is self-dual** (`AssBin.dualRel_rel`): the Koszul dual relators of `Ass` are its
  relators rescaled by `x₂x₁ ↦ -x₂x₁` (`AssBin.opScale`). The relators are the differences of the
  two monomials with one word, and on each such pair the sign `chi3` of the pairing and the sign
  of `x₂x₁` agree on exactly one monomial (`AssBin.sign_rule`, checked on the six rules). So the
  operad of the Koszul dual relators is the operad of `Ass` in every arity
  (`AssBin.quotDualEquiv`).
* **The Koszul dual of `Com` is presented by the Jacobi identity** (`ComBin.dualRel_rel`): the
  Koszul dual relators of `Com` are the multiples of `chi3` itself (`ComBin.jac`), the relator
  `μ(μ(0, 1), 2) - μ(μ(0, 2), 1) - μ(0, μ(1, 2))` (`ComBin.jac_eq`), which for a bracket reads
  `[x, [y, z]] = [[x, y], z] - [[x, z], y]`. Its operad is Koszul (`ComBin.isKoszul_jac`). The
  monomials all of whose windows are leading for the Gröbner basis of `Com` are the left combs on
  the leaf `0` (`LTree.leftComb`), one for each arrangement of `1, …, n - 1`
  (`ComBin.full_eq_image`), so **the operad presented by the Jacobi relator has dimension
  `(n - 1)!` in arity `n ≥ 2`** (`ComBin.finrank_quotient_jac`), the dimension of `Lie`.
* **The presented operads, arity by arity.** The ideal of `Com` is the kernel of the augmentation
  (`ComBin.idealOf_eq_ker`), so in every arity `n ≥ 1` the augmentation identifies the operad it
  presents with `Sym.Com K (Fin n) = K` (`ComBin.quotEquiv`). The ideal of `Ass` is the kernel of
  the evaluation to words (`AssBin.idealOf_eq_ker`), and every arrangement of `0, …, n - 1` is the
  word of a left comb on the leaf `0` (`AssBin.exists_ev_eq`), so in every arity `n ≥ 1` the
  evaluation identifies the operad it presents with the span of the arrangements
  (`AssBin.quotEquiv`), of dimension `n!` (`AssBin.finrank_quotient`), the dimension of
  `Sym.Ass K (Fin n)` (`AssBin.finrank_quotient_eq_sym`); so is its Koszul dual
  (`AssBin.finrank_quotient_dualRel`).

On the binary side the presented operad is the family of quotients
`(Mono E n → K) ⧸ idealOf K R n`, with no compositions defined on them. So the identifications
above are linear isomorphisms in each arity, not isomorphisms of shuffle operads with
`Shuf (Sym.Com K)` or `Shuf (Sym.Ass K)` under `SymOperad.toShuffle`; for `Ass` the comparison
with `Sym.Ass` is an equality of dimensions, and no map from the arrangements to the linear orders
is built. The operad presented by the Jacobi relator is not compared with the symmetric
`Operad.Lie`, whose dimensions the library does not compute; the two meet only in the count
`(n - 1)!`.
-/
import Operad.ShuffleBinCom
import Operad.ShuffleBinAss
import Operad.ShuffleReesKD
import Operad.SetHadamard

universe u v

namespace Operad

/-! ## Rescaling the ideal in every arity -/

namespace LTree

variable {E : Type v}

/-- The weight of a tree for scalars cast from the integers is the cast of its integer weight. -/
lemma wt_intCast {K : Type*} [CommRing K] (l : E → ℤ) :
    ∀ t : LTree E, wt (fun e => (l e : K)) t = ((wt l t : ℤ) : K)
  | leaf _ => by simp
  | node e a b => by simp [wt_intCast l a, wt_intCast l b]

end LTree

namespace ShuffleBar

open LTree

variable {E : Type v} [Fintype E] [DecidableEq E] {K : Type u} [Field K]

lemma sum_vecOf_mul' {n : ℕ} {t : LTree E} (ht : t ∈ monomials n) (f : Mono E n → K) :
    ∑ σ, vecOf K n t σ * f σ = f ⟨t, ht⟩ := by
  rw [sum_vecOf_mul, monoVal_of_mem]

omit [Fintype E] [DecidableEq E] in
lemma chi3_cast_mul_self (t : LTree E) : (chi3 t : K) * (chi3 t : K) = 1 := by
  rw [← Int.cast_mul, chi3_sq, Int.cast_one]

lemma scaleMono_vecOf (l : E → K) (n : ℕ) (t : LTree E) :
    scaleMono K l n (vecOf K n t) = wt l t • vecOf K n t := by
  funext m
  show wt l m.1 * vecOf K n t m = wt l t * vecOf K n t m
  by_cases h : m.1 = t
  · rw [h]
  · simp [vecOf, h]

lemma scaleMono_scaleMono (l l' : E → K) (n : ℕ) (x : Mono E n → K) :
    scaleMono K l n (scaleMono K l' n x) = scaleMono K (l * l') n x := by
  funext m
  show wt l m.1 * (wt l' m.1 * x m) = wt (l * l') m.1 * x m
  rw [wt_mul]
  ring

lemma scaleMono_one (n : ℕ) (x : Mono E n → K) : scaleMono K (1 : E → K) n x = x := by
  funext m
  show wt (1 : E → K) m.1 * x m = x m
  rw [wt_one, one_mul]

/-- **Rescaling a substituted relator** gives the substituted rescaled relator, times the weight
of the context. -/
lemma scaleMono_substVec (l : E → K) (n : ℕ) {t : LTree E} {p : List Bool} {s : Bool}
    (he : t.IsEdge p s) : ∃ c : K, ∀ r : Mono E 3 → K,
      scaleMono K l n (substVec K n t p s r) = c • substVec K n t p s (rescale K l r) := by
  obtain ⟨c, hc⟩ := wt_substAt l he
  refine ⟨c, fun r => ?_⟩
  simp only [substVec, map_sum, map_smul, scaleMono_vecOf, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hc σ.1 ((mem_monomials 3 σ.1).1 σ.2).2]
  simp only [rescale, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  ring

theorem map_scaleMono_idealOf_le (l : E → K) (R : Submodule K (Mono E 3 → K)) (n : ℕ) :
    (idealOf K R n).map (scaleMono K l n) ≤ idealOf K (R.map (rescale K l)) n := by
  rw [Submodule.map_le_iff_le_comap, idealOf, Submodule.span_le]
  rintro _ ⟨t, p, s, r, hr, he, rfl⟩
  obtain ⟨c, hc⟩ := scaleMono_substVec l n he
  rw [SetLike.mem_coe, Submodule.mem_comap, hc]
  exact Submodule.smul_mem _ _ (substVec_mem_idealOf K _ t he (Submodule.mem_map_of_mem hr))

/-- **Rescaling the generators carries the ideal of `R` onto that of the rescaled relators**, in
every arity, for nonzero scalars. -/
theorem map_scaleMono_idealOf (l : E → K) (hl : ∀ e, l e ≠ 0) (R : Submodule K (Mono E 3 → K))
    (n : ℕ) : (idealOf K R n).map (scaleMono K l n) = idealOf K (R.map (rescale K l)) n := by
  refine le_antisymm (map_scaleMono_idealOf_le l R n) fun v hv => ⟨scaleMono K l⁻¹ n v, ?_, ?_⟩
  · have h := map_scaleMono_idealOf_le l⁻¹ (R.map (rescale K l)) n (Submodule.mem_map_of_mem hv)
    rwa [map_rescale_inv l hl R] at h
  · rw [scaleMono_scaleMono, show l * l⁻¹ = 1 from funext fun e => mul_inv_cancel₀ (hl e),
      scaleMono_one]

variable (K) in
/-- **The rescaling of the functions on the monomials**, as a linear equivalence. -/
noncomputable def scaleMonoEquiv (l : E → K) (hl : ∀ e, l e ≠ 0) (n : ℕ) :
    (Mono E n → K) ≃ₗ[K] (Mono E n → K) :=
  LinearEquiv.ofLinear (scaleMono K l n) (scaleMono K l⁻¹ n)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, scaleMono_scaleMono,
        show l * l⁻¹ = 1 from funext fun e => mul_inv_cancel₀ (hl e), scaleMono_one,
        LinearMap.id_apply])
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, scaleMono_scaleMono,
        show l⁻¹ * l = 1 from funext fun e => inv_mul_cancel₀ (hl e), scaleMono_one,
        LinearMap.id_apply])

/-- **The operads presented by `R` and by its rescaling are isomorphic in every arity**, through
the rescaling of the monomials. -/
noncomputable def quotRescaleEquiv (l : E → K) (hl : ∀ e, l e ≠ 0)
    (R : Submodule K (Mono E 3 → K)) (n : ℕ) :
    ((Mono E n → K) ⧸ idealOf K R n) ≃ₗ[K]
      ((Mono E n → K) ⧸ idealOf K (R.map (rescale K l)) n) :=
  Submodule.Quotient.equiv _ _ (scaleMonoEquiv K l hl n) (map_scaleMono_idealOf l hl R n)

lemma quotRescaleEquiv_mk (l : E → K) (hl : ∀ e, l e ≠ 0) (R : Submodule K (Mono E 3 → K))
    (n : ℕ) (x : Mono E n → K) :
    quotRescaleEquiv l hl R n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (scaleMono K l n x) := rfl

end ShuffleBar

/-! ## `Ass` is self-dual -/

namespace AssBin

open LTree ShuffleBar AssShGen

/-- **The sign of a generator**: `+1` for `x₁x₂`, `-1` for `x₂x₁`. -/
def opSgn : AssShGen 2 → ℤ
  | mu => 1
  | op => -1

/-- The leading monomial of a rule. -/
def ruleLead (r : Rule) : LTree (AssShGen 2) := lead3 r.1.1.1 r.1.1.2 r.2

/-- The tail of a rule. -/
def ruleTail (r : Rule) : LTree (AssShGen 2) := tail3 r.1.1.1 r.1.1.2 r.2

lemma ruleLead_inj : ∀ r r' : Rule, ruleLead r = ruleLead r' → r = r' := by decide

lemma ruleTail_inj : ∀ r r' : Rule, ruleTail r = ruleTail r' → r = r' := by decide

lemma ruleLead_ne_ruleTail : ∀ r r' : Rule, ruleLead r ≠ ruleTail r' := by decide

/-- **The signs of the two monomials with one word**: `chi3` and the sign of `x₂x₁` disagree
on exactly one of them. -/
lemma sign_rule : ∀ r : Rule,
    chi3 (ruleLead r) * wt opSgn (ruleLead r) + chi3 (ruleTail r) * wt opSgn (ruleTail r) = 0 := by
  decide

lemma cover3 : ∀ e f : AssShGen 2,
    (∃ r : Rule, node e (node f (leaf 0) (leaf 1)) (leaf 2) = ruleLead r ∨
      node e (node f (leaf 0) (leaf 1)) (leaf 2) = ruleTail r) ∧
    (∃ r : Rule, node e (node f (leaf 0) (leaf 2)) (leaf 1) = ruleLead r ∨
      node e (node f (leaf 0) (leaf 2)) (leaf 1) = ruleTail r) ∧
    (∃ r : Rule, node e (leaf 0) (node f (leaf 1) (leaf 2)) = ruleLead r ∨
      node e (leaf 0) (node f (leaf 1) (leaf 2)) = ruleTail r) := by
  decide

/-- **Every monomial of arity three leads a rule or is its tail.** -/
lemma exists_rule (σ : Mono (AssShGen 2) 3) : ∃ r : Rule, σ.1 = ruleLead r ∨ σ.1 = ruleTail r := by
  have hm := (mem_monomials 3 σ.1).1 σ.2
  obtain ⟨e, f, h | h | h⟩ := mono3_cases hm.1 hm.2 <;> rw [h]
  · exact (cover3 e f).1
  · exact (cover3 e f).2.1
  · exact (cover3 e f).2.2

variable (K : Type*) [Field K]

/-- **The rescaling of the generators by their signs**: `x₂x₁ ↦ -x₂x₁`. -/
def opScale : AssShGen 2 → K := fun e => (opSgn e : K)

lemma opScale_ne_zero (e : AssShGen 2) : opScale K e ≠ 0 := by
  cases e <;> simp [opScale, opSgn]

lemma opScale_mul_self : opScale K * opScale K = 1 :=
  funext fun e => by cases e <;> simp [opScale, opSgn]

/-- The relator of a rule: its leading monomial minus its tail. -/
noncomputable def ruleVec (r : Rule) : Mono (AssShGen 2) 3 → K :=
  vecOf K 3 (ruleLead r) - vecOf K 3 (ruleTail r)

lemma rel_eq_span_ruleVec : rel K = Submodule.span K (Set.range (ruleVec K)) := rel_eq_span

variable {K}

lemma ruleLead_mem (r : Rule) : ruleLead r ∈ monomials 3 := lead3_mem _ _ _

lemma ruleTail_mem (r : Rule) : ruleTail r ∈ monomials 3 := tail3_mem _ _ _

lemma ruleVec_lead (r r' : Rule) :
    ruleVec K r ⟨ruleLead r', ruleLead_mem r'⟩ = if r' = r then 1 else 0 := by
  by_cases h : r' = r
  · subst h
    simp [ruleVec, vecOf, ruleLead_ne_ruleTail]
  · have h' : ruleLead r' ≠ ruleLead r := fun h' => h (ruleLead_inj _ _ h')
    simp [ruleVec, vecOf, h, h', ruleLead_ne_ruleTail]

lemma ruleVec_tail (r r' : Rule) :
    ruleVec K r ⟨ruleTail r', ruleTail_mem r'⟩ = if r' = r then -1 else 0 := by
  by_cases h : r' = r
  · subst h
    have h' : ruleTail r' ≠ ruleLead r' := fun h' => ruleLead_ne_ruleTail r' r' h'.symm
    simp [ruleVec, vecOf, h']
  · have h' : ruleTail r' ≠ ruleLead r := fun h' => ruleLead_ne_ruleTail r r' h'.symm
    have h'' : ruleTail r' ≠ ruleTail r := fun h'' => h (ruleTail_inj _ _ h'')
    simp [ruleVec, vecOf, h, h', h'']

/-- **The twisted pairing of the relator of a rule** with a function on the monomials. -/
lemma pair_ruleVec (r : Rule) (y : Mono (AssShGen 2) 3 → K) :
    ∑ σ, (chi3 σ.1 : K) * ruleVec K r σ * y σ =
      (chi3 (ruleLead r) : K) * y ⟨_, ruleLead_mem r⟩ -
        (chi3 (ruleTail r) : K) * y ⟨_, ruleTail_mem r⟩ := by
  have h : ∀ σ, (chi3 σ.1 : K) * ruleVec K r σ * y σ =
      vecOf K 3 (ruleLead r) σ * ((chi3 σ.1 : K) * y σ) -
        vecOf K 3 (ruleTail r) σ * ((chi3 σ.1 : K) * y σ) := fun σ => by
    simp only [ruleVec, Pi.sub_apply]
    ring
  rw [Finset.sum_congr rfl fun σ _ => h σ, Finset.sum_sub_distrib,
    sum_vecOf_mul' (ruleLead_mem r), sum_vecOf_mul' (ruleTail_mem r)]

lemma sign_rule_cast (r : Rule) :
    (chi3 (ruleLead r) : K) * wt (opScale K) (ruleLead r) +
      (chi3 (ruleTail r) : K) * wt (opScale K) (ruleTail r) = 0 := by
  have h := congrArg (fun z : ℤ => (z : K)) (sign_rule r)
  push_cast at h
  rw [show opScale K = fun e => (opSgn e : K) from rfl, wt_intCast, wt_intCast]
  exact h

variable (K) in
/-- **The associative operad is self-dual on the binary shuffle side**: the Koszul dual relators
of `Ass` are its relators rescaled by `x₂x₁ ↦ -x₂x₁`. -/
theorem dualRel_rel : dualRel K (rel K) = (rel K).map (rescale K (opScale K)) := by
  apply le_antisymm
  · intro ρ hρ
    have hρ' : ∀ r, (chi3 (ruleLead r) : K) * ρ ⟨_, ruleLead_mem r⟩ -
        (chi3 (ruleTail r) : K) * ρ ⟨_, ruleTail_mem r⟩ = 0 := fun r => by
      rw [← pair_ruleVec]
      refine hρ _ ?_
      rw [rel_eq_span_ruleVec]
      exact Submodule.subset_span ⟨r, rfl⟩
    set w := rescale K (opScale K) ρ with hw_def
    have hwv : ∀ σ, w σ = wt (opScale K) σ.1 * ρ σ := fun σ => rfl
    have hsum : w = ∑ r, w ⟨_, ruleLead_mem r⟩ • ruleVec K r := by
      funext σ
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      obtain ⟨r0, h | h⟩ := exists_rule σ
      · obtain rfl : σ = ⟨ruleLead r0, ruleLead_mem r0⟩ := Subtype.ext h
        simp only [ruleVec_lead, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          if_true]
      · obtain rfl : σ = ⟨ruleTail r0, ruleTail_mem r0⟩ := Subtype.ext h
        simp only [ruleVec_tail, mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, if_true, hwv]
        have h1 := hρ' r0
        have h2 := sign_rule_cast (K := K) r0
        have h4 := chi3_cast_mul_self (K := K) (ruleLead r0)
        have h5 := chi3_cast_mul_self (K := K) (ruleTail r0)
        linear_combination (-(wt (opScale K) (ruleLead r0) * ρ ⟨_, ruleLead_mem r0⟩)) * h4 +
          (wt (opScale K) (ruleLead r0) * (chi3 (ruleLead r0) : K)) * h1 +
          ((chi3 (ruleTail r0) : K) * ρ ⟨_, ruleTail_mem r0⟩) * h2 -
          (wt (opScale K) (ruleTail r0) * ρ ⟨_, ruleTail_mem r0⟩) * h5
    have hw : w ∈ rel K := by
      rw [hsum, rel_eq_span_ruleVec]
      exact Submodule.sum_mem _ fun r _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
    refine ⟨w, hw, ?_⟩
    show rescale K (opScale K) (rescale K (opScale K) ρ) = ρ
    rw [rescale_rescale, opScale_mul_self, rescale_one]
  · rw [Submodule.map_le_iff_le_comap]
    nth_rewrite 1 [rel_eq_span_ruleVec]
    rw [Submodule.span_le]
    rintro _ ⟨r', rfl⟩
    show rescale K (opScale K) (ruleVec K r') ∈ dualRel K (rel K)
    rw [mem_dualRel]
    intro y hy
    rw [rel_eq_span_ruleVec] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, rfl⟩ := hy
      rw [pair_ruleVec]
      simp only [rescale, LinearMap.coe_mk, AddHom.coe_mk, ruleVec_lead, ruleVec_tail]
      by_cases h : r = r'
      · subst h
        simp only [if_true, mul_one, mul_neg]
        linear_combination sign_rule_cast (K := K) r
      · simp [h]
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib, ha, hb, add_zero]
    | smul c a _ ha =>
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_zero c, ← ha, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring

variable (K) in
/-- **The operad of the Koszul dual relators of `Ass` is the operad of `Ass`**, in every arity,
through the rescaling `x₂x₁ ↦ -x₂x₁` of the monomials. -/
noncomputable def quotDualEquiv (n : ℕ) :
    ((Mono (AssShGen 2) n → K) ⧸ idealOf K (rel K) n) ≃ₗ[K]
      ((Mono (AssShGen 2) n → K) ⧸ idealOf K (dualRel K (rel K)) n) :=
  (quotRescaleEquiv (opScale K) (opScale_ne_zero K) (rel K) n).trans
    (Submodule.quotEquivOfEq _ _ (by rw [dualRel_rel]))

end AssBin

/-! ## Left combs -/

namespace LTree

variable {E : Type v}

/-- **The left comb** on the leaf `a` and a list of decorated leaves, the first of them on top:
`leftComb a ((e, b) :: l) = node e (leftComb a l) (leaf b)`. -/
def leftComb (a : ℕ) : List (E × ℕ) → LTree E
  | [] => leaf a
  | (e, b) :: l => node e (leftComb a l) (leaf b)

/-- A monomial is left-comb-shaped when every second input is a leaf. -/
def IsLeftCombShape : LTree E → Prop
  | leaf _ => True
  | node _ l (leaf _) => l.IsLeftCombShape
  | node _ _ (node _ _ _) => False

lemma labels_leftComb (a : ℕ) :
    ∀ l : List (E × ℕ), (leftComb a l).labels = a :: (l.map Prod.snd).reverse
  | [] => rfl
  | (e, b) :: l => by simp [leftComb, labels_leftComb a l]

lemma isLeftCombShape_leftComb (a : ℕ) : ∀ l : List (E × ℕ), (leftComb a l).IsLeftCombShape
  | [] => trivial
  | (_, _) :: l => isLeftCombShape_leftComb a l

lemma exists_leftComb : ∀ t : LTree E, t.IsLeftCombShape → ∃ a l, t = leftComb a l
  | leaf a, _ => ⟨a, [], rfl⟩
  | node e t (leaf b), h => by
    obtain ⟨a, l, rfl⟩ := exists_leftComb t h
    exact ⟨a, (e, b) :: l, rfl⟩
  | node _ _ (node _ _ _), h => h.elim

lemma minLabel_leftComb (a : ℕ) :
    ∀ l : List (E × ℕ), (∀ p ∈ l, a < p.2) → (leftComb a l).minLabel = a
  | [], _ => rfl
  | (e, b) :: l, h => by
    simp only [leftComb, minLabel_node, minLabel_leaf,
      minLabel_leftComb a l fun p hp => h p (List.mem_cons_of_mem _ hp)]
    exact min_eq_left (h _ List.mem_cons_self).le

lemma isShuffle_leftComb (a : ℕ) :
    ∀ l : List (E × ℕ), (∀ p ∈ l, a < p.2) → (leftComb a l).IsShuffle
  | [], _ => trivial
  | (e, b) :: l, h => by
    have h' : ∀ p ∈ l, a < p.2 := fun p hp => h p (List.mem_cons_of_mem _ hp)
    exact ⟨by rw [minLabel_leftComb a l h']; exact h _ List.mem_cons_self,
      isShuffle_leftComb a l h', trivial⟩

lemma lt_of_isShuffle_leftComb (a : ℕ) :
    ∀ l : List (E × ℕ), (leftComb a l).IsShuffle → ∀ p ∈ l, a < p.2
  | [], _ => by simp
  | (e, b) :: l, h => by
    have ih := lt_of_isShuffle_leftComb a l h.2.1
    have h1 := h.1
    rw [minLabel_leftComb a l ih, minLabel_leaf] at h1
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h1
    · exact ih p hp

/-- **The windows of a left-comb-shaped monomial are windows of edges into the first slot.** -/
theorem windows_mem_of_leftCombShape {L : Set (LTree E)}
    (hL : ∀ e f : E, node e (node f (leaf 0) (leaf 1)) (leaf 2) ∈ L ∧
      node e (node f (leaf 0) (leaf 2)) (leaf 1) ∈ L) :
    ∀ t : LTree E, t.IsShuffle → t.labels.Nodup → t.IsLeftCombShape → ∀ w ∈ t.windows, w ∈ L
  | leaf _, _, _, _ => by simp [windows]
  | node e l (leaf b), hs, hnd, hsh => by
    intro w hw
    simp only [windows, List.mem_append, List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw
    · cases l with
      | leaf _ => simp at hw
      | node f x y =>
        rw [List.mem_singleton] at hw
        subst hw
        rcases window_left_shape hs hnd with h | h <;> rw [h]
        · exact (hL e f).1
        · exact (hL e f).2
    · exact windows_mem_of_leftCombShape hL l hs.2.1 (List.nodup_append.1 hnd).1 hsh w hw
  | node _ _ (node _ _ _), _, _, hsh => hsh.elim

/-- **A monomial all of whose windows lie in a set without right combs is left-comb-shaped.** -/
theorem isLeftCombShape_of_windows_mem {L : Set (LTree E)}
    (hR : ∀ e f : E, node e (leaf 0) (node f (leaf 1) (leaf 2)) ∉ L) :
    ∀ t : LTree E, t.IsShuffle → (∀ w ∈ t.windows, w ∈ L) → t.IsLeftCombShape
  | leaf _, _, _ => trivial
  | node e l (leaf b), hs, h => isLeftCombShape_of_windows_mem hR l hs.2.1 fun w hw =>
      h w (by
        simp only [windows, List.mem_append]
        exact Or.inl (Or.inr hw))
  | node e l (node f x y), hs, h => by
    have hw := h (window e f true x.minLabel y.minLabel l.minLabel) (by simp [windows])
    rw [window_right_eq hs] at hw
    exact (hR e f hw).elim

end LTree

/-! ## The Koszul dual of `Com` is `Lie` -/

namespace ComBin

open LTree ShuffleBar

variable (K : Type*) [Field K]

/-- **The Jacobi relator**: the sign `chi3` on the three monomials of arity three. -/
noncomputable def jac : Mono (ComGen 2) 3 → K := fun σ => (chi3 σ.1 : K)

variable {K}

/-- **The Jacobi relator** `μ(μ(0, 1), 2) - μ(μ(0, 2), 1) - μ(0, μ(1, 2))`: for the bracket,
`[[x, y], z] - [[x, z], y] - [x, [y, z]] = 0`. -/
theorem jac_eq : jac K = vecOf K 3 lcomb - vecOf K 3 tcomb - vecOf K 3 rcomb := by
  funext σ
  simp only [jac, Pi.sub_apply]
  rcases mono3_eq σ with h | h | h <;>
    simp [h, vecOf, lcomb, tcomb, rcomb, chi3]

variable (K) in
/-- **The Koszul dual relators of `Com` are spanned by the Jacobi relator**: the Koszul dual
operad of `Com` is presented by the Jacobi identity, the shuffle presentation of `Lie`. -/
theorem dualRel_rel : dualRel K (rel K) = K ∙ jac K := by
  apply le_antisymm
  · intro ρ hρ
    rw [mem_dualRel] at hρ
    have hpair : ∀ σ τ : Mono (ComGen 2) 3, (chi3 σ.1 : K) * ρ σ = chi3 τ.1 * ρ τ := by
      intro σ τ
      have h := hρ (vecOf K 3 σ.1 - vecOf K 3 τ.1) (by
        rw [rel, LinearMap.mem_ker, map_sub, aug_vecOf σ.2, aug_vecOf τ.2, sub_self])
      have e : ∀ x : Mono (ComGen 2) 3, (chi3 x.1 : K) * (vecOf K 3 σ.1 - vecOf K 3 τ.1) x * ρ x =
          vecOf K 3 σ.1 x * ((chi3 x.1 : K) * ρ x) - vecOf K 3 τ.1 x * ((chi3 x.1 : K) * ρ x) :=
        fun x => by
          simp only [Pi.sub_apply]
          ring
      rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_sub_distrib, sum_vecOf_mul' σ.2,
        sum_vecOf_mul' τ.2] at h
      exact sub_eq_zero.1 h
    set τ₀ : Mono (ComGen 2) 3 := ⟨rcomb, rcomb_mem⟩
    refine Submodule.mem_span_singleton.2 ⟨(chi3 τ₀.1 : K) * ρ τ₀, funext fun σ => ?_⟩
    show (chi3 τ₀.1 : K) * ρ τ₀ * (chi3 σ.1 : K) = ρ σ
    rw [← hpair σ τ₀, mul_comm, ← mul_assoc, chi3_cast_mul_self, one_mul]
  · rw [Submodule.span_singleton_le_iff_mem, mem_dualRel]
    intro r hr
    rw [rel, LinearMap.mem_ker, aug_apply] at hr
    rw [← hr]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [jac]
    linear_combination r σ * chi3_cast_mul_self (K := K) σ.1

/-! ### The dimension of the Koszul dual operad -/

/-- The left comb of `μ` on the leaf `0` and a list of leaves. -/
def lcombOf (l : List ℕ) : LTree (ComGen 2) := leftComb 0 (l.map fun b => (.mu, b))

lemma labels_lcombOf (l : List ℕ) : (lcombOf l).labels = 0 :: l.reverse := by
  simp [lcombOf, labels_leftComb, Function.comp_def]

lemma lcombOf_injective : Function.Injective lcombOf := fun l l' h => by
  have := congrArg labels h
  rw [labels_lcombOf, labels_lcombOf, List.cons_inj_right, List.reverse_inj] at this
  exact this

lemma leads_rcomb (e f : ComGen 2) : node e (leaf 0) (node f (leaf 1) (leaf 2)) ∉ leads := by
  cases e
  cases f
  simp [leads, lcomb, tcomb]

lemma range_eq_cons {n : ℕ} (hn : 1 ≤ n) : List.range n = 0 :: List.range' 1 (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [List.range_eq_range', List.range'_succ]
  simp

/-- **The monomials all of whose windows are leading are the left combs on `0`**: one for each
arrangement of `1, …, n - 1`. -/
theorem full_eq_image {n : ℕ} (hn : 1 ≤ n) :
    {m | m ∈ monomials (E := ComGen 2) n ∧ ShuffleBar.IsFull leads m} =
      lcombOf '' {l | l.Perm (List.range' 1 (n - 1))} := by
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_image, mem_monomials, isFull_iff_windows]
  constructor
  · rintro ⟨⟨hs, hl⟩, hw⟩
    obtain ⟨a, l', rfl⟩ := exists_leftComb m (isLeftCombShape_of_windows_mem leads_rcomb m hs hw)
    have hlt := lt_of_isShuffle_leftComb a l' hs
    rw [labels_leftComb, range_eq_cons hn] at hl
    have ha : a = 0 := by
      have h0 : 0 ∈ a :: (l'.map Prod.snd).reverse := hl.symm.subset List.mem_cons_self
      rcases List.mem_cons.1 h0 with h0 | h0
      · exact h0.symm
      · obtain ⟨p, hp, hp0⟩ := List.mem_map.1 (List.mem_reverse.1 h0)
        exact absurd (hp0 ▸ hlt p hp) (Nat.not_lt_zero a)
    subst ha
    refine ⟨l'.map Prod.snd, (List.reverse_perm _).symm.trans ((List.perm_cons 0).1 hl), ?_⟩
    rw [lcombOf, List.map_map]
    congr 1
    conv_rhs => rw [← List.map_id l']
    exact List.map_congr_left fun p _ => Prod.ext (Subsingleton.elim _ _) rfl
  · rintro ⟨l, hl, rfl⟩
    have hpos : ∀ p ∈ l.map (fun b => ((.mu : ComGen 2), b)), 0 < p.2 := by
      intro p hp
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
      have := List.mem_range'.1 (hl.subset hb)
      simp only
      omega
    have hs : (lcombOf l).IsShuffle := isShuffle_leftComb 0 _ hpos
    have hl' : (lcombOf l).labels.Perm (List.range n) := by
      rw [labels_lcombOf, range_eq_cons hn]
      exact (List.perm_cons 0).2 ((List.reverse_perm _).trans hl)
    exact ⟨⟨hs, hl'⟩, windows_mem_of_leftCombShape leads_spec _ hs
      (hl'.nodup_iff.2 List.nodup_range) (isLeftCombShape_leftComb _ _)⟩

/-- **There are `(n - 1)!` monomials of arity `n` all of whose windows are leading.** -/
theorem ncard_full {n : ℕ} (hn : 1 ≤ n) :
    {m | m ∈ monomials (E := ComGen 2) n ∧ ShuffleBar.IsFull leads m}.ncard =
      (n - 1).factorial := by
  rw [full_eq_image hn, Set.ncard_image_of_injective _ lcombOf_injective,
    show {l : List ℕ | l.Perm (List.range' 1 (n - 1))} =
      ↑(List.range' 1 (n - 1)).permutations.toFinset from by
        ext l
        simp [List.mem_permutations],
    Set.ncard_coe_finset, List.toFinset_card_of_nodup (List.nodup_permutations _ List.nodup_range'),
    List.length_permutations, List.length_range']

variable (K) in
/-- **The Koszul dual operad of `Com` has dimension `(n - 1)!` in arity `n ≥ 2`**, the dimension
of `Lie`. -/
theorem finrank_quotient_dualRel {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank K ((Mono (ComGen 2) n → K) ⧸ idealOf K (dualRel K (rel K)) n) =
      (n - 1).factorial := by
  rw [ShuffleBar.finrank_quotient_dualRel_eq_ncard rk (isGroebner K) hn, ncard_full (by omega)]

variable (K) in
/-- **The shuffle operad presented by the Jacobi relator has dimension `(n - 1)!`** in arity
`n ≥ 2`. -/
theorem finrank_quotient_jac {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank K ((Mono (ComGen 2) n → K) ⧸ idealOf K (K ∙ jac K) n) = (n - 1).factorial := by
  rw [← dualRel_rel, finrank_quotient_dualRel K hn]

variable (K) in
/-- **The shuffle operad presented by the Jacobi relator is Koszul.** -/
theorem isKoszul_jac : ShuffleBar.IsKoszul K (K ∙ jac K) := by
  rw [← dualRel_rel]
  exact isKoszul_dualRel K

end ComBin

/-! ## The presented operads in each arity: `Com` -/

namespace ComBin

open LTree ShuffleBar

variable {K : Type*} [Field K]

/-- **The augmentation is injective on the normal monomials**: a vector supported on them with
coefficient sum zero is zero. -/
lemma eq_zero_of_aug {n : ℕ} {v : Mono (ComGen 2) n → K}
    (hN : v ∈ supportedOn K (normalSet leads n)) (h0 : aug K n v = 0) : v = 0 := by
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, v y ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hyN : IsNormal leads y.1 := by
    by_contra h
    exact hy (hN y h)
  rw [aug_apply, Finset.sum_eq_single y (fun σ _ hσ => ?_) (by simp)] at h0
  · exact hy h0
  · by_contra h
    exact hσ (normal_unique (by by_contra h'; exact h (hN σ h')) hyN)

variable (K) in
/-- **The ideal of `Com` is the kernel of the augmentation** in every arity. -/
theorem idealOf_eq_ker (n : ℕ) : idealOf K (rel K) n = LinearMap.ker (aug K n) := by
  refine le_antisymm (idealOf_le_ker n) fun v hv => ?_
  have hv' : v ∈ idealOf K (rel K) n ⊔ supportedOn K (normalSet leads n) := by
    rw [((isGroebner K).isCompl n).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨i, hi, w, hw, rfl⟩ := Submodule.mem_sup.1 hv'
  rw [LinearMap.mem_ker, map_add, LinearMap.mem_ker.1 (idealOf_le_ker n hi), zero_add] at hv
  rw [eq_zero_of_aug hw hv, add_zero]
  exact hi

lemma lcombOf_mem {n : ℕ} (hn : 1 ≤ n) : lcombOf (List.range' 1 (n - 1)) ∈ monomials n := by
  have h : lcombOf (List.range' 1 (n - 1)) ∈ lcombOf '' {l | l.Perm (List.range' 1 (n - 1))} :=
    ⟨_, List.Perm.refl _, rfl⟩
  rw [← full_eq_image hn] at h
  exact h.1

lemma aug_surjective {n : ℕ} (hn : 1 ≤ n) : Function.Surjective (aug K n) := fun c =>
  ⟨c • vecOf K n (lcombOf (List.range' 1 (n - 1))), by
    rw [map_smul, aug_vecOf (lcombOf_mem hn), smul_eq_mul, mul_one]⟩

variable (K) in
/-- **The operad presented by the relators of `Com` is `Sym.Com` in every arity `n ≥ 1`**: the
augmentation identifies the quotient with `Sym.Com K (Fin n) = K`. -/
noncomputable def quotEquiv {n : ℕ} (hn : 1 ≤ n) :
    ((Mono (ComGen 2) n → K) ⧸ idealOf K (rel K) n) ≃ₗ[K] Sym.Com K (Fin n) :=
  (Submodule.quotEquivOfEq _ _ (idealOf_eq_ker K n)).trans
    (LinearMap.quotKerEquivOfSurjective _ (aug_surjective hn))

lemma quotEquiv_mk {n : ℕ} (hn : 1 ≤ n) (v : Mono (ComGen 2) n → K) :
    quotEquiv K hn (Submodule.Quotient.mk v) = aug K n v := rfl

variable (K) in
/-- **The operad presented by the relators of `Com` is one-dimensional** in every arity `n ≥ 1`. -/
theorem finrank_quotient {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank K ((Mono (ComGen 2) n → K) ⧸ idealOf K (rel K) n) = 1 := by
  rw [(quotEquiv K hn).finrank_eq, Module.finrank_self]

end ComBin

/-! ## The presented operads in each arity: `Ass` -/

namespace AssBin

open LTree ShuffleBar AssShGen

variable {K : Type*} [Field K]

variable (K) in
/-- **The ideal of `Ass` is the kernel of the evaluation to words** in every arity. -/
theorem idealOf_eq_ker (n : ℕ) : idealOf K (rel K) n = LinearMap.ker (evL K n) := by
  refine le_antisymm (idealOf_le_ker n) fun v hv => ?_
  have hv' : v ∈ idealOf K (rel K) n ⊔ supportedOn K (normalSet leads n) := by
    rw [((isGroebner K).isCompl n).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨i, hi, w, hw, rfl⟩ := Submodule.mem_sup.1 hv'
  rw [LinearMap.mem_ker, map_add, LinearMap.mem_ker.1 (idealOf_le_ker n hi), zero_add] at hv
  rw [eq_zero_of_evL hw hv, add_zero]
  exact hi

/-- **The arrangements of `0, …, n - 1`.** -/
noncomputable def arrs (n : ℕ) : Finset (List ℕ) := (List.range n).permutations.toFinset

lemma mem_arrs {n : ℕ} {w : List ℕ} : w ∈ arrs n ↔ w.Perm (List.range n) := by
  rw [arrs, List.mem_toFinset, List.mem_permutations]

lemma card_arrs (n : ℕ) : (arrs n).card = n.factorial := by
  rw [arrs, List.toFinset_card_of_nodup (List.nodup_permutations _ List.nodup_range),
    List.length_permutations, List.length_range]

lemma ev_mem_arrs {n : ℕ} (σ : Mono (AssShGen 2) n) : ev σ.1 ∈ arrs n :=
  mem_arrs.2 ((perm_ev σ.1).trans ((mem_monomials n σ.1).1 σ.2).2)

lemma ev_leftComb_mu (a : ℕ) :
    ∀ l : List ℕ, ev (leftComb a (l.map fun b => (mu, b))) = a :: l.reverse
  | [] => rfl
  | b :: l => by simp [leftComb, ev, ap, ev_leftComb_mu a l]

lemma ev_leftComb_op (a : ℕ) (rest : List (AssShGen 2 × ℕ)) :
    ∀ A : List ℕ, ev (leftComb a (A.map (fun b => (op, b)) ++ rest)) = A ++ ev (leftComb a rest)
  | [] => rfl
  | b :: A => by simp [leftComb, ev, ap, ev_leftComb_op a rest A]

/-- **Every arrangement of `0, …, n - 1` is the word of a monomial**: a left comb on `0`, with
the letters before `0` added through `x₂x₁` and those after it through `x₁x₂`. -/
theorem exists_ev_eq {n : ℕ} (hn : 1 ≤ n) {w : List ℕ} (hw : w.Perm (List.range n)) :
    ∃ σ : Mono (AssShGen 2) n, ev σ.1 = w := by
  have h0 : 0 ∈ w := hw.symm.subset (List.mem_range.2 (by omega))
  obtain ⟨A, B, rfl⟩ := List.append_of_mem h0
  set m : LTree (AssShGen 2) :=
    leftComb 0 (A.map (fun b => (op, b)) ++ B.reverse.map fun b => (mu, b))
  have hev : ev m = A ++ 0 :: B := by
    rw [ev_leftComb_op, ev_leftComb_mu, List.reverse_reverse]
  have hnd : (0 :: (A ++ B)).Nodup := List.nodup_middle.1 (hw.nodup_iff.2 List.nodup_range)
  have hpos : ∀ p ∈ A.map (fun b => (op, b)) ++ B.reverse.map (fun b => (mu, b)), 0 < p.2 := by
    intro p hp
    have hmem : p.2 ∈ A ++ B := by
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
        exact List.mem_append_left _ hb
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
        exact List.mem_append_right _ (List.mem_reverse.1 hb)
    exact Nat.pos_of_ne_zero fun h => (List.nodup_cons.1 hnd).1 (h ▸ hmem)
  refine ⟨⟨m, (mem_monomials n m).2 ⟨isShuffle_leftComb 0 _ hpos, ?_⟩⟩, hev⟩
  exact (perm_ev m).symm.trans (hev ▸ hw)

/-- **The words of the monomials of arity `n ≥ 1` are the arrangements of `0, …, n - 1`.** -/
theorem range_evL {n : ℕ} (hn : 1 ≤ n) :
    LinearMap.range (evL K n) = Finsupp.supported K K (arrs n : Set (List ℕ)) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [evL_apply]
    exact Submodule.sum_mem _ fun σ _ =>
      Submodule.smul_mem _ _ (Finsupp.single_mem_supported K _ (ev_mem_arrs σ))
  · rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_ev_eq hn (mem_arrs.1 hw)
    exact ⟨vecOf K n σ.1, by rw [evL_vecOf σ.2, hσ]⟩

variable (K) in
/-- **The operad presented by the relators of `Ass` is the span of the arrangements** in every
arity `n ≥ 1`, through the evaluation to words. -/
noncomputable def quotEquiv {n : ℕ} (hn : 1 ≤ n) :
    ((Mono (AssShGen 2) n → K) ⧸ idealOf K (rel K) n) ≃ₗ[K]
      Finsupp.supported K K (arrs n : Set (List ℕ)) :=
  ((Submodule.quotEquivOfEq _ _ (idealOf_eq_ker K n)).trans
    (LinearMap.quotKerEquivRange (evL K n))).trans (LinearEquiv.ofEq _ _ (range_evL hn))

variable (K) in
/-- **The operad presented by the relators of `Ass` has dimension `n!`** in every arity `n ≥ 1`,
that of `Sym.Ass` (`Operad.Sym.Ass.finrank`). -/
theorem finrank_quotient {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank K ((Mono (AssShGen 2) n → K) ⧸ idealOf K (rel K) n) = n.factorial := by
  rw [(quotEquiv K hn).finrank_eq, (Finsupp.supportedEquivFinsupp _).finrank_eq,
    Module.finrank_finsupp_self]
  simp [card_arrs]

variable (K) in
/-- **In every arity `n ≥ 1` the operad presented by the relators of `Ass` has the dimension of
`Sym.Ass K (Fin n)`.** -/
theorem finrank_quotient_eq_sym {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank K ((Mono (AssShGen 2) n → K) ⧸ idealOf K (rel K) n) =
      Module.finrank K (Sym.Ass K (Fin n)) := by
  rw [finrank_quotient K hn, Sym.Ass.finrank, Fintype.card_fin]

variable (K) in
/-- **The Koszul dual operad of `Ass` has dimension `n!`** in every arity `n ≥ 1`. -/
theorem finrank_quotient_dualRel {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank K ((Mono (AssShGen 2) n → K) ⧸ idealOf K (dualRel K (rel K)) n) =
      n.factorial := by
  rw [← (quotDualEquiv K n).finrank_eq, finrank_quotient K hn]

end AssBin

end Operad
