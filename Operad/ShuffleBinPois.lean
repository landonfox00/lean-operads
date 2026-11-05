/-
# The Poisson operad on the binary side: its relators and Koszulness

`Operad.ShuffleAnyPois` proves the Poisson operad Koszul as a shuffle operad with generators of
any arity (`Operad.PoisShGen.isKoszul`, for `Operad.Rules.IsKoszul`). This file presents it as a
binary shuffle operad on the product `x₁x₂` and the bracket `[x₁, x₂]` and proves it Koszul there
too (`Operad.ShuffleBar.IsKoszul`), so that both shuffle predicates hold for the same operad
(`PoisBin.isKoszul_and`).

* **The relators** (`PoisBin.rel`) are the vectors on the twelve monomials of arity three whose
  value in the polynomials in words vanishes (`PoisBin.ev`, `PoisBin.evL`): the relations of
  `Pois` in arity three, in the Kirillov–Kostant model. The binary evaluation is the any-arity one
  through the bridge (`PoisBin.evL_eq`).
* **They are the rules** (`PoisBin.map_rel`, `PoisBin.rel_eq_span`): on `0, 1, 2` a monomial
  which is not normal is a leading monomial (`PoisBin.eq_lead_of_not_normal`), so subtracting the
  rules at the leading monomials leaves a vector supported on the normal monomials, where the
  evaluation is injective (`PoisBin.ker_evL_three`). So the relators are spanned by the six
  relations of `Operad.PoisShGen.rules`: associativity twice, the Jacobi identity, and the Leibniz
  rule three times.
* Hence, through `Operad.ShuffleBridgeBar`, **the Poisson operad is Koszul as a binary shuffle
  operad** (`PoisBin.isKoszul`), the two predicates agree for it (`PoisBin.isKoszul_iff`), the
  two presentations have the same ideals (`PoisBin.map_idealOf_rel`), and the binary presentation
  has dimension `n!` in arity `n ≥ 1` (`PoisBin.finrank_quotient`).

The binary Gröbner criterion `Operad.ShuffleBar.isKoszul` does not apply directly. Its key
`Operad.LTree.pathKey` compares path lengths first, so the left combs `e(f(-, -), -)` lead; for
either ranking of the generators the leading monomials of the relators leave `26` normal
monomials in arity four instead of `24` (checked by a script, not in Lean), so the relators are no
quadratic Gröbner basis for that key. Binary Koszulness comes from the any-arity Gröbner basis
instead, by `Operad.ShuffleBridge.shuffleBar_isKoszul_of_isKoszul`.

**Open: the Koszul dual relators.** The operad `Pois` is self-dual up to suspension, the dual of
the product being a bracket and the dual of the bracket a product. On the binary side this reads
`dualRel K (rel K) = (rel K)` with `x₁x₂` and `[x₁, x₂]` exchanged; a script confirms it in arity
three (with or without signs on either generator, the relators being homogeneous), but it is not
proved here, and neither is the Koszulness of the operad of the dual relators.
-/
import Operad.ShuffleBridgeBar
import Operad.ShuffleAnyPois

namespace Operad

instance : DecidableEq (PoisShGen 2) := fun a b =>
  match a, b with
  | .mul, .mul => isTrue rfl
  | .br, .br => isTrue rfl
  | .mul, .br => isFalse fun h => by cases h
  | .br, .mul => isFalse fun h => by cases h

instance : Fintype (PoisShGen 2) where
  elems := {.mul, .br}
  complete x := by cases x <;> simp

instance : BinaryGens PoisShGen := ⟨fun _ hk => ⟨fun e => by cases e <;> exact hk rfl⟩⟩

namespace PoisBin

open LTree STree ShuffleBridge PoisShGen MvPolynomial

variable (K : Type*) [Field K]

/-! ## Evaluation in the polynomials in words -/

/-- **The value of a binary tree** at the one-letter words of its leaves: `x₁x₂` multiplies,
`[x₁, x₂]` brackets, in the Poisson algebra of polynomials in words. -/
noncomputable def ev : LTree (PoisShGen 2) → PoisDim.W K
  | .leaf a => X [a]
  | .node e l r => PoisDim.βL K (op e) (ev l) (ev r)

/-- **A binary tree has the value of its tree with generators of any arity.** -/
theorem ev_toS : ∀ t : LTree (PoisShGen 2), ev K t = PoisShGen.ev K (toS t)
  | .leaf _ => rfl
  | .node e l r => by
    rw [ev, toS_node, PoisShGen.ev, evAt_node, ev_toS l, ev_toS r]
    rfl

/-- **The evaluation** in arity `n`: every monomial to its value. -/
noncomputable def evL (n : ℕ) : (Mono (PoisShGen 2) n → K) →ₗ[K] PoisDim.W K :=
  ∑ σ, (LinearMap.proj σ).smulRight (ev K σ.1)

/-- **The relators of the Poisson operad**: the vectors of arity three whose value in the
polynomials in words vanishes, the relations of `Pois` in arity three. -/
noncomputable def rel : Submodule K (Mono (PoisShGen 2) 3 → K) := LinearMap.ker (evL K 3)

variable {K}

lemma evL_apply {n : ℕ} (v : Mono (PoisShGen 2) n → K) :
    evL K n v = ∑ σ, v σ • ev K σ.1 := by
  simp [evL]

/-- **The binary evaluation is the evaluation of the shuffle monomials**, through the bridge. -/
theorem evL_eq (n : ℕ) (v : Mono (PoisShGen 2) n → K) :
    PoisShGen.evL K (Finset.range n) (vecEquiv PoisShGen K n v) = evL K n v := by
  rw [vecEquiv_eq_sum, map_sum, evL_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, PoisShGen.evL, Finsupp.linearCombination_single, one_smul, monoEquiv_val,
    ev_toS]

variable (K) in
lemma evL_comp (n : ℕ) :
    PoisShGen.evL K (Finset.range n) ∘ₗ (vecEquiv PoisShGen K n).toLinearMap = evL K n :=
  LinearMap.ext (evL_eq n)

variable (K) in
lemma src_rules (r : Rule) : (PoisShGen.rules K).src r = Finset.range 3 := rfl

/-! ## The relators are the rules -/

/-- **A shuffle monomial on `0, 1, 2` which is not normal is a leading monomial.** -/
lemma eq_lead_of_not_normal {g : SMono PoisShGen (Finset.range 3)}
    (h : ¬ (PoisShGen.rules K).Normal g) : ∃ r : Rule, g.1 = r.lead.1 := by
  rw [normal_iff (PoisShGen.rules K) (src_rules K) (L := Set.range fun r : Rule => ofS r.lead.1)
    rfl g] at h
  have hm := (mem_monomials 3 (ofS g.1)).1 (ofS_mem g)
  have hw : (ofS g.1).windows = [ofS g.1] := by
    obtain ⟨e, f, h' | h' | h'⟩ := mono3_cases hm.1 hm.2 <;> rw [h'] <;> rfl
  obtain ⟨r, hr⟩ : ofS g.1 ∈ Set.range fun r : Rule => ofS r.lead.1 := by
    by_contra hL
    exact h fun w hw' => by
      rw [hw, List.mem_singleton] at hw'
      exact hw' ▸ hL
  refine ⟨r, ?_⟩
  rw [← toS_ofS g.1, ← hr, toS_ofS]

/-- **The leading monomials are distinct.** -/
lemma lead_inj {r r' : Rule} (h : r.lead.1 = r'.lead.1) : r = r' := by
  have h' := congrArg ofS h
  cases r <;> cases r' <;> first | rfl | exact absurd h' (by decide)

/-- **No tail monomial is leading.** -/
lemma tail_ne_lead {r : Rule} {m : SMono PoisShGen three} (hm : m ∈ (Rule.tail K r).support)
    (r' : Rule) : m.1 ≠ r'.lead.1 := by
  intro h
  have h' := congrArg ofS h
  cases r <;> simp only [Rule.tail] at hm
  · rcases mem_support₂ hm with rfl | rfl <;> cases r' <;> exact absurd h' (by decide)
  · rcases mem_support₂ hm with rfl | rfl <;> cases r' <;> exact absurd h' (by decide)
  · rcases mem_support_sub hm with rfl | rfl <;> cases r' <;> exact absurd h' (by decide)
  · rcases mem_support₂ hm with rfl | rfl <;> cases r' <;> exact absurd h' (by decide)
  · rcases mem_support₁ hm with rfl
    cases r' <;> exact absurd h' (by decide)
  · rcases mem_support₁ hm with rfl
    cases r' <;> exact absurd h' (by decide)

/-- **The vector of a rule at a leading monomial**: one at its own, zero at the others. -/
lemma ruleVec_lead (r r' : Rule) :
    ruleVec (PoisShGen.rules K) (src_rules K) r' (SMono.cast (src_rules K r) r.lead) =
      if r' = r then 1 else 0 := by
  have hinj : Function.Injective (SMono.cast (E := PoisShGen) (src_rules K r')) :=
    fun a b h => Subtype.ext (congrArg Subtype.val h)
  have hc : SMono.cast (src_rules K r) r.lead = SMono.cast (src_rules K r') r.lead :=
    Subtype.ext rfl
  rw [ruleVec, hc, Finsupp.mapDomain_apply hinj, Finsupp.sub_apply]
  have ht : (PoisShGen.rules K).tail r' r.lead = 0 := by
    by_contra h0
    exact tail_ne_lead (Finsupp.mem_support_iff.2 h0) r rfl
  rw [ht, sub_zero]
  show Finsupp.single r'.lead (1 : K) r.lead = _
  classical
  by_cases hrr : r' = r
  · rw [hrr, Finsupp.single_eq_same, if_pos rfl]
  · rw [Finsupp.single_apply, if_neg (fun h => hrr (lead_inj (congrArg Subtype.val h))),
      if_neg hrr]

variable (K) in
/-- **The values on `0, 1, 2` vanish exactly on the span of the rules.** -/
theorem ker_evL_three : LinearMap.ker (PoisShGen.evL K (Finset.range 3)) =
    Submodule.span K (Set.range (ruleVec (PoisShGen.rules K) (src_rules K))) := by
  have hrv : ∀ r, ruleVec (PoisShGen.rules K) (src_rules K) r ∈
      LinearMap.ker (PoisShGen.evL K (Finset.range 3)) := fun r =>
    PoisShGen.ideal_le_ker _ (ruleVec_mem _ _ r)
  refine le_antisymm (fun w hw => ?_) (Submodule.span_le.2 (by rintro _ ⟨r, rfl⟩; exact hrv r))
  set ℓ : Rule → SMono PoisShGen (Finset.range 3) := fun r => SMono.cast (src_rules K r) r.lead
  set u := w - ∑ r : Rule, w (ℓ r) • ruleVec (PoisShGen.rules K) (src_rules K) r
  have hspan : ∑ r : Rule, w (ℓ r) • ruleVec (PoisShGen.rules K) (src_rules K) r ∈
      Submodule.span K (Set.range (ruleVec (PoisShGen.rules K) (src_rules K))) :=
    Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  have hu : u ∈ LinearMap.ker (PoisShGen.evL K (Finset.range 3)) :=
    Submodule.sub_mem _ hw (Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hrv r))
  have hN : u ∈ Finsupp.supported K K {t | (PoisShGen.rules K).Normal t} := by
    intro g hg
    by_contra hn
    obtain ⟨r, hr⟩ := eq_lead_of_not_normal hn
    have hg' : g = ℓ r := Subtype.ext hr
    refine Finsupp.mem_support_iff.1 hg ?_
    rw [hg']
    simp only [u, Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      ℓ, ruleVec_lead, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      sub_self]
  have h0 := PoisShGen.eq_zero_of_evL hN hu
  rw [sub_eq_zero.1 h0]
  exact hspan

/-- **The relators and the rules correspond** through the bridge. -/
theorem map_rel :
    (rel K).map (vecEquiv PoisShGen K 3).toLinearMap =
      Submodule.span K (Set.range (ruleVec (PoisShGen.rules K) (src_rules K))) := by
  rw [rel, ← evL_comp, LinearMap.ker_comp, ← ker_evL_three]
  exact Submodule.map_comap_eq_of_surjective (vecEquiv PoisShGen K 3).surjective _

variable (K) in
/-- **The relators are spanned by the rules**: each leading monomial minus its tail, the six
relations of `Operad.PoisShGen.rules` (associativity twice, Jacobi, Leibniz three times). -/
theorem rel_eq_span : rel K = Submodule.span K (Set.range fun r =>
    (vecEquiv PoisShGen K 3).symm (ruleVec (PoisShGen.rules K) (src_rules K) r)) := by
  have h := congrArg (Submodule.comap (vecEquiv PoisShGen K 3).toLinearMap) map_rel
  rw [Submodule.comap_map_eq_of_injective (vecEquiv PoisShGen K 3).injective,
    Submodule.comap_equiv_eq_map_symm, Submodule.map_span, ← Set.range_comp] at h
  exact h

/-! ## Koszulness -/

variable (K) in
/-- **The Poisson operad is Koszul as a binary shuffle operad**, through the bridge from the
quadratic Gröbner basis of `Operad.PoisShGen.rules`. -/
theorem isKoszul : ShuffleBar.IsKoszul K (rel K) :=
  shuffleBar_isKoszul_of_isKoszul _ (src_rules K) map_rel (PoisShGen.isKoszul K)

variable (K) in
/-- **The Poisson operad is Koszul in both shuffle senses**: as a binary shuffle operad,
presented by `rel`, and as a shuffle operad with generators of any arity, presented by
`PoisShGen.rules`. -/
theorem isKoszul_and : ShuffleBar.IsKoszul K (rel K) ∧ (PoisShGen.rules K).IsKoszul :=
  ⟨isKoszul K, PoisShGen.isKoszul K⟩

variable (K) in
/-- **The two Koszulness predicates of the Poisson operad agree.** -/
theorem isKoszul_iff : ShuffleBar.IsKoszul K (rel K) ↔ (PoisShGen.rules K).IsKoszul :=
  ShuffleBridge.isKoszul_iff _ (src_rules K) map_rel

variable (K) in
/-- **The two presentations of the Poisson operad agree** arity by arity. -/
theorem map_idealOf_rel (n : ℕ) :
    (LTree.idealOf K (rel K) n).map (vecEquiv PoisShGen K n).toLinearMap =
      ((PoisShGen.rules K).rw (Finset.range n)).ideal :=
  ShuffleBridge.map_idealOf _ (src_rules K) _ map_rel n

variable (K) in
/-- **The binary presentation has dimension `n!` in arity `n`.** -/
theorem finrank_quotient {n : ℕ} (hn : 0 < n) :
    Module.finrank K ((Mono (PoisShGen 2) n → K) ⧸ LTree.idealOf K (rel K) n) = n.factorial := by
  rw [(quotEquiv _ (src_rules K) _ map_rel n).finrank_eq,
    PoisShGen.finrank_eq_factorial ⟨0, Finset.mem_range.2 hn⟩, Finset.card_range]

end PoisBin

end Operad
