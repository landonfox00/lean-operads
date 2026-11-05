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

**`Pois` is self-dual up to exchanging the product and the bracket** (`PoisBin.dualRel_rel`):
the Koszul dual relators of `Pois` are its relators relabelled along the exchange `PoisBin.swap`
of `x₁x₂` and `[x₁, x₂]` (`Operad.LTree.relabelVec`). The relators are spanned by explicit
integer combinations of binary monomials (`PoisBin.relB`, `PoisBin.rel_eq_span_relB`, through
`PoisBin.vecEquiv_relB`); their pairings with the exchanged ones, twisted by `chi3`, are integers
(`PoisBin.pair_combo`), all zero (`PoisBin.pairZ_swap`, checked by `decide` on the thirty-six
pairs of rules); and both spaces have dimension six (`PoisBin.finrank_rel`,
`Operad.ShuffleBar.finrank_dualRel`). So the operad of the dual relators is that of `Pois` in
every arity (`PoisBin.quotDualEquiv`, `PoisBin.finrank_quotient_dualRel`), and it is Koszul
(`PoisBin.isKoszul_dualRel`), Koszulness being invariant under relabelling the generators
(`Operad.ShuffleBar.isKoszul_relabel`). In the symmetric setting this is `Pois^! = Pois` up to
suspension, the dual of the commutative product being a bracket and conversely; the comparison
with the symmetric Koszul dual is not made.
-/
import Operad.ShuffleBridgeBar
import Operad.ShuffleAnyPois
import Operad.ShuffleRelabel
import Operad.ShuffleKoszulDuals
import Operad.ShuffleGradedDual

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

open LTree STree ShuffleBridge PoisShGen MvPolynomial ShuffleBar

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


/-! ## The Koszul dual relators -/

/-- **The exchange of the product and the bracket.** -/
def swap : PoisShGen 2 ≃ PoisShGen 2 where
  toFun e := match e with
    | .mul => .br
    | .br => .mul
  invFun e := match e with
    | .mul => .br
    | .br => .mul
  left_inv e := by cases e <;> rfl
  right_inv e := by cases e <;> rfl

/-- The left comb `e(f(0, 1), 2)`. -/
def bL (e f : PoisShGen 2) : LTree (PoisShGen 2) := .node e (.node f (.leaf 0) (.leaf 1)) (.leaf 2)

/-- The twisted left comb `e(f(0, 2), 1)`. -/
def bT (e f : PoisShGen 2) : LTree (PoisShGen 2) := .node e (.node f (.leaf 0) (.leaf 2)) (.leaf 1)

/-- The right comb `e(0, f(1, 2))`. -/
def bR (e f : PoisShGen 2) : LTree (PoisShGen 2) := .node e (.leaf 0) (.node f (.leaf 1) (.leaf 2))

/-- **The relators**, as integer combinations of binary monomials: each leading monomial minus
its tail. -/
def relList : Rule → List (ℤ × LTree (PoisShGen 2))
  | .jac => [(1, bL .br .br), (-1, bT .br .br), (-1, bR .br .br)]
  | .leib₁ => [(1, bR .br .mul), (-1, bL .mul .br), (-1, bT .mul .br)]
  | .leib₂ => [(1, bT .br .mul), (-1, bL .mul .br), (1, bR .mul .br)]
  | .leib₃ => [(1, bL .br .mul), (-1, bT .mul .br), (-1, bR .mul .br)]
  | .as₁ => [(1, bR .mul .mul), (-1, bL .mul .mul)]
  | .as₂ => [(1, bT .mul .mul), (-1, bL .mul .mul)]

variable (K) in
/-- **The vector of an integer combination** of monomials of arity three. -/
noncomputable def combo (l : List (ℤ × LTree (PoisShGen 2))) : Mono (PoisShGen 2) 3 → K :=
  (l.map fun x => (x.1 : K) • vecOf K 3 x.2).sum

variable (K) in
/-- **The binary relator of a rule.** -/
noncomputable def relB (r : Rule) : Mono (PoisShGen 2) 3 → K := combo K (relList r)

lemma three_eq : (three : Finset ℕ) = Finset.range 3 := rfl

lemma bL_mem (e f : PoisShGen 2) : bL e f ∈ monomials 3 :=
  (mem_monomials 3 _).2 ⟨by cases e <;> cases f <;> decide, by cases e <;> cases f <;> decide⟩

lemma bT_mem (e f : PoisShGen 2) : bT e f ∈ monomials 3 :=
  (mem_monomials 3 _).2 ⟨by cases e <;> cases f <;> decide, by cases e <;> cases f <;> decide⟩

lemma bR_mem (e f : PoisShGen 2) : bR e f ∈ monomials 3 :=
  (mem_monomials 3 _).2 ⟨by cases e <;> cases f <;> decide, by cases e <;> cases f <;> decide⟩

lemma vecEquiv_bL (e f : PoisShGen 2) : vecEquiv PoisShGen K 3 (vecOf K 3 (bL e f)) =
    Finsupp.single (SMono.cast three_eq (lcomb e f)) 1 := by
  rw [vecEquiv_vecOf K (bL_mem e f)]
  rfl

lemma vecEquiv_bT (e f : PoisShGen 2) : vecEquiv PoisShGen K 3 (vecOf K 3 (bT e f)) =
    Finsupp.single (SMono.cast three_eq (tcomb e f)) 1 := by
  rw [vecEquiv_vecOf K (bT_mem e f)]
  rfl

lemma vecEquiv_bR (e f : PoisShGen 2) : vecEquiv PoisShGen K 3 (vecOf K 3 (bR e f)) =
    Finsupp.single (SMono.cast three_eq (rcomb e f)) 1 := by
  rw [vecEquiv_vecOf K (bR_mem e f)]
  rfl

/-- **The binary relator of a rule is its vector**, through the bridge. -/
lemma ruleVec_eq' (r : Rule) : ruleVec (PoisShGen.rules K) (src_rules K) r =
    Finsupp.lmapDomain K K (SMono.cast (E := PoisShGen) three_eq)
      (Finsupp.single r.lead 1 - r.tail K) := rfl

/-- **The binary relator of a rule is its vector**, through the bridge. -/
lemma vecEquiv_relB (r : Rule) :
    vecEquiv PoisShGen K 3 (relB K r) = ruleVec (PoisShGen.rules K) (src_rules K) r := by
  rw [ruleVec_eq']
  cases r <;>
    simp only [relB, combo, relList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Int.cast_one, Int.cast_neg, one_smul, neg_one_smul, map_add, map_neg, map_sub, add_zero,
      vecEquiv_bL, vecEquiv_bT, vecEquiv_bR, Rule.lead, Rule.tail, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single] <;>
    abel

variable (K) in
/-- **The relators are spanned by the binary relators of the rules.** -/
theorem rel_eq_span_relB : rel K = Submodule.span K (Set.range (relB K)) := by
  rw [rel_eq_span]
  congr 1
  ext v
  simp only [Set.mem_range]
  refine exists_congr fun r => ?_
  rw [← vecEquiv_relB, LinearEquiv.symm_apply_apply]

lemma combo_apply (l : List (ℤ × LTree (PoisShGen 2))) (τ : Mono (PoisShGen 2) 3) :
    combo K l τ = (((l.map fun y => if τ.1 = y.2 then y.1 else 0).sum : ℤ) : K) := by
  induction l with
  | nil => simp [combo]
  | cons y l ih =>
    simp only [combo, List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      vecOf, Int.cast_add] at ih ⊢
    rw [ih]
    split_ifs <;> simp

/-- **The integer pairing** of two integer combinations, twisted by `chi3`. -/
def pairZ (l l' : List (ℤ × LTree (PoisShGen 2))) : ℤ :=
  (l.map fun x => x.1 * chi3 x.2 * (l'.map fun y => if x.2 = y.2 then y.1 else 0).sum).sum

lemma pair_combo (l l' : List (ℤ × LTree (PoisShGen 2))) (hl : ∀ x ∈ l, x.2 ∈ monomials 3) :
    ∑ σ, (chi3 σ.1 : K) * combo K l σ * combo K l' σ = (pairZ l l' : K) := by
  induction l with
  | nil => simp [combo, pairZ]
  | cons x l ih =>
    have hx := hl x (List.mem_cons_self ..)
    have h1 : ∀ σ : Mono (PoisShGen 2) 3, (chi3 σ.1 : K) * combo K (x :: l) σ * combo K l' σ =
        (x.1 : K) * (vecOf K 3 x.2 σ * ((chi3 σ.1 : K) * combo K l' σ)) +
          (chi3 σ.1 : K) * combo K l σ * combo K l' σ := fun σ => by
      simp only [combo, List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun σ _ => h1 σ, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_vecOf_mul' hx, ih fun y hy => hl y (List.mem_cons_of_mem _ hy), combo_apply, pairZ,
      pairZ, List.map_cons, List.sum_cons]
    push_cast
    ring

/-- The exchange of the product and the bracket in an integer combination. -/
def swapList (l : List (ℤ × LTree (PoisShGen 2))) : List (ℤ × LTree (PoisShGen 2)) :=
  l.map fun y => (y.1, y.2.mapDec swap)

lemma relabelVec_combo (l : List (ℤ × LTree (PoisShGen 2))) :
    relabelVec K swap 3 (combo K l) = combo K (swapList l) := by
  induction l with
  | nil => simp [combo, swapList]
  | cons y l ih =>
    simp only [combo, swapList, List.map_cons, List.sum_cons, map_add, map_smul,
      relabelVec_vecOf] at ih ⊢
    rw [ih]

/-- **The relators pair to zero with the exchanged relators**, checked by the kernel on the
thirty-six pairs of rules. -/
lemma pairZ_swap : ∀ r r' : Rule, pairZ (relList r) (swapList (relList r')) = 0 := by
  decide

lemma relList_mem (r : Rule) : ∀ x ∈ relList r, x.2 ∈ monomials 3 := by
  intro x hx
  cases r <;> simp only [relList, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl <;>
    first | exact bL_mem _ _ | exact bT_mem _ _ | exact bR_mem _ _

variable (K) in
/-- **The binary relators have dimension six.** -/
lemma finrank_rel : Module.finrank K (rel K) = 6 := by
  have h1 := Submodule.finrank_quotient_add_finrank (rel K)
  have h2 := finrank_quotient K (n := 3) (by norm_num)
  rw [ShuffleBar.idealOf_three] at h2
  have h3 : Module.finrank K (Mono (PoisShGen 2) 3 → K) = 12 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
      show (3 : ℕ) = 2 + 1 from rfl, card_monomials]
    rfl
  rw [h2, h3] at h1
  simp only [Nat.factorial] at h1
  omega

variable (K) in
/-- **The Poisson operad is self-dual up to exchanging the product and the bracket**: the Koszul
dual relators of `Pois` are its relators with `x₁x₂` and `[x₁, x₂]` exchanged. -/
theorem dualRel_rel :
    dualRel K (rel K) = (rel K).map (relabelVec K swap 3).toLinearMap := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    nth_rewrite 1 [rel_eq_span_relB]
    rw [Submodule.span_le]
    rintro _ ⟨r', rfl⟩
    show relabelVec K swap 3 (relB K r') ∈ dualRel K (rel K)
    rw [mem_dualRel, relB, relabelVec_combo]
    intro y hy
    rw [rel_eq_span_relB] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, rfl⟩ := hy
      rw [relB, pair_combo _ _ (relList_mem r), pairZ_swap, Int.cast_zero]
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib, ha, hb, add_zero]
    | smul c a _ ha =>
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_zero c, ← ha, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
  · rw [finrank_dualRel, LinearEquiv.finrank_map_eq, finrank_rel,
      Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
      show (3 : ℕ) = 2 + 1 from rfl, card_monomials]
    rfl

variable (K) in
/-- **The operad of the Koszul dual relators of `Pois` is the operad of `Pois`**, in every arity,
through the exchange of the product and the bracket. -/
noncomputable def quotDualEquiv (n : ℕ) :
    ((Mono (PoisShGen 2) n → K) ⧸ LTree.idealOf K (rel K) n) ≃ₗ[K]
      ((Mono (PoisShGen 2) n → K) ⧸ LTree.idealOf K (dualRel K (rel K)) n) :=
  (quotRelabelEquiv K swap (rel K) n).trans
    (Submodule.quotEquivOfEq _ _ (by rw [dualRel_rel]))

variable (K) in
/-- **The Koszul dual relators of `Pois` present a Koszul operad**: Koszulness is invariant under
relabelling the generators. -/
theorem isKoszul_dualRel : ShuffleBar.IsKoszul K (dualRel K (rel K)) := by
  rw [dualRel_rel]
  exact ShuffleBar.isKoszul_relabel swap (isKoszul K)

variable (K) in
/-- **The Koszul dual of `Pois` has dimension `n!` in arity `n ≥ 1`.** -/
theorem finrank_quotient_dualRel {n : ℕ} (hn : 0 < n) :
    Module.finrank K ((Mono (PoisShGen 2) n → K) ⧸ LTree.idealOf K (dualRel K (rel K)) n) =
      n.factorial := by
  rw [← (quotDualEquiv K n).finrank_eq, finrank_quotient K hn]

end PoisBin

end Operad
