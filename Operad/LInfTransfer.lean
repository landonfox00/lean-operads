/-
# The homotopy transfer theorem for dg Lie algebras: the induction

A **shifted dg Lie algebra** (`LInfT.ShLie`) is an odd differential `d` and an odd graded symmetric
bracket `b` with `d² = 0`, the Leibniz rule and the shifted Jacobi identity: an L∞[1]-structure
concentrated in arities one and two. With a retraction `(e, h)`, `h d + d h = e - 1`
(`HTT.Retract`), the transferred operation on a set of inputs is `e d e` on one input and
`e ∘ λ` on more (`LInfT.lp`). Composites with an inner transferred operation on `T` put its value
as a new least input, below the inputs of `S ∖ T` (`LInfT.treeB`, on `WithBot α`).

The theorem is Markl's induction on the number of inputs, as in `Operad.HTT` for dg algebras:

* **the ∞-morphism equation** `∑_T ± tree (lp T, S ∖ T) = d (tree S) + λ S` follows from
  **the key equation** `d (λ S) + ∑_T ± λ (lp T, S ∖ T) = 0` by the homotopy formula
  (`LInfT.morph_of_key`);
* the key equation follows from the ∞-morphism equation on smaller sets (`LInfT.key_of_morph`),
  by the Leibniz rule, **insertion** (`LInfT.insL_eq`: composing the brackets of the trees with an
  inner operation inserts it into one of the two trees) and **the Jacobi identity**
  (`LInfT.sum_brackets_lam_eq_zero`: the brackets of the brackets of the trees cancel);
* `LInfT.morph_key` runs the induction. The trees have the parity of their inputs
  (`LInfT.isPar_tree`).
-/
import Operad.LInfTree

universe u v

namespace Operad

namespace LInfT

open GerBV KS End

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-! ## Shifted dg Lie algebras -/

/-- **A shifted dg Lie algebra**: an L∞[1]-structure concentrated in arities one and two, an odd
differential `d` and an odd graded symmetric bracket `b`, with `d² = 0`, the Leibniz rule and the
shifted Jacobi identity (`LInf.isLInf_two_iff`). -/
structure ShLie (ε d : V →ₗ[R] V) (b : End R V 2) : Prop where
  d_odd : ∀ x, d (ε x) = -ε (d x)
  b_odd : IsHomog ε 1 b
  dd : ∀ x, d (d x) = 0
  symm : ∀ p q x y, IsPar ε p x → IsPar ε q y → b ![y, x] = σ R (p && q) • b ![x, y]
  leibniz : ∀ p q x y, IsPar ε p x → IsPar ε q y →
    d (b ![x, y]) + b ![d x, y] + σ R p • b ![x, d y] = 0
  jacobi : ∀ p q r x y z, IsPar ε p x → IsPar ε q y → IsPar ε r z →
    b ![b ![x, y], z] + σ R (q && r) • b ![b ![x, z], y] + σ R (p && xor q r) • b ![b ![y, z], x]
      = 0

lemma b_sub_left (b : End R V 2) (x x' y : V) : b ![x - x', y] = b ![x, y] - b ![x', y] := by
  have h := b.map_update_sub ![x, y] 0 x x'
  rwa [HTT.vec2_update_zero, HTT.vec2_update_zero, HTT.vec2_update_zero] at h

lemma b_sub_right (b : End R V 2) (x y y' : V) : b ![x, y - y'] = b ![x, y] - b ![x, y'] := by
  have h := b.map_update_sub ![x, y] 1 y y'
  rwa [HTT.vec2_update_one, HTT.vec2_update_one, HTT.vec2_update_one] at h

lemma b_sum_left (b : End R V 2) {ι : Type*} (s : Finset ι) (x : ι → V) (y : V) :
    b ![∑ i ∈ s, x i, y] = ∑ i ∈ s, b ![x i, y] := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := b.map_update_zero ![(0 : V), y] 0
    rw [HTT.vec2_update_zero] at h
    simpa using h
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HTT.mu_add_left, ih]

lemma b_sum_right (b : End R V 2) {ι : Type*} (s : Finset ι) (x : V) (y : ι → V) :
    b ![x, ∑ i ∈ s, y i] = ∑ i ∈ s, b ![x, y i] := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := b.map_update_zero ![x, (0 : V)] 1
    rw [HTT.vec2_update_one] at h
    simpa using h
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HTT.mu_add_right, ih]

variable {ε : V →ₗ[R] V}

lemma isPar_b {b : End R V 2} (hb : IsHomog ε 1 b) {p q : Bool} {x y : V} (hx : IsPar ε p x)
    (hy : IsPar ε q y) : IsPar ε (!xor p q) (b ![x, y]) := by
  have h := hb ![x, y]
  have e : (fun t => ε (![x, y] t)) = ![σ R p • x, σ R q • y] := by
    funext t
    fin_cases t
    exacts [hx, hy]
  rw [e, HTT.mu_smul_left, HTT.mu_smul_right, pow_one, neg_one_smul] at h
  unfold IsPar
  rw [LInf.σ_not, ← LInf.σ_mul, neg_smul, ← smul_smul, h, neg_neg]

lemma isPar_add {p : Bool} {x y : V} (hx : IsPar ε p x) (hy : IsPar ε p y) :
    IsPar ε p (x + y) := by
  unfold IsPar at *
  rw [map_add, hx, hy, smul_add]

lemma isPar_smul {p : Bool} (c : R) {x : V} (hx : IsPar ε p x) : IsPar ε p (c • x) := by
  unfold IsPar at *
  rw [map_smul, hx, smul_comm]

lemma isPar_zero (p : Bool) : IsPar ε p (0 : V) := by
  unfold IsPar
  rw [map_zero, smul_zero]

lemma isPar_sum {p : Bool} {ι : Type*} (s : Finset ι) {x : ι → V} (hx : ∀ i ∈ s, IsPar ε p (x i)) :
    IsPar ε p (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isPar_zero p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isPar_add (hx a (Finset.mem_insert_self a s))
      (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

/-! ## Parities of the trees -/

variable [Invertible (2 : R)] {α : Type*} [LinearOrder α]

variable {d e h : V →ₗ[R] V} {b : End R V 2}

/-- **The trees have the parity of their inputs.** -/
theorem isPar_tree (hb : IsHomog ε 1 b) (hr : HTT.Retract ε d e h) (p : α → Bool) (v : α → V)
    (hv : ∀ a, IsPar ε (p a) (v a)) :
    ∀ (n : ℕ) (S : Finset α), S.card = n → IsPar ε (par p S) (tree b e h p v S) ∧
      IsPar ε (!par p S) (lam b e h p v S) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn
    have hlam : IsPar ε (!par p S) (lam b e h p v S) := by
      unfold lam
      refine isPar_smul _ (isPar_sum _ fun T hT => isPar_smul _ ?_)
      have h1 := ih _ (hn ▸ card_lt_of_mem_splits hT) T rfl
      have h2 := ih _ (hn ▸ card_sdiff_lt_of_mem_splits hT) (S \ T) rfl
      have h3 := isPar_b hb h1.1 h2.1
      have hS : S = T ∪ (S \ T) := (Finset.union_sdiff_of_subset (mem_splits.1 hT).1).symm
      rwa [hS, par_union p Finset.disjoint_sdiff, ← hS]
    refine ⟨?_, hlam⟩
    by_cases hS : S.card ≤ 1
    · rw [tree_of_card_le_one b e h p v hS]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hS with h0 | h1
      · rw [Finset.card_eq_zero.1 h0, Finset.sum_empty]
        exact isPar_zero _
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
        rw [Finset.sum_singleton]
        have h1 : par p {a} = p a := by
          rw [show ({a} : Finset α) = insert a ∅ from rfl, par_insert p (Finset.notMem_empty a),
            par_empty, Bool.xor_false]
        rw [h1]
        unfold IsPar
        rw [← hr.e_even, hv a, map_smul]
    · rw [tree_of_one_lt b e h p v (by omega)]
      unfold IsPar at hlam ⊢
      rw [← neg_neg (ε (h _)), ← hr.h_odd, hlam, map_smul, LInf.σ_not, neg_smul, neg_neg]

/-! ## The inner output as a new first input -/

/-- The parities with a new least input of parity `q`. -/
def botP (q : Bool) (p : α → Bool) : WithBot α → Bool := WithBot.recBotCoe q p

/-- The inputs with a new least input `x`. -/
def botV (x : V) (v : α → V) : WithBot α → V := WithBot.recBotCoe x v

/-- The inclusion of the inputs, below which the new input sits. -/
noncomputable def cemb : α ↪o WithBot α := OrderEmbedding.ofStrictMono _ WithBot.coe_strictMono

variable (b d e h) (p : α → Bool) (v : α → V)

/-- **The transferred operation on a set of inputs**: `e d e` on one input, `e ∘ λ` on more. -/
noncomputable def lp (S : Finset α) : V :=
  if S.card ≤ 1 then ∑ a ∈ S, e (d (e (v a))) else e (lam b e h p v S)

/-- The inputs of a composite with an inner operation on `T`: a new first input, and `S ∖ T`. -/
noncomputable def bset (T S : Finset α) : Finset (WithBot α) :=
  insert ⊥ ((S \ T).map cemb.toEmbedding)

/-- The tree with the transferred operation on `T` as a new first input, and the inputs `S ∖ T`. -/
noncomputable def treeB (T S : Finset α) : V :=
  tree b e h (botP (!par p T) p) (botV (lp d e h b p v T) v) (bset T S)

/-- The brackets of the trees with the transferred operation on `T` as a new first input. -/
noncomputable def lamB (T S : Finset α) : V :=
  lam b e h (botP (!par p T) p) (botV (lp d e h b p v T) v) (bset T S)

/-- The nonempty subsets. -/
def nes (S : Finset α) : Finset (Finset α) := S.powerset.filter Finset.Nonempty

omit [Invertible (2 : R)] [LinearOrder α] in
lemma mem_nes {S T : Finset α} : T ∈ nes S ↔ T ⊆ S ∧ T.Nonempty := by
  unfold nes
  rw [Finset.mem_filter, Finset.mem_powerset]

/-- **Composing the trees with the transferred operations**: `∑_T ± tree (lp T, S ∖ T)`. -/
noncomputable def ins (S : Finset α) : V :=
  ∑ T ∈ nes S, ks R p T (S \ T) • treeB d e h b p v T S

/-- Composing the brackets of the trees with the transferred operations. -/
noncomputable def insL (S : Finset α) : V :=
  ∑ T ∈ nes S, ks R p T (S \ T) • lamB d e h b p v T S

omit [Invertible (2 : R)] in
lemma card_bset (T S : Finset α) : (bset T S).card = (S \ T).card + 1 := by
  unfold bset
  rw [Finset.card_insert_of_notMem, Finset.card_map]
  intro hb
  obtain ⟨a, -, ha⟩ := Finset.mem_map.1 hb
  exact WithBot.coe_ne_bot ha

lemma treeB_self (S : Finset α) : treeB d e h b p v S S = e (lp d e h b p v S) := by
  unfold treeB
  have h1 : bset S S = {⊥} := by
    unfold bset
    rw [Finset.sdiff_self, Finset.map_empty]
    rfl
  rw [h1, tree_singleton]
  rfl

lemma lamB_self (S : Finset α) : lamB d e h b p v S S = 0 := by
  unfold lamB
  exact lam_of_card_le_one _ _ _ _ _ (by rw [card_bset, Finset.sdiff_self, Finset.card_empty])

lemma treeB_of_ne {S T : Finset α} (hT : T ⊆ S) (hne : T ≠ S) :
    treeB d e h b p v T S = h (lamB d e h b p v T S) := by
  unfold treeB lamB
  refine tree_of_one_lt _ _ _ _ _ ?_
  rw [card_bset]
  have : (S \ T).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro e'
    exact hne (Finset.Subset.antisymm hT (Finset.sdiff_eq_empty_iff_subset.1 e'))
  have := this.card_pos
  omega

/-- **The ∞-morphism equation from the key equation**, by the homotopy formula. -/
theorem morph_of_key (hr : HTT.Retract ε d e h) {S : Finset α} (hS : S.Nonempty)
    (hK : d (lam b e h p v S) + insL d e h b p v S = 0) :
    ins d e h b p v S = d (tree b e h p v S) + lam b e h p v S := by
  have hmem : S ∈ nes S := mem_nes.2 ⟨subset_rfl, hS⟩
  have hrest : ∑ T ∈ (nes S).erase S, ks R p T (S \ T) • treeB d e h b p v T S
      = h (insL d e h b p v S) := by
    unfold insL
    rw [← Finset.add_sum_erase _ _ hmem, lamB_self, smul_zero, zero_add, map_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    obtain ⟨hne, hT'⟩ := Finset.mem_erase.1 hT
    rw [treeB_of_ne d e h b p v (mem_nes.1 hT').1 hne, map_smul]
  have hI : insL d e h b p v S = -d (lam b e h p v S) := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact hK
  unfold ins
  rw [← Finset.add_sum_erase _ _ hmem, hrest, hI, Finset.sdiff_self, ks_empty_right, one_smul,
    treeB_self, map_neg]
  unfold lp
  by_cases h1 : S.card ≤ 1
  · rw [if_pos h1, lam_of_card_le_one b e h p v h1]
    simp only [map_zero, neg_zero, add_zero]
    rw [tree_of_card_le_one b e h p v h1, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hr.de, hr.ee, hr.ee]
  · rw [if_neg h1, tree_of_one_lt b e h p v (by omega), hr.ee]
    have := hr.homotopy (lam b e h p v S)
    linear_combination (norm := module) -this

/-! ## Inserting the transferred operations into the brackets of the trees -/

omit [Invertible (2 : R)] in
lemma cemb_apply (a : α) : (cemb : α ↪o WithBot α) a = (a : WithBot α) := rfl

omit [Invertible (2 : R)] in
lemma bot_notMem_map (U : Finset α) : (⊥ : WithBot α) ∉ U.map cemb.toEmbedding := by
  intro hb
  obtain ⟨a, -, ha⟩ := Finset.mem_map.1 hb
  exact WithBot.coe_ne_bot ha

omit [Invertible (2 : R)] in
lemma map_injective_cemb : Function.Injective fun A : Finset α => A.map cemb.toEmbedding :=
  fun _ _ h => Finset.map_injective _ h

omit [Invertible (2 : R)] in
/-- The parts of a set with a new least element: those containing it, and the others. -/
lemma sum_splits_bset {M : Type*} [AddCommMonoid M] (U : Finset α)
    (f : Finset (WithBot α) → M) :
    ∑ A' ∈ splits (insert ⊥ (U.map cemb.toEmbedding)), f A'
      = ∑ A ∈ U.powerset.filter (· ≠ U), f (insert ⊥ (A.map cemb.toEmbedding)) +
        ∑ A ∈ nes U, f (A.map cemb.toEmbedding) := by
  classical
  have hU := bot_notMem_map U
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun A' => (⊥ : WithBot α) ∈ A')]
  congr 1
  · symm
    refine Finset.sum_nbij' (fun A => insert ⊥ (A.map cemb.toEmbedding))
      (fun A' => (A'.erase ⊥).preimage cemb (cemb.injective.injOn)) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      rw [Finset.mem_filter, Finset.mem_powerset] at hA
      rw [Finset.mem_filter, mem_splits]
      refine ⟨⟨Finset.insert_subset_insert _ (Finset.map_subset_map.2 hA.1),
        Finset.insert_nonempty _ _, fun e => hA.2 ?_⟩, Finset.mem_insert_self _ _⟩
      have := congrArg (fun B => B.erase ⊥) e
      simp only [Finset.erase_insert (bot_notMem_map _)] at this
      exact Finset.map_injective _ this
    · intro A' hA'
      rw [Finset.mem_filter, mem_splits] at hA'
      obtain ⟨⟨h1, -, h3⟩, h4⟩ := hA'
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun a ha => ?_, fun e => h3 ?_⟩
      · rw [Finset.mem_preimage, Finset.mem_erase] at ha
        have := h1 ha.2
        rw [Finset.mem_insert, Finset.mem_map] at this
        rcases this with h | ⟨b, hb, hb'⟩
        · exact absurd h ha.1
        · have hba : b = a := WithBot.coe_injective hb'
          exact hba ▸ hb
      · ext x
        constructor
        · intro hx
          exact h1 hx
        · intro hx
          rw [Finset.mem_insert, Finset.mem_map] at hx
          rcases hx with rfl | ⟨b, hb, rfl⟩
          · exact h4
          · rw [← e] at hb
            rw [Finset.mem_preimage, Finset.mem_erase] at hb
            exact hb.2
    · intro A _
      ext a
      simp [Finset.mem_preimage, cemb_apply]
    · intro A' hA'
      rw [Finset.mem_filter, mem_splits] at hA'
      obtain ⟨⟨h1, -, -⟩, h4⟩ := hA'
      ext x
      rw [Finset.mem_insert, Finset.mem_map]
      constructor
      · rintro (rfl | ⟨b, hb, rfl⟩)
        · exact h4
        · rw [Finset.mem_preimage, Finset.mem_erase] at hb
          exact hb.2
      · intro hx
        induction x using WithBot.recBotCoe with
        | bot => exact Or.inl rfl
        | coe a =>
          refine Or.inr ⟨a, ?_, rfl⟩
          rw [Finset.mem_preimage, Finset.mem_erase]
          exact ⟨WithBot.coe_ne_bot, hx⟩
    · intro A _
      rfl
  · symm
    refine Finset.sum_nbij' (fun A => A.map cemb.toEmbedding)
      (fun A' => A'.preimage cemb (cemb.injective.injOn)) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      obtain ⟨hAU, hAn⟩ := mem_nes.1 hA
      rw [Finset.mem_filter, mem_splits]
      refine ⟨⟨(Finset.map_subset_map.2 hAU).trans (Finset.subset_insert _ _),
        Finset.map_nonempty.2 hAn, fun e => bot_notMem_map A ?_⟩, bot_notMem_map A⟩
      have e' : A.map cemb.toEmbedding = insert ⊥ (U.map cemb.toEmbedding) := e
      rw [e']
      exact Finset.mem_insert_self _ _
    · intro A' hA'
      rw [Finset.mem_filter, mem_splits] at hA'
      obtain ⟨⟨h1, h2, -⟩, h4⟩ := hA'
      refine mem_nes.2 ⟨fun a ha => ?_, ?_⟩
      · rw [Finset.mem_preimage] at ha
        have := h1 ha
        rw [Finset.mem_insert, Finset.mem_map] at this
        rcases this with h | ⟨b, hb, hb'⟩
        · exact absurd h WithBot.coe_ne_bot
        · have hba : b = a := WithBot.coe_injective hb'
          exact hba ▸ hb
      · obtain ⟨x, hx⟩ := h2
        induction x using WithBot.recBotCoe with
        | bot => exact absurd hx h4
        | coe a => exact ⟨a, by rw [Finset.mem_preimage]; exact hx⟩
    · intro A _
      ext a
      simp [Finset.mem_preimage, cemb_apply]
    · intro A' hA'
      rw [Finset.mem_filter, mem_splits] at hA'
      obtain ⟨-, h4⟩ := hA'
      ext x
      rw [Finset.mem_map]
      constructor
      · rintro ⟨b, hb, rfl⟩
        rw [Finset.mem_preimage] at hb
        exact hb
      · intro hx
        induction x using WithBot.recBotCoe with
        | bot => exact absurd hx h4
        | coe a => exact ⟨a, by rw [Finset.mem_preimage]; exact hx, rfl⟩
    · intro A _
      rfl

omit [Invertible (2 : R)] in
/-- The new least input moves past nothing. -/
lemma ks_insert_bot_left (q : WithBot α → Bool) (A B : Finset α) :
    ks R q (insert ⊥ (A.map cemb.toEmbedding)) (B.map cemb.toEmbedding)
      = ks R (q ∘ cemb) A B := by
  rw [Finset.insert_eq, ks_union_left q _ (Finset.disjoint_singleton_left.2 (bot_notMem_map A)),
    ks_singleton_left, ks_map]
  have : (B.map cemb.toEmbedding).filter (· < ⊥) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact fun x _ => not_lt_bot
  rw [this, Finset.prod_empty, one_mul]

omit [Invertible (2 : R)] in
/-- Every other input moves past the new least input. -/
lemma ks_insert_bot_right (q : WithBot α → Bool) (A B : Finset α) :
    ks R q (A.map cemb.toEmbedding) (insert ⊥ (B.map cemb.toEmbedding))
      = ks R (q ∘ cemb) A B * σ R (par (q ∘ cemb) A && q ⊥) := by
  rw [Finset.insert_eq, ks_union_right q _ (Finset.disjoint_singleton_left.2 (bot_notMem_map B)),
    ks_singleton_right, ks_map, σ_par_and]
  have hf : (A.map cemb.toEmbedding).filter (⊥ < ·) = A.map cemb.toEmbedding :=
    Finset.filter_true_of_mem fun x hx => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
      exact WithBot.bot_lt_coe a
  rw [hf, Finset.prod_map, mul_comm]
  rfl

/-- **The brackets with a new first input**, as brackets of trees with and without it. -/
lemma lamB_eq (T S : Finset α) :
    lamB d e h b p v T S = (⅟2 : R) •
      (∑ A ∈ (S \ T).powerset.filter (· ≠ S \ T), ks R p A ((S \ T) \ A) •
          b ![treeB d e h b p v T (T ∪ A), tree b e h p v ((S \ T) \ A)] +
        ∑ A ∈ nes (S \ T), (ks R p A ((S \ T) \ A) * σ R (par p A && !par p T)) •
          b ![tree b e h p v A, treeB d e h b p v T (T ∪ ((S \ T) \ A))]) := by
  set q := botP (!par p T) p
  set w := botV (lp d e h b p v T) v
  have hq : q ∘ cemb = p := rfl
  have hw : w ∘ cemb = v := rfl
  have htree : ∀ A : Finset α, tree b e h q w (A.map cemb.toEmbedding) = tree b e h p v A :=
    fun A => (tree_map b e h cemb q w _ A rfl).symm
  have hB : ∀ A : Finset α, Disjoint A T →
      tree b e h q w (insert ⊥ (A.map cemb.toEmbedding)) = treeB d e h b p v T (T ∪ A) := by
    intro A hA
    unfold treeB bset
    rw [Finset.union_sdiff_cancel_left hA.symm]
  unfold lamB lam bset
  rw [sum_splits_bset]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun A hA => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    have hAd : Disjoint A T := Finset.disjoint_of_subset_left hA.1 Finset.sdiff_disjoint
    have e1 : insert ⊥ ((S \ T).map cemb.toEmbedding) \ insert ⊥ (A.map cemb.toEmbedding)
        = ((S \ T) \ A).map cemb.toEmbedding := by
      rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem (bot_notMem_map _),
        ← Finset.map_sdiff]
    rw [e1, ks_insert_bot_left, hq, htree, hB A hAd]
  · refine Finset.sum_congr rfl fun A hA => ?_
    obtain ⟨hAU, -⟩ := mem_nes.1 hA
    have hd : Disjoint ((S \ T) \ A) T :=
      Finset.disjoint_of_subset_left Finset.sdiff_subset Finset.sdiff_disjoint
    have e1 : insert ⊥ ((S \ T).map cemb.toEmbedding) \ A.map cemb.toEmbedding
        = insert ⊥ (((S \ T) \ A).map cemb.toEmbedding) := by
      rw [Finset.insert_sdiff_of_notMem _ (bot_notMem_map A), ← Finset.map_sdiff]
    rw [e1, ks_insert_bot_right, hq, htree, hB _ hd]
    rfl

omit [Invertible (2 : R)] in
lemma σ_and_not' (a c : Bool) : σ R (a && !c) = σ R a * σ R (c && a) := by
  cases a <;> cases c <;> simp [σ]

omit [Invertible (2 : R)] in
/-- Choosing the part with the inner operation, then the rest of a part. -/
lemma sum_nes_ne {M : Type*} [AddCommMonoid M] (S : Finset α) (G : Finset α → Finset α → M) :
    ∑ T ∈ nes S, ∑ A ∈ (S \ T).powerset.filter (· ≠ S \ T), G T A
      = ∑ A ∈ splits S, ∑ T ∈ nes A, G T (A \ T) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.1 ∪ x.2, x.1⟩) (fun x _ => ⟨x.2, x.1 \ x.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨T, A⟩ hx
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset] at hx
    obtain ⟨hT, hAS, hne⟩ := hx
    obtain ⟨hTS, hTn⟩ := mem_nes.1 hT
    rw [Finset.mem_sigma]
    refine ⟨mem_splits.2 ⟨Finset.union_subset hTS (hAS.trans Finset.sdiff_subset),
      hTn.mono Finset.subset_union_left, fun e => hne ?_⟩,
      mem_nes.2 ⟨Finset.subset_union_left, hTn⟩⟩
    simp only at e
    rw [← e, Finset.union_sdiff_cancel_left (Finset.disjoint_of_subset_right hAS
      Finset.disjoint_sdiff)]
  · rintro ⟨A, T⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hA, hT⟩ := hx
    obtain ⟨hAS, -, hAne⟩ := mem_splits.1 hA
    obtain ⟨hTA, hTn⟩ := mem_nes.1 hT
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨mem_nes.2 ⟨hTA.trans hAS, hTn⟩, Finset.sdiff_subset_sdiff hAS subset_rfl,
      fun e => hAne ?_⟩
    simp only at e
    rw [← Finset.union_sdiff_of_subset hTA, e, Finset.union_sdiff_of_subset (hTA.trans hAS)]
  · rintro ⟨T, A⟩ hx
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset] at hx
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Finset.union_sdiff_cancel_left (Finset.disjoint_of_subset_right hx.2.1
      Finset.disjoint_sdiff)
  · rintro ⟨A, T⟩ hx
    rw [Finset.mem_sigma] at hx
    simp only [Sigma.mk.injEq]
    exact ⟨Finset.union_sdiff_of_subset (mem_nes.1 hx.2).1, HEq.rfl⟩
  · rintro ⟨T, A⟩ hx
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset] at hx
    simp only
    rw [Finset.union_sdiff_cancel_left (Finset.disjoint_of_subset_right hx.2.1
      Finset.disjoint_sdiff)]

omit [Invertible (2 : R)] in
/-- Choosing the part with the inner operation, then a part outside it. -/
lemma sum_nes_nes {M : Type*} [AddCommMonoid M] (S : Finset α) (G : Finset α → Finset α → M) :
    ∑ T ∈ nes S, ∑ A ∈ nes (S \ T), G T A = ∑ A ∈ splits S, ∑ T ∈ nes (S \ A), G T A := by
  refine Finset.sum_comm' fun T A => ?_
  rw [mem_nes, mem_nes, mem_splits, mem_nes]
  constructor
  · rintro ⟨⟨hTS, hTn⟩, hAT, hAn⟩
    have hd : Disjoint A T := Finset.disjoint_of_subset_left hAT Finset.sdiff_disjoint
    refine ⟨⟨Finset.subset_sdiff.2 ⟨hTS, hd.symm⟩, hTn⟩, hAT.trans Finset.sdiff_subset, hAn,
      fun e => ?_⟩
    obtain ⟨a, ha⟩ := hTn
    exact Finset.disjoint_left.1 hd (by rw [e]; exact hTS ha) ha
  · rintro ⟨⟨hTA, hTn⟩, hAS, hAn, -⟩
    have hd : Disjoint T A := Finset.disjoint_of_subset_left hTA Finset.sdiff_disjoint
    exact ⟨⟨hTA.trans Finset.sdiff_subset, hTn⟩, Finset.subset_sdiff.2 ⟨hAS, hd.symm⟩, hAn⟩

/-- **Composing the brackets of the trees with the transferred operations inserts the operations
into one of the two trees.** -/
theorem insL_eq (S : Finset α) :
    insL d e h b p v S = (⅟2 : R) • ∑ A ∈ splits S, ks R p A (S \ A) •
      (b ![ins d e h b p v A, tree b e h p v (S \ A)] +
        σ R (par p A) • b ![tree b e h p v A, ins d e h b p v (S \ A)]) := by
  unfold insL
  simp only [lamB_eq d e h b p v _ S]
  simp only [smul_add, Finset.smul_sum, Finset.sum_add_distrib]
  rw [sum_nes_ne S, sum_nes_nes S]
  congr 1
  · refine Finset.sum_congr rfl fun A hA => ?_
    have hAS := (mem_splits.1 hA).1
    unfold ins
    rw [b_sum_left, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTA := (mem_nes.1 hT).1
    have e1 : (S \ T) \ (A \ T) = S \ A := by
      ext x
      have h1 := @hTA x
      have h2 := @hAS x
      simp only [Finset.mem_sdiff]
      tauto
    have e2 : T ∪ (A \ T) = A := Finset.union_sdiff_of_subset hTA
    have hu : (A \ T) ∪ (S \ A) = S \ T := by
      ext x
      have h1 := @hTA x
      have h2 := @hAS x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [e1, e2, HTT.mu_smul_left]
    simp only [smul_smul]
    congr 1
    have h1 := ks_union_right (R := R) p T
      (Finset.disjoint_of_subset_left Finset.sdiff_subset Finset.disjoint_sdiff :
        Disjoint (A \ T) (S \ A))
    have h2 := ks_union_left (R := R) p (S \ A) (Finset.disjoint_sdiff : Disjoint T (A \ T))
    rw [hu] at h1
    rw [e2] at h2
    rw [h1, h2]
    ring
  · refine Finset.sum_congr rfl fun A hA => ?_
    have hAS := (mem_splits.1 hA).1
    unfold ins
    rw [b_sum_right, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTB := (mem_nes.1 hT).1
    set B := S \ A with hBdef
    have hTS : T ⊆ S := hTB.trans Finset.sdiff_subset
    have hdTA : Disjoint T A := Finset.disjoint_of_subset_left hTB Finset.sdiff_disjoint
    have e1 : (S \ T) \ A = B \ T := by
      ext x
      simp only [hBdef, Finset.mem_sdiff]
      tauto
    have e2 : T ∪ (B \ T) = B := Finset.union_sdiff_of_subset hTB
    rw [e1, e2, HTT.mu_smul_right]
    simp only [smul_smul]
    congr 1
    have hST : S \ T = A ∪ (B \ T) := by
      rw [← e1, Finset.union_sdiff_of_subset (Finset.subset_sdiff.2 ⟨hAS, hdTA.symm⟩)]
    have h1 := ks_union_right (R := R) p T (Finset.disjoint_of_subset_right Finset.sdiff_subset
      Finset.sdiff_disjoint.symm : Disjoint A (B \ T))
    rw [← hST] at h1
    have h2 := ks_union_right (R := R) p A (Finset.disjoint_sdiff : Disjoint T (B \ T))
    rw [e2] at h2
    have h3 := ks_mul_ks (R := R) p hdTA
    have h4 := ks_mul_self (R := R) p T A
    rw [h1, h2, σ_and_not']
    linear_combination (-(⅟2 * ks R p T (B \ T) * ks R p A (B \ T) * σ R (par p A) *
      ks R p T A)) * h3 + (⅟2 * ks R p T (B \ T) * ks R p A (B \ T) * σ R (par p A) *
      ks R p A T) * h4

/-- The bracket of the bracket of three trees, with the Koszul sign of the three parts. -/
noncomputable def jt (X Y Z : Finset α) : V :=
  (ks R p X Y * ks R p X Z * ks R p Y Z) •
    b ![b ![tree b e h p v X, tree b e h p v Y], tree b e h p v Z]

omit [Invertible (2 : R)] [LinearOrder α] in
lemma σ_and_not (a c : Bool) : σ R a * σ R (!c && a) = σ R (c && a) := by
  cases a <;> cases c <;> simp [σ]

variable {b d e h p v}

/-- **The brackets of the brackets of the trees cancel**, by the Jacobi identity. -/
theorem sum_brackets_lam_eq_zero (hL : ShLie ε d b) (hr : HTT.Retract ε d e h)
    (hv : ∀ a, IsPar ε (p a) (v a))
    (S : Finset α) :
    ∑ A ∈ splits S, ks R p A (S \ A) • (b ![lam b e h p v A, tree b e h p v (S \ A)] +
      σ R (par p A) • b ![tree b e h p v A, lam b e h p v (S \ A)]) = 0 := by
  have hpar : ∀ X : Finset α, IsPar ε (par p X) (tree b e h p v X) := fun X =>
    (isPar_tree hL.b_odd hr p v hv _ X rfl).1
  -- the first halves
  have step1 : ∀ A ∈ splits S, ks R p A (S \ A) • b ![lam b e h p v A, tree b e h p v (S \ A)]
      = (⅟2 : R) • ∑ X ∈ splits A, jt e h b p v X (A \ X) (S \ A) := by
    intro A _
    unfold lam
    rw [HTT.mu_smul_left, b_sum_left, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun X hX => ?_
    have hXA := (mem_splits.1 hX).1
    have hks : ks R p A (S \ A) = ks R p X (S \ A) * ks R p (A \ X) (S \ A) := by
      have := ks_union_left (R := R) p (S \ A) (Finset.disjoint_sdiff : Disjoint X (A \ X))
      rwa [Finset.union_sdiff_of_subset hXA] at this
    rw [HTT.mu_smul_left, hks]
    unfold jt
    module
  -- the second halves
  have step2 : ∀ A ∈ splits S, ks R p A (S \ A) • σ R (par p A) •
      b ![tree b e h p v A, lam b e h p v (S \ A)]
      = (⅟2 : R) • ∑ Y ∈ splits (S \ A), jt e h b p v Y ((S \ A) \ Y) A := by
    intro A hA
    have hAS := (mem_splits.1 hA).1
    unfold lam
    rw [HTT.mu_smul_right, b_sum_right, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun Y hY => ?_
    have hYW := (mem_splits.1 hY).1
    set Z := (S \ A) \ Y with hZ
    have hYZ : Disjoint Y Z := Finset.disjoint_sdiff
    have hAY : Disjoint A Y := Finset.disjoint_of_subset_right hYW Finset.disjoint_sdiff
    have hAZ : Disjoint A Z := Finset.disjoint_of_subset_right Finset.sdiff_subset
      Finset.disjoint_sdiff
    have hks : ks R p A (S \ A) = ks R p A Y * ks R p A Z := by
      have := ks_union_right (R := R) p A hYZ
      rwa [Finset.union_sdiff_of_subset hYW] at this
    have hw := isPar_b hL.b_odd (hpar Y) (hpar Z)
    have hs := hL.symm _ _ _ _ hw (hpar A)
    have hσ : σ R (par p A) * σ R ((!xor (par p Y) (par p Z)) && par p A)
        = (ks R p Y A * ks R p A Y) * (ks R p Z A * ks R p A Z) := by
      rw [σ_and_not, σ_xor_and, ks_mul_ks p hAY.symm, ks_mul_ks p hAZ.symm]
    rw [HTT.mu_smul_right, hs, hks]
    unfold jt
    simp only [smul_smul]
    congr 1
    have h1 := ks_mul_self (R := R) p A Y
    have h2 := ks_mul_self (R := R) p A Z
    linear_combination (⅟2 * ks R p Y Z * ks R p A Y * ks R p A Z) * hσ +
      (⅟2 * ks R p Y Z * ks R p Y A * ks R p Z A * ks R p A Z * ks R p A Z) * h1 +
      (⅟2 * ks R p Y Z * ks R p Y A * ks R p Z A) * h2
  -- the sum over the three-part splittings
  have hsum : ∑ A ∈ splits S, ks R p A (S \ A) • (b ![lam b e h p v A, tree b e h p v (S \ A)] +
      σ R (par p A) • b ![tree b e h p v A, lam b e h p v (S \ A)])
      = ∑ q ∈ trip S, jt e h b p v q.1 q.2 (S \ (q.1 ∪ q.2)) := by
    simp only [smul_add]
    rw [Finset.sum_add_distrib, Finset.sum_congr rfl step1, Finset.sum_congr rfl step2,
      ← Finset.smul_sum, ← Finset.smul_sum, sum_splits_splits S (jt e h b p v),
      sum_splits_splits_sdiff S fun A Y Z => jt e h b p v Y Z A, ← add_smul,
      invOf_two_add_invOf_two, one_smul]
  rw [hsum]
  refine sum_trip_eq_zero S _ (fun q hq => ?_) fun q hq => ?_
  · obtain ⟨-, -, -, -, hXY, -⟩ := mem_trip.1 hq
    unfold jt
    rw [hL.symm _ _ _ _ (hpar q.1) (hpar q.2), HTT.mu_smul_left, smul_smul,
      ← ks_mul_ks p hXY]
    congr 1
    have h1 := ks_mul_self (R := R) p q.2 q.1
    linear_combination (ks R p q.2 (S \ (q.1 ∪ q.2)) * ks R p q.1 (S \ (q.1 ∪ q.2)) *
      ks R p q.1 q.2) * h1
  · obtain ⟨-, -, -, -, hXY, -⟩ := mem_trip.1 hq
    set X := q.1
    set Y := q.2
    set Z := S \ (X ∪ Y)
    have hXZ : Disjoint X Z := disjoint_sdiff_union
    have hYZ : Disjoint Y Z := by
      have := (disjoint_sdiff_union : Disjoint Y (S \ (Y ∪ X)))
      rwa [Finset.union_comm] at this
    have hJ := hL.jacobi _ _ _ _ _ _ (hpar X) (hpar Y) (hpar Z)
    rw [σ_and_xor, ← ks_mul_ks p hYZ, ← ks_mul_ks p hXY, ← ks_mul_ks p hXZ] at hJ
    have e1 : ks R p X Z * ks R p X Y * ks R p Z Y
        = (ks R p X Y * ks R p X Z * ks R p Y Z) * (ks R p Y Z * ks R p Z Y) := by
      have := ks_mul_self (R := R) p Y Z
      linear_combination (-(ks R p X Z * ks R p X Y * ks R p Z Y)) * this
    have e2 : ks R p Y Z * ks R p Y X * ks R p Z X
        = (ks R p X Y * ks R p X Z * ks R p Y Z) *
          ((ks R p X Y * ks R p Y X) * (ks R p X Z * ks R p Z X)) := by
      have h1 := ks_mul_self (R := R) p X Y
      have h2 := ks_mul_self (R := R) p X Z
      linear_combination (-(ks R p Y Z * ks R p Y X * ks R p Z X * ks R p X Z * ks R p X Z)) * h1
        - (ks R p Y Z * ks R p Y X * ks R p Z X) * h2
    unfold jt
    rw [e1, e2]
    linear_combination (norm := module) (ks R p X Y * ks R p X Z * ks R p Y Z) • hJ

/-- **The key equation from the ∞-morphism equation on smaller sets**, by the Leibniz rule and
`insL_eq` and `sum_brackets_lam_eq_zero`. -/
theorem key_of_morph (hL : ShLie ε d b) (hr : HTT.Retract ε d e h)
    (hv : ∀ a, IsPar ε (p a) (v a)) (S : Finset α)
    (hM : ∀ A ∈ splits S, ins d e h b p v A = d (tree b e h p v A) + lam b e h p v A) :
    d (lam b e h p v S) + insL d e h b p v S = 0 := by
  have hJ := sum_brackets_lam_eq_zero hL hr hv S
  have hd : d (lam b e h p v S) = (⅟2 : R) • ∑ A ∈ splits S, ks R p A (S \ A) •
      (-b ![ins d e h b p v A - lam b e h p v A, tree b e h p v (S \ A)] -
        σ R (par p A) • b ![tree b e h p v A,
          ins d e h b p v (S \ A) - lam b e h p v (S \ A)]) := by
    conv_lhs => unfold lam
    rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun A hA => ?_
    rw [map_smul, hM A hA, hM (S \ A) (sdiff_mem_splits hA), add_sub_cancel_right,
      add_sub_cancel_right]
    have hpar := (isPar_tree hL.b_odd hr p v hv _ A rfl).1
    have := hL.leibniz _ _ (tree b e h p v A) (tree b e h p v (S \ A)) hpar
      (isPar_tree hL.b_odd hr p v hv _ (S \ A) rfl).1
    congr 1
    linear_combination (norm := module) this
  rw [hd, insL_eq, ← smul_add, ← Finset.sum_add_distrib]
  have h2 : ∑ A ∈ splits S, (ks R p A (S \ A) •
      (-b ![ins d e h b p v A - lam b e h p v A, tree b e h p v (S \ A)] -
        σ R (par p A) • b ![tree b e h p v A,
          ins d e h b p v (S \ A) - lam b e h p v (S \ A)]) +
      ks R p A (S \ A) • (b ![ins d e h b p v A, tree b e h p v (S \ A)] +
        σ R (par p A) • b ![tree b e h p v A, ins d e h b p v (S \ A)]))
      = ∑ A ∈ splits S, ks R p A (S \ A) • (b ![lam b e h p v A, tree b e h p v (S \ A)] +
        σ R (par p A) • b ![tree b e h p v A, lam b e h p v (S \ A)]) := by
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [b_sub_left, b_sub_right]
    module
  rw [h2, hJ, smul_zero]

/-- **The ∞-morphism equation and the key equation**, by induction on the number of inputs. -/
theorem morph_key (hL : ShLie ε d b) (hr : HTT.Retract ε d e h)
    (hv : ∀ a, IsPar ε (p a) (v a)) :
    ∀ (n : ℕ) (S : Finset α), S.card = n →
      d (lam b e h p v S) + insL d e h b p v S = 0 ∧
        (S.Nonempty → ins d e h b p v S = d (tree b e h p v S) + lam b e h p v S) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn
    have hK := key_of_morph hL hr hv S fun A hA =>
      (ih _ (hn ▸ card_lt_of_mem_splits hA) A rfl).2 (mem_splits.1 hA).2.1
    exact ⟨hK, fun hS => morph_of_key d e h b p v hr hS hK⟩

end LInfT

end Operad
