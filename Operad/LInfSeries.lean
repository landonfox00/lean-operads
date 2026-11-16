/-
# Series and their composition along partitions of the inputs

A **series** `V ⇝ W` is one multilinear map in each arity (`LSer.Ser`). It is evaluated on a
finite set of inputs of any linear order, in increasing order (`LSer.ev`); evaluation is invariant
under order embeddings (`LSer.ev_map`), and sums on each input expand into sums over the choices
(`LSer.ev_sum`).

**The composite along partitions** (`LSer.cmp`): for parities `p` of the inputs, the outer series
on the values of the blocks, listed by their least inputs, with the Koszul sign of the
partition, summed over the partitions of the inputs.

* **Associativity** (`LSer.cmp_assoc`): composing with composites on the blocks is composing the
  composite of the outer series with the blocks' values, by the gluing of partitions and the sign
  of a coarsening (`Operad.InputPartition`).
* **Relabelling** (`LSer.cmp_map`): composites are invariant under order embeddings of the inputs.
-/
import Operad.InputPartition
import Mathlib.LinearAlgebra.Multilinear.Basic

universe u

namespace Operad

namespace LSer

open GerBV KS IPart

variable {R : Type u} [CommRing R]

/-- **Series**: one multilinear map in each arity. -/
abbrev Ser (R : Type u) [CommRing R] (V W : Type*) [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] :=
  ∀ k : ℕ, MultilinearMap R (fun _ : Fin k => V) W

variable {V W X U : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup X] [Module R X] [AddCommGroup U] [Module R U]

/-! ## Evaluation on a finite set of inputs -/

section ev

variable {α : Type*} [LinearOrder α]

/-- **A series evaluated on the inputs in `S`**, in increasing order. -/
noncomputable def ev (F : Ser R V W) (v : α → V) (S : Finset α) : W :=
  F S.card (v ∘ S.orderEmbOfFin rfl)

lemma ev_eq (F : Ser R V W) (v : α → V) (S : Finset α) {k : ℕ} (h : S.card = k) :
    ev F v S = F k (v ∘ S.orderEmbOfFin h) := by
  subst h
  rfl

/-- **Evaluation only depends on the inputs in `S`.** -/
lemma ev_congr (F : Ser R V W) {v v' : α → V} {S : Finset α} (h : ∀ a ∈ S, v a = v' a) :
    ev F v S = ev F v' S := by
  unfold ev
  congr 1
  funext j
  exact h _ (Finset.orderEmbOfFin_mem _ _ _)

/-- **Evaluation is invariant under order embeddings.** -/
lemma ev_map {β : Type*} [LinearOrder β] (F : Ser R V W) (ι : α ↪o β) (w : β → V)
    (S : Finset α) : ev F (w ∘ ι) S = ev F w (S.map ι.toEmbedding) := by
  rw [ev_eq F w (S.map ι.toEmbedding) (Finset.card_map _)]
  unfold ev
  congr 1
  funext j
  simp only [Function.comp_apply]
  congr 1
  have := Finset.orderEmbOfFin_unique (s := S.map ι.toEmbedding) (Finset.card_map _)
    (f := fun j => ι (S.orderEmbOfFin rfl j))
    (fun j => Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem _ _ _))
    (ι.strictMono.comp (S.orderEmbOfFin rfl).strictMono)
  exact congrFun this j

/-- Scalars on each input come out as their product. -/
lemma ev_smul (F : Ser R V W) (c : α → R) (v : α → V) (S : Finset α) :
    ev F (fun m => c m • v m) S = (∏ m ∈ S, c m) • ev F v S := by
  unfold ev
  have h := (F S.card).map_smul_univ (fun j => c (S.orderEmbOfFin rfl j))
    (v ∘ S.orderEmbOfFin rfl)
  rw [show ((fun m => c m • v m) ∘ ⇑(S.orderEmbOfFin rfl))
    = fun i => c (S.orderEmbOfFin rfl i) • v (S.orderEmbOfFin rfl i) from rfl]
  refine Eq.trans h ?_
  congr 1
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S rfl]
  rw [Finset.prod_map]
  rfl

/-- **Sums on each input expand into the sum over the choices**, the labels outside `S` taking
a fixed value. -/
lemma ev_sum [DecidableEq α] [Fintype α] {ι : Type*} [DecidableEq ι] (F : Ser R V W)
    (S : Finset α) (A : α → Finset ι) (i₀ : ι) (g : α → ι → V) :
    ev F (fun m => ∑ i ∈ A m, g m i) S
      = ∑ ρ ∈ Fintype.piFinset (fun m => if m ∈ S then A m else {i₀}),
        ev F (fun m => g m (ρ m)) S := by
  classical
  unfold ev
  rw [show ((fun m => ∑ i ∈ A m, g m i) ∘ ⇑(S.orderEmbOfFin rfl))
    = fun j => ∑ i ∈ A (S.orderEmbOfFin rfl j), g (S.orderEmbOfFin rfl j) i from rfl,
    (F S.card).map_sum_finset (fun j i => g (S.orderEmbOfFin rfl j) i)
    (fun j => A (S.orderEmbOfFin rfl j))]
  set e := S.orderIsoOfFin rfl
  have he : ∀ j, (e j : α) = S.orderEmbOfFin rfl j := fun j => Finset.coe_orderIsoOfFin_apply _ _ _
  symm
  refine Finset.sum_nbij' (fun ρ j => ρ (S.orderEmbOfFin rfl j))
    (fun ρ' m => if h : m ∈ S then ρ' (e.symm ⟨m, h⟩) else i₀) ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    rw [Fintype.mem_piFinset] at hρ ⊢
    intro j
    have := hρ (S.orderEmbOfFin rfl j)
    rwa [if_pos (Finset.orderEmbOfFin_mem _ _ _)] at this
  · intro ρ' hρ'
    rw [Fintype.mem_piFinset] at hρ' ⊢
    intro m
    dsimp only
    by_cases hm : m ∈ S
    · rw [dif_pos hm, if_pos hm]
      have := hρ' (e.symm ⟨m, hm⟩)
      rwa [← he, OrderIso.apply_symm_apply] at this
    · rw [dif_neg hm, if_neg hm]
      exact Finset.mem_singleton_self _
  · intro ρ hρ
    rw [Fintype.mem_piFinset] at hρ
    funext m
    by_cases hm : m ∈ S
    · simp only [dif_pos hm]
      rw [← he, OrderIso.apply_symm_apply]
    · simp only [dif_neg hm]
      have := hρ m
      rw [if_neg hm] at this
      exact (Finset.mem_singleton.1 this).symm
  · intro ρ' _
    funext j
    simp only [dif_pos (Finset.orderEmbOfFin_mem S rfl j)]
    congr 1
    rw [OrderIso.symm_apply_eq]
    exact Subtype.ext (he j).symm
  · intro ρ _
    rfl

end ev

/-! ## Composition along partitions -/

section cmp

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- **The composite along the partitions of `S`**: the outer series on the values of the
blocks, listed by their least inputs, with the Koszul sign of the partition. -/
noncomputable def cmp (G : Ser R W X) (Φ : Finset α → W) (p : α → Bool) (S : Finset α) : X :=
  ∑ r ∈ roots S, sgn R p r S • ev G (fun m => Φ (blk r S m)) (fix r S)

end cmp

/-! ## Associativity -/

section assoc

variable {α : Type*} [LinearOrder α] [Fintype α]

omit [Fintype α] in
lemma sgn_congr (p : α → Bool) {r r' : α → α} {S : Finset α} (h : ∀ x ∈ S, r x = r' x) :
    sgn R p r S = sgn R p r' S := by
  unfold sgn
  refine Finset.prod_congr rfl fun x hx => Finset.prod_congr rfl fun y hy => ?_
  rw [h x hx, h y hy]

omit [Fintype α] in
lemma fix_comp {S : Finset α} {r s : α → α} (hr : IsRoot S r) (hs : IsRoot (fix r S) s) :
    fix (s ∘ r) S = fix s (fix r S) := by
  ext x
  simp only [mem_fix, Function.comp_apply]
  constructor
  · rintro ⟨hx, hsx⟩
    have h1 : r x = x := le_antisymm (hr.le x) (by
      have := hs.le (r x)
      rw [hsx] at this
      exact this)
    rw [h1] at hsx
    exact ⟨⟨hx, h1⟩, hsx⟩
  · rintro ⟨⟨hx, h1⟩, h2⟩
    rw [h1]
    exact ⟨hx, h2⟩

/-- The facts about glued partitions used for associativity. -/
lemma glue_facts {S : Finset α} {t : α → α} (ht : IsRoot S t) {ρ : α → α → α}
    (hρ : ∀ m, ρ m ∈ blockRoots S t m) {m : α} (hm : m ∈ fix t S) :
    (∀ x ∈ blk t S m, ρ m x = glue t ρ x) ∧
      fix (ρ m) (blk t S m) = blk (restrictRoot (glue t ρ) t S) (fix (glue t ρ) S) m ∧
      ∀ m' ∈ fix (ρ m) (blk t S m), blk (ρ m) (blk t S m) m' = blk (glue t ρ) S m' := by
  classical
  have hin : IsRoot (blk t S m) (ρ m) := by
    have := hρ m
    unfold blockRoots at this
    rw [if_pos hm] at this
    exact mem_roots.1 this
  have hg := ht.glue hρ
  have ha : ∀ x ∈ blk t S m, ρ m x = glue t ρ x := fun x hx => by
    unfold IPart.glue
    rw [(mem_blk.1 hx).2]
  refine ⟨ha, ?_, fun m' hm' => ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨hxb, hxx⟩ := mem_fix.1 hx
      obtain ⟨hxS, hxm⟩ := mem_blk.1 hxb
      have hfix : x ∈ fix (glue t ρ) S := mem_fix.2 ⟨hxS, by rw [← ha x hxb, hxx]⟩
      refine mem_blk.2 ⟨hfix, ?_⟩
      unfold restrictRoot
      rw [if_pos hfix, hxm]
    · intro hx
      obtain ⟨hfix, hsx⟩ := mem_blk.1 hx
      obtain ⟨hxS, hxx⟩ := mem_fix.1 hfix
      unfold restrictRoot at hsx
      rw [if_pos hfix] at hsx
      have hxb : x ∈ blk t S m := mem_blk.2 ⟨hxS, hsx⟩
      exact mem_fix.2 ⟨hxb, by rw [ha x hxb, hxx]⟩
  · obtain ⟨hm'b, -⟩ := mem_fix.1 hm'
    obtain ⟨-, hm't⟩ := mem_blk.1 hm'b
    ext x
    constructor
    · intro hx
      obtain ⟨hxb, hxm'⟩ := mem_blk.1 hx
      exact mem_blk.2 ⟨(mem_blk.1 hxb).1, by rw [← ha x hxb, hxm']⟩
    · intro hx
      obtain ⟨hxS, hxm'⟩ := mem_blk.1 hx
      have hxm : t x = m := by rw [← hg.2 x, hxm', hm't]
      have hxb : x ∈ blk t S m := mem_blk.2 ⟨hxS, hxm⟩
      exact mem_blk.2 ⟨hxb, by rw [ha x hxb, hxm']⟩

/-- **Associativity of composition along partitions**: composing with composites on the blocks
is composing the composite of the outer series with the blocks' values. -/
theorem cmp_assoc (H : Ser R X U) (G : Ser R W X) (Φ : Finset α → W) (p : α → Bool)
    (S : Finset α) :
    cmp H (fun B => cmp G Φ p B) p S
      = ∑ r ∈ roots S, sgn R p r S • cmp H (fun M => ev G (fun m' => Φ (blk r S m')) M)
          (fun m => par p (blk r S m)) (fix r S) := by
  classical
  set F : (α → α) → (α → α) → U := fun r t =>
    (sgn R p t S * ∏ m ∈ fix t S, sgn R p r (blk t S m)) •
      ev H (fun m => ev G (fun m' => Φ (blk r S m')) (blk (restrictRoot r t S) (fix r S) m))
        (fix t S) with hF
  have hB : ∀ t : α → α, (fun m => if m ∈ fix t S then roots (blk t S m) else {id})
      = blockRoots S t := fun t => by
    funext m
    unfold blockRoots
    congr
  have hL : cmp H (fun B => cmp G Φ p B) p S
      = ∑ t ∈ roots S, ∑ ρ ∈ Fintype.piFinset (blockRoots S t), F (glue t ρ) t := by
    unfold cmp
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := mem_roots.1 ht
    rw [ev_sum H (fix t S) (fun m => roots (blk t S m)) id, hB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [Fintype.mem_piFinset] at hρ
    rw [ev_smul, smul_smul, hF]
    dsimp only
    congr 1
    · congr 1
      refine Finset.prod_congr rfl fun m hm => ?_
      exact sgn_congr p (glue_facts ht' hρ hm).1
    · refine ev_congr H fun m hm => ?_
      obtain ⟨-, h2, h3⟩ := glue_facts ht' hρ hm
      rw [h2]
      refine ev_congr G fun m' hm' => ?_
      rw [← h2] at hm'
      rw [h3 m' hm']
  have hR : ∑ r ∈ roots S, sgn R p r S • cmp H (fun M => ev G (fun m' => Φ (blk r S m')) M)
      (fun m => par p (blk r S m)) (fix r S)
      = ∑ r ∈ roots S, ∑ s ∈ roots (fix r S), F r (s ∘ r) := by
    unfold cmp
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := mem_roots.1 hr
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := mem_roots.1 hs
    rw [hF]
    dsimp only
    rw [sgn_coarsen hr' (hr'.comp hs') (finer_comp r s hr'.idem), restrictRoot_comp hs',
      fix_comp hr' hs', smul_smul]
  rw [hL, hR, sum_blockRoots]

end assoc

/-! ## Relabelling -/

section relabel

variable {α β : Type*} [LinearOrder α] [Fintype α] [LinearOrder β] [Fintype β]

/-- A partition carried along an order embedding of the inputs. -/
noncomputable def liftRoot (ι : α ↪o β) (r : α → α) : β → β :=
  Function.extend ι (ι ∘ r) id

/-- A partition pulled back along an order embedding of the inputs. -/
noncomputable def pullRoot (ι : α ↪o β) (S : Finset α) (r' : β → β) : α → α := by
  classical
  exact fun x => if x ∈ S then @Function.invFun α β ⟨x⟩ ι (r' (ι x)) else x

omit [Fintype α] [Fintype β] in
lemma liftRoot_apply (ι : α ↪o β) (r : α → α) (a : α) : liftRoot ι r (ι a) = ι (r a) := by
  unfold liftRoot
  rw [ι.injective.extend_apply]
  rfl

omit [Fintype α] [Fintype β] in
lemma liftRoot_apply' (ι : α ↪o β) (r : α → α) {b : β} (hb : ¬ ∃ a, ι a = b) :
    liftRoot ι r b = b := by
  unfold liftRoot
  rw [Function.extend_apply' _ _ _ hb]
  rfl

omit [Fintype α] [Fintype β] in
lemma isRoot_lift {S : Finset α} {r : α → α} (hr : IsRoot S r) (ι : α ↪o β) :
    IsRoot (S.map ι.toEmbedding) (liftRoot ι r) := by
  have hm : ∀ {a}, ι a ∈ S.map ι.toEmbedding ↔ a ∈ S := fun {a} => by
    rw [Finset.mem_map]
    exact ⟨fun ⟨a', ha', e⟩ => ι.injective e ▸ ha', fun h => ⟨a, h, rfl⟩⟩
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b => ?_, fun b => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hb
    rw [show ι.toEmbedding a = ι a from rfl, liftRoot_apply]
    exact hm.2 (hr.mem a ha)
  · by_cases h : ∃ a, ι a = b
    · obtain ⟨a, rfl⟩ := h
      rw [liftRoot_apply, hr.off a fun h' => hb (hm.2 h')]
    · exact liftRoot_apply' ι r h
  · by_cases h : ∃ a, ι a = b
    · obtain ⟨a, rfl⟩ := h
      rw [liftRoot_apply, liftRoot_apply, hr.idem]
    · rw [liftRoot_apply' ι r h, liftRoot_apply' ι r h]
  · by_cases h : ∃ a, ι a = b
    · obtain ⟨a, rfl⟩ := h
      rw [liftRoot_apply]
      exact ι.monotone (hr.le a)
    · rw [liftRoot_apply' ι r h]

omit [Fintype α] [Fintype β] in
lemma pullRoot_lift {S : Finset α} {r : α → α} (hr : IsRoot S r) (ι : α ↪o β) :
    pullRoot ι S (liftRoot ι r) = r := by
  classical
  funext x
  unfold pullRoot
  split_ifs with hx
  · rw [liftRoot_apply, @Function.leftInverse_invFun α β ⟨x⟩ ι ι.injective]
  · exact (hr.off x hx).symm

omit [Fintype α] [Fintype β] in
lemma isRoot_pull {S : Finset α} {r' : β → β} (ι : α ↪o β)
    (hr : IsRoot (S.map ι.toEmbedding) r') :
    IsRoot S (pullRoot ι S r') ∧ liftRoot ι (pullRoot ι S r') = r' := by
  classical
  have hm : ∀ {a}, ι a ∈ S.map ι.toEmbedding ↔ a ∈ S := fun {a} => by
    rw [Finset.mem_map]
    exact ⟨fun ⟨a', ha', e⟩ => ι.injective e ▸ ha', fun h => ⟨a, h, rfl⟩⟩
  -- the root of an input of `S` is in the image
  have hroot : ∀ x ∈ S, ∃ a ∈ S, ι a = r' (ι x) := fun x hx => by
    obtain ⟨a, ha, e⟩ := Finset.mem_map.1 (hr.mem _ (hm.2 hx))
    exact ⟨a, ha, e⟩
  have hpull : ∀ x ∈ S, ι (pullRoot ι S r' x) = r' (ι x) := fun x hx => by
    unfold pullRoot
    rw [if_pos hx]
    obtain ⟨a, -, e⟩ := hroot x hx
    rw [← e, @Function.leftInverse_invFun α β ⟨x⟩ ι ι.injective]
  have hpS : ∀ x ∈ S, pullRoot ι S r' x ∈ S := fun x hx => by
    obtain ⟨a, ha, e⟩ := hroot x hx
    have := hpull x hx
    rw [← e] at this
    rwa [ι.injective this]
  have hoff : ∀ x, x ∉ S → pullRoot ι S r' x = x := fun x hx => by
    unfold pullRoot
    rw [if_neg hx]
  refine ⟨⟨hpS, hoff, fun x => ?_, fun x => ?_⟩, ?_⟩
  · by_cases hx : x ∈ S
    · apply ι.injective
      rw [hpull _ (hpS x hx), hpull x hx, hr.idem]
    · rw [hoff x hx, hoff x hx]
  · by_cases hx : x ∈ S
    · apply ι.le_iff_le.1
      rw [hpull x hx]
      exact hr.le _
    · rw [hoff x hx]
  · funext b
    by_cases h : ∃ a, ι a = b
    · obtain ⟨a, rfl⟩ := h
      rw [liftRoot_apply]
      by_cases ha : a ∈ S
      · exact hpull a ha
      · rw [hoff a ha, hr.off _ fun h' => ha (hm.1 h')]
    · rw [liftRoot_apply' ι _ h]
      exact (hr.off b fun hb => by
        obtain ⟨a, -, e⟩ := Finset.mem_map.1 hb
        exact h ⟨a, e⟩).symm

omit [Fintype α] [Fintype β] in
lemma fix_lift {S : Finset α} {r : α → α} (ι : α ↪o β) :
    fix (liftRoot ι r) (S.map ι.toEmbedding) = (fix r S).map ι.toEmbedding := by
  ext b
  rw [mem_fix, Finset.mem_map, Finset.mem_map]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, h⟩
    rw [show ι.toEmbedding a = ι a from rfl, liftRoot_apply] at h
    exact ⟨a, mem_fix.2 ⟨ha, ι.injective h⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨haS, haa⟩ := mem_fix.1 ha
    refine ⟨⟨a, haS, rfl⟩, ?_⟩
    rw [show ι.toEmbedding a = ι a from rfl, liftRoot_apply, haa]

omit [Fintype α] [Fintype β] in
lemma blk_lift {S : Finset α} {r : α → α} (ι : α ↪o β) (m : α) :
    blk (liftRoot ι r) (S.map ι.toEmbedding) (ι m) = (blk r S m).map ι.toEmbedding := by
  ext b
  rw [mem_blk, Finset.mem_map, Finset.mem_map]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, h⟩
    rw [show ι.toEmbedding a = ι a from rfl, liftRoot_apply] at h
    exact ⟨a, mem_blk.2 ⟨ha, ι.injective h⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨haS, ham⟩ := mem_blk.1 ha
    refine ⟨⟨a, haS, rfl⟩, ?_⟩
    rw [show ι.toEmbedding a = ι a from rfl, liftRoot_apply, ham]

omit [Fintype α] [Fintype β] in
lemma sgn_lift (p : β → Bool) (r : α → α) (ι : α ↪o β) (S : Finset α) :
    sgn R p (liftRoot ι r) (S.map ι.toEmbedding) = sgn R (p ∘ ι) r S := by
  unfold sgn
  rw [Finset.prod_map]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.prod_map]
  refine Finset.prod_congr rfl fun y _ => ?_
  simp only [show ∀ a, ι.toEmbedding a = ι a from fun _ => rfl, liftRoot_apply,
    ι.lt_iff_lt, Function.comp_apply]

/-- **Composites are invariant under order embeddings of the inputs.** -/
theorem cmp_map (G : Ser R W X) (ι : α ↪o β) (Φ : Finset β → W) (q : β → Bool)
    (S : Finset α) :
    cmp G (fun B => Φ (B.map ι.toEmbedding)) (q ∘ ι) S = cmp G Φ q (S.map ι.toEmbedding) := by
  classical
  unfold cmp
  symm
  refine Finset.sum_nbij' (pullRoot ι S) (liftRoot ι) (fun r' hr' => ?_) (fun r hr => ?_)
    (fun r' hr' => ?_) (fun r hr => ?_) (fun r' hr' => ?_)
  · exact mem_roots.2 (isRoot_pull ι (mem_roots.1 hr')).1
  · exact mem_roots.2 (isRoot_lift (mem_roots.1 hr) ι)
  · exact (isRoot_pull ι (mem_roots.1 hr')).2
  · exact pullRoot_lift (mem_roots.1 hr) ι
  · obtain ⟨hp, hl⟩ := isRoot_pull ι (mem_roots.1 hr')
    set r := pullRoot ι S r'
    rw [← hl, sgn_lift, fix_lift, ← ev_map]
    congr 1
    refine ev_congr G fun m _ => ?_
    simp only [Function.comp_apply]
    rw [blk_lift]

end relabel

end LSer

end Operad
