/-
# The universal property of presented shuffle operads

A morphism of shuffle operads out of the shuffle operad presented by rules of any arity
(`Operad.Rules.Presented`) is the same as a family of values of the generators satisfying the
relations (`Operad.Rules.Holds`).

* **Evaluation respects substitution at several leaves** (`Operad.ev_subst_on`), and so
  **contexts** (`Operad.ev_ctx`): for a context `f` from the monomials on `A` to those on `B`, the
  evaluation of `f g` is a fixed linear function of the evaluation of `g`. The inputs of the
  context are first moved to their least leaves (`Operad.STree.atFirst`) by a strictly increasing
  relabelling, then substituted one at a time, and the subtree is then grafted at its least leaf.
* Hence **evaluation kills the ideal of the rules** as soon as it kills the relations
  `lead - tail` (`Operad.Rules.evL_ideal`), and the lift of the free shuffle operad factors
  through the presented one (`Operad.Rules.presLift`), sending the generators to their values
  (`Operad.Rules.presLift_gen`). It is unique (`Operad.Rules.presented_hom_ext`), and conversely
  the values of a morphism out of the presented operad satisfy the relations
  (`Operad.Rules.holds_of_hom`), the morphism being their lift (`Operad.Rules.eq_presLift`).
-/
import Operad.ShuffleFreeUniv

universe u v w

namespace Operad

namespace STree

variable {E : ℕ → Type v}

/-! ## Substituting at several leaves -/

lemma lset_subst (t : STree E) (xs : ℕ → STree E) :
    lset (t.subst xs) = (lset t).biUnion fun a => lset (xs a) := by
  ext n
  simp only [lset, labels_subst, Multiset.mem_toFinset, Multiset.mem_bind, Finset.mem_biUnion]

lemma disjoint_lset_of_nodup_bind {s : Multiset ℕ} {xs : ℕ → STree E}
    (h : (s.bind fun a => (xs a).labels).Nodup) {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) : Disjoint (lset (xs a)) (lset (xs b)) := by
  obtain ⟨-, l, rfl, hl⟩ := Multiset.nodup_bind.1 h
  have := hl.forall (fun _ _ h => h.symm) (Multiset.mem_coe.1 ha) (Multiset.mem_coe.1 hb) hab
  exact Finset.disjoint_left.2 fun _ hn hn' =>
    Multiset.disjoint_left.1 this (mem_lset.1 hn) (mem_lset.1 hn')

/-- **Substituting valid trees at the leaves** of a valid tree, each with its leaf as least leaf
and with disjoint leaves, gives a valid tree. -/
lemma Valid.subst {s : STree E} (hs : Valid s) {xs : ℕ → STree E}
    (hx : ∀ a ∈ lset s, Valid (xs a)) (hfirst : ∀ a ∈ lset s, (xs a).first = a)
    (hdisj : ∀ a ∈ lset s, ∀ b ∈ lset s, a ≠ b → Disjoint (lset (xs a)) (lset (xs b))) :
    Valid (s.subst xs) := by
  refine ⟨isShuffle_subst hs.shuffle (fun a ha => (hx a (mem_lset.2 ha)).shuffle)
    fun a ha b hb hab => ?_, ?_⟩
  · show (xs a).first < (xs b).first
    rw [hfirst a (mem_lset.2 ha), hfirst b (mem_lset.2 hb)]
    exact hab
  · rw [labels_subst, Multiset.nodup_bind]
    refine ⟨fun a ha => (hx a (mem_lset.2 ha)).nodup,
      Multiset.Nodup.pairwise (fun a ha b hb hab => ?_) hs.nodup⟩
    have := hdisj a (mem_lset.2 ha) b (mem_lset.2 hb) hab
    exact Multiset.disjoint_left.2 fun hn hn' =>
      Finset.disjoint_left.1 this (mem_lset.2 hn) (mem_lset.2 hn')

lemma valid_leaf (a : ℕ) : Valid (leaf a : STree E) :=
  ⟨isShuffle_leaf a, Multiset.nodup_singleton a⟩

open Classical in
/-- **Substitute at the leaves in `S`** only. -/
noncomputable def substOn (S : Finset ℕ) (ys : ℕ → STree E) (b : ℕ) : STree E :=
  if b ∈ S then ys b else leaf b

lemma substOn_of_mem {S : Finset ℕ} {ys : ℕ → STree E} {b : ℕ} (hb : b ∈ S) :
    substOn S ys b = ys b := if_pos hb

lemma substOn_of_notMem {S : Finset ℕ} {ys : ℕ → STree E} {b : ℕ} (hb : b ∉ S) :
    substOn S ys b = leaf b := if_neg hb

open Classical in
/-- **The inputs of a substitution moved to their least leaves**: the input at `a ∈ A` is placed
at the least leaf of `xs a`. -/
noncomputable def atFirst (A : Finset ℕ) (xs : ℕ → STree E) (c : ℕ) : STree E :=
  if hc : ∃ a ∈ A, (xs a).first = c then xs hc.choose else leaf c

lemma atFirst_first {A : Finset ℕ} {xs : ℕ → STree E}
    (hm : Set.InjOn (fun a => (xs a).first) ↑A) {a : ℕ} (ha : a ∈ A) :
    atFirst A xs (xs a).first = xs a := by
  have hc : ∃ a' ∈ A, (xs a').first = (xs a).first := ⟨a, ha, rfl⟩
  rw [atFirst, dif_pos hc, hm hc.choose_spec.1 ha hc.choose_spec.2]

end STree

open STree

/-! ## Evaluation of substitutions and contexts -/

section Ctx

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [LinearOrder A] → Type w}
  [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (P A)] [ShuffleOperad R P]
  {E : ℕ → Type v} (φ : ∀ k, E k → P (Fin k))

/-- **Evaluation respects substitution at several leaves**: substituting valid trees, each with
its leaf as least leaf and with disjoint leaves, at the leaves in `S ⊆ A` of the valid trees on
`A` is a fixed linear function of their evaluations. -/
theorem ev_subst_on {A : Finset ℕ} {ys : ℕ → STree E} (hys : ∀ b ∈ A, Valid (ys b))
    (hfirst : ∀ b ∈ A, (ys b).first = b)
    (hdisj : ∀ b ∈ A, ∀ b' ∈ A, b ≠ b' → Disjoint (lset (ys b)) (lset (ys b'))) :
    ∀ S ⊆ A, ∃ Θ : P (NS A) →ₗ[R] P (NS (A.biUnion fun b => lset (substOn S ys b))),
      ∀ s : STree E, Valid s → ∀ hs : lset s = A,
        castN R P (by rw [lset_subst, hs]) (ev R P φ (s.subst (substOn S ys))) =
          Θ (castN R P hs (ev R P φ s)) := by
  intro S hS
  induction S using Finset.induction_on with
  | empty =>
    have h0 : substOn (∅ : Finset ℕ) ys = leaf := funext fun b => substOn_of_notMem
      (Finset.notMem_empty b)
    have hA : A = A.biUnion fun b => lset (substOn ∅ ys b) := by
      rw [h0]
      ext n
      simp
    refine ⟨castN R P hA, fun s _ hsA => ?_⟩
    rw [ev_congr φ (show s.subst (substOn ∅ ys) = s by rw [h0, subst_leaf]), castN_castN,
      castN_castN]
  | insert b S hb ih =>
    have hbA : b ∈ A := hS (Finset.mem_insert_self b S)
    obtain ⟨Θ, hΘ⟩ := ih ((Finset.subset_insert b S).trans hS)
    -- the leaves of the substituted inputs
    have hmem : ∀ c ∈ A, c ∈ lset (ys c) := fun c hc => by
      have := first_mem (hys c hc).shuffle
      rw [hfirst c hc] at this
      exact mem_lset.2 this
    have hnot : ∀ c ∈ A, c ≠ b → b ∉ lset (ys c) := fun c hc hcb h =>
      Finset.disjoint_left.1 (hdisj c hc b hbA hcb) h (hmem b hbA)
    have hbL : b ∈ A.biUnion fun c => lset (substOn S ys c) := Finset.mem_biUnion.2 ⟨b, hbA, by
      rw [substOn_of_notMem hb, lset_leaf]
      exact Finset.mem_singleton_self b⟩
    have hdL : Disjoint ((A.biUnion fun c => lset (substOn S ys c)).erase b) (lset (ys b)) := by
      refine Finset.disjoint_left.2 fun n hn hn' => ?_
      obtain ⟨hnb, hn⟩ := Finset.mem_erase.1 hn
      obtain ⟨c, hc, hnc⟩ := Finset.mem_biUnion.1 hn
      by_cases hcS : c ∈ S
      · rw [substOn_of_mem hcS] at hnc
        exact Finset.disjoint_left.1 (hdisj c hc b hbA fun h => hb (h ▸ hcS)) hnc hn'
      · rw [substOn_of_notMem hcS, lset_leaf, Finset.mem_singleton] at hnc
        rw [hnc] at hnb hn'
        exact Finset.disjoint_left.1 (hdisj c hc b hbA hnb) (hmem c hc) hn'
    have hL' : (A.biUnion fun c => lset (substOn S ys c)).erase b ∪ lset (ys b) =
        A.biUnion fun c => lset (substOn (insert b S) ys c) := by
      ext n
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_biUnion]
      constructor
      · rintro (⟨hnb, c, hc, hn⟩ | hn)
        · refine ⟨c, hc, ?_⟩
          by_cases hcS : c ∈ S
          · rwa [substOn_of_mem (Finset.mem_insert_of_mem hcS), ← substOn_of_mem (ys := ys) hcS]
          · rw [substOn_of_notMem hcS, lset_leaf, Finset.mem_singleton] at hn
            have hc' : c ∉ insert b S := by
              rw [Finset.mem_insert, not_or]
              exact ⟨fun h => hnb (hn.trans h), hcS⟩
            rw [substOn_of_notMem hc', lset_leaf, hn]
            exact Finset.mem_singleton_self c
        · exact ⟨b, hbA, by rwa [substOn_of_mem (Finset.mem_insert_self b S)]⟩
      · rintro ⟨c, hc, hn⟩
        by_cases hcb : c = b
        · rw [hcb, substOn_of_mem (Finset.mem_insert_self b S)] at hn
          exact Or.inr hn
        · by_cases hcS : c ∈ S
          · rw [substOn_of_mem (Finset.mem_insert_of_mem hcS)] at hn
            refine Or.inl ⟨fun h => hnot c hc hcb (h ▸ hn), c, hc, ?_⟩
            rwa [substOn_of_mem hcS]
          · have hc' : c ∉ insert b S := by
              rw [Finset.mem_insert, not_or]
              exact ⟨hcb, hcS⟩
            rw [substOn_of_notMem hc', lset_leaf, Finset.mem_singleton] at hn
            refine Or.inl ⟨by rw [hn]; exact hcb, c, hc, ?_⟩
            rw [substOn_of_notMem hcS, lset_leaf, hn]
            exact Finset.mem_singleton_self c
    refine ⟨castN R P hL' ∘ₗ (compN R P (A.biUnion fun c => lset (substOn S ys c)) (lset (ys b))
      b).flip (ev R P φ (ys b)) ∘ₗ Θ, fun s hs hsA => ?_⟩
    have hsub : ∀ c ∈ lset s, Valid (substOn S ys c) := fun c hc => by
      by_cases hcS : c ∈ S
      · rw [substOn_of_mem hcS]
        exact hys c (hsA ▸ hc)
      · rw [substOn_of_notMem hcS]
        exact valid_leaf c
    have hsubf : ∀ c ∈ lset s, (substOn S ys c).first = c := fun c hc => by
      by_cases hcS : c ∈ S
      · rw [substOn_of_mem hcS]
        exact hfirst c (hsA ▸ hc)
      · rw [substOn_of_notMem hcS, first_leaf]
    have hsubd : ∀ c ∈ lset s, ∀ c' ∈ lset s, c ≠ c' →
        Disjoint (lset (substOn S ys c)) (lset (substOn S ys c')) := by
      intro c hc c' hc' hcc'
      rw [hsA] at hc hc'
      by_cases hcS : c ∈ S <;> by_cases hc'S : c' ∈ S
      · rw [substOn_of_mem hcS, substOn_of_mem hc'S]
        exact hdisj c hc c' hc' hcc'
      · rw [substOn_of_mem hcS, substOn_of_notMem hc'S, lset_leaf, Finset.disjoint_singleton_right]
        exact Finset.disjoint_left.1 (hdisj c' hc' c hc (Ne.symm hcc')) (hmem c' hc')
      · rw [substOn_of_notMem hcS, substOn_of_mem hc'S, lset_leaf, Finset.disjoint_singleton_left]
        exact Finset.disjoint_left.1 (hdisj c hc c' hc' hcc') (hmem c hc)
      · rw [substOn_of_notMem hcS, substOn_of_notMem hc'S, lset_leaf, lset_leaf,
          Finset.disjoint_singleton]
        exact hcc'
    have hv₁ : Valid (s.subst (substOn S ys)) := hs.subst hsub hsubf hsubd
    have hl₁ : lset (s.subst (substOn S ys)) = A.biUnion fun c => lset (substOn S ys c) := by
      rw [lset_subst, hsA]
    have hsplit : s.subst (substOn (insert b S) ys) =
        (s.subst (substOn S ys)).subst (Function.update leaf b (ys b)) := by
      rw [subst_subst]
      refine subst_congr _ fun c hc => ?_
      show substOn (insert b S) ys c = (substOn S ys c).subst (Function.update leaf b (ys b))
      have hcA : c ∈ A := hsA ▸ mem_lset.2 hc
      by_cases hcb : c = b
      · rw [hcb, substOn_of_mem (Finset.mem_insert_self b S), substOn_of_notMem hb, subst_leaf',
          Function.update_self]
      · by_cases hcS : c ∈ S
        · rw [substOn_of_mem (Finset.mem_insert_of_mem hcS), substOn_of_mem hcS]
          conv_lhs => rw [← subst_leaf (ys c)]
          refine subst_congr _ fun n hn => (Function.update_of_ne ?_ _ _).symm
          rintro rfl
          exact hnot c hcA hcb (mem_lset.2 hn)
        · have hc' : c ∉ insert b S := by
            rw [Finset.mem_insert, not_or]
            exact ⟨hcb, hcS⟩
          rw [substOn_of_notMem hc', substOn_of_notMem hcS, subst_leaf',
            Function.update_of_ne hcb]
    have hb₁ : b ∈ lset (s.subst (substOn S ys)) := hl₁ ▸ hbL
    have hd₁ : Disjoint ((lset (s.subst (substOn S ys))).erase b) (lset (ys b)) := hl₁ ▸ hdL
    have key := hΘ s hs hsA
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    rw [← key, ev_congr φ hsplit, ev_subst φ hv₁ (hys b hbA) hb₁ (hfirst b hbA) hd₁,
      ← castN_rfl (R := R) (ev R P φ (ys b)), compN_castN]
    simp only [castN_castN, castN_rfl]

/-- **Evaluation respects contexts**: for a context `f` from the monomials on `A` to those on
`B`, the evaluation of `f g` is a fixed linear function of the evaluation of `g`. -/
theorem ev_ctx {A B : Finset ℕ} {f : SMono E A → SMono E B} (hf : IsSCtx f) :
    ∃ Φ : P (NS A) →ₗ[R] P (NS B), ∀ g : SMono E A,
      castN R P (lset_smono (f g)) (ev R P φ (f g).1) =
        Φ (castN R P (lset_smono g) (ev R P φ g.1)) := by
  rcases isEmpty_or_nonempty (SMono E A) with hA | hA
  · exact ⟨0, fun g => (hA.false g).elim⟩
  obtain ⟨g₀⟩ := hA
  obtain ⟨T, p, xs, hp, hxs, hfx⟩ := hf
  -- the inputs are valid, with disjoint leaves
  have hU : ∀ g : SMono E A, (g.1.subst xs).labels ≤ B.val := fun g => by
    rw [← (f g).labels_eq, hfx g]
    exact labels_get?_le (get?_replace hp _)
  have hnd := Multiset.nodup_of_le (hU g₀) B.nodup
  rw [labels_subst, g₀.labels_eq] at hnd
  have hvx : ∀ a ∈ A, Valid (xs a) := fun a ha =>
    ⟨hxs.shuffle a ha, (Multiset.nodup_bind.1 hnd).1 a ha⟩
  have hdx : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → Disjoint (lset (xs a)) (lset (xs a')) :=
    fun a ha a' ha' h => disjoint_lset_of_nodup_bind hnd ha ha' h
  -- the inputs moved to their least leaves
  set h : ℕ → ℕ := fun a => (xs a).first with hh
  have hmono : StrictMonoOn h ↑A := hxs.mono
  set ys := atFirst A xs with hys_def
  have hys : ∀ a ∈ A, ys (h a) = xs a := fun a ha => atFirst_first hmono.injOn ha
  set A' := A.image h with hA'
  have hysv : ∀ c ∈ A', Valid (ys c) := fun c hc => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    rw [hys a ha]
    exact hvx a ha
  have hysf : ∀ c ∈ A', (ys c).first = c := fun c hc => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    rw [hys a ha]
  have hysd : ∀ c ∈ A', ∀ c' ∈ A', c ≠ c' → Disjoint (lset (ys c)) (lset (ys c')) := by
    intro c hc c' hc' hcc'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hc'
    rw [hys a ha, hys a' ha']
    exact hdx a ha a' ha' fun e => hcc' (congrArg h e)
  obtain ⟨Θ, hΘ⟩ := ev_subst_on (R := R) φ hysv hysf hysd A' (Finset.Subset.refl _)
  have hsubst : ∀ g : SMono E A, (g.1.relabel h).subst (substOn A' ys) = g.1.subst xs :=
    fun g => by
      rw [relabel_subst]
      refine subst_congr _ fun a ha => ?_
      have haA : a ∈ A := g.mem_labels.1 ha
      rw [substOn_of_mem (Finset.mem_image_of_mem h haA), hys a haA]
  have hlr : ∀ g : SMono E A, lset (g.1.relabel h) = A' := fun g => by
    rw [lset_relabel, lset_smono]
  have hfg : ∀ g : SMono E A, StrictMonoOn h ↑(lset g.1) := fun g => by
    rw [lset_smono]
    exact hmono
  have hLg : ∀ g : SMono E A, lset (g.1.subst xs) = A'.biUnion fun c => lset (substOn A' ys c) :=
    fun g => by
    rw [← hsubst g, lset_subst, hlr g]
  -- the inner part: substituting the inputs
  have hin : ∀ g : SMono E A, Θ (ShuffleOperad.map (R := R) (relIso h hmono)
      (castN R P (lset_smono g) (ev R P φ g.1))) =
      castN R P (hLg g) (ev R P φ (g.1.subst xs)) := fun g => by
    have := hΘ (g.1.relabel h) (g.valid.relabel (hfg g)) (hlr g)
    rw [ev_relabel φ g.valid (hfg g), castN_castN] at this
    rw [map_relIso_castN, ← this, ev_congr φ (hsubst g).symm, castN_castN]
  -- the outer part: grafting the substituted subtree at its least leaf
  obtain ⟨b, hb⟩ : ∃ b, (g₀.1.subst xs).first = b := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T', T.replace p (leaf b) = T' := ⟨_, rfl⟩
  have hUfirst : ∀ g : SMono E A, (g.1.subst xs).first = b := fun g => by
    rw [← hb, first_subst g.isShuffle, first_subst g₀.isShuffle, g.first_eq g₀]
  have hUl : ∀ g : SMono E A, (g.1.subst xs).labels = (g₀.1.subst xs).labels := fun g => by
    rw [labels_subst, labels_subst, g.labels_eq, g₀.labels_eq]
  have hUv : ∀ g : SMono E A, Valid (g.1.subst xs) := fun g =>
    ⟨isShuffle_get? (p := p) (f g).isShuffle (by rw [hfx g]; exact get?_replace hp _),
      Multiset.nodup_of_le (hU g) B.nodup⟩
  have hW : (T.replace p (g₀.1.subst xs)).replace p (leaf b) = T' := by
    rw [replace_replace, hT']
  have hlab := labels_replace (get?_replace hp (g₀.1.subst xs)) (leaf b)
  rw [hW, ← hfx g₀, (f g₀).labels_eq, labels_leaf] at hlab
  have hbU : b ∈ (g₀.1.subst xs).labels := hb ▸ first_mem (hUv g₀).shuffle
  obtain ⟨U', hU'⟩ := Multiset.exists_cons_of_mem hbU
  have hTU : T'.labels + U' = B.val := by
    have : b ::ₘ (T'.labels + U') = b ::ₘ B.val := by
      rw [← Multiset.add_cons, ← hU', hlab, ← Multiset.singleton_add, add_comm]
    exact (Multiset.cons_inj_right b).1 this
  have hBnd := B.nodup
  rw [← hTU, Multiset.nodup_add] at hBnd
  obtain ⟨hT'nd, -, hT'U'⟩ := hBnd
  have hT'get : T'.get? p = some (leaf b) := hT' ▸ get?_replace hp (leaf b)
  have hbT : b ∈ lset T' := mem_lset.2 (mem_labels_of_get? hT'get)
  have hT'v : Valid T' := ⟨by
    rw [← hW]
    exact isShuffle_replace (by rw [← hfx g₀]; exact (f g₀).isShuffle) (get?_replace hp _)
      (isShuffle_leaf b) ((first_leaf b).trans hb.symm), hT'nd⟩
  have hdT : ∀ g : SMono E A, Disjoint ((lset T').erase b) (lset (g.1.subst xs)) := fun g => by
    refine Finset.disjoint_left.2 fun n hn hn' => ?_
    obtain ⟨hnb, hn⟩ := Finset.mem_erase.1 hn
    rw [mem_lset, hUl g, hU', Multiset.mem_cons] at hn'
    exact Multiset.disjoint_left.1 hT'U' (mem_lset.1 hn) (hn'.resolve_left hnb)
  have hsplit : ∀ g : SMono E A,
      (f g).1 = T'.subst (Function.update leaf b (g.1.subst xs)) := fun g => by
    rw [subst_update hT'nd hT'get, subst_leaf, ← hT', replace_replace, hfx g]
  have hB : (lset T').erase b ∪ (A'.biUnion fun c => lset (substOn A' ys c)) = B := by
    rw [← hLg g₀, ← lset_subst_update hbT, ← hsplit g₀, lset_smono]
  refine ⟨castN R P hB ∘ₗ compN R P (lset T') (A'.biUnion fun c => lset (substOn A' ys c)) b
    (ev R P φ T') ∘ₗ Θ ∘ₗ ShuffleOperad.map (R := R) (relIso h hmono), fun g => ?_⟩
  simp only [LinearMap.comp_apply]
  rw [hin g, ← castN_rfl (R := R) (ev R P φ T'), compN_castN, ev_congr φ (hsplit g),
    ev_subst φ hT'v (hUv g) hbT (hUfirst g) (hdT g)]
  simp only [castN_castN]

variable (R P) in
/-- **The evaluation of combinations of monomials** on a finite set of natural numbers. -/
noncomputable def evL (C : Finset ℕ) : (SMono E C →₀ R) →ₗ[R] P (NS C) :=
  Finsupp.linearCombination R fun m => castN R P (lset_smono m) (ev R P φ m.1)

lemma evL_single {C : Finset ℕ} (m : SMono E C) :
    evL R P φ C (Finsupp.single m 1) = castN R P (lset_smono m) (ev R P φ m.1) := by
  rw [evL, Finsupp.linearCombination_single, one_smul]

/-- **Evaluation of combinations respects contexts.** -/
theorem evL_mapDomain {A B : Finset ℕ} {f : SMono E A → SMono E B} (hf : IsSCtx f) :
    ∃ Φ : P (NS A) →ₗ[R] P (NS B), ∀ v : SMono E A →₀ R,
      evL R P φ B (Finsupp.mapDomain f v) = Φ (evL R P φ A v) := by
  obtain ⟨Φ, hΦ⟩ := ev_ctx (R := R) φ hf
  refine ⟨Φ, fun v => ?_⟩
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [Finsupp.mapDomain_add, map_add, map_add, map_add, hv, hw]
  | single m r =>
    simp only [Finsupp.mapDomain_single, evL, Finsupp.linearCombination_single, map_smul]
    rw [hΦ]

end Ctx

/-! ## The universal property -/

section Univ

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [LinearOrder A] → Type w}
  [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (P A)] [ShuffleOperad R P]
  {E : ℕ → Type v} {ρ : Type*} {O : AdmOrder E} (G : Rules R ρ O.toCtxOrder)
  (φ : ∀ k, E k → P (Fin k))

/-- **The values of the generators satisfy the relations**: each relation `lead - tail`
evaluates to zero. -/
def Rules.Holds : Prop :=
  ∀ r, evL R P φ (G.src r) (Finsupp.single (G.lead r) 1 - G.tail r) = 0

variable {G φ}

/-- **Evaluation kills the ideal of the rules** when it kills the relations. -/
theorem Rules.evL_ideal (hφ : G.Holds φ) (C : Finset ℕ) {v : SMono E C →₀ R}
    (hv : v ∈ (G.rw C).ideal) : evL R P φ C v = 0 := by
  rw [Rules.ideal_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, f, hf, rfl⟩ := hx
    obtain ⟨Φ, hΦ⟩ := evL_mapDomain (R := R) φ (f := f) hf
    rw [hΦ, hφ r, map_zero]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

lemma FreeSh.liftApp_eq_evL (A : Type) [Fintype A] [LinearOrder A] (x : FreeSh R E A) :
    FreeSh.liftApp R P φ A x = ShuffleOperad.map (R := R) (rangeIso A) (evL R P φ _ x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  | single m r => simp only [FreeSh.liftApp, evL, Finsupp.linearCombination_single, map_smul]

variable (G) in
/-- **The universal property of the presented shuffle operad**, existence: values of the
generators satisfying the relations extend to a morphism of shuffle operads out of the presented
operad. -/
noncomputable def Rules.presLift (hφ : G.Holds φ) : ShuffleOperadHom R G.Presented P :=
  G.shuffleIdeal.liftHom (FreeSh.lift R P φ) fun A _ _ x hx => by
    show FreeSh.liftApp R P φ A x = 0
    rw [FreeSh.liftApp_eq_evL, Rules.evL_ideal hφ _ hx, map_zero]

lemma Rules.presLift_proj (hφ : G.Holds φ) (A : Type) [Fintype A] [LinearOrder A]
    (x : FreeSh R E A) :
    (G.presLift hφ).app A (G.shuffleIdeal.proj A x) = (FreeSh.lift R P φ).app A x := rfl

/-- **The lift sends the generators to their values.** -/
theorem Rules.presLift_gen (hφ : G.Holds φ) {k : ℕ} (hk : 0 < k) (g : E k) :
    (G.presLift hφ).app (Fin k) (G.shuffleIdeal.proj _ (Finsupp.single (FreeSh.genM hk g) 1)) =
      φ k g :=
  FreeSh.lift_gen φ hk g

/-- **The universal property of the presented shuffle operad**, uniqueness: two morphisms out of
the presented operad agreeing on the generators agree. -/
theorem Rules.presented_hom_ext {ψ₁ ψ₂ : ShuffleOperadHom R G.Presented P}
    (h : ∀ k (hk : 0 < k) (g : E k),
      ψ₁.app (Fin k) (G.shuffleIdeal.proj _ (Finsupp.single (FreeSh.genM hk g) 1)) =
        ψ₂.app (Fin k) (G.shuffleIdeal.proj _ (Finsupp.single (FreeSh.genM hk g) 1))) :
    ψ₁ = ψ₂ :=
  ShuffleOperadHom.ext fun A _ _ q => G.shuffleIdeal.hom_ext_proj
    (fun A _ _ x => FreeSh.hom_ext (ψ₁ := ψ₁.comp G.shuffleIdeal.projHom)
      (ψ₂ := ψ₂.comp G.shuffleIdeal.projHom) h A x) A q

/-! ## The converse -/

omit [ShuffleOperad R P] in
lemma castN_eq_zero_iff {S S' : Finset ℕ} (h : S = S') {x : P (NS S)} :
    castN R P h x = 0 ↔ x = 0 := by
  subst h
  rfl

lemma map_eq_zero_iff {A B : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    (e : A ≃o B) {x : P A} : ShuffleOperad.map (R := R) e x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have := congrArg (ShuffleOperad.map (R := R) e.symm) h
  rwa [← ShuffleOperad.map_trans, OrderIso.self_trans_symm, ShuffleOperad.map_refl, map_zero]
    at this

/-- **Normal forms are a context**: relabelling the leaves of the monomials on `C` by their
positions. -/
lemma isSCtx_normalize (C : Finset ℕ) :
    IsSCtx (fun m : SMono E C => normalize m.valid (lset_smono m)) :=
  ⟨leaf 0, [], fun a => leaf (posIn C a), rfl, ⟨fun _ _ => trivial, fun a ha n hn => by
      rw [labels_leaf, Multiset.mem_singleton] at hn
      rw [hn, ← image_posIn C]
      exact Finset.mem_image_of_mem _ ha, strictMonoOn_posIn C⟩,
    fun _ => (replace_nil _ _).symm⟩

/-- **Evaluation of normal forms**: relabelling by the positions. -/
lemma evL_normalize (C : Finset ℕ) (v : SMono E C →₀ R) :
    evL R P φ _ (Finsupp.mapDomain (fun m : SMono E C => normalize m.valid (lset_smono m)) v) =
      castN R P (image_posIn C) (ShuffleOperad.map (R := R)
        (relIso (posIn C) (strictMonoOn_posIn C)) (evL R P φ C v)) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [Finsupp.mapDomain_add, map_add, hv, hw]
  | single m r =>
    simp only [Finsupp.mapDomain_single, evL, Finsupp.linearCombination_single, map_smul]
    congr 1
    have hf : StrictMonoOn (posIn C) ↑(lset m.1) := by
      rw [lset_smono]
      exact strictMonoOn_posIn C
    rw [ev_congr φ (normalize_val m.valid (lset_smono m)), ev_relabel φ m.valid hf,
      map_relIso_castN]
    simp only [castN_castN]

variable (G) in
/-- **The values of the generators** under a morphism out of the presented operad. -/
noncomputable def Rules.homValues (ψ : ShuffleOperadHom R G.Presented P) (k : ℕ) (g : E k) :
    P (Fin k) :=
  if hk : 0 < k then
    ψ.app (Fin k) (G.shuffleIdeal.proj _ (Finsupp.single (FreeSh.genM hk g) 1))
  else 0

/-- **The values of the generators under a morphism out of the presented operad satisfy the
relations.** -/
theorem Rules.holds_of_hom (ψ : ShuffleOperadHom R G.Presented P) : G.Holds (G.homValues ψ) := by
  intro r
  have hv : Finsupp.single (G.lead r) 1 - G.tail r ∈ (G.rw (G.src r)).ideal := by
    rw [Rules.ideal_eq_span]
    exact Submodule.subset_span ⟨r, id, O.toCtxOrder.ctx_id _, by rw [Finsupp.mapDomain_id]⟩
  have hν := G.mapDomain_mem_ideal (isSCtx_normalize (G.src r)) hv
  have hψ : ∀ x, ψ.app (NS (G.src r)) (G.shuffleIdeal.proj _ x) =
      FreeSh.liftApp R P (G.homValues ψ) (NS (G.src r)) x := fun x =>
    FreeSh.eq_lift (G.homValues ψ) (ψ := ψ.comp G.shuffleIdeal.projHom) (fun k hk g => by
      show ψ.app (Fin k) (G.shuffleIdeal.proj _ _) = _
      rw [Rules.homValues, dif_pos hk]) (NS (G.src r)) x
  have hp : G.shuffleIdeal.proj (NS (G.src r)) (Finsupp.mapDomain
      (fun m : SMono E (G.src r) => normalize m.valid (lset_smono m))
      (Finsupp.single (G.lead r) 1 - G.tail r)) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hν
  have h0 := congrArg (ψ.app (NS (G.src r))) hp
  rw [map_zero, hψ, FreeSh.liftApp_eq_evL, evL_normalize] at h0
  rwa [map_eq_zero_iff, castN_eq_zero_iff, map_eq_zero_iff] at h0

/-- **The universal property of the presented shuffle operad**: a morphism out of the presented
operad is the lift of its values on the generators. -/
theorem Rules.eq_presLift (ψ : ShuffleOperadHom R G.Presented P) :
    ψ = G.presLift (Rules.holds_of_hom ψ) :=
  Rules.presented_hom_ext fun k hk g => by
    rw [Rules.presLift_gen, Rules.homValues, dif_pos hk]

end Univ

end Operad
