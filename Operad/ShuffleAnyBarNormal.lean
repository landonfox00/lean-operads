/-
# Normal bar trees of a shuffle operad with a Gröbner basis

For rules `G` on shuffle monomials with generators of any arity, the bar construction of the
operad they present is the quotient of the bar construction of the free shuffle operad by the
ideal of the **flagged rules** `G.bar` (`Operad.Rules.bar`): a leading monomial may be rewritten at
an uncut edge. Here, for homogeneous rules:

* **Lifting contexts** (`STree.lift_ctx`): a monomial `g h` of a context, flagged at the root,
  is a bar context applied to `h` flagged at the root.
* **The critical ambiguities of the flagged rules have no cut edge** (`STree.critical_cuts`): the
  two occurrences of leading monomials cover the monomial, and each has its edges uncut. So such
  an ambiguity is the flagged image of an ambiguity of `G`, and **resolvability passes from `G`
  to `G.bar`** (`Operad.Rules.bar_resolvable`): if the normal monomials are a basis of the
  operad presented by `G`, the normal bar trees are a basis of its bar construction.
-/
import Operad.ShuffleAnyBar

universe v

namespace Operad

namespace STree

variable {E : ℕ → Type v}

/-! ## Cut edges and positions -/

/-- **A cut edge is a vertex flagged `true`.** -/
theorem mem_cutKeys_iff : ∀ {t : STree (BE E)} {y : ℕ ×ₗ ℕ}, y ∈ cutKeys t ↔
    ∃ q, ∃ k, ∃ (d : BE E k) (c : Fin k → STree (BE E)), t.get? q = some (node d c) ∧
      d.2 = true ∧ y = key (node d c)
  | leaf _, y => by
    simp only [cutKeys, Finset.notMem_empty, false_iff]
    rintro ⟨q, k, d, c, hq, -, -⟩
    rcases q with _ | ⟨i, q⟩
    · simp at hq
    · simp at hq
  | @node _ k d c, y => by
    rw [mem_cutKeys_node]
    constructor
    · rintro (⟨hd, rfl⟩ | ⟨i, hi⟩)
      · exact ⟨[], k, d, c, rfl, hd, rfl⟩
      · obtain ⟨q, k', d', c', hq, hd', rfl⟩ := mem_cutKeys_iff.1 hi
        refine ⟨i :: q, k', d', c', ?_, hd', rfl⟩
        rw [get?_node_cons, dif_pos i.2]
        exact hq
    · rintro ⟨q, k', d', c', hq, hd', rfl⟩
      rcases q with _ | ⟨i, q⟩
      · rw [get?_nil, Option.some_inj] at hq
        cases hq
        exact Or.inl ⟨hd', rfl⟩
      · obtain ⟨hi, hq⟩ := get?_node_cons_eq_some.1 hq
        exact Or.inr ⟨⟨i, hi⟩, mem_cutKeys_iff.2 ⟨q, k', d', c', hq, hd', rfl⟩⟩

lemma weight_le_of_mem_vkeys : ∀ {t : STree E} {x : ℕ ×ₗ ℕ}, x ∈ t.vkeys →
    (ofLex x).2 ≤ t.weight
  | leaf _, _, hx => absurd hx (Multiset.notMem_zero _)
  | node e c, x, hx => by
    rcases mem_vkeys_node.1 hx with rfl | ⟨i, hi⟩
    · exact le_rfl
    · exact (weight_le_of_mem_vkeys hi).trans (weight_lt_node e c i).le

/-- **A bar tree with no cuts** has every vertex flagged `false`. -/
theorem eq_allF_of_cutKeys : ∀ {t : STree (BE E)}, cutKeys t = ∅ → t = allF (forget t)
  | leaf _, _ => rfl
  | node d c, h => by
    have hd : d.2 = false := by
      cases hd : d.2
      · rfl
      · have : key (node d c) ∈ cutKeys (node d c) := mem_cutKeys_node.2 (Or.inl ⟨hd, rfl⟩)
        rw [h] at this
        exact absurd this (Finset.notMem_empty _)
    rw [forget_node, allF_node]
    obtain ⟨d₁, d₂⟩ := d
    simp only at hd
    subst hd
    congr 1
    funext i
    refine eq_allF_of_cutKeys (Finset.eq_empty_of_forall_notMem fun y hy => ?_)
    have : y ∈ cutKeys (node (d₁, false) c) := mem_cutKeys_node.2 (Or.inr ⟨i, hy⟩)
    rw [h] at this
    exact absurd this (Finset.notMem_empty _)

lemma allF_eq_fl_false (t : STree E) : allF t = fl false t := by
  cases t <;> rfl

/-- **A bar tree whose only possible cut is at its root** is flagged at the root only. -/
theorem eq_fl_of_cutKeys {t : STree (BE E)} (h : ∀ y ∈ cutKeys t, y = key t) :
    t = fl (rootF t) (forget t) := by
  cases t with
  | leaf a => rfl
  | node d c =>
    rw [forget_node, fl_node]
    obtain ⟨d₁, d₂⟩ := d
    congr 1
    funext i
    refine eq_allF_of_cutKeys (Finset.eq_empty_of_forall_notMem fun y hy => ?_)
    have hy' := h y (mem_cutKeys_node.2 (Or.inr ⟨i, hy⟩))
    have hw := weight_le_of_mem_vkeys (mem_vkeys_of_mem_cutKeys hy)
    rw [hy', key, ofLex_toLex] at hw
    exact absurd (weight_lt_node (d₁, d₂) c i) (not_lt.2 hw)

/-! ## Flags, substitution and replacement -/

lemma fl_subst (b : Bool) {t : STree E} (ht : ∀ a, t ≠ leaf a) (xs : ℕ → STree E) :
    fl b (t.subst xs) = (fl b t).subst fun a => allF (xs a) := by
  cases t with
  | leaf a => exact absurd rfl (ht a)
  | node e c =>
    rw [subst_node, fl_node, fl_node, subst_node]
    congr 1
    funext i
    exact allF_subst (c i) xs

lemma fl_replace (b : Bool) : ∀ (t : STree E) {p : List ℕ}, p ≠ [] → ∀ u : STree E,
    fl b (t.replace p u) = (fl b t).replace p (allF u)
  | _, [], h, _ => absurd rfl h
  | leaf _, _ :: _, _, _ => rfl
  | node e c, i :: p, _, u => by
    rw [replace_node_cons, fl_node, fl_node, replace_node_cons]
    congr 1
    funext j
    split_ifs
    · exact allF_replace (c j) p u
    · rfl

lemma get?_fl (b : Bool) : ∀ (t : STree E) {p : List ℕ}, p ≠ [] →
    (fl b t).get? p = (t.get? p).map allF
  | _, [], h => absurd rfl h
  | leaf _, _ :: _, _ => rfl
  | @node _ k e c, i :: p, _ => by
    rw [fl_node, get?_node_cons, get?_node_cons]
    split_ifs with h
    · exact get?_mapG _ (c ⟨i, h⟩) p
    · rfl

/-! ## Lifting contexts -/

variable {A B C : Finset ℕ}

/-- **Lifting a context to bar trees**: a monomial `g h` of a context, flagged at the root, is a
bar context applied to `h` flagged at the root, for the monomials `h` with as many vertices as a
given one which is not a leaf. -/
theorem lift_ctx {g : SMono E C → SMono E B} (hg : IsSCtx g) (L : SMono E C)
    (hL : ∀ a, L.1 ≠ leaf a) (b : Bool) :
    ∃ (g' : SMono (BE E) C → SMono (BE E) B) (b' : Bool), IsSCtx g' ∧
      ∀ h : SMono E C, h.1.weight = L.1.weight → flM b (g h) = g' (flM b' h) := by
  obtain ⟨p, xs, hget, hin, hrep⟩ := IsSCtx.normal hg L
  have hmono : StrictMonoOn (fun a => (allF (xs a)).first) (C : Set ℕ) :=
    fun a ha a' ha' h => by simpa only [first_allF] using hin.mono ha ha' h
  have hnl : ∀ h : SMono E C, h.1.weight = L.1.weight → ∀ a, h.1 ≠ leaf a :=
    fun h hw => not_leaf_of_weight hw hL
  by_cases hp : p = []
  · subst hp
    have hgL : (g L).1 = L.1.subst xs := by
      rw [get?_nil, Option.some_inj] at hget
      exact hget
    have hget' : (flM b (g L)).1.get? [] = some ((flM b L).1.subst fun a => allF (xs a)) := by
      rw [get?_nil, flM_val, hgL, fl_subst b hL]
      rfl
    refine ⟨ctxOf (flM b (g L)) [] (flM b L) _ hget' hmono, b, isSCtx_ctxOf _ _ _ _ _ _,
      fun h hw => Subtype.ext ?_⟩
    rw [ctxOf_val, replace_nil, flM_val, hrep, replace_nil, fl_subst b (hnl h hw)]
    rfl
  · have hget' : (flM b (g L)).1.get? p = some ((flM false L).1.subst fun a => allF (xs a)) := by
      rw [flM_val, get?_fl b _ hp, hget, Option.map_some, allF_subst, allF_eq_fl_false]
      rfl
    refine ⟨ctxOf (flM b (g L)) p (flM false L) _ hget' hmono, false, isSCtx_ctxOf _ _ _ _ _ _,
      fun h hw => Subtype.ext ?_⟩
    rw [ctxOf_val, flM_val, hrep, fl_replace b _ hp, allF_subst, allF_eq_fl_false, flM_val,
      flM_val]

/-! ## Critical ambiguities of the flagged rules -/

lemma get?_eq_of_replace_eq {T u : STree (BE E)} {p : List ℕ} (h : T = T.replace p u)
    (hp : (T.get? p).isSome) : T.get? p = some u := by
  conv_lhs => rw [h]
  exact get?_replace hp u

lemma isSome_of_append {T : STree (BE E)} {p q : List ℕ} (h : (T.get? (p ++ q)).isSome) :
    (T.get? p).isSome := by
  rw [get?_append] at h
  cases hp : T.get? p with
  | none => rw [hp] at h; simp at h
  | some _ => rfl

/-- **The non-root vertices of an occurrence of a flagged monomial are not cut.** -/
lemma rootF_get?_window {T : STree (BE E)} {p q : List ℕ} {ℓ : STree E} {b : Bool}
    {xs : ℕ → STree (BE E)} (hT : T.get? p = some ((fl b ℓ).subst xs)) (hq : q ∈ vert (fl b ℓ))
    (hq0 : q ≠ []) {Z : STree (BE E)} (hZ : T.get? (p ++ q) = some Z) : rootF Z = false := by
  obtain ⟨k, d, c, hq⟩ := hq
  rw [get?_fl b ℓ hq0] at hq
  obtain ⟨u, hu, hu'⟩ := Option.map_eq_some_iff.1 hq
  rw [get?_append_of hT, get?_subst (get?_fl b ℓ hq0 ▸ Option.map_eq_some_iff.2 ⟨u, hu, hu'⟩) xs,
    Option.some_inj] at hZ
  subst hZ
  cases u with
  | leaf a => cases hu'
  | node e c' =>
    rw [allF_node] at hu'
    cases hu'
    rfl

/-- In two overlapping occurrences covering a tree, **a vertex at the root of one occurrence
lies inside the other one**, unless it is the root of the tree. -/
lemma rootF_eq_false_aux {T : STree (BE E)} {p p' : List ℕ} {ℓ ℓ' : STree (BE E)}
    (hW : ∀ z ∈ occVert p ℓ, z ≠ p → ∀ Z, T.get? z = some Z → rootF Z = false)
    (hW' : ∀ z ∈ occVert p' ℓ', z ≠ p' → ∀ Z, T.get? z = some Z → rootF Z = false)
    (hcov : vert T ⊆ occVert p ℓ ∪ occVert p' ℓ') (hov : (occVert p ℓ ∩ occVert p' ℓ').Nonempty)
    (hT : ∀ a, T ≠ leaf a) {q : List ℕ} (hq : q ∈ occVert p ℓ) (hq0 : q ≠ []) {Z : STree (BE E)}
    (hZ : T.get? q = some Z) : rootF Z = false := by
  by_cases hqp : q = p
  · subst hqp
    rcases hcov (nil_mem_vert hT) with ⟨x, -, hx⟩ | ⟨x, -, hx⟩
    · exact absurd (List.append_eq_nil_iff.1 hx).1 hq0
    · have hp' : p' = [] := (List.append_eq_nil_iff.1 hx).1
      subst hp'
      obtain ⟨z, ⟨z₁, hz₁, rfl⟩, ⟨z₂, hz₂, hz⟩⟩ := hov
      simp only [List.nil_append] at hz
      have hqv : q ∈ vert ℓ' := by
        by_cases hqz : q = z₂
        · rw [hqz]
          exact hz₂
        · exact vert_of_prefix hz₂ ⟨z₁, hz.symm⟩ hqz
      exact hW' q ⟨q, hqv, rfl⟩ hq0 Z hZ
  · exact hW q hq hqp Z hZ

end STree

open STree

variable {E : ℕ → Type v} {K : Type*} [CommRing K] {ρ : Type*} {O : STree.AdmOrder E}
  (G : Rules K ρ O.toCtxOrder)

/-- **A critical ambiguity of the flagged rules has no cut edge** below its root: the two
occurrences cover its monomial, and their edges are uncut. -/
theorem Rules.critical_cuts {C : Finset ℕ} {r₁ r₂ : ρ × Bool} (B : G.bar.Amb C r₁ r₂)
    (hB : Critical G.bar B) : ∀ y ∈ cutKeys B.top.1, y = key B.top.1 := by
  obtain ⟨p₁, p₂, xs₁, xs₂, h₁, h₂, hcov, hov⟩ := hB
  set T := B.top.1 with hT
  have e₁ : T = T.replace p₁ ((G.bar.lead r₁).1.subst xs₁) := h₁ (G.bar.lead r₁)
  have e₂ : T = T.replace p₂ ((G.bar.lead r₂).1.subst xs₂) := by
    rw [← h₂ (G.bar.lead r₂), ← B.eq]
    rfl
  have W : ∀ {p : List ℕ} {r : ρ × Bool} {xs : ℕ → STree (BE E)},
      T = T.replace p ((G.bar.lead r).1.subst xs) → ∀ z ∈ occVert p (G.bar.lead r).1, z ≠ p →
        ∀ Z, T.get? z = some Z → rootF Z = false := by
    rintro p r xs e z ⟨q, hq, rfl⟩ hne Z hZ
    have hq0 : q ≠ [] := fun h => hne (by simp only [h, List.append_nil])
    have hp : T.get? p = some ((G.bar.lead r).1.subst xs) :=
      get?_eq_of_replace_eq e (isSome_of_append (q := q) (by rw [hZ]; rfl))
    exact rootF_get?_window hp hq hq0 hZ
  intro y hy
  obtain ⟨q, k, d, c, hq, hd, rfl⟩ := mem_cutKeys_iff.1 hy
  by_cases hq0 : q = []
  · subst hq0
    rw [get?_nil, Option.some_inj] at hq
    rw [hq]
  · exfalso
    have hTl : ∀ a, T ≠ leaf a := fun a h => by
      rw [h] at hq
      rcases q with _ | ⟨i, q⟩
      · exact hq0 rfl
      · simp at hq
    have hflag : rootF (node d c) = true := hd
    rcases hcov ⟨k, d, c, hq⟩ with hq1 | hq2
    · rw [rootF_eq_false_aux (W e₁) (W e₂) hcov hov hTl hq1 hq0 hq] at hflag
      exact Bool.false_ne_true hflag
    · rw [rootF_eq_false_aux (W e₂) (W e₁) (by rwa [Set.union_comm]) (by rwa [Set.inter_comm])
        hTl hq2 hq0 hq] at hflag
      exact Bool.false_ne_true hflag

/-- **An occurrence with no cut edge below its root**: the monomials of its context flagged at
the root are flagged at the root only. -/
theorem occ_flag {A C : Finset ℕ} {f : SMono (BE E) C → SMono (BE E) A} (hf : IsSCtx f)
    (b : Bool) {f₀ : SMono E C → SMono E A} (he : ∀ X, forgetM (f X) = f₀ (forgetM X))
    (L : SMono E C) (hL : ∀ a, L.1 ≠ leaf a)
    (hcut : ∀ y ∈ cutKeys (f (flM b L)).1, y = key (f (flM b L)).1) (m : SMono E C)
    (hm : m.1.weight = L.1.weight) :
    f (flM b m) = flM (rootF (f (flM b L)).1) (f₀ m) := by
  obtain ⟨fk, b', -, H⟩ := exists_merge_ctx hf L hL b
  obtain ⟨hc, hr, hw, -⟩ := H m hm
  have hk : key (f (flM b m)).1 = key (f (flM b L)).1 := by
    rw [key, key, (f (flM b m)).first_eq (f (flM b L)), hw]
  have h1 := eq_fl_of_cutKeys (t := (f (flM b m)).1) fun y hy => by
    rw [hk]
    exact hcut y (by rw [← cuts, hc] at hy; exact hy)
  have h2 : forget (f (flM b m)).1 = (f₀ m).1 := by rw [← forgetM_val, he, forgetM_flM]
  apply Subtype.ext
  rw [flM_val, ← hr, ← h2]
  exact h1

section Transport

variable (hlead : ∀ r a, (G.lead r).1 ≠ leaf a)
  (hom : ∀ r, ∀ m ∈ (G.tail r).support, m.1.weight = (G.lead r).1.weight)
include hlead hom

/-- **Flagging maps the ideal below a monomial** into the ideal of the flagged rules below a bar
monomial over it. -/
theorem Rules.flM_mem_idealOn {C : Finset ℕ} {T : SMono (BE E) C} (b : Bool)
    {v : SMono E C →₀ K} (hv : v ∈ (G.rw C).idealOn ((G.rw C).below (forgetM T))) :
    Finsupp.mapDomain (flM b) v ∈ (G.bar.rw C).idealOn ((G.bar.rw C).below T) := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, u, ⟨r, g, hg, rfl, rfl⟩, rfl⟩ := hx
    obtain ⟨g', b', hg', H⟩ := lift_ctx hg (G.lead r) (hlead r) b
    have h1 : flM b (g (G.lead r)) = g' (G.bar.lead (r, b')) := H _ rfl
    have h2 : Finsupp.mapDomain (flM b) (Finsupp.mapDomain g (G.tail r)) =
        Finsupp.mapDomain g' (G.bar.tail (r, b')) := by
      rw [← Finsupp.mapDomain_comp]
      show _ = Finsupp.mapDomain g' (Finsupp.mapDomain (flM b') (G.tail r))
      rw [← Finsupp.mapDomain_comp]
      exact Finsupp.mapDomain_congr fun m hm => H m (hom r m hm)
    rw [Finsupp.mapDomain_sub (f := flM b), Finsupp.mapDomain_single, h1, h2]
    refine (G.bar.rw C).sub_mem_idealOn ?_ ⟨(r, b'), g', hg', rfl, rfl⟩
    show O.lt (forgetM (g' (G.bar.lead (r, b')))) (forgetM T)
    rw [← h1, forgetM_flM]
    exact hm
  | zero => rw [Finsupp.mapDomain_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Finsupp.mapDomain_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Finsupp.mapDomain_smul]; exact Submodule.smul_mem _ _ hx

/-- **The critical ambiguities of the flagged rules are resolvable** when the rules are
resolvable: such an ambiguity is the flagged image of an ambiguity of the rules. -/
theorem Rules.bar_crit_res (hres : ∀ C, (G.rw C).Resolvable) {C : Finset ℕ} {r₁ r₂ : ρ × Bool}
    (B : G.bar.Amb C r₁ r₂) (hB : Critical G.bar B) : B.Res := by
  classical
  have hcut := G.critical_cuts B hB
  obtain ⟨f₁, hf₁, he₁⟩ := IsSCtx.forget B.ctx₁
  obtain ⟨f₂, hf₂, he₂⟩ := IsSCtx.forget B.ctx₂
  have ht₁ : f₁ (G.lead r₁.1) = forgetM B.top :=
    ((he₁ (G.bar.lead r₁)).trans (congrArg f₁ (forgetM_flM r₁.2 (G.lead r₁.1)))).symm
  have ht₂ : f₂ (G.lead r₂.1) = forgetM B.top :=
    ((congrArg forgetM B.eq).trans ((he₂ (G.bar.lead r₂)).trans
      (congrArg f₂ (forgetM_flM r₂.2 (G.lead r₂.1))))).symm
  let B₀ : G.Amb C r₁.1 r₂.1 := ⟨f₁, f₂, hf₁, hf₂, ht₁.trans ht₂.symm⟩
  have hB₀ : B₀.Res := Rules.resolvable_iff.1 (hres C) r₁.1 r₂.1 B₀
  have hB₀top : B₀.top = forgetM B.top := ht₁
  have hcut₂ : ∀ y ∈ cutKeys (B.f₂ (flM r₂.2 (G.lead r₂.1))).1,
      y = key (B.f₂ (flM r₂.2 (G.lead r₂.1))).1 := by
    have : B.f₂ (flM r₂.2 (G.lead r₂.1)) = B.top := B.eq.symm
    rw [this]
    exact hcut
  have hroot₂ : rootF (B.f₂ (flM r₂.2 (G.lead r₂.1))).1 = rootF B.top.1 := by
    have : B.f₂ (flM r₂.2 (G.lead r₂.1)) = B.top := B.eq.symm
    rw [this]
  have hT₁ : Finsupp.mapDomain B.f₁ (G.bar.tail r₁) =
      Finsupp.mapDomain (flM (rootF B.top.1)) (Finsupp.mapDomain f₁ (G.tail r₁.1)) := by
    show Finsupp.mapDomain B.f₁ (Finsupp.mapDomain (flM r₁.2) (G.tail r₁.1)) = _
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun m hm =>
      occ_flag B.ctx₁ r₁.2 he₁ (G.lead r₁.1) (hlead _) hcut m (hom _ m hm)
  have hT₂ : Finsupp.mapDomain B.f₂ (G.bar.tail r₂) =
      Finsupp.mapDomain (flM (rootF B.top.1)) (Finsupp.mapDomain f₂ (G.tail r₂.1)) := by
    show Finsupp.mapDomain B.f₂ (Finsupp.mapDomain (flM r₂.2) (G.tail r₂.1)) = _
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, ← hroot₂]
    exact Finsupp.mapDomain_congr fun m hm =>
      occ_flag B.ctx₂ r₂.2 he₂ (G.lead r₂.1) (hlead _) hcut₂ m (hom _ m hm)
  have := G.flM_mem_idealOn hlead hom (T := B.top) (rootF B.top.1) (v := Finsupp.mapDomain f₁
    (G.tail r₁.1) - Finsupp.mapDomain f₂ (G.tail r₂.1)) (hB₀top ▸ hB₀)
  rw [Finsupp.mapDomain_sub (f := flM (rootF B.top.1)), ← hT₁, ← hT₂] at this
  exact this

/-- **The flagged rules are resolvable** when the rules are: if the normal monomials are a basis
of the operad presented by homogeneous rules, the normal bar trees are a basis of its bar
construction. -/
theorem Rules.bar_resolvable (hres : ∀ C, (G.rw C).Resolvable) (A : Finset ℕ) :
    (G.bar.rw A).Resolvable :=
  resolvable_of_critical G.bar (fun r a h => by
      have hl := hlead r.1
      change fl r.2 (G.lead r.1).1 = leaf a at h
      rcases hL : (G.lead r.1).1 with a' | ⟨e, c⟩
      · exact hl a' hL
      · rw [hL, fl_node] at h
        cases h)
    (fun B hB => G.bar_crit_res hlead hom hres B hB) A

end Transport

end Operad
