/-
# PBW implies Koszul for shuffle operads with generators of any arity

**Koszulness** (`Operad.Rules.IsKoszul`) of the shuffle operad presented by quadratic rules `G`:
its bar construction is the bar construction of the free shuffle operad (`STree.Bar.C`, with
the differential `STree.Bar.d`) modulo the ideal of the flagged rules (`Operad.Rules.bar`), a
subcomplex; Koszulness is the vanishing of its homology below the diagonal, in every arity.

**The theorem** (`Operad.Rules.isKoszul_of_resolvable`): if the rules are quadratic and
resolvable — the normal monomials are a basis of the operad they present, a PBW basis — the
operad is Koszul. The proof is Hoffbeck's:

* The normal bar trees are a basis of the bar construction (`Operad.Rules.bar_resolvable`), and
  **normality is local** (`STree.bar_normal_iff`, `STree.bar_normal_iff_quad`): a bar tree is
  normal if and only if every edge of its underlying monomial whose window is a leading
  monomial — the set `STree.leadKeys` — is cut.
* So the differential on the normal bar trees is, up to terms over strictly smaller underlying
  monomials, its **leading part**, merging only along the cut edges with a window which is not
  leading; over a fixed monomial the leading part is the complex of the subsets of a finite set,
  contracted by cutting along an edge with a window which is not leading
  (`Operad.CutComplex.dL_hL_add`), and below the diagonal such an edge exists.
* **Hoffbeck's filtration argument** (`Operad.Hoffbeck.exact_of_leading`) concludes.
-/
import Operad.ShuffleAnyBarNormal

universe v

namespace Operad

namespace STree

variable {E : ℕ → Type v}

/-! ## The keys of an occurrence -/

/-- **The keys of the vertices of a tree in a substitution**: the keys of its substituted
subtrees. -/
def wk (xs : ℕ → STree E) : STree E → Finset (ℕ ×ₗ ℕ)
  | leaf _ => ∅
  | node e c => insert (key ((node e c).subst xs)) (Finset.univ.biUnion fun i => wk xs (c i))

/-- **The keys of the edges of an occurrence**: those of its vertices other than the root. -/
def nwk (xs : ℕ → STree E) : STree E → Finset (ℕ ×ₗ ℕ)
  | leaf _ => ∅
  | node _ c => Finset.univ.biUnion fun i => wk xs (c i)

@[simp] lemma wk_leaf (xs : ℕ → STree E) (a : ℕ) : wk xs (leaf a) = ∅ := rfl

lemma wk_node (xs : ℕ → STree E) {k : ℕ} (e : E k) (c : Fin k → STree E) :
    wk xs (node e c) =
      insert (key ((node e c).subst xs)) (Finset.univ.biUnion fun i => wk xs (c i)) := rfl

lemma nwk_node (xs : ℕ → STree E) {k : ℕ} (e : E k) (c : Fin k → STree E) :
    nwk xs (node e c) = Finset.univ.biUnion fun i => wk xs (c i) := rfl

/-- **A sub-bar-tree's cut edges are cut edges.** -/
theorem cutKeys_subset_of_get? : ∀ {T Y : STree (BE E)} {p : List ℕ}, T.get? p = some Y →
    cutKeys Y ⊆ cutKeys T
  | T, Y, [], h => by
    rw [get?_nil, Option.some_inj] at h
    rw [h]
  | leaf _, _, _ :: _, h => by simp at h
  | node d c, Y, i :: p, h => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    intro y hy
    exact mem_cutKeys_node.2 (Or.inr ⟨⟨i, hi⟩, cutKeys_subset_of_get? h hy⟩)

lemma mem_vkeys_of_get? : ∀ {T Y : STree (BE E)} {p : List ℕ}, T.get? p = some Y →
    Y.vkeys ≤ T.vkeys
  | T, Y, [], h => by
    rw [get?_nil, Option.some_inj] at h
    rw [h]
  | leaf _, _, _ :: _, h => by simp at h
  | node d c, Y, i :: p, h => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    refine (mem_vkeys_of_get? h).trans ?_
    rw [vkeys_node]
    exact (Finset.single_le_sum (f := fun j => (c j).vkeys) (fun _ _ => Multiset.zero_le _)
      (Finset.mem_univ _)).trans (Multiset.le_cons_self _ _)

lemma nodup_vkeys_children {k : ℕ} {d : BE E k} {c : Fin k → STree (BE E)}
    (hn : (node d c).vkeys.Nodup) :
    key (node d c) ∉ ∑ i, (c i).vkeys ∧ (∀ i, (c i).vkeys.Nodup) ∧
      ∀ i j, i ≠ j → Disjoint (c i).vkeys (c j).vkeys := by
  rw [vkeys_node, Multiset.nodup_cons] at hn
  refine ⟨hn.1, fun i => Multiset.nodup_of_le (Finset.single_le_sum
    (f := fun j => (c j).vkeys) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)) hn.2,
    fun i j hij => ?_⟩
  have hle : (c i).vkeys + (c j).vkeys ≤ ∑ l, (c l).vkeys := by
    rw [← Finset.sum_pair (f := fun l => (c l).vkeys) hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => Multiset.zero_le _
  exact (Multiset.nodup_add.1 (Multiset.nodup_of_le hle hn.2)).2.2

/-- **A cut edge of a tree with distinct keys which is a vertex of a subtree is a cut edge of
the subtree.** -/
theorem mem_cutKeys_of_get? : ∀ {T Y : STree (BE E)} {p : List ℕ}, T.vkeys.Nodup →
    T.get? p = some Y → ∀ {y : ℕ ×ₗ ℕ}, y ∈ cutKeys T → y ∈ Y.vkeys → y ∈ cutKeys Y
  | T, Y, [], _, h, _, hy, _ => by
    rw [get?_nil, Option.some_inj] at h
    rwa [← h]
  | leaf _, _, _ :: _, _, h, _, _, _ => by simp at h
  | node d c, Y, i :: p, hn, h, y, hy, hyY => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    obtain ⟨hroot, hnc, hdisj⟩ := nodup_vkeys_children hn
    have hyc : y ∈ (c ⟨i, hi⟩).vkeys := Multiset.mem_of_le (mem_vkeys_of_get? h) hyY
    rcases mem_cutKeys_node.1 hy with ⟨-, rfl⟩ | ⟨j, hj⟩
    · exact absurd ((Multiset.mem_sum (s := Finset.univ)).2 ⟨⟨i, hi⟩, Finset.mem_univ _, hyc⟩)
        hroot
    · by_cases hij : j = ⟨i, hi⟩
      · subst hij
        exact mem_cutKeys_of_get? (hnc _) h hj hyY
      · exact absurd hyc (Multiset.disjoint_left.1 (hdisj j _ hij) (mem_vkeys_of_mem_cutKeys hj))

/-- The keys of the vertices of a tree substituted into a bar tree with no cuts are keys of its
vertices, and are not cut, the keys being distinct. -/
theorem wk_props : ∀ (g : STree E) (F : ℕ → STree (BE E)),
    ((allF g).subst F).vkeys.Nodup → ∀ y ∈ wk (fun a => forget (F a)) g,
      y ∈ ((allF g).subst F).vkeys ∧ y ∉ cutKeys ((allF g).subst F)
  | leaf _, _, _, y, hy => absurd hy (Finset.notMem_empty _)
  | node e c, F, hn, y, hy => by
    rw [allF_node, subst_node] at hn ⊢
    obtain ⟨hroot, hnc, hdisj⟩ := nodup_vkeys_children hn
    have hf : forget (node (e, false) fun i => (allF (c i)).subst F) =
        (node e c).subst fun a => forget (F a) := by
      rw [forget_node, subst_node]
      congr 1
      funext i
      rw [forget_subst, forget_allF]
    have hkey : key ((node e c).subst fun a => forget (F a)) =
        key (node (e, false) fun i => (allF (c i)).subst F) := by
      rw [← hf, key_forget]
    rw [wk_node, Finset.mem_insert, Finset.mem_biUnion] at hy
    rcases hy with rfl | ⟨i, -, hi⟩
    · rw [hkey]
      refine ⟨mem_vkeys_node.2 (Or.inl rfl), fun h => ?_⟩
      rcases mem_cutKeys_node.1 h with ⟨h, -⟩ | ⟨j, hj⟩
      · exact Bool.false_ne_true h
      · exact hroot ((Multiset.mem_sum (s := Finset.univ)).2
          ⟨j, Finset.mem_univ _, mem_vkeys_of_mem_cutKeys hj⟩)
    · obtain ⟨h1, h2⟩ := wk_props (c i) F (hnc i) y hi
      refine ⟨mem_vkeys_node.2 (Or.inr ⟨i, h1⟩), fun h => ?_⟩
      rcases mem_cutKeys_node.1 h with ⟨-, rfl⟩ | ⟨j, hj⟩
      · exact hroot ((Multiset.mem_sum (s := Finset.univ)).2 ⟨i, Finset.mem_univ _, h1⟩)
      · by_cases hij : j = i
        · subst hij
          exact h2 hj
        · exact Multiset.disjoint_left.1 (hdisj j i hij) (mem_vkeys_of_mem_cutKeys hj) h1

/-! ## Lifting occurrences to bar trees -/

lemma exists_glue {k : ℕ} {e : E k} {c : Fin k → STree E} (hn : (node e c).labels.Nodup)
    (F : Fin k → ℕ → STree (BE E)) :
    ∃ G : ℕ → STree (BE E), ∀ i, ∀ a ∈ (c i).labels, G a = F i a := by
  classical
  refine ⟨fun a => if h : ∃ i, a ∈ (c i).labels then F h.choose a else leaf a, fun i a ha => ?_⟩
  have h : ∃ i, a ∈ (c i).labels := ⟨i, ha⟩
  dsimp only
  rw [dif_pos h]
  by_cases hi : h.choose = i
  · rw [hi]
  · exact absurd ha (not_mem_of_node hn hi h.choose_spec)

lemma node_injective_forget {k k' : ℕ} {d : BE E k'} {c' : Fin k' → STree (BE E)} {e : E k}
    {c : Fin k → STree E} (h : forget (node d c') = node e c) :
    ∃ hk : k' = k, hk ▸ d.1 = e ∧ ∀ i, forget (c' (hk ▸ i)) = c i := by
  rw [forget_node] at h
  injection h with hk he hc
  subst hk
  exact ⟨rfl, eq_of_heq he, fun i => congrFun (eq_of_heq hc) i⟩

/-- **Lifting an occurrence to a bar tree**: a bar tree over a substituted tree, none of whose
vertices coming from the tree is cut, is that tree with no cuts, with bar trees substituted. -/
theorem lift_allF : ∀ (g : STree E) (Y : STree (BE E)) (xs₀ : ℕ → STree E), g.labels.Nodup →
    forget Y = g.subst xs₀ → (∀ y ∈ wk xs₀ g, y ∉ cutKeys Y) →
    ∃ F : ℕ → STree (BE E), Y = (allF g).subst F ∧ ∀ a ∈ g.labels, forget (F a) = xs₀ a
  | leaf a, Y, xs₀, _, hY, _ => ⟨fun _ => Y, rfl, fun b hb => by
      rw [labels_leaf, Multiset.mem_singleton] at hb
      subst hb
      exact hY⟩
  | node e c, Y, xs₀, hn, hY, hcut => by
    cases Y with
    | leaf a => cases hY
    | node d c' =>
      rw [subst_node] at hY
      obtain ⟨hk, hd, hc⟩ := node_injective_forget hY
      subst hk
      have hd2 : d.2 = false := by
        cases hd2 : d.2
        · rfl
        · refine absurd (mem_cutKeys_node.2 (Or.inl ⟨hd2, rfl⟩)) (hcut _ ?_)
          rw [wk_node, ← key_forget, hY, ← subst_node]
          exact Finset.mem_insert_self _ _
      have hcut' : ∀ i, ∀ y ∈ wk xs₀ (c i), y ∉ cutKeys (c' i) := fun i y hy h =>
        hcut y (by
          rw [wk_node]
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hy⟩))
          (mem_cutKeys_node.2 (Or.inr ⟨i, h⟩))
      choose F hF hF' using fun i =>
        lift_allF (c i) (c' i) xs₀ (nodup_of_node hn i) (hc i) (hcut' i)
      obtain ⟨G, hG⟩ := exists_glue hn F
      refine ⟨G, ?_, fun a ha => ?_⟩
      · obtain ⟨d₁, d₂⟩ := d
        simp only at hd hd2
        subst hd hd2
        rw [allF_node, subst_node]
        congr 1
        funext i
        rw [hF i]
        exact subst_congr _ fun a ha => (hG i a (by rwa [labels_allF] at ha)).symm
      · obtain ⟨i, hi⟩ := mem_labels_node.1 ha
        rw [hG i a hi]
        exact hF' i a hi

/-- **Lifting an occurrence flagged at the root.** -/
theorem lift_fl {k : ℕ} (e : E k) (c : Fin k → STree E) (Y : STree (BE E)) (xs₀ : ℕ → STree E)
    (hn : (node e c).labels.Nodup) (hY : forget Y = (node e c).subst xs₀)
    (hcut : ∀ y ∈ nwk xs₀ (node e c), y ∉ cutKeys Y) :
    ∃ F : ℕ → STree (BE E), Y = (fl (rootF Y) (node e c)).subst F ∧
      ∀ a ∈ (node e c).labels, forget (F a) = xs₀ a := by
  cases Y with
  | leaf a => cases hY
  | node d c' =>
    rw [subst_node] at hY
    obtain ⟨hk, hd, hc⟩ := node_injective_forget hY
    subst hk
    have hcut' : ∀ i, ∀ y ∈ wk xs₀ (c i), y ∉ cutKeys (c' i) := fun i y hy h =>
      hcut y (by rw [nwk_node]; exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hy⟩)
        (mem_cutKeys_node.2 (Or.inr ⟨i, h⟩))
    choose F hF hF' using fun i =>
      lift_allF (c i) (c' i) xs₀ (nodup_of_node hn i) (hc i) (hcut' i)
    obtain ⟨G, hG⟩ := exists_glue hn F
    refine ⟨G, ?_, fun a ha => ?_⟩
    · obtain ⟨d₁, d₂⟩ := d
      simp only at hd
      subst hd
      rw [fl_node, subst_node]
      congr 1
      funext i
      rw [hF i]
      exact subst_congr _ fun a ha => (hG i a (by rwa [labels_allF] at ha)).symm
    · obtain ⟨i, hi⟩ := mem_labels_node.1 ha
      rw [hG i a hi]
      exact hF' i a hi

/-! ## The weight two -/

lemma weight_eq_zero_iff {t : STree E} : t.weight = 0 ↔ ∃ a, t = leaf a := by
  cases t with
  | leaf a => exact ⟨fun _ => ⟨a, rfl⟩, fun _ => rfl⟩
  | node e c =>
    simp only [weight_node, reduceCtorEq, exists_const, iff_false]
    omega

lemma wk_of_weight_one (xs : ℕ → STree E) {g : STree E} (hg : g.weight = 1) :
    wk xs g = {key (g.subst xs)} := by
  cases g with
  | leaf a => simp at hg
  | node f d =>
    rw [weight_node] at hg
    have h0 : ∀ l, (d l).weight = 0 := fun l => by
      have := Finset.single_le_sum (f := fun j => (d j).weight) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)
      simp only at this
      omega
    have hb : (Finset.univ.biUnion fun l => wk xs (d l)) = ∅ :=
      Finset.eq_empty_of_forall_notMem fun y hy => by
        obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.1 hy
        obtain ⟨a, ha⟩ := weight_eq_zero_iff.1 (h0 l)
        rw [ha, wk_leaf] at hl
        exact Finset.notMem_empty _ hl
    rw [wk_node, hb]
    rfl

/-- **An occurrence of a monomial with two vertices has one edge.** -/
theorem nwk_eq_singleton (xs : ℕ → STree E) {L : STree E} (hL : L.weight = 2) :
    ∃ y, nwk xs L = {y} := by
  cases L with
  | leaf a => simp at hL
  | @node k e c =>
    rw [weight_node] at hL
    have hsum : ∑ i, (c i).weight = 1 := by omega
    obtain ⟨i, hi⟩ : ∃ i, (c i).weight ≠ 0 := by
      by_contra h
      push Not at h
      rw [Finset.sum_eq_zero fun i _ => h i] at hsum
      exact absurd hsum (by norm_num)
    have hrest : ∑ j ∈ Finset.univ.erase i, (c j).weight = 1 - (c i).weight := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
      omega
    have hi1 : (c i).weight = 1 := by
      have := Finset.single_le_sum (f := fun j => (c j).weight) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
      simp only at this
      omega
    have hj : ∀ j, j ≠ i → (c j).weight = 0 := fun j hj => by
      rw [hi1, Nat.sub_self] at hrest
      exact (Finset.sum_eq_zero_iff.1 hrest) j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
    refine ⟨key ((c i).subst xs), ?_⟩
    rw [nwk_node]
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hy⟩
      by_cases hji : j = i
      · subst hji
        rwa [wk_of_weight_one xs hi1, Finset.mem_singleton] at hy
      · obtain ⟨a, ha⟩ := weight_eq_zero_iff.1 (hj j hji)
        rw [ha, wk_leaf] at hy
        exact absurd hy (Finset.notMem_empty _)
    · rintro rfl
      exact ⟨i, by rw [wk_of_weight_one xs hi1]; exact Finset.mem_singleton_self _⟩

/-! ## Counting edges -/

lemma card_vkeys : ∀ t : STree E, Multiset.card t.vkeys = t.weight
  | leaf _ => rfl
  | node e c => by
    rw [vkeys_node, Multiset.card_cons, Multiset.card_sum, weight_node, add_comm,
      Finset.sum_congr rfl fun i _ => card_vkeys (c i)]

/-- **A tree with distinct keys has one edge less than vertices.** -/
lemma card_edgeKeys {t : STree E} (hn : t.vkeys.Nodup) : t.edgeKeys.card = t.weight - 1 := by
  cases t with
  | leaf a => rfl
  | node e c =>
    rw [vkeys_node, Multiset.nodup_cons] at hn
    rw [edgeKeys_node, Multiset.card_toFinset, Multiset.dedup_eq_self.2 hn.2, Multiset.card_sum,
      weight_node]
    rw [Finset.sum_congr rfl fun i _ => card_vkeys (c i)]
    omega

lemma edgeKeys_subset_vkeys {t : STree E} {y : ℕ ×ₗ ℕ} (hy : y ∈ t.edgeKeys) : y ∈ t.vkeys := by
  cases t with
  | leaf a => exact absurd hy (Finset.notMem_empty _)
  | node e c =>
    rw [edgeKeys_node, Multiset.mem_toFinset] at hy
    exact Multiset.mem_cons_of_mem hy

lemma key_notMem_edgeKeys {t : STree E} (hn : t.vkeys.Nodup) : t.key ∉ t.edgeKeys := by
  cases t with
  | leaf a => exact Finset.notMem_empty _
  | node e c =>
    rw [vkeys_node, Multiset.nodup_cons] at hn
    rw [edgeKeys_node, Multiset.mem_toFinset]
    exact hn.1

/-- **The cut edges of a bar tree not flagged at the root are edges.** -/
lemma cutKeys_subset_edgeKeys {t : STree (BE E)} (h : rootF t = false) :
    cutKeys t ⊆ t.edgeKeys := by
  cases t with
  | leaf a => exact Finset.empty_subset _
  | node d c =>
    intro y hy
    rw [edgeKeys_node, Multiset.mem_toFinset]
    rcases mem_cutKeys_node.1 hy with ⟨hd, -⟩ | ⟨i, hi⟩
    · exact absurd hd (by simp only [rootF] at h; rw [h]; decide)
    · exact (Multiset.mem_sum (s := Finset.univ)).2 ⟨i, Finset.mem_univ _,
        mem_vkeys_of_mem_cutKeys hi⟩

lemma rootF_setF_false (x : ℕ ×ₗ ℕ) {t : STree (BE E)} (h : rootF t = false) :
    rootF (setF x false t) = false := by
  cases t with
  | leaf a => rfl
  | node d c =>
    rw [rootF_setF_node]
    split_ifs
    · rfl
    · exact h

lemma rootF_setF_of_ne {x : ℕ ×ₗ ℕ} (b : Bool) {t : STree (BE E)} (h : t.key ≠ x) :
    rootF (setF x b t) = rootF t := by
  cases t with
  | leaf a => rfl
  | node d c =>
    rw [rootF_setF_node, if_neg h]
    rfl

end STree

open STree

variable {E : ℕ → Type v} {K : Type*} [CommRing K] {ρ : Type*} {O : STree.AdmOrder E}
  (G : Rules K ρ O.toCtxOrder)

/-! ## Normality is local -/

/-- **The leading edges of a monomial**: the edges of the occurrences of leading monomials, the
edges whose window is a leading monomial when the rules are quadratic. -/
def Rules.leadKeys {A : Finset ℕ} (t : SMono E A) : Set (ℕ ×ₗ ℕ) :=
  {y | ∃ r p xs₀, t.1.get? p = some ((G.lead r).1.subst xs₀) ∧
    StrictMonoOn (fun a => (xs₀ a).first) (G.src r : Set ℕ) ∧ y ∈ nwk xs₀ (G.lead r).1}

/-- **A bar tree is normal** if and only if every occurrence of a leading monomial in its
underlying monomial has a cut edge. -/
theorem Rules.bar_normal_iff (hlead : ∀ r a, (G.lead r).1 ≠ leaf a) {A : Finset ℕ}
    (X : SMono (BE E) A) :
    G.bar.Normal X ↔ ∀ r p xs₀, (forget X.1).get? p = some ((G.lead r).1.subst xs₀) →
      StrictMonoOn (fun a => (xs₀ a).first) (G.src r : Set ℕ) →
        ∃ y ∈ nwk xs₀ (G.lead r).1, y ∈ cutKeys X.1 := by
  constructor
  · intro hN r p xs₀ hp hm
    by_contra hc
    push Not at hc
    rw [get?_forget] at hp
    obtain ⟨Y, hXY, hY⟩ := Option.map_eq_some_iff.1 hp
    rcases hL : (G.lead r).1 with a | ⟨e, c⟩
    · exact hlead r a hL
    have hn : (node e c).labels.Nodup := hL ▸ (G.lead r).nodup
    rw [hL] at hY hc
    obtain ⟨F, hF, hF'⟩ := lift_fl e c Y xs₀ hn hY
      fun y hy h => hc y hy (cutKeys_subset_of_get? hXY h)
    have hget : X.1.get? p = some ((G.bar.lead (r, rootF Y)).1.subst F) := by
      rw [hXY, hF]
      show some ((fl (rootF Y) (node e c)).subst F) = some ((fl (rootF Y) (G.lead r).1).subst F)
      rw [hL]
    have hmono : StrictMonoOn (fun a => (F a).first) (G.bar.src (r, rootF Y) : Set ℕ) :=
      fun a ha a' ha' h => by
        have hla : ∀ b ∈ G.src r, (F b).first = (xs₀ b).first := fun b hb => by
          rw [← first_forget, hF' b (by rw [← hL]; exact (G.lead r).mem_labels.2 hb)]
        simp only
        rw [hla a ha, hla a' ha']
        exact hm ha ha' h
    exact hN (r, rootF Y) _ (isSCtx_ctxOf X p _ F hget hmono) (ctxOf_self X p _ F hget hmono)
  · rintro H ⟨r, b⟩ f hf hfX
    obtain ⟨p, xs, hget, hin, -⟩ := IsSCtx.normal hf (G.bar.lead (r, b))
    rw [hfX] at hget
    have hget' : X.1.get? p = some ((fl b (G.lead r).1).subst xs) := hget
    have hp : (forget X.1).get? p = some ((G.lead r).1.subst fun a => forget (xs a)) := by
      rw [get?_forget, hget', Option.map_some, forget_subst, forget_fl]
    have hm : StrictMonoOn (fun a => (forget (xs a)).first) (G.src r : Set ℕ) :=
      fun a ha a' ha' h => by simpa only [first_forget] using hin.mono ha ha' h
    obtain ⟨y, hy, hyX⟩ := H r p _ hp hm
    rcases hL : (G.lead r).1 with a | ⟨e, c⟩
    · exact hlead r a hL
    rw [hL] at hget' hy
    rw [nwk_node, Finset.mem_biUnion] at hy
    obtain ⟨i, -, hy⟩ := hy
    have hnX : X.1.vkeys.Nodup := nodup_vkeys X.isShuffle X.nodup
    have hnW := Multiset.nodup_of_le (mem_vkeys_of_get? hget') hnX
    rw [fl_node, subst_node] at hget' hnW
    obtain ⟨hroot, hnc, hdisj⟩ := nodup_vkeys_children hnW
    obtain ⟨h1, h2⟩ := wk_props (c i) xs (hnc i) y hy
    have hyW := mem_cutKeys_of_get? hnX hget' hyX
      (mem_vkeys_node.2 (Or.inr ⟨i, h1⟩))
    rcases mem_cutKeys_node.1 hyW with ⟨-, rfl⟩ | ⟨j, hj⟩
    · exact hroot ((Multiset.mem_sum (s := Finset.univ)).2 ⟨i, Finset.mem_univ _, h1⟩)
    · by_cases hij : j = i
      · subst hij
        exact h2 hj
      · exact Multiset.disjoint_left.1 (hdisj j i hij) (mem_vkeys_of_mem_cutKeys hj) h1

/-- **Normality is local**, for quadratic rules: a bar tree is normal if and only if its leading
edges are cut. -/
theorem Rules.bar_normal_iff_quad (hquad : ∀ r, (G.lead r).1.weight = 2) {A : Finset ℕ}
    (X : SMono (BE E) A) : G.bar.Normal X ↔ G.leadKeys (forgetM X) ⊆ ↑(cuts X) := by
  have hlead : ∀ r a, (G.lead r).1 ≠ leaf a := fun r a h => by
    have := hquad r
    rw [h, weight_leaf] at this
    exact absurd this (by norm_num)
  rw [G.bar_normal_iff hlead]
  constructor
  · rintro H y ⟨r, p, xs₀, hp, hm, hy⟩
    obtain ⟨y', hy'⟩ := nwk_eq_singleton xs₀ (hquad r)
    obtain ⟨z, hz, hzX⟩ := H r p xs₀ hp hm
    rw [hy', Finset.mem_singleton] at hy hz
    rw [hy, ← hz]
    exact hzX
  · intro H r p xs₀ hp hm
    obtain ⟨y, hy⟩ := nwk_eq_singleton xs₀ (hquad r)
    exact ⟨y, by rw [hy]; exact Finset.mem_singleton_self y,
      H ⟨r, p, xs₀, hp, hm, by rw [hy]; exact Finset.mem_singleton_self y⟩⟩

/-! ## Koszulness -/

namespace STree.Bar

variable (K)

/-- **The bar construction of the free shuffle operad** on the leaves `A`, with `w` vertices,
in degree `s`: the combinations of bar trees with `s` components (`s - 1` cut edges). -/
def C (A : Finset ℕ) (w s : ℕ) : Submodule K (SMono (BE E) A →₀ K) :=
  Finsupp.supported K K {X | rootF X.1 = false ∧ X.1.weight = w ∧ (cuts X).card + 1 = s}

end STree.Bar

/-- **Koszulness** of the shuffle operad presented by the rules: in every arity and weight, the
homology of its bar construction — the bar construction of the free shuffle operad modulo the
ideal of the flagged rules — vanishes below the diagonal: every cycle with fewer components than
vertices is a boundary. -/
def Rules.IsKoszul : Prop :=
  ∀ (A : Finset ℕ) (w s : ℕ), s < w → ∀ v ∈ Bar.C K A w s, Bar.d K v ∈ (G.bar.rw A).ideal →
    ∃ u ∈ Bar.C K A w (s + 1), v - Bar.d K u ∈ (G.bar.rw A).ideal

section Normal

variable {G} (hquad : ∀ r, (G.lead r).1.weight = 2)
include hquad

/-- **Merging along a cut edge of a normal bar tree** gives a normal bar tree exactly when the
edge is not leading. -/
theorem Rules.bar_normal_setM_false {A : Finset ℕ} {X : SMono (BE E) A} (hX : G.bar.Normal X)
    {k : ℕ ×ₗ ℕ} :
    G.bar.Normal (setM k false X) ↔ k ∉ G.leadKeys (forgetM X) := by
  rw [G.bar_normal_iff_quad hquad, forgetM_setM]
  have hX' := (G.bar_normal_iff_quad hquad X).1 hX
  have hc : cuts (setM k false X) = (cuts X).erase k := cutKeys_setF_false k X.1
  rw [hc, Finset.coe_erase]
  constructor
  · intro h hk
    exact (h hk).2 rfl
  · intro hk y hy
    refine ⟨hX' hy, fun h => hk ?_⟩
    rw [Set.mem_singleton_iff] at h
    rw [← h]
    exact hy

/-- **Cutting along an edge of a normal bar tree** gives a normal bar tree. -/
theorem Rules.bar_normal_setM_true {A : Finset ℕ} {X : SMono (BE E) A} (hX : G.bar.Normal X)
    (k : ℕ ×ₗ ℕ) : G.bar.Normal (setM k true X) := by
  rw [G.bar_normal_iff_quad hquad, forgetM_setM]
  have hX' := (G.bar_normal_iff_quad hquad X).1 hX
  intro y hy
  show y ∈ cutKeys (setF k true X.1)
  rw [mem_cutKeys_setF_true]
  exact Or.inr (hX' hy)

end Normal

/-- Two linear maps which agree on the basis elements of a set agree on their combinations. -/
lemma eq_of_supported {X M : Type*} [AddCommGroup M] [Module K M]
    {f g : (X →₀ K) →ₗ[K] M} {s : Set X}
    (h : ∀ x ∈ s, f (Finsupp.single x 1) = g (Finsupp.single x 1))
    {v : X →₀ K} (hv : v ∈ Finsupp.supported K K s) : f v = g v := by
  have := Hoffbeck.map_mem_of_supported (P := LinearMap.eqLocus f g) LinearMap.id
    (fun x hx => LinearMap.mem_eqLocus.2 (h x hx)) hv
  exact LinearMap.mem_eqLocus.1 this

/-- **PBW implies Koszul** (Hoffbeck; Dotsenko–Khoroshkin): a shuffle operad presented by
quadratic rules which are resolvable — whose normal monomials are a basis of the operad, a PBW
basis, by the Buchberger criterion when the critical ambiguities are resolvable — is Koszul. -/
theorem Rules.isKoszul_of_resolvable (hquad : ∀ r, (G.lead r).1.weight = 2)
    (hom : ∀ r, ∀ m ∈ (G.tail r).support, m.1.weight = 2)
    (hres : ∀ C, (G.rw C).Resolvable) : G.IsKoszul := by
  classical
  have hlead : ∀ r a, (G.lead r).1 ≠ leaf a := fun r a h => by
    have := hquad r
    rw [h, weight_leaf] at this
    exact absurd this (by norm_num)
  have hom' : ∀ r, ∀ m ∈ (G.tail r).support, m.1.weight = (G.lead r).1.weight :=
    fun r m hm => by rw [hom r m hm, hquad r]
  intro A w s hsw v hv hdv
  set S := G.bar.rw A with hSdef
  have hS : S.Resolvable := G.bar_resolvable hlead hom' hres A
  have hirr : ∀ X, X ∈ S.Irr ↔ G.bar.Normal X := fun X => G.bar.mem_irr_iff
  -- the bar trees of a degree: a set closed under reduction
  let P : ℕ → Set (SMono (BE E) A) := fun n =>
    {X | rootF X.1 = false ∧ X.1.weight = w ∧ (cuts X).card + 1 = n}
  have hPcl : ∀ n, ∀ X ∈ P n, ∀ u ∈ S.red X, u ∈ Finsupp.supported K K (P n) := by
    intro n X hX u hu
    refine Finsupp.supported_mono (fun Y hY => ?_) (G.bar_red_inv hlead hom' hu)
    obtain ⟨h1, h2, h3⟩ := hY
    refine ⟨?_, ?_, ?_⟩
    · rw [h2]
      exact hX.1
    · rw [h3]
      exact hX.2.1
    · rw [h1]
      exact hX.2.2
  have hnfP : ∀ n, ∀ u ∈ Finsupp.supported K K (P n),
      S.nf u ∈ Finsupp.supported K K (S.Irr ∩ P n) := by
    intro n u hu
    rw [Finsupp.supported_inter]
    exact ⟨S.nf_mem_supported u, S.nf_mem_of_closed (hPcl n) hu⟩
  -- the differential lowers the degree
  have hdP : ∀ n, ∀ X ∈ P (n + 1), Bar.d K (Finsupp.single X 1) ∈ Finsupp.supported K K (P n) := by
    intro n X hX
    rw [Bar.d, CutComplex.d_single, one_smul, CutComplex.dX]
    refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _
      (Finsupp.single_mem_supported K _ ⟨rootF_setF_false k hX.1, ?_, ?_⟩)
    · rw [setM_val, weight_setF]
      exact hX.2.1
    · have hc : cuts (setM k false X) = (cuts X).erase k := cutKeys_setF_false k X.1
      have h2 := hX.2.2
      have hpos := Finset.card_pos.2 ⟨k, hk⟩
      rw [hc, Finset.card_erase_of_mem hk]
      omega
  -- the normal form commutes with the differential modulo the ideal
  have hnfd : ∀ u, S.nf (Bar.d K (S.nf u)) = S.nf (Bar.d K u) := fun u => by
    have h := hS.ideal_le_ker (G.bar_d_mem_ideal hlead hom' (S.nf_sub_mem u))
    rw [LinearMap.mem_ker, map_sub, map_sub, sub_eq_zero] at h
    exact h
  let V := S.Irr ∩ P s
  let V' := S.Irr ∩ P (s + 1)
  let D : (SMono (BE E) A →₀ K) →ₗ[K] (SMono (BE E) A →₀ K) := S.nf ∘ₗ Bar.d K
  let D₀ : (SMono (BE E) A →₀ K) →ₗ[K] (SMono (BE E) A →₀ K) :=
    CutComplex.dL cuts (fun x => setM x false) forgetM G.leadKeys
  have hD : ∀ X ∈ V', D (Finsupp.single X 1) ∈ Finsupp.supported K K V := fun X hX =>
    hnfP s _ (hdP s X hX.2)
  have hDD : ∀ u ∈ Finsupp.supported K K V', D (D u) = 0 := fun u _ => by
    show S.nf (Bar.d K (S.nf (Bar.d K u))) = 0
    rw [hnfd, Bar.d_d, map_zero]
  have hlead' : ∀ X ∈ V ∪ V', D (Finsupp.single X 1) - D₀ (Finsupp.single X 1) ∈
      Finsupp.supported K K {Y | O.lt (forgetM Y) (forgetM X)} := by
    intro X hX
    have hXn : G.bar.Normal X := (hirr X).1 (by rcases hX with h | h <;> exact h.1)
    show S.nf (Bar.d K (Finsupp.single X 1)) - CutComplex.dL cuts (fun x => setM x false) forgetM
      G.leadKeys (Finsupp.single X 1) ∈ _
    rw [Bar.d, CutComplex.d_single, CutComplex.dL_single, one_smul, one_smul, CutComplex.dX,
      CutComplex.dLX, map_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : k ∈ G.leadKeys (forgetM X)
    · rw [if_neg (not_not.2 hk), sub_zero, map_smul]
      refine Submodule.smul_mem _ _ ?_
      have hne : (S.red (setM k false X)).Nonempty := by
        by_contra hne
        exact ((G.bar_normal_setM_false hquad hXn).1 ((hirr _).1 (S.mem_irr_iff.2 hne))) hk
      rw [Rewriting.nf_single, one_smul]
      refine Finsupp.supported_mono (fun Y hY => ?_) (S.nfMono_mem_below hne)
      show O.lt (forgetM Y) (forgetM X)
      have : O.bar.lt Y (setM k false X) := hY
      rw [← forgetM_setM k false X]
      exact this
    · rw [if_pos hk, map_smul, S.nf_single_of_irr ((hirr _).2
        ((G.bar_normal_setM_false hquad hXn).2 hk)), sub_self]
      exact Submodule.zero_mem _
  have hfib : ∀ X ∈ V, D₀ (Finsupp.single X 1) ∈
      Finsupp.supported K K {Y | forgetM Y = forgetM X} := by
    intro X _
    show CutComplex.dL cuts (fun x => setM x false) forgetM G.leadKeys (Finsupp.single X 1) ∈ _
    rw [CutComplex.dL_single, one_smul, CutComplex.dLX]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Finsupp.single_mem_supported K _ (forgetM_setM k false X))
  have hexact : ∀ t, ∀ u ∈ Finsupp.supported K K (V ∩ forgetM ⁻¹' {t}), D₀ u = 0 →
      ∃ u' ∈ Finsupp.supported K K (V' ∩ forgetM ⁻¹' {t}), D₀ u' = u := by
    intro t u hu hDu
    by_cases hu0 : u = 0
    · exact ⟨0, Submodule.zero_mem _, by rw [hu0, map_zero]⟩
    obtain ⟨X, hX⟩ := Finsupp.support_nonempty_iff.2 hu0
    obtain ⟨⟨hXirr, hXr, hXw, hXc⟩, hXt⟩ := (Finsupp.mem_supported K u).1 hu hX
    have hXt' : forgetM X = t := hXt
    have hnX := nodup_vkeys X.isShuffle X.nodup
    have hcard : (cuts X).card < X.1.edgeKeys.card := by
      rw [card_edgeKeys hnX, hXw]
      omega
    obtain ⟨k₀, hk₀e, hk₀c⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hk₀L : k₀ ∉ G.leadKeys t := fun h => hk₀c
      ((G.bar_normal_iff_quad hquad X).1 ((hirr X).1 hXirr) (hXt' ▸ h))
    have hedge : ∀ Y : SMono (BE E) A, forgetM Y = t → k₀ ∈ Y.1.edgeKeys := fun Y hY => by
      rw [← edgeKeys_forget, ← forgetM_val, hY, ← hXt', forgetM_val, edgeKeys_forget]
      exact hk₀e
    let H₀ : (SMono (BE E) A →₀ K) →ₗ[K] (SMono (BE E) A →₀ K) :=
      CutComplex.hL cuts (fun x => setM x true) k₀
    have hhom : ∀ Y ∈ V ∩ forgetM ⁻¹' {t},
        (D₀ ∘ₗ H₀ + H₀ ∘ₗ D₀) (Finsupp.single Y (1 : K)) =
          LinearMap.id (R := K) (Finsupp.single Y (1 : K)) := by
      intro Y hY
      have hYt : forgetM Y = t := hY.2
      exact CutComplex.dL_hL_add (t := t) hk₀L (fun x => forgetM_setM k₀ true x)
        (fun x _ k _ => cutKeys_setF_false k x.1)
        (fun x hx _ => cutKeys_setF_true (edgeKeys_subset_vkeys (hedge x hx)))
        (fun x _ h => Subtype.ext (by
          rw [setM_val, setM_val, setF_setF_self, setF_false_of_notMem h]))
        (fun x _ h => Subtype.ext (by
          rw [setM_val, setM_val, setF_setF_self,
            setF_true_of_mem (nodup_vkeys x.isShuffle x.nodup) h]))
        (fun x _ h k hk => Subtype.ext (setF_comm (fun e => h (by rw [← e]; exact hk))
          false true x.1)) hYt
    refine ⟨H₀ u, Hoffbeck.map_mem_of_supported H₀ (fun Y hY => ?_) hu, ?_⟩
    · show CutComplex.hL cuts (fun x => setM x true) k₀ (Finsupp.single Y 1) ∈ _
      rw [CutComplex.hL_single, one_smul, CutComplex.hX]
      split_ifs with h
      · exact Submodule.zero_mem _
      · obtain ⟨⟨hYirr, hYr, hYw, hYc⟩, hYt⟩ := hY
        have hYt' : forgetM Y = t := hYt
        refine Submodule.smul_mem _ _ (Finsupp.single_mem_supported K _ ⟨⟨(hirr _).2
          (G.bar_normal_setM_true hquad ((hirr Y).1 hYirr) k₀), ?_, ?_, ?_⟩, ?_⟩)
        · rw [setM_val, rootF_setF_of_ne true]
          · exact hYr
          · intro he
            exact key_notMem_edgeKeys (nodup_vkeys Y.isShuffle Y.nodup) (he ▸ hedge Y hYt')
        · rw [setM_val, weight_setF]
          exact hYw
        · have hc : cuts (setM k₀ true Y) = insert k₀ (cuts Y) :=
            cutKeys_setF_true (edgeKeys_subset_vkeys (hedge Y hYt'))
          rw [hc, Finset.card_insert_of_notMem h, hYc]
        · show forgetM (setM k₀ true Y) = t
          rw [forgetM_setM, hYt']
    · have h := eq_of_supported hhom hu
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hDu, map_zero,
        add_zero, LinearMap.id_apply] at h
      exact h
  have hv₀ : S.nf v ∈ Finsupp.supported K K V := hnfP s v hv
  have hDv₀ : D (S.nf v) = 0 := by
    show S.nf (Bar.d K (S.nf v)) = 0
    rw [hnfd]
    exact hS.ideal_le_ker hdv
  obtain ⟨u, hu, hDu⟩ := Hoffbeck.exact_of_leading (fun x y => O.lt x y) forgetM (O.wf A)
    O.trans D D₀ hD hDD hlead' hfib hexact (S.nf v) hv₀ hDv₀
  refine ⟨u, Finsupp.supported_mono Set.inter_subset_right hu, ?_⟩
  have hDu' : S.nf (Bar.d K u) = S.nf v := hDu
  have e : v - Bar.d K u = (v - S.nf v) + (S.nf (Bar.d K u) - Bar.d K u) := by
    rw [hDu', sub_add_sub_cancel]
  rw [e]
  refine Submodule.add_mem _ ?_ (S.nf_sub_mem _)
  rw [← neg_sub]
  exact Submodule.neg_mem _ (S.nf_sub_mem v)

/-- **A quadratic Gröbner basis presents a Koszul operad** (Dotsenko–Khoroshkin, for generators
of any arity): if the critical ambiguities of quadratic rules are resolvable, the shuffle operad
they present is Koszul. -/
theorem Rules.isKoszul_of_critical (hquad : ∀ r, (G.lead r).1.weight = 2)
    (hom : ∀ r, ∀ m ∈ (G.tail r).support, m.1.weight = 2)
    (hcrit : ∀ {C : Finset ℕ} {r₁ r₂ : ρ} (B : G.Amb C r₁ r₂), Critical G B → B.Res) :
    G.IsKoszul := by
  have hlead : ∀ r a, (G.lead r).1 ≠ leaf a := fun r a h => by
    have := hquad r
    rw [h, weight_leaf] at this
    exact absurd this (by norm_num)
  exact G.isKoszul_of_resolvable hquad hom (STree.resolvable_of_critical G hlead hcrit)

end Operad
