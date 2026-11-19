/-
# The sign rule of merging an edge, for generators of any arity

Step (2b) of the symmetric–shuffle bridge for generators of any arity, third part; the binary
case is `Operad.ShuffleBarSymSign`, whose lemmas on inversions of lists are used as they are.
Setting and notation as in `Operad.ShuffleAnySym`.

* **The cut edges in preorder**: the cut edges of `toBar t` are named by the keys of the vertices
  of `t` other than the root (`ShuffleAnySym.cutKeys_toBar`), which are distinct
  (`ShuffleAnySym.nodup_tail_wKeys`), so the sign of merging the cut edge `κ` is `(-1)` to the
  number of those keys smaller than `κ` (`ShuffleAnySym.sgn_toBar`).
* **Merging an edge** (`ShuffleAnySym.mergeT`): the vertex of key `κ` is merged into its parent,
  the children of the two vertices sorted by their least leaves, the merged monomial
  (`ShuffleAnySym.mergedMono`, a monomial by `ShuffleAnySym.mergedMono_mem`) having its leaves
  named by their ranks. The merged tree is a shuffle tree with the same leaves whose bar tree is
  `setF κ false (toBar t)` (`ShuffleAnySym.mergeT_spec`, by `ShuffleAnySym.toBar_rootMerge`).
* **The sign rule** (`ShuffleAnySym.wsign_mergeT`): `wsign t · (-1)^p · kzAt t κ ·
  wsign (mergeT t κ)` is the sign of merging `κ` in the bar tree, `p` the position of `κ` in
  preorder and `kzAt` the Koszul sign of sorting the children of the merged vertex
  (`ShuffleAnySym.wKeys_mergeT`).
* **The differential identity from the expansion over the edges**
  (`ShuffleAnySym.ΦL_d_of_expansion`): if `Bar.d` of every basis vector is the signed sum of its
  merged trees (`ShuffleAnySym.DExpansion`), then `ΦL ∘ Bar.d = STree.Bar.d ∘ ΦL`. The expansion
  holds on the trees with one or two vertices (`ShuffleAnySym.dExpansion_of_weight`).
-/
import Operad.ShuffleAnySymDiff
import Operad.ShuffleBarSymSign

universe u

namespace Operad

open Function Sym GerBV GrComposite STree FreeGr Bar

namespace ShuffleAnySym

open ShuffleBarSym

/-! ## The cut edges of a bar tree in preorder -/

section CutKeys

open STree

variable {T : ℕ → Type}

lemma weight_toBar_child {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T)) (j : Fin k) :
    (toBar (ch j)).weight < (toBar (STree.node m ch)).weight := by
  obtain ⟨l, e, c, h⟩ := m.exists_node
  have h1 : 0 < m.1.1.weight := by
    rw [h]
    simp [STree.weight]
  have h2 : (kids ch j).weight ≤ ((fl false m.1.1).labels.map fun a => (kids ch a).weight).sum :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _
      (Multiset.mem_map_of_mem _ (by rw [labels_fl]; exact m.mem j.2))
  rw [kids_fin, weight_cutRoot] at h2
  rw [toBar_node, weight_subst, weight_fl]
  omega

lemma wKeys_node {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T)) :
    wKeys (STree.node m ch)
      = wkey (STree.node m ch) :: (List.ofFn fun j => wKeys (ch j)).flatten := rfl

lemma wkey_mem_wKeys {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T)) :
    wkey (STree.node m ch) ∈ wKeys (STree.node m ch) := by
  simp [wKeys]

lemma wKeys_eq_cons {t : STree (VMono T)} (hw : t.weight ≠ 0) :
    wKeys t = wkey t :: (wKeys t).tail := by
  cases t with
  | leaf => simp [STree.weight] at hw
  | node β ch => rfl

lemma weight_ne_zero_of_mem {t : STree (VMono T)} {κ : ℕ ×ₗ ℕ} (h : κ ∈ wKeys t) :
    t.weight ≠ 0 := by
  cases t with
  | leaf => simp [wKeys] at h
  | node β ch => simp [STree.weight]

/-- **A key of a vertex** names a leaf of the tree and counts at most the generators of the tree. -/
lemma mem_wKeys : ∀ {t : STree (VMono T)} {κ : ℕ ×ₗ ℕ}, t.IsShuffle → κ ∈ wKeys t →
    (ofLex κ).1 ∈ t.labels ∧ (ofLex κ).2 ≤ (toBar t).weight
  | STree.leaf _, _, _, h => by simp [wKeys] at h
  | STree.node m ch, κ, ht, h => by
    simp only [wKeys, List.mem_cons, List.mem_flatten, List.mem_ofFn] at h
    rcases h with rfl | ⟨_, ⟨j, rfl⟩, hj⟩
    · refine ⟨?_, le_rfl⟩
      show (toBar (STree.node m ch)).first ∈ _
      rw [first_toBar _ ht]
      exact first_mem ht
    · have := mem_wKeys (ht.child j) hj
      exact ⟨Multiset.mem_of_le (labels_le_node _ _ j) this.1,
        this.2.trans (weight_toBar_child m ch j).le⟩

lemma cutKeys_cutRoot_toBar_node {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T)) :
    cutKeys (cutRoot (toBar (STree.node m ch)))
      = insert (wkey (STree.node m ch)) (cutKeys (toBar (STree.node m ch))) := by
  obtain ⟨l, e, c, hT⟩ := toBar_node_eq m ch
  rw [wkey, hT, cutKeys_cutRoot_node]
  congr 1
  ext y
  rw [mem_cutKeys_node, Finset.mem_biUnion]
  simp

lemma cutKeys_toBar_node_of {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T))
    (ih : ∀ j, cutKeys (cutRoot (toBar (ch j))) = (wKeys (ch j)).toFinset) :
    cutKeys (toBar (STree.node m ch)) = (List.ofFn fun j => wKeys (ch j)).flatten.toFinset := by
  rw [cutKeys_toBar_node]
  ext κ
  simp only [Finset.mem_biUnion, Finset.mem_range, List.mem_toFinset, List.mem_flatten,
    List.mem_ofFn]
  constructor
  · rintro ⟨a, ha, hκ⟩
    rw [kids_of_lt ch ha, ih, List.mem_toFinset] at hκ
    exact ⟨_, ⟨⟨a, ha⟩, rfl⟩, hκ⟩
  · rintro ⟨_, ⟨j, rfl⟩, hκ⟩
    refine ⟨j, j.2, ?_⟩
    rw [kids_fin, ih, List.mem_toFinset]
    exact hκ

/-- **The cut edges of the bar tree with the edge above the root cut** are named by the keys of
all the vertices of the shuffle tree. -/
theorem cutKeys_cutRoot_toBar : ∀ t : STree (VMono T),
    cutKeys (cutRoot (toBar t)) = (wKeys t).toFinset
  | STree.leaf _ => rfl
  | STree.node m ch => by
    rw [cutKeys_cutRoot_toBar_node,
      cutKeys_toBar_node_of m ch fun j => cutKeys_cutRoot_toBar (ch j), wKeys,
      List.toFinset_cons]

/-- **The cut edges of a bar tree are named by the keys of the vertices other than the root**, in
the preorder of the shuffle tree. -/
theorem cutKeys_toBar (t : STree (VMono T)) : cutKeys (toBar t) = (wKeys t).tail.toFinset := by
  cases t with
  | leaf => rfl
  | node m ch =>
    rw [cutKeys_toBar_node_of m ch fun j => cutKeys_cutRoot_toBar (ch j), wKeys, List.tail_cons]

/-- **The keys of the vertices other than the root are distinct.** -/
theorem nodup_tail_wKeys {t : STree (VMono T)} (ht : t.IsShuffle) (hnd : t.labels.Nodup) :
    (wKeys t).tail.Nodup := by
  cases t with
  | leaf => exact List.nodup_nil
  | node m ch =>
    have hc := card_cutKeys_toBar m ch ht hnd
    have hl := length_wKeys (STree.node m ch)
    rw [cutKeys_toBar] at hc
    have hlen : (wKeys (STree.node m ch)).tail.toFinset.card
        = (wKeys (STree.node m ch)).tail.length := by
      rw [List.length_tail]
      omega
    have := (Multiset.toFinset_card_eq_card_iff_nodup
      (m := ((wKeys (STree.node m ch)).tail : Multiset (ℕ ×ₗ ℕ)))).1 hlen
    exact Multiset.coe_nodup.1 this

variable (K : Type u) [CommRing K]

/-- **The sign of merging a cut edge of a bar tree** is `(-1)` to the number of vertices of the
shuffle tree other than the root with smaller key. -/
theorem sgn_toBar {t : STree (VMono T)} (ht : t.IsShuffle) (hnd : t.labels.Nodup)
    (κ : ℕ ×ₗ ℕ) :
    CutComplex.sgn K (cutKeys (toBar t)) κ = (-1) ^ (wKeys t).tail.countP (· < κ) := by
  unfold CutComplex.sgn
  have hf : ((wKeys t).tail.toFinset.filter (· < κ))
      = ((wKeys t).tail.filter (· < κ)).toFinset := by
    ext x
    simp
  rw [cutKeys_toBar, hf, List.toFinset_card_of_nodup ((nodup_tail_wKeys ht hnd).filter _),
    ← List.countP_eq_length_filter]

end CutKeys

/-! ## Merging an edge of a shuffle tree of monomials -/

section Merge

open STree

variable {T : ℕ → Type}

/-- **The merged monomial**: the monomial `m₂` grafted on the leaf `j` of `m₁`, its leaves named
by the ranks of the children of the merged vertex in the order `π`. -/
noncomputable def mergedMono {k l N : ℕ} (m₁ : STree T) (j : Fin k) (m₂ : STree T)
    (hN : N + 1 = k + l) (π : Equiv.Perm (Fin N)) : STree T :=
  mergeMono m₁ j m₂ (rk₁ j hN π) (rk₂ j hN π)

lemma VMono.two_le {k : ℕ} (m : VMono T k) : 2 ≤ k := m.2

/-- **The merged monomial is a monomial** of the merged arity, when the children are sorted. -/
theorem mergedMono_mem {k l N : ℕ} (m₁ : VMono T k) (ch : Fin k → STree (VMono T)) (j : Fin k)
    (m₂ : VMono T l) (c₂ : Fin l → STree (VMono T)) (hj : ch j = STree.node m₂ c₂)
    (ht : (STree.node m₁ ch).IsShuffle) (hN : N + 1 = k + l) :
    ((mergedMono m₁.1.1 j m₂.1.1 hN (sortP (planar ch j c₂ hN))).IsShuffle ∧
      (mergedMono m₁.1.1 j m₂.1.1 hN (sortP (planar ch j c₂ hN))).labels
        = (Finset.range N).val) ∧ 2 ≤ N := by
  set Q := planar ch j c₂ hN with hQ
  set π := sortP Q with hπ
  have hk := m₁.two_le
  have hl := m₂.two_le
  have ht₂ : (STree.node m₂ c₂).IsShuffle := hj ▸ ht.child j
  have hF₁ : ∀ a : Without (Fin k) j, (Q (posEquivF j l N hN (Sum.inl a))).first
      = (ch a.1).first := fun a => by rw [hQ, planar_inl]
  have hF₂ : ∀ i : Fin l, (Q (posEquivF j l N hN (Sum.inr i))).first = (c₂ i).first :=
    fun i => by rw [hQ, planar_inr]
  have hl0 : 0 < l := by omega
  have hc0 : (c₂ ⟨0, hl0⟩).first = (ch j).first := by rw [hj, first_node _ _ hl0]
  -- the ranks of the children of the child are increasing
  have hs₂ : StrictMonoOn (fun i => (STree.leaf (rk₂ j hN π i) : STree T).first)
      {a | a ∈ m₂.1.1.labels} := by
    intro a ha b hb hab
    have ha' := m₂.lt ha
    have hb' := m₂.lt hb
    show rk₂ j hN π a < rk₂ j hN π b
    rw [rk₂, dif_pos ha', rk₂, dif_pos hb']
    refine sortP_symm_lt Q ?_
    rw [hF₂, hF₂]
    exact ht₂.mono (show (⟨a, ha'⟩ : Fin l) < ⟨b, hb'⟩ from hab)
  -- the least ranks above the leaves of the vertex
  let ins : ℕ → STree T := fun a =>
    if a = (j : ℕ) then m₂.1.1.subst (fun i => STree.leaf (rk₂ j hN π i))
    else STree.leaf (rk₁ j hN π a)
  have hmin : ∀ a : Fin k, (ins a).first = π.symm (if h : a = j then
      posEquivF j l N hN (Sum.inr ⟨0, hl0⟩) else posEquivF j l N hN (Sum.inl ⟨a, h⟩)) := by
    intro a
    by_cases h : a = j
    · subst h
      rw [dif_pos rfl]
      simp only [ins, if_true]
      rw [first_subst m₂.isShuffle, m₂.first]
      show rk₂ a hN π 0 = _
      rw [rk₂, dif_pos hl0]
    · simp only [ins, if_neg (fun h' => h (Fin.ext h')), dif_neg h]
      show rk₁ j hN π a = _
      rw [rk₁, dif_pos a.2, dif_neg (by simpa using h)]
  have hfirst : ∀ a : Fin k, (Q (if h : a = j then posEquivF j l N hN (Sum.inr ⟨0, hl0⟩)
      else posEquivF j l N hN (Sum.inl ⟨a, h⟩))).first = (ch a).first := by
    intro a
    by_cases h : a = j
    · subst h
      rw [dif_pos rfl, hF₂, hc0]
    · rw [dif_neg h, hF₁]
  have hstrict : StrictMonoOn (fun a => (ins a).first) {a | a ∈ m₁.1.1.labels} := by
    intro a ha b hb hab
    have ha' := m₁.lt ha
    have hb' := m₁.lt hb
    show (ins (⟨a, ha'⟩ : Fin k)).first < (ins (⟨b, hb'⟩ : Fin k)).first
    rw [hmin, hmin]
    refine sortP_symm_lt Q ?_
    rw [hfirst, hfirst]
    exact ht.mono (show (⟨a, ha'⟩ : Fin k) < ⟨b, hb'⟩ from hab)
  have hshuf : (mergedMono m₁.1.1 j m₂.1.1 hN π).IsShuffle := by
    refine isShuffle_subst m₁.isShuffle (fun a _ => ?_) hstrict
    show (ins a).IsShuffle
    simp only [ins]
    split_ifs
    · exact isShuffle_subst m₂.isShuffle (fun _ _ => trivial) hs₂
    · trivial
  -- the leaves are the ranks
  have hlabs : (mergedMono m₁.1.1 j m₂.1.1 hN π).labels = Multiset.range N := by
    have e1 : (mergedMono m₁.1.1 j m₂.1.1 hN π).labels = ∑ a : Fin k, (ins a).labels := by
      rw [mergedMono, mergeMono, labels_subst, bind_kids m₁]
    have e2 : (ins j).labels = ∑ i : Fin l, {rk₂ j hN π i} := by
      simp only [ins, if_true]
      rw [labels_subst, bind_kids m₂]
      rfl
    have e3 : ∀ a : Without (Fin k) j, (ins a.1).labels = {rk₁ j hN π a.1} := by
      intro a
      simp only [ins, if_neg (fun h' => a.2 (Fin.ext h'))]
      rfl
    have e4 : Multiset.range N = ∑ r : Fin N, {(r : ℕ)} := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ({i} : Multiset ℕ)) N, Finset.sum_eq_multiset_sum,
        Multiset.sum_map_singleton]
      rfl
    rw [e1, Fintype.sum_eq_add_sum_subtype_ne _ j, e2, e4,
      ← Equiv.sum_comp ((posEquivF j l N hN).trans π.symm), Fintype.sum_sum_type,
      add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [e3, rk₁_of]
      rfl
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [rk₂_of]
      rfl
  exact ⟨⟨hshuf, hlabs.trans (Finset.range_val N).symm⟩, by omega⟩

end Merge

/-! ## Merging the edge above a child of the root -/

section RootMerge

open STree

variable {T : ℕ → Type}

lemma mergeN_eq {k : ℕ} (m₁ : VMono T k) (l : ℕ) : k + l - 1 + 1 = k + l := by
  have := m₁.two_le
  omega

/-- **Merging the edge above the child `j` of the root**, for `ch j = node m₂ c₂`: the vertex of
the merged monomial, with the children of the two vertices sorted by their least leaves. -/
noncomputable def rootMerge {k l : ℕ} (m₁ : VMono T k) (ch : Fin k → STree (VMono T)) (j : Fin k)
    (m₂ : VMono T l) (c₂ : Fin l → STree (VMono T)) : STree (VMono T) :=
  @dite _ (((mergedMono m₁.1.1 j m₂.1.1 (mergeN_eq m₁ l)
      (sortP (planar ch j c₂ (mergeN_eq m₁ l)))).IsShuffle ∧
    (mergedMono m₁.1.1 j m₂.1.1 (mergeN_eq m₁ l)
      (sortP (planar ch j c₂ (mergeN_eq m₁ l)))).labels = (Finset.range (k + l - 1)).val) ∧
      2 ≤ k + l - 1) (Classical.propDecidable _)
    (fun h => STree.node (⟨⟨_, h.1⟩, h.2⟩ : VMono T (k + l - 1))
      (planar ch j c₂ (mergeN_eq m₁ l) ∘ sortP (planar ch j c₂ (mergeN_eq m₁ l))))
    fun _ => STree.node m₁ ch

variable {k l : ℕ} {m₁ : VMono T k} {ch : Fin k → STree (VMono T)} {j : Fin k} {m₂ : VMono T l}
  {c₂ : Fin l → STree (VMono T)}

lemma rootMerge_eq (hj : ch j = STree.node m₂ c₂) (ht : (STree.node m₁ ch).IsShuffle) :
    rootMerge m₁ ch j m₂ c₂ = STree.node
      (⟨⟨_, (mergedMono_mem m₁ ch j m₂ c₂ hj ht (mergeN_eq m₁ l)).1⟩,
        (mergedMono_mem m₁ ch j m₂ c₂ hj ht (mergeN_eq m₁ l)).2⟩ : VMono T (k + l - 1))
      (planar ch j c₂ (mergeN_eq m₁ l) ∘ sortP (planar ch j c₂ (mergeN_eq m₁ l))) :=
  dif_pos (mergedMono_mem m₁ ch j m₂ c₂ hj ht (mergeN_eq m₁ l))

lemma isShuffle_planar {N : ℕ} (hN : N + 1 = k + l) (hj : ch j = STree.node m₂ c₂)
    (ht : (STree.node m₁ ch).IsShuffle) (r : Fin N) : (planar ch j c₂ hN r).IsShuffle := by
  obtain ⟨x, rfl⟩ := (posEquivF j l N hN).surjective r
  rcases x with a | i
  · rw [planar_inl]
    exact ht.child _
  · rw [planar_inr]
    exact (hj ▸ ht.child j : (STree.node m₂ c₂).IsShuffle).child i

lemma first_planar_injective {N : ℕ} (hN : N + 1 = k + l) (hj : ch j = STree.node m₂ c₂)
    (ht : (STree.node m₁ ch).IsShuffle) (hnd : (STree.node m₁ ch).labels.Nodup) :
    Function.Injective fun r => (planar ch j c₂ hN r).first := by
  have ht₂ : (STree.node m₂ c₂).IsShuffle := hj ▸ ht.child j
  have hsub : ∀ i, (c₂ i).labels ≤ (ch j).labels := fun i => by
    rw [hj]
    exact labels_le_node _ _ i
  have hcross : ∀ (a : Without (Fin k) j) (i : Fin l), (ch a.1).first ≠ (c₂ i).first := by
    intro a i h
    have h1 := first_mem (ht.child a.1)
    have h2 := Multiset.mem_of_le (hsub i) (first_mem (ht₂.child i))
    rw [← h] at h2
    exact not_mem_of_node hnd a.2 h1 h2
  intro r r' h
  obtain ⟨x, rfl⟩ := (posEquivF j l N hN).surjective r
  obtain ⟨y, rfl⟩ := (posEquivF j l N hN).surjective r'
  congr 1
  rcases x with a | i <;> rcases y with b | i' <;>
    simp only [planar_inl, planar_inr] at h
  · exact congrArg Sum.inl (Subtype.ext (ht.mono.injective h))
  · exact absurd h (hcross a i')
  · exact absurd h.symm (hcross b i)
  · exact congrArg Sum.inr (ht₂.mono.injective h)

/-- **The merged tree is a shuffle tree.** -/
theorem isShuffle_rootMerge (hj : ch j = STree.node m₂ c₂) (ht : (STree.node m₁ ch).IsShuffle)
    (hnd : (STree.node m₁ ch).labels.Nodup) : (rootMerge m₁ ch j m₂ c₂).IsShuffle := by
  rw [rootMerge_eq hj ht]
  have hk := m₁.two_le
  refine ⟨by omega, fun r => isShuffle_planar _ hj ht _, ?_⟩
  exact (monotone_sortP _).strictMono_of_injective
    ((first_planar_injective _ hj ht hnd).comp (Equiv.injective _))

/-- **The merged tree has the leaves of the tree.** -/
theorem labels_rootMerge (hj : ch j = STree.node m₂ c₂) (ht : (STree.node m₁ ch).IsShuffle) :
    (rootMerge m₁ ch j m₂ c₂).labels = (STree.node m₁ ch).labels := by
  rw [rootMerge_eq hj ht, STree.labels_node, STree.labels_node]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp (sortP (planar ch j c₂ (mergeN_eq m₁ l)))
      (fun r => (planar ch j c₂ (mergeN_eq m₁ l) r).labels),
    ← Equiv.sum_comp (posEquivF j l (k + l - 1) (mergeN_eq m₁ l)), Fintype.sum_sum_type]
  simp only [planar_inl, planar_inr]
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun a => (ch a).labels) j, hj, STree.labels_node,
    add_comm]

lemma kids_planar_sortP {N : ℕ} (Q : Fin N → STree (VMono T)) (r : Fin N) :
    kids (Q ∘ sortP Q) ((sortP Q).symm r : ℕ) = cutRoot (toBar (Q r)) := by
  rw [kids_fin]
  simp

/-- A key of a child of a vertex is not the key of the vertex. -/
lemma wkey_notMem_wKeys_child {k : ℕ} {m : VMono T k} {ch : Fin k → STree (VMono T)}
    (ht : (STree.node m ch).IsShuffle) (j : Fin k) : wkey (STree.node m ch) ∉ wKeys (ch j) :=
  fun h => absurd (mem_wKeys (ht.child j) h).2 (not_le.2 (weight_toBar_child m ch j))

/-- **Merging the edge above a child of the root, on bar trees**: the bar tree of the merged
tree is the bar tree of the tree with that edge merged. -/
theorem toBar_rootMerge (hj : ch j = STree.node m₂ c₂) (ht : (STree.node m₁ ch).IsShuffle)
    (hnd : (STree.node m₁ ch).labels.Nodup) :
    toBar (rootMerge m₁ ch j m₂ c₂) = setF (wkey (ch j)) false (toBar (STree.node m₁ ch)) := by
  set hN := mergeN_eq m₁ l
  set Q := planar ch j c₂ hN with hQ
  set π := sortP Q with hπ
  have ht₂ : (STree.node m₂ c₂).IsShuffle := hj ▸ ht.child j
  rw [rootMerge_eq hj ht, toBar_node]
  show (fl false (mergedMono m₁.1.1 j m₂.1.1 hN π)).subst (kids (Q ∘ π)) = _
  rw [mergedMono, mergeMono, fl_false, allF_subst, subst_subst, toBar_node, setF_false_fl_subst,
    ite_self, fl_false]
  refine subst_congr _ fun a ha => ?_
  rw [labels_allF] at ha
  have hak := m₁.lt ha
  by_cases haj : a = (j : ℕ)
  · have hja : (⟨a, hak⟩ : Fin k) = j := Fin.ext haj
    simp only [if_pos haj]
    rw [allF_subst, subst_subst]
    have hkid : kids ch a = (fl true m₂.1.1).subst (kids c₂) := by
      obtain ⟨l', e₂, g₂, hm₂⟩ := m₂.exists_node
      rw [kids_of_lt ch hak, hja, hj, toBar_node, hm₂]
      rfl
    have hkey : STree.key ((fl true m₂.1.1).subst (kids c₂)) = wkey (ch j) := by
      rw [← hkid, kids_of_lt ch hak, hja, key_cutRoot]
      rfl
    rw [hkid, setF_false_fl_subst, if_pos hkey, fl_false]
    refine subst_congr _ fun i hi => ?_
    rw [labels_allF] at hi
    have hil := m₂.lt hi
    show kids (Q ∘ π) (rk₂ j hN π i) = setF (wkey (ch j)) false (kids c₂ i)
    rw [show rk₂ j hN π i = rk₂ j hN π ((⟨i, hil⟩ : Fin l) : ℕ) from rfl, rk₂_of, hπ,
      kids_planar_sortP, hQ, planar_inr, kids_of_lt c₂ hil]
    refine (setF_false_of_notMem fun hmem => ?_).symm
    rw [cutKeys_cutRoot_toBar, List.mem_toFinset, hj] at hmem
    exact wkey_notMem_wKeys_child ht₂ _ hmem
  · have hja : (⟨a, hak⟩ : Fin k) ≠ j := fun h => haj (congrArg Fin.val h)
    simp only [if_neg haj]
    show kids (Q ∘ π) (rk₁ j hN π a) = _
    rw [show rk₁ j hN π a = rk₁ j hN π ((⟨⟨a, hak⟩, hja⟩ : Without (Fin k) j).1 : ℕ) from rfl,
      rk₁_of, hπ, kids_planar_sortP, hQ, planar_inl, ← kids_of_lt ch hak]
    refine (setF_false_of_notMem fun hmem => ?_).symm
    rw [kids_of_lt ch hak, cutKeys_cutRoot_toBar, List.mem_toFinset] at hmem
    have h1 := (mem_wKeys (ht.child _) hmem).1
    have h2 : (ofLex (wkey (ch j))).1 ∈ (ch j).labels := by
      show (toBar (ch j)).first ∈ _
      rw [first_toBar _ (ht.child j)]
      exact first_mem (ht.child j)
    exact not_mem_of_node hnd hja h1 h2

end RootMerge

/-! ## Merging an edge at any depth -/

section MergeT

open STree

variable {T : ℕ → Type}

/-- Merging the edge above the child `j` of the root, a leaf leaving the tree as it is. -/
noncomputable def mergeAt {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T)) (j : Fin k) :
    STree (VMono T) → STree (VMono T)
  | .leaf _ => .node m ch
  | .node m₂ c₂ => rootMerge m ch j m₂ c₂

open Classical in
/-- **Merging the edge above the vertex of key `κ`** of a shuffle tree of monomials: at the child
of the root of key `κ` if there is one (`rootMerge`), and in every child otherwise. -/
noncomputable def mergeT : STree (VMono T) → ℕ ×ₗ ℕ → STree (VMono T)
  | .leaf a, _ => .leaf a
  | .node m ch, κ =>
    if h : ∃ j, wkey (ch j) = κ ∧ (ch j).weight ≠ 0 then mergeAt m ch h.choose (ch h.choose)
    else .node m fun j => mergeT (ch j) κ

lemma mergeT_of_not_mem : ∀ {t : STree (VMono T)} {κ : ℕ ×ₗ ℕ}, κ ∉ wKeys t → mergeT t κ = t
  | .leaf _, _, _ => rfl
  | .node m ch, κ, h => by
    have hmem : ∀ j, κ ∉ wKeys (ch j) := fun j hj => h (by
      rw [wKeys_node]
      exact List.mem_cons_of_mem _ ((mem_flatten_ofFn _ _).2 ⟨j, hj⟩))
    have hno : ¬∃ j, wkey (ch j) = κ ∧ (ch j).weight ≠ 0 := by
      rintro ⟨j, rfl, hw⟩
      exact hmem j (by rw [wKeys_eq_cons hw]; exact List.mem_cons_self ..)
    rw [mergeT, dif_neg hno]
    congr 1
    funext j
    exact mergeT_of_not_mem (hmem j)

variable {k : ℕ} {m : VMono T k} {ch : Fin k → STree (VMono T)}

lemma first_of_wkey_eq (ht : (STree.node m ch).IsShuffle) {j j' : Fin k}
    (h : wkey (ch j') = wkey (ch j)) : j' = j := by
  have := congrArg (fun κ : ℕ ×ₗ ℕ => (ofLex κ).1) h
  simp only [wkey, STree.key, ofLex_toLex] at this
  rw [first_toBar _ (ht.child _), first_toBar _ (ht.child _)] at this
  exact ht.mono.injective this

lemma mergeT_root (ht : (STree.node m ch).IsShuffle) {j : Fin k} {l : ℕ} {m₂ : VMono T l}
    {c₂ : Fin l → STree (VMono T)} (hj : ch j = STree.node m₂ c₂) :
    mergeT (STree.node m ch) (wkey (ch j)) = rootMerge m ch j m₂ c₂ := by
  have hex : ∃ j', wkey (ch j') = wkey (ch j) ∧ (ch j').weight ≠ 0 :=
    ⟨j, rfl, by rw [hj]; simp [STree.weight]⟩
  rw [mergeT, dif_pos hex]
  have hc : hex.choose = j := first_of_wkey_eq ht hex.choose_spec.1
  rw [hc, hj]
  rfl

lemma nodup_wKeys_child (ht : (STree.node m ch).IsShuffle)
    (hnd : (STree.node m ch).labels.Nodup) (j : Fin k) : (wKeys (ch j)).Nodup := by
  have := nodup_tail_wKeys ht hnd
  rw [wKeys_node, List.tail_cons] at this
  exact (List.nodup_flatten.1 this).1 _ (List.mem_ofFn.2 ⟨j, rfl⟩)

lemma not_mem_wKeys_of_ne (ht : (STree.node m ch).IsShuffle)
    (hnd : (STree.node m ch).labels.Nodup) {a b : Fin k} (hab : a ≠ b) {κ : ℕ ×ₗ ℕ}
    (hκ : κ ∈ wKeys (ch a)) : κ ∉ wKeys (ch b) := fun h' =>
  not_mem_of_node hnd hab (mem_wKeys (ht.child a) hκ).1 (mem_wKeys (ht.child b) h').1

lemma mergeT_child (ht : (STree.node m ch).IsShuffle) (hnd : (STree.node m ch).labels.Nodup)
    {j₀ : Fin k} {κ : ℕ ×ₗ ℕ} (hκ : κ ∈ (wKeys (ch j₀)).tail) :
    mergeT (STree.node m ch) κ = STree.node m (Function.update ch j₀ (mergeT (ch j₀) κ)) := by
  have hκ' : κ ∈ wKeys (ch j₀) := List.mem_of_mem_tail hκ
  have hno : ¬∃ j, wkey (ch j) = κ ∧ (ch j).weight ≠ 0 := by
    rintro ⟨j, rfl, hw⟩
    by_cases hjj : j = j₀
    · subst hjj
      have hnd' := nodup_wKeys_child ht hnd j
      rw [wKeys_eq_cons hw] at hnd'
      exact (List.nodup_cons.1 hnd').1 hκ
    · exact not_mem_wKeys_of_ne ht hnd (Ne.symm hjj) hκ'
        (by rw [wKeys_eq_cons hw]; exact List.mem_cons_self ..)
  rw [mergeT, dif_neg hno]
  congr 1
  funext j
  by_cases hjj : j = j₀
  · subst hjj
    rw [Function.update_self]
  · rw [Function.update_of_ne hjj]
    exact mergeT_of_not_mem (not_mem_wKeys_of_ne ht hnd (Ne.symm hjj) hκ')

lemma cutRoot_setF {y : STree (BE T)} {κ : ℕ ×ₗ ℕ} (hκ : STree.key y ≠ κ) :
    cutRoot (setF κ false y) = setF κ false (cutRoot y) := by
  cases y with
  | leaf => rfl
  | node d c =>
    have h2 : STree.key (STree.node ((d.1, true) : BE T _) c) ≠ κ := fun h =>
      hκ ((key_cutRoot (STree.node d c)).symm.trans h)
    show cutRoot (setF κ false (STree.node d c)) = setF κ false (STree.node (d.1, true) c)
    rw [setF_node, setF_node, if_neg h2]
    rfl

/-- **Merging an edge of a shuffle tree of monomials**: for `κ` the key of a vertex other than the
root, the merged tree is a shuffle tree with the same leaves, and its bar tree is the bar tree with
the cut edge `κ` merged. -/
theorem mergeT_spec : ∀ (t : STree (VMono T)) (κ : ℕ ×ₗ ℕ), t.IsShuffle → t.labels.Nodup →
    κ ∈ (wKeys t).tail → (mergeT t κ).IsShuffle ∧ (mergeT t κ).labels = t.labels ∧
      toBar (mergeT t κ) = setF κ false (toBar t)
  | .leaf _, _, _, _, h => by simp [wKeys] at h
  | .node (k := k) m ch, κ, ht, hnd, hκ => by
    rw [wKeys_node, List.tail_cons, mem_flatten_ofFn] at hκ
    obtain ⟨j₀, hj₀⟩ := hκ
    have hw := weight_ne_zero_of_mem hj₀
    rw [wKeys_eq_cons hw, List.mem_cons] at hj₀
    rcases hj₀ with rfl | hj₀
    · obtain ⟨l, m₂, c₂, hc⟩ : ∃ (l : ℕ) (m₂ : VMono T l) (c₂ : Fin l → STree (VMono T)),
          ch j₀ = STree.node m₂ c₂ := by
        cases h : ch j₀ with
        | leaf => rw [h] at hw; simp [STree.weight] at hw
        | node m₂ c₂ => exact ⟨_, m₂, c₂, rfl⟩
      rw [mergeT_root ht hc]
      exact ⟨isShuffle_rootMerge hc ht hnd, labels_rootMerge hc ht, toBar_rootMerge hc ht hnd⟩
    · have hjs := ht.child j₀
      have hjnd := nodup_of_node hnd j₀
      obtain ⟨ih1, ih2, ih3⟩ := mergeT_spec (ch j₀) κ hjs hjnd hj₀
      rw [mergeT_child ht hnd hj₀]
      have hfirst : ∀ j, (Function.update ch j₀ (mergeT (ch j₀) κ) j).first = (ch j).first := by
        intro j
        by_cases hjj : j = j₀
        · subst hjj
          rw [Function.update_self]
          exact first_eq_of_labels ih1 hjs ih2
        · rw [Function.update_of_ne hjj]
      refine ⟨⟨ht.pos, fun j => ?_, ?_⟩, ?_, ?_⟩
      · by_cases hjj : j = j₀
        · subst hjj
          rw [Function.update_self]
          exact ih1
        · rw [Function.update_of_ne hjj]
          exact ht.child j
      · simp only [hfirst]
        exact ht.mono
      · simp only [STree.labels_node]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hjj : j = j₀
        · subst hjj
          rw [Function.update_self, ih2]
        · rw [Function.update_of_ne hjj]
      · have hne : STree.key (toBar (ch j₀)) ≠ κ := by
          intro h
          have hnd' := nodup_wKeys_child ht hnd j₀
          rw [wKeys_eq_cons hw] at hnd'
          exact (List.nodup_cons.1 hnd').1 (by rw [show wkey (ch j₀) = κ from h]; exact hj₀)
        rw [toBar_node, toBar_node, setF_false_fl_subst, ite_self]
        refine subst_congr _ fun a ha => ?_
        rw [labels_fl] at ha
        have hak := m.lt ha
        rw [kids_of_lt _ hak, kids_of_lt _ hak]
        by_cases haj : (⟨a, hak⟩ : Fin k) = j₀
        · rw [haj, Function.update_self, ih3]
          exact cutRoot_setF hne
        · rw [Function.update_of_ne haj]
          refine (setF_false_of_notMem ?_).symm
          rw [cutKeys_cutRoot_toBar, List.mem_toFinset]
          exact not_mem_wKeys_of_ne ht hnd (Ne.symm haj) (List.mem_of_mem_tail hj₀)

end MergeT

/-! ## The sign of merging an edge -/

section MergeSign

open STree

variable {T : ℕ → Type}

/-- The leaves of different children of a merged vertex are disjoint. -/
lemma disjoint_planar {k l N : ℕ} {m₁ : VMono T k} {ch : Fin k → STree (VMono T)} {j : Fin k}
    {m₂ : VMono T l} {c₂ : Fin l → STree (VMono T)} (hN : N + 1 = k + l)
    (hj : ch j = STree.node m₂ c₂) (hnd : (STree.node m₁ ch).labels.Nodup) {r r' : Fin N}
    (hrr : r ≠ r') {x : ℕ} (hx : x ∈ (planar ch j c₂ hN r).labels) :
    x ∉ (planar ch j c₂ hN r').labels := by
  have hnd₂ : (STree.node m₂ c₂).labels.Nodup := hj ▸ nodup_of_node hnd j
  have hsub : ∀ i, (c₂ i).labels ≤ (ch j).labels := fun i => by
    rw [hj]
    exact labels_le_node _ _ i
  obtain ⟨x₁, rfl⟩ := (posEquivF j l N hN).surjective r
  obtain ⟨x₂, rfl⟩ := (posEquivF j l N hN).surjective r'
  have hne : x₁ ≠ x₂ := fun e => hrr (by rw [e])
  intro hx'
  rcases x₁ with a | i <;> rcases x₂ with b | i' <;> simp only [planar_inl, planar_inr] at hx hx'
  · exact not_mem_of_node hnd (fun e => hne (by rw [Subtype.ext e])) hx hx'
  · exact not_mem_of_node hnd a.2 hx (Multiset.mem_of_le (hsub i') hx')
  · exact not_mem_of_node hnd b.2 hx' (Multiset.mem_of_le (hsub i) hx)
  · exact not_mem_of_node hnd₂ (fun e => hne (by rw [e])) hx hx'

variable (K : Type u) [CommRing K]

/-- The Koszul sign of sorting the children of the vertex merged with its child `j`. -/
noncomputable def kzRoot {k : ℕ} (m₁ : VMono T k) (ch : Fin k → STree (VMono T)) (j : Fin k) :
    STree (VMono T) → K
  | .leaf _ => 1
  | .node (k := l) _ c₂ => kz K (fun r => wKeys (planar ch j c₂ (mergeN_eq m₁ l) r))
      (sortP (planar ch j c₂ (mergeN_eq m₁ l)))

open Classical in
/-- **The Koszul sign of merging the edge above the vertex of key `κ`**: the sign of sorting the
children of the merged vertex, a block of parity the number of vertices of its subtree. -/
noncomputable def kzAt : STree (VMono T) → ℕ ×ₗ ℕ → K
  | .leaf _, _ => 1
  | .node m ch, κ =>
    if h : ∃ j, wkey (ch j) = κ ∧ (ch j).weight ≠ 0 then kzRoot K m ch h.choose (ch h.choose)
    else ∏ j, kzAt (ch j) κ

lemma kzAt_of_not_mem : ∀ {t : STree (VMono T)} {κ : ℕ ×ₗ ℕ}, κ ∉ wKeys t → kzAt K t κ = 1
  | .leaf _, _, _ => rfl
  | .node m ch, κ, h => by
    have hmem : ∀ j, κ ∉ wKeys (ch j) := fun j hj => h (by
      rw [wKeys_node]
      exact List.mem_cons_of_mem _ ((mem_flatten_ofFn _ _).2 ⟨j, hj⟩))
    have hno : ¬∃ j, wkey (ch j) = κ ∧ (ch j).weight ≠ 0 := by
      rintro ⟨j, rfl, hw⟩
      exact hmem j (by rw [wKeys_eq_cons hw]; exact List.mem_cons_self ..)
    rw [kzAt, dif_neg hno]
    exact Finset.prod_eq_one fun j _ => kzAt_of_not_mem (hmem j)

lemma weight_mergeT_node {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T)) (κ : ℕ ×ₗ ℕ) :
    (mergeT (STree.node m ch) κ).weight ≠ 0 := by
  rw [mergeT]
  split_ifs with h
  · generalize h.choose = j
    cases ch j with
    | leaf => simp [mergeAt]
    | node m₂ c₂ =>
      simp only [mergeAt, rootMerge]
      split_ifs <;> simp [STree.weight]
  · simp [STree.weight]

/-- **The preorder of the merged tree**: removing the key `κ` from the keys of the vertices other
than the root and permuting the blocks of the children of the merged vertex by `π`, with the
Koszul sign `kzAt`. -/
theorem wKeys_mergeT : ∀ (t : STree (VMono T)) (κ : ℕ ×ₗ ℕ), t.IsShuffle → t.labels.Nodup →
    κ ∈ (wKeys t).tail → ∃ (P X Y S : List (ℕ ×ₗ ℕ)) (N : ℕ) (B : Fin N → List (ℕ ×ₗ ℕ))
      (π : Equiv.Perm (Fin N)), (wKeys t).tail = P ++ (X ++ κ :: Y) ++ S ∧
        (wKeys (mergeT t κ)).tail = P ++ (List.ofFn (B ∘ π)).flatten ++ S ∧
        (List.ofFn B).flatten = X ++ Y ∧ (∀ a b, a ≠ b → ∀ x ∈ B a, x ∉ B b) ∧
        kzAt K t κ = kz K B π
  | .leaf _, _, _, _, h => by simp [wKeys] at h
  | .node (k := k) m ch, κ, ht, hnd, hκ => by
    have hκ0 := hκ
    rw [wKeys_node, List.tail_cons, mem_flatten_ofFn] at hκ
    obtain ⟨j₀, hj₀⟩ := hκ
    have hw := weight_ne_zero_of_mem hj₀
    have hsplit := flatten_ofFn_split (fun a => wKeys (ch a)) j₀
    rw [wKeys_eq_cons hw, List.mem_cons] at hj₀
    rcases hj₀ with rfl | hj₀
    · obtain ⟨l, m₂, c₂, hc⟩ : ∃ (l : ℕ) (m₂ : VMono T l) (c₂ : Fin l → STree (VMono T)),
          ch j₀ = STree.node m₂ c₂ := by
        cases h : ch j₀ with
        | leaf => rw [h] at hw; simp [STree.weight] at hw
        | node m₂ c₂ => exact ⟨_, m₂, c₂, rfl⟩
      set hN := mergeN_eq m l
      set Q := planar ch j₀ c₂ hN with hQ
      have hpre : wKeys (ch j₀)
          = wkey (ch j₀) :: (List.ofFn fun i => wKeys (c₂ i)).flatten := by
        rw [hc, wKeys_node]
      refine ⟨[], ((List.ofFn fun a => wKeys (ch a)).take j₀).flatten,
        (List.ofFn fun i => wKeys (c₂ i)).flatten
          ++ ((List.ofFn fun a => wKeys (ch a)).drop (j₀ + 1)).flatten, [], _,
        fun r => wKeys (Q r), sortP Q, ?_, ?_, ?_, ?_, ?_⟩
      · rw [wKeys_node, List.tail_cons, hsplit, hpre]
        simp
      · rw [mergeT_root ht hc, rootMerge_eq hc ht, wKeys_node, List.tail_cons]
        simp only [List.nil_append, List.append_nil]
        rfl
      · rw [hQ, ofFn_planar ch j₀ c₂ hN wKeys, List.flatten_append, List.flatten_append]
        simp
      · intro a b hab x hx hx'
        have h1 := (mem_wKeys (isShuffle_planar hN hc ht a) hx).1
        have h2 := (mem_wKeys (isShuffle_planar hN hc ht b) hx').1
        exact disjoint_planar hN hc hnd hab h1 h2
      · have hex : ∃ j', wkey (ch j') = wkey (ch j₀) ∧ (ch j').weight ≠ 0 := ⟨j₀, rfl, hw⟩
        rw [kzAt, dif_pos hex]
        have hch : hex.choose = j₀ := first_of_wkey_eq ht hex.choose_spec.1
        rw [hch, hc]
        rfl
    · have hjs := ht.child j₀
      have hjnd := nodup_of_node hnd j₀
      obtain ⟨P, X, Y, S, N, B, π, h1, h2, h3, h4, h5⟩ := wKeys_mergeT (ch j₀) κ hjs hjnd hj₀
      obtain ⟨ih1, ih2, ih3⟩ := mergeT_spec (ch j₀) κ hjs hjnd hj₀
      have hwm : (mergeT (ch j₀) κ).weight ≠ 0 := by
        cases h : ch j₀ with
        | leaf => rw [h] at hw; simp [STree.weight] at hw
        | node m₂ c₂ => exact weight_mergeT_node m₂ c₂ κ
      have hvk : wkey (mergeT (ch j₀) κ) = wkey (ch j₀) := by
        rw [wkey, ih3, key_setF]
        rfl
      set A := ((List.ofFn fun a => wKeys (ch a)).take j₀).flatten
      set C := ((List.ofFn fun a => wKeys (ch a)).drop (j₀ + 1)).flatten
      refine ⟨A ++ wkey (ch j₀) :: P, X, Y, S ++ C, N, B, π, ?_, ?_, h3, h4, ?_⟩
      · rw [wKeys_node, List.tail_cons, hsplit, wKeys_eq_cons hw, h1]
        simp
      · rw [mergeT_child ht hnd hj₀, wKeys_node, List.tail_cons,
          flatten_ofFn_split _ j₀]
        simp only [Function.update_self]
        rw [take_ofFn_update wKeys ch j₀ (mergeT (ch j₀) κ),
          drop_ofFn_update wKeys ch j₀ (mergeT (ch j₀) κ)]
        rw [wKeys_eq_cons hwm, h2, hvk]
        simp only [List.append_assoc, List.cons_append]
        rfl
      · have hno : ¬∃ j, wkey (ch j) = κ ∧ (ch j).weight ≠ 0 := by
          rintro ⟨j, rfl, hw'⟩
          by_cases hjj : j = j₀
          · subst hjj
            have hnd' := nodup_wKeys_child ht hnd j
            rw [wKeys_eq_cons hw'] at hnd'
            exact (List.nodup_cons.1 hnd').1 hj₀
          · exact not_mem_wKeys_of_ne ht hnd (Ne.symm hjj) (List.mem_of_mem_tail hj₀)
              (by rw [wKeys_eq_cons hw']; exact List.mem_cons_self ..)
        rw [kzAt, dif_neg hno, Fintype.prod_eq_single j₀ fun j hj =>
          kzAt_of_not_mem K (not_mem_wKeys_of_ne ht hnd (Ne.symm hj) (List.mem_of_mem_tail hj₀))]
        exact h5

/-- **The sign rule of merging an edge.** For a shuffle tree of monomials `t` with distinct leaves
and the key `κ` of a vertex other than the root, `wsign t` times `(-1)` to the position of `κ` among
the keys of the vertices other than the root in preorder, times the Koszul sign of sorting the
children of the merged vertex, times the sign of the merged tree, is the sign `CutComplex.sgn` of
merging the cut edge `κ` of the bar tree. -/
theorem wsign_mergeT {t : STree (VMono T)} (ht : t.IsShuffle) (hnd : t.labels.Nodup)
    {κ : ℕ ×ₗ ℕ} (hκ : κ ∈ (wKeys t).tail) :
    wsign K t * (-1) ^ (wKeys t).tail.idxOf κ * kzAt K t κ * wsign K (mergeT t κ)
      = CutComplex.sgn K (cutKeys (toBar t)) κ := by
  obtain ⟨P, X, Y, S, N, B, π, h1, h2, h3, h4, h5⟩ := wKeys_mergeT K t κ ht hnd hκ
  have hL := nodup_tail_wKeys ht hnd
  rw [h1] at hL
  have hw : κ ∉ P ++ X := by
    intro hmem
    have hL' : (P ++ X ++ κ :: (Y ++ S)).Nodup := by simpa using hL
    exact (List.nodup_append.1 hL').2.2 _ hmem _ (List.mem_cons_self ..) rfl
  have hidx : (wKeys t).tail.idxOf κ = P.length + X.length := by
    rw [h1, show P ++ (X ++ κ :: Y) ++ S = (P ++ X) ++ κ :: (Y ++ S) by simp,
      List.idxOf_append_of_notMem hw, List.idxOf_cons_self, List.length_append, add_zero]
  rw [wsign, wsign, hidx, h5, h1, h2, sign_rule_list K P X Y S κ B π h3 h4 hw,
    sgn_toBar K ht hnd, h1]

end MergeSign

/-! ## The differential identity from the expansion of the bar differential -/

section Reduction

open STree

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma nodup_smono {n : ℕ} (t : SMono (VMono T) (Finset.range n)) : t.1.labels.Nodup := by
  rw [t.2.2]
  exact Finset.nodup _

/-- **The merged tree as a shuffle basis index**: `mergeT t κ` for `κ` the key of a vertex other
than the root, and `t` otherwise. -/
noncomputable def mergeS {n : ℕ} (t : SMono (VMono T) (Finset.range n)) (κ : ℕ ×ₗ ℕ) :
    SMono (VMono T) (Finset.range n) :=
  if h : κ ∈ (wKeys t.1).tail then
    ⟨mergeT t.1 κ, (mergeT_spec t.1 κ t.2.1 (nodup_smono t) h).1,
      (mergeT_spec t.1 κ t.2.1 (nodup_smono t) h).2.1.trans t.2.2⟩
  else t

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma mergeS_val {n : ℕ} (t : SMono (VMono T) (Finset.range n)) {κ : ℕ ×ₗ ℕ}
    (h : κ ∈ (wKeys t.1).tail) : (mergeS t κ).1 = mergeT t.1 κ := by
  rw [mergeS, dif_pos h]

/-- **The expansion of the bar differential over the edges**, on the basis vector of `t`: the
merged trees, with the sign `(-1)` to the position of the edge among the vertices other than the
root in preorder, times the Koszul sign of sorting the children of the merged vertex. This is the
statement left open; `ΦL_d_of_expansion` derives the differential identity from it. -/
def DExpansion {n : ℕ} (t : SMono (VMono T) (Finset.range n)) : Prop :=
  Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n t)
    = ∑ κ ∈ (wKeys t.1).tail.toFinset,
        ((-1 : K) ^ (wKeys t.1).tail.idxOf κ * kzAt K t.1 κ) • barBasisN c hc n (mergeS t κ)

/-- **`Φ` intertwines the differentials on a basis vector whose bar differential expands over the
edges**: the sign rule `wsign_mergeT` and the merged bar trees `mergeT_spec` turn the expansion
into `STree.Bar.d`. -/
theorem ΦL_d_barBasisN_of_expansion {n : ℕ} (t : SMono (VMono T) (Finset.range n))
    (hexp : DExpansion c hc t) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n t))
      = STree.Bar.d K (ΦL c hc n (barBasisN c hc n t)) := by
  have hnd := nodup_smono t
  unfold DExpansion at hexp
  have hcut : cuts (treeEquiv n t : barSet T n).1 = (wKeys t.1).tail.toFinset :=
    cutKeys_toBar t.1
  rw [hexp, map_sum, Φ_barBasisN, map_smul, STree.Bar.d, CutComplex.d_single, one_smul,
    CutComplex.dX, hcut, Finset.smul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [List.mem_toFinset] at hκ
  have hX : (treeEquiv n (mergeS t κ) : barSet T n).1
      = setM κ false (treeEquiv n t : barSet T n).1 :=
    Subtype.ext (by
      show toBar (mergeS t κ).1 = setF κ false (toBar t.1)
      rw [mergeS_val t hκ, (mergeT_spec t.1 κ t.2.1 hnd hκ).2.2])
  rw [map_smul, Φ_barBasisN, hX, smul_smul, smul_smul, mergeS_val t hκ]
  congr 1
  have hs := wsign_mergeT K t.2.1 hnd hκ
  rw [cutKeys_toBar] at hs
  rw [← hs]
  linear_combination (-((-1 : K) ^ (wKeys t.1).tail.idxOf κ * kzAt K t.1 κ
    * wsign K (mergeT t.1 κ))) * wsign_mul_self K t.1

/-- **The differential identity from the expansion**: if the bar differential of every basis
vector of `B(T, Ī)(Fin n)` expands over the edges (`DExpansion`), then
`ΦL ∘ Bar.d = STree.Bar.d ∘ ΦL` on all of `B(T, Ī)(Fin n)`. -/
theorem ΦL_d_of_expansion {n : ℕ} (hexp : ∀ t : SMono (VMono T) (Finset.range n),
      DExpansion c hc t) (x : BarCoop (Ibar K E c hc) (Fin n)) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) x) = STree.Bar.d K (ΦL c hc n x) := by
  have h : (ΦL c hc n).comp (Bar.d (Ibar K E c hc) (Fin n))
      = (STree.Bar.d K).comp (ΦL c hc n) :=
    (barBasisN c hc n).ext fun t => ΦL_d_barBasisN_of_expansion c hc t (hexp t)
  exact LinearMap.congr_fun h x

end Reduction

/-! ## The expansion on trees with at most two vertices -/

section ExpansionTwo

open STree

variable {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma kzAt_root (K : Type u) [CommRing K] {k l : ℕ} {m : VMono T k}
    {ch : Fin k → STree (VMono T)} (ht : (STree.node m ch).IsShuffle) {j : Fin k}
    {m₂ : VMono T l} {c₂ : Fin l → STree (VMono T)} (hj : ch j = STree.node m₂ c₂) :
    kzAt K (STree.node m ch) (wkey (ch j))
      = kz K (fun r => wKeys (planar ch j c₂ (mergeN_eq m l) r))
          (sortP (planar ch j c₂ (mergeN_eq m l))) := by
  have hex : ∃ j', wkey (ch j') = wkey (ch j) ∧ (ch j').weight ≠ 0 :=
    ⟨j, rfl, by rw [hj]; simp [STree.weight]⟩
  rw [kzAt, dif_pos hex]
  have hch : hex.choose = j := first_of_wkey_eq ht hex.choose_spec.1
  rw [hch, hj]
  rfl

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)

omit [IsEmpty (T 1)] in
/-- **The expansion holds on the trees with one or two vertices**, by the computations of
`ShuffleAnySymDiff.lean`: a corolla has no edge and is killed by the bar differential, and a tree
with two vertices has one edge, of position zero, whose merged vertex has leaves as children. -/
theorem dExpansion_of_weight {n : ℕ} (t : SMono (VMono T) (Finset.range n))
    (hw : t.1.weight = 1 ∨ t.1.weight = 2) : DExpansion c hc t := by
  unfold DExpansion
  rcases hw with hw | hw
  · have htail : (wKeys t.1).tail = [] :=
      List.eq_nil_of_length_eq_zero (by rw [List.length_tail, length_wKeys, hw])
    rw [htail, d_barBasisN_of_weight_one c hc t hw]
    simp
  · obtain ⟨t, ht, hlab⟩ := t
    obtain ⟨k, m₁, ch, j₀, l, m₂, c₂, rfl, hj₀, hl₁, hl₂⟩ := exists_two hw
    have hnd : (STree.node m₁ ch).labels.Nodup := by
      rw [hlab]
      exact Finset.nodup _
    have hw₀ : (ch j₀).weight ≠ 0 := by
      rw [hj₀]
      simp [STree.weight]
    have hmem : wkey (ch j₀) ∈ (wKeys (STree.node m₁ ch)).tail := by
      rw [wKeys_node, List.tail_cons, mem_flatten_ofFn]
      exact ⟨j₀, by rw [wKeys_eq_cons hw₀]; exact List.mem_cons_self ..⟩
    have htail : (wKeys (STree.node m₁ ch)).tail = [wkey (ch j₀)] := by
      have hlen : (wKeys (STree.node m₁ ch)).tail.length = 1 := by
        rw [List.length_tail, length_wKeys, hw]
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hlen
      rw [ha] at hmem ⊢
      rw [List.mem_singleton.1 hmem]
    have hleaf : ∀ r, wKeys (planar ch j₀ c₂ (mergeN_eq m₁ l) r) = [] := by
      intro r
      obtain ⟨x, rfl⟩ := (posEquivF j₀ l _ (mergeN_eq m₁ l)).surjective r
      rcases x with a | i
      · obtain ⟨y, hy⟩ := hl₁ a.1 a.2
        rw [planar_inl, hy]
        rfl
      · obtain ⟨y, hy⟩ := hl₂ i
        rw [planar_inr, hy]
        rfl
    have hspec := mergeT_spec (STree.node m₁ ch) (wkey (ch j₀)) ht hnd hmem
    have hkey : wkey (ch j₀) = twoKey ch j₀ := by
      rw [twoKey, kids_fin, key_cutRoot]
      rfl
    have hS : mergeS ⟨STree.node m₁ ch, ht, hlab⟩ (wkey (ch j₀))
        = corollaS ⟨⟨_, (twoMono_mem hj₀ hl₁ hl₂ ht hlab).1⟩,
          (twoMono_mem hj₀ hl₁ hl₂ ht hlab).2⟩ := by
      refine Subtype.ext ?_
      rw [mergeS_val _ hmem]
      refine (toBar_injective (isShuffle_corolla _) hspec.1 ?_).symm
      rw [toBar_corolla, hspec.2.2, hkey, setF_toBar_two hj₀ hl₁ hl₂]
    dsimp only
    rw [htail, d_barBasisN_two c hc m₁ ch j₀ m₂ c₂ hj₀ hl₁ hl₂ ht hlab]
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.sum_singleton,
      List.idxOf_cons_self, pow_zero, one_mul]
    rw [kzAt_root K ht hj₀, kz_eq_one_of_nil K hleaf, one_smul, hS]

end ExpansionTwo

end ShuffleAnySym

end Operad
