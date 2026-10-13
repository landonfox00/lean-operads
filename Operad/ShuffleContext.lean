/-
# Contexts in shuffle monomials

A *context* is a monomial `M` with a vertex at the path `q` whose subtree is a small monomial `y`
with trees `ins 0, …, ins (k - 1)` grafted onto its leaves, the inputs being shuffle monomials in
increasing order of least labels (`LTree.IsCtx`). Replacing `y` by another monomial `y'` on the
same leaves gives the monomial `M.replaceAt q (y'.plug ins)`. This file has what the comparison of
substitutions at two windows of a monomial needs.

* **Grafting and replacing** (`LTree.plug_plug`, `LTree.subtreeAt_plug`, `LTree.replaceAt_plug`,
  `LTree.replaceAt_append`): grafting commutes with taking and replacing subtrees inside the
  grafted tree, and the leaf of label `j` sits at the path `LTree.leafPos j y`.
* **Windows of grafted trees** (`LTree.windowRoot_plug`, `LTree.winIns_plug`): grafting inputs
  whose least labels increase with the labels keeps the windows, and grafts their inputs.
* **Contexts** (`LTree.IsCtx`): replacing the small monomial keeps the monomials of arity `n`
  (`LTree.ctx_mem_monomials`) and the order of the path-lexicographic keys
  (`LTree.pathKey_ctx_lt`); an edge of the small monomial, or of an input, is an edge of the
  monomial with the same window, and substituting there is substituting in the small monomial,
  or in the input (`LTree.substAt_ctx`, `LTree.substAt_ctx_ins`). The window of an edge is a
  context of arity three (`LTree.isCtx_window`), and so is, after standardization, the subtree of
  three vertices spanned by two adjacent edges, of arity four (`LTree.isCtx_std`, through the
  truncation `LTree.trunc`).
* **Two edges** of a monomial share a vertex, or one lies in an input of the window of the other,
  or they lie in disjoint subtrees (`LTree.edge_pair_cases`); substitutions at disjoint subtrees
  commute (`LTree.replaceAt_comm`).
-/
import Operad.ShuffleDualKoszul

namespace Operad

namespace LTree

variable {E : Type*}

/-! ## Grafting and replacing -/

lemma plug_plug (f g : ℕ → LTree E) : ∀ m : LTree E,
    (m.plug f).plug g = m.plug fun k => (f k).plug g
  | leaf _ => rfl
  | node e l r => by simp only [plug, plug_plug f g l, plug_plug f g r]

lemma relabel_plug (h : ℕ → ℕ) (ins : ℕ → LTree E) : ∀ m : LTree E,
    (m.relabel h).plug ins = m.plug (ins ∘ h)
  | leaf _ => rfl
  | node e l r => by simp only [relabel_node, plug, relabel_plug h ins l, relabel_plug h ins r]

lemma subtreeAt_plug (ins : ℕ → LTree E) : ∀ (y : LTree E) (p : List Bool), ValidPath y p →
    (y.plug ins).subtreeAt p = (y.subtreeAt p).plug ins
  | y, [], _ => by simp
  | leaf _, _ :: _, h => h.elim
  | node _ l _, false :: p, h => subtreeAt_plug ins l p h
  | node _ _ r, true :: p, h => subtreeAt_plug ins r p h

lemma replaceAt_plug (ins : ℕ → LTree E) : ∀ (y : LTree E) (p : List Bool) (X : LTree E),
    ValidPath y p → (y.plug ins).replaceAt p (X.plug ins) = (y.replaceAt p X).plug ins
  | y, [], X, _ => by simp
  | leaf _, _ :: _, _, h => h.elim
  | node e l r, false :: p, X, h => by simp only [plug, replaceAt, replaceAt_plug ins l p X h]
  | node e l r, true :: p, X, h => by simp only [plug, replaceAt, replaceAt_plug ins r p X h]

lemma replaceAt_append : ∀ (t : LTree E) (q p : List Bool) (U X : LTree E), ValidPath t q →
    (t.replaceAt q U).replaceAt (q ++ p) X = t.replaceAt q (U.replaceAt p X)
  | t, [], p, U, X, _ => by simp
  | leaf _, _ :: _, _, _, _, h => h.elim
  | node e l r, false :: q, p, U, X, h => by
    simp only [replaceAt, List.cons_append, replaceAt_append l q p U X h]
  | node e l r, true :: q, p, U, X, h => by
    simp only [replaceAt, List.cons_append, replaceAt_append r q p U X h]

lemma subtreeAt_replaceAt_append {t : LTree E} {q : List Bool} (h : ValidPath t q) (p : List Bool)
    (U : LTree E) : (t.replaceAt q U).subtreeAt (q ++ p) = U.subtreeAt p := by
  rw [subtreeAt_append, subtreeAt_replaceAt t q U h]

/-- The edge into the second slot only needs a vertex there. -/
lemma isEdgeRoot_true (e g : E) (c a b : LTree E) : (node e c (node g a b)).IsEdgeRoot true := by
  cases c <;> trivial

lemma isEdgeRoot_plug (ins : ℕ → LTree E) :
    ∀ (u : LTree E) (s : Bool), u.IsEdgeRoot s → (u.plug ins).IsEdgeRoot s
  | node _ (node _ _ _) _, false, _ => trivial
  | node _ (leaf _) (node _ _ _), true, _ => isEdgeRoot_true _ _ _ _ _
  | node _ (node _ _ _) (node _ _ _), true, _ => trivial

lemma winInputs_true (e g : E) (c a b : LTree E) :
    (node e c (node g a b)).winInputs true = (c, a, b) := by
  cases c <;> rfl

lemma windowRoot_true (e g : E) (c a b : LTree E) :
    (node e c (node g a b)).windowRoot true = window e g true a.minLabel b.minLabel c.minLabel := by
  cases c <;> rfl

/-! ## The leaf of a label -/

/-- **The path to the leaf labelled `k`**, on a tree with distinct labels. -/
def leafPos (k : ℕ) : LTree E → List Bool
  | leaf _ => []
  | node _ l r => if k ∈ l.labels then false :: leafPos k l else true :: leafPos k r

lemma subtreeAt_leafPos (k : ℕ) : ∀ y : LTree E, k ∈ y.labels → y.subtreeAt (leafPos k y) = leaf k
  | leaf a, h => by
    simp only [labels_leaf, List.mem_singleton] at h
    subst h
    rfl
  | node e l r, h => by
    by_cases hl : k ∈ l.labels
    · simp only [leafPos, hl, if_true, subtreeAt]
      exact subtreeAt_leafPos k l hl
    · have hr : k ∈ r.labels := by simpa [hl] using h
      simp only [leafPos, hl, if_false, subtreeAt]
      exact subtreeAt_leafPos k r hr

lemma validPath_leafPos (k : ℕ) : ∀ y : LTree E, ValidPath y (leafPos k y)
  | leaf _ => trivial
  | node e l r => by
    by_cases hl : k ∈ l.labels
    · simp only [leafPos, hl, if_true]
      exact validPath_leafPos k l
    · simp only [leafPos, hl, if_false]
      exact validPath_leafPos k r

lemma subtreeAt_plug_leafPos (ins : ℕ → LTree E) {y : LTree E} {k : ℕ} (hk : k ∈ y.labels)
    (d : List Bool) : (y.plug ins).subtreeAt (leafPos k y ++ d) = (ins k).subtreeAt d := by
  rw [subtreeAt_append, subtreeAt_plug ins y _ (validPath_leafPos k y), subtreeAt_leafPos k y hk]
  rfl

lemma replaceAt_plug_leafPos (ins : ℕ → LTree E) {k : ℕ} (d : List Bool) (X : LTree E) :
    ∀ y : LTree E, y.labels.Nodup → k ∈ y.labels →
      (y.plug ins).replaceAt (leafPos k y ++ d) X =
        y.plug (Function.update ins k ((ins k).replaceAt d X))
  | leaf a, _, h => by
    simp only [labels_leaf, List.mem_singleton] at h
    subst h
    simp [leafPos, plug]
  | node e l r, hnd, h => by
    have hnd' := List.nodup_append.1 (by simpa using hnd : (l.labels ++ r.labels).Nodup)
    by_cases hl : k ∈ l.labels
    · have hr : k ∉ r.labels := fun hr => hnd'.2.2 k hl k hr rfl
      simp only [leafPos, hl, if_true, plug, List.cons_append, replaceAt,
        replaceAt_plug_leafPos ins d X l hnd'.1 hl]
      congr 1
      exact plug_congr fun a ha => by
        rw [Function.update_of_ne (fun h : a = k => hr (h ▸ ha))]
    · have hr : k ∈ r.labels := by simpa [hl] using h
      simp only [leafPos, hl, if_false, plug, List.cons_append, replaceAt,
        replaceAt_plug_leafPos ins d X r hnd'.2.1 hr]
      congr 1
      exact plug_congr fun a ha => by
        rw [Function.update_of_ne (fun h : a = k => hl (h ▸ ha))]

/-! ## Inputs in increasing order of least labels -/

lemma minLabel_plug_of_strictOn {ins : ℕ → LTree E} : ∀ m : LTree E,
    StrictOn (fun a => (ins a).minLabel) m → (m.plug ins).minLabel = (ins m.minLabel).minLabel
  | leaf _, _ => rfl
  | node e l r, h => by
    simp only [plug, minLabel_node, minLabel_plug_of_strictOn l h.left,
      minLabel_plug_of_strictOn r h.right]
    have hl : l.minLabel ∈ (node e l r).labels := by simp [minLabel_mem]
    have hr : r.minLabel ∈ (node e l r).labels := by simp [minLabel_mem]
    rcases le_or_gt l.minLabel r.minLabel with hlr | hlr
    · rw [min_eq_left hlr]
      rcases hlr.lt_or_eq with hlr | hlr
      · exact min_eq_left (h _ hl _ hr hlr).le
      · rw [hlr, min_self]
    · rw [min_eq_right hlr.le]
      exact min_eq_right (h _ hr _ hl hlr).le

lemma isShuffle_plug_of_strictOn {ins : ℕ → LTree E} : ∀ m : LTree E, m.IsShuffle →
    StrictOn (fun a => (ins a).minLabel) m → (∀ a ∈ m.labels, (ins a).IsShuffle) →
    (m.plug ins).IsShuffle
  | leaf a, _, _, hs => hs a (by simp)
  | node e l r, ⟨hlr, hl, hr⟩, h, hs => by
    refine ⟨?_, isShuffle_plug_of_strictOn l hl h.left fun a ha => hs a (by simp [ha]),
      isShuffle_plug_of_strictOn r hr h.right fun a ha => hs a (by simp [ha])⟩
    rw [minLabel_plug_of_strictOn l h.left, minLabel_plug_of_strictOn r h.right]
    exact h _ (by simp [minLabel_mem]) _ (by simp [minLabel_mem]) hlr

/-- **Grafting inputs in increasing order of least labels keeps the window.** -/
lemma windowRoot_plug {ins : ℕ → LTree E} : ∀ (u : LTree E) (s : Bool),
    StrictOn (fun a => (ins a).minLabel) u → u.IsEdgeRoot s →
      (u.plug ins).windowRoot s = u.windowRoot s
  | node e (node g a b) c, false, h, _ => by
    have ha : a.minLabel ∈ (node e (node g a b) c).labels := by simp [minLabel_mem]
    have hb : b.minLabel ∈ (node e (node g a b) c).labels := by simp [minLabel_mem]
    have hc : c.minLabel ∈ (node e (node g a b) c).labels := by simp [minLabel_mem]
    simp only [plug, windowRoot, minLabel_plug_of_strictOn a h.left.left,
      minLabel_plug_of_strictOn b h.left.right, minLabel_plug_of_strictOn c h.right, window,
      rank3_relabel h ha hb hc ha, rank3_relabel h ha hb hc hb, rank3_relabel h ha hb hc hc]
  | node e (leaf c) (node g a b), true, h, _ => by
    have ha : a.minLabel ∈ (node e (leaf c) (node g a b)).labels := by simp [minLabel_mem]
    have hb : b.minLabel ∈ (node e (leaf c) (node g a b)).labels := by simp [minLabel_mem]
    have hc : (leaf c : LTree E).minLabel ∈ (node e (leaf c) (node g a b)).labels := by simp
    simp only [plug]
    rw [windowRoot_true, windowRoot_true, minLabel_plug_of_strictOn a h.right.left,
      minLabel_plug_of_strictOn b h.right.right,
      show ((ins c).minLabel = (ins (leaf c : LTree E).minLabel).minLabel) from rfl, window,
      window, rank3_relabel h ha hb hc ha, rank3_relabel h ha hb hc hb,
      rank3_relabel h ha hb hc hc]
  | node e (node g' a' b') (node g a b), true, h, _ => by
    set c := node g' a' b'
    have ha : a.minLabel ∈ (node e c (node g a b)).labels := by simp [minLabel_mem]
    have hb : b.minLabel ∈ (node e c (node g a b)).labels := by simp [minLabel_mem]
    have hc : c.minLabel ∈ (node e c (node g a b)).labels := by simp [minLabel_mem]
    have hpc : (node g' a' b').plug ins = c.plug ins := rfl
    simp only [plug]
    rw [windowRoot_true, windowRoot_true, minLabel_plug_of_strictOn a h.right.left,
      minLabel_plug_of_strictOn b h.right.right, hpc, minLabel_plug_of_strictOn c h.left,
      window, window, rank3_relabel h ha hb hc ha, rank3_relabel h ha hb hc hb,
      rank3_relabel h ha hb hc hc]

/-- **Grafting inputs in increasing order of least labels grafts the inputs of the window.** -/
lemma winIns_plug {ins : ℕ → LTree E} : ∀ (u : LTree E) (s : Bool),
    StrictOn (fun a => (ins a).minLabel) u → u.IsEdgeRoot s →
    ∀ k, (u.plug ins).winIns s k = (u.winIns s k).plug ins
  | node e (node g a b) c, false, h, _, k => by
    have hb : b.minLabel ∈ (node e (node g a b) c).labels := by simp [minLabel_mem]
    have hc : c.minLabel ∈ (node e (node g a b) c).labels := by simp [minLabel_mem]
    simp only [winIns, plug, winInputs, minLabel_plug_of_strictOn b h.left.right,
      minLabel_plug_of_strictOn c h.right, h.lt_iff hb hc, ins3]
    split_ifs <;> rfl
  | node e c (node g a b), true, _, _, k => by
    simp only [winIns, plug, winInputs_true, ins3]
    split_ifs <;> rfl

/-! ## Contexts -/

/-- **A context of arity `k`** in `M` at the vertex `q`: inputs `ins 0, …, ins (k - 1)`, shuffle
monomials in increasing order of least labels, whose labels are those of the subtree at `q`. A
monomial `y` on the labels `0, …, k - 1` gives the monomial `M.replaceAt q (y.plug ins)`. -/
structure IsCtx (M : LTree E) (q : List Bool) (k : ℕ) (ins : ℕ → LTree E) : Prop where
  node : ∃ e l r, M.subtreeAt q = node e l r
  shuffle : ∀ j < k, (ins j).IsShuffle
  mono : ∀ i j, i < j → j < k → (ins i).minLabel < (ins j).minLabel
  perm : (M.subtreeAt q).labels.Perm ((List.range k).flatMap fun j => (ins j).labels)

lemma lt_of_perm_range {y : LTree E} {k : ℕ} (hy : y.labels.Perm (List.range k)) :
    ∀ a ∈ y.labels, a < k := fun _ ha => List.mem_range.1 (hy.subset ha)

namespace IsCtx

variable {M : LTree E} {q : List Bool} {k : ℕ} {ins : ℕ → LTree E} (hc : IsCtx M q k ins)
include hc

lemma valid : ValidPath M q := validPath_of_node M q hc.node

lemma strictOn {y : LTree E} (hy : ∀ a ∈ y.labels, a < k) :
    StrictOn (fun a => (ins a).minLabel) y :=
  fun a _ b hb hab => hc.mono a b hab (hy b hb)

lemma perm_plug {y : LTree E} (hy : y.labels.Perm (List.range k)) :
    (y.plug ins).labels.Perm (M.subtreeAt q).labels := by
  rw [labels_plug]
  exact (hy.flatMap_right _).trans hc.perm.symm

/-- **A context keeps the labels.** -/
lemma labels_ctx {y : LTree E} (hy : y.labels.Perm (List.range k)) :
    (M.replaceAt q (y.plug ins)).labels.Perm M.labels :=
  labels_replaceAt_perm M q _ hc.node (hc.perm_plug hy)

/-- **A context keeps the shuffle condition.** -/
lemma isShuffle_ctx (hM : M.IsShuffle) {y : LTree E} (hys : y.IsShuffle)
    (hy : y.labels.Perm (List.range k)) : (M.replaceAt q (y.plug ins)).IsShuffle :=
  isShuffle_replaceAt M q _ hc.node hM
    (isShuffle_plug_of_strictOn y hys (hc.strictOn (lt_of_perm_range hy))
      fun a ha => hc.shuffle a (lt_of_perm_range hy a ha))
    (hc.perm_plug hy)

/-- **The inputs of a context have disjoint labels.** -/
lemma disjoint (hnd : M.labels.Nodup) :
    ∀ j < k, ∀ j' < k, j ≠ j' → ∀ i ∈ (ins j).labels, i ∉ (ins j').labels := by
  have h := hc.perm.nodup_iff.1 (nodup_subtreeAt M q hnd)
  rw [List.nodup_flatMap] at h
  intro j hj j' hj' hjj i hi hi'
  have hd := h.2.forall (fun a b hab => List.Disjoint.symm hab) (List.mem_range.2 hj)
    (List.mem_range.2 hj') hjj
  exact hd hi hi'

lemma nodup_ins (hnd : M.labels.Nodup) : ∀ j < k, (ins j).labels.Nodup := by
  have h := hc.perm.nodup_iff.1 (nodup_subtreeAt M q hnd)
  rw [List.nodup_flatMap] at h
  exact fun j hj => h.1 j (List.mem_range.2 hj)

/-- **The path to a leaf of an input**, after replacing: to the vertex, then in the new
monomial to the input, then inside the input. -/
lemma path_ctx_of_mem (hnd : M.labels.Nodup) {y : LTree E} (hy : y.labels.Perm (List.range k))
    {i j : ℕ} (hj : j < k) (hi : i ∈ (ins j).labels) :
    (M.replaceAt q (y.plug ins)).path i = M.decAt q ++ y.path j ++ (ins j).path i := by
  have hmem : i ∈ (y.plug ins).labels := by
    rw [labels_plug, List.mem_flatMap]
    exact ⟨j, hy.symm.subset (List.mem_range.2 hj), hi⟩
  rw [path_replaceAt_of_mem M q _ hnd hc.node (hc.perm_plug hy) hmem, List.append_assoc,
    path_plug ins (hc.disjoint hnd) hj hi y (lt_of_perm_range hy)
      (hy.nodup_iff.2 List.nodup_range) (hy.symm.subset (List.mem_range.2 hj))]

lemma path_ctx_of_not_mem (hnd : M.labels.Nodup) {y : LTree E}
    (hy : y.labels.Perm (List.range k)) {i : ℕ} (hi : i ∈ M.labels)
    (hi' : i ∉ (M.subtreeAt q).labels) : (M.replaceAt q (y.plug ins)).path i = M.path i :=
  path_replaceAt_of_not_mem M q _ hnd hc.node (hc.perm_plug hy) hi hi'

/-- **A context is compatible with the path-lexicographic key**: replacing by a monomial with a
smaller key gives a monomial with a smaller key. -/
theorem pathKey_ctx_lt (rk : E → ℕ) {n : ℕ} (hM : M.labels.Perm (List.range n)) {y y' : LTree E}
    (hy : y.labels.Perm (List.range k)) (hy' : y'.labels.Perm (List.range k))
    (h : pathKey rk k y < pathKey rk k y') :
    pathKey rk n (M.replaceAt q (y.plug ins)) < pathKey rk n (M.replaceAt q (y'.plug ins)) := by
  have hnd : M.labels.Nodup := hM.nodup_iff.2 List.nodup_range
  set u := M.subtreeAt q with hu
  rw [pathKey_lt_iff, map_range_lt_iff] at h ⊢
  obtain ⟨k₀, hk₀, heq, hlt⟩ := h
  have hmemu : ∀ i ∈ u.labels, ∃ j < k, i ∈ (ins j).labels := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := List.mem_flatMap.1 (hc.perm.subset hi)
    exact ⟨j, List.mem_range.1 hj, hij⟩
  have hinsu : ∀ j < k, ∀ i ∈ (ins j).labels, i ∈ u.labels := fun j hj i hi =>
    hc.perm.symm.subset (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, hi⟩)
  have hut : ∀ i ∈ u.labels, i ∈ M.labels := fun i hi => labels_subtreeAt_subset M q hi
  have hseg : ∀ (m : LTree E), m.labels.Perm (List.range k) → ∀ j < k, ∀ i ∈ (ins j).labels,
      seg rk (M.replaceAt q (m.plug ins)) i
        = ((M.decAt q).length + (m.path j).length + ((ins j).path i).length) ::
          ((M.decAt q).map rk ++ (m.path j).map rk ++ ((ins j).path i).map rk) := by
    intro m hm j hj i hi
    rw [seg, hc.path_ctx_of_mem hnd hm hj hi]
    simp only [List.length_append, List.map_append, Nat.add_assoc, List.append_assoc]
  set i₀ := (ins k₀).minLabel with hi₀
  have hi₀mem : i₀ ∈ (ins k₀).labels := minLabel_mem _
  have hi₀n : i₀ < n := List.mem_range.1 (hM.subset (hut _ (hinsu k₀ hk₀ _ hi₀mem)))
  refine ⟨i₀, hi₀n, ?_, ?_⟩
  · intro j hj
    have hjt : j ∈ M.labels := hM.symm.subset (List.mem_range.2 (by omega))
    by_cases hju : j ∈ u.labels
    · obtain ⟨j', hj', hjj⟩ := hmemu j hju
      rcases lt_or_ge j' k₀ with hkk | hkk
      · rw [hseg y hy j' hj' j hjj, hseg y' hy' j' hj' j hjj]
        have := heq j' hkk
        simp only [seg, List.cons.injEq] at this
        rw [this.1, this.2]
      · exfalso
        have h1 : (ins j').minLabel ≤ j := minLabel_le_of_mem _ hjj
        have h2 : (ins k₀).minLabel ≤ (ins j').minLabel := by
          rcases hkk.lt_or_eq with hkk | hkk
          · exact (hc.mono k₀ j' hkk hj').le
          · rw [hkk]
        omega
    · rw [seg, seg, hc.path_ctx_of_not_mem hnd hy hjt hju, hc.path_ctx_of_not_mem hnd hy' hjt hju]
  · rw [hseg y hy k₀ hk₀ i₀ hi₀mem, hseg y' hy' k₀ hk₀ i₀ hi₀mem]
    simp only [seg] at hlt
    rw [List.cons_lt_cons_iff] at hlt ⊢
    rcases hlt with hlt | ⟨hl, hlt⟩
    · left
      omega
    · right
      refine ⟨by rw [hl], ?_⟩
      rw [List.append_assoc, List.append_assoc, append_lt_append_left_iff]
      exact append_lt_append_of_length_eq (by simp [hl]) hlt _ _

section Monomials

variable [Fintype E] [DecidableEq E]

/-- **A context keeps the monomials of arity `n`.** -/
lemma ctx_mem_monomials {n : ℕ} (hM : M ∈ monomials n) {y : LTree E} (hy : y ∈ monomials k) :
    M.replaceAt q (y.plug ins) ∈ monomials n := by
  rw [mem_monomials] at hM hy ⊢
  exact ⟨hc.isShuffle_ctx hM.1 hy.1 hy.2, (hc.labels_ctx hy.2).trans hM.2⟩

end Monomials

end IsCtx

/-! ### Edges of the small monomial and of the inputs -/

section Edges

variable {M : LTree E} {q : List Bool} (hq : ValidPath M q) (ins : ℕ → LTree E)
include hq

/-- **An edge of the small monomial is an edge of the monomial.** -/
lemma isEdge_ctx {y : LTree E} {p : List Bool} {s : Bool} (he : y.IsEdge p s) :
    (M.replaceAt q (y.plug ins)).IsEdge (q ++ p) s := by
  unfold IsEdge
  rw [subtreeAt_replaceAt_append hq, subtreeAt_plug ins y p (validPath_of_node y p he.exists_node)]
  exact isEdgeRoot_plug ins _ s he

/-- **The window of an edge of the small monomial** is unchanged by grafting the inputs. -/
lemma windowAt_ctx {y : LTree E} {p : List Bool} {s : Bool} (he : y.IsEdge p s)
    (hmono : StrictOn (fun a => (ins a).minLabel) y) :
    (M.replaceAt q (y.plug ins)).windowAt (q ++ p) s = y.windowAt p s := by
  unfold windowAt
  rw [subtreeAt_replaceAt_append hq, subtreeAt_plug ins y p (validPath_of_node y p he.exists_node)]
  exact windowRoot_plug _ s (hmono.mono (labels_subtreeAt_subset y p)) he

/-- **Substituting at an edge of the small monomial** is substituting in the small monomial. -/
lemma substAt_ctx {y : LTree E} {p : List Bool} {s : Bool} (he : y.IsEdge p s)
    (hmono : StrictOn (fun a => (ins a).minLabel) y) (σ : LTree E) :
    (M.replaceAt q (y.plug ins)).substAt (q ++ p) s σ =
      M.replaceAt q ((y.substAt p s σ).plug ins) := by
  have hv : ValidPath y p := validPath_of_node y p he.exists_node
  have hw : ((y.subtreeAt p).plug ins).winIns s = fun j => ((y.subtreeAt p).winIns s j).plug ins :=
    funext fun j => winIns_plug _ s (hmono.mono (labels_subtreeAt_subset y p)) he j
  unfold substAt
  rw [subtreeAt_replaceAt_append hq, subtreeAt_plug ins y p hv, replaceAt_append M q p _ _ hq,
    ← replaceAt_plug ins y p _ hv, plug_plug, hw]

/-- **An edge of an input is an edge of the monomial.** -/
lemma isEdge_ctx_ins {y : LTree E} {j : ℕ} (hj : j ∈ y.labels) {d : List Bool} {s : Bool}
    (he : (ins j).IsEdge d s) :
    (M.replaceAt q (y.plug ins)).IsEdge (q ++ (leafPos j y ++ d)) s := by
  unfold IsEdge
  rw [subtreeAt_replaceAt_append hq, subtreeAt_plug_leafPos ins hj]
  exact he

lemma windowAt_ctx_ins {y : LTree E} {j : ℕ} (hj : j ∈ y.labels) (d : List Bool) (s : Bool) :
    (M.replaceAt q (y.plug ins)).windowAt (q ++ (leafPos j y ++ d)) s = (ins j).windowAt d s := by
  unfold windowAt
  rw [subtreeAt_replaceAt_append hq, subtreeAt_plug_leafPos ins hj]

/-- **Substituting at an edge of an input** is substituting in the input. -/
lemma substAt_ctx_ins {y : LTree E} (hnd : y.labels.Nodup) {j : ℕ} (hj : j ∈ y.labels)
    (d : List Bool) (s : Bool) (τ : LTree E) :
    (M.replaceAt q (y.plug ins)).substAt (q ++ (leafPos j y ++ d)) s τ =
      M.replaceAt q (y.plug (Function.update ins j ((ins j).substAt d s τ))) := by
  unfold substAt
  rw [subtreeAt_replaceAt_append hq, subtreeAt_plug_leafPos ins hj, replaceAt_append M q _ _ _ hq,
    replaceAt_plug_leafPos ins d _ y hnd hj]

end Edges

/-! ### The context of a window -/

/-- **The window of an edge is a context of arity three.** -/
lemma isCtx_window {M : LTree E} {p : List Bool} {s : Bool} (he : M.IsEdge p s)
    (hs : M.IsShuffle) (hnd : M.labels.Nodup) : IsCtx M p 3 ((M.subtreeAt p).winIns s) where
  node := he.exists_node
  shuffle j _ := (winSpec_of_edge he hs hnd).shuffle j
  mono := (winSpec_of_edge he hs hnd).mono
  perm := by
    have := (winSpec_of_edge he hs hnd).perm
    simpa [show List.range 3 = [0, 1, 2] from rfl, List.append_assoc] using this

/-! ### Standardized contexts -/

/-- **A grafting decomposition gives a context**, after standardization: if the subtree at `q` is
`T` with the inputs `F a` grafted, each leaf `a` of `T` being the least label of `F a`, then the
standardization of `T` with the inputs in increasing order of least labels is a context. -/
lemma isCtx_std {M : LTree E} {q : List Bool} {T : LTree E} {F : ℕ → LTree E}
    (hnode : ∃ e l r, M.subtreeAt q = node e l r) (hu : M.subtreeAt q = T.plug F)
    (hT : T.labels.Nodup) (hmin : ∀ a ∈ T.labels, (F a).minLabel = a)
    (hs : ∀ a ∈ T.labels, (F a).IsShuffle) :
    IsCtx M q T.arity (F ∘ Nat.nth (· ∈ T.labelSet)) ∧
      (std T).plug (F ∘ Nat.nth (· ∈ T.labelSet)) = M.subtreeAt q := by
  have hcard : T.labelSet.card = T.arity := card_labelSet hT
  have hnth : ∀ i < T.arity, Nat.nth (· ∈ T.labelSet) i ∈ T.labels := fun i hi => by
    have := Nat.nth_mem_of_lt_card (finite_mem T.labelSet)
      (by simpa [card_finite_mem, hcard] using hi)
    simpa [labelSet] using this
  have hplug : (std T).plug (F ∘ Nat.nth (· ∈ T.labelSet)) = T.plug F := by
    rw [← relabel_plug, ← destd, destd_std]
  refine ⟨⟨hnode, fun j hj => hs _ (hnth j hj), fun i j hij hj => ?_, ?_⟩, hplug.trans hu.symm⟩
  · simp only [Function.comp, hmin _ (hnth i (hij.trans hj)), hmin _ (hnth j hj)]
    exact Nat.nth_strictMonoOn (finite_mem T.labelSet)
      (by simpa [card_finite_mem, hcard] using hij.trans hj)
      (by simpa [card_finite_mem, hcard] using hj) hij
  · rw [hu, labels_plug]
    have hT' : T.labels = (std T).labels.map (Nat.nth (· ∈ T.labelSet)) := by
      conv_lhs => rw [← destd_std (t := T)]
      rw [destd, labels_relabel]
    rw [hT', List.flatMap_map]
    exact (labels_std_perm hT).flatMap_right _

/-! ## Truncation -/

/-- **Truncation along a shape**: the vertices of `u` at the vertices of the shape `S` are kept,
and the subtrees at the leaves of `S` become leaves labelled by their least labels. -/
def trunc : LTree Unit → LTree E → LTree E
  | leaf _, u => leaf u.minLabel
  | node _ _ _, leaf a => leaf a
  | node _ S₁ S₂, node e l r => node e (trunc S₁ l) (trunc S₂ r)

/-- **The subtrees cut off by the truncation**, by least label. -/
def cutIns : LTree Unit → LTree E → ℕ → LTree E
  | leaf _, u, _ => u
  | node _ _ _, leaf a, _ => leaf a
  | node _ S₁ S₂, node _ l r, a =>
    if a ∈ (trunc S₁ l).labels then cutIns S₁ l a else cutIns S₂ r a

/-- `u` has a vertex at every vertex of the shape `S`. -/
def Covers : LTree Unit → LTree E → Prop
  | leaf _, _ => True
  | node _ _ _, leaf _ => False
  | node _ S₁ S₂, node _ l r => Covers S₁ l ∧ Covers S₂ r

lemma sublist_trunc : ∀ (S : LTree Unit) (u : LTree E), (trunc S u).labels.Sublist u.labels
  | leaf _, u => List.singleton_sublist.2 (minLabel_mem u)
  | node _ _ _, leaf _ => List.Sublist.refl _
  | node _ S₁ S₂, node _ l r => (sublist_trunc S₁ l).append (sublist_trunc S₂ r)

@[simp] lemma minLabel_trunc : ∀ (S : LTree Unit) (u : LTree E), (trunc S u).minLabel = u.minLabel
  | leaf _, _ => rfl
  | node _ _ _, leaf _ => rfl
  | node _ S₁ S₂, node _ l r => by simp [trunc, minLabel_trunc S₁ l, minLabel_trunc S₂ r]

lemma isShuffle_trunc : ∀ (S : LTree Unit) (u : LTree E), u.IsShuffle → (trunc S u).IsShuffle
  | leaf _, _, _ => trivial
  | node _ _ _, leaf _, _ => trivial
  | node _ S₁ S₂, node _ l r, ⟨h, hl, hr⟩ =>
    ⟨by simpa using h, isShuffle_trunc S₁ l hl, isShuffle_trunc S₂ r hr⟩

/-- **A tree is its truncation with the cut subtrees grafted.** -/
lemma plug_trunc : ∀ (S : LTree Unit) (u : LTree E), u.labels.Nodup →
    (trunc S u).plug (cutIns S u) = u
  | leaf _, _, _ => rfl
  | node _ _ _, leaf _, _ => rfl
  | node _ S₁ S₂, node e l r, hnd => by
    have hnd' := List.nodup_append.1 (by simpa using hnd : (l.labels ++ r.labels).Nodup)
    simp only [trunc, plug]
    congr 1
    · refine (plug_congr fun a ha => ?_).trans (plug_trunc S₁ l hnd'.1)
      simp [cutIns, ha]
    · refine (plug_congr fun a ha => ?_).trans (plug_trunc S₂ r hnd'.2.1)
      have ha' : a ∉ (trunc S₁ l).labels := fun h =>
        hnd'.2.2 a ((sublist_trunc S₁ l).subset h) a ((sublist_trunc S₂ r).subset ha) rfl
      simp [cutIns, ha']

lemma minLabel_cutIns : ∀ (S : LTree Unit) (u : LTree E), ∀ a ∈ (trunc S u).labels,
    (cutIns S u a).minLabel = a
  | leaf _, u, a, ha => by
    simp only [trunc, labels_leaf, List.mem_singleton] at ha
    simp [cutIns, ha]
  | node _ _ _, leaf b, a, ha => by
    simp only [trunc, labels_leaf, List.mem_singleton] at ha
    simp [cutIns, ha]
  | node _ S₁ S₂, node e l r, a, ha => by
    by_cases h₁ : a ∈ (trunc S₁ l).labels
    · simp only [cutIns, h₁, if_true]
      exact minLabel_cutIns S₁ l a h₁
    · have h₂ : a ∈ (trunc S₂ r).labels := by simpa [trunc, h₁] using ha
      simp only [cutIns, h₁, if_false]
      exact minLabel_cutIns S₂ r a h₂

lemma isShuffle_cutIns : ∀ (S : LTree Unit) (u : LTree E), u.IsShuffle →
    ∀ a, (cutIns S u a).IsShuffle
  | leaf _, _, h, _ => h
  | node _ _ _, leaf _, _, _ => trivial
  | node _ S₁ S₂, node e l r, ⟨_, hl, hr⟩, a => by
    simp only [cutIns]
    split_ifs
    · exact isShuffle_cutIns S₁ l hl a
    · exact isShuffle_cutIns S₂ r hr a

lemma arity_trunc : ∀ (S : LTree Unit) (u : LTree E), Covers S u → (trunc S u).arity = S.arity
  | leaf _, _, _ => rfl
  | node _ _ _, leaf _, h => h.elim
  | node _ S₁ S₂, node _ l r, ⟨h₁, h₂⟩ => by
    simp [trunc, arity, arity_trunc S₁ l h₁, arity_trunc S₂ r h₂]

/-- **The edges of the shape are edges of the truncation.** -/
lemma isEdge_trunc : ∀ (S : LTree Unit) (u : LTree E) (x : List Bool) (s : Bool), Covers S u →
    S.IsEdge x s → (trunc S u).IsEdge x s
  | leaf _, _, [], _, _, h => by simp [IsEdge, IsEdgeRoot] at h
  | leaf _, _, _ :: _, _, _, h => by simp [IsEdge, IsEdgeRoot, subtreeAt] at h
  | node _ _ _, leaf _, _, _, h, _ => h.elim
  | node _ S₁ S₂, node e l r, [], false, ⟨h₁, _⟩, h => by
    match S₁, l, h₁, h with
    | node _ _ _, node _ _ _, _, _ => trivial
    | leaf _, _, _, h => simp [IsEdge, IsEdgeRoot] at h
    | node _ _ _, leaf _, h₁, _ => exact h₁.elim
  | node _ S₁ S₂, node e l r, [], true, ⟨_, h₂⟩, h => by
    match S₂, r, h₂, h with
    | node _ _ _, node _ _ _, _, _ => exact isEdgeRoot_true _ _ _ _ _
    | leaf _, _, _, h => simp [IsEdge, IsEdgeRoot] at h
    | node _ _ _, leaf _, h₂, _ => exact h₂.elim
  | node _ S₁ _, node _ l _, false :: x, s, ⟨h₁, _⟩, h => isEdge_trunc S₁ l x s h₁ h
  | node _ _ S₂, node _ _ r, true :: x, s, ⟨_, h₂⟩, h => isEdge_trunc S₂ r x s h₂ h

/-- The shape of the two edges at a vertex. -/
def cherryShape : LTree Unit := node () (node () (leaf 0) (leaf 0)) (node () (leaf 0) (leaf 0))

/-- The shape of an edge into the slot `s` followed by an edge into the slot `s'`. -/
def chainShape (s s' : Bool) : LTree Unit :=
  if s then node () (leaf 0) (if s' then node () (leaf 0) (node () (leaf 0) (leaf 0))
      else node () (node () (leaf 0) (leaf 0)) (leaf 0))
  else node () (if s' then node () (leaf 0) (node () (leaf 0) (leaf 0))
      else node () (node () (leaf 0) (leaf 0)) (leaf 0)) (leaf 0)

lemma covers_cherry {u : LTree E} (h₁ : u.IsEdgeRoot false) (h₂ : u.IsEdgeRoot true) :
    Covers cherryShape u := by
  rcases u with _ | ⟨e, _ | ⟨f, a, b⟩, _ | ⟨g, c, d⟩⟩ <;>
    first
    | exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
    | simp_all [IsEdgeRoot]

lemma covers_chain {u : LTree E} {s s' : Bool} (h₁ : u.IsEdgeRoot s)
    (h₂ : (u.subtreeAt [s]).IsEdgeRoot s') : Covers (chainShape s s') u := by
  match u, s, s', h₁, h₂ with
  | node _ (node _ (node _ _ _) _) _, false, false, _, _ =>
    exact ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩
  | node _ (node _ _ (node _ _ _)) _, false, true, _, _ =>
    exact ⟨⟨trivial, ⟨trivial, trivial⟩⟩, trivial⟩
  | node _ _ (node _ (node _ _ _) _), true, false, _, _ =>
    exact ⟨trivial, ⟨⟨trivial, trivial⟩, trivial⟩⟩
  | node _ _ (node _ _ (node _ _ _)), true, true, _, _ =>
    exact ⟨trivial, ⟨trivial, ⟨trivial, trivial⟩⟩⟩

lemma arity_cherryShape : cherryShape.arity = 4 := rfl

lemma arity_chainShape (s s' : Bool) : (chainShape s s').arity = 4 := by
  cases s <;> cases s' <;> rfl

lemma isEdge_cherryShape (s : Bool) : cherryShape.IsEdge [] s := by
  cases s <;> trivial

lemma isEdge_chainShape (s s' : Bool) :
    (chainShape s s').IsEdge [] s ∧ (chainShape s s').IsEdge [s] s' := by
  cases s <;> cases s' <;> exact ⟨trivial, trivial⟩

/-- **The subtree of three vertices spanned by two edges**, along a shape covered by the subtree
at `q`, is a context of arity four after standardization. -/
theorem exists_ctx4 {M : LTree E} (hs : M.IsShuffle) (hnd : M.labels.Nodup) {q : List Bool}
    {S : LTree Unit} (hnode : ∃ e l r, M.subtreeAt q = node e l r)
    (hS : Covers S (M.subtreeAt q)) (hS4 : S.arity = 4) :
    ∃ (W : LTree E) (ins : ℕ → LTree E), IsCtx M q 4 ins ∧ W.plug ins = M.subtreeAt q ∧
      W.IsShuffle ∧ W.labels.Perm (List.range 4) ∧ ∀ x s, S.IsEdge x s → W.IsEdge x s := by
  set u := M.subtreeAt q with hu
  have hund : u.labels.Nodup := nodup_subtreeAt M q hnd
  have hus : u.IsShuffle := isShuffle_subtreeAt M q hs
  have hT : (trunc S u).labels.Nodup := (sublist_trunc S u).nodup hund
  have h4 : (trunc S u).arity = 4 := (arity_trunc S u hS).trans hS4
  obtain ⟨hc, hW⟩ := isCtx_std hnode (plug_trunc S u hund).symm hT (minLabel_cutIns S u)
    fun a _ => isShuffle_cutIns S u hus a
  rw [h4] at hc
  refine ⟨std (trunc S u), _, hc, hW, isShuffle_std (isShuffle_trunc S u hus), ?_,
    fun x s hx => isEdge_std.2 (isEdge_trunc S u x s hS hx)⟩
  have := labels_std_perm hT
  rwa [h4] at this

/-! ## Two edges of a monomial -/

/-- Two paths: one extends the other, or they part. -/
lemma path_cases : ∀ p₁ p₂ : List Bool, (∃ x, p₂ = p₁ ++ x) ∨ (∃ x, p₁ = p₂ ++ x) ∨
    ∃ c d₁ d₂ b, p₁ = c ++ b :: d₁ ∧ p₂ = c ++ (!b) :: d₂
  | [], p₂ => Or.inl ⟨p₂, rfl⟩
  | _ :: _, [] => Or.inr (Or.inl ⟨_, rfl⟩)
  | b₁ :: p₁, b₂ :: p₂ => by
    by_cases hb : b₁ = b₂
    · subst hb
      rcases path_cases p₁ p₂ with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨c, d₁, d₂, b, rfl, rfl⟩
      · exact Or.inl ⟨x, rfl⟩
      · exact Or.inr (Or.inl ⟨x, rfl⟩)
      · exact Or.inr (Or.inr ⟨b₁ :: c, d₁, d₂, b, rfl, rfl⟩)
    · have : b₂ = !b₁ := by cases b₁ <;> cases b₂ <;> simp_all
      subst this
      exact Or.inr (Or.inr ⟨[], p₁, p₂, b₁, rfl, rfl⟩)

/-- **A position in a tree with distinct labels** is a vertex of it, or goes through a leaf. -/
lemma pos_cases : ∀ (y : LTree E) (x : List Bool), y.labels.Nodup →
    (∃ e l r, y.subtreeAt x = node e l r) ∨ ∃ j ∈ y.labels, ∃ d, x = leafPos j y ++ d
  | leaf a, x, _ => Or.inr ⟨a, by simp, x, by simp [leafPos]⟩
  | node e l r, [], _ => Or.inl ⟨e, l, r, rfl⟩
  | node e l r, false :: x, hnd => by
    have hnd' := List.nodup_append.1 (by simpa using hnd : (l.labels ++ r.labels).Nodup)
    rcases pos_cases l x hnd'.1 with h | ⟨j, hj, d, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, by simp [hj], d, by simp [leafPos, hj]⟩
  | node e l r, true :: x, hnd => by
    have hnd' := List.nodup_append.1 (by simpa using hnd : (l.labels ++ r.labels).Nodup)
    rcases pos_cases r x hnd'.2.1 with h | ⟨j, hj, d, rfl⟩
    · exact Or.inl h
    · have hl : j ∉ l.labels := fun h => hnd'.2.2 j h j hj rfl
      exact Or.inr ⟨j, by simp [hj], d, by simp [leafPos, hl]⟩

@[simp] lemma subtreeAt_leaf (a : ℕ) (x : List Bool) : (leaf a : LTree E).subtreeAt x = leaf a := by
  cases x <;> rfl

lemma window_pos {e f : E} {s : Bool} {ma mb mo : ℕ} {x : List Bool}
    (h : ∃ e' l r, (window e f s ma mb mo).subtreeAt x = node e' l r) : x = [] ∨ x = [s] := by
  rcases x with _ | ⟨b, _ | ⟨b', x⟩⟩
  · exact Or.inl rfl
  · cases s <;> cases b <;> simp_all [window, subtreeAt]
  · cases s <;> cases b <;> cases b' <;> simp_all [window, subtreeAt]

lemma windowRoot_eq_window {u : LTree E} {s : Bool} (h : u.IsEdgeRoot s) :
    ∃ e f ma mb mo, u.windowRoot s = window e f s ma mb mo := by
  match u, s, h with
  | node e (node f a b) c, false, _ => exact ⟨e, f, _, _, _, rfl⟩
  | node e c (node f a b), true, _ => exact ⟨e, f, _, _, _, windowRoot_true e f c a b⟩

/-- **The window of an edge has its edge at the root**, on the same side. -/
lemma isEdge_windowAt {M : LTree E} {p : List Bool} {s : Bool} (he : M.IsEdge p s) :
    (M.windowAt p s).IsEdge [] s := by
  obtain ⟨e, f, ma, mb, mo, hW⟩ := windowRoot_eq_window (u := M.subtreeAt p) he
  unfold windowAt IsEdge
  rw [hW, subtreeAt_nil]
  cases s <;> simp [window, IsEdgeRoot]

/-- **An edge below a vertex with an edge**: at the vertex, at the lower vertex of the window, or
inside an input of the window. -/
theorem edge_below_cases {M : LTree E} {p : List Bool} {s : Bool} (he : M.IsEdge p s)
    (hs : M.IsShuffle) (hnd : M.labels.Nodup) {x : List Bool} {s' : Bool}
    (he' : M.IsEdge (p ++ x) s') :
    x = [] ∨ x = [s] ∨ ∃ j < 3, ∃ d, x = leafPos j (M.windowAt p s) ++ d ∧
      ((M.subtreeAt p).winIns s j).IsEdge d s' := by
  have hw := winSpec_of_edge he hs hnd
  obtain ⟨-, hWl, -⟩ := ShuffleBar.windowRoot_shape (M.subtreeAt p) s he
    (isShuffle_subtreeAt M p hs) (nodup_subtreeAt M p hnd)
  rcases pos_cases (M.windowAt p s) x (hWl.nodup_iff.2 List.nodup_range) with hx | ⟨j, hj, d, rfl⟩
  · obtain ⟨e, f, ma, mb, mo, hW⟩ := windowRoot_eq_window (u := M.subtreeAt p) he
    unfold windowAt at hx
    rw [hW] at hx
    rcases window_pos hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · refine Or.inr (Or.inr ⟨j, List.mem_range.1 (hWl.subset hj), d, rfl, ?_⟩)
    unfold IsEdge at he' ⊢
    rw [subtreeAt_append, ← hw.window] at he'
    unfold windowAt at hj he'
    rwa [subtreeAt_plug_leafPos _ hj] at he'

/-! ### Disjoint subtrees -/

lemma subtreeAt_replaceAt_of_diverge : ∀ (t : LTree E) (c d₁ d₂ : List Bool) (b : Bool)
    (X : LTree E), (t.replaceAt (c ++ b :: d₁) X).subtreeAt (c ++ (!b) :: d₂) =
      t.subtreeAt (c ++ (!b) :: d₂)
  | leaf _, [], _, _, _, _ => rfl
  | leaf _, _ :: _, _, _, _, _ => rfl
  | node _ _ _, [], _, _, false, _ => rfl
  | node _ _ _, [], _, _, true, _ => rfl
  | node _ l _, false :: c, d₁, d₂, b, X => subtreeAt_replaceAt_of_diverge l c d₁ d₂ b X
  | node _ _ r, true :: c, d₁, d₂, b, X => subtreeAt_replaceAt_of_diverge r c d₁ d₂ b X

lemma replaceAt_comm : ∀ (t : LTree E) (c d₁ d₂ : List Bool) (b : Bool) (X Y : LTree E),
    (t.replaceAt (c ++ b :: d₁) X).replaceAt (c ++ (!b) :: d₂) Y =
      (t.replaceAt (c ++ (!b) :: d₂) Y).replaceAt (c ++ b :: d₁) X
  | leaf _, [], _, _, _, _, _ => rfl
  | leaf _, _ :: _, _, _, _, _, _ => rfl
  | node _ _ _, [], _, _, false, _, _ => rfl
  | node _ _ _, [], _, _, true, _, _ => rfl
  | node e l r, false :: c, d₁, d₂, b, X, Y => by
    simp only [List.cons_append, replaceAt, replaceAt_comm l c d₁ d₂ b X Y]
  | node e l r, true :: c, d₁, d₂, b, X, Y => by
    simp only [List.cons_append, replaceAt, replaceAt_comm r c d₁ d₂ b X Y]

/-- **Substituting in a disjoint subtree keeps the subtree.** -/
lemma subtreeAt_substAt_of_diverge (t : LTree E) (c d₁ d₂ : List Bool) (b s : Bool)
    (σ : LTree E) : (t.substAt (c ++ b :: d₁) s σ).subtreeAt (c ++ (!b) :: d₂) =
      t.subtreeAt (c ++ (!b) :: d₂) :=
  subtreeAt_replaceAt_of_diverge t c d₁ d₂ b _

/-- **Substitutions in disjoint subtrees commute.** -/
lemma substAt_comm_of_diverge (t : LTree E) (c d₁ d₂ : List Bool) (b s₁ s₂ : Bool)
    (σ τ : LTree E) : (t.substAt (c ++ b :: d₁) s₁ σ).substAt (c ++ (!b) :: d₂) s₂ τ =
      (t.substAt (c ++ (!b) :: d₂) s₂ τ).substAt (c ++ b :: d₁) s₁ σ := by
  have h2 := subtreeAt_replaceAt_of_diverge t c d₂ d₁ (!b)
    (τ.plug ((t.subtreeAt (c ++ (!b) :: d₂)).winIns s₂))
  rw [Bool.not_not] at h2
  unfold substAt
  rw [subtreeAt_replaceAt_of_diverge, h2]
  have := replaceAt_comm t c d₁ d₂ b (σ.plug ((t.subtreeAt (c ++ b :: d₁)).winIns s₁))
    (τ.plug ((t.subtreeAt (c ++ (!b) :: d₂)).winIns s₂))
  exact this

end LTree

end Operad
