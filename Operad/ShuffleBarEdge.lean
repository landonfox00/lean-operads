/-
# Bar trees with one uncut edge

The chains of the bar construction of degree `n - 2` in arity `n` are supported on the bar trees
with exactly one uncut edge. Substituting the monomials of arity three at that edge
(`Operad.ShuffleBar.substBar`) sorts these bar trees into classes, one copy of the monomials of
arity three each, and the relator subcomplex is, in that degree, the sum over the classes of the
relators placed in each.

* **Keys and paths.** On a monomial with distinct labels the key of a vertex determines its path
  (`LTree.eq_of_key_subtreeAt`), and the flag of a vertex of a bar tree says whether its key is a
  cut key (`ShuffleBar.flagAt_eq`). So a bar tree with one uncut edge has one uncut vertex below
  the root (`ShuffleBar.eq_of_flagAt_eq_false`), the lower vertex of that edge.
* **A plugged monomial of arity three determines the monomial and its inputs**, given the side of
  its edge (`LTree.plug_inj`, `LTree.side3_eq_of_plug_eq`).
* **The classes** (`ShuffleBar.substBar_eq_substBar`): if two bar trees with one uncut edge have a
  substitution in common, the edges are at the same path and all their substitutions agree; the
  substitutions at an edge are distinct (`ShuffleBar.substBar_injective`), and a bar tree is the
  substitution of its own window (`ShuffleBar.substBar_windowAt`).
* **The relator subcomplex in degree `n - 2`** (`ShuffleBar.mem_J_iff_winCoef`): a chain lies in
  it exactly when, at every bar tree with one uncut edge, its coefficients on the substitutions at
  that edge (`ShuffleBar.winCoef`) form a relator.
-/
import Operad.ShuffleVData
import Operad.ShuffleGraded

universe u v

namespace Operad

namespace LTree

section Positions

variable {X : Type*}

lemma key_eq_iff {t u : LTree X} : key t = key u ↔ t.minLabel = u.minLabel ∧ t.arity = u.arity := by
  simp [key]

lemma arity_subtreeAt_cons_lt (e : X) (l r : LTree X) (b : Bool) (q : List Bool) :
    ((node e l r).subtreeAt (b :: q)).arity < (node e l r).arity := by
  have hl := ShuffleBar.arity_subtreeAt_le l q
  have hr := ShuffleBar.arity_subtreeAt_le r q
  have := arity_pos l
  have := arity_pos r
  cases b <;> simp only [subtreeAt, arity] <;> omega

/-- **The key tells the vertices apart**: on a monomial with distinct labels, two vertices with
the same key are at the same path. -/
theorem eq_of_key_subtreeAt : ∀ (m : LTree X) (q₁ q₂ : List Bool), m.labels.Nodup →
    (∃ e l r, m.subtreeAt q₁ = node e l r) → (∃ e l r, m.subtreeAt q₂ = node e l r) →
    key (m.subtreeAt q₁) = key (m.subtreeAt q₂) → q₁ = q₂
  | leaf _, [], _, _, ⟨_, _, _, h⟩, _, _ => by simp at h
  | leaf _, _ :: _, _, _, ⟨_, _, _, h⟩, _, _ => by simp [subtreeAt] at h
  | node _ _ _, [], [], _, _, _, _ => rfl
  | node e l r, [], b :: q, _, _, _, hk => by
    have := arity_subtreeAt_cons_lt e l r b q
    rw [key_eq_iff, subtreeAt_nil] at hk
    omega
  | node e l r, b :: q, [], _, _, _, hk => by
    have := arity_subtreeAt_cons_lt e l r b q
    rw [key_eq_iff, subtreeAt_nil] at hk
    omega
  | node e l r, false :: q₁, false :: q₂, hnd, h₁, h₂, hk => by
    have hnd' : (l.labels ++ r.labels).Nodup := by simpa using hnd
    rw [eq_of_key_subtreeAt l q₁ q₂ (List.nodup_append.1 hnd').1 h₁ h₂ hk]
  | node e l r, true :: q₁, true :: q₂, hnd, h₁, h₂, hk => by
    have hnd' : (l.labels ++ r.labels).Nodup := by simpa using hnd
    rw [eq_of_key_subtreeAt r q₁ q₂ (List.nodup_append.1 hnd').2.1 h₁ h₂ hk]
  | node e l r, false :: q₁, true :: q₂, hnd, _, _, hk => by
    have hnd' : (l.labels ++ r.labels).Nodup := by simpa using hnd
    rw [key_eq_iff] at hk
    exact absurd hk.1 (ne_of_nodup_append hnd'
      (labels_subtreeAt_subset l q₁ (minLabel_mem _))
      (labels_subtreeAt_subset r q₂ (minLabel_mem _)))
  | node e l r, true :: q₁, false :: q₂, hnd, _, _, hk => by
    have hnd' : (l.labels ++ r.labels).Nodup := by simpa using hnd
    rw [key_eq_iff] at hk
    exact absurd hk.1.symm (ne_of_nodup_append hnd'
      (labels_subtreeAt_subset l q₂ (minLabel_mem _))
      (labels_subtreeAt_subset r q₁ (minLabel_mem _)))

/-- The key of a vertex is a key of the monomial. -/
lemma key_subtreeAt_mem_nodeKeys : ∀ (m : LTree X) (q : List Bool),
    (∃ e l r, m.subtreeAt q = node e l r) → key (m.subtreeAt q) ∈ m.nodeKeys
  | leaf _, [], ⟨_, _, _, h⟩ => by simp at h
  | leaf _, _ :: _, ⟨_, _, _, h⟩ => by simp [subtreeAt] at h
  | node _ _ _, [], _ => by simp [nodeKeys]
  | node _ l _, false :: q, h => Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (key_subtreeAt_mem_nodeKeys l q h))
  | node _ _ r, true :: q, h => Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (key_subtreeAt_mem_nodeKeys r q h))

/-- **The key of a vertex below the root is the key of an edge.** -/
lemma key_subtreeAt_mem_edgeKeys (m : LTree X) (b : Bool) (q : List Bool)
    (h : ∃ e l r, m.subtreeAt (b :: q) = node e l r) : key (m.subtreeAt (b :: q)) ∈ m.edgeKeys := by
  cases m with
  | leaf => obtain ⟨_, _, _, h⟩ := h; simp [subtreeAt] at h
  | node e l r =>
    rw [edgeKeys_node]
    cases b
    · exact Finset.mem_union_left _ (key_subtreeAt_mem_nodeKeys l q h)
    · exact Finset.mem_union_right _ (key_subtreeAt_mem_nodeKeys r q h)

lemma edgeKeys_mapDec {Y : Type*} (f : X → Y) (t : LTree X) :
    (t.mapDec f).edgeKeys = t.edgeKeys := by
  cases t with
  | leaf => rfl
  | node e l r => rw [mapDec_node, edgeKeys_node, edgeKeys_node, nodeKeys_mapDec, nodeKeys_mapDec]

/-- The lower vertex of an edge is a vertex. -/
lemma IsEdge.exists_node_child {t : LTree X} {p : List Bool} {s : Bool} (h : t.IsEdge p s) :
    ∃ e l r, t.subtreeAt (p ++ [s]) = node e l r := by
  unfold IsEdge at h
  rw [subtreeAt_append]
  generalize t.subtreeAt p = u at h
  match u, s, h with
  | node _ (node e a b) _, false, _ => exact ⟨e, a, b, rfl⟩
  | node _ _ (node e a b), true, _ => exact ⟨e, a, b, rfl⟩

/-- **Every edge key is the key of the lower vertex of an edge.** -/
lemma exists_isEdge_of_mem_edgeKeys : ∀ (m : LTree X) {k : ℕ ×ₗ ℕ}, k ∈ m.edgeKeys →
    ∃ p s, m.IsEdge p s ∧ key (m.subtreeAt (p ++ [s])) = k
  | leaf _, k, hk => by simp [edgeKeys, edgeWins] at hk
  | node e l r, k, hk => by
    rw [edgeKeys_node, Finset.mem_union] at hk
    rcases hk with hk | hk
    · cases l with
      | leaf => simp [nodeKeys] at hk
      | node e' a b =>
        rw [nodeKeys, Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · exact ⟨[], false, trivial, rfl⟩
        · obtain ⟨p, s, he, hk⟩ :=
            exists_isEdge_of_mem_edgeKeys (node e' a b) (by rw [edgeKeys_node]; exact hk)
          exact ⟨false :: p, s, he, hk⟩
    · cases r with
      | leaf => simp [nodeKeys] at hk
      | node e' a b =>
        rw [nodeKeys, Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · exact ⟨[], true, by cases l <;> trivial, rfl⟩
        · obtain ⟨p, s, he, hk⟩ :=
            exists_isEdge_of_mem_edgeKeys (node e' a b) (by rw [edgeKeys_node]; exact hk)
          exact ⟨true :: p, s, he, hk⟩

end Positions

section Plug

variable {X : Type*}

/-- **The side of the edge of a plugged monomial of arity three** is determined by the plugged
tree, the inputs being fixed. -/
lemma side3_eq_of_plug_eq {σ σ' : LTree X} (hσs : σ.IsShuffle)
    (hσl : σ.labels.Perm (List.range 3)) (hσs' : σ'.IsShuffle)
    (hσl' : σ'.labels.Perm (List.range 3)) {ins : ℕ → LTree X}
    (h : σ.plug ins = σ'.plug ins) : side3 σ = side3 σ' := by
  have h0 := arity_pos (ins 0)
  have h1 := arity_pos (ins 1)
  have h2 := arity_pos (ins 2)
  obtain ⟨e, f, rfl | rfl | rfl⟩ := mono3_cases hσs hσl <;>
    obtain ⟨e', f', rfl | rfl | rfl⟩ := mono3_cases hσs' hσl' <;>
    first
    | rfl
    | (simp only [plug, node.injEq] at h
       have := congrArg arity h.2.1
       simp only [arity] at this
       omega)

/-- **A plugged monomial of arity three determines the monomial and the inputs**, the inputs in
increasing order of least labels and the side of the edge being given. -/
lemma plug_inj {σ σ' : LTree X} (hσs : σ.IsShuffle) (hσl : σ.labels.Perm (List.range 3))
    (hσs' : σ'.IsShuffle) (hσl' : σ'.labels.Perm (List.range 3)) {ins ins' : ℕ → LTree X}
    (h12 : (ins 1).minLabel < (ins 2).minLabel) (h12' : (ins' 1).minLabel < (ins' 2).minLabel)
    (hside : side3 σ = side3 σ') (h : σ.plug ins = σ'.plug ins') :
    σ = σ' ∧ ins 0 = ins' 0 ∧ ins 1 = ins' 1 ∧ ins 2 = ins' 2 := by
  obtain ⟨e, f, rfl | rfl | rfl⟩ := mono3_cases hσs hσl <;>
    obtain ⟨e', f', rfl | rfl | rfl⟩ := mono3_cases hσs' hσl' <;>
    simp only [side3, Bool.false_eq_true, Bool.true_eq_false] at hside <;>
    simp only [plug, node.injEq] at h
  · obtain ⟨rfl, ⟨rfl, h0, h1⟩, h2⟩ := h
    exact ⟨rfl, h0, h1, h2⟩
  · obtain ⟨-, ⟨-, -, h1⟩, h2⟩ := h
    rw [h1, h2] at h12
    exact absurd (h12.trans h12') (lt_irrefl _)
  · obtain ⟨-, ⟨-, -, h1⟩, h2⟩ := h
    rw [h1, h2] at h12
    exact absurd (h12.trans h12') (lt_irrefl _)
  · obtain ⟨rfl, ⟨rfl, h0, h2⟩, h1⟩ := h
    exact ⟨rfl, h0, h1, h2⟩
  · obtain ⟨rfl, h0, rfl, h1, h2⟩ := h
    exact ⟨rfl, h0, h1, h2⟩

end Plug

end LTree

namespace ShuffleBar

open LTree

variable {E : Type v}

/-! ## Flags and keys -/

lemma side3_liftW (c : Bool) (σ : LTree E) : side3 (liftW c σ) = side3 σ := by
  cases σ with
  | leaf => rfl
  | node e l r => cases l <;> rfl

lemma rootFlag_liftW (c : Bool) (e : E) (l r : LTree E) : rootFlag (liftW c (node e l r)) = c :=
  rfl

/-- **The flag of a vertex says whether its key is cut**, on a bar tree with distinct labels. -/
lemma flagAt_eq : ∀ (x : BarTree E) (q : List Bool), x.labels.Nodup →
    (∃ d l r, x.subtreeAt q = node d l r) → flagAt x q = decide (key (x.subtreeAt q) ∈ cutKeys x)
  | leaf _, [], _, ⟨_, _, _, h⟩ => by simp at h
  | leaf _, _ :: _, _, ⟨_, _, _, h⟩ => by simp [subtreeAt] at h
  | node d l r, [], _, _ => by
    have hl : key (node d l r) ∉ cutKeys l := fun h => key_not_mem_left d l r (cutKeys_subset l h)
    have hr : key (node d l r) ∉ cutKeys r := fun h => key_not_mem_right d l r (cutKeys_subset r h)
    simp only [flagAt, subtreeAt_nil, rootFlag, cutKeys]
    cases d.2 <;> simp [hl, hr]
  | node d l r, false :: q, hnd, h => by
    have hnd' : (l.labels ++ r.labels).Nodup := by simpa using hnd
    have hk : key (l.subtreeAt q) ∈ l.nodeKeys := key_subtreeAt_mem_nodeKeys l q h
    have ih := flagAt_eq l q (List.nodup_append.1 hnd').1 h
    have hiff : key (l.subtreeAt q) ∈ cutKeys (node d l r) ↔ key (l.subtreeAt q) ∈ cutKeys l := by
      constructor
      · intro h'
        rw [cutKeys, Finset.mem_union, Finset.mem_union] at h'
        rcases h' with h' | h' | h'
        · split_ifs at h' with hd
          · rw [Finset.mem_singleton] at h'
            exact absurd (h' ▸ hk) (key_not_mem_left d l r)
          · simp at h'
        · exact h'
        · exact absurd (cutKeys_subset r h') (Finset.disjoint_left.1 (disjoint_nodeKeys hnd) hk)
      · intro h'
        rw [cutKeys, Finset.mem_union, Finset.mem_union]
        exact Or.inr (Or.inl h')
    show flagAt l q = decide (key (l.subtreeAt q) ∈ cutKeys (node d l r))
    rw [ih, decide_eq_decide.2 hiff]
  | node d l r, true :: q, hnd, h => by
    have hnd' : (l.labels ++ r.labels).Nodup := by simpa using hnd
    have hk : key (r.subtreeAt q) ∈ r.nodeKeys := key_subtreeAt_mem_nodeKeys r q h
    have ih := flagAt_eq r q (List.nodup_append.1 hnd').2.1 h
    have hiff : key (r.subtreeAt q) ∈ cutKeys (node d l r) ↔ key (r.subtreeAt q) ∈ cutKeys r := by
      constructor
      · intro h'
        rw [cutKeys, Finset.mem_union, Finset.mem_union] at h'
        rcases h' with h' | h' | h'
        · split_ifs at h' with hd
          · rw [Finset.mem_singleton] at h'
            exact absurd (h' ▸ hk) (key_not_mem_right d l r)
          · simp at h'
        · exact absurd (cutKeys_subset l h') (Finset.disjoint_right.1 (disjoint_nodeKeys hnd) hk)
        · exact h'
      · intro h'
        rw [cutKeys, Finset.mem_union, Finset.mem_union]
        exact Or.inr (Or.inr h')
    show flagAt r q = decide (key (r.subtreeAt q) ∈ cutKeys (node d l r))
    rw [ih, decide_eq_decide.2 hiff]

/-- **A bar tree with one uncut edge has one uncut vertex below the root.** -/
theorem eq_of_flagAt_eq_false {Y : BarTree E} (hY : Valid Y)
    (hc : (cutKeys Y).card + 3 = Y.arity) {b₁ b₂ : Bool} {q₁ q₂ : List Bool}
    (hn₁ : ∃ d l r, Y.subtreeAt (b₁ :: q₁) = node d l r)
    (hn₂ : ∃ d l r, Y.subtreeAt (b₂ :: q₂) = node d l r)
    (hf₁ : flagAt Y (b₁ :: q₁) = false) (hf₂ : flagAt Y (b₂ :: q₂) = false) :
    b₁ :: q₁ = b₂ :: q₂ := by
  have hsub : cutKeys Y ⊆ Y.edgeKeys := by
    have := cutKeys_subset_edgeKeys hY.root
    rwa [edgeKeys_mapDec] at this
  have hcard : (Y.edgeKeys \ cutKeys Y).card = 1 := by
    cases Y with
    | leaf => obtain ⟨_, _, _, h⟩ := hn₁; simp [subtreeAt] at h
    | node d l r =>
      have := card_edgeKeys hY.nodup
      rw [Finset.card_sdiff_of_subset hsub]
      omega
  have hmem : ∀ (b : Bool) (q : List Bool), (∃ d l r, Y.subtreeAt (b :: q) = node d l r) →
      flagAt Y (b :: q) = false → key (Y.subtreeAt (b :: q)) ∈ Y.edgeKeys \ cutKeys Y := by
    intro b q hn hf
    rw [flagAt_eq Y _ hY.nodup hn, decide_eq_false_iff_not] at hf
    exact Finset.mem_sdiff.2 ⟨key_subtreeAt_mem_edgeKeys Y b q hn, hf⟩
  exact eq_of_key_subtreeAt Y _ _ hY.nodup hn₁ hn₂
    (Finset.card_le_one.1 hcard.le _ (hmem _ _ hn₁ hf₁) _ (hmem _ _ hn₂ hf₂))

/-- **The lower vertex of the window of a substitution is uncut.** -/
lemma plug_liftW_subtreeAt_side3 (c : Bool) {σ : LTree E} (hσs : σ.IsShuffle)
    (hσl : σ.labels.Perm (List.range 3)) (ins : ℕ → BarTree E) :
    ∃ f A B, ((liftW c σ).plug ins).subtreeAt [side3 σ] = node (f, false) A B := by
  obtain ⟨e, f, rfl | rfl | rfl⟩ := mono3_cases hσs hσl <;> exact ⟨f, _, _, rfl⟩

lemma substBar_subtreeAt_side3 {x : BarTree E} {p : List Bool} {s : Bool} (h : x.IsEdge p s)
    {σ : LTree E} (hσs : σ.IsShuffle) (hσl : σ.labels.Perm (List.range 3)) :
    ∃ f A B, (substBar x p s σ).subtreeAt (p ++ [side3 σ]) = node (f, false) A B := by
  rw [substBar, substAt, subtreeAt_append,
    subtreeAt_replaceAt _ _ _ (validPath_of_node _ _ h.exists_node)]
  exact plug_liftW_subtreeAt_side3 _ hσs hσl _

lemma subtreeAt_substBar {x : BarTree E} {p : List Bool} {s : Bool} (h : x.IsEdge p s)
    (σ : LTree E) :
    (substBar x p s σ).subtreeAt p = (liftW (flagAt x p) σ).plug ((x.subtreeAt p).winIns s) := by
  rw [substBar, substAt, subtreeAt_replaceAt _ _ _ (validPath_of_node _ _ h.exists_node)]

/-! ## The classes of the bar trees with one uncut edge -/

section Classes

variable [Fintype E] [DecidableEq E]

/-- **The substitutions at an uncut edge are distinct.** -/
theorem substBar_injective {y : BarTree E} (hy : Valid y) {p : List Bool} {s : Bool}
    (h : IsUncut y p s) {σ τ : Mono E 3} (he : substBar y p s σ.1 = substBar y p s τ.1) :
    σ = τ := by
  obtain ⟨hσs, hσl, -⟩ := mono_shape σ
  obtain ⟨hτs, hτl, -⟩ := mono_shape τ
  have hp := congrArg (·.subtreeAt p) he
  simp only [subtreeAt_substBar h.1] at hp
  have hw := winSpec_of_edge h.1 hy.shuffle hy.nodup
  have hs1 : (liftW (flagAt y p) σ.1).IsShuffle := (isShuffle_liftW _ _).2 hσs
  have hs2 : (liftW (flagAt y p) τ.1).IsShuffle := (isShuffle_liftW _ _).2 hτs
  have hl1 : (liftW (flagAt y p) σ.1).labels.Perm (List.range 3) := by simpa using hσl
  have hl2 : (liftW (flagAt y p) τ.1).labels.Perm (List.range 3) := by simpa using hτl
  have heq := (plug_inj hs1 hl1 hs2 hl2 hw.lt12 hw.lt12
    (side3_eq_of_plug_eq hs1 hl1 hs2 hl2 hp) hp).1
  apply Subtype.ext
  simpa using congrArg (·.mapDec Prod.fst) heq

omit [Fintype E] [DecidableEq E] in
/-- **A bar tree is the substitution of the window of an uncut edge.** -/
lemma substBar_windowAt {y : BarTree E} (hy : Valid y) {p : List Bool} {s : Bool}
    (h : IsUncut y p s) : substBar y p s ((y.mapDec Prod.fst).windowAt p s) = y := by
  rw [substBar, substAt, ← subtreeAt_eq_plug hy.shuffle hy.nodup h, replaceAt_subtreeAt]

lemma windowAt_mem_monomials {y : BarTree E} (hy : Valid y) {p : List Bool} {s : Bool}
    (h : IsUncut y p s) : (y.mapDec Prod.fst).windowAt p s ∈ monomials 3 := by
  obtain ⟨h1, h2, -⟩ := window_full_shape hy.shuffle hy.nodup h
  exact (mem_monomials 3 _).2 ⟨h1, h2⟩

/-- **Two bar trees with one uncut edge with a substitution in common** have their edges at the
same path and the same substitutions. -/
theorem substBar_eq_substBar {x y : BarTree E} (hx : Valid x) (hy : Valid y)
    (hc : (cutKeys y).card + 3 = y.arity) {p p' : List Bool} {s s' : Bool}
    (hux : IsUncut x p' s') (huy : IsUncut y p s) {σ₀ τ₀ : Mono E 3}
    (h : substBar x p' s' τ₀.1 = substBar y p s σ₀.1) :
    p' = p ∧ ∀ τ : Mono E 3, substBar x p' s' τ.1 = substBar y p s τ.1 := by
  obtain ⟨hσs, hσl, hσn⟩ := mono_shape σ₀
  obtain ⟨hτs, hτl, hτn⟩ := mono_shape τ₀
  have hY := hy.substBar huy σ₀
  have hcY : (cutKeys (substBar y p s σ₀.1)).card + 3 = (substBar y p s σ₀.1).arity := by
    rw [cutKeys_substBar hy.shuffle hy.nodup huy hσl hσn, ← length_labels,
      (perm_labels_substBar hy.shuffle hy.nodup huy hσl).length_eq, length_labels, hc]
  -- the uncut vertices
  obtain ⟨f₁, A₁, B₁, h₁⟩ := substBar_subtreeAt_side3 hux.1 hτs hτl
  obtain ⟨f₂, A₂, B₂, h₂⟩ := substBar_subtreeAt_side3 huy.1 hσs hσl
  rw [h] at h₁
  have hq : p' ++ [side3 τ₀.1] = p ++ [side3 σ₀.1] := by
    obtain ⟨b₁, q₁, hq₁⟩ : ∃ b q, p' ++ [side3 τ₀.1] = b :: q := by
      cases p' <;> exact ⟨_, _, rfl⟩
    obtain ⟨b₂, q₂, hq₂⟩ : ∃ b q, p ++ [side3 σ₀.1] = b :: q := by
      cases p <;> exact ⟨_, _, rfl⟩
    rw [hq₁] at h₁ ⊢
    rw [hq₂] at h₂ ⊢
    exact eq_of_flagAt_eq_false hY hcY ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩
      (by simp [flagAt, h₁, rootFlag]) (by simp [flagAt, h₂, rootFlag])
  obtain ⟨rfl, -⟩ := List.append_inj' hq rfl
  refine ⟨rfl, fun τ => ?_⟩
  -- the windows and their inputs
  have hp := congrArg (·.subtreeAt p') h
  simp only [subtreeAt_substBar hux.1, subtreeAt_substBar huy.1] at hp
  have hwx := winSpec_of_edge hux.1 hx.shuffle hx.nodup
  have hwy := winSpec_of_edge huy.1 hy.shuffle hy.nodup
  have hs1 : (liftW (flagAt x p') τ₀.1).IsShuffle := (isShuffle_liftW _ _).2 hτs
  have hs2 : (liftW (flagAt y p') σ₀.1).IsShuffle := (isShuffle_liftW _ _).2 hσs
  have hl1 : (liftW (flagAt x p') τ₀.1).labels.Perm (List.range 3) := by simpa using hτl
  have hl2 : (liftW (flagAt y p') σ₀.1).labels.Perm (List.range 3) := by simpa using hσl
  have hside : side3 (liftW (flagAt x p') τ₀.1) = side3 (liftW (flagAt y p') σ₀.1) := by
    rw [side3_liftW, side3_liftW]
    simpa using (List.append_inj' hq rfl).2
  obtain ⟨hlift, i0, i1, i2⟩ := plug_inj hs1 hl1 hs2 hl2 hwx.lt12 hwy.lt12 hside hp
  have hflag : flagAt x p' = flagAt y p' := by
    obtain ⟨e, l, r, he⟩ := hτn
    obtain ⟨e', l', r', he'⟩ := hσn
    have := congrArg rootFlag hlift
    rwa [he, he', rootFlag_liftW, rootFlag_liftW] at this
  have hplug : (liftW (flagAt x p') τ.1).plug ((x.subtreeAt p').winIns s') =
      (liftW (flagAt y p') τ.1).plug ((y.subtreeAt p').winIns s) := by
    rw [hflag]
    refine plug_congr fun a ha => ?_
    rw [labels_liftW] at ha
    have := lt_three_of_perm (mono_shape τ).2.1 a ha
    interval_cases a
    · exact i0
    · exact i1
    · exact i2
  have hctx : ∀ W : BarTree E, x.replaceAt p' W = y.replaceAt p' W := fun W => by
    have h' : x.replaceAt p' ((liftW (flagAt x p') τ₀.1).plug ((x.subtreeAt p').winIns s')) =
        y.replaceAt p' ((liftW (flagAt y p') σ₀.1).plug ((y.subtreeAt p').winIns s)) := h
    rw [← replaceAt_replaceAt x p' _ W, h', replaceAt_replaceAt]
  rw [substBar, substAt, substBar, substAt]
  exact (congrArg _ hplug).trans (hctx _)

/-- **The substitutions of two bar trees with one uncut edge either never meet or meet exactly
at the same monomial.** -/
theorem substBar_eq_iff {x y : BarTree E} (hx : Valid x) (hy : Valid y)
    (hc : (cutKeys y).card + 3 = y.arity) {p p' : List Bool} {s s' : Bool}
    (hux : IsUncut x p' s') (huy : IsUncut y p s) {σ₀ τ₀ : Mono E 3}
    (h : substBar x p' s' τ₀.1 = substBar y p s σ₀.1) (σ τ : Mono E 3) :
    substBar x p' s' τ.1 = substBar y p s σ.1 ↔ τ = σ := by
  rw [(substBar_eq_substBar hx hy hc hux huy h).2 τ]
  exact ⟨substBar_injective hy huy, fun h' => h' ▸ rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- **A bar tree with one uncut edge has an uncut edge.** -/
lemma exists_isUncut {y : BarTree E} (hy : Valid y) (hc : (cutKeys y).card + 3 = y.arity) :
    ∃ p s, IsUncut y p s := by
  have hsub : cutKeys y ⊆ y.edgeKeys := by
    have := cutKeys_subset_edgeKeys hy.root
    rwa [edgeKeys_mapDec] at this
  obtain ⟨k, hk⟩ : (y.edgeKeys \ cutKeys y).Nonempty := by
    rw [← Finset.card_pos]
    cases y with
    | leaf => simp [arity] at hc
    | node d l r =>
      have := card_edgeKeys hy.nodup
      rw [Finset.card_sdiff_of_subset hsub]
      omega
  rw [Finset.mem_sdiff] at hk
  obtain ⟨p, s, he, hkey⟩ := exists_isEdge_of_mem_edgeKeys y hk.1
  refine ⟨p, s, he, ?_⟩
  rw [flagAt_eq y _ hy.nodup he.exists_node_child, hkey]
  exact decide_eq_false hk.2

omit [Fintype E] [DecidableEq E] in
lemma card_add_three_of_adm {n : ℕ} {y : BarTree E} (hy : Adm n (n - 2) y) :
    (cutKeys y).card + 3 = y.arity := by
  have h1 := hy.2.2
  have h2 : y.arity = n := by rw [← length_labels, hy.2.1.length_eq, List.length_range]
  omega

end Classes

/-! ## The relator subcomplex in degree `n - 2` -/

section Top

variable [Fintype E] [DecidableEq E] (K : Type u) [Field K]

/-- **The coefficients of a chain on the substitutions at an edge**, a function on the monomials
of arity three. -/
noncomputable def winCoef (y : BarTree E) (p : List Bool) (s : Bool) :
    (BarTree E →₀ K) →ₗ[K] (Mono E 3 → K) where
  toFun z σ := z (substBar y p s σ.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma winCoef_apply (y : BarTree E) (p : List Bool) (s : Bool) (z : BarTree E →₀ K)
    (σ : Mono E 3) : winCoef K y p s z σ = z (substBar y p s σ.1) := rfl

lemma substRel_apply (x : BarTree E) (p : List Bool) (s : Bool) (r : Mono E 3 → K)
    (b : BarTree E) :
    substRel K x p s r b = ∑ τ, r τ * if substBar x p s τ.1 = b then 1 else 0 := by
  simp [substRel, Finsupp.finsetSum_apply, Finsupp.single_apply]

lemma substRel_apply_substBar {y : BarTree E} (hy : Valid y) {p : List Bool} {s : Bool}
    (h : IsUncut y p s) (r : Mono E 3 → K) (σ : Mono E 3) :
    substRel K y p s r (substBar y p s σ.1) = r σ := by
  rw [substRel_apply, Finset.sum_eq_single σ]
  · simp
  · intro τ _ hτ
    rw [if_neg fun h' => hτ (substBar_injective hy h h'), mul_zero]
  · simp

lemma substRel_apply_of_forall_ne {y : BarTree E} {p : List Bool} {s : Bool} (r : Mono E 3 → K)
    {b : BarTree E} (hb : ∀ σ : Mono E 3, substBar y p s σ.1 ≠ b) : substRel K y p s r b = 0 := by
  rw [substRel_apply]
  exact Finset.sum_eq_zero fun τ _ => by rw [if_neg (hb τ), mul_zero]

/-- **At an edge, a substituted relator has coefficients that relator or zero.** -/
lemma winCoef_substRel {x y : BarTree E} (hx : Valid x) (hy : Valid y)
    (hc : (cutKeys y).card + 3 = y.arity) {p p' : List Bool} {s s' : Bool}
    (hux : IsUncut x p' s') (huy : IsUncut y p s) (r : Mono E 3 → K) :
    winCoef K y p s (substRel K x p' s' r) = r ∨ winCoef K y p s (substRel K x p' s' r) = 0 := by
  by_cases hm : ∃ σ₀ τ₀ : Mono E 3, substBar x p' s' τ₀.1 = substBar y p s σ₀.1
  · obtain ⟨σ₀, τ₀, h⟩ := hm
    refine Or.inl (funext fun σ => ?_)
    rw [winCoef_apply, substRel_apply, Finset.sum_eq_single σ]
    · rw [if_pos ((substBar_eq_iff hx hy hc hux huy h σ σ).2 rfl), mul_one]
    · intro τ _ hτ
      rw [if_neg fun h' => hτ ((substBar_eq_iff hx hy hc hux huy h σ τ).1 h'), mul_zero]
    · simp
  · push Not at hm
    refine Or.inr (funext fun σ => ?_)
    rw [winCoef_apply, substRel_apply_of_forall_ne K r fun τ => hm σ τ]
    rfl

variable {K}

/-- The coefficients of a chain of the relator subcomplex at an edge form a relator. -/
theorem winCoef_mem_of_mem_J {R : Submodule K (Mono E 3 → K)} {n : ℕ} {z : BarTree E →₀ K}
    (hzJ : z ∈ J K R) (hz : z ∈ C K n (n - 2)) {y : BarTree E} (hy : Adm n (n - 2) y)
    {p : List Bool} {s : Bool} (h : IsUncut y p s) : winCoef K y p s z ∈ R := by
  have hzg := J_inf_C_le R n (n - 2) ⟨hzJ, hz⟩
  clear hzJ hz
  induction hzg using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, p', s', r, hx, hux, hr, rfl⟩ := hv
    rcases winCoef_substRel K hx.1 hy.1 (card_add_three_of_adm hy) hux h r with h' | h'
    · rw [h']
      exact hr
    · rw [h']
      exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add v w _ _ hv hw => rw [map_add]; exact add_mem hv hw
  | smul c v _ hv => rw [map_smul]; exact Submodule.smul_mem _ c hv

theorem mem_J_of_winCoef {R : Submodule K (Mono E 3 → K)} {n : ℕ} :
    ∀ (N : ℕ) (z : BarTree E →₀ K), z.support.card ≤ N → z ∈ C K n (n - 2) →
      (∀ y p s, Adm n (n - 2) y → IsUncut y p s → winCoef K y p s z ∈ R) → z ∈ J K R
  | 0, z, hN, _, _ => by
    rw [Finsupp.card_support_eq_zero.1 (Nat.le_zero.1 hN)]
    exact zero_mem _
  | N + 1, z, hN, hz, hw => by
    by_cases h0 : z = 0
    · rw [h0]
      exact zero_mem _
    obtain ⟨y, hy⟩ := Finsupp.support_nonempty_iff.2 h0
    have hyA : Adm n (n - 2) y := hz hy
    obtain ⟨p, s, hu⟩ := exists_isUncut hyA.1 (card_add_three_of_adm hyA)
    set z₁ := substRel K y p s (winCoef K y p s z) with hz₁
    have hz₁J : z₁ ∈ J K R :=
      Submodule.subset_span ⟨y, p, s, _, hyA.1, hu, hw y p s hyA hu, rfl⟩
    have hz₁C : z₁ ∈ C K n (n - 2) := substRel_mem_C hyA hu _
    have hsupp : (z - z₁).support ⊆ z.support.erase y := by
      intro b hb
      rw [Finsupp.mem_support_iff, Finsupp.sub_apply] at hb
      by_cases hm : ∃ σ : Mono E 3, substBar y p s σ.1 = b
      · obtain ⟨σ, rfl⟩ := hm
        rw [hz₁, substRel_apply_substBar K hyA.1 hu, winCoef_apply, sub_self] at hb
        exact absurd rfl hb
      · push Not at hm
        rw [hz₁, substRel_apply_of_forall_ne K _ hm, sub_zero] at hb
        refine Finset.mem_erase.2 ⟨fun hby => ?_, Finsupp.mem_support_iff.2 hb⟩
        refine hm ⟨_, windowAt_mem_monomials hyA.1 hu⟩ ?_
        rw [hby]
        exact substBar_windowAt hyA.1 hu
    have hcard : (z - z₁).support.card ≤ N := by
      have := Finset.card_le_card hsupp
      rw [Finset.card_erase_of_mem hy] at this
      omega
    have hrec : z - z₁ ∈ J K R := by
      refine mem_J_of_winCoef N (z - z₁) hcard (sub_mem hz hz₁C) fun y' p' s' hy' hu' => ?_
      rw [map_sub]
      exact sub_mem (hw y' p' s' hy' hu') (winCoef_mem_of_mem_J hz₁J hz₁C hy' hu')
    rw [← sub_add_cancel z z₁]
    exact add_mem hrec hz₁J

/-- **The relator subcomplex in degree `n - 2`**: a chain lies in it exactly when, at every bar
tree with one uncut edge, its coefficients on the substitutions at that edge form a relator. -/
theorem mem_J_iff_winCoef {R : Submodule K (Mono E 3 → K)} {n : ℕ} {z : BarTree E →₀ K}
    (hz : z ∈ C K n (n - 2)) :
    z ∈ J K R ↔ ∀ y p s, Adm n (n - 2) y → IsUncut y p s → winCoef K y p s z ∈ R :=
  ⟨fun hzJ _ _ _ hy h => winCoef_mem_of_mem_J hzJ hz hy h,
    mem_J_of_winCoef _ z le_rfl hz⟩

end Top

end ShuffleBar

end Operad
