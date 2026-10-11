/-
# The vertices of a shuffle monomial, and the signs of the fully cut bar trees

Every vertex of a shuffle monomial has a *key*, its least label and its number of leaves, and a
*right label*, the least label of its second input (`LTree.vlist`, the list of these pairs in
preorder). On a shuffle monomial with distinct labels both tell the vertices apart
(`LTree.nodup_map_vkey`, `LTree.nodup_map_vrl`).

* Replacing the subtree at a path by one with the same labels keeps the pairs of the other
  vertices (`LTree.vlist_replaceAt`): they form the *context* (`LTree.ctxL`).
* **The arity-three monomials** are `e(f(0, 1), 2)`, `e(f(0, 2), 1)` and `e(0, f(1, 2))`
  (`LTree.mono3_cases`); `side3` is the side of their edge and `chi3` the sign `+1, -1, -1`.
* **The orientation sign** of a monomial (`LTree.tauS`) is the sign of the list of its right
  labels, the root first and the other vertices in the order of their keys. In the bar differential
  of a fully cut bar tree, the edge of key `k` has the sign `topSgn`, `-1` to the number of edges
  of smaller key.
* **Coherence of the signs** (`LTree.topSgn_mul_tauS_substAt`): substituting the monomials `σ` of
  arity three at an edge of a monomial, the sign of the new edge times the orientation sign is
  `c · chi3 σ`, with `c = ±1` depending only on the edge. This is what makes the fully cut bar
  trees, oriented by `tauS`, dual to the monomials of the Koszul dual operad, whose relators are
  orthogonal to those of the operad for the pairing twisted by `chi3`.
-/
import Operad.ShuffleBar
import Operad.ListInv

universe v

namespace Operad

namespace LTree

variable {E : Type v}

/-- The pair of a vertex: its key and its right label. -/
abbrev VD := (ℕ ×ₗ ℕ) ×ₗ ℕ

/-- The key of a pair. -/
def vkey (x : VD) : ℕ ×ₗ ℕ := (ofLex x).1

/-- The right label of a pair. -/
def vrl (x : VD) : ℕ := (ofLex x).2

/-- The pair of a vertex. -/
def vpair (e : E) (l r : LTree E) : VD := toLex (key (node e l r), r.minLabel)

@[simp] lemma vkey_vpair (e : E) (l r : LTree E) : vkey (vpair e l r) = key (node e l r) := rfl

@[simp] lemma vrl_vpair (e : E) (l r : LTree E) : vrl (vpair e l r) = r.minLabel := rfl

@[simp] lemma vkey_toLex (k : ℕ ×ₗ ℕ) (a : ℕ) : vkey (toLex (k, a)) = k := rfl

@[simp] lemma vrl_toLex (k : ℕ ×ₗ ℕ) (a : ℕ) : vrl (toLex (k, a)) = a := rfl

/-- **The pairs of the vertices**, key and right label, in preorder. -/
def vlist : LTree E → List VD
  | leaf _ => []
  | node e l r => vpair e l r :: (vlist l ++ vlist r)

@[simp] lemma vlist_leaf (a : ℕ) : vlist (leaf a : LTree E) = [] := rfl

@[simp] lemma vlist_node (e : E) (l r : LTree E) :
    vlist (node e l r) = vpair e l r :: (vlist l ++ vlist r) := rfl

/-- The keys of the pairs are the keys of the vertices. -/
lemma map_vkey_vlist : ∀ t : LTree E, (vlist t).map vkey = t.keyList
  | leaf _ => rfl
  | node e l r => by
    simp only [vlist_node, List.map_cons, List.map_append, map_vkey_vlist l, map_vkey_vlist r,
      vkey_vpair, keyList]

/-- **The keys tell the vertices apart**, on a monomial with distinct labels. -/
lemma nodup_map_vkey {t : LTree E} (hnd : t.labels.Nodup) : ((vlist t).map vkey).Nodup := by
  rw [map_vkey_vlist]
  exact nodup_keyList t hnd

lemma nodup_vlist {t : LTree E} (hnd : t.labels.Nodup) : (vlist t).Nodup :=
  (nodup_map_vkey hnd).of_map _

/-- **The right labels are labels above the least one**, on a shuffle monomial. -/
lemma rl_mem_of_vlist : ∀ {t : LTree E}, t.IsShuffle → ∀ {x : VD}, x ∈ vlist t →
    vrl x ∈ t.labels ∧ t.minLabel < vrl x
  | leaf _, _, x, hx => by simp at hx
  | node e l r, hs, x, hx => by
    obtain ⟨hlr, hl, hr⟩ := hs
    rw [vlist_node, List.mem_cons, List.mem_append] at hx
    simp only [labels_node, List.mem_append, minLabel_node, min_eq_left hlr.le]
    rcases hx with rfl | hx | hx
    · exact ⟨Or.inr (minLabel_mem r), hlr⟩
    · obtain ⟨h1, h2⟩ := rl_mem_of_vlist hl hx
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := rl_mem_of_vlist hr hx
      exact ⟨Or.inr h1, hlr.trans h2⟩

/-- **The right labels tell the vertices apart**, on a shuffle monomial with distinct labels. -/
lemma nodup_map_vrl : ∀ {t : LTree E}, t.IsShuffle → t.labels.Nodup → ((vlist t).map vrl).Nodup
  | leaf _, _, _ => by simp
  | node e l r, hs, hnd => by
    obtain ⟨hlr, hls, hrs⟩ := hs
    have hnd' : (l.labels ++ r.labels).Nodup := by simpa using hnd
    have hl : l.labels.Nodup := (List.nodup_append.1 hnd').1
    have hr : r.labels.Nodup := (List.nodup_append.1 hnd').2.1
    have hdis : ∀ a ∈ l.labels, ∀ b ∈ r.labels, a ≠ b := fun a ha b hb =>
      ne_of_nodup_append hnd' ha hb
    rw [vlist_node, List.map_cons, List.map_append, List.nodup_cons, List.nodup_append]
    refine ⟨?_, nodup_map_vrl hls hl, nodup_map_vrl hrs hr, ?_⟩
    · simp only [vrl_vpair, List.mem_append, List.mem_map, not_or, not_exists, not_and]
      exact ⟨fun x hx h => hdis _ (rl_mem_of_vlist hls hx).1 _ (minLabel_mem r) h,
        fun x hx h => (ne_of_lt (rl_mem_of_vlist hrs hx).2) h.symm⟩
    · simp only [List.mem_map]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
      exact hdis _ (rl_mem_of_vlist hls hx).1 _ (rl_mem_of_vlist hrs hy).1 h

/-! ## Replacing a subtree -/

/-- **A path to a vertex or a leaf**, never past a leaf. -/
def ValidPath : LTree E → List Bool → Prop
  | leaf _, [] => True
  | leaf _, _ :: _ => False
  | node _ _ _, [] => True
  | node _ l _, false :: p => ValidPath l p
  | node _ _ r, true :: p => ValidPath r p

@[simp] lemma validPath_nil (t : LTree E) : ValidPath t [] := by cases t <;> trivial

lemma validPath_of_node : ∀ (t : LTree E) (p : List Bool), (∃ e l r, t.subtreeAt p = node e l r) →
    ValidPath t p
  | t, [], _ => validPath_nil t
  | leaf _, _ :: _, ⟨_, _, _, h⟩ => by simp [subtreeAt] at h
  | node _ l _, false :: p, h => validPath_of_node l p h
  | node _ _ r, true :: p, h => validPath_of_node r p h

/-- **The pairs of the vertices outside the subtree at a path.** -/
def ctxL : LTree E → List Bool → List VD
  | leaf _, _ => []
  | node _ _ _, [] => []
  | node e l r, false :: p => vpair e l r :: (ctxL l p ++ vlist r)
  | node e l r, true :: p => vpair e l r :: (vlist l ++ ctxL r p)

lemma subtreeAt_replaceAt : ∀ (t : LTree E) (p : List Bool) (u : LTree E), ValidPath t p →
    (t.replaceAt p u).subtreeAt p = u
  | t, [], u, _ => by simp only [replaceAt_nil, subtreeAt_nil]
  | leaf _, _ :: _, _, h => h.elim
  | node _ l _, false :: p, u, h => subtreeAt_replaceAt l p u h
  | node _ _ r, true :: p, u, h => subtreeAt_replaceAt r p u h

lemma replaceAt_replaceAt : ∀ (t : LTree E) (p : List Bool) (u w : LTree E),
    (t.replaceAt p u).replaceAt p w = t.replaceAt p w
  | t, [], u, w => by simp only [replaceAt_nil]
  | leaf _, _ :: _, _, _ => rfl
  | node e l r, false :: p, u, w => by simp [replaceAt, replaceAt_replaceAt l p u w]
  | node e l r, true :: p, u, w => by simp [replaceAt, replaceAt_replaceAt r p u w]

lemma validPath_replaceAt : ∀ (t : LTree E) (p : List Bool) (u : LTree E), ValidPath t p →
    ValidPath (t.replaceAt p u) p
  | _, [], _, _ => validPath_nil _
  | leaf _, _ :: _, _, h => h.elim
  | node _ l _, false :: p, u, h => validPath_replaceAt l p u h
  | node _ _ r, true :: p, u, h => validPath_replaceAt r p u h

lemma labels_replaceAt_perm' : ∀ (t : LTree E) (p : List Bool) (u : LTree E), ValidPath t p →
    u.labels.Perm (t.subtreeAt p).labels → (t.replaceAt p u).labels.Perm t.labels
  | t, [], u, _, h => by cases t <;> simpa [replaceAt] using h
  | leaf _, _ :: _, _, h, _ => h.elim
  | node e l r, false :: p, u, h, hu => by
    simp only [replaceAt, labels_node]
    exact (labels_replaceAt_perm' l p u h hu).append_right _
  | node e l r, true :: p, u, h, hu => by
    simp only [replaceAt, labels_node]
    exact (labels_replaceAt_perm' r p u h hu).append_left _

/-- **Replacing the subtree at a path** by one with the same labels keeps the other pairs. -/
lemma vlist_replaceAt : ∀ (t : LTree E) (p : List Bool) (u : LTree E), ValidPath t p →
    u.labels.Perm (t.subtreeAt p).labels → (vlist (t.replaceAt p u)).Perm (ctxL t p ++ vlist u)
  | t, [], u, _, _ => by cases t <;> simp [ctxL]
  | leaf _, _ :: _, _, h, _ => h.elim
  | node e l r, false :: p, u, h, hu => by
    have hp := labels_replaceAt_perm' l p u h hu
    have ha : (l.replaceAt p u).arity = l.arity := by
      rw [← length_labels, ← length_labels, hp.length_eq]
    have hk : vpair e (l.replaceAt p u) r = vpair e l r := by
      rw [vpair, vpair, key_node, key_node, minLabel_eq_of_perm hp, ha]
    simp only [replaceAt, vlist_node, hk, ctxL, List.cons_append, List.perm_cons]
    refine ((vlist_replaceAt l p u h hu).append_right _).trans ?_
    simp only [List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  | node e l r, true :: p, u, h, hu => by
    have hp := labels_replaceAt_perm' r p u h hu
    have ha : (r.replaceAt p u).arity = r.arity := by
      rw [← length_labels, ← length_labels, hp.length_eq]
    have hk : vpair e l (r.replaceAt p u) = vpair e l r := by
      rw [vpair, vpair, key_node, key_node, minLabel_eq_of_perm hp, ha]
    simp only [replaceAt, vlist_node, hk, ctxL, List.cons_append, List.perm_cons,
      List.append_assoc]
    exact (vlist_replaceAt r p u h hu).append_left _

/-! ## The monomials of arity three -/

/-- The side of the edge of a monomial of arity three. -/
def side3 : LTree E → Bool
  | node _ (node _ _ _) _ => false
  | _ => true

/-- **The sign of a monomial of arity three**: `+1` for `e(f(0, 1), 2)`, `-1` otherwise. -/
def chi3 : LTree E → ℤ
  | node _ (node _ (leaf 0) (leaf 1)) (leaf 2) => 1
  | _ => -1

lemma chi3_sq (σ : LTree E) : chi3 σ * chi3 σ = 1 := by
  unfold chi3
  split <;> norm_num

lemma eq_leaf_of_arity_one : ∀ {t : LTree E}, t.arity = 1 → ∃ a, t = leaf a
  | leaf a, _ => ⟨a, rfl⟩
  | node _ l r, h => by
    have := arity_pos l
    have := arity_pos r
    simp only [arity] at h
    omega

lemma eq_node_of_arity_two : ∀ {t : LTree E}, t.arity = 2 → ∃ f a b, t = node f (leaf a) (leaf b)
  | leaf _, h => by simp [arity] at h
  | node f l r, h => by
    have := arity_pos l
    have := arity_pos r
    simp only [arity] at h
    obtain ⟨a, rfl⟩ := eq_leaf_of_arity_one (show l.arity = 1 by omega)
    obtain ⟨b, rfl⟩ := eq_leaf_of_arity_one (show r.arity = 1 by omega)
    exact ⟨f, a, b, rfl⟩

/-- **The three shapes of the monomials of arity three.** -/
lemma mono3_cases {σ : LTree E} (hs : σ.IsShuffle) (hl : σ.labels.Perm (List.range 3)) :
    ∃ e f, σ = node e (node f (leaf 0) (leaf 1)) (leaf 2) ∨
      σ = node e (node f (leaf 0) (leaf 2)) (leaf 1) ∨
      σ = node e (leaf 0) (node f (leaf 1) (leaf 2)) := by
  have harity : σ.arity = 3 := by rw [← length_labels, hl.length_eq]; rfl
  have hnd : σ.labels.Nodup := hl.nodup_iff.2 List.nodup_range
  have h3 : ∀ a < 3, a ∈ σ.labels := fun a ha => hl.symm.subset (List.mem_range.2 ha)
  have hmem : ∀ a ∈ σ.labels, a < 3 := fun a ha => List.mem_range.1 (hl.subset ha)
  match σ, hs, harity, hnd, h3, hmem with
  | leaf a, _, harity, _, _, _ => simp [arity] at harity
  | node e l r, hs, harity, hnd, h3, hmem =>
    have := arity_pos l
    have := arity_pos r
    simp only [arity] at harity
    rcases (show (l.arity = 1 ∧ r.arity = 2) ∨ (l.arity = 2 ∧ r.arity = 1) by omega) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨a, rfl⟩ := eq_leaf_of_arity_one h1
      obtain ⟨f, b, c, rfl⟩ := eq_node_of_arity_two h2
      obtain ⟨hab, -, hbc, -, -⟩ := hs
      simp only [minLabel_node, minLabel_leaf] at hab hbc
      simp only [labels_node, labels_leaf, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hmem h3
      have e0 := h3 0 (by norm_num)
      have e1 := h3 1 (by norm_num)
      have e2 := h3 2 (by norm_num)
      have hmin := min_le_left b c
      have hmin' := min_le_right b c
      obtain ⟨rfl, rfl, rfl⟩ : a = 0 ∧ b = 1 ∧ c = 2 := by omega
      exact ⟨e, f, Or.inr (Or.inr rfl)⟩
    · obtain ⟨f, a, b, rfl⟩ := eq_node_of_arity_two h1
      obtain ⟨c, rfl⟩ := eq_leaf_of_arity_one h2
      obtain ⟨hac, ⟨hab, -, -⟩, -⟩ := hs
      simp only [minLabel_node, minLabel_leaf] at hac hab
      have hbc : b ≠ c := by
        simp only [labels_node, labels_leaf, List.cons_append, List.nil_append] at hnd
        simp at hnd
        omega
      simp only [labels_node, labels_leaf, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hmem h3
      have e0 := h3 0 (by norm_num)
      have e1 := h3 1 (by norm_num)
      have e2 := h3 2 (by norm_num)
      have hmin := min_le_left a b
      rw [min_eq_left hab.le] at hac
      rcases (show (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 0 ∧ b = 2 ∧ c = 1) by omega) with
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact ⟨e, f, Or.inl rfl⟩
      · exact ⟨e, f, Or.inr (Or.inl rfl)⟩

/-! ## The orientation sign -/

section Signs

open ListInv

/-- The right labels of a set of pairs, in the order of the pairs. -/
noncomputable def rlList (S : Finset VD) : List ℕ := (S.sort (· ≤ ·)).map vrl

lemma sort_insert_split {S : Finset VD} {x : VD} (hx : x ∉ S) :
    (insert x S).sort (· ≤ ·) =
      (S.filter (· < x)).sort (· ≤ ·) ++ x :: (S.filter (x < ·)).sort (· ≤ ·) := by
  set L := (S.filter (· < x)).sort (· ≤ ·) ++ x :: (S.filter (x < ·)).sort (· ≤ ·) with hL
  have hnd : L.Nodup := by
    rw [hL, List.nodup_append, List.nodup_cons]
    refine ⟨Finset.sort_nodup _ _, ⟨by simp, Finset.sort_nodup _ _⟩, ?_⟩
    intro a ha b hb hab
    subst hab
    simp only [Finset.mem_sort, Finset.mem_filter, List.mem_cons] at ha hb
    rcases hb with rfl | hb
    · exact lt_irrefl _ ha.2
    · exact lt_asymm ha.2 hb.2
  have hfin : L.toFinset = insert x S := by
    ext y
    simp only [hL, List.mem_toFinset, List.mem_append, Finset.mem_sort, Finset.mem_filter,
      List.mem_cons, Finset.mem_insert]
    constructor
    · rintro (⟨h, -⟩ | rfl | ⟨h, -⟩)
      · exact Or.inr h
      · exact Or.inl rfl
      · exact Or.inr h
    · rintro (rfl | h)
      · exact Or.inr (Or.inl rfl)
      · rcases lt_trichotomy y x with hyx | rfl | hxy
        · exact Or.inl ⟨h, hyx⟩
        · exact absurd h hx
        · exact Or.inr (Or.inr ⟨h, hxy⟩)
  have hpw : L.Pairwise (· ≤ ·) := by
    rw [hL, List.pairwise_append, List.pairwise_cons]
    refine ⟨Finset.pairwise_sort _ _, ⟨fun b hb => ?_, Finset.pairwise_sort _ _⟩,
      fun a ha b hb => ?_⟩
    · simp only [Finset.mem_sort, Finset.mem_filter] at hb
      exact hb.2.le
    · simp only [Finset.mem_sort, Finset.mem_filter, List.mem_cons] at ha hb
      rcases hb with rfl | hb
      · exact ha.2.le
      · exact (ha.2.trans hb.2).le
  rw [← hfin]
  exact (List.toFinset_sort (· ≤ ·) hnd).2 hpw

lemma sort_split {S : Finset VD} {x : VD} (hx : x ∉ S) :
    S.sort (· ≤ ·) = (S.filter (· < x)).sort (· ≤ ·) ++ (S.filter (x < ·)).sort (· ≤ ·) := by
  set L := (S.filter (· < x)).sort (· ≤ ·) ++ (S.filter (x < ·)).sort (· ≤ ·) with hL
  have hnd : L.Nodup := by
    rw [hL, List.nodup_append]
    refine ⟨Finset.sort_nodup _ _, Finset.sort_nodup _ _, ?_⟩
    intro a ha b hb hab
    subst hab
    simp only [Finset.mem_sort, Finset.mem_filter] at ha hb
    exact lt_asymm ha.2 hb.2
  have hfin : L.toFinset = S := by
    ext y
    simp only [hL, List.mem_toFinset, List.mem_append, Finset.mem_sort, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases lt_trichotomy y x with hyx | rfl | hxy
      · exact Or.inl ⟨h, hyx⟩
      · exact absurd h hx
      · exact Or.inr ⟨h, hxy⟩
  have hpw : L.Pairwise (· ≤ ·) := by
    rw [hL, List.pairwise_append]
    refine ⟨Finset.pairwise_sort _ _, Finset.pairwise_sort _ _, fun a ha b hb => ?_⟩
    simp only [Finset.mem_sort, Finset.mem_filter] at ha hb
    exact (ha.2.trans hb.2).le
  rw [← hfin]
  exact (List.toFinset_sort (· ≤ ·) hnd).2 hpw

/-- **Moving a pair to the front**, past the pairs before it. -/
lemma sgn_rlList_insert (r0 : ℕ) {S : Finset VD} {x : VD} (hx : x ∉ S)
    (hrl : ∀ y ∈ S, vrl y ≠ vrl x) :
    sgn (r0 :: rlList (insert x S)) =
      (-1) ^ (S.filter (· < x)).card * sgn (r0 :: vrl x :: rlList S) := by
  have h1 : rlList (insert x S) =
      rlList (S.filter (· < x)) ++ vrl x :: rlList (S.filter (x < ·)) := by
    simp [rlList, sort_insert_split hx]
  have h2 : rlList S = rlList (S.filter (· < x)) ++ rlList (S.filter (x < ·)) := by
    simp [rlList, sort_split hx]
  have hnot : vrl x ∉ rlList (S.filter (· < x)) := by
    simp only [rlList, List.mem_map, Finset.mem_sort, Finset.mem_filter, not_exists, not_and]
    exact fun y hy h => hrl y hy.1 h
  have hlen : (rlList (S.filter (· < x))).length = (S.filter (· < x)).card := by
    simp [rlList]
  have hc : (rlList (S.filter (· < x)) ++ vrl x :: rlList (S.filter (x < ·))).countP (· < r0) =
      (vrl x :: (rlList (S.filter (· < x)) ++ rlList (S.filter (x < ·)))).countP (· < r0) :=
    List.Perm.countP_eq _ List.perm_middle
  rw [h1, sgn_cons, sgn_move hnot, hc, sgn_cons r0 (vrl x :: _), h2, hlen]
  ring

lemma lt_iff_vkey {x y : VD} (h : vkey y ≠ vkey x) : y < x ↔ vkey y < vkey x := by
  obtain ⟨⟨ky, ay⟩, rfl⟩ := toLex.surjective y
  obtain ⟨⟨kx, ax⟩, rfl⟩ := toLex.surjective x
  simp only [vkey_toLex] at h ⊢
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (h1 | ⟨h1, -⟩)
    · exact h1
    · exact absurd h1 h
  · exact Or.inl

/-- **The orientation sign of a monomial**: the sign of its right labels, the root first and the
other vertices in the order of their keys. -/
noncomputable def tauS : LTree E → ℤ
  | leaf _ => 1
  | node _ l r => sgn (r.minLabel :: rlList (vlist l ++ vlist r).toFinset)

lemma tauS_mul_self (t : LTree E) : tauS t * tauS t = 1 := by
  cases t with
  | leaf => rfl
  | node e l r => exact sgn_mul_self _

/-- **The sign of an edge** in the bar differential of the fully cut bar tree: `-1` to the number
of edges of smaller key. -/
def topSgn (M : LTree E) (k : ℕ ×ₗ ℕ) : ℤ := (-1) ^ (M.edgeKeys.filter (· < k)).card

lemma edgeKeys_eq_vlist (e : E) (l r : LTree E) :
    (node e l r).edgeKeys = ((vlist l ++ vlist r).map vkey).toFinset := by
  rw [edgeKeys_node]
  ext k
  simp only [Finset.mem_union, List.map_append, List.mem_toFinset, List.mem_append,
    map_vkey_vlist, mem_keyList_iff]

lemma nodup_of_perm_vlist {e : E} {l r : LTree E} (hs : (node e l r).IsShuffle)
    (hnd : (node e l r).labels.Nodup) {L : List VD} (hperm : (vlist l ++ vlist r).Perm L) :
    (L.map vkey).Nodup ∧ (L.map vrl).Nodup := by
  have h1 := nodup_map_vkey hnd
  have h2 := nodup_map_vrl hs hnd
  rw [vlist_node, List.map_cons, List.nodup_cons] at h1 h2
  exact ⟨(hperm.map vkey).nodup_iff.1 h1.2, (hperm.map vrl).nodup_iff.1 h2.2⟩

/-- **The sign of an edge times the orientation sign** is the sign of the right labels with the
lower vertex of the edge moved next to the root. -/
lemma topSgn_mul_tauS (e : E) (l r : LTree E) (hs : (node e l r).IsShuffle)
    (hnd : (node e l r).labels.Nodup) {x : VD} {S : List VD}
    (hperm : (vlist l ++ vlist r).Perm (x :: S)) :
    topSgn (node e l r) (vkey x) * tauS (node e l r) =
      sgn (r.minLabel :: vrl x :: rlList S.toFinset) := by
  obtain ⟨hndk, hndr⟩ := nodup_of_perm_vlist hs hnd hperm
  rw [List.map_cons, List.nodup_cons] at hndk hndr
  have hxS : x ∉ S.toFinset := fun h =>
    hndk.1 (List.mem_map_of_mem (List.mem_toFinset.1 h))
  have hfin : (vlist l ++ vlist r).toFinset = insert x S.toFinset := by
    rw [List.toFinset_eq_of_perm _ _ hperm, List.toFinset_cons]
  have hrl : ∀ y ∈ S.toFinset, vrl y ≠ vrl x := fun y hy h =>
    hndr.1 (h ▸ List.mem_map_of_mem (List.mem_toFinset.1 hy))
  have hcount : ((node e l r).edgeKeys.filter (· < vkey x)).card =
      (S.toFinset.filter (· < x)).card := by
    have hne : ∀ y ∈ S, vkey y ≠ vkey x := fun y hy h =>
      hndk.1 (h ▸ List.mem_map_of_mem hy)
    rw [edgeKeys_eq_vlist, List.toFinset_eq_of_perm _ _ (hperm.map vkey), List.map_cons,
      List.toFinset_cons, Finset.filter_insert, if_neg (lt_irrefl _)]
    rw [← Finset.card_image_of_injOn (f := vkey) (s := S.toFinset.filter (· < x))]
    · congr 1
      ext k
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_map, Finset.mem_image]
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hk⟩
        exact ⟨y, ⟨hy, (lt_iff_vkey (hne y hy)).2 hk⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hyx⟩, rfl⟩
        exact ⟨⟨y, hy, rfl⟩, (lt_iff_vkey (hne y hy)).1 hyx⟩
    · intro a ha b hb hab
      simp only [Finset.coe_filter, List.mem_toFinset, Set.mem_setOf_eq] at ha hb
      exact (List.inj_on_of_nodup_map hndk.2) ha.1 hb.1 hab
  rw [tauS, hfin, sgn_rlList_insert _ hxS hrl, topSgn, hcount, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul]
  norm_num

/-- **Exchanging the right labels of the lower vertex and of the upper vertex** of an edge
changes the sign. -/
lemma sgn_swap_rl (r0 : ℕ) {O : List VD} {K : ℕ ×ₗ ℕ} (hK : ∀ y ∈ O, vkey y ≠ K) {β γ : ℕ}
    (hβγ : β ≠ γ) (hβ : ∀ y ∈ O, vrl y ≠ β) (hγ : ∀ y ∈ O, vrl y ≠ γ) :
    sgn (r0 :: β :: rlList (toLex (K, γ) :: O).toFinset) =
      -sgn (r0 :: γ :: rlList (toLex (K, β) :: O).toFinset) := by
  have hnotin : ∀ ρ : ℕ, toLex (K, ρ) ∉ O.toFinset := fun ρ h =>
    hK _ (List.mem_toFinset.1 h) rfl
  have hfl : ∀ ρ : ℕ, O.toFinset.filter (· < toLex (K, ρ)) = O.toFinset.filter (vkey · < K) :=
    fun ρ => Finset.filter_congr fun y hy =>
      lt_iff_vkey (by simpa using hK y (List.mem_toFinset.1 hy))
  have hfr : ∀ ρ : ℕ, O.toFinset.filter (toLex (K, ρ) < ·) = O.toFinset.filter (K < vkey ·) :=
    fun ρ => Finset.filter_congr fun y hy =>
      lt_iff_vkey (by simpa using (hK y (List.mem_toFinset.1 hy)).symm)
  have hsplit : ∀ ρ : ℕ, rlList (toLex (K, ρ) :: O).toFinset =
      rlList (O.toFinset.filter (vkey · < K)) ++ ρ :: rlList (O.toFinset.filter (K < vkey ·)) := by
    intro ρ
    rw [List.toFinset_cons, rlList, sort_insert_split (hnotin ρ), hfl ρ, hfr ρ]
    simp [rlList]
  set A := rlList (O.toFinset.filter (vkey · < K))
  set B := rlList (O.toFinset.filter (K < vkey ·))
  have hA : ∀ ρ, (ρ = β ∨ ρ = γ) → ρ ∉ A := by
    rintro ρ hρ h
    simp only [A, rlList, List.mem_map, Finset.mem_sort, Finset.mem_filter,
      List.mem_toFinset] at h
    obtain ⟨y, ⟨hy, -⟩, rfl⟩ := h
    rcases hρ with h | h
    · exact hβ y hy h
    · exact hγ y hy h
  rw [hsplit, hsplit, sgn_cons, sgn_cons r0, sgn_swap hβγ (hA γ (Or.inr rfl)) (hA β (Or.inl rfl))]
  have hc : (β :: (A ++ γ :: B)).countP (· < r0) = (γ :: (A ++ β :: B)).countP (· < r0) := by
    exact List.Perm.countP_eq _ ((List.perm_middle.cons β).trans
      ((List.Perm.swap γ β _).trans (List.perm_middle.symm.cons γ)))
  rw [hc]
  ring

end Signs

/-- Two lists with the same counts are permutations of each other. -/
macro (name := permByCount) "perm_by_count" : tactic => `(tactic| (
    rw [List.perm_iff_count]
    intro _
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega))

section Coherence

open ListInv

@[simp] lemma chi3_a (e f : E) : chi3 (node e (node f (leaf 0) (leaf 1)) (leaf 2)) = 1 := rfl

@[simp] lemma chi3_b (e f : E) : chi3 (node e (node f (leaf 0) (leaf 2)) (leaf 1)) = -1 := rfl

@[simp] lemma chi3_c (e f : E) : chi3 (node e (leaf 0) (node f (leaf 1) (leaf 2))) = -1 := rfl

lemma chi3_cases (σ : LTree E) : chi3 σ = 1 ∨ chi3 σ = -1 := by
  unfold chi3
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The data of a monomial of arity three with its inputs plugged**: the root, its two inputs,
the pair `x` of the lower vertex of the edge; the right labels of `x` and of the root are those
of the second and third inputs for `e(f(0, 1), 2)` and the other way round otherwise. -/
lemma shape_data {σ : LTree E} (hσs : σ.IsShuffle) (hσl : σ.labels.Perm (List.range 3))
    (ins : ℕ → LTree E) (hlt : (ins 1).minLabel < (ins 2).minLabel) :
    ∃ e X Y x, σ.plug ins = node e X Y ∧
      (vlist X ++ vlist Y).Perm (x :: (vlist (ins 0) ++ vlist (ins 1) ++ vlist (ins 2))) ∧
      vkey x = key ((σ.plug ins).subtreeAt [side3 σ]) ∧
      (chi3 σ = 1 → vrl x = (ins 1).minLabel ∧ Y.minLabel = (ins 2).minLabel) ∧
      (chi3 σ = -1 → vrl x = (ins 2).minLabel ∧ Y.minLabel = (ins 1).minLabel) := by
  obtain ⟨e, f, rfl | rfl | rfl⟩ := mono3_cases hσs hσl
  · refine ⟨e, node f (ins 0) (ins 1), ins 2, vpair f (ins 0) (ins 1), rfl, ?_, rfl,
      fun _ => ⟨rfl, rfl⟩, fun h => by simp at h⟩
    simp only [vlist_node, List.cons_append, List.append_assoc, List.Perm.refl]
  · refine ⟨e, node f (ins 0) (ins 2), ins 1, vpair f (ins 0) (ins 2), rfl, ?_, rfl,
      fun h => by simp at h, fun _ => ⟨rfl, rfl⟩⟩
    simp only [vlist_node, List.cons_append, List.append_assoc]
    perm_by_count
  · refine ⟨e, ins 0, node f (ins 1) (ins 2), vpair f (ins 1) (ins 2), rfl, ?_, rfl,
      fun h => by simp at h, fun _ => ⟨rfl, ?_⟩⟩
    · simp only [vlist_node]
      perm_by_count
    · simp only [minLabel_node]
      exact min_eq_left hlt.le

/-- **The coherence of the signs of the bar construction**: on the monomials obtained from `t` by
substituting the monomials of arity three at an edge, the sign of the new edge in the bar
differential of the fully cut bar tree, times the orientation sign, is the sign `chi3` of the
substituted monomial, up to a factor depending only on the edge. -/
theorem topSgn_mul_tauS_substAt {t : LTree E} (hs : t.IsShuffle) (hnd : t.labels.Nodup)
    {p : List Bool} {s : Bool} (he : t.IsEdge p s) :
    ∃ c : ℤ, c * c = 1 ∧ ∀ σ : LTree E, σ.IsShuffle → σ.labels.Perm (List.range 3) →
      topSgn (t.substAt p s σ) (key ((t.substAt p s σ).subtreeAt (p ++ [side3 σ]))) *
        tauS (t.substAt p s σ) = c * chi3 σ := by
  have hw := winSpec_of_edge he hs hnd
  have hvp : ValidPath t p := validPath_of_node t p he.exists_node
  set u := t.subtreeAt p with hu
  set A := u.winIns s 0 with hA
  set B := u.winIns s 1 with hB
  set C := u.winIns s 2 with hC
  have hβγ : B.minLabel < C.minLabel := hw.lt12
  have hWp : ∀ σ : LTree E, σ.labels.Perm (List.range 3) →
      (σ.plug (u.winIns s)).labels.Perm u.labels := fun σ h2 =>
    perm_labels_plug_winIns he hs hnd h2
  have htn : ∀ σ : LTree E, σ.labels.Perm (List.range 3) → (t.substAt p s σ).labels.Nodup :=
    fun σ h2 => (perm_labels_substAt he hs hnd h2).nodup_iff.2 hnd
  have hts : ∀ σ : LTree E, σ.IsShuffle → σ.labels.Perm (List.range 3) →
      (t.substAt p s σ).IsShuffle := fun σ h1 h2 => isShuffle_substAt he hs hnd h1 h2
  have hchild : ∀ σ : LTree E, (t.substAt p s σ).subtreeAt (p ++ [side3 σ]) =
      (σ.plug (u.winIns s)).subtreeAt [side3 σ] := fun σ => by
    rw [substAt, subtreeAt_append, subtreeAt_replaceAt _ _ _ hvp]
  rcases p with _ | ⟨b, p'⟩
  · -- the edge at the root
    refine ⟨sgn (C.minLabel :: B.minLabel :: rlList (vlist A ++ vlist B ++ vlist C).toFinset),
      sgn_mul_self _, fun σ hσs hσl => ?_⟩
    obtain ⟨e, X, Y, x, hpl, hperm, hkx, h1, h2⟩ := shape_data hσs hσl (u.winIns s) hβγ
    have hσ : t.substAt [] s σ = node e X Y := by
      rw [substAt, replaceAt_nil, ← hpl]
    rw [hchild, ← hkx, hσ]
    have hs' := hts σ hσs hσl
    have hnd' := htn σ hσl
    rw [hσ] at hs' hnd'
    rw [topSgn_mul_tauS e X Y hs' hnd' hperm]
    rcases chi3_cases σ with hχ | hχ
    · obtain ⟨hx, hY⟩ := h1 hχ
      rw [hχ, mul_one, hx, hY]
    · obtain ⟨hx, hY⟩ := h2 hχ
      rw [hχ, hx, hY]
      have := sgn_swap (Ne.symm hβγ.ne) (l₂ := []) (l₃ := rlList (vlist A ++ vlist B ++
        vlist C).toFinset) (by simp) (by simp)
      simp only [List.nil_append] at this
      rw [this]
      ring
  · -- an edge below the root
    cases t with
    | leaf a => exact absurd hvp (by simp [ValidPath])
    | node e₀ l r =>
    have hkeyW : ∀ σ : LTree E, σ.labels.Perm (List.range 3) →
        key (σ.plug (u.winIns s)) = key u := fun σ h2 => ShuffleBar.key_eq_of_perm (hWp σ h2)
    cases b with
    | false =>
      set O := ctxL l p' ++ vlist r ++ (vlist A ++ vlist B ++ vlist C) with hO
      refine ⟨sgn (r.minLabel :: B.minLabel :: rlList (toLex (key u, C.minLabel) :: O).toFinset),
        sgn_mul_self _, fun σ hσs hσl => ?_⟩
      obtain ⟨e, X, Y, x, hpl, hperm, hkx, h1, h2⟩ := shape_data hσs hσl (u.winIns s) hβγ
      rw [← hA, ← hB, ← hC] at hperm
      have hσ : (node e₀ l r).substAt (false :: p') s σ =
          node e₀ (l.replaceAt p' (node e X Y)) r := by
        rw [← hpl]
        rfl
      have hvp' : ValidPath l p' := hvp
      have hperm' : (vlist (l.replaceAt p' (node e X Y)) ++ vlist r).Perm
          (x :: (vpair e X Y :: O)) := by
        have h0 := vlist_replaceAt l p' (node e X Y) hvp' (hpl ▸ hWp σ hσl)
        refine (h0.append_right _).trans ?_
        simp only [vlist_node, hO]
        refine ((((hperm.cons _).append_left _).append_right _)).trans ?_
        perm_by_count
      have hxr : vpair e X Y = toLex (key u, Y.minLabel) := by
        rw [vpair, ← hkeyW σ hσl, hpl]
      rw [hchild, ← hkx, hσ]
      have hs' := hts σ hσs hσl
      have hnd' := htn σ hσl
      rw [hσ] at hs' hnd'
      rw [topSgn_mul_tauS e₀ _ r hs' hnd' hperm', hxr]
      obtain ⟨hndk, hndr⟩ := nodup_of_perm_vlist hs' hnd' hperm'
      rcases chi3_cases σ with hχ | hχ
      · obtain ⟨hx, hY⟩ := h1 hχ
        rw [hχ, mul_one, hx, hY]
      · obtain ⟨hx, hY⟩ := h2 hχ
        rw [hχ, hx, hY]
        simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_map, not_or,
          not_exists, not_and, hxr, hx, hY, vkey_toLex, vrl_toLex] at hndk hndr
        rw [sgn_swap_rl r.minLabel (fun y hy h => hndk.2.1 y hy h) hβγ.ne
          (fun y hy h => hndr.2.1 y hy h) (fun y hy h => hndr.1.2 y hy h)]
        ring
    | true =>
      set O := vlist l ++ ctxL r p' ++ (vlist A ++ vlist B ++ vlist C) with hO
      refine ⟨sgn (r.minLabel :: B.minLabel :: rlList (toLex (key u, C.minLabel) :: O).toFinset),
        sgn_mul_self _, fun σ hσs hσl => ?_⟩
      obtain ⟨e, X, Y, x, hpl, hperm, hkx, h1, h2⟩ := shape_data hσs hσl (u.winIns s) hβγ
      rw [← hA, ← hB, ← hC] at hperm
      have hσ : (node e₀ l r).substAt (true :: p') s σ =
          node e₀ l (r.replaceAt p' (node e X Y)) := by
        rw [← hpl]
        rfl
      have hvp' : ValidPath r p' := hvp
      have hr' : (r.replaceAt p' (node e X Y)).minLabel = r.minLabel :=
        minLabel_eq_of_perm (labels_replaceAt_perm' r p' _ hvp' (hpl ▸ hWp σ hσl))
      have hperm' : (vlist l ++ vlist (r.replaceAt p' (node e X Y))).Perm
          (x :: (vpair e X Y :: O)) := by
        have h0 := vlist_replaceAt r p' (node e X Y) hvp' (hpl ▸ hWp σ hσl)
        refine (h0.append_left _).trans ?_
        simp only [vlist_node, hO]
        refine ((((hperm.cons _).append_left _).append_left _)).trans ?_
        perm_by_count
      have hxr : vpair e X Y = toLex (key u, Y.minLabel) := by
        rw [vpair, ← hkeyW σ hσl, hpl]
      rw [hchild, ← hkx, hσ]
      have hs' := hts σ hσs hσl
      have hnd' := htn σ hσl
      rw [hσ] at hs' hnd'
      rw [topSgn_mul_tauS e₀ l _ hs' hnd' hperm', hxr, hr']
      obtain ⟨hndk, hndr⟩ := nodup_of_perm_vlist hs' hnd' hperm'
      rcases chi3_cases σ with hχ | hχ
      · obtain ⟨hx, hY⟩ := h1 hχ
        rw [hχ, mul_one, hx, hY]
      · obtain ⟨hx, hY⟩ := h2 hχ
        rw [hχ, hx, hY]
        simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_map, not_or,
          not_exists, not_and, hxr, hx, hY, vkey_toLex, vrl_toLex] at hndk hndr
        rw [sgn_swap_rl r.minLabel (fun y hy h => hndk.2.1 y hy h) hβγ.ne
          (fun y hy h => hndr.2.1 y hy h) (fun y hy h => hndr.1.2 y hy h)]
        ring

end Coherence

end LTree

end Operad
