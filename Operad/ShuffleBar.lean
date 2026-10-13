/-
# The bar construction of a shuffle operad on binary generators

The bar construction of the free shuffle operad on binary generators `E` has, in arity `n`, a
basis of *bar trees*: shuffle monomials of arity `n` with some internal edges cut. The cut edges
separate the monomial into *components*, the vertices of the bar construction, each a monomial of
the free operad; the homological degree is the number of components. The differential merges two
components along a cut edge, with the sign given by the position of the edge among the cut edges,
ordered by their sets of leaves.

* **Bar trees** (`ShuffleBar.BarTree`) are monomials whose vertices carry a flag, `true` when the
  edge above the vertex is cut; `full` forgets the flags. A vertex is named by its *key*, its least
  label and its number of leaves, which tells the vertices of a monomial with distinct labels apart
  (`cutKeys`, the keys of the cut edges).
* **The differential** (`ShuffleBar.d`) merges along each cut edge (`mergeK`) with the sign
  `(-1)^#(cut edges of smaller key)`, and **squares to zero** (`d_d`).
* **Relators.** For relators `R`, functions on the arity-three monomials, substituting a relator at
  an uncut edge of a bar tree (`substRel`) gives an element of the bar construction of the free
  operad which vanishes in that of the quotient: these span the kernel `J R` of the projection onto
  the bar construction of the shuffle operad presented by `R`. It is a subcomplex (`d_mem_J`), so
  `d` induces the differential of the bar construction of the quotient.

* **Normal bar trees** (`NormalBar`): for a set `L` of arity-three leading monomials, no uncut edge
  has its window in `L` (the windows of the edges, by the key of their lower vertex, are
  `LTree.edgeWins`). Cutting an edge (`cutK`) and merging it (`mergeK`) are inverse
  (`mergeK_cutK`, `cutK_mergeK`) and commute along different edges (`mergeK_cutK_comm`); a monomial
  with `n` labels has `n - 2` edges (`LTree.card_edgeKeys`).

The underlying combinatorics of the free shuffle operad, its windows and their substitution, are
those of `Operad.ShuffleTree` and `Operad.ShuffleSubst`, applied to monomials decorated by
`E × Bool`.
-/
import Operad.ShuffleNormal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Prod.Lex

universe u v

namespace Operad

namespace LTree

variable {E F : Type*}

/-! ## Mapping the decorations -/

/-- **Map the decorations** of a tree. -/
def mapDec (f : E → F) : LTree E → LTree F
  | leaf a => leaf a
  | node e l r => node (f e) (l.mapDec f) (r.mapDec f)

@[simp] lemma mapDec_leaf (f : E → F) (a : ℕ) : (leaf a : LTree E).mapDec f = leaf a := rfl

@[simp] lemma mapDec_node (f : E → F) (e : E) (l r : LTree E) :
    (node e l r).mapDec f = node (f e) (l.mapDec f) (r.mapDec f) := rfl

@[simp] lemma labels_mapDec (f : E → F) : ∀ t : LTree E, (t.mapDec f).labels = t.labels
  | leaf _ => rfl
  | node _ l r => by simp [labels_mapDec f l, labels_mapDec f r]

@[simp] lemma minLabel_mapDec (f : E → F) : ∀ t : LTree E, (t.mapDec f).minLabel = t.minLabel
  | leaf _ => rfl
  | node _ l r => by simp [minLabel_mapDec f l, minLabel_mapDec f r]

@[simp] lemma arity_mapDec (f : E → F) : ∀ t : LTree E, (t.mapDec f).arity = t.arity
  | leaf _ => rfl
  | node _ l r => by simp [arity, arity_mapDec f l, arity_mapDec f r]

@[simp] lemma size_mapDec (f : E → F) : ∀ t : LTree E, (t.mapDec f).size = t.size
  | leaf _ => rfl
  | node _ l r => by simp [size_mapDec f l, size_mapDec f r]

@[simp] lemma isShuffle_mapDec (f : E → F) : ∀ t : LTree E, (t.mapDec f).IsShuffle ↔ t.IsShuffle
  | leaf _ => Iff.rfl
  | node _ l r => by simp [isShuffle_mapDec f l, isShuffle_mapDec f r]

lemma mapDec_mapDec {G : Type*} (f : E → F) (g : F → G) :
    ∀ t : LTree E, (t.mapDec f).mapDec g = t.mapDec (g ∘ f)
  | leaf _ => rfl
  | node _ l r => by simp [mapDec_mapDec f g l, mapDec_mapDec f g r]

lemma mapDec_id : ∀ t : LTree E, t.mapDec id = t
  | leaf _ => rfl
  | node _ l r => by simp [mapDec_id l, mapDec_id r]

lemma path_mapDec (f : E → F) (i : ℕ) : ∀ t : LTree E, (t.mapDec f).path i = (t.path i).map f
  | leaf _ => rfl
  | node _ l r => by
    simp only [mapDec_node, path, labels_mapDec, List.map_cons]
    split_ifs
    · rw [path_mapDec f i l]
    · rw [path_mapDec f i r]

lemma subtreeAt_append : ∀ (t : LTree E) (p q : List Bool),
    t.subtreeAt (p ++ q) = (t.subtreeAt p).subtreeAt q
  | leaf _, [], _ => by simp
  | leaf _, _ :: _, [] => by simp [subtreeAt]
  | leaf _, _ :: _, _ :: _ => by simp [subtreeAt]
  | node _ _ _, [], _ => by simp
  | node _ l _, false :: p, q => subtreeAt_append l p q
  | node _ _ r, true :: p, q => subtreeAt_append r p q

lemma subtreeAt_mapDec (f : E → F) :
    ∀ (t : LTree E) (p : List Bool), (t.mapDec f).subtreeAt p = (t.subtreeAt p).mapDec f
  | leaf _, [] => rfl
  | leaf _, _ :: _ => rfl
  | node _ _ _, [] => rfl
  | node _ l _, false :: p => subtreeAt_mapDec f l p
  | node _ _ r, true :: p => subtreeAt_mapDec f r p

lemma replaceAt_mapDec (f : E → F) : ∀ (t : LTree E) (p : List Bool) (u : LTree E),
    (t.mapDec f).replaceAt p (u.mapDec f) = (t.replaceAt p u).mapDec f
  | leaf _, [], _ => rfl
  | leaf _, _ :: _, _ => rfl
  | node _ _ _, [], _ => rfl
  | node e l r, false :: p, u => by
    simp only [mapDec_node, replaceAt, replaceAt_mapDec f l p u]
  | node e l r, true :: p, u => by
    simp only [mapDec_node, replaceAt, replaceAt_mapDec f r p u]

lemma plug_mapDec (f : E → F) (ins : ℕ → LTree E) :
    ∀ m : LTree E, (m.mapDec f).plug (fun k => (ins k).mapDec f) = (m.plug ins).mapDec f
  | leaf _ => rfl
  | node e l r => by simp only [mapDec_node, plug, plug_mapDec f ins l, plug_mapDec f ins r]

lemma isEdgeRoot_mapDec (f : E → F) :
    ∀ (u : LTree E) (s : Bool), (u.mapDec f).IsEdgeRoot s ↔ u.IsEdgeRoot s
  | leaf _, _ => Iff.rfl
  | node _ (leaf _) (leaf _), _ => by cases ‹Bool› <;> exact Iff.rfl
  | node _ (node _ _ _) (leaf _), _ => by cases ‹Bool› <;> exact Iff.rfl
  | node _ (leaf _) (node _ _ _), _ => by cases ‹Bool› <;> exact Iff.rfl
  | node _ (node _ _ _) (node _ _ _), _ => by cases ‹Bool› <;> exact Iff.rfl

lemma isEdge_mapDec (f : E → F) (t : LTree E) (p : List Bool) (s : Bool) :
    (t.mapDec f).IsEdge p s ↔ t.IsEdge p s := by
  unfold IsEdge
  rw [subtreeAt_mapDec, isEdgeRoot_mapDec]

lemma windowRoot_mapDec (f : E → F) :
    ∀ (u : LTree E) (s : Bool), u.IsEdgeRoot s →
      (u.mapDec f).windowRoot s = (u.windowRoot s).mapDec f
  | node e (node g a b) c, false, _ => by
    simp [windowRoot, window]
  | node e c (node g a b), true, _ => by
    cases c <;> simp [windowRoot, window]

lemma windowAt_mapDec (f : E → F) (t : LTree E) (p : List Bool) (s : Bool) (h : t.IsEdge p s) :
    (t.mapDec f).windowAt p s = (t.windowAt p s).mapDec f := by
  unfold windowAt
  rw [subtreeAt_mapDec, windowRoot_mapDec f _ s h]

lemma winInputs_mapDec (f : E → F) :
    ∀ (u : LTree E) (s : Bool), u.IsEdgeRoot s →
      (u.mapDec f).winInputs s = ((u.winInputs s).1.mapDec f, (u.winInputs s).2.1.mapDec f,
        (u.winInputs s).2.2.mapDec f)
  | node e (node g a b) c, false, _ => by
    simp only [mapDec_node, winInputs, minLabel_mapDec]
    split_ifs <;> rfl
  | node e c (node g a b), true, _ => by
    cases c <;> rfl

lemma winIns_mapDec (f : E → F) (u : LTree E) (s : Bool) (h : u.IsEdgeRoot s) (k : ℕ) :
    (u.mapDec f).winIns s k = (u.winIns s k).mapDec f := by
  simp only [winIns, winInputs_mapDec f u s h, ins3]
  split_ifs <;> rfl

lemma substAt_mapDec (f : E → F) (t : LTree E) (p : List Bool) (s : Bool) (h : t.IsEdge p s)
    (m : LTree E) : (t.mapDec f).substAt p s (m.mapDec f) = (t.substAt p s m).mapDec f := by
  unfold substAt
  rw [subtreeAt_mapDec, ← replaceAt_mapDec, ← plug_mapDec]
  congr 2
  funext k
  exact winIns_mapDec f _ s h k

/-! ## Keys -/

section Keys

variable {X : Type*}

/-- **The key of a vertex**: its least label and its number of leaves, ordered lexicographically.
On a tree with distinct labels it tells the vertices apart. -/
def key (t : LTree X) : ℕ ×ₗ ℕ := toLex (t.minLabel, t.arity)

/-- The keys of the vertices. -/
def nodeKeys : LTree X → Finset (ℕ ×ₗ ℕ)
  | leaf _ => ∅
  | node d l r => insert (key (node d l r)) (l.nodeKeys ∪ r.nodeKeys)

lemma key_node (d : X) (l r : LTree X) :
    key (node d l r) = toLex (min l.minLabel r.minLabel, l.arity + r.arity) := rfl

lemma mem_nodeKeys_labels : ∀ (t : LTree X) {k : ℕ ×ₗ ℕ}, k ∈ t.nodeKeys →
    (ofLex k).1 ∈ t.labels ∧ (ofLex k).2 ≤ t.arity
  | leaf _, k, hk => by simp [nodeKeys] at hk
  | node d l r, k, hk => by
    simp only [nodeKeys, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hk | hk
    · exact ⟨by simpa [key] using minLabel_mem (node d l r), le_rfl⟩
    · have := mem_nodeKeys_labels l hk
      exact ⟨by simp [this.1], by simp only [arity]; omega⟩
    · have := mem_nodeKeys_labels r hk
      exact ⟨by simp [this.1], by simp only [arity]; omega⟩

lemma key_not_mem_left (d : X) (l r : LTree X) : key (node d l r) ∉ l.nodeKeys := fun h => by
  have := (mem_nodeKeys_labels l h).2
  have := arity_pos r
  simp only [key, arity, ofLex_toLex] at *
  omega

lemma key_not_mem_right (d : X) (l r : LTree X) : key (node d l r) ∉ r.nodeKeys := fun h => by
  have := (mem_nodeKeys_labels r h).2
  have := arity_pos l
  simp only [key, arity, ofLex_toLex] at *
  omega

lemma disjoint_nodeKeys {d : X} {l r : LTree X} (h : (node d l r).labels.Nodup) :
    Disjoint l.nodeKeys r.nodeKeys := by
  rw [Finset.disjoint_left]
  intro k hl hr
  simp only [labels_node] at h
  exact ne_of_nodup_append h (mem_nodeKeys_labels l hl).1 (mem_nodeKeys_labels r hr).1 rfl

lemma key_mapDec {Y : Type*} (f : X → Y) (t : LTree X) : key (t.mapDec f) = key t := by
  simp [key]

/-- **The windows of the edges**, each with the key of its lower vertex. -/
def edgeWins : LTree X → List ((ℕ ×ₗ ℕ) × LTree X)
  | leaf _ => []
  | node e l r =>
    (match l with
      | leaf _ => []
      | node f a b => [(key (node f a b), window e f false a.minLabel b.minLabel r.minLabel)]) ++
    (match r with
      | leaf _ => []
      | node f a b => [(key (node f a b), window e f true a.minLabel b.minLabel l.minLabel)]) ++
    l.edgeWins ++ r.edgeWins

/-- **An edge window is the window of an edge**, at the position of its lower vertex. -/
theorem exists_of_mem_edgeWins {k : ℕ ×ₗ ℕ} {w : LTree X} : ∀ t : LTree X, (k, w) ∈ t.edgeWins →
    ∃ p s, t.IsEdge p s ∧ key (t.subtreeAt (p ++ [s])) = k ∧ t.windowAt p s = w
  | leaf _, h => by simp [edgeWins] at h
  | node e l r, h => by
    simp only [edgeWins, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · match l, h with
      | node f a b, h =>
        simp only [List.mem_singleton, Prod.mk.injEq] at h
        exact ⟨[], false, trivial, by simp [subtreeAt, h.1],
          by simp [windowAt, windowRoot, h.2]⟩
    · match r, h with
      | node f a b, h =>
        simp only [List.mem_singleton, Prod.mk.injEq] at h
        refine ⟨[], true, ?_, by simp [subtreeAt, h.1], ?_⟩
        · show IsEdgeRoot (node e l (node f a b)) true
          cases l <;> trivial
        · show windowRoot (node e l (node f a b)) true = w
          cases l <;> simp [windowRoot, h.2]
    · obtain ⟨p, s, hp, hk, hw⟩ := exists_of_mem_edgeWins l h
      exact ⟨false :: p, s, hp, hk, hw⟩
    · obtain ⟨p, s, hp, hk, hw⟩ := exists_of_mem_edgeWins r h
      exact ⟨true :: p, s, hp, hk, hw⟩

lemma mem_edgeWins_key {k : ℕ ×ₗ ℕ} {w : LTree X} : ∀ t : LTree X, (k, w) ∈ t.edgeWins →
    k ∈ t.nodeKeys ∧ (ofLex k).2 < t.arity
  | leaf _, h => by simp [edgeWins] at h
  | node e l r, h => by
    have hl := arity_pos l
    have hr := arity_pos r
    simp only [edgeWins, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · match l, h with
      | node f a b, h =>
        simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        refine ⟨by simp [nodeKeys], ?_⟩
        simp only [key, ofLex_toLex, arity] at *
        omega
    · match r, h with
      | node f a b, h =>
        simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        refine ⟨by simp [nodeKeys], ?_⟩
        simp only [key, ofLex_toLex, arity] at *
        omega
    · obtain ⟨h1, h2⟩ := mem_edgeWins_key l h
      refine ⟨by simp [nodeKeys, h1], ?_⟩
      simp only [arity]
      omega
    · obtain ⟨h1, h2⟩ := mem_edgeWins_key r h
      refine ⟨by simp [nodeKeys, h1], ?_⟩
      simp only [arity]
      omega

/-- The keys of the vertices, in preorder. -/
def keyList : LTree X → List (ℕ ×ₗ ℕ)
  | leaf _ => []
  | node d l r => key (node d l r) :: (l.keyList ++ r.keyList)

lemma mem_keyList_iff : ∀ (t : LTree X) (k : ℕ ×ₗ ℕ), k ∈ t.keyList ↔ k ∈ t.nodeKeys
  | leaf _, k => by simp [keyList, nodeKeys]
  | node d l r, k => by
    simp [keyList, nodeKeys, mem_keyList_iff l, mem_keyList_iff r]

lemma nodup_keyList : ∀ t : LTree X, t.labels.Nodup → t.keyList.Nodup
  | leaf _, _ => by simp [keyList]
  | node d l r, hnd => by
    rw [keyList, List.nodup_cons, List.mem_append, mem_keyList_iff, mem_keyList_iff]
    refine ⟨fun h => h.elim (key_not_mem_left d l r) (key_not_mem_right d l r),
      List.nodup_append.2 ⟨nodup_keyList l (List.nodup_append.1 hnd).1,
        nodup_keyList r (List.nodup_append.1 hnd).2.1, fun a ha b hb hab => ?_⟩⟩
    subst hab
    rw [mem_keyList_iff] at ha hb
    exact Finset.disjoint_left.1 (disjoint_nodeKeys hnd) ha hb

/-- The key of the root, if it is a vertex. -/
def rootKey : LTree X → List (ℕ ×ₗ ℕ)
  | leaf _ => []
  | node d l r => [key (node d l r)]

lemma edgeWins_keys (e : X) (l r : LTree X) : (node e l r).edgeWins.map Prod.fst =
    l.rootKey ++ r.rootKey ++ l.edgeWins.map Prod.fst ++ r.edgeWins.map Prod.fst := by
  cases l <;> cases r <;> simp [edgeWins, rootKey]

lemma perm_keyList : ∀ t : LTree X, t.keyList.Perm (t.rootKey ++ t.edgeWins.map Prod.fst)
  | leaf _ => by simp [keyList, rootKey, edgeWins]
  | node e l r => by
    rw [edgeWins_keys]
    simp only [keyList, rootKey, List.singleton_append]
    refine List.Perm.cons _ (((perm_keyList l).append (perm_keyList r)).trans ?_)
    simp only [List.append_assoc]
    refine List.Perm.append_left _ ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _

/-- The keys of the lower vertices of the edges: the vertices other than the root. -/
def edgeKeys (t : LTree X) : Finset (ℕ ×ₗ ℕ) := (t.edgeWins.map Prod.fst).toFinset

lemma length_keyList : ∀ t : LTree X, t.keyList.length + 1 = t.arity
  | leaf _ => rfl
  | node d l r => by
    have := length_keyList l
    have := length_keyList r
    simp only [keyList, List.length_cons, List.length_append, arity]
    omega

/-- **A monomial with `n` distinct labels has `n - 2` edges.** -/
lemma card_edgeKeys {e : X} {l r : LTree X} (hnd : (node e l r).labels.Nodup) :
    (node e l r).edgeKeys.card + 2 = (node e l r).arity := by
  have hp : (l.keyList ++ r.keyList).Perm ((node e l r).edgeWins.map Prod.fst) := by
    have := perm_keyList (node e l r)
    simp only [keyList, rootKey, List.singleton_append] at this
    exact this.cons_inv
  have hnd' : (l.keyList ++ r.keyList).Nodup := by
    have := nodup_keyList (node e l r) hnd
    rw [keyList, List.nodup_cons] at this
    exact this.2
  rw [edgeKeys, List.toFinset_card_of_nodup (hp.nodup_iff.1 hnd'), ← hp.length_eq,
    List.length_append]
  have := length_keyList l
  have := length_keyList r
  simp only [arity]
  omega

lemma mem_edgeKeys {t : LTree X} {k : ℕ ×ₗ ℕ} : k ∈ t.edgeKeys ↔ ∃ w, (k, w) ∈ t.edgeWins := by
  simp [edgeKeys]

lemma edgeKeys_node (e : X) (l r : LTree X) :
    (node e l r).edgeKeys = l.nodeKeys ∪ r.nodeKeys := by
  have hp : (l.keyList ++ r.keyList).Perm ((node e l r).edgeWins.map Prod.fst) := by
    have := perm_keyList (node e l r)
    simp only [keyList, rootKey, List.singleton_append] at this
    exact this.cons_inv
  ext k
  rw [edgeKeys, ← List.toFinset_eq_of_perm _ _ hp]
  simp [mem_keyList_iff]

lemma nodeKeys_mapDec {Y : Type*} (f : X → Y) : ∀ t : LTree X, (t.mapDec f).nodeKeys = t.nodeKeys
  | leaf _ => rfl
  | node d l r => by
    simp only [mapDec_node, nodeKeys, nodeKeys_mapDec f l, nodeKeys_mapDec f r]
    rw [show key (node (f d) (l.mapDec f) (r.mapDec f)) = key (node d l r) from
      key_mapDec f (node d l r)]

end Keys

end LTree

/-! ## Bar trees -/

namespace ShuffleBar

open LTree

variable {E : Type v}

/-- **A tree of the bar construction**: a shuffle monomial whose vertices are flagged, `true` when
the edge above the vertex is cut. On a bar tree of the bar construction the root is not flagged. -/
abbrev BarTree (E : Type v) := LTree (E × Bool)

/-- **The underlying monomial**, flags forgotten. -/
abbrev full (x : BarTree E) : LTree E := x.mapDec Prod.fst

/-- **The keys of the cut edges**, each named by the vertex below it. -/
def cutKeys : BarTree E → Finset (ℕ ×ₗ ℕ)
  | leaf _ => ∅
  | node d l r => (if d.2 then {key (node d l r)} else ∅) ∪ (cutKeys l ∪ cutKeys r)

/-- **Merge along the cut edge of key `k`**: its flag is cleared. -/
def mergeK : BarTree E → ℕ ×ₗ ℕ → BarTree E
  | leaf a, _ => leaf a
  | node d l r, k =>
    if d.2 ∧ key (node d l r) = k then node (d.1, false) l r
    else node d (mergeK l k) (mergeK r k)

/-- The flag of the root. -/
def rootFlag : BarTree E → Bool
  | leaf _ => false
  | node d _ _ => d.2

lemma cutKeys_subset : ∀ x : BarTree E, cutKeys x ⊆ x.nodeKeys
  | leaf _ => by simp [cutKeys]
  | node d l r => by
    rw [cutKeys, nodeKeys]
    refine Finset.union_subset ?_ (Finset.union_subset ?_ ?_)
    · split_ifs <;> simp
    · exact (cutKeys_subset l).trans fun k hk =>
        Finset.mem_insert_of_mem (Finset.mem_union_left _ hk)
    · exact (cutKeys_subset r).trans fun k hk =>
        Finset.mem_insert_of_mem (Finset.mem_union_right _ hk)

@[simp] lemma labels_mergeK (k : ℕ ×ₗ ℕ) : ∀ x : BarTree E, (mergeK x k).labels = x.labels
  | leaf _ => rfl
  | node d l r => by
    simp only [mergeK]
    split_ifs
    · rfl
    · simp [labels_mergeK k l, labels_mergeK k r]

@[simp] lemma minLabel_mergeK (k : ℕ ×ₗ ℕ) : ∀ x : BarTree E, (mergeK x k).minLabel = x.minLabel
  | leaf _ => rfl
  | node d l r => by
    simp only [mergeK]
    split_ifs
    · rfl
    · simp [minLabel_mergeK k l, minLabel_mergeK k r]

@[simp] lemma arity_mergeK (k : ℕ ×ₗ ℕ) : ∀ x : BarTree E, (mergeK x k).arity = x.arity
  | leaf _ => rfl
  | node d l r => by
    simp only [mergeK]
    split_ifs
    · rfl
    · simp [arity, arity_mergeK k l, arity_mergeK k r]

@[simp] lemma key_mergeK (k : ℕ ×ₗ ℕ) (x : BarTree E) : key (mergeK x k) = key x := by
  simp [key]

@[simp] lemma full_mergeK (k : ℕ ×ₗ ℕ) :
    ∀ x : BarTree E, (mergeK x k).mapDec Prod.fst = x.mapDec Prod.fst
  | leaf _ => rfl
  | node d l r => by
    simp only [mergeK]
    split_ifs
    · rfl
    · simp only [mapDec_node]
      exact congrArg₂ _ (full_mergeK k l) (full_mergeK k r)

@[simp] lemma isShuffle_mergeK (k : ℕ ×ₗ ℕ) (x : BarTree E) :
    (mergeK x k).IsShuffle ↔ x.IsShuffle := by
  rw [← isShuffle_mapDec Prod.fst, full_mergeK, isShuffle_mapDec]

lemma key_node_mergeK (d : E × Bool) (l r : BarTree E) (k : ℕ ×ₗ ℕ) :
    key (node d (mergeK l k) (mergeK r k)) = key (node d l r) := by
  simp [key_node]

lemma rootFlag_mergeK_le (k : ℕ ×ₗ ℕ) (x : BarTree E) (h : rootFlag x = false) :
    rootFlag (mergeK x k) = false := by
  cases x with
  | leaf => rfl
  | node d l r =>
    simp only [mergeK]
    split_ifs <;> simp_all [rootFlag]

lemma mergeK_of_not_mem {k : ℕ ×ₗ ℕ} : ∀ x : BarTree E, k ∉ cutKeys x → mergeK x k = x
  | leaf _, _ => rfl
  | node d l r, hk => by
    simp only [cutKeys, Finset.mem_union, not_or] at hk
    have hroot : ¬(d.2 ∧ key (node d l r) = k) := by
      rintro ⟨h1, rfl⟩
      exact hk.1 (by simp [h1])
    simp only [mergeK, hroot, if_false, mergeK_of_not_mem l hk.2.1, mergeK_of_not_mem r hk.2.2]

/-- Merging along the cut edge of key `k` removes `k` from the cut edges. -/
theorem cutKeys_mergeK {k : ℕ ×ₗ ℕ} : ∀ x : BarTree E, x.labels.Nodup → k ∈ cutKeys x →
    cutKeys (mergeK x k) = (cutKeys x).erase k
  | leaf _, _, hk => by simp [cutKeys] at hk
  | node d l r, hnd, hk => by
    have hl : k ∈ cutKeys l → k ∉ cutKeys r := fun h h' =>
      Finset.disjoint_left.1 (disjoint_nodeKeys hnd) (cutKeys_subset l h) (cutKeys_subset r h')
    have hkl : key (node d l r) ∉ cutKeys l := fun h => key_not_mem_left d l r (cutKeys_subset l h)
    have hkr : key (node d l r) ∉ cutKeys r := fun h => key_not_mem_right d l r (cutKeys_subset r h)
    have hndl : l.labels.Nodup := (List.nodup_append.1 hnd).1
    have hndr : r.labels.Nodup := (List.nodup_append.1 hnd).2.1
    by_cases hroot : d.2 ∧ key (node d l r) = k
    · obtain ⟨h1, rfl⟩ := hroot
      simp only [mergeK, h1, and_self, if_true, cutKeys, Bool.false_eq_true, if_false,
        Finset.empty_union, Finset.singleton_union]
      rw [Finset.erase_insert (by simp [hkl, hkr])]
    · simp only [mergeK, hroot, if_false, cutKeys]
      rw [key_node_mergeK]
      simp only [cutKeys, Finset.mem_union] at hk
      have hk0 : k ∉ (if d.2 then ({key (node d l r)} : Finset (ℕ ×ₗ ℕ)) else ∅) := by
        split_ifs with h1
        · exact fun h => hroot ⟨h1, (Finset.mem_singleton.1 h).symm⟩
        · simp
      rcases hk with hk | hk | hk
      · exact absurd hk hk0
      · rw [cutKeys_mergeK l hndl hk, mergeK_of_not_mem r (hl hk), Finset.erase_union_distrib,
          Finset.erase_union_distrib, Finset.erase_eq_of_notMem hk0,
          Finset.erase_eq_of_notMem (hl hk)]
      · have hk' : k ∉ cutKeys l := fun h => hl h hk
        rw [cutKeys_mergeK r hndr hk, mergeK_of_not_mem l hk', Finset.erase_union_distrib,
          Finset.erase_union_distrib, Finset.erase_eq_of_notMem hk0,
          Finset.erase_eq_of_notMem hk']

/-- **Merging along two different cut edges** in either order gives the same bar tree. -/
theorem mergeK_comm {k k' : ℕ ×ₗ ℕ} (hkk : k ≠ k') :
    ∀ x : BarTree E, mergeK (mergeK x k) k' = mergeK (mergeK x k') k
  | leaf _ => rfl
  | node d l r => by
    by_cases h : d.2 ∧ key (node d l r) = k
    · have h' : ¬(d.2 ∧ key (node d l r) = k') := fun h' => hkk (h.2.symm.trans h'.2)
      have e1 : mergeK (node d l r) k = node (d.1, false) l r := by rw [mergeK, if_pos h]
      have e2 : mergeK (node d l r) k' = node d (mergeK l k') (mergeK r k') := by
        rw [mergeK, if_neg h']
      have e3 : mergeK (node (d.1, false) l r) k' =
          node (d.1, false) (mergeK l k') (mergeK r k') := by
        rw [mergeK, if_neg (by simp)]
      have e4 : mergeK (node d (mergeK l k') (mergeK r k')) k =
          node (d.1, false) (mergeK l k') (mergeK r k') := by
        rw [mergeK, if_pos (by rw [key_node_mergeK]; exact h)]
      rw [e1, e2, e3, e4]
    · by_cases h' : d.2 ∧ key (node d l r) = k'
      · have e1 : mergeK (node d l r) k' = node (d.1, false) l r := by rw [mergeK, if_pos h']
        have e2 : mergeK (node d l r) k = node d (mergeK l k) (mergeK r k) := by
          rw [mergeK, if_neg h]
        have e3 : mergeK (node (d.1, false) l r) k =
            node (d.1, false) (mergeK l k) (mergeK r k) := by
          rw [mergeK, if_neg (by simp)]
        have e4 : mergeK (node d (mergeK l k) (mergeK r k)) k' =
            node (d.1, false) (mergeK l k) (mergeK r k) := by
          rw [mergeK, if_pos (by rw [key_node_mergeK]; exact h')]
        rw [e1, e2, e3, e4]
      · have e1 : mergeK (node d l r) k = node d (mergeK l k) (mergeK r k) := by
          rw [mergeK, if_neg h]
        have e2 : mergeK (node d l r) k' = node d (mergeK l k') (mergeK r k') := by
          rw [mergeK, if_neg h']
        have e3 : mergeK (node d (mergeK l k) (mergeK r k)) k' =
            node d (mergeK (mergeK l k) k') (mergeK (mergeK r k) k') := by
          rw [mergeK, if_neg (by rw [key_node_mergeK]; exact h')]
        have e4 : mergeK (node d (mergeK l k') (mergeK r k')) k =
            node d (mergeK (mergeK l k') k) (mergeK (mergeK r k') k) := by
          rw [mergeK, if_neg (by rw [key_node_mergeK]; exact h)]
        rw [e1, e2, e3, e4, mergeK_comm hkk l, mergeK_comm hkk r]

/-! ## The differential -/

variable (K : Type u) [CommRing K]

/-- **The sign of merging along the cut edge of key `k`**: `-1` to the number of cut edges of
smaller key. -/
def sgn (x : BarTree E) (k : ℕ ×ₗ ℕ) : K := (-1) ^ ((cutKeys x).filter (· < k)).card

/-- **The differential of a bar tree**: the merges along its cut edges, with their signs. -/
noncomputable def dTree (x : BarTree E) : BarTree E →₀ K :=
  ∑ k ∈ cutKeys x, sgn K x k • Finsupp.single (mergeK x k) 1

/-- **The differential of the bar construction** of the free shuffle operad. -/
noncomputable def d : (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) :=
  Finsupp.linearCombination K (dTree K)

@[simp] lemma d_single (x : BarTree E) (c : K) : d K (Finsupp.single x c) = c • dTree K x := by
  simp [d]

lemma sgn_mergeK {x : BarTree E} (hx : x.labels.Nodup) {k k' : ℕ ×ₗ ℕ} (hk : k ∈ cutKeys x) :
    sgn K (mergeK x k) k' = (if k < k' then -1 else 1) * sgn K x k' := by
  unfold sgn
  rw [cutKeys_mergeK x hx hk, Finset.filter_erase]
  split_ifs with h
  · have hmem : k ∈ (cutKeys x).filter (· < k') := Finset.mem_filter.2 ⟨hk, h⟩
    rw [← Finset.card_erase_add_one hmem, pow_succ]
    ring
  · have hnot : k ∉ (cutKeys x).filter (· < k') := fun h' => h (Finset.mem_filter.1 h').2
    rw [Finset.erase_eq_of_notMem hnot, one_mul]

/-- **The differential squares to zero.** -/
theorem d_dTree (x : BarTree E) (hx : x.labels.Nodup) : d K (dTree K x) = 0 := by
  have key1 : d K (dTree K x) = ∑ p ∈ (cutKeys x).offDiag,
      (sgn K x p.1 * sgn K (mergeK x p.1) p.2) • Finsupp.single (mergeK (mergeK x p.1) p.2) 1 := by
    rw [Finset.sum_finset_product (cutKeys x).offDiag (cutKeys x) (fun k => (cutKeys x).erase k)
      (fun p => by simp [Finset.mem_offDiag, and_comm, ne_comm])]
    rw [dTree, map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [map_smul, d_single, one_smul, dTree, cutKeys_mergeK x hx hk, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [smul_smul]
  rw [key1]
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) (fun p hp => ?_) (fun p hp _ => ?_)
    (fun p hp => ?_) (fun p _ => rfl)
  · obtain ⟨h1, h2, h12⟩ := Finset.mem_offDiag.1 hp
    simp only
    rw [mergeK_comm h12, sgn_mergeK K hx h1, sgn_mergeK K hx h2, ← add_smul]
    have : ¬(p.1 < p.2 ∧ p.2 < p.1) := fun h => lt_asymm h.1 h.2
    rcases lt_or_gt_of_ne h12 with h | h
    · simp [h, not_lt_of_gt h]
      ring_nf
      simp
    · simp [h, not_lt_of_gt h]
      ring_nf
      simp
  · obtain ⟨_, _, h12⟩ := Finset.mem_offDiag.1 hp
    exact fun h => h12 (by rw [Prod.ext_iff] at h; exact h.1.symm)
  · obtain ⟨h1, h2, h12⟩ := Finset.mem_offDiag.1 hp
    exact Finset.mem_offDiag.2 ⟨h2, h1, Ne.symm h12⟩

/-! ## Substitution at an uncut edge -/

/-- The flag of the vertex at a path, `false` at a leaf. -/
def flagAt (x : BarTree E) (p : List Bool) : Bool := rootFlag (x.subtreeAt p)

/-- **An uncut edge**: an edge whose lower vertex is not flagged; its two vertices lie in the same
component. -/
def IsUncut (x : BarTree E) (p : List Bool) (s : Bool) : Prop :=
  x.IsEdge p s ∧ flagAt x (p ++ [s]) = false

/-- **A monomial as a bar tree**, its root flagged `c` and no other vertex. -/
def liftW (c : Bool) : LTree E → BarTree E
  | leaf a => leaf a
  | node e l r => node (e, c) (l.mapDec (·, false)) (r.mapDec (·, false))

/-- **Substitution at an uncut edge**: the window of the edge replaced by the monomial `σ`, the
flag of the upper vertex kept. -/
def substBar (x : BarTree E) (p : List Bool) (s : Bool) (σ : LTree E) : BarTree E :=
  x.substAt p s (liftW (flagAt x p) σ)

@[simp] lemma liftW_mapDec (c : Bool) : ∀ σ : LTree E, (liftW c σ).mapDec Prod.fst = σ
  | leaf _ => rfl
  | node e l r => by
    simp only [liftW, mapDec_node, mapDec_mapDec]
    exact congrArg₂ _ (mapDec_id l) (mapDec_id r)

@[simp] lemma labels_liftW (c : Bool) (σ : LTree E) : (liftW c σ).labels = σ.labels := by
  rw [← labels_mapDec Prod.fst, liftW_mapDec]

@[simp] lemma isShuffle_liftW (c : Bool) (σ : LTree E) : (liftW c σ).IsShuffle ↔ σ.IsShuffle := by
  rw [← isShuffle_mapDec Prod.fst, liftW_mapDec]

lemma full_substBar {x : BarTree E} {p : List Bool} {s : Bool} (h : x.IsEdge p s) (σ : LTree E) :
    (substBar x p s σ).mapDec Prod.fst = (x.mapDec Prod.fst).substAt p s σ := by
  rw [substBar, ← substAt_mapDec Prod.fst x p s h, liftW_mapDec]

/-- The window of an uncut edge, as a bar tree, is the window of the monomial lifted. -/
lemma windowRoot_of_uncut : ∀ (u : BarTree E) (s : Bool), u.IsEdgeRoot s →
    rootFlag (u.subtreeAt [s]) = false →
    u.windowRoot s = liftW (rootFlag u) ((u.mapDec Prod.fst).windowRoot s)
  | node (e, c) (node (f, c') a b) d, false, _, hc => by
    simp only [subtreeAt, rootFlag] at hc
    subst hc
    simp [windowRoot, window, rootFlag, liftW]
  | node (e, c) d (node (f, c') a b), true, _, hc => by
    simp only [subtreeAt, rootFlag] at hc
    subst hc
    cases d <;> simp [windowRoot, window, rootFlag, liftW]

lemma windowAt_of_uncut {x : BarTree E} {p : List Bool} {s : Bool} (h : IsUncut x p s) :
    x.windowAt p s = liftW (flagAt x p) ((x.mapDec Prod.fst).windowAt p s) := by
  unfold windowAt flagAt
  rw [subtreeAt_mapDec]
  refine windowRoot_of_uncut _ s h.1 ?_
  have := h.2
  unfold flagAt at this
  rwa [subtreeAt_append] at this

/-! ### Keys and merges under grafting and replacement -/

lemma key_eq_of_perm {X : Type*} {t u : LTree X} (h : t.labels.Perm u.labels) : key t = key u := by
  simp only [key, minLabel_eq_of_perm h, ← length_labels, h.length_eq]

lemma arity_subtreeAt_le {X : Type*} :
    ∀ (t : LTree X) (p : List Bool), (t.subtreeAt p).arity ≤ t.arity
  | leaf _, [] => le_rfl
  | leaf _, _ :: _ => le_rfl
  | node _ _ _, [] => le_rfl
  | node _ l r, false :: p => by
    have := arity_subtreeAt_le l p
    simp only [subtreeAt, arity]
    omega
  | node _ l r, true :: p => by
    have := arity_subtreeAt_le r p
    simp only [subtreeAt, arity]
    omega

lemma not_mem_cutKeys_of_arity {k : ℕ ×ₗ ℕ} {u : BarTree E} (h : u.arity < (ofLex k).2) :
    k ∉ cutKeys u := fun hk => by
  have := (mem_nodeKeys_labels u (cutKeys_subset u hk)).2
  omega

/-- The monomial `m` with no vertex flagged. -/
abbrev unflag (m : LTree E) : BarTree E := m.mapDec (·, false)

lemma cutKeys_plug_unflag (ins : ℕ → BarTree E) : ∀ m : LTree E,
    cutKeys ((unflag m).plug ins) = m.labels.toFinset.biUnion fun a => cutKeys (ins a)
  | leaf a => by simp [plug]
  | node e l r => by
    simp only [mapDec_node, plug, cutKeys, Bool.false_eq_true, if_false, Finset.empty_union,
      labels_node, List.toFinset_append]
    rw [cutKeys_plug_unflag ins l, cutKeys_plug_unflag ins r, Finset.union_biUnion]

lemma cutKeys_plug_liftW (ins : ℕ → BarTree E) (c : Bool) (e : E) (l r : LTree E) :
    cutKeys ((liftW c (node e l r)).plug ins) =
      (if c then {key ((liftW c (node e l r)).plug ins)} else ∅) ∪
        (node e l r).labels.toFinset.biUnion fun a => cutKeys (ins a) := by
  simp only [liftW, plug, cutKeys, labels_node, List.toFinset_append]
  rw [cutKeys_plug_unflag ins l, cutKeys_plug_unflag ins r, Finset.union_biUnion]

lemma mergeK_plug_unflag (ins : ℕ → BarTree E) (k : ℕ ×ₗ ℕ) : ∀ m : LTree E,
    mergeK ((unflag m).plug ins) k = (unflag m).plug fun a => mergeK (ins a) k
  | leaf _ => rfl
  | node e l r => by
    simp only [mapDec_node, plug, mergeK, Bool.false_eq_true, false_and, if_false]
    rw [mergeK_plug_unflag ins k l, mergeK_plug_unflag ins k r]

lemma mergeK_plug_liftW (ins : ℕ → BarTree E) (c : Bool) (e : E) (l r : LTree E) (k : ℕ ×ₗ ℕ)
    (hk : ¬(c ∧ key ((liftW c (node e l r)).plug ins) = k)) :
    mergeK ((liftW c (node e l r)).plug ins) k =
      (liftW c (node e l r)).plug fun a => mergeK (ins a) k := by
  change mergeK (node (e, c) ((unflag l).plug ins) ((unflag r).plug ins)) k = _
  rw [mergeK]
  split_ifs with h'
  · exact absurd h' hk
  · rw [mergeK_plug_unflag, mergeK_plug_unflag]
    rfl

lemma mergeK_plug_liftW_root (ins : ℕ → BarTree E) (c : Bool) (e : E) (l r : LTree E)
    (k : ℕ ×ₗ ℕ) (hk : c ∧ key ((liftW c (node e l r)).plug ins) = k) :
    mergeK ((liftW c (node e l r)).plug ins) k = (liftW false (node e l r)).plug ins := by
  change mergeK (node (e, c) ((unflag l).plug ins) ((unflag r).plug ins)) k = _
  rw [mergeK]
  split_ifs with h'
  · rfl
  · exact absurd hk h'

lemma subtreeAt_mergeK (k : ℕ ×ₗ ℕ) :
    ∀ (x : BarTree E) (p : List Bool), (mergeK x k).subtreeAt p = mergeK (x.subtreeAt p) k
  | leaf _, [] => rfl
  | leaf _, _ :: _ => rfl
  | node _ _ _, [] => by simp
  | node d l r, b :: p => by
    by_cases h : d.2 ∧ key (node d l r) = k
    · have hk : ∀ t : BarTree E, t.arity < (node d l r).arity → mergeK t k = t := fun t ht =>
        mergeK_of_not_mem t (not_mem_cutKeys_of_arity (by
          rw [← h.2]
          simpa [key] using ht))
      rw [mergeK, if_pos h]
      cases b
      · simp only [subtreeAt]
        rw [hk]
        have := arity_subtreeAt_le l p
        have := arity_pos r
        simp only [arity]
        omega
      · simp only [subtreeAt]
        rw [hk]
        have := arity_subtreeAt_le r p
        have := arity_pos l
        simp only [arity]
        omega
    · rw [mergeK, if_neg h]
      cases b
      · exact subtreeAt_mergeK k l p
      · exact subtreeAt_mergeK k r p

lemma mergeK_replaceAt (k : ℕ ×ₗ ℕ) : ∀ (x : BarTree E) (p : List Bool) (U : BarTree E),
    (∃ e l r, x.subtreeAt p = node e l r) → U.labels.Perm (x.subtreeAt p).labels →
    mergeK (x.replaceAt p U) k = (mergeK x k).replaceAt p (mergeK U k)
  | leaf _, [], _, _, _ => by simp
  | leaf _, _ :: _, _, ⟨_, _, _, h⟩, _ => by simp [subtreeAt] at h
  | node _ _ _, [], _, _, _ => by simp
  | node d l r, b :: p, U, hv, hU => by
    have hUa : U.arity = (subtreeAt (node d l r) (b :: p)).arity := by
      rw [← length_labels, ← length_labels, hU.length_eq]
    cases b
    · have hkey : key (node d (l.replaceAt p U) r) = key (node d l r) :=
        key_eq_of_perm (by simpa using (labels_replaceAt_perm l p U hv hU).append_right _)
      by_cases h : d.2 ∧ key (node d l r) = k
      · have hUk : mergeK U k = U := mergeK_of_not_mem U (not_mem_cutKeys_of_arity (by
          rw [← h.2, hUa]
          have := arity_subtreeAt_le l p
          have := arity_pos r
          simp only [key, subtreeAt, arity, ofLex_toLex]
          omega))
        rw [replaceAt, mergeK, if_pos (by rw [hkey]; exact h), mergeK, if_pos h, hUk]
        rfl
      · rw [replaceAt, mergeK, if_neg (by rw [hkey]; exact h), mergeK, if_neg h,
          mergeK_replaceAt k l p U hv hU]
        rfl
    · have hkey : key (node d l (r.replaceAt p U)) = key (node d l r) :=
        key_eq_of_perm (by simpa using (labels_replaceAt_perm r p U hv hU).append_left _)
      by_cases h : d.2 ∧ key (node d l r) = k
      · have hUk : mergeK U k = U := mergeK_of_not_mem U (not_mem_cutKeys_of_arity (by
          rw [← h.2, hUa]
          have := arity_subtreeAt_le r p
          have := arity_pos l
          simp only [key, subtreeAt, arity, ofLex_toLex]
          omega))
        rw [replaceAt, mergeK, if_pos (by rw [hkey]; exact h), mergeK, if_pos h, hUk]
        rfl
      · rw [replaceAt, mergeK, if_neg (by rw [hkey]; exact h), mergeK, if_neg h,
          mergeK_replaceAt k r p U hv hU]
        rfl

lemma cutKeys_replaceAt : ∀ (x : BarTree E) (p : List Bool) (U : BarTree E),
    (∃ e l r, x.subtreeAt p = node e l r) → U.labels.Perm (x.subtreeAt p).labels →
    cutKeys U = cutKeys (x.subtreeAt p) → cutKeys (x.replaceAt p U) = cutKeys x
  | leaf _, [], _, _, _, h => by simpa using h
  | leaf _, _ :: _, _, ⟨_, _, _, h⟩, _, _ => by simp [subtreeAt] at h
  | node _ _ _, [], _, _, _, h => by simpa using h
  | node d l r, false :: p, U, hv, hU, h => by
    have hkey : key (node d (l.replaceAt p U) r) = key (node d l r) :=
      key_eq_of_perm (by simpa using (labels_replaceAt_perm l p U hv hU).append_right _)
    simp only [replaceAt, cutKeys, hkey, cutKeys_replaceAt l p U hv hU h]
  | node d l r, true :: p, U, hv, hU, h => by
    have hkey : key (node d l (r.replaceAt p U)) = key (node d l r) :=
      key_eq_of_perm (by simpa using (labels_replaceAt_perm r p U hv hU).append_left _)
    simp only [replaceAt, cutKeys, hkey, cutKeys_replaceAt r p U hv hU h]

/-! ### Substitution -/

/-- **The window of an edge** of a shuffle monomial with distinct labels is a shuffle monomial of
arity three on `0, 1, 2`. -/
lemma windowRoot_shape {X : Type*} : ∀ (u : LTree X) (s : Bool), u.IsEdgeRoot s → u.IsShuffle →
    u.labels.Nodup → (u.windowRoot s).IsShuffle ∧ (u.windowRoot s).labels.Perm (List.range 3) ∧
      ∃ e l r, u.windowRoot s = node e l r
  | node e (node f a b) c, false, _, hs, hnd => by
    rcases window_left_shape hs hnd with h | h <;> simp only [windowRoot, h]
    · exact ⟨by simp, (by decide : ([0, 1, 2] : List ℕ).Perm (List.range 3)), _, _, _, rfl⟩
    · exact ⟨by simp, (by decide : ([0, 2, 1] : List ℕ).Perm (List.range 3)), _, _, _, rfl⟩
  | node e c (node f a b), true, _, hs, _ => by
    have h := window_right_eq hs
    have hw : windowRoot (node e c (node f a b)) true = window e f true a.minLabel b.minLabel
        c.minLabel := by cases c <;> rfl
    rw [hw, h]
    exact ⟨by simp, (by decide : ([0, 1, 2] : List ℕ).Perm (List.range 3)), _, _, _, rfl⟩

lemma winIns_root {X : Type*} (d d' : X) (l r : LTree X) (s : Bool)
    (he : (node d l r).IsEdgeRoot s) : (node d l r).winIns s = (node d' l r).winIns s := by
  cases s <;> cases l <;> cases r <;> first | rfl | exact absurd he (by simp [IsEdgeRoot])

lemma winIns_mergeK (k : ℕ ×ₗ ℕ) : ∀ (d : E × Bool) (l r : BarTree E) (s : Bool),
    (node d l r).IsEdgeRoot s → rootFlag ((node d l r).subtreeAt [s]) = false →
    (node d (mergeK l k) (mergeK r k)).winIns s = fun a => mergeK ((node d l r).winIns s a) k
  | d, node f a b, c, false, _, hf => by
    simp only [subtreeAt, rootFlag] at hf
    have : mergeK (node f a b) k = node f (mergeK a k) (mergeK b k) := by
      rw [mergeK, if_neg (by simp [hf])]
    funext i
    simp only [winIns, this, winInputs, minLabel_mergeK]
    split_ifs <;> simp only [ins3] <;> split_ifs <;> rfl
  | d, c, node f a b, true, _, hf => by
    simp only [subtreeAt, rootFlag] at hf
    have : mergeK (node f a b) k = node f (mergeK a k) (mergeK b k) := by
      rw [mergeK, if_neg (by simp [hf])]
    funext i
    have e1 : (node d (mergeK c k) (node f (mergeK a k) (mergeK b k))).winInputs true =
        (mergeK c k, mergeK a k, mergeK b k) := by cases mergeK c k <;> rfl
    have e2 : (node d c (node f a b)).winInputs true = (c, a, b) := by cases c <;> rfl
    simp only [winIns, this, e1, e2, ins3]
    split_ifs <;> rfl

section Subst

variable {x : BarTree E} {p : List Bool} {s : Bool} {σ : LTree E}

/-- At an uncut edge, the vertex is its window, a monomial lifted, with the inputs grafted. -/
lemma subtreeAt_eq_plug (hs : x.IsShuffle) (hnd : x.labels.Nodup) (h : IsUncut x p s) :
    x.subtreeAt p =
      (liftW (flagAt x p) ((x.mapDec Prod.fst).windowAt p s)).plug ((x.subtreeAt p).winIns s) := by
  have hw := winSpec h.1 (isShuffle_subtreeAt x p hs) (nodup_subtreeAt x p hnd)
  rw [← windowAt_of_uncut h]
  exact hw.window.symm

lemma window_full_shape (hs : x.IsShuffle) (hnd : x.labels.Nodup) (h : IsUncut x p s) :
    ((x.mapDec Prod.fst).windowAt p s).IsShuffle ∧
      ((x.mapDec Prod.fst).windowAt p s).labels.Perm (List.range 3) ∧
      ∃ e l r, (x.mapDec Prod.fst).windowAt p s = node e l r := by
  unfold windowAt
  rw [subtreeAt_mapDec]
  exact windowRoot_shape _ s ((isEdgeRoot_mapDec _ _ s).2 h.1)
    (by simpa using isShuffle_subtreeAt x p hs) (by simpa using nodup_subtreeAt x p hnd)

lemma perm_labels_plug_liftW (hs : x.IsShuffle) (hnd : x.labels.Nodup) (h : IsUncut x p s)
    (hσ : σ.labels.Perm (List.range 3)) (c : Bool) :
    ((liftW c σ).plug ((x.subtreeAt p).winIns s)).labels.Perm (x.subtreeAt p).labels :=
  ((perm_labels_plug (by simpa using hσ) _).trans
    (winSpec h.1 (isShuffle_subtreeAt x p hs) (nodup_subtreeAt x p hnd)).perm.symm)

/-- **Substitution keeps the cut edges.** -/
theorem cutKeys_substBar (hs : x.IsShuffle) (hnd : x.labels.Nodup) (h : IsUncut x p s)
    (hσ : σ.labels.Perm (List.range 3)) (hσn : ∃ e l r, σ = node e l r) :
    cutKeys (substBar x p s σ) = cutKeys x := by
  obtain ⟨e', l', r', rfl⟩ := hσn
  obtain ⟨-, hwl, e, l, r, hw⟩ := window_full_shape hs hnd h
  have hu := subtreeAt_eq_plug hs hnd h
  have hperm := perm_labels_plug_liftW hs hnd h hσ (flagAt x p)
  refine cutKeys_replaceAt x p _ h.1.exists_node hperm ?_
  rw [hw] at hu hwl
  have hk : key ((liftW (flagAt x p) (node e' l' r')).plug ((x.subtreeAt p).winIns s)) =
      key ((liftW (flagAt x p) (node e l r)).plug ((x.subtreeAt p).winIns s)) :=
    (key_eq_of_perm hperm).trans (congrArg key hu)
  conv_rhs => rw [hu]
  rw [cutKeys_plug_liftW, cutKeys_plug_liftW, List.toFinset_eq_of_perm _ _ hσ,
    List.toFinset_eq_of_perm _ _ hwl, hk]

/-- **Merging commutes with substitution.** -/
theorem mergeK_substBar (hs : x.IsShuffle) (hnd : x.labels.Nodup) (h : IsUncut x p s)
    (hσ : σ.labels.Perm (List.range 3)) (hσn : ∃ e l r, σ = node e l r) (k : ℕ ×ₗ ℕ) :
    mergeK (substBar x p s σ) k = substBar (mergeK x k) p s σ := by
  obtain ⟨e', l', r', rfl⟩ := hσn
  have hperm := perm_labels_plug_liftW hs hnd h hσ (flagAt x p)
  unfold substBar substAt
  rw [mergeK_replaceAt k x p _ h.1.exists_node hperm]
  simp only [flagAt, subtreeAt_mergeK]
  congr 1
  obtain ⟨d, L, R, hu⟩ := h.1.exists_node
  have hflag : flagAt x p = d.2 := by simp [flagAt, hu, rootFlag]
  have hkey : key ((liftW (flagAt x p) (node e' l' r')).plug ((x.subtreeAt p).winIns s)) =
      key (node d L R) := by rw [← hu]; exact key_eq_of_perm hperm
  rw [hflag, hu] at hkey
  rw [hu]
  simp only [rootFlag]
  by_cases hroot : d.2 ∧ key (node d L R) = k
  · have e1 : mergeK (node d L R) k = node (d.1, false) L R := by rw [mergeK, if_pos hroot]
    have he : (node d L R).IsEdgeRoot s := by rw [← hu]; exact h.1
    rw [e1, ← winIns_root d (d.1, false) L R s he,
      mergeK_plug_liftW_root _ _ _ _ _ _ ⟨hroot.1, hkey.trans hroot.2⟩]
  · have e1 : mergeK (node d L R) k = node d (mergeK L k) (mergeK R k) := by
      rw [mergeK, if_neg hroot]
    have he : (node d L R).IsEdgeRoot s := by rw [← hu]; exact h.1
    have hf : rootFlag ((node d L R).subtreeAt [s]) = false := by
      have := h.2
      rwa [flagAt, subtreeAt_append, hu] at this
    rw [e1, winIns_mergeK k d L R s he hf,
      mergeK_plug_liftW _ _ _ _ _ _ (fun h' => hroot ⟨h'.1, hkey.symm.trans h'.2⟩)]

lemma isEdgeRoot_mergeK (k : ℕ ×ₗ ℕ) (u : BarTree E) (s : Bool) :
    (mergeK u k).IsEdgeRoot s ↔ u.IsEdgeRoot s := by
  rw [← isEdgeRoot_mapDec Prod.fst, full_mergeK, isEdgeRoot_mapDec]

/-- **An uncut edge stays uncut after a merge.** -/
lemma IsUncut.mergeK (h : IsUncut x p s) (k : ℕ ×ₗ ℕ) : IsUncut (mergeK x k) p s := by
  refine ⟨?_, ?_⟩
  · unfold IsEdge
    rw [subtreeAt_mergeK, isEdgeRoot_mergeK]
    exact h.1
  · unfold flagAt
    rw [subtreeAt_mergeK]
    exact rootFlag_mergeK_le k _ h.2

lemma isShuffle_substBar (hs : x.IsShuffle) (hnd : x.labels.Nodup) (h : IsUncut x p s)
    (hσs : σ.IsShuffle) (hσ : σ.labels.Perm (List.range 3)) : (substBar x p s σ).IsShuffle :=
  isShuffle_substAt h.1 hs hnd (by simpa using hσs) (by simpa using hσ)

lemma perm_labels_substBar (hs : x.IsShuffle) (hnd : x.labels.Nodup) (h : IsUncut x p s)
    (hσ : σ.labels.Perm (List.range 3)) : (substBar x p s σ).labels.Perm x.labels :=
  perm_labels_substAt h.1 hs hnd (by simpa using hσ)

lemma rootFlag_substBar (hs : x.IsShuffle) (hnd : x.labels.Nodup) (h : IsUncut x p s)
    (hσn : ∃ e l r, σ = node e l r) : rootFlag (substBar x p s σ) = rootFlag x := by
  obtain ⟨e, l, r, rfl⟩ := hσn
  obtain ⟨d, L, R, hu⟩ := h.1.exists_node
  unfold substBar substAt
  cases p with
  | nil =>
    simp only [replaceAt_nil, flagAt, subtreeAt_nil]
    simp [liftW, plug, rootFlag]
  | cons b p =>
    cases x with
    | leaf => simp [subtreeAt] at hu
    | node d' L' R' => cases b <;> rfl

end Subst

/-- **A bar tree of the bar construction**: a shuffle monomial with distinct labels whose root is
not cut. -/
structure Valid (x : BarTree E) : Prop where
  shuffle : x.IsShuffle
  nodup : x.labels.Nodup
  root : rootFlag x = false

lemma Valid.mergeK {x : BarTree E} (hx : Valid x) (k : ℕ ×ₗ ℕ) : Valid (mergeK x k) :=
  ⟨(isShuffle_mergeK k x).2 hx.shuffle, by simpa using hx.nodup, rootFlag_mergeK_le k x hx.root⟩

lemma sgn_congr {x y : BarTree E} (h : cutKeys x = cutKeys y) (k : ℕ ×ₗ ℕ) :
    sgn K x k = sgn K y k := by
  simp [sgn, h]

/-! ## Relators and the bar construction of the quotient -/

section Relators

variable [Fintype E] [DecidableEq E]

lemma mono_shape (σ : Mono E 3) :
    σ.1.IsShuffle ∧ σ.1.labels.Perm (List.range 3) ∧ ∃ e l r, σ.1 = node e l r := by
  have h := (mem_monomials 3 σ.1).1 σ.2
  refine ⟨h.1, h.2, ?_⟩
  match hσ : σ.1 with
  | leaf a =>
    have := h.2.length_eq
    rw [hσ] at this
    simp at this
  | node e l r => exact ⟨e, l, r, rfl⟩

lemma Valid.substBar {x : BarTree E} (hx : Valid x) {p : List Bool} {s : Bool} (h : IsUncut x p s)
    (σ : Mono E 3) : Valid (substBar x p s σ.1) := by
  obtain ⟨hσs, hσ, hσn⟩ := mono_shape σ
  exact ⟨isShuffle_substBar hx.shuffle hx.nodup h hσs hσ,
    (perm_labels_substBar hx.shuffle hx.nodup h hσ).nodup_iff.2 hx.nodup,
    (rootFlag_substBar hx.shuffle hx.nodup h hσn).trans hx.root⟩

/-- **A relator substituted at an uncut edge**: the relator `r`, a function on the monomials of
arity three, read as the sum of the bar trees with the window of the edge replaced by each
monomial, with the coefficients of `r`. -/
noncomputable def substRel (x : BarTree E) (p : List Bool) (s : Bool) (r : Mono E 3 → K) :
    BarTree E →₀ K :=
  ∑ σ, r σ • Finsupp.single (substBar x p s σ.1) 1

/-- **The relator subcomplex**: the span of the relators substituted at the uncut edges of the
bar trees, the kernel of the projection of the bar construction of the free shuffle operad onto
that of the shuffle operad presented by `R`. -/
noncomputable def J (R : Submodule K (Mono E 3 → K)) : Submodule K (BarTree E →₀ K) :=
  Submodule.span K {v | ∃ x p s r, Valid x ∧ IsUncut x p s ∧ r ∈ R ∧ v = substRel K x p s r}

/-- **The differential of a substituted relator** is a sum of substituted relators. -/
theorem d_substRel {x : BarTree E} (hx : Valid x) {p : List Bool} {s : Bool} (h : IsUncut x p s)
    (r : Mono E 3 → K) :
    d K (substRel K x p s r) = ∑ k ∈ cutKeys x, sgn K x k • substRel K (mergeK x k) p s r := by
  simp only [substRel, map_sum, map_smul, d_single, one_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  obtain ⟨-, hσ, hσn⟩ := mono_shape σ
  rw [dTree, cutKeys_substBar hx.shuffle hx.nodup h hσ hσn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sgn_congr K (cutKeys_substBar hx.shuffle hx.nodup h hσ hσn),
    mergeK_substBar hx.shuffle hx.nodup h hσ hσn, smul_comm]

/-- **The relator subcomplex is a subcomplex.** -/
theorem d_mem_J (R : Submodule K (Mono E 3 → K)) {v : BarTree E →₀ K} (hv : v ∈ J K R) :
    d K v ∈ J K R := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, p, s, r, hx, h, hr, rfl⟩ := hv
    rw [d_substRel K hx h]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, p, s, r, hx.mergeK k, h.mergeK k, hr, rfl⟩)
  | zero => simp
  | add v w _ _ hv hw => rw [map_add]; exact add_mem hv hw
  | smul c v _ hv => rw [map_smul]; exact Submodule.smul_mem _ c hv

end Relators

/-! ## Normal bar trees, and cutting an edge -/

/-- **A normal bar tree** for a set `L` of arity-three monomials: no uncut edge has its window in
`L`, so that every component is a normal monomial. -/
def NormalBar (L : Set (LTree E)) (x : BarTree E) : Prop :=
  ∀ kw ∈ (x.mapDec Prod.fst).edgeWins, kw.1 ∉ cutKeys x → kw.2 ∉ L

lemma normalBar_mergeK {L : Set (LTree E)} {x : BarTree E} (hnd : x.labels.Nodup)
    {k : ℕ ×ₗ ℕ} (hk : k ∈ cutKeys x) :
    NormalBar L (mergeK x k) ↔
      NormalBar L x ∧ ∀ w, (k, w) ∈ (x.mapDec Prod.fst).edgeWins → w ∉ L := by
  unfold NormalBar
  rw [full_mergeK, cutKeys_mergeK x hnd hk]
  constructor
  · intro h
    exact ⟨fun kw hkw hc => h kw hkw fun h' => hc (Finset.mem_of_mem_erase h'),
      fun w hw => h (k, w) hw (Finset.notMem_erase k _)⟩
  · rintro ⟨h1, h2⟩ ⟨k', w⟩ hkw hc
    by_cases hkk : k' = k
    · subst hkk
      exact h2 w hkw
    · exact h1 _ hkw fun h => hc (Finset.mem_erase.2 ⟨hkk, h⟩)

lemma key_mem_cutKeys : ∀ (x : BarTree E) (q : List Bool) (d : E × Bool) (l r : BarTree E),
    x.subtreeAt q = node d l r → d.2 = true → key (node d l r) ∈ cutKeys x
  | leaf _, [], _, _, _, h, _ => by simp at h
  | leaf _, _ :: _, _, _, _, h, _ => by simp [subtreeAt] at h
  | node d' l' r', [], d, l, r, h, hd => by
    simp only [subtreeAt_nil, node.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [cutKeys, hd]
  | node d' l' r', false :: q, d, l, r, h, hd => by
    have := key_mem_cutKeys l' q d l r h hd
    simp [cutKeys, this]
  | node d' l' r', true :: q, d, l, r, h, hd => by
    have := key_mem_cutKeys r' q d l r h hd
    simp [cutKeys, this]

lemma cutKeys_subset_insert : ∀ x : BarTree E,
    cutKeys x ⊆ insert (key x) (x.mapDec Prod.fst).edgeKeys
  | leaf _ => by simp [cutKeys]
  | node d l r => by
    rw [cutKeys, mapDec_node, edgeKeys_node, nodeKeys_mapDec, nodeKeys_mapDec]
    refine Finset.union_subset ?_ (Finset.union_subset ?_ ?_)
    · split_ifs <;> simp
    · exact (cutKeys_subset l).trans fun k hk =>
        Finset.mem_insert_of_mem (Finset.mem_union_left _ hk)
    · exact (cutKeys_subset r).trans fun k hk =>
        Finset.mem_insert_of_mem (Finset.mem_union_right _ hk)

/-- **The cut edges are edges**, the root being uncut. -/
lemma cutKeys_subset_edgeKeys {x : BarTree E} (hx : rootFlag x = false) :
    cutKeys x ⊆ (x.mapDec Prod.fst).edgeKeys := by
  cases x with
  | leaf => simp [cutKeys]
  | node d l r =>
    simp only [rootFlag] at hx
    rw [cutKeys, mapDec_node, edgeKeys_node, nodeKeys_mapDec, nodeKeys_mapDec,
      if_neg (by simp [hx]), Finset.empty_union]
    exact Finset.union_subset_union (cutKeys_subset l) (cutKeys_subset r)

/-- Cut the edge above the vertex of key `k`, in a subtree. -/
def cutAux : BarTree E → ℕ ×ₗ ℕ → BarTree E
  | leaf a, _ => leaf a
  | node d l r, k =>
    if key (node d l r) = k then node (d.1, true) l r else node d (cutAux l k) (cutAux r k)

/-- **Cut the edge above the vertex of key `k`.** -/
def cutK : BarTree E → ℕ ×ₗ ℕ → BarTree E
  | leaf a, _ => leaf a
  | node d l r, k => node d (cutAux l k) (cutAux r k)

@[simp] lemma full_cutAux (k : ℕ ×ₗ ℕ) :
    ∀ x : BarTree E, (cutAux x k).mapDec Prod.fst = x.mapDec Prod.fst
  | leaf _ => rfl
  | node d l r => by
    simp only [cutAux]
    split_ifs
    · rfl
    · simp only [mapDec_node]
      exact congrArg₂ _ (full_cutAux k l) (full_cutAux k r)

@[simp] lemma full_cutK (k : ℕ ×ₗ ℕ) (x : BarTree E) :
    (cutK x k).mapDec Prod.fst = x.mapDec Prod.fst := by
  cases x with
  | leaf => rfl
  | node d l r =>
    simp only [cutK, mapDec_node]
    exact congrArg₂ _ (full_cutAux k l) (full_cutAux k r)

@[simp] lemma labels_cutK (k : ℕ ×ₗ ℕ) (x : BarTree E) : (cutK x k).labels = x.labels := by
  rw [← labels_mapDec Prod.fst, full_cutK, labels_mapDec]

lemma isShuffle_cutK (k : ℕ ×ₗ ℕ) (x : BarTree E) : (cutK x k).IsShuffle ↔ x.IsShuffle := by
  rw [← isShuffle_mapDec Prod.fst, full_cutK, isShuffle_mapDec]

lemma rootFlag_cutK (k : ℕ ×ₗ ℕ) (x : BarTree E) : rootFlag (cutK x k) = rootFlag x := by
  cases x <;> rfl

lemma key_cutAux (k : ℕ ×ₗ ℕ) (x : BarTree E) : key (cutAux x k) = key x := by
  rw [← key_mapDec Prod.fst, full_cutAux, key_mapDec]

lemma cutAux_of_not_mem {k : ℕ ×ₗ ℕ} : ∀ x : BarTree E, k ∉ x.nodeKeys → cutAux x k = x
  | leaf _, _ => rfl
  | node d l r, hk => by
    simp only [nodeKeys, Finset.mem_insert, Finset.mem_union, not_or] at hk
    simp only [cutAux, if_neg (Ne.symm hk.1), cutAux_of_not_mem l hk.2.1,
      cutAux_of_not_mem r hk.2.2]

lemma minLabel_cutAux (k : ℕ ×ₗ ℕ) (x : BarTree E) : (cutAux x k).minLabel = x.minLabel := by
  rw [← minLabel_mapDec Prod.fst, full_cutAux, minLabel_mapDec]

lemma arity_cutAux (k : ℕ ×ₗ ℕ) (x : BarTree E) : (cutAux x k).arity = x.arity := by
  rw [← arity_mapDec Prod.fst, full_cutAux, arity_mapDec]

lemma key_node_cutAux (d : E × Bool) (l r : BarTree E) (k : ℕ ×ₗ ℕ) :
    key (node d (cutAux l k) (cutAux r k)) = key (node d l r) := by
  simp [key_node, minLabel_cutAux, arity_cutAux]

lemma cutKeys_cutAux {k : ℕ ×ₗ ℕ} : ∀ x : BarTree E, x.labels.Nodup → k ∈ x.nodeKeys →
    cutKeys (cutAux x k) = insert k (cutKeys x)
  | leaf _, _, hk => by simp [nodeKeys] at hk
  | node d l r, hnd, hk => by
    have hdisj := disjoint_nodeKeys hnd
    by_cases hroot : key (node d l r) = k
    · subst hroot
      have hkey : key (node (d.1, true) l r) = key (node d l r) := rfl
      rw [cutAux, if_pos rfl, cutKeys, cutKeys, hkey, if_pos rfl]
      ext k'
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
      split_ifs <;> simp
    · simp only [nodeKeys, Finset.mem_insert, Finset.mem_union] at hk
      rw [cutAux, if_neg hroot, cutKeys, cutKeys, key_node_cutAux]
      rcases hk with hk | hk | hk
      · exact absurd hk.symm hroot
      · have hk' : k ∉ r.nodeKeys := fun h => Finset.disjoint_left.1 hdisj hk h
        rw [cutKeys_cutAux l (List.nodup_append.1 hnd).1 hk, cutAux_of_not_mem r hk']
        ext k'
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      · have hk' : k ∉ l.nodeKeys := fun h => Finset.disjoint_left.1 hdisj h hk
        rw [cutKeys_cutAux r (List.nodup_append.1 hnd).2.1 hk, cutAux_of_not_mem l hk']
        ext k'
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto

/-- **Cutting an edge adds it to the cut edges.** -/
lemma cutKeys_cutK {x : BarTree E} (hnd : x.labels.Nodup) {k : ℕ ×ₗ ℕ}
    (hk : k ∈ (x.mapDec Prod.fst).edgeKeys) : cutKeys (cutK x k) = insert k (cutKeys x) := by
  cases x with
  | leaf => simp [edgeKeys, edgeWins] at hk
  | node d l r =>
    have hdisj := disjoint_nodeKeys hnd
    rw [mapDec_node, edgeKeys_node, nodeKeys_mapDec, nodeKeys_mapDec, Finset.mem_union] at hk
    rw [cutK, cutKeys, cutKeys, key_node_cutAux]
    rcases hk with hk | hk
    · rw [cutKeys_cutAux l (List.nodup_append.1 hnd).1 hk,
        cutAux_of_not_mem r fun h => Finset.disjoint_left.1 hdisj hk h]
      ext k'
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    · rw [cutKeys_cutAux r (List.nodup_append.1 hnd).2.1 hk,
        cutAux_of_not_mem l fun h => Finset.disjoint_left.1 hdisj h hk]
      ext k'
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto

lemma mergeK_cutAux {k : ℕ ×ₗ ℕ} : ∀ y : BarTree E, k ∉ cutKeys y → mergeK (cutAux y k) k = y
  | leaf _, _ => rfl
  | node d l r, hk => by
    have hkl : k ∉ cutKeys l := fun h => hk (by rw [cutKeys]; simp [h])
    have hkr : k ∉ cutKeys r := fun h => hk (by rw [cutKeys]; simp [h])
    by_cases hroot : key (node d l r) = k
    · have hd : d.2 = false := by
        by_contra hd
        exact hk (by rw [cutKeys]; simp [hd, hroot])
      rw [cutAux, if_pos hroot, mergeK, if_pos ⟨rfl, hroot⟩]
      obtain ⟨e, c⟩ := d
      simp only at hd
      subst hd
      rfl
    · rw [cutAux, if_neg hroot, mergeK, if_neg (by rw [key_node_cutAux]; exact fun h => hroot h.2),
        mergeK_cutAux l hkl, mergeK_cutAux r hkr]

lemma cutAux_mergeK {k : ℕ ×ₗ ℕ} : ∀ y : BarTree E, y.labels.Nodup → k ∈ cutKeys y →
    cutAux (mergeK y k) k = y
  | leaf _, _, hk => by simp [cutKeys] at hk
  | node d l r, hnd, hk => by
    have hdisj := disjoint_nodeKeys hnd
    by_cases hroot : d.2 ∧ key (node d l r) = k
    · rw [mergeK, if_pos hroot, cutAux,
        if_pos (show key (node (d.1, false) l r) = k from hroot.2)]
      obtain ⟨e, c⟩ := d
      obtain ⟨h1, -⟩ := hroot
      simp only at h1
      subst h1
      rfl
    · have hlr : k ∈ cutKeys l ∨ k ∈ cutKeys r := by
        rw [cutKeys, Finset.mem_union, Finset.mem_union] at hk
        rcases hk with hk | hk | hk
        · split_ifs at hk with hd
          · exact absurd ⟨hd, (Finset.mem_singleton.1 hk).symm⟩ hroot
          · simp at hk
        · exact Or.inl hk
        · exact Or.inr hk
      have hne : key (node d l r) ≠ k := by
        rintro rfl
        rcases hlr with h | h
        · exact key_not_mem_left d l r (cutKeys_subset l h)
        · exact key_not_mem_right d l r (cutKeys_subset r h)
      rw [mergeK, if_neg hroot, cutAux, if_neg (by rw [key_node_mergeK]; exact hne)]
      rcases hlr with h | h
      · have hr : k ∉ r.nodeKeys := fun h' => Finset.disjoint_left.1 hdisj (cutKeys_subset l h) h'
        rw [cutAux_mergeK l (List.nodup_append.1 hnd).1 h,
          mergeK_of_not_mem r fun h' => hr (cutKeys_subset r h'), cutAux_of_not_mem r hr]
      · have hl : k ∉ l.nodeKeys := fun h' => Finset.disjoint_left.1 hdisj h' (cutKeys_subset r h)
        rw [cutAux_mergeK r (List.nodup_append.1 hnd).2.1 h,
          mergeK_of_not_mem l fun h' => hl (cutKeys_subset l h'), cutAux_of_not_mem l hl]

/-- **Merging undoes cutting.** -/
lemma mergeK_cutK {x : BarTree E} (hx : rootFlag x = false) {k : ℕ ×ₗ ℕ} (hk : k ∉ cutKeys x) :
    mergeK (cutK x k) k = x := by
  cases x with
  | leaf => rfl
  | node d l r =>
    simp only [rootFlag] at hx
    have hkl : k ∉ cutKeys l := fun h => hk (by rw [cutKeys]; simp [h])
    have hkr : k ∉ cutKeys r := fun h => hk (by rw [cutKeys]; simp [h])
    rw [cutK, mergeK, if_neg (by simp [hx]), mergeK_cutAux l hkl, mergeK_cutAux r hkr]

/-- **Cutting undoes merging.** -/
lemma cutK_mergeK {x : BarTree E} (hnd : x.labels.Nodup) (hx : rootFlag x = false)
    {k : ℕ ×ₗ ℕ} (hk : k ∈ cutKeys x) : cutK (mergeK x k) k = x := by
  cases x with
  | leaf => simp [cutKeys] at hk
  | node d l r =>
    simp only [rootFlag] at hx
    have hdisj := disjoint_nodeKeys hnd
    rw [cutKeys, if_neg (by simp [hx]), Finset.empty_union, Finset.mem_union] at hk
    rw [mergeK, if_neg (by simp [hx]), cutK]
    rcases hk with h | h
    · have hr : k ∉ r.nodeKeys := fun h' => Finset.disjoint_left.1 hdisj (cutKeys_subset l h) h'
      rw [cutAux_mergeK l (List.nodup_append.1 hnd).1 h,
        mergeK_of_not_mem r fun h' => hr (cutKeys_subset r h'), cutAux_of_not_mem r hr]
    · have hl : k ∉ l.nodeKeys := fun h' => Finset.disjoint_left.1 hdisj h' (cutKeys_subset r h)
      rw [cutAux_mergeK r (List.nodup_append.1 hnd).2.1 h,
        mergeK_of_not_mem l fun h' => hl (cutKeys_subset l h'), cutAux_of_not_mem l hl]

lemma mergeK_cutAux_comm {k k₀ : ℕ ×ₗ ℕ} (hkk : k ≠ k₀) :
    ∀ y : BarTree E, mergeK (cutAux y k₀) k = cutAux (mergeK y k) k₀
  | leaf _ => rfl
  | node d l r => by
    by_cases h0 : key (node d l r) = k₀
    · have h1 : ¬(d.2 ∧ key (node d l r) = k) := fun h => hkk (h.2.symm.trans h0)
      rw [cutAux, if_pos h0, mergeK, if_neg (fun h => hkk (h.2.symm.trans h0)), mergeK,
        if_neg h1, cutAux, if_pos (by rw [key_node_mergeK]; exact h0)]
    · by_cases h1 : d.2 ∧ key (node d l r) = k
      · rw [cutAux, if_neg h0, mergeK, if_pos (by rw [key_node_cutAux]; exact h1), mergeK,
          if_pos h1, cutAux, if_neg (show ¬key (node (d.1, false) l r) = k₀ from h0)]
      · rw [cutAux, if_neg h0, mergeK, if_neg (by rw [key_node_cutAux]; exact h1), mergeK,
          if_neg h1, cutAux, if_neg (by rw [key_node_mergeK]; exact h0),
          mergeK_cutAux_comm hkk l, mergeK_cutAux_comm hkk r]

/-- **Merging and cutting different edges commute.** -/
lemma mergeK_cutK_comm {k k₀ : ℕ ×ₗ ℕ} (hkk : k ≠ k₀) (x : BarTree E) :
    mergeK (cutK x k₀) k = cutK (mergeK x k) k₀ := by
  cases x with
  | leaf => rfl
  | node d l r =>
    by_cases h1 : d.2 ∧ key (node d l r) = k
    · rw [cutK, mergeK, if_pos (by rw [key_node_cutAux]; exact h1), mergeK, if_pos h1, cutK]
    · rw [cutK, mergeK, if_neg (by rw [key_node_cutAux]; exact h1), mergeK, if_neg h1, cutK,
        mergeK_cutAux_comm hkk l, mergeK_cutAux_comm hkk r]

lemma normalBar_cutK {L : Set (LTree E)} {x : BarTree E} (hnd : x.labels.Nodup) {k : ℕ ×ₗ ℕ}
    (hk : k ∈ (x.mapDec Prod.fst).edgeKeys) (h : NormalBar L x) : NormalBar L (cutK x k) := by
  unfold NormalBar at h ⊢
  rw [full_cutK, cutKeys_cutK hnd hk]
  exact fun kw hkw hc => h kw hkw fun h' => hc (Finset.mem_insert_of_mem h')

end ShuffleBar

end Operad
