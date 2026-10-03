/-
# The bar construction of shuffle operads with generators of any arity

The bar construction of the free shuffle operad on generators `E` of any arity has a basis of
**bar trees**: shuffle monomials some of whose internal edges are cut. Here a bar tree is a
monomial on the generators with a flag, `BE E k = E k × Bool`, the flag of a vertex saying
whether the edge above it is cut (`forget` forgets the flags). The cut edges separate a bar tree
into components, the vertices of the bar construction.

* **Keys** (`STree.key`): a vertex is named by the least leaf and the number of vertices of its
  subtree. In a shuffle tree with distinct leaves the keys of the vertices are distinct
  (`STree.nodup_vkeys`), and the keys of the edges (`STree.edgeKeys`) are the keys of the
  vertices other than the root.
* **Cutting and merging** (`STree.setF`): set the flag of the vertex with a given key. Merging
  along a cut removes it from the set of cuts (`STree.cutKeys_setF_false`), and cutting along an
  edge adds it (`STree.cutKeys_setF_true`).
* **The differential** (`STree.Bar.d`) merges along each cut edge, with the sign of its position
  among the cut edges ordered by their keys, and **squares to zero** (`STree.Bar.d_d`): the bar
  trees with their cuts are a complex of cuts (`Operad.CutComplex`).
-/
import Operad.ShuffleAnyGroebner
import Operad.Hoffbeck

universe v

namespace Operad

namespace STree

variable {E F G : ℕ → Type v}

/-! ## Mapping the generators -/

/-- **Map the generators** of a tree. -/
def mapG (φ : ∀ k, E k → F k) : STree E → STree F
  | leaf a => leaf a
  | node e c => node (φ _ e) fun i => (c i).mapG φ

section MapG

variable (φ : ∀ k, E k → F k)

@[simp] lemma mapG_leaf (a : ℕ) : (leaf a : STree E).mapG φ = leaf a := rfl

@[simp] lemma mapG_node {k : ℕ} (e : E k) (c : Fin k → STree E) :
    (node e c).mapG φ = node (φ k e) fun i => (c i).mapG φ := rfl

lemma mapG_mapG (ψ : ∀ k, F k → G k) :
    ∀ t : STree E, (t.mapG φ).mapG ψ = t.mapG fun k e => ψ k (φ k e)
  | leaf _ => rfl
  | node e c => by
    simp only [mapG_node]
    congr 1
    funext i
    exact mapG_mapG ψ (c i)

lemma mapG_id : ∀ t : STree E, t.mapG (fun _ e => e) = t
  | leaf _ => rfl
  | node e c => by
    simp only [mapG_node]
    congr 1
    funext i
    exact mapG_id (c i)

@[simp] lemma first_mapG : ∀ t : STree E, (t.mapG φ).first = t.first
  | leaf _ => rfl
  | @node _ k e c => by
    by_cases h : 0 < k
    · rw [mapG_node, first_node _ _ h, first_node _ _ h]
      exact first_mapG (c _)
    · simp only [mapG_node, first, dif_neg h]

@[simp] lemma labels_mapG : ∀ t : STree E, (t.mapG φ).labels = t.labels
  | leaf _ => rfl
  | node e c => by
    simp only [mapG_node, labels_node]
    exact Finset.sum_congr rfl fun i _ => labels_mapG (c i)

@[simp] lemma weight_mapG : ∀ t : STree E, (t.mapG φ).weight = t.weight
  | leaf _ => rfl
  | node e c => by
    simp only [mapG_node, weight_node]
    rw [Finset.sum_congr rfl fun i _ => weight_mapG (c i)]

@[simp] lemma isShuffle_mapG : ∀ t : STree E, (t.mapG φ).IsShuffle ↔ t.IsShuffle
  | leaf _ => Iff.rfl
  | node e c => by
    rw [mapG_node, isShuffle_node, isShuffle_node]
    simp only [first_mapG]
    exact and_congr Iff.rfl (and_congr (forall_congr' fun i => isShuffle_mapG (c i)) Iff.rfl)

lemma subst_mapG : ∀ (t : STree E) (xs : ℕ → STree E),
    (t.subst xs).mapG φ = (t.mapG φ).subst fun a => (xs a).mapG φ
  | leaf _, _ => rfl
  | node e c, xs => by
    simp only [subst_node, mapG_node]
    congr 1
    funext i
    exact subst_mapG (c i) xs

lemma get?_mapG : ∀ (t : STree E) (p : List ℕ), (t.mapG φ).get? p = (t.get? p).map (mapG φ)
  | t, [] => by simp
  | leaf _, _ :: _ => rfl
  | @node _ k e c, i :: p => by
    rw [mapG_node, get?_node_cons, get?_node_cons]
    split_ifs with h
    · exact get?_mapG (c ⟨i, h⟩) p
    · rfl

lemma replace_mapG : ∀ (t : STree E) (p : List ℕ) (u : STree E),
    (t.replace p u).mapG φ = (t.mapG φ).replace p (u.mapG φ)
  | _, [], _ => by rw [replace_nil, replace_nil]
  | leaf _, _ :: _, _ => rfl
  | @node _ k e c, i :: p, u => by
    rw [replace_node_cons, mapG_node, mapG_node, replace_node_cons]
    congr 1
    funext j
    split_ifs
    · exact replace_mapG (c j) p u
    · rfl

end MapG

/-! ## Keys -/

/-- **The key of a tree**: its least leaf and its number of vertices. -/
def key (t : STree E) : ℕ ×ₗ ℕ := toLex (t.first, t.weight)

/-- **The keys of the vertices**: the keys of the subtrees at the vertices. -/
def vkeys : STree E → Multiset (ℕ ×ₗ ℕ)
  | leaf _ => 0
  | node e c => key (node e c) ::ₘ ∑ i, (c i).vkeys

/-- **The keys of the edges**: the keys of the vertices other than the root. -/
def edgeKeys : STree E → Finset (ℕ ×ₗ ℕ)
  | leaf _ => ∅
  | node _ c => (∑ i, (c i).vkeys).toFinset

@[simp] lemma vkeys_leaf (a : ℕ) : (leaf a : STree E).vkeys = 0 := rfl

@[simp] lemma vkeys_node {k : ℕ} (e : E k) (c : Fin k → STree E) :
    (node e c).vkeys = key (node e c) ::ₘ ∑ i, (c i).vkeys := rfl

@[simp] lemma edgeKeys_leaf (a : ℕ) : (leaf a : STree E).edgeKeys = ∅ := rfl

@[simp] lemma edgeKeys_node {k : ℕ} (e : E k) (c : Fin k → STree E) :
    (node e c).edgeKeys = (∑ i, (c i).vkeys).toFinset := rfl

@[simp] lemma key_mapG (φ : ∀ k, E k → F k) (t : STree E) : (t.mapG φ).key = t.key := by
  rw [key, key, first_mapG, weight_mapG]

@[simp] lemma vkeys_mapG (φ : ∀ k, E k → F k) : ∀ t : STree E, (t.mapG φ).vkeys = t.vkeys
  | leaf _ => rfl
  | node e c => by
    rw [mapG_node, vkeys_node, vkeys_node, ← mapG_node, key_mapG]
    congr 1
    exact Finset.sum_congr rfl fun i _ => vkeys_mapG φ (c i)

@[simp] lemma edgeKeys_mapG (φ : ∀ k, E k → F k) : ∀ t : STree E, (t.mapG φ).edgeKeys = t.edgeKeys
  | leaf _ => rfl
  | node e c => by
    rw [mapG_node, edgeKeys_node, edgeKeys_node]
    simp only [vkeys_mapG]

lemma mem_vkeys_node {k : ℕ} {e : E k} {c : Fin k → STree E} {x : ℕ ×ₗ ℕ} :
    x ∈ (node e c).vkeys ↔ x = key (node e c) ∨ ∃ i, x ∈ (c i).vkeys := by
  simp [Multiset.mem_sum]

lemma mem_edgeKeys_node {k : ℕ} {e : E k} {c : Fin k → STree E} {x : ℕ ×ₗ ℕ} :
    x ∈ (node e c).edgeKeys ↔ ∃ i, x ∈ (c i).vkeys := by
  simp [Multiset.mem_sum]

lemma weight_lt_node {k : ℕ} (e : E k) (c : Fin k → STree E) (i : Fin k) :
    (c i).weight < (node e c).weight := by
  rw [weight_node]
  have := Finset.single_le_sum (f := fun j => (c j).weight) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  simp only at this
  omega

/-- The key of a vertex has a leaf of the tree and at most its number of vertices. -/
theorem mem_vkeys : ∀ {t : STree E}, t.IsShuffle → ∀ {x : ℕ ×ₗ ℕ}, x ∈ t.vkeys →
    (ofLex x).1 ∈ t.labels ∧ (ofLex x).2 ≤ t.weight
  | leaf _, _, _, hx => absurd hx (Multiset.notMem_zero _)
  | node e c, h, x, hx => by
    rcases mem_vkeys_node.1 hx with rfl | ⟨i, hi⟩
    · exact ⟨first_mem h, le_rfl⟩
    · obtain ⟨h1, h2⟩ := mem_vkeys (h.child i) hi
      exact ⟨Multiset.mem_of_le (labels_le_node e c i) h1, h2.trans (weight_lt_node e c i).le⟩

lemma nodup_sum_fin {α : Type*} {k : ℕ} (f : Fin k → Multiset α) (h₁ : ∀ i, (f i).Nodup)
    (h₂ : ∀ i j, i ≠ j → Disjoint (f i) (f j)) : (∑ i, f i).Nodup := by
  classical
  suffices ∀ s : Finset (Fin k), (∑ i ∈ s, f i).Nodup from this _
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Multiset.nodup_add]
    exact ⟨h₁ i, ih, Multiset.disjoint_finsetSum_right.2 fun j hj =>
      h₂ i j fun h => hi (h ▸ hj)⟩

/-- **The keys of the vertices of a shuffle tree with distinct leaves are distinct.** -/
theorem nodup_vkeys : ∀ {t : STree E}, t.IsShuffle → t.labels.Nodup → t.vkeys.Nodup
  | leaf _, _, _ => Multiset.nodup_zero
  | node e c, h, hn => by
    rw [vkeys_node, Multiset.nodup_cons]
    refine ⟨fun hk => ?_, nodup_sum_fin _ (fun i => nodup_vkeys (h.child i) (nodup_of_node hn i))
      fun i j hij => Multiset.disjoint_left.2 fun hx hx' => ?_⟩
    · obtain ⟨i, hi⟩ := (Multiset.mem_sum (s := Finset.univ)).1 hk
      have := (mem_vkeys (h.child i) hi.2).2
      simp only [key, ofLex_toLex] at this
      exact absurd (weight_lt_node e c i) (not_lt.2 this)
    · exact not_mem_of_node hn hij (mem_vkeys (h.child i) hx).1 (mem_vkeys (h.child j) hx').1

/-! ## Bar trees: flags, cuts and merges -/

variable (E) in
/-- **Generators with a flag**: on a vertex of a bar tree, whether the edge above it is cut. -/
abbrev BE (k : ℕ) : Type v := E k × Bool

/-- **The underlying tree** of a bar tree: forget the flags. -/
def forget (t : STree (BE E)) : STree E := t.mapG fun _ d => d.1

/-- **No cuts**: every vertex flagged `false`. -/
def allF (t : STree E) : STree (BE E) := t.mapG fun _ e => (e, false)

/-- **Flag the root** with `b` and the other vertices with `false`. -/
def fl (b : Bool) : STree E → STree (BE E)
  | leaf a => leaf a
  | node e c => node (e, b) fun i => allF (c i)

/-- **The flag of the root**, `false` for a leaf. -/
def rootF : STree (BE E) → Bool
  | leaf _ => false
  | node d _ => d.2

@[simp] lemma forget_leaf (a : ℕ) : forget (leaf a : STree (BE E)) = leaf a := rfl

@[simp] lemma forget_node {k : ℕ} (d : BE E k) (c : Fin k → STree (BE E)) :
    forget (node d c) = node d.1 fun i => forget (c i) := rfl

@[simp] lemma allF_leaf (a : ℕ) : allF (leaf a : STree E) = leaf a := rfl

@[simp] lemma allF_node {k : ℕ} (e : E k) (c : Fin k → STree E) :
    allF (node e c) = node (e, false) fun i => allF (c i) := rfl

@[simp] lemma fl_leaf (b : Bool) (a : ℕ) : fl b (leaf a : STree E) = leaf a := rfl

@[simp] lemma fl_node (b : Bool) {k : ℕ} (e : E k) (c : Fin k → STree E) :
    fl b (node e c) = node (e, b) fun i => allF (c i) := rfl

@[simp] lemma forget_allF (t : STree E) : forget (allF t) = t := by
  rw [forget, allF, mapG_mapG]
  exact mapG_id t

@[simp] lemma forget_fl (b : Bool) : ∀ t : STree E, forget (fl b t) = t
  | leaf _ => rfl
  | node e c => by simp

@[simp] lemma first_forget (t : STree (BE E)) : (forget t).first = t.first := first_mapG _ t

@[simp] lemma labels_forget (t : STree (BE E)) : (forget t).labels = t.labels := labels_mapG _ t

@[simp] lemma weight_forget (t : STree (BE E)) : (forget t).weight = t.weight := weight_mapG _ t

@[simp] lemma isShuffle_forget (t : STree (BE E)) : (forget t).IsShuffle ↔ t.IsShuffle :=
  isShuffle_mapG _ t

@[simp] lemma key_forget (t : STree (BE E)) : (forget t).key = t.key := key_mapG _ t

@[simp] lemma vkeys_forget (t : STree (BE E)) : (forget t).vkeys = t.vkeys := vkeys_mapG _ t

@[simp] lemma edgeKeys_forget (t : STree (BE E)) : (forget t).edgeKeys = t.edgeKeys :=
  edgeKeys_mapG _ t

lemma key_eq_of_forget {s t : STree (BE E)} (h : forget s = forget t) : s.key = t.key := by
  rw [← key_forget, h, key_forget]

lemma forget_subst (t : STree (BE E)) (xs : ℕ → STree (BE E)) :
    forget (t.subst xs) = (forget t).subst fun a => forget (xs a) := subst_mapG _ t xs

lemma forget_replace (t : STree (BE E)) (p : List ℕ) (u : STree (BE E)) :
    forget (t.replace p u) = (forget t).replace p (forget u) := replace_mapG _ t p u

lemma get?_forget (t : STree (BE E)) (p : List ℕ) :
    (forget t).get? p = (t.get? p).map forget := get?_mapG _ t p

lemma allF_subst (t : STree E) (xs : ℕ → STree E) :
    allF (t.subst xs) = (allF t).subst fun a => allF (xs a) := subst_mapG _ t xs

lemma allF_replace (t : STree E) (p : List ℕ) (u : STree E) :
    allF (t.replace p u) = (allF t).replace p (allF u) := replace_mapG _ t p u

@[simp] lemma first_fl (b : Bool) (t : STree E) : (fl b t).first = t.first := by
  rw [← first_forget, forget_fl]

@[simp] lemma labels_fl (b : Bool) (t : STree E) : (fl b t).labels = t.labels := by
  rw [← labels_forget, forget_fl]

@[simp] lemma weight_fl (b : Bool) (t : STree E) : (fl b t).weight = t.weight := by
  rw [← weight_forget, forget_fl]

@[simp] lemma isShuffle_fl (b : Bool) (t : STree E) : (fl b t).IsShuffle ↔ t.IsShuffle := by
  rw [← isShuffle_forget, forget_fl]

@[simp] lemma first_allF (t : STree E) : (allF t).first = t.first := first_mapG _ t

@[simp] lemma labels_allF (t : STree E) : (allF t).labels = t.labels := labels_mapG _ t

@[simp] lemma weight_allF (t : STree E) : (allF t).weight = t.weight := weight_mapG _ t

@[simp] lemma isShuffle_allF (t : STree E) : (allF t).IsShuffle ↔ t.IsShuffle :=
  isShuffle_mapG _ t

/-- **Set the flag** of the vertices with key `x` to `b`: cut (`true`) or merge (`false`) along
the edge above the vertex with key `x`. -/
def setF (x : ℕ ×ₗ ℕ) (b : Bool) : STree (BE E) → STree (BE E)
  | leaf a => leaf a
  | node d c => node (d.1, if key (node d c) = x then b else d.2) fun i => (c i).setF x b

/-- **The keys of the cut edges**: the keys of the vertices flagged `true`. -/
def cutKeys : STree (BE E) → Finset (ℕ ×ₗ ℕ)
  | leaf _ => ∅
  | node d c => (if d.2 then {key (node d c)} else ∅) ∪ Finset.univ.biUnion fun i => (c i).cutKeys

section SetF

variable (x : ℕ ×ₗ ℕ) (b : Bool)

@[simp] lemma setF_leaf (a : ℕ) : setF x b (leaf a : STree (BE E)) = leaf a := rfl

lemma setF_node {k : ℕ} (d : BE E k) (c : Fin k → STree (BE E)) :
    setF x b (node d c) =
      node (d.1, if key (node d c) = x then b else d.2) fun i => (c i).setF x b := rfl

@[simp] lemma forget_setF : ∀ t : STree (BE E), forget (setF x b t) = forget t
  | leaf _ => rfl
  | node d c => by
    rw [setF_node, forget_node, forget_node]
    congr 1
    funext i
    exact forget_setF (c i)

@[simp] lemma first_setF (t : STree (BE E)) : (setF x b t).first = t.first := by
  rw [← first_forget, forget_setF, first_forget]

@[simp] lemma labels_setF (t : STree (BE E)) : (setF x b t).labels = t.labels := by
  rw [← labels_forget, forget_setF, labels_forget]

@[simp] lemma weight_setF (t : STree (BE E)) : (setF x b t).weight = t.weight := by
  rw [← weight_forget, forget_setF, weight_forget]

@[simp] lemma isShuffle_setF (t : STree (BE E)) : (setF x b t).IsShuffle ↔ t.IsShuffle := by
  rw [← isShuffle_forget, forget_setF, isShuffle_forget]

@[simp] lemma key_setF (t : STree (BE E)) : (setF x b t).key = t.key :=
  key_eq_of_forget (forget_setF x b t)

@[simp] lemma vkeys_setF (t : STree (BE E)) : (setF x b t).vkeys = t.vkeys := by
  rw [← vkeys_forget, forget_setF, vkeys_forget]

@[simp] lemma edgeKeys_setF (t : STree (BE E)) : (setF x b t).edgeKeys = t.edgeKeys := by
  rw [← edgeKeys_forget, forget_setF, edgeKeys_forget]

/-- The key of a node does not depend on the flags. -/
lemma key_node_setF {k : ℕ} (d : BE E k) (b' : Bool) (c : Fin k → STree (BE E)) :
    key (node (d.1, b') fun i => (c i).setF x b) = key (node d c) :=
  key_eq_of_forget (by simp)

lemma rootF_setF_node {k : ℕ} (d : BE E k) (c : Fin k → STree (BE E)) :
    rootF (setF x b (node d c)) = if key (node d c) = x then b else d.2 := rfl

end SetF

lemma mem_cutKeys_node {k : ℕ} {d : BE E k} {c : Fin k → STree (BE E)} {y : ℕ ×ₗ ℕ} :
    y ∈ cutKeys (node d c) ↔ (d.2 = true ∧ y = key (node d c)) ∨ ∃ i, y ∈ cutKeys (c i) := by
  rw [cutKeys, Finset.mem_union, Finset.mem_biUnion]
  split_ifs with h <;> simp [h]

/-- **The cut edges are vertices.** -/
theorem mem_vkeys_of_mem_cutKeys : ∀ {t : STree (BE E)} {y : ℕ ×ₗ ℕ}, y ∈ cutKeys t →
    y ∈ t.vkeys
  | leaf _, _, h => absurd h (Finset.notMem_empty _)
  | node d c, y, h => by
    rw [mem_vkeys_node]
    rcases mem_cutKeys_node.1 h with ⟨-, rfl⟩ | ⟨i, hi⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i, mem_vkeys_of_mem_cutKeys hi⟩

/-- **Merging along an edge removes it from the cuts.** -/
theorem mem_cutKeys_setF_false (x : ℕ ×ₗ ℕ) : ∀ (t : STree (BE E)) (y : ℕ ×ₗ ℕ),
    y ∈ cutKeys (setF x false t) ↔ y ≠ x ∧ y ∈ cutKeys t
  | leaf _, y => by simp [cutKeys]
  | node d c, y => by
    rw [setF_node, mem_cutKeys_node, mem_cutKeys_node, key_node_setF]
    simp only [mem_cutKeys_setF_false x]
    by_cases hk : key (node d c) = x
    · subst hk
      simp only [if_true, Bool.false_eq_true, false_and, false_or]
      constructor
      · rintro ⟨i, hne, hi⟩
        exact ⟨hne, Or.inr ⟨i, hi⟩⟩
      · rintro ⟨hne, ⟨-, rfl⟩ | ⟨i, hi⟩⟩
        · exact absurd rfl hne
        · exact ⟨i, hne, hi⟩
    · simp only [hk, if_false]
      constructor
      · rintro (⟨h, rfl⟩ | ⟨i, hne, hi⟩)
        · exact ⟨hk, Or.inl ⟨h, rfl⟩⟩
        · exact ⟨hne, Or.inr ⟨i, hi⟩⟩
      · rintro ⟨hne, ⟨h, rfl⟩ | ⟨i, hi⟩⟩
        · exact Or.inl ⟨h, rfl⟩
        · exact Or.inr ⟨i, hne, hi⟩

theorem cutKeys_setF_false (x : ℕ ×ₗ ℕ) (t : STree (BE E)) :
    cutKeys (setF x false t) = (cutKeys t).erase x := by
  ext y
  rw [mem_cutKeys_setF_false, Finset.mem_erase]

/-- **Cutting along an edge adds it to the cuts.** -/
theorem mem_cutKeys_setF_true (x : ℕ ×ₗ ℕ) : ∀ (t : STree (BE E)) (y : ℕ ×ₗ ℕ),
    y ∈ cutKeys (setF x true t) ↔ (y = x ∧ x ∈ t.vkeys) ∨ y ∈ cutKeys t
  | leaf _, y => by simp [cutKeys]
  | node d c, y => by
    rw [setF_node, mem_cutKeys_node, mem_cutKeys_node, key_node_setF, mem_vkeys_node]
    simp only [mem_cutKeys_setF_true x]
    by_cases hk : key (node d c) = x
    · simp only [hk, if_true]
      aesop
    · simp only [hk, if_false]
      aesop

theorem cutKeys_setF_true {x : ℕ ×ₗ ℕ} {t : STree (BE E)} (hx : x ∈ t.vkeys) :
    cutKeys (setF x true t) = insert x (cutKeys t) := by
  ext y
  rw [mem_cutKeys_setF_true, Finset.mem_insert]
  exact or_congr (and_iff_left hx) Iff.rfl

/-- **Setting the flags at two different keys commutes.** -/
theorem setF_comm {x y : ℕ ×ₗ ℕ} (hxy : x ≠ y) (b b' : Bool) :
    ∀ t : STree (BE E), setF x b (setF y b' t) = setF y b' (setF x b t)
  | leaf _ => rfl
  | node d c => by
    rw [setF_node, setF_node, setF_node, setF_node, key_node_setF, key_node_setF]
    congr 1
    · by_cases hx : key (node d c) = x
      · have hy : key (node d c) ≠ y := hx ▸ hxy
        simp only [hx, if_true, if_neg (hx ▸ hy)]
      · by_cases hy : key (node d c) = y
        · simp only [hy, if_true, if_neg (hy ▸ hx)]
        · simp only [if_neg hx, if_neg hy]
    · funext i
      exact setF_comm hxy b b' (c i)

/-- **Setting the flags at a key twice** is setting them once. -/
theorem setF_setF_self (x : ℕ ×ₗ ℕ) (b b' : Bool) :
    ∀ t : STree (BE E), setF x b (setF x b' t) = setF x b t
  | leaf _ => rfl
  | node d c => by
    rw [setF_node, setF_node, setF_node, key_node_setF]
    congr 1
    · by_cases hx : key (node d c) = x
      · simp only [hx, if_true]
      · simp only [if_neg hx]
    · funext i
      exact setF_setF_self x b b' (c i)

/-- **Setting the flags at a key which is not a vertex** does nothing. -/
theorem setF_of_notMem {x : ℕ ×ₗ ℕ} (b : Bool) :
    ∀ {t : STree (BE E)}, x ∉ t.vkeys → setF x b t = t
  | leaf _, _ => rfl
  | node d c, h => by
    rw [mem_vkeys_node, not_or, not_exists] at h
    rw [setF_node, if_neg (Ne.symm h.1)]
    congr 1
    funext i
    exact setF_of_notMem b (h.2 i)

/-- **Merging along an edge which is not cut** does nothing. -/
theorem setF_false_of_notMem : ∀ {x : ℕ ×ₗ ℕ} {t : STree (BE E)}, x ∉ cutKeys t →
    setF x false t = t
  | _, leaf _, _ => rfl
  | x, node d c, h => by
    rw [mem_cutKeys_node, not_or, not_exists] at h
    rw [setF_node]
    have hd : (if key (node d c) = x then false else d.2) = d.2 := by
      split_ifs with hk
      · cases hd2 : d.2
        · rfl
        · exact absurd ⟨hd2, hk.symm⟩ h.1
      · rfl
    rw [hd]
    congr 1
    funext i
    exact setF_false_of_notMem (h.2 i)

/-- **Cutting along an edge which is cut** does nothing, the keys being distinct. -/
theorem setF_true_of_mem : ∀ {x : ℕ ×ₗ ℕ} {t : STree (BE E)}, t.vkeys.Nodup →
    x ∈ cutKeys t → setF x true t = t
  | _, leaf _, _, h => absurd h (Finset.notMem_empty _)
  | x, @node _ k d c, hn, h => by
    rw [vkeys_node, Multiset.nodup_cons] at hn
    have hnc : ∀ i, (c i).vkeys.Nodup := fun i =>
      Multiset.nodup_of_le (Finset.single_le_sum (f := fun j => (c j).vkeys)
        (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)) hn.2
    have hdisj : ∀ i j, i ≠ j → Disjoint (c i).vkeys (c j).vkeys := fun i j hij => by
      have hle : (c i).vkeys + (c j).vkeys ≤ ∑ l, (c l).vkeys := by
        rw [← Finset.sum_pair (f := fun l => (c l).vkeys) hij]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => Multiset.zero_le _
      exact (Multiset.nodup_add.1 (Multiset.nodup_of_le hle hn.2)).2.2
    rw [setF_node]
    by_cases hk : key (node d c) = x
    · -- the root is the cut vertex
      subst hk
      have hc : ∀ i, key (node d c) ∉ (c i).vkeys := fun i hi =>
        hn.1 ((Multiset.mem_sum (s := Finset.univ)).2 ⟨i, Finset.mem_univ i, hi⟩)
      rcases mem_cutKeys_node.1 h with ⟨hd, -⟩ | ⟨i, hi⟩
      · rw [if_pos rfl]
        obtain ⟨d₁, d₂⟩ := d
        simp only at hd
        subst hd
        congr 1
        funext i
        exact setF_of_notMem true (hc i)
      · exact absurd (mem_vkeys_of_mem_cutKeys hi) (hc i)
    · rw [if_neg hk]
      rcases mem_cutKeys_node.1 h with ⟨-, rfl⟩ | ⟨i, hi⟩
      · exact absurd rfl hk
      · congr 1
        funext j
        by_cases hij : j = i
        · subst hij
          exact setF_true_of_mem (hnc j) hi
        · exact setF_of_notMem true fun hj =>
            Multiset.disjoint_left.1 (hdisj i j (Ne.symm hij)) (mem_vkeys_of_mem_cutKeys hi) hj

/-! ## Flags and contexts -/

lemma sum_map_finsetSum {ι : Type*} (s : Finset ι) (g : ι → Multiset ℕ) (f : ℕ → ℕ) :
    ((∑ i ∈ s, g i).map f).sum = ∑ i ∈ s, ((g i).map f).sum := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Multiset.map_add, Multiset.sum_add, ih]

/-- **The number of vertices of a substituted tree.** -/
theorem weight_subst : ∀ (t : STree E) (xs : ℕ → STree E),
    (t.subst xs).weight = t.weight + (t.labels.map fun a => (xs a).weight).sum
  | leaf a, xs => by simp
  | node e c, xs => by
    simp only [subst_node, weight_node, labels_node, sum_map_finsetSum]
    rw [Finset.sum_congr rfl fun i _ => weight_subst (c i) xs, Finset.sum_add_distrib]
    ring

/-- **Replacing a subtree by one with as many vertices** keeps the number of vertices. -/
theorem weight_replace : ∀ {t u : STree E} {p : List ℕ}, t.get? p = some u → ∀ {v : STree E},
    v.weight = u.weight → (t.replace p v).weight = t.weight
  | t, u, [], h, v, hv => by
    rw [get?_nil, Option.some_inj] at h
    subst h
    simpa using hv
  | leaf _, _, _ :: _, h, _, _ => by simp at h
  | @node _ k e c, u, i :: p, h, v, hv => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    rw [replace_node_cons, weight_node, weight_node]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · have : j = ⟨i, hi⟩ := Fin.ext hj
      subst this
      exact weight_replace h hv
    · rfl

theorem key_replace {t u : STree E} {p : List ℕ} (h : t.get? p = some u) {v : STree E}
    (hf : v.first = u.first) (hw : v.weight = u.weight) : (t.replace p v).key = t.key := by
  rw [key, key, first_replace h hf, weight_replace h hw]

lemma rootF_replace : ∀ (t : STree (BE E)) {p : List ℕ}, p ≠ [] → ∀ u : STree (BE E),
    rootF (t.replace p u) = rootF t
  | _, [], h, _ => absurd rfl h
  | leaf _, _ :: _, _, _ => rfl
  | node _ _, _ :: _, _, _ => rfl

lemma get?_setF (x : ℕ ×ₗ ℕ) (b : Bool) : ∀ (t : STree (BE E)) (p : List ℕ),
    (setF x b t).get? p = (t.get? p).map (setF x b)
  | t, [] => by simp
  | leaf _, _ :: _ => rfl
  | @node _ k d c, i :: p => by
    rw [setF_node, get?_node_cons, get?_node_cons]
    split_ifs with h
    · exact get?_setF x b (c ⟨i, h⟩) p
    · rfl

/-- **Setting a flag commutes with replacing a subtree** by one with the same key. -/
theorem setF_replace (x : ℕ ×ₗ ℕ) (b : Bool) : ∀ {t w : STree (BE E)} {p : List ℕ},
    t.get? p = some w → ∀ {u : STree (BE E)}, u.first = w.first → u.weight = w.weight →
    setF x b (t.replace p u) = (setF x b t).replace p (setF x b u)
  | t, w, [], _, u, _, _ => by rw [replace_nil, replace_nil]
  | leaf _, _, _ :: _, h, _, _, _ => by simp at h
  | @node _ k d c, w, i :: p, h, u, hf, hw => by
    have h' := h
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    rw [replace_node_cons, setF_node, setF_node, replace_node_cons,
      ← replace_node_cons, key_replace h' hf hw]
    congr 1
    funext j
    split_ifs with hj
    · have : j = ⟨i, hi⟩ := Fin.ext hj
      subst this
      exact setF_replace x b h hf hw
    · rfl

/-- **The cuts of a replaced tree** only depend on the key and the cuts of the replacing tree. -/
theorem cutKeys_replace_congr : ∀ {t w : STree (BE E)} {p : List ℕ}, t.get? p = some w →
    ∀ {u u' : STree (BE E)}, u.first = w.first → u.weight = w.weight → u'.first = w.first →
    u'.weight = w.weight → cutKeys u = cutKeys u' →
    cutKeys (t.replace p u) = cutKeys (t.replace p u')
  | t, w, [], _, u, u', _, _, _, _, h => by rw [replace_nil, replace_nil, h]
  | leaf _, _, _ :: _, h, _, _, _, _, _, _, _ => by simp at h
  | @node _ k d c, w, i :: p, h, u, u', hf, hw, hf', hw', hc => by
    have h' := h
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    have hk : key (node d c |>.replace (i :: p) u) = key (node d c |>.replace (i :: p) u') := by
      rw [key_replace h' hf hw, key_replace h' hf' hw']
    rw [replace_node_cons, replace_node_cons] at hk ⊢
    rw [cutKeys, cutKeys, hk]
    congr 1
    refine Finset.biUnion_congr rfl fun j _ => ?_
    split_ifs with hj
    · have : j = ⟨i, hi⟩ := Fin.ext hj
      subst this
      exact cutKeys_replace_congr h hf hw hf' hw' hc
    · rfl

/-- **The cuts of a substituted tree with no cuts** are those of the substituted trees. -/
theorem mem_cutKeys_allF_subst : ∀ (g : STree E) (xs : ℕ → STree (BE E)) (y : ℕ ×ₗ ℕ),
    y ∈ cutKeys ((allF g).subst xs) ↔ ∃ a ∈ g.labels, y ∈ cutKeys (xs a)
  | leaf a, xs, y => by simp
  | node e c, xs, y => by
    rw [allF_node, subst_node, mem_cutKeys_node]
    simp only [Bool.false_eq_true, false_and, false_or, mem_cutKeys_allF_subst, labels_node,
      Multiset.mem_sum, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, a, ha, hy⟩
      exact ⟨a, ⟨i, ha⟩, hy⟩
    · rintro ⟨a, ⟨i, ha⟩, hy⟩
      exact ⟨i, a, ha, hy⟩

/-- **The cuts of a substituted tree flagged at the root.** -/
theorem mem_cutKeys_fl_subst {k : ℕ} (b : Bool) (e : E k) (c : Fin k → STree E)
    (xs : ℕ → STree (BE E)) (y : ℕ ×ₗ ℕ) :
    y ∈ cutKeys ((fl b (node e c)).subst xs) ↔
      (b = true ∧ y = key ((fl b (node e c)).subst xs)) ∨
        ∃ a ∈ (node e c).labels, y ∈ cutKeys (xs a) := by
  rw [fl_node, subst_node, mem_cutKeys_node]
  simp only [mem_cutKeys_allF_subst, labels_node, Multiset.mem_sum, Finset.mem_univ, true_and]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨i, a, ha, hy⟩
    exact ⟨a, ⟨i, ha⟩, hy⟩
  · rintro ⟨a, ⟨i, ha⟩, hy⟩
    exact ⟨i, a, ha, hy⟩

/-- **Merging in a substituted tree with no cuts** merges in the substituted trees. -/
theorem setF_false_allF_subst (x : ℕ ×ₗ ℕ) : ∀ (g : STree E) (xs : ℕ → STree (BE E)),
    setF x false ((allF g).subst xs) = (allF g).subst fun a => setF x false (xs a)
  | leaf _, _ => rfl
  | node e c, xs => by
    rw [allF_node, subst_node, subst_node, setF_node]
    simp only [ite_self]
    congr 1
    funext i
    exact setF_false_allF_subst x (c i) xs

/-- **Merging in a substituted tree flagged at the root.** -/
theorem setF_false_fl_subst (x : ℕ ×ₗ ℕ) (b : Bool) (g : STree E) (xs : ℕ → STree (BE E)) :
    setF x false ((fl b g).subst xs) =
      (fl (if key ((fl b g).subst xs) = x then false else b) g).subst
        fun a => setF x false (xs a) := by
  cases g with
  | leaf a => rfl
  | node e c =>
    rw [fl_node, subst_node, setF_node, fl_node, subst_node]
    congr 1
    funext i
    exact setF_false_allF_subst x (c i) xs

/-! ## Bar monomials and the differential -/

section BarMono

variable {A : Finset ℕ}

/-- **The underlying monomial** of a bar monomial. -/
def forgetM (X : SMono (BE E) A) : SMono E A :=
  ⟨forget X.1, (isShuffle_forget _).2 X.isShuffle, by rw [labels_forget]; exact X.labels_eq⟩

/-- **A monomial with its root flagged** `b` and no cuts. -/
def flM (b : Bool) (g : SMono E A) : SMono (BE E) A :=
  ⟨fl b g.1, (isShuffle_fl _ _).2 g.isShuffle, by rw [labels_fl]; exact g.labels_eq⟩

/-- **Set the flag** of the vertex with key `x` of a bar monomial. -/
def setM (x : ℕ ×ₗ ℕ) (b : Bool) (X : SMono (BE E) A) : SMono (BE E) A :=
  ⟨setF x b X.1, (isShuffle_setF _ _ _).2 X.isShuffle, by rw [labels_setF]; exact X.labels_eq⟩

/-- **The cut edges** of a bar monomial. -/
def cuts (X : SMono (BE E) A) : Finset (ℕ ×ₗ ℕ) := cutKeys X.1

@[simp] lemma forgetM_val (X : SMono (BE E) A) : (forgetM X).1 = forget X.1 := rfl

@[simp] lemma flM_val (b : Bool) (g : SMono E A) : (flM b g).1 = fl b g.1 := rfl

@[simp] lemma setM_val (x : ℕ ×ₗ ℕ) (b : Bool) (X : SMono (BE E) A) :
    (setM x b X).1 = setF x b X.1 := rfl

@[simp] lemma forgetM_flM (b : Bool) (g : SMono E A) : forgetM (flM b g) = g :=
  Subtype.ext (forget_fl b g.1)

@[simp] lemma forgetM_setM (x : ℕ ×ₗ ℕ) (b : Bool) (X : SMono (BE E) A) :
    forgetM (setM x b X) = forgetM X :=
  Subtype.ext (forget_setF x b X.1)

/-- **A bar context forgets to a context.** -/
theorem IsSCtx.forget {B : Finset ℕ} {f : SMono (BE E) A → SMono (BE E) B} (hf : IsSCtx f) :
    ∃ f₀ : SMono E A → SMono E B, IsSCtx f₀ ∧ ∀ X, forgetM (f X) = f₀ (forgetM X) := by
  obtain ⟨T, p, xs, hp, hxs, hf⟩ := hf
  have key : ∀ X : SMono (BE E) A, (forgetM (f X)).1 =
      (STree.forget T).replace p ((forgetM X).1.subst fun a => (xs a).forget) := by
    intro X
    rw [forgetM_val, hf, forget_replace, forget_subst, forgetM_val]
  refine ⟨fun g => forgetM (f (flM false g)), ⟨STree.forget T, p, fun a => (xs a).forget, ?_,
    ⟨fun a ha => (isShuffle_forget _).2 (hxs.shuffle a ha),
      fun a ha b hb => hxs.labels a ha b (by rwa [labels_forget] at hb),
      fun a ha a' ha' h => by simpa only [first_forget] using hxs.mono ha ha' h⟩,
    fun g => by rw [key, forgetM_flM]⟩, fun X => Subtype.ext ?_⟩
  · rw [get?_forget]
    cases h : T.get? p
    · rw [h] at hp
      exact absurd hp (by simp)
    · rfl
  · rw [key, key, forgetM_flM]

end BarMono

namespace Bar

variable {A : Finset ℕ} (K : Type*) [CommRing K]

/-- **The differential of the bar construction** of the free shuffle operad: merge along each
cut edge, with the sign of its position among the cut edges. -/
noncomputable def d : (SMono (BE E) A →₀ K) →ₗ[K] (SMono (BE E) A →₀ K) :=
  CutComplex.d cuts fun x => setM x false

/-- **The differential of the bar construction squares to zero.** -/
theorem d_d (v : SMono (BE E) A →₀ K) : d K (d K v) = 0 :=
  CutComplex.d_d _ _ (fun X k _ => cutKeys_setF_false k X.1) (fun X k _ k' _ => by
    by_cases h : k = k'
    · rw [h]
    · exact Subtype.ext (setF_comm h false false X.1)) v

end Bar

/-! ## The flagged rewriting system -/

/-- **The admissible order on bar monomials**: compare the underlying monomials. -/
def AdmOrder.bar (O : AdmOrder E) : AdmOrder (BE E) where
  lt X Y := O.lt (forgetM X) (forgetM Y)
  wf A := InvImage.wf forgetM (O.wf A)
  trans := O.trans
  lt_ctx hf X Y h := by
    obtain ⟨f₀, hf₀, he⟩ := IsSCtx.forget hf
    rw [he, he]
    exact O.lt_ctx hf₀ h

end STree

open STree

variable {E : ℕ → Type v} {K : Type*} [CommRing K] {ρ : Type*} {O : STree.AdmOrder E}

/-- **The flagged rules** of rules on shuffle monomials: each rule with its root flagged either
way, acting on bar monomials at the uncut edges. -/
noncomputable def Rules.bar (G : Rules K ρ O.toCtxOrder) : Rules K (ρ × Bool) O.bar.toCtxOrder where
  src r := G.src r.1
  lead r := flM r.2 (G.lead r.1)
  tail r := Finsupp.mapDomain (flM r.2) (G.tail r.1)
  tail_lt r m hm := by
    classical
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hm)
    show O.lt (forgetM (flM _ m')) (forgetM (flM _ _))
    rw [forgetM_flM, forgetM_flM]
    exact G.tail_lt r.1 m' hm'

namespace STree

/-! ## Windows of the flagged rules -/

lemma first_fl_subst_eq {C : Finset ℕ} (m L : SMono E C) (b : Bool) (xs : ℕ → STree (BE E)) :
    ((fl b m.1).subst xs).first = ((fl b L.1).subst xs).first := by
  rw [first_subst ((isShuffle_fl b _).2 m.isShuffle),
    first_subst ((isShuffle_fl b _).2 L.isShuffle), first_fl, first_fl, m.first_eq L]

lemma rootF_fl_subst {g : STree E} (hg : ∀ a, g ≠ leaf a) (b : Bool) (xs : ℕ → STree (BE E)) :
    rootF ((fl b g).subst xs) = b := by
  cases g with
  | leaf a => exact absurd rfl (hg a)
  | node e c => rfl

section Window

variable {C : Finset ℕ} {m L : SMono E C} (hw : m.1.weight = L.1.weight) (b : Bool)
  (xs : ℕ → STree (BE E))
include hw

lemma weight_fl_subst_eq : ((fl b m.1).subst xs).weight = ((fl b L.1).subst xs).weight := by
  rw [weight_subst, weight_subst, weight_fl, weight_fl, labels_fl, labels_fl, hw, m.labels_eq,
    L.labels_eq]

lemma key_fl_subst_eq : ((fl b m.1).subst xs).key = ((fl b L.1).subst xs).key := by
  rw [key, key, first_fl_subst_eq m L b xs, weight_fl_subst_eq hw b xs]

omit hw in
include hw in
lemma not_leaf_of_weight (hL : ∀ a, L.1 ≠ leaf a) : ∀ a, m.1 ≠ leaf a := by
  intro a ha
  rcases hL' : L.1 with a' | ⟨e, c⟩
  · exact absurd hL' (hL a')
  have := hw
  rw [ha, hL', weight_leaf, weight_node] at this
  omega

lemma cutKeys_fl_subst_eq (hL : ∀ a, L.1 ≠ leaf a) :
    cutKeys ((fl b m.1).subst xs) = cutKeys ((fl b L.1).subst xs) := by
  have hm := not_leaf_of_weight hw hL
  have hk := key_fl_subst_eq hw b xs
  ext y
  rcases hL' : L.1 with a | ⟨e, c⟩
  · exact absurd hL' (hL a)
  rcases hm' : m.1 with a | ⟨e', c'⟩
  · exact absurd hm' (hm a)
  rw [hL', hm'] at hk
  rw [mem_cutKeys_fl_subst, mem_cutKeys_fl_subst, hk, ← hL', ← hm', m.labels_eq, L.labels_eq]

end Window

variable {A C : Finset ℕ}

/-- **Merging in an occurrence of a flagged monomial**: in the monomials `f (flM b m)` of a
context `f`, for monomials `m` with as many vertices as `L`, the cut edges are the same, and
merging along a cut edge is applying another context to `m` flagged at the root. -/
theorem exists_merge_ctx {f : SMono (BE E) C → SMono (BE E) A} (hf : IsSCtx f) (L : SMono E C)
    (hL : ∀ a, L.1 ≠ leaf a) (b : Bool) :
    ∃ (fk : (ℕ ×ₗ ℕ) → SMono (BE E) C → SMono (BE E) A) (b' : ℕ ×ₗ ℕ → Bool),
      (∀ k, IsSCtx (fk k)) ∧ ∀ m : SMono E C, m.1.weight = L.1.weight →
        cuts (f (flM b m)) = cuts (f (flM b L)) ∧
          rootF (f (flM b m)).1 = rootF (f (flM b L)).1 ∧
          (f (flM b m)).1.weight = (f (flM b L)).1.weight ∧
          ∀ k, setM k false (f (flM b m)) = fk k (flM (b' k) m) := by
  obtain ⟨p, xs, hget, hin, hrep⟩ := IsSCtx.normal hf (flM b L)
  set Tt := (f (flM b L)).1 with hTt
  let b' : ℕ ×ₗ ℕ → Bool := fun k => if key ((fl b L.1).subst xs) = k then false else b
  have hget' : ∀ k, (setM k false (f (flM b L))).1.get? p =
      some ((flM (b' k) L).1.subst fun a => setF k false (xs a)) := fun k => by
    rw [setM_val, get?_setF, hget]
    exact congrArg some (setF_false_fl_subst k b L.1 xs)
  have hmono : ∀ k, StrictMonoOn (fun a => (setF k false (xs a)).first) (C : Set ℕ) :=
    fun k a ha a' ha' h => by simpa only [first_setF] using hin.mono ha ha' h
  refine ⟨fun k => ctxOf (setM k false (f (flM b L))) p (flM (b' k) L) _ (hget' k) (hmono k),
    b', fun k => isSCtx_ctxOf _ _ _ _ _ _, fun m hw => ?_⟩
  have hm : (f (flM b m)).1 = Tt.replace p ((fl b m.1).subst xs) := hrep (flM b m)
  have hTt' : Tt = Tt.replace p ((fl b L.1).subst xs) := (replace_self hget).symm
  have hf1 := first_fl_subst_eq m L b xs
  have hw1 := weight_fl_subst_eq hw b xs
  refine ⟨?_, ?_, ?_, fun k => ?_⟩
  · show cutKeys (f (flM b m)).1 = cutKeys Tt
    rw [hm]
    conv_rhs => rw [hTt']
    exact cutKeys_replace_congr hget hf1 hw1 rfl rfl (cutKeys_fl_subst_eq hw b xs hL)
  · rw [hm]
    rcases p with _ | ⟨i, p⟩
    · rw [replace_nil, hTt', replace_nil, rootF_fl_subst hL b xs,
        rootF_fl_subst (not_leaf_of_weight hw hL) b xs]
    · rw [rootF_replace _ (List.cons_ne_nil i p), hTt',
        rootF_replace _ (List.cons_ne_nil i p)]
  · rw [hm, weight_replace hget hw1]
  · apply Subtype.ext
    rw [setM_val, ctxOf_val, hm, setF_replace k false hget hf1 hw1, setF_false_fl_subst,
      key_fl_subst_eq hw b xs]
    rfl

end STree

open STree

variable (G : Rules K ρ O.toCtxOrder)

/-- **Reductions of the flagged rules keep the cuts**, the root flag and the number of
vertices, when the rules are homogeneous. -/
theorem Rules.bar_red_inv (hlead : ∀ r a, (G.lead r).1 ≠ leaf a)
    (hom : ∀ r, ∀ m ∈ (G.tail r).support, m.1.weight = (G.lead r).1.weight)
    {A : Finset ℕ} {X : SMono (BE E) A} {v : SMono (BE E) A →₀ K}
    (hv : v ∈ (G.bar.rw A).red X) :
    v ∈ Finsupp.supported K K {Y | cuts Y = cuts X ∧ rootF Y.1 = rootF X.1 ∧
      Y.1.weight = X.1.weight} := by
  classical
  obtain ⟨⟨r, b⟩, f, hf, rfl, rfl⟩ := hv
  obtain ⟨fk, b', -, H⟩ := exists_merge_ctx hf (G.lead r) (hlead r) b
  intro Y hY
  have hY' : Y ∈ (Finsupp.mapDomain (f ∘ flM b) (G.tail r)).support := by
    rw [Finsupp.mapDomain_comp]
    exact hY
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hY')
  obtain ⟨h1, h2, h3, -⟩ := H m (hom r m hm)
  exact ⟨h1, h2, h3⟩

/-- **The ideal of the flagged rules is a subcomplex** of the bar construction of the free
shuffle operad, when the rules are homogeneous: the differential maps it into itself. So the
differential passes to the quotient, the bar construction of the operad presented by the
rules. -/
theorem Rules.bar_d_mem_ideal (hlead : ∀ r a, (G.lead r).1 ≠ leaf a)
    (hom : ∀ r, ∀ m ∈ (G.tail r).support, m.1.weight = (G.lead r).1.weight)
    {A : Finset ℕ} {v : SMono (BE E) A →₀ K} (hv : v ∈ (G.bar.rw A).ideal) :
    Bar.d K v ∈ (G.bar.rw A).ideal := by
  classical
  rw [Rules.ideal_eq_span] at hv ⊢
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨r, b⟩, f, hf, rfl⟩ := hx
    obtain ⟨fk, b', hfk, H⟩ := exists_merge_ctx hf (G.lead r) (hlead r) b
    set w := Finsupp.single (G.lead r) (1 : K) - G.tail r with hw
    have hx : Finsupp.mapDomain f (Finsupp.single (G.bar.lead (r, b)) 1 - G.bar.tail (r, b)) =
        Finsupp.mapDomain (f ∘ flM b) w := by
      rw [Finsupp.mapDomain_comp]
      congr 1
      rw [hw]
      have := Finsupp.mapDomain_sub (f := flM b) (v₁ := Finsupp.single (G.lead r) (1 : K))
        (v₂ := G.tail r)
      rw [Finsupp.mapDomain_single] at this
      exact this.symm
    have hwm : ∀ m ∈ w.support, m.1.weight = (G.lead r).1.weight := by
      intro m hm
      rcases Finset.mem_union.1 (Finsupp.support_sub hm) with h | h
      · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
      · exact hom r m h
    set S := cuts (f (flM b (G.lead r)))
    have hdX : ∀ m ∈ w.support, CutComplex.dX cuts (fun x => setM x false) (f (flM b m)) =
        ∑ k ∈ S, CutComplex.sgn K S k • Finsupp.single (fk k (flM (b' k) m)) (1 : K) := by
      intro m hm
      obtain ⟨h1, -, -, h4⟩ := H m (hwm m hm)
      rw [CutComplex.dX, h1]
      exact Finset.sum_congr rfl fun k _ => by rw [h4 k]
    rw [hx, Bar.d, CutComplex.d, Finsupp.linearCombination_mapDomain,
      Finsupp.linearCombination_apply, Finsupp.sum,
      Finset.sum_congr rfl fun m hm => by rw [Function.comp_apply, Function.comp_apply, hdX m hm]]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Submodule.sum_mem _ fun k _ => ?_
    have e : ∑ m ∈ w.support, w m • CutComplex.sgn K S k • Finsupp.single (fk k (flM (b' k) m)) 1 =
        CutComplex.sgn K S k • Finsupp.mapDomain (fk k ∘ flM (b' k)) w := by
      rw [Finsupp.mapDomain, Finsupp.sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_comm, Finsupp.smul_single_one]
      rfl
    have hk : Finsupp.mapDomain (fk k ∘ flM (b' k)) w = Finsupp.mapDomain (fk k)
        (Finsupp.single (G.bar.lead (r, b' k)) 1 - G.bar.tail (r, b' k)) := by
      rw [Finsupp.mapDomain_comp]
      congr 1
      rw [hw]
      have := Finsupp.mapDomain_sub (f := flM (b' k)) (v₁ := Finsupp.single (G.lead r) (1 : K))
        (v₂ := G.tail r)
      rw [Finsupp.mapDomain_single] at this
      exact this
    have key : CutComplex.sgn K S k • Finsupp.mapDomain (fk k ∘ flM (b' k)) w ∈ Submodule.span K
        {x | ∃ r f, O.bar.toCtxOrder.IsCtx f ∧
          x = Finsupp.mapDomain f (Finsupp.single (G.bar.lead r) 1 - G.bar.tail r)} := by
      rw [hk]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(r, b' k), fk k, hfk k, rfl⟩)
    rw [← e] at key
    exact key
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end Operad
