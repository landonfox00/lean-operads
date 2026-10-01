/-
# Koszulness of shuffle operads with a quadratic Gröbner basis

**The criterion of Dotsenko and Khoroshkin** (`isKoszul`): a shuffle operad presented by
relators of arity three which are a quadratic Gröbner basis (`LTree.IsGroebner`) is Koszul.

The bar construction of the free shuffle operad on binary generators has a basis of bar trees
(`Operad.ShuffleBar`); in arity `n` and degree `s` (the number of components) it is `C n s`. That
of the operad presented by relators `R` is its quotient by the subcomplex `J R` spanned by the
relators substituted at the uncut edges, and **Koszulness** (`IsKoszul`) is the vanishing of its
homology below the diagonal: every cycle of degree `s < n - 1` modulo `J R` is a boundary modulo
`J R`. The proof is Hoffbeck's argument for PBW bases, the filtration by the path-lexicographic key
of the underlying monomial.

* **The leading part of the differential** (`d₀`) merges only along the cut edges whose window is
  not a leading monomial (`Nkeys`), which keeps a normal bar tree normal (`normalBar_mergeK_iff`).
  For a fixed underlying monomial it is the complex of the subsets of a finite set; cutting the
  least mergeable edge is a contracting homotopy (`d₀_hTree_add`) as soon as there is a mergeable
  edge, which is the case below the diagonal (`nkeys_nonempty`).
* **Components.** A bar tree is its top component (`top`), a monomial, with the cut subtrees below
  it grafted (`hang`, `plug_top`). A substitution at an uncut edge happens in the top component or
  inside one hanging subtree (`top_hang_substBar`).
* **Normalizing the components** (`Φ`, `ΦL`): each component replaced by its normal form
  (`LTree.IsGroebner.nf`), from the top down, by multilinear grafting (`graftL`). It fixes the
  normal bar trees (`Φ_of_normal`) and kills the substituted relators (`Φ_substRel`), because the
  normal forms of the substitutions of a relator cancel in the component where they happen.
* **Reduction** (`reduce`): a bar tree which is not normal is congruent modulo `J R` to normal bar
  trees of lower level (`lev`, the rank of the key of the underlying monomial), substituting at an
  uncut edge with a leading window the relator it leads. So normalization is congruent to the
  identity (`ΦL_spec`), and modulo `J R` the differential of a normal bar tree is its leading part
  plus terms of lower level (`ΦL_dTree_sub`).
* **Acyclicity** (`acyclic`), by induction on the level: the leading part of a cycle is a cycle of
  `d₀`, hence the boundary of its homotopy, and what remains is a cycle of lower level.
-/
import Operad.ShuffleBar

universe u v

namespace Operad

namespace ShuffleBar

open LTree

variable {E : Type v} (K : Type u) [Field K] (L : Set (LTree E))

/-! ## The leading part of the differential -/

open Classical in
/-- The keys of the edges whose window is a leading monomial. -/
noncomputable def Lkeys (T : LTree E) : Finset (ℕ ×ₗ ℕ) :=
  ((T.edgeWins.filter fun kw => kw.2 ∈ L).map Prod.fst).toFinset

/-- **The mergeable edges** of a monomial: those whose window is not a leading monomial. -/
noncomputable def Nkeys (T : LTree E) : Finset (ℕ ×ₗ ℕ) := T.edgeKeys \ Lkeys L T

lemma mem_Lkeys {T : LTree E} {k : ℕ ×ₗ ℕ} : k ∈ Lkeys L T ↔ ∃ w ∈ L, (k, w) ∈ T.edgeWins := by
  classical
  simp only [Lkeys, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k', w⟩, ⟨hw, hL⟩, rfl⟩
    exact ⟨w, hL, hw⟩
  · rintro ⟨w, hL, hw⟩
    exact ⟨(k, w), ⟨hw, hL⟩, rfl⟩

/-- A normal bar tree cuts every edge whose window is a leading monomial. -/
lemma Lkeys_subset_cutKeys {x : BarTree E} (h : NormalBar L x) :
    Lkeys L (x.mapDec Prod.fst) ⊆ cutKeys x := fun k hk => by
  obtain ⟨w, hL, hw⟩ := (mem_Lkeys L).1 hk
  by_contra hc
  exact h (k, w) hw hc hL

/-- **Merging along a mergeable edge keeps a bar tree normal**, and along another edge does not. -/
lemma normalBar_mergeK_iff {x : BarTree E} (hnd : x.labels.Nodup) (hN : NormalBar L x)
    {k : ℕ ×ₗ ℕ} (hk : k ∈ cutKeys x) :
    NormalBar L (mergeK x k) ↔ k ∉ Lkeys L (x.mapDec Prod.fst) := by
  rw [normalBar_mergeK hnd hk, mem_Lkeys]
  constructor
  · rintro ⟨-, h⟩ ⟨w, hL, hw⟩
    exact h w hw hL
  · intro h
    exact ⟨hN, fun w hw hL => h ⟨w, hL, hw⟩⟩

/-- **The leading part of the differential of a bar tree**: the merges along its mergeable cut
edges. -/
noncomputable def d₀Tree (x : BarTree E) : BarTree E →₀ K :=
  ∑ k ∈ (cutKeys x).filter (· ∈ Nkeys L (x.mapDec Prod.fst)),
    sgn K x k • Finsupp.single (mergeK x k) 1

/-- **The leading part of the differential.** -/
noncomputable def d₀ : (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) :=
  Finsupp.linearCombination K (d₀Tree K L)

@[simp] lemma d₀_single (x : BarTree E) (c : K) :
    d₀ K L (Finsupp.single x c) = c • d₀Tree K L x := by
  simp [d₀]

/-- **The contracting homotopy on a bar tree**: cut its least mergeable edge, if it is uncut. -/
noncomputable def hTree (x : BarTree E) : BarTree E →₀ K :=
  if hne : (Nkeys L (x.mapDec Prod.fst)).Nonempty then
    if (Nkeys L (x.mapDec Prod.fst)).min' hne ∈ cutKeys x then 0
    else sgn K (cutK x ((Nkeys L (x.mapDec Prod.fst)).min' hne))
      ((Nkeys L (x.mapDec Prod.fst)).min' hne) •
        Finsupp.single (cutK x ((Nkeys L (x.mapDec Prod.fst)).min' hne)) 1
  else 0

/-- **The contracting homotopy.** -/
noncomputable def hL : (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) :=
  Finsupp.linearCombination K (hTree K L)

@[simp] lemma hL_single (x : BarTree E) (c : K) :
    hL K L (Finsupp.single x c) = c • hTree K L x := by
  simp [hL]

lemma sgn_mul_self (x : BarTree E) (k : ℕ ×ₗ ℕ) : sgn K x k * sgn K x k = 1 := by
  rw [sgn, ← pow_add, ← two_mul, pow_mul]
  simp

lemma sgn_cutK {x : BarTree E} (hnd : x.labels.Nodup) {k₀ : ℕ ×ₗ ℕ}
    (hk₀ : k₀ ∈ (x.mapDec Prod.fst).edgeKeys) (hc : k₀ ∉ cutKeys x) (k : ℕ ×ₗ ℕ) :
    sgn K (cutK x k₀) k = (if k₀ < k then -1 else 1) * sgn K x k := by
  unfold sgn
  rw [cutKeys_cutK hnd hk₀, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => hc (Finset.mem_filter.1 h').1), pow_succ]
    ring
  · rw [one_mul]

/-- **The homotopy formula** on a normal bar tree with a mergeable edge. -/
theorem d₀_hTree_add {x : BarTree E} (hnd : x.labels.Nodup) (hx : rootFlag x = false)
    (hne : (Nkeys L (x.mapDec Prod.fst)).Nonempty) :
    d₀ K L (hTree K L x) + hL K L (d₀Tree K L x) = Finsupp.single x 1 := by
  set T := x.mapDec Prod.fst with hT
  set k₀ := (Nkeys L T).min' hne with hk₀def
  have hk₀N : k₀ ∈ Nkeys L T := Finset.min'_mem _ hne
  have hk₀E : k₀ ∈ T.edgeKeys := (Finset.mem_sdiff.1 hk₀N).1
  have hmin : ∀ k ∈ Nkeys L T, k ≠ k₀ → k₀ < k := fun k hk hkk =>
    lt_of_le_of_ne (Finset.min'_le _ k hk) (Ne.symm hkk)
  -- the homotopy of a merge, along a mergeable edge other than `k₀`
  have hT_merge : ∀ k ∈ cutKeys x, (mergeK x k).mapDec Prod.fst = T := fun k _ => full_mergeK k x
  by_cases hc : k₀ ∈ cutKeys x
  · -- the least mergeable edge is cut: only the merge along it survives the homotopy
    have hh : hTree K L x = 0 := by
      simp only [hTree, ← hT, dif_pos hne, ← hk₀def, if_pos hc]
    rw [hh, map_zero, zero_add, d₀Tree, map_sum]
    rw [Finset.sum_eq_single k₀]
    · rw [map_smul, hL_single, one_smul, hTree, full_mergeK, ← hT, dif_pos hne, ← hk₀def,
        cutKeys_mergeK x hnd hc, if_neg (Finset.notMem_erase k₀ _), cutK_mergeK hnd hx hc,
        smul_smul, sgn_mul_self, one_smul]
    · intro k hk hkk
      have hk' := (Finset.mem_filter.1 hk).1
      rw [map_smul, hL_single, one_smul, hTree, full_mergeK, ← hT, dif_pos hne, ← hk₀def,
        cutKeys_mergeK x hnd hk', if_pos (Finset.mem_erase.2 ⟨Ne.symm hkk, hc⟩), smul_zero]
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨hc, hk₀N⟩) h
  · -- the least mergeable edge is uncut: cut it
    set y := cutK x k₀ with hy
    have hcy : cutKeys y = insert k₀ (cutKeys x) := cutKeys_cutK hnd hk₀E
    have hh : hTree K L x = sgn K y k₀ • Finsupp.single y 1 := by
      simp only [hTree, ← hT, dif_pos hne, ← hk₀def, if_neg hc, hy]
    have hfy : y.mapDec Prod.fst = T := full_cutK k₀ x
    have hfilter : (cutKeys y).filter (· ∈ Nkeys L (y.mapDec Prod.fst)) =
        insert k₀ ((cutKeys x).filter (· ∈ Nkeys L T)) := by
      rw [hfy, hcy, Finset.filter_insert, if_pos hk₀N]
    have hnot : k₀ ∉ (cutKeys x).filter (· ∈ Nkeys L T) := fun h => hc (Finset.mem_filter.1 h).1
    rw [hh, map_smul, d₀_single, one_smul, d₀Tree, hfilter, Finset.sum_insert hnot,
      mergeK_cutK hx hc, d₀Tree, map_sum, smul_add, smul_smul, sgn_mul_self, one_smul,
      add_assoc, Finset.smul_sum, ← Finset.sum_add_distrib]
    conv_rhs => rw [← add_zero (Finsupp.single x (1 : K))]
    congr 1
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hkc, hkN⟩ := Finset.mem_filter.1 hk
    have hkk : k ≠ k₀ := fun h => hc (h ▸ hkc)
    have hlt : k₀ < k := hmin k hkN hkk
    -- the homotopy of `mergeK x k`
    set z := mergeK x k with hz
    have hcz : cutKeys z = (cutKeys x).erase k := cutKeys_mergeK x hnd hkc
    have hk₀z : k₀ ∉ cutKeys z := by rw [hcz]; exact fun h => hc (Finset.mem_of_mem_erase h)
    have hfz : z.mapDec Prod.fst = T := by rw [hz]; exact full_mergeK k x
    have hhz : hTree K L z = sgn K (cutK z k₀) k₀ • Finsupp.single (cutK z k₀) 1 := by
      simp only [hTree, hfz, dif_pos hne, ← hk₀def, if_neg hk₀z]
    have hnz : z.labels.Nodup := by rw [hz, labels_mergeK]; exact hnd
    have hk₀Ez : k₀ ∈ (z.mapDec Prod.fst).edgeKeys := by rw [hz, full_mergeK]; exact hk₀E
    have hs1 : sgn K (cutK z k₀) k₀ = sgn K y k₀ := by
      rw [sgn_cutK K hnz hk₀Ez hk₀z, sgn_cutK K hnd hk₀E hc, if_neg (lt_irrefl _), one_mul,
        one_mul]
      unfold sgn
      have hnk : k ∉ (cutKeys x).filter (· < k₀) := fun h =>
        absurd (Finset.mem_filter.1 h).2 (not_lt.2 hlt.le)
      rw [hcz, Finset.filter_erase, Finset.erase_eq_of_notMem hnk]
    have hs2 : sgn K y k = -sgn K x k := by
      rw [hy, sgn_cutK K hnd hk₀E hc, if_pos hlt, neg_one_mul]
    rw [map_smul, hL_single, one_smul, hhz, hs1, hs2, mergeK_cutK_comm hkk, ← hz, smul_smul,
      smul_smul, ← add_smul]
    rw [mul_neg, mul_comm (sgn K x k), neg_add_cancel, zero_smul]

/-! ## Components -/

lemma _root_.Operad.LTree.plug_congr {X : Type*} {ins ins' : ℕ → LTree X} :
    ∀ {m : LTree X}, (∀ a ∈ m.labels, ins a = ins' a) → m.plug ins = m.plug ins'
  | leaf a, h => h a (by simp)
  | node e l r, h => by
    simp only [plug]
    rw [plug_congr fun a ha => h a (by simp [ha]), plug_congr fun a ha => h a (by simp [ha])]

section Components

/-- The part of a subtree in the component above it: a cut subtree becomes a leaf, labelled by its
least label. -/
def topAux : BarTree E → LTree E
  | leaf a => leaf a
  | node d l r => if d.2 then leaf (min l.minLabel r.minLabel) else node d.1 (topAux l) (topAux r)

/-- **The top component** of a bar tree, a monomial: the cut subtrees below it replaced by leaves
labelled by their least labels. -/
def top : BarTree E → LTree E
  | leaf a => leaf a
  | node d l r => node d.1 (topAux l) (topAux r)

/-- The cut subtree of least label `a` directly below the component above a subtree; the leaf `a`
if there is none. -/
def hangAux : BarTree E → ℕ → BarTree E
  | leaf _, a => leaf a
  | node d l r, a =>
    if d.2 then (if min l.minLabel r.minLabel = a then node d l r else leaf a)
    else if a ∈ (topAux l).labels then hangAux l a else hangAux r a

/-- **The cut subtrees hanging from the top component**, by least label; the leaf `a` for a leaf
of the top component which is a leaf of the bar tree. -/
def hang : BarTree E → ℕ → BarTree E
  | leaf _, a => leaf a
  | node _ l r, a => if a ∈ (topAux l).labels then hangAux l a else hangAux r a

lemma topAux_of_flag {d : E × Bool} {l r : BarTree E} (h : d.2 = false) :
    topAux (node d l r) = top (node d l r) := by
  simp [topAux, top, h]

lemma hangAux_of_flag {d : E × Bool} {l r : BarTree E} (h : d.2 = false) :
    hangAux (node d l r) = hang (node d l r) := by
  funext a
  simp [hangAux, hang, h]

@[simp] lemma minLabel_topAux : ∀ y : BarTree E, (topAux y).minLabel = y.minLabel
  | leaf _ => rfl
  | node d l r => by
    simp only [topAux]
    split_ifs
    · rfl
    · simp [minLabel_topAux l, minLabel_topAux r]

@[simp] lemma minLabel_top (y : BarTree E) : (top y).minLabel = y.minLabel := by
  cases y with
  | leaf => rfl
  | node d l r => simp [top]

lemma sublist_topAux : ∀ y : BarTree E, (topAux y).labels.Sublist y.labels
  | leaf _ => List.Sublist.refl _
  | node d l r => by
    simp only [topAux]
    split_ifs
    · simp only [labels_leaf, List.singleton_sublist]
      rw [← minLabel_node d l r]
      exact minLabel_mem _
    · exact (sublist_topAux l).append (sublist_topAux r)

lemma sublist_top (y : BarTree E) : (top y).labels.Sublist y.labels := by
  cases y with
  | leaf => exact List.Sublist.refl _
  | node d l r => exact (sublist_topAux l).append (sublist_topAux r)

lemma isShuffle_topAux : ∀ y : BarTree E, y.IsShuffle → (topAux y).IsShuffle
  | leaf _, _ => trivial
  | node d l r, h => by
    simp only [topAux]
    split_ifs
    · trivial
    · exact ⟨by simpa using h.1, isShuffle_topAux l h.2.1, isShuffle_topAux r h.2.2⟩

lemma isShuffle_top {y : BarTree E} (h : y.IsShuffle) : (top y).IsShuffle := by
  cases y with
  | leaf => trivial
  | node d l r => exact ⟨by simpa using h.1, isShuffle_topAux l h.2.1, isShuffle_topAux r h.2.2⟩

lemma nodup_top {y : BarTree E} (h : y.labels.Nodup) : (top y).labels.Nodup :=
  (sublist_top y).nodup h

lemma size_hangAux_le : ∀ (y : BarTree E) (a : ℕ), (hangAux y a).size ≤ y.size
  | leaf _, _ => le_rfl
  | node d l r, a => by
    simp only [hangAux]
    split_ifs
    · exact le_rfl
    · simp
    · have := size_hangAux_le l a
      simp only [size_node]
      omega
    · have := size_hangAux_le r a
      simp only [size_node]
      omega

lemma size_hang_lt (d : E × Bool) (l r : BarTree E) (a : ℕ) :
    (hang (node d l r) a).size < (node d l r).size := by
  simp only [hang]
  split_ifs
  · have := size_hangAux_le l a
    simp only [size_node]
    omega
  · have := size_hangAux_le r a
    simp only [size_node]
    omega

/-- The labels of the top part are the least labels of the hanging subtrees and the leaves. -/
lemma hangAux_of_not_mem : ∀ (y : BarTree E) (a : ℕ), a ∉ (topAux y).labels → hangAux y a = leaf a
  | leaf b, a, _ => rfl
  | node d l r, a, ha => by
    simp only [topAux] at ha
    simp only [hangAux]
    split_ifs at ha ⊢ with h1 h2 h3
    · simp [h2] at ha
    · rfl
    · simp only [labels_node, List.mem_append, not_or] at ha
      exact absurd h3 ha.1
    · simp only [labels_node, List.mem_append, not_or] at ha
      exact hangAux_of_not_mem r a ha.2

/-- **A subtree is its top part with the hanging subtrees grafted.** -/
theorem plug_topAux : ∀ y : BarTree E, y.labels.Nodup → (unflag (topAux y)).plug (hangAux y) = y
  | leaf a, _ => rfl
  | node d l r, hnd => by
    by_cases hd : d.2
    · simp [topAux, hd, plug, hangAux]
    · have hd' : d.2 = false := by simpa using hd
      have hl := plug_topAux l (List.nodup_append.1 hnd).1
      have hr := plug_topAux r (List.nodup_append.1 hnd).2.1
      simp only [topAux, hd', Bool.false_eq_true, if_false, mapDec_node, plug]
      have el : (unflag (topAux l)).plug (hangAux (node d l r)) = l := by
        refine (plug_congr fun a ha => ?_).trans hl
        rw [labels_mapDec] at ha
        simp [hangAux, hd', ha]
      have er : (unflag (topAux r)).plug (hangAux (node d l r)) = r := by
        refine (plug_congr fun a ha => ?_).trans hr
        rw [labels_mapDec] at ha
        have ha' : a ∉ (topAux l).labels := fun h =>
          ne_of_nodup_append hnd ((sublist_topAux l).subset h) ((sublist_topAux r).subset ha) rfl
        simp [hangAux, hd', ha']
      rw [el, er]
      obtain ⟨e, c⟩ := d
      simp only at hd'
      subst hd'
      rfl

/-- **A bar tree is its top component with the hanging subtrees grafted.** -/
theorem plug_top (y : BarTree E) (hnd : y.labels.Nodup) :
    (liftW (rootFlag y) (top y)).plug (hang y) = y := by
  cases y with
  | leaf => rfl
  | node d l r =>
    have := plug_topAux (node (d.1, false) l r) hnd
    simp only [topAux, Bool.false_eq_true, if_false, mapDec_node, plug, hangAux] at this
    simp only [top, liftW, plug, rootFlag]
    simp only [node.injEq] at this
    have e : hang (node d l r) =
        fun x => if x ∈ (topAux l).labels then hangAux l x else hangAux r x := rfl
    rw [e, this.2.1, this.2.2]

/-! ### Grafting onto the top component -/

/-- The hanging subtree of least label `a` among the inputs `ins k`, `k ∈ ks`, in order. -/
def pick (ins : ℕ → BarTree E) (a : ℕ) : List ℕ → BarTree E
  | [] => leaf a
  | k :: ks => if a ∈ (topAux (ins k)).labels then hangAux (ins k) a else pick ins a ks

lemma pick_append (ins : ℕ → BarTree E) (a : ℕ) : ∀ ks ks' : List ℕ,
    pick ins a (ks ++ ks') =
      if a ∈ ks.flatMap (fun k => (topAux (ins k)).labels) then pick ins a ks else pick ins a ks'
  | [], ks' => by simp
  | k :: ks, ks' => by
    simp only [List.cons_append, pick, List.flatMap_cons, List.mem_append]
    by_cases h : a ∈ (topAux (ins k)).labels
    · simp [h]
    · simp only [h, if_false, false_or]
      exact pick_append ins a ks ks'

lemma topAux_plug_unflag (ins : ℕ → BarTree E) :
    ∀ m : LTree E, topAux ((unflag m).plug ins) = m.plug fun k => topAux (ins k)
  | leaf _ => rfl
  | node e l r => by
    simp only [mapDec_node, plug, topAux, Bool.false_eq_true, if_false]
    rw [topAux_plug_unflag ins l, topAux_plug_unflag ins r]

lemma labels_topAux_plug_unflag (ins : ℕ → BarTree E) (m : LTree E) :
    (topAux ((unflag m).plug ins)).labels = m.labels.flatMap fun k => (topAux (ins k)).labels := by
  rw [topAux_plug_unflag, labels_plug]

lemma hangAux_plug_unflag (ins : ℕ → BarTree E) (a : ℕ) :
    ∀ m : LTree E, hangAux ((unflag m).plug ins) a = pick ins a m.labels
  | leaf k => by
    simp only [mapDec_leaf, plug, labels_leaf, pick]
    split_ifs with h
    · rfl
    · exact hangAux_of_not_mem _ a h
  | node e l r => by
    simp only [mapDec_node, plug, hangAux, Bool.false_eq_true, if_false, labels_node,
      pick_append, labels_topAux_plug_unflag]
    rw [hangAux_plug_unflag ins a l, hangAux_plug_unflag ins a r]

lemma top_plug_liftW (ins : ℕ → BarTree E) (c : Bool) (e : E) (l r : LTree E) :
    top ((liftW c (node e l r)).plug ins) = (node e l r).plug fun k => topAux (ins k) := by
  simp only [liftW, plug, top]
  rw [topAux_plug_unflag, topAux_plug_unflag]

lemma hang_plug_liftW (ins : ℕ → BarTree E) (c : Bool) (e : E) (l r : LTree E) (a : ℕ) :
    hang ((liftW c (node e l r)).plug ins) a = pick ins a (node e l r).labels := by
  simp only [liftW, plug, hang, labels_node, pick_append, labels_topAux_plug_unflag]
  rw [hangAux_plug_unflag, hangAux_plug_unflag]

/-- `pick` does not depend on the order of the inputs when their top parts have disjoint labels. -/
lemma pick_perm (ins : ℕ → BarTree E) (a : ℕ) {ks ks' : List ℕ} (h : ks.Perm ks')
    (hdisj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → a ∈ (topAux (ins k)).labels →
      a ∉ (topAux (ins k')).labels) (hnd : ks.Nodup) : pick ins a ks = pick ins a ks' := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp only [pick]
    rw [ih (fun k hk k' hk' => hdisj k (List.mem_cons_of_mem _ hk) k' (List.mem_cons_of_mem _ hk'))
      (List.nodup_cons.1 hnd).2]
  | swap x y l =>
    simp only [pick]
    have hxy : y ≠ x := fun h => by
      subst h
      exact (List.nodup_cons.1 hnd).1 List.mem_cons_self
    by_cases hx : a ∈ (topAux (ins x)).labels
    · by_cases hy : a ∈ (topAux (ins y)).labels
      · exact absurd hx (hdisj y (by simp) x (by simp) hxy hy)
      · simp [hx, hy]
    · by_cases hy : a ∈ (topAux (ins y)).labels <;> simp [hx, hy]
  | trans h₁ _ ih₁ ih₂ =>
    rw [ih₁ hdisj hnd, ih₂ (fun k hk k' hk' => hdisj k (h₁.symm.subset hk) k' (h₁.symm.subset hk'))
      (h₁.nodup_iff.1 hnd)]

lemma winIns_top : ∀ (y : BarTree E) (s : Bool), y.IsEdgeRoot s →
    rootFlag (y.subtreeAt [s]) = false →
    (top y).IsEdgeRoot s ∧ (top y).winIns s = fun k => topAux (y.winIns s k)
  | node d (node f a b) e, false, _, hf => by
    simp only [subtreeAt, rootFlag] at hf
    simp only [top, topAux, hf, Bool.false_eq_true, if_false]
    refine ⟨trivial, ?_⟩
    funext k
    simp only [winIns, winInputs, minLabel_topAux, ins3]
    split_ifs <;> rfl
  | node d e (node f a b), true, _, hf => by
    simp only [subtreeAt, rootFlag] at hf
    simp only [top, topAux, hf, Bool.false_eq_true, if_false]
    have e1 : (node d.1 (topAux e) (node f.1 (topAux a) (topAux b))).winInputs true =
        (topAux e, topAux a, topAux b) := by cases topAux e <;> rfl
    have e2 : (node d e (node f a b)).winInputs true = (e, a, b) := by cases e <;> rfl
    refine ⟨by cases topAux e <;> trivial, ?_⟩
    funext k
    simp only [winIns, e1, e2, ins3]
    split_ifs <;> rfl

lemma substBar_cons_false (d : E × Bool) (l r : BarTree E) (p : List Bool) (s : Bool)
    (σ : LTree E) : substBar (node d l r) (false :: p) s σ = node d (substBar l p s σ) r := rfl

lemma substBar_cons_true (d : E × Bool) (l r : BarTree E) (p : List Bool) (s : Bool)
    (σ : LTree E) : substBar (node d l r) (true :: p) s σ = node d l (substBar r p s σ) := rfl

lemma topAux_cut {d : E × Bool} {l r : BarTree E} (h : d.2 = true) :
    topAux (node d l r) = leaf (node d l r).minLabel := by
  simp [topAux, h]

lemma hangAux_cut {d : E × Bool} {l r : BarTree E} (h : d.2 = true) (a : ℕ) :
    hangAux (node d l r) a = if (node d l r).minLabel = a then node d l r else leaf a := by
  simp [hangAux, h]

lemma minLabel_substBar {x : BarTree E} {p : List Bool} {s : Bool} {σ : LTree E}
    (hs : x.IsShuffle) (hnd : x.labels.Nodup) (h : IsUncut x p s)
    (hσ : σ.labels.Perm (List.range 3)) : (substBar x p s σ).minLabel = x.minLabel :=
  minLabel_eq_of_perm (perm_labels_substBar hs hnd h hσ)

lemma topAux_eq_top {y : BarTree E} (h : rootFlag y = false) : topAux y = top y := by
  cases y with
  | leaf => rfl
  | node d l r => exact topAux_of_flag (by simpa [rootFlag] using h)

lemma hangAux_eq_hang {y : BarTree E} (h : rootFlag y = false) : hangAux y = hang y := by
  cases y with
  | leaf => rfl
  | node d l r => exact hangAux_of_flag (by simpa [rootFlag] using h)

section Subst

variable [Fintype E] [DecidableEq E]

/-- **Where a substitution happens**: at an uncut edge of the top component, which changes the
top component by the same substitution and keeps the hanging subtrees; or inside a hanging
subtree, which changes only that subtree. -/
theorem top_hang_substBar : ∀ (p : List Bool) (y : BarTree E) (s : Bool), y.IsShuffle →
    y.labels.Nodup → IsUncut y p s →
    ((top y).IsEdge p s ∧ ∀ σ : Mono E 3,
      top (substBar y p s σ.1) = (top y).substAt p s σ.1 ∧ hang (substBar y p s σ.1) = hang y) ∨
    ∃ a q, IsUncut (hang y a) q s ∧ (hang y a).size < y.size ∧ (hang y a).IsShuffle ∧
      (hang y a).labels.Nodup ∧ a ∈ (top y).labels ∧ ∀ σ : Mono E 3,
        top (substBar y p s σ.1) = top y ∧
          hang (substBar y p s σ.1) = Function.update (hang y) a (substBar (hang y a) q s σ.1)
  | [], y, s, hs, hnd, h => by
    have he : y.IsEdgeRoot s := by simpa [IsEdge] using h.1
    have hw := winSpec he hs hnd
    have hf : rootFlag (y.subtreeAt [s]) = false := h.2
    obtain ⟨hte, htw⟩ := winIns_top y s he hf
    have hwin := windowRoot_of_uncut y s he hf
    obtain ⟨-, hwl, e, wl, wr, hwe⟩ := windowRoot_shape (y.mapDec Prod.fst) s
      ((isEdgeRoot_mapDec _ y s).2 he) (by simpa using hs) (by simpa using hnd)
    have hdisj := winIns_disjoint (p := []) h.1 hs hnd
    simp only [subtreeAt_nil] at hdisj
    refine Or.inl ⟨by simpa [IsEdge] using hte, fun σ => ?_⟩
    obtain ⟨-, hσ, e', σl, σr, hσe⟩ := mono_shape σ
    have hsub : substBar y [] s σ.1 = (liftW (rootFlag y) σ.1).plug (y.winIns s) := by
      simp [substBar, substAt, flagAt]
    rw [hsub, hσe]
    refine ⟨?_, ?_⟩
    · rw [top_plug_liftW, substAt, subtreeAt_nil, replaceAt_nil, htw]
    · funext a
      rw [hang_plug_liftW]
      conv_rhs => rw [← hw.window, hwin, hwe, hang_plug_liftW]
      have hσ' : (node e' σl σr).labels.Perm (List.range 3) := hσe ▸ hσ
      have hw' : (node e wl wr).labels.Perm (List.range 3) := hwe ▸ hwl
      refine pick_perm _ a (hσ'.trans hw'.symm) (fun k hk k' hk' hkk ha ha' => ?_)
        (hσ'.nodup_iff.2 List.nodup_range)
      have hk3 := List.mem_range.1 (hσ'.subset hk)
      have hk3' := List.mem_range.1 (hσ'.subset hk')
      exact hdisj k hk3 k' hk3' hkk a ((sublist_topAux _).subset ha)
        ((sublist_topAux _).subset ha')
  | _ :: _, leaf _, s, _, _, h => by
    exact absurd h.1 (by cases s <;> simp [IsEdge, subtreeAt, IsEdgeRoot])
  | b :: p, node d l r, s, hs, hnd, h => by
    have hdisj : ∀ a ∈ (topAux l).labels, a ∉ (topAux r).labels := fun a ha ha' =>
      ne_of_nodup_append hnd ((sublist_topAux l).subset ha) ((sublist_topAux r).subset ha') rfl
    have hang_eq : ∀ (L R : BarTree E) a, hang (node d L R) a =
        if a ∈ (topAux L).labels then hangAux L a else hangAux R a := fun _ _ _ => rfl
    cases b with
    | false =>
      have hl : IsUncut l p s := h
      have hls : l.IsShuffle := hs.2.1
      have hlnd : l.labels.Nodup := (List.nodup_append.1 hnd).1
      have hsize : l.size < (node d l r).size := by simp only [size_node]; omega
      have hroot : ∀ σ : Mono E 3, rootFlag (substBar l p s σ.1) = rootFlag l := fun σ =>
        rootFlag_substBar hls hlnd hl (mono_shape σ).2.2
      have hmin : ∀ σ : Mono E 3, (substBar l p s σ.1).minLabel = l.minLabel := fun σ =>
        minLabel_substBar hls hlnd hl (mono_shape σ).2.1
      by_cases hc : rootFlag l = true
      · -- the edge lies in the cut subtree `l`
        have hcut : ∀ t : BarTree E, rootFlag t = true →
            topAux t = leaf t.minLabel ∧ ∀ a, hangAux t a = if t.minLabel = a then t else leaf a :=
          fun t ht => by
            cases t with
            | leaf => simp [rootFlag] at ht
            | node d' a' b' =>
              simp only [rootFlag] at ht
              exact ⟨topAux_cut ht, hangAux_cut ht⟩
        obtain ⟨htl, hhl⟩ := hcut l hc
        have hyl : hang (node d l r) l.minLabel = l := by
          rw [hang_eq, if_pos (by simp [htl]), hhl, if_pos rfl]
        refine Or.inr ⟨l.minLabel, p, by rw [hyl]; exact hl, by rw [hyl]; exact hsize,
          by rw [hyl]; exact hls, by rw [hyl]; exact hlnd, by simp [top, htl],
          fun σ => ⟨?_, ?_⟩⟩
        · rw [substBar_cons_false]
          simp only [top, (hcut _ ((hroot σ).trans hc)).1, hmin σ, htl]
        · rw [substBar_cons_false, hyl]
          funext a
          simp only [hang_eq, (hcut _ ((hroot σ).trans hc)).1, Function.update_apply, htl,
            (hcut _ ((hroot σ).trans hc)).2, hmin σ, hhl, labels_leaf, List.mem_singleton]
          by_cases ha : a = l.minLabel
          · subst ha
            simp
          · simp [ha]
      · have hc' : rootFlag l = false := by simpa using hc
        rcases top_hang_substBar p l s hls hlnd hl with ⟨hte, hσ⟩ | ⟨a, q, hq, hsz, hhs, hhnd, ha,
          hσ⟩
        · refine Or.inl ⟨?_, fun σ => ⟨?_, ?_⟩⟩
          · show (topAux l).IsEdge p s
            rw [topAux_eq_top hc']
            exact hte
          · rw [substBar_cons_false]
            simp only [top]
            rw [topAux_eq_top ((hroot σ).trans hc'), (hσ σ).1, topAux_eq_top hc']
            rfl
          · rw [substBar_cons_false]
            funext a
            have hperm : ((top l).substAt p s σ.1).labels.Perm (top l).labels :=
              perm_labels_substAt hte (isShuffle_top hls) (nodup_top hlnd) (mono_shape σ).2.1
            simp only [hang_eq, topAux_eq_top ((hroot σ).trans hc'), (hσ σ).1, hperm.mem_iff,
              hangAux_eq_hang ((hroot σ).trans hc'), (hσ σ).2, topAux_eq_top hc',
              hangAux_eq_hang hc']
        · have hya : hang (node d l r) a = hang l a := by
            rw [hang_eq, if_pos (by rw [topAux_eq_top hc']; exact ha), hangAux_eq_hang hc']
          refine Or.inr ⟨a, q, by rw [hya]; exact hq, by rw [hya]; exact hsz.trans hsize,
            by rw [hya]; exact hhs, by rw [hya]; exact hhnd, ?_, fun σ => ⟨?_, ?_⟩⟩
          · simp only [top, labels_node, List.mem_append]
            left
            rw [topAux_eq_top hc']
            exact ha
          · rw [substBar_cons_false]
            simp only [top]
            rw [topAux_eq_top ((hroot σ).trans hc'), (hσ σ).1, topAux_eq_top hc']
          · rw [substBar_cons_false, hya]
            funext a'
            simp only [hang_eq, topAux_eq_top ((hroot σ).trans hc'), (hσ σ).1,
              hangAux_eq_hang ((hroot σ).trans hc'), (hσ σ).2, Function.update_apply,
              topAux_eq_top hc', hangAux_eq_hang hc']
            by_cases haa : a' = a
            · subst haa
              simp [ha]
            · simp [haa]
    | true =>
      have hr : IsUncut r p s := h
      have hrs : r.IsShuffle := hs.2.2
      have hrnd : r.labels.Nodup := (List.nodup_append.1 hnd).2.1
      have hsize : r.size < (node d l r).size := by simp only [size_node]; omega
      have hroot : ∀ σ : Mono E 3, rootFlag (substBar r p s σ.1) = rootFlag r := fun σ =>
        rootFlag_substBar hrs hrnd hr (mono_shape σ).2.2
      have hmin : ∀ σ : Mono E 3, (substBar r p s σ.1).minLabel = r.minLabel := fun σ =>
        minLabel_substBar hrs hrnd hr (mono_shape σ).2.1
      by_cases hc : rootFlag r = true
      · have hcut : ∀ t : BarTree E, rootFlag t = true →
            topAux t = leaf t.minLabel ∧ ∀ a, hangAux t a = if t.minLabel = a then t else leaf a :=
          fun t ht => by
            cases t with
            | leaf => simp [rootFlag] at ht
            | node d' a' b' =>
              simp only [rootFlag] at ht
              exact ⟨topAux_cut ht, hangAux_cut ht⟩
        obtain ⟨htr, hhr⟩ := hcut r hc
        have hnl : r.minLabel ∉ (topAux l).labels := fun h' =>
          hdisj _ h' (by simp [htr])
        have hyr : hang (node d l r) r.minLabel = r := by
          rw [hang_eq, if_neg hnl, hhr, if_pos rfl]
        refine Or.inr ⟨r.minLabel, p, by rw [hyr]; exact hr, by rw [hyr]; exact hsize,
          by rw [hyr]; exact hrs, by rw [hyr]; exact hrnd, by simp [top, htr],
          fun σ => ⟨?_, ?_⟩⟩
        · rw [substBar_cons_true]
          simp only [top, (hcut _ ((hroot σ).trans hc)).1, hmin σ, htr]
        · rw [substBar_cons_true, hyr]
          funext a
          simp only [hang_eq, (hcut _ ((hroot σ).trans hc)).2, Function.update_apply, hhr,
            hmin σ]
          by_cases ha : a = r.minLabel
          · subst ha
            simp [hnl]
          · simp [ha, Ne.symm ha]
      · have hc' : rootFlag r = false := by simpa using hc
        rcases top_hang_substBar p r s hrs hrnd hr with ⟨hte, hσ⟩ | ⟨a, q, hq, hsz, hhs, hhnd, ha,
          hσ⟩
        · refine Or.inl ⟨?_, fun σ => ⟨?_, ?_⟩⟩
          · show (topAux r).IsEdge p s
            rw [topAux_eq_top hc']
            exact hte
          · rw [substBar_cons_true]
            simp only [top]
            rw [topAux_eq_top ((hroot σ).trans hc'), (hσ σ).1, topAux_eq_top hc']
            rfl
          · rw [substBar_cons_true]
            funext a
            simp only [hang_eq]
            rw [hangAux_eq_hang ((hroot σ).trans hc'), (hσ σ).2, hangAux_eq_hang hc']
        · have hna : a ∉ (topAux l).labels := fun h' =>
            hdisj a h' (by rw [topAux_eq_top hc']; exact ha)
          have hya : hang (node d l r) a = hang r a := by
            rw [hang_eq, if_neg hna, hangAux_eq_hang hc']
          refine Or.inr ⟨a, q, by rw [hya]; exact hq, by rw [hya]; exact hsz.trans hsize,
            by rw [hya]; exact hhs, by rw [hya]; exact hhnd, ?_, fun σ => ⟨?_, ?_⟩⟩
          · simp only [top, labels_node, List.mem_append]
            right
            rw [topAux_eq_top hc']
            exact ha
          · rw [substBar_cons_true]
            simp only [top]
            rw [topAux_eq_top ((hroot σ).trans hc'), (hσ σ).1, topAux_eq_top hc']
          · rw [substBar_cons_true, hya]
            funext a'
            simp only [hang_eq, hangAux_eq_hang ((hroot σ).trans hc'), (hσ σ).2,
              Function.update_apply, hangAux_eq_hang hc']
            by_cases haa : a' = a
            · subst haa
              simp [hna]
            · simp [haa]

end Subst

end Components

/-! ## Grafting combinations -/

section Graft

/-- The bilinear map grafting two combinations of bar trees under a vertex `d`. -/
noncomputable def nodeL (d : E × Bool) :
    (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) :=
  Finsupp.linearCombination K fun s =>
    Finsupp.linearCombination K fun t => Finsupp.single (node d s t) (1 : K)

lemma nodeL_single (d : E × Bool) (s t : BarTree E) (a b : K) :
    nodeL K d (Finsupp.single s a) (Finsupp.single t b) =
      Finsupp.single (node d s t) (a * b) := by
  simp [nodeL, Finsupp.smul_single, smul_eq_mul]

/-- **Grafting combinations**: each leaf `a` of a bar tree replaced by the combination `H a`. -/
noncomputable def graftL (H : ℕ → (BarTree E →₀ K)) : BarTree E → (BarTree E →₀ K)
  | leaf a => H a
  | node d l r => nodeL K d (graftL H l) (graftL H r)

lemma graftL_single (ins : ℕ → BarTree E) :
    ∀ m : BarTree E, graftL K (fun a => Finsupp.single (ins a) 1) m = Finsupp.single (m.plug ins) 1
  | leaf _ => rfl
  | node d l r => by
    rw [graftL, graftL_single ins l, graftL_single ins r, nodeL_single, one_mul]
    rfl

lemma graftL_congr {H H' : ℕ → (BarTree E →₀ K)} :
    ∀ {m : BarTree E}, (∀ a ∈ m.labels, H a = H' a) → graftL K H m = graftL K H' m
  | leaf a, h => h a (by simp)
  | node d l r, h => by
    rw [graftL, graftL, graftL_congr fun a ha => h a (by simp [ha]),
      graftL_congr fun a ha => h a (by simp [ha])]

/-- **Grafting is linear in the combination grafted at a leaf.** -/
lemma graftL_update_sum {ι : Type*} (H : ℕ → (BarTree E →₀ K)) (a : ℕ) (t : Finset ι) (c : ι → K)
    (u : ι → (BarTree E →₀ K)) : ∀ m : BarTree E, m.labels.Nodup → a ∈ m.labels →
      graftL K (Function.update H a (∑ i ∈ t, c i • u i)) m =
        ∑ i ∈ t, c i • graftL K (Function.update H a (u i)) m
  | leaf b, _, ha => by
    simp only [labels_leaf, List.mem_singleton] at ha
    subst ha
    simp [graftL]
  | node d l r, hnd, ha => by
    have hdisj : ∀ x ∈ l.labels, x ∉ r.labels := fun x hx hx' =>
      ne_of_nodup_append hnd hx hx' rfl
    simp only [labels_node, List.mem_append] at ha
    rcases ha with ha | ha
    · have hr : ∀ v, graftL K (Function.update H a v) r = graftL K H r := fun v =>
        graftL_congr K fun x hx => by
          have hxa : x ≠ a := fun h => hdisj a ha (h ▸ hx)
          rw [Function.update_of_ne hxa]
      simp only [graftL, hr]
      rw [graftL_update_sum H a t c u l (List.nodup_append.1 hnd).1 ha, map_sum,
        LinearMap.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, LinearMap.smul_apply]
    · have hl : ∀ v, graftL K (Function.update H a v) l = graftL K H l := fun v =>
        graftL_congr K fun x hx => by
          have hxa : x ≠ a := fun h => hdisj x hx (h ▸ ha)
          rw [Function.update_of_ne hxa]
      simp only [graftL, hl]
      rw [graftL_update_sum H a t c u r (List.nodup_append.1 hnd).2.1 ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]

lemma graftL_update_zero (H : ℕ → (BarTree E →₀ K)) (a : ℕ) (m : BarTree E)
    (hnd : m.labels.Nodup) (ha : a ∈ m.labels) : graftL K (Function.update H a 0) m = 0 := by
  have := graftL_update_sum K H a (∅ : Finset ℕ) (fun _ => 0) (fun _ => 0) m hnd ha
  simpa using this

end Graft

/-! ## Normality of the components -/

section NormalComponents

lemma mem_edgeWins_left {d : E × Bool} {l r : BarTree E} {kw : (ℕ ×ₗ ℕ) × LTree E}
    (h : kw ∈ (l.mapDec Prod.fst).edgeWins) : kw ∈ ((node d l r).mapDec Prod.fst).edgeWins := by
  simp only [mapDec_node, edgeWins, List.mem_append]
  exact Or.inl (Or.inr h)

lemma mem_edgeWins_right {d : E × Bool} {l r : BarTree E} {kw : (ℕ ×ₗ ℕ) × LTree E}
    (h : kw ∈ (r.mapDec Prod.fst).edgeWins) : kw ∈ ((node d l r).mapDec Prod.fst).edgeWins := by
  simp only [mapDec_node, edgeWins, List.mem_append]
  exact Or.inr h

lemma NormalBar.left {d : E × Bool} {l r : BarTree E} (hnd : (node d l r).labels.Nodup)
    (h : NormalBar L (node d l r)) : NormalBar L l := by
  rintro ⟨k, w⟩ hkw hc
  have hk := (mem_edgeWins_key _ hkw).1
  rw [nodeKeys_mapDec] at hk
  refine h (k, w) (mem_edgeWins_left hkw) fun hc' => ?_
  rw [cutKeys, Finset.mem_union, Finset.mem_union] at hc'
  rcases hc' with hc' | hc' | hc'
  · split_ifs at hc'
    · exact key_not_mem_left d l r (Finset.mem_singleton.1 hc' ▸ hk)
    · simp at hc'
  · exact hc hc'
  · exact Finset.disjoint_left.1 (disjoint_nodeKeys hnd) hk (cutKeys_subset r hc')

lemma NormalBar.right {d : E × Bool} {l r : BarTree E} (hnd : (node d l r).labels.Nodup)
    (h : NormalBar L (node d l r)) : NormalBar L r := by
  rintro ⟨k, w⟩ hkw hc
  have hk := (mem_edgeWins_key _ hkw).1
  rw [nodeKeys_mapDec] at hk
  refine h (k, w) (mem_edgeWins_right hkw) fun hc' => ?_
  rw [cutKeys, Finset.mem_union, Finset.mem_union] at hc'
  rcases hc' with hc' | hc' | hc'
  · split_ifs at hc'
    · exact key_not_mem_right d l r (Finset.mem_singleton.1 hc' ▸ hk)
    · simp at hc'
  · exact Finset.disjoint_left.1 (disjoint_nodeKeys hnd) (cutKeys_subset l hc') hk
  · exact hc hc'

/-- The key of an uncut child is not a cut key. -/
lemma key_not_mem_cutKeys_left {d d' : E × Bool} {a b r : BarTree E}
    (hnd : (node d (node d' a b) r).labels.Nodup) (hd : d'.2 = false) :
    key (node d' a b) ∉ cutKeys (node d (node d' a b) r) := by
  intro h
  rw [cutKeys, Finset.mem_union, Finset.mem_union] at h
  rcases h with h | h | h
  · split_ifs at h
    · exact key_not_mem_left d (node d' a b) r
        (Finset.mem_singleton.1 h ▸ by simp [nodeKeys])
    · simp at h
  · rw [cutKeys, if_neg (by simp [hd]), Finset.empty_union, Finset.mem_union] at h
    rcases h with h | h
    · exact key_not_mem_left d' a b (cutKeys_subset a h)
    · exact key_not_mem_right d' a b (cutKeys_subset b h)
  · exact Finset.disjoint_left.1 (disjoint_nodeKeys hnd) (by simp [nodeKeys]) (cutKeys_subset r h)

lemma key_not_mem_cutKeys_right {d d' : E × Bool} {a b l : BarTree E}
    (hnd : (node d l (node d' a b)).labels.Nodup) (hd : d'.2 = false) :
    key (node d' a b) ∉ cutKeys (node d l (node d' a b)) := by
  intro h
  rw [cutKeys, Finset.mem_union, Finset.mem_union] at h
  rcases h with h | h | h
  · split_ifs at h
    · exact key_not_mem_right d l (node d' a b)
        (Finset.mem_singleton.1 h ▸ by simp [nodeKeys])
    · simp at h
  · exact Finset.disjoint_left.1 (disjoint_nodeKeys hnd) (cutKeys_subset l h) (by simp [nodeKeys])
  · rw [cutKeys, if_neg (by simp [hd]), Finset.empty_union, Finset.mem_union] at h
    rcases h with h | h
    · exact key_not_mem_left d' a b (cutKeys_subset a h)
    · exact key_not_mem_right d' a b (cutKeys_subset b h)

lemma isNormal_topAux {t : BarTree E} (ih : rootFlag t = false → IsNormal L (top t)) :
    IsNormal L (topAux t) := by
  cases t with
  | leaf => exact fun w hw => by simp [topAux, windows] at hw
  | node d' a b =>
    by_cases hd : d'.2
    · rw [topAux_cut hd]
      exact fun w hw => by simp [windows] at hw
    · have hd' : d'.2 = false := by simpa using hd
      rw [topAux_of_flag hd']
      exact ih hd'

/-- **The top component of a normal bar tree is a normal monomial.** -/
theorem isNormal_top : ∀ y : BarTree E, y.labels.Nodup → NormalBar L y → IsNormal L (top y)
  | leaf _, _, _ => fun w hw => by simp [top, windows] at hw
  | node d l r, hnd, h => by
    have hnl := (List.nodup_append.1 hnd).1
    have hnr := (List.nodup_append.1 hnd).2.1
    have hl : IsNormal L (topAux l) :=
      isNormal_topAux L fun _ => isNormal_top l hnl (NormalBar.left L hnd h)
    have hr : IsNormal L (topAux r) :=
      isNormal_topAux L fun _ => isNormal_top r hnr (NormalBar.right L hnd h)
    intro w hw
    simp only [top, windows, List.mem_append] at hw
    rcases hw with ((hw | hw) | hw) | hw
    · cases l with
      | leaf => simp [topAux] at hw
      | node d' a b =>
        by_cases hd : d'.2
        · simp [topAux, hd] at hw
        · have hd' : d'.2 = false := by simpa using hd
          obtain rfl : w = window d.1 d'.1 false a.minLabel b.minLabel r.minLabel := by
            simpa [topAux, hd'] using hw
          refine h (key (node d' a b), window d.1 d'.1 false a.minLabel b.minLabel r.minLabel)
            ?_ (key_not_mem_cutKeys_left hnd hd')
          simp [edgeWins, key_node]
    · cases r with
      | leaf => cases topAux l <;> simp [topAux] at hw
      | node d' a b =>
        by_cases hd : d'.2
        · cases topAux l <;> simp [topAux, hd] at hw
        · have hd' : d'.2 = false := by simpa using hd
          obtain rfl : w = window d.1 d'.1 true a.minLabel b.minLabel l.minLabel := by
            cases hl' : topAux l <;> simp [topAux, hd', hl'] at hw <;>
              simpa [← minLabel_topAux l, hl'] using hw
          refine h (key (node d' a b), window d.1 d'.1 true a.minLabel b.minLabel l.minLabel)
            ?_ (key_not_mem_cutKeys_right hnd hd')
          cases l <;> simp [edgeWins, key_node]
    · exact hl w hw
    · exact hr w hw
  termination_by y => y.size
  decreasing_by all_goals (simp only [size_node]; omega)

/-- The hanging subtrees of a normal bar tree are normal bar trees. -/
lemma hangAux_props : ∀ (y : BarTree E) (a : ℕ), y.IsShuffle → y.labels.Nodup → NormalBar L y →
    (hangAux y a).IsShuffle ∧ (hangAux y a).labels.Nodup ∧ NormalBar L (hangAux y a)
  | leaf _, a, _, _, _ => ⟨trivial, by simp [hangAux], fun kw hkw => by
      simp [hangAux, edgeWins] at hkw⟩
  | node d l r, a, hs, hnd, h => by
    simp only [hangAux]
    split_ifs
    · exact ⟨hs, hnd, h⟩
    · exact ⟨trivial, by simp, fun kw hkw => by simp [edgeWins] at hkw⟩
    · exact hangAux_props l a hs.2.1 (List.nodup_append.1 hnd).1 (NormalBar.left L hnd h)
    · exact hangAux_props r a hs.2.2 (List.nodup_append.1 hnd).2.1 (NormalBar.right L hnd h)

lemma hang_props (y : BarTree E) (a : ℕ) (hs : y.IsShuffle) (hnd : y.labels.Nodup)
    (h : NormalBar L y) :
    (hang y a).IsShuffle ∧ (hang y a).labels.Nodup ∧ NormalBar L (hang y a) := by
  cases y with
  | leaf => exact ⟨trivial, by simp [hang], fun kw hkw => by simp [hang, edgeWins] at hkw⟩
  | node d l r =>
    simp only [hang]
    split_ifs
    · exact hangAux_props L l a hs.2.1 (List.nodup_append.1 hnd).1 (NormalBar.left L hnd h)
    · exact hangAux_props L r a hs.2.2 (List.nodup_append.1 hnd).2.1
        (NormalBar.right L hnd h)

end NormalComponents

/-! ## Normalizing the components -/

section Normalize

variable {L} [Fintype E] [DecidableEq E] {rk : E → ℕ} {R : Submodule K (Mono E 3 → K)}
  (hG : IsGroebner K rk L R)

/-- **The normalization of the components** of a bar tree: each component replaced by its normal
form, from the top down. -/
noncomputable def Φ : BarTree E → (BarTree E →₀ K)
  | leaf a => Finsupp.single (leaf a) 1
  | node d l r => Finsupp.linearCombination K
      (fun m => graftL K (fun a => Φ (hang (node d l r) a)) (liftW d.2 m))
      (hG.nf (top (node d l r)))
termination_by x => x.size
decreasing_by exact size_hang_lt d l r _

/-- **The normalization**, as a linear map. -/
noncomputable def ΦL : (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) :=
  Finsupp.linearCombination K (Φ K hG)

lemma Φ_node (d : E × Bool) (l r : BarTree E) :
    Φ K hG (node d l r) = Finsupp.linearCombination K
      (fun m => graftL K (fun a => Φ K hG (hang (node d l r) a)) (liftW d.2 m))
      (hG.nf (top (node d l r))) := by
  rw [Φ]

/-- **The normalization of a normal bar tree** is itself. -/
theorem Φ_of_normal : ∀ (n : ℕ) (y : BarTree E), y.size ≤ n → y.IsShuffle → y.labels.Nodup →
    NormalBar L y → Φ K hG y = Finsupp.single y 1
  | 0, y, hy, _, _, _ => absurd hy (by cases y <;> simp)
  | _ + 1, leaf a, _, _, _, _ => by rw [Φ]
  | n + 1, node d l r, hy, hs, hnd, h => by
    rw [Φ_node, hG.nf_of_isNormal (isShuffle_top hs) (nodup_top hnd)
      (isNormal_top L _ hnd h), Finsupp.linearCombination_single, one_smul]
    have hsub : ∀ a, Φ K hG (hang (node d l r) a) = Finsupp.single (hang (node d l r) a) 1 :=
      fun a => by
        obtain ⟨h1, h2, h3⟩ := hang_props L (node d l r) a hs hnd h
        exact Φ_of_normal n _ (by have := size_hang_lt d l r a; omega) h1 h2 h3
    rw [graftL_congr K (fun a _ => hsub a), graftL_single]
    congr 1
    exact plug_top (node d l r) hnd

/-- **The normalization kills the substituted relators.** -/
theorem Φ_substRel : ∀ (n : ℕ) (y : BarTree E), y.size ≤ n → y.IsShuffle → y.labels.Nodup →
    ∀ {p : List Bool} {s : Bool}, IsUncut y p s → ∀ {r : Mono E 3 → K}, r ∈ R →
      ΦL K hG (substRel K y p s r) = 0
  | 0, y, hy, _, _, _, _, _, _, _ => absurd hy (by cases y <;> simp)
  | n + 1, y, hy, hs, hnd, p, s, h, r, hr => by
    obtain ⟨d, l', r', hy'⟩ : ∃ d l r, y = node d l r := by
      cases y with
      | leaf => exact absurd h.1 (by cases p <;> cases s <;> simp [IsEdge, subtreeAt, IsEdgeRoot])
      | node d l r => exact ⟨d, l, r, rfl⟩
    have hnode : ∀ σ : Mono E 3, ∃ d' l'' r'', substBar y p s σ.1 = node d' l'' r'' := by
      intro σ
      have := rootFlag_substBar hs hnd h (mono_shape σ).2.2
      cases hz : substBar y p s σ.1 with
      | leaf a =>
        exfalso
        have hl := perm_labels_substBar hs hnd h (mono_shape σ).2.1
        rw [hz, hy'] at hl
        have := hl.length_eq
        simp only [labels_leaf, List.length_singleton, labels_node, List.length_append,
          length_labels] at this
        have := arity_pos l'
        have := arity_pos r'
        omega
      | node d' l'' r'' => exact ⟨d', l'', r'', rfl⟩
    have hΦ : ∀ σ : Mono E 3, Φ K hG (substBar y p s σ.1) = Finsupp.linearCombination K
        (fun m => graftL K (fun a => Φ K hG (hang (substBar y p s σ.1) a)) (liftW (rootFlag y) m))
        (hG.nf (top (substBar y p s σ.1))) := fun σ => by
      obtain ⟨d', l'', r'', hz⟩ := hnode σ
      have hroot := rootFlag_substBar hs hnd h (mono_shape σ).2.2
      rw [← hroot, hz, Φ_node]
      rfl
    simp only [ΦL, substRel, map_sum, map_smul, Finsupp.linearCombination_single, one_smul, hΦ]
    rcases top_hang_substBar p y s hs hnd h with ⟨hte, hσ⟩ | ⟨a, q, hq, hsz, hhs, hhnd, ha, hσ⟩
    · -- the substitution happens in the top component
      simp only [fun σ => (hσ σ).1, fun σ => (hσ σ).2]
      set lc := Finsupp.linearCombination K
        (fun m => graftL K (fun a => Φ K hG (hang y a)) (liftW (rootFlag y) m)) with hlc
      have : ∑ σ : Mono E 3, r σ • lc (hG.nf ((top y).substAt p s σ.1)) =
          lc (∑ σ : Mono E 3, r σ • hG.nf ((top y).substAt p s σ.1)) := by
        rw [map_sum]
        simp [map_smul]
      rw [this, hG.sum_nf_substAt (isShuffle_top hs) (nodup_top hnd) hte hr, map_zero]
    · -- the substitution happens in a hanging subtree
      simp only [fun σ => (hσ σ).1, fun σ => (hσ σ).2, Finsupp.linearCombination_apply,
        Finsupp.sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun m hm => ?_
      obtain ⟨-, hml, -⟩ := hG.mem_support_nf (nodup_top hnd) hm
      have hmnd : (liftW (rootFlag y) m).labels.Nodup := by
        rw [labels_liftW]
        exact hml.nodup_iff.2 (nodup_top hnd)
      have hma : a ∈ (liftW (rootFlag y) m).labels := by
        rw [labels_liftW]
        exact hml.symm.subset ha
      have hcomp : ∀ σ : Mono E 3, (fun b => Φ K hG (Function.update (hang y) a
          (substBar (hang y a) q s σ.1) b)) =
          Function.update (fun b => Φ K hG (hang y b)) a (Φ K hG (substBar (hang y a) q s σ.1)) :=
        fun σ => by
          funext b
          by_cases hb : b = a
          · subst hb
            simp
          · simp [hb]
      simp only [hcomp]
      simp only [smul_comm (r _) ((hG.nf (top y)) m)]
      rw [← Finset.smul_sum]
      rw [← graftL_update_sum K _ a Finset.univ r (fun σ => Φ K hG (substBar (hang y a) q s σ.1))
        _ hmnd hma]
      have h0 : ∑ σ : Mono E 3, r σ • Φ K hG (substBar (hang y a) q s σ.1) = 0 := by
        have := Φ_substRel n (hang y a) (by omega) hhs hhnd hq hr
        simpa [ΦL, substRel, map_sum, map_smul] using this
      rw [h0, graftL_update_zero K _ a _ hmnd hma, smul_zero]

end Normalize

/-! ## The bar construction in a given arity and degree -/

section Koszul

variable [Fintype E] [DecidableEq E]

/-- **A bar tree of arity `n` and degree `s`**: a bar tree of the bar construction on the labels
`0, …, n - 1` with `s` components. -/
def Adm (n s : ℕ) (x : BarTree E) : Prop :=
  Valid x ∧ x.labels.Perm (List.range n) ∧ (cutKeys x).card + 1 = s

/-- **The bar construction of the free shuffle operad** in arity `n` and degree `s`. -/
def C (n s : ℕ) : Submodule K (BarTree E →₀ K) := Finsupp.supported K K {x | Adm n s x}

/-- **Koszulness**: the bar construction of the shuffle operad presented by the relators `R`, the
quotient of that of the free shuffle operad by `J R`, has its homology on the diagonal: in arity
`n`, every cycle of degree `s < n - 1` is a boundary. -/
def IsKoszul (R : Submodule K (Mono E 3 → K)) : Prop :=
  ∀ n s, s + 1 < n → ∀ x ∈ C K n s, d K x ∈ J K R → ∃ y ∈ C K n (s + 1), x - d K y ∈ J K R

omit [Fintype E] [DecidableEq E] in
lemma map_mem_of_supported {M : Type*} [AddCommGroup M] [Module K M] {S : Set (BarTree E)}
    {P : Submodule K M} (f : (BarTree E →₀ K) →ₗ[K] M)
    (h : ∀ y ∈ S, f (Finsupp.single y 1) ∈ P) {v : BarTree E →₀ K}
    (hv : v ∈ Finsupp.supported K K S) : f v ∈ P := by
  rw [Finsupp.supported_eq_span_single] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact h y hy
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact P.smul_mem c hx

omit [Fintype E] [DecidableEq E] in
lemma mem_of_supported {S : Set (BarTree E)} {P : Submodule K (BarTree E →₀ K)}
    (h : ∀ y ∈ S, Finsupp.single y 1 ∈ P) {v : BarTree E →₀ K}
    (hv : v ∈ Finsupp.supported K K S) : v ∈ P :=
  map_mem_of_supported K LinearMap.id h hv

omit [Fintype E] [DecidableEq E] in
lemma Adm.mergeK {n s : ℕ} {x : BarTree E} (hx : Adm n (s + 1) x) {k : ℕ ×ₗ ℕ}
    (hk : k ∈ cutKeys x) : Adm n s (mergeK x k) := by
  refine ⟨hx.1.mergeK k, by simpa using hx.2.1, ?_⟩
  rw [cutKeys_mergeK x hx.1.nodup hk, Finset.card_erase_of_mem hk]
  have := hx.2.2
  have : 0 < (cutKeys x).card := Finset.card_pos.2 ⟨k, hk⟩
  omega

omit [Fintype E] [DecidableEq E] in
/-- **The differential lowers the degree.** -/
lemma d_mem_C {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n (s + 1)) : d K v ∈ C K n s := by
  refine map_mem_of_supported K (d K) (fun y hy => ?_) hv
  rw [d_single, one_smul, dTree]
  exact Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _
    (Finsupp.single_mem_supported K _ (Adm.mergeK hy hk))

lemma full_mem_monomials {n s : ℕ} {x : BarTree E} (hx : Adm n s x) :
    x.mapDec Prod.fst ∈ monomials n :=
  (mem_monomials _ _).2 ⟨(isShuffle_mapDec _ x).2 hx.1.shuffle, by simpa using hx.2.1⟩

variable (rk : E → ℕ)

/-- **The level of a bar tree**: the rank of the key of its underlying monomial. -/
noncomputable def lev (n : ℕ) (x : BarTree E) : ℕ :=
  ((monomials n).filter fun t => pathKey rk n t ≤ pathKey rk n (x.mapDec Prod.fst)).card

lemma lev_lt {n : ℕ} {x y : BarTree E} (hy : y.mapDec Prod.fst ∈ monomials n)
    (h : pathKey rk n (x.mapDec Prod.fst) < pathKey rk n (y.mapDec Prod.fst)) :
    lev rk n x < lev rk n y := by
  refine Finset.card_lt_card ⟨fun t ht => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.trans h.le⟩
  · have := hsub (Finset.mem_filter.2 ⟨hy, le_rfl⟩)
    simp only [Finset.mem_filter] at this
    exact absurd this.2 (not_le.2 h)

lemma lev_pos {n s : ℕ} {x : BarTree E} (hx : Adm n s x) : 0 < lev rk n x :=
  Finset.card_pos.2 ⟨_, Finset.mem_filter.2 ⟨full_mem_monomials hx, le_rfl⟩⟩

variable {L} {R : Submodule K (Mono E 3 → K)} (hG : IsGroebner K rk L R)

/-- The normal bar trees of arity `n` and degree `s`. -/
def Nrm (L : Set (LTree E)) (n s : ℕ) : Set (BarTree E) := {x | Adm n s x ∧ NormalBar L x}

include hG in
/-- **Reduction modulo the relators**: a bar tree which is not normal is congruent to normal bar
trees of lower level, by substituting at an uncut edge with a leading window the relator which
that window leads. -/
theorem reduce (n s : ℕ) : ∀ (N : ℕ) (y : BarTree E), lev rk n y ≤ N → Adm n s y →
    ¬ NormalBar L y → Finsupp.single y (1 : K) ∈
      Finsupp.supported K K {z | z ∈ Nrm L n s ∧ lev rk n z < lev rk n y} ⊔ J K R
  | 0, y, hN, hy, _ => absurd (lev_pos rk hy) (by omega)
  | N + 1, y, hN, hy, hn => by
    obtain ⟨⟨k, w⟩, hkw, hkc, hwL⟩ : ∃ kw ∈ (y.mapDec Prod.fst).edgeWins, kw.1 ∉ cutKeys y ∧
        kw.2 ∈ L := by
      unfold NormalBar at hn
      push Not at hn
      exact hn
    obtain ⟨p, s', he, hk, hw⟩ := exists_of_mem_edgeWins _ hkw
    have hs := hy.1.shuffle
    have hnd := hy.1.nodup
    have hfull := full_mem_monomials hy
    have hu : IsUncut y p s' := by
      refine ⟨(isEdge_mapDec _ y p s').1 he, ?_⟩
      by_contra hf
      obtain ⟨d', a, b, hab⟩ : ∃ d' a b, y.subtreeAt (p ++ [s']) = node d' a b := by
        have := (isEdge_mapDec _ y p s').1 he
        unfold IsEdge at this
        rw [subtreeAt_append]
        cases hsub : y.subtreeAt p with
        | leaf => rw [hsub] at this; exact absurd this (by cases s' <;> simp [IsEdgeRoot])
        | node d0 l0 r0 =>
          rw [hsub] at this
          cases s' with
          | false =>
            cases l0 with
            | leaf => exact absurd this (by simp [IsEdgeRoot])
            | node d1 a1 b1 => exact ⟨d1, a1, b1, rfl⟩
          | true =>
            cases r0 with
            | leaf => exact absurd this (by cases l0 <;> simp [IsEdgeRoot])
            | node d1 a1 b1 => exact ⟨d1, a1, b1, rfl⟩
      have hflag : d'.2 = true := by
        simpa [flagAt, hab, rootFlag] using hf
      have := key_mem_cutKeys y (p ++ [s']) d' a b hab hflag
      rw [← hab, ← key_mapDec Prod.fst, ← subtreeAt_mapDec, hk] at this
      exact hkc this
    obtain ⟨r, hr, hrw, hlt⟩ := hG.lead w hwL
    set w' : Mono E 3 := ⟨w, hG.mem w hwL⟩ with hw'
    have hself : substBar y p s' w = y := by
      rw [substBar, ← hw, ← windowAt_of_uncut hu]
      exact substAt_windowAt hu.1 hs hnd
    have hfself : (y.mapDec Prod.fst).substAt p s' w = y.mapDec Prod.fst := by
      rw [← hw]
      exact substAt_windowAt he ((isShuffle_mapDec _ y).2 hs) (by simpa using hnd)
    have hJ : substRel K y p s' r ∈ J K R := Submodule.subset_span ⟨y, p, s', r, hy.1, hu, hr, rfl⟩
    have hsplit : substRel K y p s' r = r w' • Finsupp.single y 1 +
        ∑ σ ∈ Finset.univ.erase w', r σ • Finsupp.single (substBar y p s' σ.1) 1 := by
      rw [substRel, ← Finset.add_sum_erase _ _ (Finset.mem_univ w'), hw', hself]
    -- each other term is of lower level
    have hlow : ∀ σ ∈ Finset.univ.erase w', r σ • Finsupp.single (substBar y p s' σ.1) (1 : K) ∈
        Finsupp.supported K K {z | z ∈ Nrm L n s ∧ lev rk n z < lev rk n y} ⊔ J K R := by
      intro σ hσ
      by_cases hrσ : r σ = 0
      · simp [hrσ]
      refine Submodule.smul_mem _ _ ?_
      have hσne : σ.1 ≠ w := fun h => (Finset.mem_erase.1 hσ).1 (Subtype.ext h)
      obtain ⟨-, hσp, hσn⟩ := mono_shape σ
      have hadm : Adm n s (substBar y p s' σ.1) :=
        ⟨hy.1.substBar hu σ, (perm_labels_substBar hs hnd hu hσp).trans hy.2.1,
          by rw [cutKeys_substBar hs hnd hu hσp hσn]; exact hy.2.2⟩
      have hkey : pathKey rk n ((substBar y p s' σ.1).mapDec Prod.fst) <
          pathKey rk n (y.mapDec Prod.fst) := by
        rw [full_substBar hu.1]
        have := pathKey_substAt_lt' rk hfull he σ.2 (hG.mem w hwL) (hlt σ hσne hrσ)
        rwa [hfself] at this
      have hlev := lev_lt rk hfull hkey
      by_cases hσN : NormalBar L (substBar y p s' σ.1)
      · exact Submodule.mem_sup_left (Finsupp.single_mem_supported K _ ⟨⟨hadm, hσN⟩, hlev⟩)
      · have := reduce n s N _ (by omega) hadm hσN
        refine (sup_le_sup_right (Finsupp.supported_mono fun z hz => ?_) _) this
        exact ⟨hz.1, hz.2.trans hlev⟩
    have : Finsupp.single y (1 : K) = (r w')⁻¹ • substRel K y p s' r -
        (r w')⁻¹ • ∑ σ ∈ Finset.univ.erase w', r σ • Finsupp.single (substBar y p s' σ.1) 1 := by
      rw [hsplit, smul_add, smul_smul, inv_mul_cancel₀ hrw, one_smul, add_sub_cancel_right]
    rw [this]
    refine Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.smul_mem _ _ hJ))
      (Submodule.smul_mem _ _ (Submodule.sum_mem _ hlow))

include hG in
/-- **Every bar tree is congruent to normal bar trees** of the same arity and degree. -/
theorem single_mem_sup {n s : ℕ} {y : BarTree E} (hy : Adm n s y) :
    Finsupp.single y (1 : K) ∈ Finsupp.supported K K (Nrm L n s) ⊔ J K R := by
  by_cases hN : NormalBar L y
  · exact Submodule.mem_sup_left (Finsupp.single_mem_supported K _ ⟨hy, hN⟩)
  · exact (sup_le_sup_right (Finsupp.supported_mono fun z hz => hz.1) _)
      (reduce K rk hG n s _ y le_rfl hy hN)

include hG in
lemma mem_sup_of_C {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n s) :
    v ∈ Finsupp.supported K K (Nrm L n s) ⊔ J K R :=
  mem_of_supported K (fun _ hy => single_mem_sup K rk hG hy) hv

/-- The normalization vanishes on the relator subcomplex. -/
lemma ΦL_J {v : BarTree E →₀ K} (hv : v ∈ J K R) : ΦL K hG v = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, p, s, r, hx, h, hr, rfl⟩ := hv
    exact Φ_substRel K hG x.size x le_rfl hx.shuffle hx.nodup h hr
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

lemma ΦL_normal {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K (Nrm L n s)) :
    ΦL K hG v = v := by
  have : ∀ v ∈ Finsupp.supported K K (Nrm L n s), ΦL K hG v - v ∈ (⊥ : Submodule K _) :=
    fun v hv => by
      have := map_mem_of_supported K (P := ⊥) (ΦL K hG - LinearMap.id) (fun y hy => by
        simp only [LinearMap.sub_apply, LinearMap.id_apply, Submodule.mem_bot, ΦL,
          Finsupp.linearCombination_single, one_smul]
        rw [Φ_of_normal K hG y.size y le_rfl hy.1.1.shuffle hy.1.1.nodup hy.2, sub_self]) hv
      simpa using this
  simpa [sub_eq_zero] using this v hv

include hG in
/-- **The normalization of a chain is normal and congruent to it.** -/
lemma ΦL_spec {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n s) :
    ΦL K hG v ∈ Finsupp.supported K K (Nrm L n s) ∧ v - ΦL K hG v ∈ J K R := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (mem_sup_of_C K rk hG hv)
  rw [map_add, ΦL_normal K rk hG ha, ΦL_J K rk hG hb, add_zero, add_sub_cancel_left]
  exact ⟨ha, hb⟩

/-! ### The filtration by levels -/

lemma lev_mergeK (n : ℕ) (x : BarTree E) (k : ℕ ×ₗ ℕ) : lev rk n (mergeK x k) = lev rk n x := by
  simp [lev]

lemma lev_cutK (n : ℕ) (x : BarTree E) (k : ℕ ×ₗ ℕ) : lev rk n (cutK x k) = lev rk n x := by
  simp [lev]

/-- **The leading part**: the merges along mergeable edges, normal of the same level. -/
lemma d₀Tree_mem {n s : ℕ} {y : BarTree E} (hy : y ∈ Nrm L n (s + 1)) :
    d₀Tree K L y ∈ Finsupp.supported K K {z | z ∈ Nrm L n s ∧ lev rk n z = lev rk n y} := by
  refine Submodule.sum_mem _ fun k hk =>
    Submodule.smul_mem _ _ (Finsupp.single_mem_supported K _ ?_)
  obtain ⟨hkc, hkN⟩ := Finset.mem_filter.1 hk
  refine ⟨⟨hy.1.mergeK hkc, ?_⟩, lev_mergeK rk n y k⟩
  exact (normalBar_mergeK_iff L hy.1.1.nodup hy.2 hkc).2 (Finset.mem_sdiff.1 hkN).2

include hG in
/-- **The differential is its leading part plus terms of lower level.** -/
lemma ΦL_dTree_sub {n s : ℕ} {y : BarTree E} (hy : y ∈ Nrm L n (s + 1)) :
    ΦL K hG (dTree K y) - d₀Tree K L y ∈
      Finsupp.supported K K {z | z ∈ Nrm L n s ∧ lev rk n z < lev rk n y} := by
  classical
  have hsplit : dTree K y = d₀Tree K L y + ∑ k ∈ (cutKeys y).filter
      (fun k => k ∉ Nkeys L (y.mapDec Prod.fst)), sgn K y k • Finsupp.single (mergeK y k) 1 := by
    rw [dTree, d₀Tree, Finset.sum_filter_add_sum_filter_not]
  have hd₀ : ΦL K hG (d₀Tree K L y) = d₀Tree K L y :=
    ΦL_normal K rk hG (Finsupp.supported_mono (fun z hz => hz.1) (d₀Tree_mem K rk hy))
  rw [hsplit, map_add, hd₀, add_sub_cancel_left, map_sum]
  refine Submodule.sum_mem _ fun k hk => ?_
  obtain ⟨hkc, hkN⟩ := Finset.mem_filter.1 hk
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  have hadm := hy.1.mergeK hkc
  have hkL : k ∈ Lkeys L (y.mapDec Prod.fst) := by
    by_contra h
    exact hkN (Finset.mem_sdiff.2 ⟨cutKeys_subset_edgeKeys hy.1.1.root hkc, h⟩)
  have hn : ¬ NormalBar L (mergeK y k) := fun h =>
    ((normalBar_mergeK_iff L hy.1.1.nodup hy.2 hkc).1 h) hkL
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (reduce K rk hG n s _ _ le_rfl hadm hn)
  rw [← hab, map_add, ΦL_normal K rk hG (Finsupp.supported_mono (fun z hz => hz.1) ha),
    ΦL_J K rk hG hb, add_zero]
  rw [lev_mergeK] at ha
  exact ha

/-- **The homotopy cuts an edge**, keeping the level. -/
lemma hTree_mem {n s : ℕ} {y : BarTree E} (hy : y ∈ Nrm L n (s + 1)) :
    hTree K L y ∈ Finsupp.supported K K {z | z ∈ Nrm L n (s + 2) ∧ lev rk n z = lev rk n y} := by
  unfold hTree
  split_ifs with hne hc
  · exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Finsupp.single_mem_supported K _ ?_)
    set k₀ := (Nkeys L (y.mapDec Prod.fst)).min' hne
    have hk₀E : k₀ ∈ (y.mapDec Prod.fst).edgeKeys :=
      (Finset.mem_sdiff.1 (Finset.min'_mem _ hne)).1
    refine ⟨⟨⟨⟨(isShuffle_cutK _ _).2 hy.1.1.shuffle, by simpa using hy.1.1.nodup,
      (rootFlag_cutK _ _).trans hy.1.1.root⟩, by simpa using hy.1.2.1, ?_⟩,
      normalBar_cutK hy.1.1.nodup hk₀E hy.2⟩, lev_cutK rk n y k₀⟩
    rw [cutKeys_cutK hy.1.1.nodup hk₀E, Finset.card_insert_of_notMem hc, hy.1.2.2]
  · exact Submodule.zero_mem _

omit [Fintype E] [DecidableEq E] in
/-- **Below the diagonal, a normal bar tree has a mergeable edge.** -/
lemma nkeys_nonempty {n s : ℕ} {y : BarTree E} (hy : y ∈ Nrm L n (s + 1)) (hs : s + 2 < n) :
    (Nkeys L (y.mapDec Prod.fst)).Nonempty := by
  obtain ⟨d, l, r, rfl⟩ : ∃ d l r, y = node d l r := by
    cases y with
    | leaf a =>
      have := hy.1.2.1.length_eq
      simp at this
      omega
    | node d l r => exact ⟨d, l, r, rfl⟩
  have hcard := card_edgeKeys (e := d.1) (l := l.mapDec Prod.fst) (r := r.mapDec Prod.fst)
    (by simpa using hy.1.1.nodup)
  have harity : (node d.1 (l.mapDec Prod.fst) (r.mapDec Prod.fst)).arity = n := by
    rw [← length_labels, show (node d.1 (l.mapDec Prod.fst) (r.mapDec Prod.fst)).labels =
      (node d l r).labels by simp, hy.1.2.1.length_eq, List.length_range]
  have hlt : (cutKeys (node d l r)).card < ((node d l r).mapDec Prod.fst).edgeKeys.card := by
    rw [mapDec_node]
    have := hy.1.2.2
    omega
  obtain ⟨k, hkE, hkc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨k, Finset.mem_sdiff.2 ⟨hkE, fun hkL => hkc (Lkeys_subset_cutKeys L hy.2 hkL)⟩⟩

omit [Fintype E] [DecidableEq E] in
lemma homotopy_supported {n s : ℕ} (hs : s + 2 < n) {v : BarTree E →₀ K}
    (hv : v ∈ Finsupp.supported K K (Nrm L n (s + 1))) :
    d₀ K L (hL K L v) + hL K L (d₀ K L v) = v := by
  have := map_mem_of_supported K (P := ⊥)
    ((d₀ K L ∘ₗ hL K L) + (hL K L ∘ₗ d₀ K L) - LinearMap.id) (fun y hy => by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, hL_single,
        d₀_single, one_smul, LinearMap.id_apply, Submodule.mem_bot]
      rw [d₀_hTree_add K L hy.1.1.nodup hy.1.1.root (nkeys_nonempty hy hs), sub_self]) hv
  simpa [sub_eq_zero] using this

include hG in
lemma ΦL_d_ΦL_d {n s : ℕ} {w : BarTree E →₀ K} (hw : w ∈ C K n (s + 2)) :
    ΦL K hG (d K (ΦL K hG (d K w))) = 0 := by
  have hdw := d_mem_C K hw
  obtain ⟨-, hj⟩ := ΦL_spec K rk hG hdw
  have hdd : d K (d K w) = 0 := by
    have := map_mem_of_supported K (P := ⊥) (d K ∘ₗ d K) (fun y hy => by
      simp only [LinearMap.comp_apply, d_single, one_smul, Submodule.mem_bot]
      exact d_dTree K y hy.1.nodup) hw
    simpa using this
  have : ΦL K hG (d K (ΦL K hG (d K w))) =
      ΦL K hG (d K (d K w)) - ΦL K hG (d K (d K w - ΦL K hG (d K w))) := by
    rw [map_sub (d K), map_sub, sub_sub_cancel]
  rw [this, hdd, map_zero, zero_sub, ΦL_J K rk hG (d_mem_J K R hj), neg_zero]

include hG in
/-- **Acyclicity below the diagonal**, by induction on the level. -/
theorem acyclic (n s : ℕ) (hs : s + 2 < n) : ∀ (N : ℕ) (z : BarTree E →₀ K),
    z ∈ Finsupp.supported K K {y | y ∈ Nrm L n (s + 1) ∧ lev rk n y ≤ N} →
    ΦL K hG (d K z) = 0 → ∃ w ∈ Finsupp.supported K K (Nrm L n (s + 2)), ΦL K hG (d K w) = z
  | 0, z, hz, _ => by
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [map_zero, map_zero]
    ext y
    by_contra h
    obtain ⟨hy1, hy2⟩ := (Finsupp.mem_supported K z).1 hz (Finsupp.mem_support_iff.2 (Ne.symm h))
    have := lev_pos rk hy1.1
    omega
  | N + 1, z, hz, hdz => by
    classical
    set zt := z.filter fun y => lev rk n y = N + 1 with hzt
    set zl := z.filter fun y => ¬ lev rk n y = N + 1 with hzl
    have hz' : zt + zl = z := Finsupp.filter_add_filter_not _ _
    have hztm : zt ∈ Finsupp.supported K K {y | y ∈ Nrm L n (s + 1) ∧ lev rk n y = N + 1} := by
      rw [Finsupp.mem_supported, hzt, Finsupp.support_filter]
      intro y hy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy
      exact ⟨((Finsupp.mem_supported K z).1 hz hy.1).1, hy.2⟩
    have hzlm : zl ∈ Finsupp.supported K K {y | y ∈ Nrm L n (s + 1) ∧ lev rk n y ≤ N} := by
      rw [Finsupp.mem_supported, hzl, Finsupp.support_filter]
      intro y hy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy
      obtain ⟨h1, h2⟩ := (Finsupp.mem_supported K z).1 hz hy.1
      have h3 := hy.2
      exact ⟨h1, by omega⟩
    -- the lower part of the differential of a chain of levels at most `M`
    have hlow : ∀ (M : ℕ) (v : BarTree E →₀ K),
        v ∈ Finsupp.supported K K {y | y ∈ Nrm L n (s + 1) ∧ lev rk n y ≤ M} →
        ΦL K hG (d K v) - d₀ K L v ∈
          Finsupp.supported K K {y | y ∈ Nrm L n s ∧ lev rk n y < M} := fun M v hv =>
      map_mem_of_supported K (ΦL K hG ∘ₗ d K - d₀ K L) (fun y hy => by
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, d_single, d₀_single, one_smul]
        refine Finsupp.supported_mono ?_ (ΦL_dTree_sub K rk hG hy.1)
        intro z hz
        exact ⟨hz.1, lt_of_lt_of_le hz.2 hy.2⟩) hv
    have hd₀ : ∀ (P : ℕ → Prop) (v : BarTree E →₀ K),
        v ∈ Finsupp.supported K K {y | y ∈ Nrm L n (s + 1) ∧ P (lev rk n y)} →
        d₀ K L v ∈ Finsupp.supported K K {y | y ∈ Nrm L n s ∧ P (lev rk n y)} := fun P v hv =>
      map_mem_of_supported K (d₀ K L) (fun y hy => by
        rw [d₀_single, one_smul]
        refine Finsupp.supported_mono ?_ (d₀Tree_mem K rk hy.1)
        intro z hz
        exact ⟨hz.1, hz.2 ▸ hy.2⟩) hv
    -- the leading part of `zt` is a cycle
    have hcyc : d₀ K L zt = 0 := by
      have e1 := hlow (N + 1) zt (by
        refine Finsupp.supported_mono ?_ hztm
        intro y hy
        exact ⟨hy.1, hy.2.le⟩)
      have e2 := hlow N zl hzlm
      have e3 := hd₀ (· ≤ N) zl hzlm
      have e4 := hd₀ (· = N + 1) zt hztm
      have hsum : d₀ K L zt = -((ΦL K hG (d K zt) - d₀ K L zt) +
          (ΦL K hG (d K zl) - d₀ K L zl) + d₀ K L zl) := by
        rw [← hz', map_add, map_add] at hdz
        rw [eq_neg_iff_add_eq_zero, ← hdz]
        abel
      ext y
      by_cases hy : lev rk n y = N + 1
      · rw [hsum, Finsupp.neg_apply, Finsupp.add_apply, Finsupp.add_apply]
        have h1 := (Finsupp.mem_supported' K _).1 e1 y (fun h => by have := h.2; omega)
        have h2 := (Finsupp.mem_supported' K _).1 e2 y (fun h => by have := h.2; omega)
        have h3 := (Finsupp.mem_supported' K _).1 e3 y (fun h => by have := h.2; omega)
        simp [h1, h2, h3]
      · exact (Finsupp.mem_supported' K _).1 e4 y (fun h => hy h.2)
    -- cut along the least mergeable edges
    have hztN : zt ∈ Finsupp.supported K K (Nrm L n (s + 1)) := by
      refine Finsupp.supported_mono ?_ hztm
      intro y hy
      exact hy.1
    have hhom := homotopy_supported K hs hztN
    rw [hcyc, map_zero, add_zero] at hhom
    set w₁ := hL K L zt with hw₁
    have hw₁m : w₁ ∈ Finsupp.supported K K {y | y ∈ Nrm L n (s + 2) ∧ lev rk n y = N + 1} :=
      map_mem_of_supported K (hL K L) (fun y hy => by
        rw [hL_single, one_smul]
        refine Finsupp.supported_mono ?_ (hTree_mem K rk hy.1)
        intro z hz
        exact ⟨hz.1, hz.2.trans hy.2⟩) hztm
    have hw₁C : w₁ ∈ C K n (s + 2) := by
      refine Finsupp.supported_mono ?_ hw₁m
      intro y hy
      exact hy.1.1
    -- what remains is of lower level
    have hlow₁ : ΦL K hG (d K w₁) - d₀ K L w₁ ∈
        Finsupp.supported K K {y | y ∈ Nrm L n (s + 1) ∧ lev rk n y < N + 1} :=
      map_mem_of_supported K (ΦL K hG ∘ₗ d K - d₀ K L) (fun y hy => by
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, d_single, d₀_single, one_smul]
        refine Finsupp.supported_mono ?_ (ΦL_dTree_sub K rk hG hy.1)
        intro z hz
        exact ⟨hz.1, lt_of_lt_of_le hz.2 hy.2.le⟩) hw₁m
    set z' := z - ΦL K hG (d K w₁) with hz'def
    have hz'm : z' ∈ Finsupp.supported K K {y | y ∈ Nrm L n (s + 1) ∧ lev rk n y ≤ N} := by
      have : z' = zl - (ΦL K hG (d K w₁) - d₀ K L w₁) := by
        rw [hz'def, ← hz', ← hhom]
        abel
      rw [this]
      refine Submodule.sub_mem _ hzlm (Finsupp.supported_mono ?_ hlow₁)
      intro y hy
      exact ⟨hy.1, Nat.lt_succ_iff.1 hy.2⟩
    have hdz' : ΦL K hG (d K z') = 0 := by
      rw [hz'def, map_sub, map_sub, hdz, ΦL_d_ΦL_d K rk hG hw₁C, sub_zero]
    obtain ⟨w₂, hw₂, hw₂z⟩ := acyclic n s hs N z' hz'm hdz'
    have hw₁N : w₁ ∈ Finsupp.supported K K (Nrm L n (s + 2)) := by
      refine Finsupp.supported_mono ?_ hw₁m
      intro y hy
      exact hy.1
    refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁N hw₂, ?_⟩
    rw [map_add, map_add, hw₂z, hz'def]
    abel

include hG in
/-- **The criterion of Dotsenko and Khoroshkin**: a shuffle operad presented by relators of arity
three which are a quadratic Gröbner basis is Koszul. -/
theorem isKoszul : IsKoszul K R := by
  intro n s hs x hx hdx
  cases s with
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    have : x = 0 := by
      ext y
      by_contra h
      have := (Finsupp.mem_supported K x).1 hx (Finsupp.mem_support_iff.2 (by simpa using h))
      exact absurd this.2.2 (by omega)
    rw [this, map_zero, sub_zero]
    exact Submodule.zero_mem _
  | succ s =>
    obtain ⟨hzN, hxz⟩ := ΦL_spec K rk hG hx
    have hdz : ΦL K hG (d K (ΦL K hG x)) = 0 := by
      have : ΦL K hG x = x - (x - ΦL K hG x) := by abel
      rw [this, map_sub, map_sub, ΦL_J K rk hG hdx, ΦL_J K rk hG (d_mem_J K R hxz), sub_zero]
    have hlev : ΦL K hG x ∈ Finsupp.supported K K
        {y | y ∈ Nrm L n (s + 1) ∧ lev rk n y ≤ (monomials (E := E) n).card} := by
      refine Finsupp.supported_mono ?_ hzN
      intro y hy
      exact ⟨hy, Finset.card_filter_le _ _⟩
    obtain ⟨w, hw, hwz⟩ := acyclic K rk hG n s (by omega) _ _ hlev hdz
    have hwC : w ∈ C K n (s + 2) := by
      refine Finsupp.supported_mono ?_ hw
      intro y hy
      exact hy.1
    refine ⟨w, hwC, ?_⟩
    obtain ⟨-, hj⟩ := ΦL_spec K rk hG (d_mem_C K hwC)
    have : x - d K w = (x - ΦL K hG x) - (d K w - ΦL K hG (d K w)) := by
      rw [hwz]
      abel
    rw [this]
    exact Submodule.sub_mem _ hxz hj

end Koszul

end ShuffleBar

end Operad
