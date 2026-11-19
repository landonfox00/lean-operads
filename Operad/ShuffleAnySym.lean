/-
# The bar construction of a free operad on generators of any arity, in shuffle coordinates

Step (2b) of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin) for generators
of any arity, first part; the binary case is `Operad.ShuffleBarSym`.

Throughout, `E` is a graded linear species over a field `K` with an even basis `c k` of
each `E (Fin k)` indexed by `T k`, with no generators in arities zero and one
(`IsEmpty (T 0)`, `IsEmpty (T 1)`), `T(E) = FreeGrL K E`, and `Ī` its ideal of the
operations with at least two inputs.

* **Bases**: the shuffle trees on `0, …, k - 1` index a basis of `T(E) (Fin k)`
  (`ShuffleAnySym.tBasis`); those with `k ≥ 2` (`ShuffleAnySym.VMono`) a basis of `Ī (Fin k)`
  and of the generators `sĪ (Fin k)` of the bar construction (`ShuffleAnySym.genBasis`); and the
  shuffle trees of such monomials a basis of `B(T, Ī)` (`ShuffleAnySym.barBasisN`).
* **The bar tree** `ShuffleAnySym.toBar t` of a shuffle tree of monomials: the monomials of the
  vertices grafted along cut edges, a tree of the bar construction of the free shuffle operad
  (`Operad.ShuffleAnyBar`). It has as many cut edges as `t` has vertices other than the root
  (`ShuffleAnySym.card_cutKeys_toBar`), `toBar` is injective on shuffle trees
  (`ShuffleAnySym.toBar_injective`) and onto the bar trees with distinct leaves and no cut above
  the root (`ShuffleAnySym.exists_toBar`): `ShuffleAnySym.treeEquiv`.
* **Keys and signs**: a vertex is named by the key of the root of its bar tree
  (`ShuffleAnySym.wkey`), and `ShuffleAnySym.wsign t` is the sign of the permutation from the
  preorder of the vertices other than the root to the order of their keys.
* **The comparison** `ShuffleAnySym.ΦL : B(T, Ī)(Fin n) → (bar trees →₀ K)` sends a basis vector
  `t` to `wsign t` times its bar tree (`ShuffleAnySym.Φ_barBasisN`); it is injective with range
  the combinations of the bar trees with no cut above the root (`ShuffleAnySym.ΦL_range`), and
  maps the trees with `s` vertices onto the bar trees with `s` components
  (`ShuffleAnySym.map_ΦL_deg`). Over a field of characteristic zero the trees with `s` vertices
  are the eigenspace `FreeGrL.vx s` of the vertex count (`ShuffleAnySym.deg_eq_vx`), so the bar
  differential lowers the degree by one (`ShuffleAnySym.d_mem_deg`).

The keys differ from the binary case: `ShuffleBarSym.vkey` counts the leaves above a vertex,
`wkey` the generators, which is what `STree.key` reads on the bar tree when the arity does not
determine the number of generators.
-/
import Operad.ShuffleBarSym
import Operad.ShuffleAnyKoszul

universe u

namespace Operad

open Sym GerBV FreeGr Bar

namespace ShuffleAnySym

open ShuffleBarSym

section Bases

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- **The shuffle-tree basis of the free graded operad on even generators of any arity**: the
evaluations of the shuffle trees. -/
noncomputable def tBasis (A : Type) [Fintype A] [LinearOrder A] :
    Module.Basis (STree.SMono T (Finset.range (Fintype.card A))) K (FreeGrL K E A) :=
  FreeGrL.shuffleBasis c (p := fun _ _ => false) hc A

/-- **The basis vectors are even.** -/
lemma par_tBasis (A : Type) [Fintype A] [LinearOrder A]
    (t : STree.SMono T (Finset.range (Fintype.card A))) :
    GrOperad.par (R := K) false (tBasis c hc A t) = tBasis c hc A t := by
  have := FreeGrL.par_shuffleBasis c (p := fun _ _ => false) hc A t
  rwa [vpar_false] at this

omit [IsEmpty (T 0)] in
/-- A shuffle tree has a leaf. -/
lemma labels_ne_zero : ∀ t : STree T, t.IsShuffle → t.labels ≠ 0
  | .leaf a, _ => by simp [STree.labels]
  | .node (k := k) e ch, h => by
    intro h0
    have h1 : (ch ⟨0, h.1⟩).labels ≤ (STree.node e ch).labels :=
      Finset.single_le_sum (f := fun i => (ch i).labels) (fun _ _ => Multiset.zero_le _)
        (Finset.mem_univ _)
    rw [h0] at h1
    exact labels_ne_zero _ (h.2.1 _) (Multiset.le_zero.1 h1)

include hc in
/-- **The free graded operad vanishes in arity zero.** -/
lemma free_zero (y : FreeGrL K E (Fin 0)) : y = 0 := by
  haveI : IsEmpty (STree.SMono T (Finset.range (Fintype.card (Fin 0)))) :=
    ⟨fun ⟨t, ht⟩ => labels_ne_zero t ht.1 (by rw [ht.2]; simp)⟩
  exact (tBasis c hc (Fin 0)).repr.injective (Subsingleton.elim _ _)

variable (K E) in
/-- **The ideal `Ī` of the free graded operad** of the operations with at least two inputs. -/
noncomputable abbrev Ibar : GrOperadIdeal K (FreeGrL K E) :=
  GrOperadIdeal.atLeastTwo K (FreeGrL K E) (free_zero c hc)

variable (T) in
/-- **The decorations of the vertices of the bar construction**: the shuffle trees on
`0, …, k - 1` with at least two leaves. -/
abbrev VMono (k : ℕ) : Type := {_t : STree.SMono T (Finset.range k) // 2 ≤ k}

instance : IsEmpty (VMono T 0) := ⟨fun ⟨_, h⟩ => absurd h (by omega)⟩

/-- The shuffle trees with at least two leaves, as indices of `tBasis`. -/
def vmonoEquiv {k : ℕ} (h : 2 ≤ k) :
    STree.SMono T (Finset.range (Fintype.card (Fin k))) ≃ VMono T k where
  toFun t := ⟨⟨t.1, t.2.1, by simpa using t.2.2⟩, h⟩
  invFun t := ⟨t.1.1, t.1.2.1, by simpa using t.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The basis of `Ī (Fin k)`**: the shuffle trees with `k ≥ 2` leaves. -/
noncomputable def idealBasis (k : ℕ) : Module.Basis (VMono T k) K ((Ibar K E c hc).sub (Fin k)) :=
  if h : 2 ≤ k then
    ((tBasis c hc (Fin k)).map (LinearEquiv.ofTop _
      (GrOperadIdeal.atLeastTwo_sub_of_le (by simpa using h))).symm).reindex (vmonoEquiv h)
  else
    haveI : IsEmpty (VMono T k) := ⟨fun t => h t.2⟩
    haveI : Subsingleton ((Ibar K E c hc).sub (Fin k)) := by
      rw [GrOperadIdeal.atLeastTwo_sub_of_lt (by simp; omega)]
      infer_instance
    Module.Basis.empty _

lemma idealBasis_apply {k : ℕ} (t : VMono T k) :
    (idealBasis c hc k t : FreeGrL K E (Fin k)) =
      tBasis c hc (Fin k) ⟨t.1.1, t.1.2.1, by simpa using t.1.2.2⟩ := by
  rw [idealBasis, dif_pos t.2, Module.Basis.reindex_apply, Module.Basis.map_apply,
    LinearEquiv.coe_ofTop_symm_apply]
  rfl

/-- **The basis of the generators `sĪ (Fin k)` of the bar construction.** -/
noncomputable def genBasis (k : ℕ) : Module.Basis (VMono T k) K (BarGen (Ibar K E c hc) (Fin k)) :=
  idealBasis c hc k

/-- **The generators of the bar construction are odd.** -/
lemma par_genBasis (k : ℕ) (t : VMono T k) :
    GrSpecies.par (R := K) ((fun _ _ => true) k t) (genBasis c hc k t) = genBasis c hc k t := by
  refine IdealSp.ext _ ?_
  show GrOperad.par (R := K) false (idealBasis c hc k t : FreeGrL K E (Fin k)) = _
  rw [idealBasis_apply, par_tBasis]
  exact (idealBasis_apply c hc t).symm

/-- **The shuffle basis of the bar construction `B(T, Ī)`**: on a finite linear order `A`, the
shuffle trees on the positions of `A` whose vertices are shuffle trees with at least two
leaves. -/
noncomputable def barBasis (A : Type) [Fintype A] [LinearOrder A] :
    Module.Basis (STree.SMono (VMono T) (Finset.range (Fintype.card A))) K
      (BarCoop (Ibar K E c hc) A) :=
  FreeGrL.shuffleBasis (genBasis c hc) (par_genBasis c hc) A

end Bases

/-! ## Bar trees from shuffle trees of monomials -/

section Trees

open STree

variable {T : ℕ → Type}

/-- **Cut the edge above the root** of a bar tree. -/
def cutRoot : STree (BE T) → STree (BE T)
  | .leaf a => .leaf a
  | .node d ch => .node (d.1, true) ch

/-- **Uncut the edge above the root** of a bar tree. -/
def uncutRoot : STree (BE T) → STree (BE T)
  | .leaf a => .leaf a
  | .node d ch => .node (d.1, false) ch

@[simp] lemma labels_cutRoot (y : STree (BE T)) : (cutRoot y).labels = y.labels := by
  cases y <;> rfl

@[simp] lemma first_cutRoot (y : STree (BE T)) : (cutRoot y).first = y.first := by
  cases y <;> rfl

@[simp] lemma weight_cutRoot (y : STree (BE T)) : (cutRoot y).weight = y.weight := by
  cases y <;> rfl

@[simp] lemma isShuffle_cutRoot (y : STree (BE T)) : (cutRoot y).IsShuffle ↔ y.IsShuffle := by
  cases y <;> rfl

@[simp] lemma key_cutRoot (y : STree (BE T)) : (cutRoot y).key = y.key := by
  rw [STree.key, STree.key, first_cutRoot, weight_cutRoot]

@[simp] lemma labels_uncutRoot (y : STree (BE T)) : (uncutRoot y).labels = y.labels := by
  cases y <;> rfl

@[simp] lemma first_uncutRoot (y : STree (BE T)) : (uncutRoot y).first = y.first := by
  cases y <;> rfl

@[simp] lemma weight_uncutRoot (y : STree (BE T)) : (uncutRoot y).weight = y.weight := by
  cases y <;> rfl

@[simp] lemma isShuffle_uncutRoot (y : STree (BE T)) :
    (uncutRoot y).IsShuffle ↔ y.IsShuffle := by
  cases y <;> rfl

lemma rootF_uncutRoot (y : STree (BE T)) : rootF (uncutRoot y) = false := by
  cases y <;> rfl

lemma uncutRoot_cutRoot {y : STree (BE T)} (hy : rootF y = false) :
    uncutRoot (cutRoot y) = y := by
  cases y with
  | leaf => rfl
  | node d ch =>
    obtain ⟨e, b⟩ := d
    simp only [rootF] at hy
    subst hy
    rfl

lemma cutRoot_injective {y y' : STree (BE T)} (hy : rootF y = false) (hy' : rootF y' = false)
    (h : cutRoot y = cutRoot y') : y = y' := by
  rw [← uncutRoot_cutRoot hy, ← uncutRoot_cutRoot hy', h]

/-- **The bar tree of a shuffle tree of monomials**: each vertex, a shuffle tree on
`0, …, k - 1`, with the bar trees of its children grafted on its leaves along cut edges. -/
def toBar : STree (VMono T) → STree (BE T)
  | .leaf a => .leaf a
  | .node (k := k) m ch => (fl false m.1.1).subst fun a =>
      if h : a < k then cutRoot (toBar (ch ⟨a, h⟩)) else .leaf a

/-- The inputs grafted on the top vertex. -/
def kids {k : ℕ} (ch : Fin k → STree (VMono T)) (a : ℕ) : STree (BE T) :=
  if h : a < k then cutRoot (toBar (ch ⟨a, h⟩)) else .leaf a

lemma toBar_node {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T)) :
    toBar (.node m ch) = (fl false m.1.1).subst (kids ch) := rfl

lemma kids_fin {k : ℕ} (ch : Fin k → STree (VMono T)) (j : Fin k) :
    kids ch j = cutRoot (toBar (ch j)) := by
  rw [kids, dif_pos j.2]

lemma kids_of_lt {k : ℕ} (ch : Fin k → STree (VMono T)) {a : ℕ} (h : a < k) :
    kids ch a = cutRoot (toBar (ch ⟨a, h⟩)) := by
  rw [kids, dif_pos h]

lemma VMono.labels {k : ℕ} (m : VMono T k) : m.1.1.labels = Multiset.range k := m.1.2.2

lemma VMono.isShuffle {k : ℕ} (m : VMono T k) : m.1.1.IsShuffle := m.1.2.1

lemma VMono.lt {k : ℕ} (m : VMono T k) {a : ℕ} (ha : a ∈ m.1.1.labels) : a < k := by
  rw [m.labels] at ha
  exact Multiset.mem_range.1 ha

lemma VMono.mem {k : ℕ} (m : VMono T k) {a : ℕ} (ha : a < k) : a ∈ m.1.1.labels := by
  rw [m.labels]
  exact Multiset.mem_range.2 ha

lemma VMono.first {k : ℕ} (m : VMono T k) : m.1.1.first = 0 :=
  Nat.le_zero.1 (STree.first_le m.isShuffle 0 (m.mem (by have := m.2; omega)))

lemma VMono.exists_node {k : ℕ} (m : VMono T k) :
    ∃ (l : ℕ) (e : T l) (c : Fin l → STree T), m.1.1 = .node e c := by
  rcases h : m.1.1 with a | ⟨e, c⟩
  · have h1 := congrArg Multiset.card m.labels
    rw [h, Multiset.card_range] at h1
    have h2 := m.2
    simp only [STree.labels, Multiset.card_singleton] at h1
    omega
  · exact ⟨_, e, c, rfl⟩

lemma bind_kids {k : ℕ} (m : VMono T k) (f : ℕ → Multiset ℕ) :
    Multiset.bind m.1.1.labels f = ∑ j : Fin k, f j := by
  rw [m.labels, Fin.sum_univ_eq_sum_range f, Finset.sum_eq_multiset_sum, Multiset.bind]
  rfl

/-- **The leaves of the bar tree are those of the shuffle tree.** -/
theorem labels_toBar : ∀ t : STree (VMono T), (toBar t).labels = t.labels
  | .leaf _ => rfl
  | .node m ch => by
    rw [toBar_node, labels_subst, labels_fl, bind_kids m, STree.labels]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [kids_fin, labels_cutRoot, labels_toBar (ch j)]

lemma rootF_toBar : ∀ t : STree (VMono T), rootF (toBar t) = false
  | .leaf _ => rfl
  | .node m ch => by
    obtain ⟨l, e, c, h⟩ := m.exists_node
    rw [toBar_node, h]
    rfl

lemma strictMonoOn_kids {k : ℕ} (m : VMono T k) {ch : Fin k → STree (VMono T)}
    (hmin : ∀ j, (toBar (ch j)).first = (ch j).first)
    (hmono : StrictMono fun j => (ch j).first) :
    StrictMonoOn (fun a => (kids ch a).first) {a | a ∈ (fl false m.1.1).labels} := by
  intro a ha b hb hab
  rw [Set.mem_setOf_eq, labels_fl] at ha hb
  have ha' := m.lt ha
  have hb' := m.lt hb
  show (kids ch a).first < (kids ch b).first
  rw [kids_of_lt ch ha', kids_of_lt ch hb', first_cutRoot, first_cutRoot, hmin, hmin]
  exact hmono (show (⟨a, ha'⟩ : Fin k) < ⟨b, hb'⟩ from hab)

/-- **The least leaf of the bar tree** is that of the shuffle tree. -/
theorem first_toBar : ∀ t : STree (VMono T), t.IsShuffle → (toBar t).first = t.first
  | .leaf _, _ => rfl
  | .node (k := k) m ch, ht => by
    rw [toBar_node, first_subst ((isShuffle_fl _ _).2 m.isShuffle), first_fl, m.first,
      first_node _ _ ht.pos, kids_of_lt ch ht.pos, first_cutRoot]
    exact first_toBar _ (ht.child _)

/-- **The bar tree of a shuffle tree is a shuffle tree.** -/
theorem isShuffle_toBar : ∀ t : STree (VMono T), t.IsShuffle → (toBar t).IsShuffle
  | .leaf _, _ => trivial
  | .node (k := k) m ch, ht => by
    rw [toBar_node]
    refine isShuffle_subst ((isShuffle_fl _ _).2 m.isShuffle) (fun a ha => ?_)
      (strictMonoOn_kids m (fun j => first_toBar (ch j) (ht.child j)) ht.mono)
    rw [labels_fl] at ha
    rw [kids_of_lt ch (m.lt ha), isShuffle_cutRoot]
    exact isShuffle_toBar _ (ht.child _)

lemma mem_labels_toBar {t : STree (VMono T)} {a : ℕ} : a ∈ (toBar t).labels ↔ a ∈ t.labels := by
  rw [labels_toBar t]

lemma nodup_toBar {t : STree (VMono T)} (h : t.labels.Nodup) : (toBar t).labels.Nodup := by
  rw [labels_toBar]
  exact h

/-! ### The cut edges of the bar tree -/

lemma cutKeys_toBar_node {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T)) :
    cutKeys (toBar (.node m ch)) = (Finset.range k).biUnion fun a => cutKeys (kids ch a) := by
  obtain ⟨l, e, c, h⟩ := m.exists_node
  ext y
  rw [toBar_node, h, mem_cutKeys_fl_subst, Finset.mem_biUnion, ← h]
  simp only [Bool.false_eq_true, false_and, false_or]
  constructor
  · rintro ⟨a, ha, hy⟩
    exact ⟨a, Finset.mem_range.2 (m.lt ha), hy⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨a, m.mem (Finset.mem_range.1 ha), hy⟩

lemma toBar_node_eq {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T)) :
    ∃ (l : ℕ) (e : T l) (c : Fin l → STree (BE T)), toBar (.node m ch) = .node (e, false) c := by
  obtain ⟨l, e, c, h⟩ := m.exists_node
  refine ⟨l, e, fun i => (allF (c i)).subst (kids ch), ?_⟩
  rw [toBar_node, h]
  rfl

lemma cutKeys_cutRoot_node {k : ℕ} (d : BE T k) (c : Fin k → STree (BE T)) :
    cutKeys (cutRoot (.node d c))
      = insert (STree.key (.node d c)) (Finset.univ.biUnion fun i => cutKeys (c i)) := by
  ext y
  rw [cutRoot, mem_cutKeys_node, Finset.mem_insert, Finset.mem_biUnion]
  simp only [true_and, Finset.mem_univ]
  rfl

lemma key_notMem_cutKeys {k : ℕ} {d : BE T k} {c : Fin k → STree (BE T)}
    (hnd : (STree.node d c).vkeys.Nodup) :
    STree.key (.node d c) ∉ Finset.univ.biUnion fun i => cutKeys (c i) := by
  intro h
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 h
  rw [vkeys_node] at hnd
  exact (Multiset.nodup_cons.1 hnd).1 (Multiset.mem_sum.2
    ⟨i, Finset.mem_univ _, mem_vkeys_of_mem_cutKeys hi⟩)

lemma card_cutKeys_cutRoot_node {k : ℕ} {e : T k} {c : Fin k → STree (BE T)}
    (hnd : (STree.node ((e, false) : BE T k) c).vkeys.Nodup) :
    (cutKeys (cutRoot (.node ((e, false) : BE T k) c))).card
      = (cutKeys (.node ((e, false) : BE T k) c)).card + 1 := by
  have e2 : cutKeys (.node ((e, false) : BE T k) c)
      = Finset.univ.biUnion fun i => cutKeys (c i) := by
    ext y
    rw [mem_cutKeys_node, Finset.mem_biUnion]
    simp
  rw [cutKeys_cutRoot_node, e2, Finset.card_insert_of_notMem (key_notMem_cutKeys hnd)]

lemma disjoint_cutKeys_kids {k : ℕ} {m : VMono T k} {ch : Fin k → STree (VMono T)}
    (hs : (STree.node m ch).IsShuffle) (hnd : (STree.node m ch).labels.Nodup) :
    (↑(Finset.range k) : Set ℕ).PairwiseDisjoint fun a => cutKeys (kids ch a) := by
  intro a ha b hb hab
  have ha' : a < k := Finset.mem_range.1 ha
  have hb' : b < k := Finset.mem_range.1 hb
  have hd := disjoint_of_node hnd (show (⟨a, ha'⟩ : Fin k) ≠ ⟨b, hb'⟩ from
    fun h => hab (congrArg Fin.val h))
  refine Finset.disjoint_left.2 fun κ h1 h2 => ?_
  simp only [kids_of_lt ch ha', kids_of_lt ch hb'] at h1 h2
  have m1 := (mem_vkeys ((isShuffle_cutRoot _).2 (isShuffle_toBar _ (hs.child _)))
    (mem_vkeys_of_mem_cutKeys h1)).1
  have m2 := (mem_vkeys ((isShuffle_cutRoot _).2 (isShuffle_toBar _ (hs.child _)))
    (mem_vkeys_of_mem_cutKeys h2)).1
  rw [labels_cutRoot, mem_labels_toBar] at m1 m2
  exact Multiset.disjoint_left.1 hd m1 m2

/-- **The number of cut edges** of the bar tree of a shuffle tree, the edge above its root cut, is
its number of vertices. -/
theorem card_cutKeys_cutRoot_toBar : ∀ t : STree (VMono T), t.IsShuffle → t.labels.Nodup →
    (cutKeys (cutRoot (toBar t))).card = t.weight
  | .leaf _, _, _ => rfl
  | .node (k := k) m ch, hs, hnd => by
    obtain ⟨l, e, c, hT⟩ := toBar_node_eq m ch
    have hv : (toBar (.node m ch)).vkeys.Nodup :=
      nodup_vkeys (isShuffle_toBar _ hs) (nodup_toBar hnd)
    rw [hT] at hv
    rw [hT, card_cutKeys_cutRoot_node hv, ← hT, cutKeys_toBar_node,
      Finset.card_biUnion (disjoint_cutKeys_kids hs hnd), STree.weight, add_comm,
      ← Fin.sum_univ_eq_sum_range (fun a => (cutKeys (kids ch a)).card)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [kids_fin, card_cutKeys_cutRoot_toBar (ch j) (hs.child j) (nodup_of_node hnd j)]

/-- **The number of components** of the bar tree of a shuffle tree with a vertex is its number of
vertices. -/
theorem card_cutKeys_toBar {k : ℕ} (m : VMono T k) (ch : Fin k → STree (VMono T))
    (hs : (STree.node m ch).IsShuffle) (hnd : (STree.node m ch).labels.Nodup) :
    (cutKeys (toBar (.node m ch))).card + 1 = (STree.node m ch).weight := by
  rw [← card_cutKeys_cutRoot_toBar _ hs hnd]
  obtain ⟨l, e, c, hT⟩ := toBar_node_eq m ch
  have hv : (toBar (.node m ch)).vkeys.Nodup :=
    nodup_vkeys (isShuffle_toBar _ hs) (nodup_toBar hnd)
  rw [hT] at hv
  rw [hT, card_cutKeys_cutRoot_node hv]

/-! ### Injectivity -/

/-- **A hanging tree**: a leaf, or a bar tree cut above its root. -/
def IsHang (y : STree (BE T)) : Prop :=
  ∀ (k : ℕ) (e : T k) (c : Fin k → STree (BE T)), y ≠ .node (e, false) c

lemma isHang_leaf (a : ℕ) : IsHang (.leaf a : STree (BE T)) := fun _ _ _ h => by cases h

lemma isHang_cutRoot (y : STree (BE T)) : IsHang (cutRoot y) := by
  cases y with
  | leaf a => exact isHang_leaf a
  | node d ch =>
    intro k e c h
    rw [cutRoot] at h
    injection h with hk he hc
    subst hk
    exact absurd (congrArg Prod.snd (eq_of_heq he)) (by simp)

lemma isHang_kids {k : ℕ} (ch : Fin k → STree (VMono T)) (a : ℕ) : IsHang (kids ch a) := by
  unfold kids
  split_ifs
  · exact isHang_cutRoot _
  · exact isHang_leaf _

lemma fl_false (t : STree T) : fl false t = allF t := by
  cases t <;> rfl

/-- **The shape of a tree with hanging trees substituted**: two such trees agree only if the
trees agree after replacing each hanging tree by its least leaf. -/
theorem subst_first_eq : ∀ (g g' : STree T) {xs xs' : ℕ → STree (BE T)},
    (∀ a ∈ g.labels, IsHang (xs a)) → (∀ a ∈ g'.labels, IsHang (xs' a)) →
    (allF g).subst xs = (allF g').subst xs' →
    g.subst (fun a => .leaf (xs a).first) = g'.subst (fun a => .leaf (xs' a).first)
  | .leaf a, .leaf a', xs, xs', _, _, h => by
    have h' : xs a = xs' a' := h
    show STree.leaf (xs a).first = STree.leaf (xs' a').first
    rw [h']
  | .leaf a, .node e c, xs, xs', hx, _, h => by
    have h' : xs a = .node (e, false) fun i => (allF (c i)).subst xs' := h
    exact absurd h' (hx a (Multiset.mem_singleton_self a) _ _ _)
  | .node e c, .leaf a', xs, xs', _, hx', h => by
    have h' : (STree.node (e, false) fun i => (allF (c i)).subst xs) = xs' a' := h
    exact absurd h'.symm (hx' a' (Multiset.mem_singleton_self a') _ _ _)
  | .node (k := k) e c, .node (k := k') e' c', xs, xs', hx, hx', h => by
    have h' : (STree.node (e, false) fun i => (allF (c i)).subst xs)
        = .node (e', false) fun i => (allF (c' i)).subst xs' := h
    injection h' with hk he hc
    subst hk
    have he' : e = e' := congrArg Prod.fst (eq_of_heq he)
    subst he'
    rw [subst_node, subst_node]
    congr 1
    funext i
    exact subst_first_eq (c i) (c' i) (fun a ha => hx a (mem_labels_node.2 ⟨i, ha⟩))
      (fun a ha => hx' a (mem_labels_node.2 ⟨i, ha⟩)) (congrFun (eq_of_heq hc) i)

/-- Relabelling the leaves by a function injective on them is injective. -/
theorem subst_leaf_injOn {F : ℕ → ℕ} {S : Set ℕ} (hF : Set.InjOn F S) :
    ∀ (g g' : STree T), (∀ a ∈ g.labels, a ∈ S) → (∀ a ∈ g'.labels, a ∈ S) →
      g.subst (fun a => .leaf (F a)) = g'.subst (fun a => .leaf (F a)) → g = g'
  | .leaf a, .leaf a', ha, ha', h => by
    have h' : STree.leaf (F a) = (STree.leaf (F a') : STree T) := h
    injection h' with h'
    rw [hF (ha a (Multiset.mem_singleton_self a)) (ha' a' (Multiset.mem_singleton_self a')) h']
  | .leaf a, .node e c, _, _, h => by
    have h' : STree.leaf (F a) = STree.node e fun i => (c i).subst fun a => .leaf (F a) := h
    cases h'
  | .node e c, .leaf a', _, _, h => by
    have h' : (STree.node e fun i => (c i).subst fun a => .leaf (F a)) = STree.leaf (F a') := h
    cases h'
  | .node (k := k) e c, .node (k := k') e' c', ha, ha', h => by
    rw [subst_node, subst_node] at h
    injection h with hk he hc
    subst hk
    have he' : e = e' := eq_of_heq he
    subst he'
    congr 1
    funext i
    exact subst_leaf_injOn hF (c i) (c' i) (fun a h => ha a (mem_labels_node.2 ⟨i, h⟩))
      (fun a h => ha' a (mem_labels_node.2 ⟨i, h⟩)) (congrFun (eq_of_heq hc) i)

/-- Substitutions in a tree agree only if they agree on its leaves. -/
theorem subst_eq_subst {E : ℕ → Type} : ∀ (t : STree E) {xs xs' : ℕ → STree E},
    t.subst xs = t.subst xs' → ∀ a ∈ t.labels, xs a = xs' a
  | .leaf b, xs, xs', h, a, ha => by
    rw [Multiset.mem_singleton.1 ha]
    exact h
  | .node e c, xs, xs', h, a, ha => by
    rw [subst_node, subst_node] at h
    injection h with _ _ hc
    obtain ⟨i, hi⟩ := mem_labels_node.1 ha
    exact subst_eq_subst (c i) (congrFun hc i) a hi

/-- Two increasing enumerations of the same finite set of numbers agree. -/
lemma range_map_eq {k k' : ℕ} {F F' : ℕ → ℕ} (hF : StrictMonoOn F (Set.Iio k))
    (hF' : StrictMonoOn F' (Set.Iio k'))
    (h : (Multiset.range k).map F = (Multiset.range k').map F') :
    k = k' ∧ ∀ a < k, F a = F' a := by
  have hk : k = k' := by
    have := congrArg Multiset.card h
    simpa using this
  subst hk
  refine ⟨rfl, fun a ha => ?_⟩
  have hs : ∀ {G : ℕ → ℕ}, StrictMonoOn G (Set.Iio k) →
      ((List.range k).map G).Pairwise (· < ·) := fun {G} hG => by
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range (n := k)).imp_of_mem fun {x y} hx hy hxy =>
      hG (List.mem_range.1 hx) (List.mem_range.1 hy) hxy
  have hp : ((List.range k).map F).Perm ((List.range k).map F') := Multiset.coe_eq_coe.1 h
  have he := hp.eq_of_pairwise (fun a b _ _ h1 h2 => absurd h1 (lt_asymm h2)) (hs hF) (hs hF')
  exact List.map_inj_left.1 he a (List.mem_range.2 ha)

lemma first_kids {k : ℕ} {ch : Fin k → STree (VMono T)} (hch : ∀ j, (ch j).IsShuffle)
    {a : ℕ} (ha : a < k) : (kids ch a).first = (ch ⟨a, ha⟩).first := by
  rw [kids_of_lt ch ha, first_cutRoot, first_toBar _ (hch _)]

lemma strictMonoOn_first_kids {k : ℕ} {m : VMono T k} {ch : Fin k → STree (VMono T)}
    (hs : (STree.node m ch).IsShuffle) :
    StrictMonoOn (fun a => (kids ch a).first) (Set.Iio k) := by
  intro a ha b hb hab
  show (kids ch a).first < (kids ch b).first
  rw [first_kids hs.child ha, first_kids hs.child hb]
  exact hs.mono (show (⟨a, ha⟩ : Fin k) < ⟨b, hb⟩ from hab)

/-- **The bar tree determines the shuffle tree of monomials.** -/
theorem toBar_injective : ∀ {t t' : STree (VMono T)}, t.IsShuffle → t'.IsShuffle →
    toBar t = toBar t' → t = t'
  | .leaf a, .leaf a', _, _, h => by
    have h' : STree.leaf a = (STree.leaf a' : STree (BE T)) := h
    injection h' with h'
    rw [h']
  | .leaf a, .node m ch, _, _, h => by
    obtain ⟨l, e, c, hT⟩ := toBar_node_eq m ch
    rw [hT] at h
    cases h
  | .node m ch, .leaf a', _, _, h => by
    obtain ⟨l, e, c, hT⟩ := toBar_node_eq m ch
    rw [hT] at h
    cases h
  | .node (k := k) m ch, .node (k := k') m' ch', hs, hs', h => by
    rw [toBar_node, toBar_node, fl_false, fl_false] at h
    have h1 := subst_first_eq m.1.1 m'.1.1 (fun a _ => isHang_kids ch a)
      (fun a _ => isHang_kids ch' a) h
    have h2 := congrArg STree.labels h1
    rw [labels_subst, labels_subst, m.labels, m'.labels] at h2
    simp only [STree.labels] at h2
    rw [Multiset.bind_singleton, Multiset.bind_singleton] at h2
    obtain ⟨hk, hF⟩ := range_map_eq (strictMonoOn_first_kids hs) (strictMonoOn_first_kids hs') h2
    subst hk
    have h3 : m'.1.1.subst (fun a => .leaf (kids ch' a).first)
        = m'.1.1.subst (fun a => .leaf (kids ch a).first) :=
      subst_congr _ fun a ha => by rw [hF a (m'.lt ha)]
    rw [h3] at h1
    have hm : m.1.1 = m'.1.1 := subst_leaf_injOn
      (strictMonoOn_first_kids hs).injOn m.1.1 m'.1.1 (fun a ha => m.lt ha)
      (fun a ha => m'.lt ha) h1
    have hmm : m = m' := Subtype.ext (Subtype.ext hm)
    subst hmm
    have hk := subst_eq_subst (allF m.1.1) h
    have hch : ch = ch' := funext fun j => by
      have h4 := hk j (by rw [labels_allF]; exact m.mem j.2)
      rw [kids_fin, kids_fin] at h4
      exact toBar_injective (hs.child j) (hs'.child j)
        (cutRoot_injective (rootF_toBar _) (rootF_toBar _) h4)
    rw [hch]

/-! ### Surjectivity -/

lemma cutRoot_uncutRoot {z : STree (BE T)} (hz : IsHang z) : cutRoot (uncutRoot z) = z := by
  cases z with
  | leaf a => rfl
  | node d c =>
    obtain ⟨e, b⟩ := d
    cases b
    · exact absurd rfl (hz _ e c)
    · rfl

lemma weight_le_node {E : ℕ → Type} {k : ℕ} (e : E k) (c : Fin k → STree E) (i : Fin k) :
    (c i).weight < (STree.node e c).weight := by
  have h : (c i).weight ≤ ∑ j, (c j).weight :=
    Finset.single_le_sum (f := fun j => (c j).weight) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  show (c i).weight < 1 + ∑ j, (c j).weight
  omega

/-- **A bar tree is its top component with hanging trees substituted**: the top component has
the least leaves of the hanging trees as its leaves. -/
theorem exists_hang : ∀ y : STree (BE T), y.IsShuffle → y.labels.Nodup →
    ∃ (g : STree T) (xs : ℕ → STree (BE T)), g.IsShuffle ∧ (allF g).subst xs = y ∧
      g.labels ≤ y.labels ∧ g.first = y.first ∧
      ∀ a ∈ g.labels, IsHang (xs a) ∧ (xs a).first = a ∧ (xs a).IsShuffle ∧
        (xs a).labels ≤ y.labels ∧
        ∀ (k : ℕ) (e : T k) (c : Fin k → STree (BE T)), y = .node (e, false) c →
          (xs a).weight < y.weight
  | .leaf b, _, _ => ⟨.leaf b, .leaf, trivial, rfl, le_rfl, rfl, fun a ha => by
      rw [STree.labels, Multiset.mem_singleton] at ha
      subst ha
      exact ⟨isHang_leaf a, rfl, trivial, le_rfl, fun k e c h => by cases h⟩⟩
  | .node (k := k) (e, true) c, hs, _ =>
    ⟨.leaf (STree.node (e, true) c).first, fun _ => .node (e, true) c, trivial, rfl,
      Multiset.singleton_le.2 (first_mem hs), rfl, fun a ha => by
        rw [STree.labels, Multiset.mem_singleton] at ha
        subst ha
        refine ⟨fun k' e' c' h => ?_, rfl, hs, le_rfl, fun k' e' c' h => ?_⟩
        · injection h with hk he hc
          subst hk
          exact absurd (congrArg Prod.snd (eq_of_heq he)) (by simp)
        · injection h with hk he hc
          subst hk
          exact absurd (congrArg Prod.snd (eq_of_heq he)) (by simp)⟩
  | .node (k := k) (e, false) c, hs, hnd => by
    have ih := fun i => exists_hang (c i) (hs.child i) (nodup_of_node hnd i)
    choose g xs hg hsub hle hfirst hx using ih
    have hgn : (STree.node e g).labels.Nodup :=
      Multiset.nodup_of_le (Finset.sum_le_sum fun i _ => hle i) hnd
    obtain ⟨G, hG⟩ := exists_glue hgn xs
    refine ⟨.node e g, G, ⟨hs.pos, hg, fun i j hij => ?_⟩, ?_,
      Finset.sum_le_sum fun i _ => hle i, ?_, fun a ha => ?_⟩
    · show (g i).first < (g j).first
      rw [hfirst i, hfirst j]
      exact hs.mono hij
    · rw [allF_node, subst_node]
      congr 1
      funext i
      rw [← hsub i]
      exact subst_congr _ fun a ha => hG i a (by rwa [labels_allF] at ha)
    · rw [first_node _ _ hs.pos, first_node _ _ hs.pos, hfirst]
    · obtain ⟨i, hi⟩ := mem_labels_node.1 ha
      obtain ⟨h1, h2, h3, h4, -⟩ := hx i a hi
      rw [hG i a hi]
      refine ⟨h1, h2, h3, h4.trans (labels_le_node _ c i), fun k' e' c' _ => ?_⟩
      have hw : ((xs i a).weight ≤ (c i).weight) := by
        have h5 := hsub i
        have h6 := congrArg STree.weight h5
        rw [weight_subst] at h6
        have hmem : (xs i a).weight ∈ ((allF (g i)).labels.map fun b => (xs i b).weight) :=
          Multiset.mem_map.2 ⟨a, by rw [labels_allF]; exact hi, rfl⟩
        have hle' := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
        omega
      exact lt_of_le_of_lt hw (weight_le_node _ c i)

lemma univ_map_val (k : ℕ) :
    (Finset.univ : Finset (Fin k)).val.map (fun j : Fin k => (j : ℕ)) = Multiset.range k := by
  have h : (Finset.univ : Finset (Fin k)).map Fin.valEmbedding = Finset.range k := by
    ext a
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    exact ⟨fun ⟨j, hj⟩ => hj ▸ j.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩
  have h' := congrArg Finset.val h
  rw [Finset.map_val, Finset.range_val] at h'
  exact h'

section Surj

variable [IsEmpty (T 0)] [IsEmpty (T 1)]

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma card_labels_pos {t : STree T} (h : t.IsShuffle) : 0 < Multiset.card t.labels :=
  Multiset.card_pos.2 (labels_ne_zero t h)

/-- A shuffle tree with a vertex has at least two leaves: there are no generators with fewer
than two inputs. -/
lemma two_le_card_labels {k : ℕ} {e : T k} {c : Fin k → STree T}
    (h : (STree.node e c).IsShuffle) : 2 ≤ Multiset.card (STree.node e c).labels := by
  have hk : 2 ≤ k := by
    rcases k with _ | _ | k
    · exact isEmptyElim e
    · exact isEmptyElim e
    · omega
  have hc : Multiset.card (∑ i, (c i).labels) = ∑ i, Multiset.card (c i).labels :=
    map_sum Multiset.cardHom _ _
  rw [labels_node, hc]
  calc 2 ≤ k := hk
    _ = ∑ _i : Fin k, 1 := by simp
    _ ≤ ∑ i, Multiset.card (c i).labels :=
      Finset.sum_le_sum fun i _ => card_labels_pos (h.child i)

/-- **Every shuffle bar tree with distinct leaves and no cut above its root is the bar tree of a
shuffle tree of monomials.** -/
theorem exists_toBar : ∀ (N : ℕ) (y : STree (BE T)), y.weight ≤ N → y.IsShuffle →
    y.labels.Nodup → rootF y = false → ∃ t : STree (VMono T), t.IsShuffle ∧ toBar t = y
  | _, .leaf a, _, _, _, _ => ⟨.leaf a, trivial, rfl⟩
  | 0, .node d c, hw, _, _, _ => by
    simp only [STree.weight] at hw
    omega
  | N + 1, .node (e, b) c, hw, hs, hnd, hr => by
    have hb : b = false := hr
    subst hb
    obtain ⟨g, xs, hg, hsub, hle, -, hx⟩ := exists_hang _ hs hnd
    rcases g with a | ⟨e₀, c₀⟩
    · exact absurd hsub ((hx a (Multiset.mem_singleton_self a)).1 _ _ _)
    have hgn : (STree.node e₀ c₀).labels.Nodup := Multiset.nodup_of_le hle hnd
    obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S.val = (STree.node e₀ c₀).labels := ⟨⟨_, hgn⟩, rfl⟩
    have hmemS : ∀ {a}, a ∈ S ↔ a ∈ (STree.node e₀ c₀).labels := fun {a} => by
      rw [← hS]
      exact Iff.rfl
    obtain ⟨k, hk⟩ : ∃ k, S.card = k := ⟨_, rfl⟩
    have hk2 : 2 ≤ k := by
      rw [← hk, Finset.card_def, hS]
      exact two_le_card_labels hg
    have hiso : ∀ j, ((S.orderIsoOfFin hk j : S) : ℕ) = S.orderEmbOfFin hk j := fun j =>
      Finset.coe_orderIsoOfFin_apply S hk j
    have hr0 : ∀ a (h : a ∈ S), ∃ j : Fin k, S.orderEmbOfFin hk j = a := fun a h =>
      ⟨(S.orderIsoOfFin hk).symm ⟨a, h⟩, by rw [← hiso, OrderIso.apply_symm_apply]⟩
    classical
    let r : ℕ → ℕ := fun a => if h : a ∈ S then ((hr0 a h).choose : ℕ) else 0
    have hFr : ∀ a (h : a ∈ S), ∃ hlt : r a < k, S.orderEmbOfFin hk ⟨r a, hlt⟩ = a :=
      fun a h => by
        have h1 : r a = ((hr0 a h).choose : ℕ) := dif_pos h
        refine ⟨by rw [h1]; exact (hr0 a h).choose.2, ?_⟩
        have h2 : (⟨r a, by rw [h1]; exact (hr0 a h).choose.2⟩ : Fin k) = (hr0 a h).choose :=
          Fin.ext h1
        rw [h2]
        exact (hr0 a h).choose_spec
    have hrF : ∀ j : Fin k, r (S.orderEmbOfFin hk j) = j := fun j => by
      obtain ⟨hlt, h1⟩ := hFr _ (S.orderEmbOfFin_mem hk j)
      have h2 := (S.orderEmbOfFin hk).injective h1
      exact congrArg Fin.val h2
    have hrmono : StrictMonoOn r {a | a ∈ (STree.node e₀ c₀).labels} := by
      intro a ha b hb hab
      obtain ⟨hla, h1⟩ := hFr a (hmemS.2 ha)
      obtain ⟨hlb, h2⟩ := hFr b (hmemS.2 hb)
      by_contra hcon
      have h3 : (⟨r b, hlb⟩ : Fin k) ≤ ⟨r a, hla⟩ := not_lt.1 hcon
      have h4 := (S.orderEmbOfFin hk).monotone h3
      rw [h1, h2] at h4
      exact absurd hab (not_lt.2 h4)
    have hm0s : ((STree.node e₀ c₀).subst fun a => STree.leaf (r a)).IsShuffle :=
      isShuffle_subst hg (fun _ _ => trivial) hrmono
    have hm0l : ((STree.node e₀ c₀).subst fun a => STree.leaf (r a)).labels
        = (Finset.range k).val := by
      rw [labels_subst]
      show Multiset.bind _ (fun a => ({r a} : Multiset ℕ)) = _
      rw [Multiset.bind_singleton, ← hS, ← Finset.map_orderEmbOfFin_univ S hk, Finset.map_val,
        Multiset.map_map, Finset.range_val, ← univ_map_val]
      exact Multiset.map_congr rfl fun j _ => hrF j
    have hxS : ∀ j : Fin k, S.orderEmbOfFin hk j ∈ (STree.node e₀ c₀).labels := fun j =>
      hmemS.1 (S.orderEmbOfFin_mem hk j)
    have hch : ∀ j : Fin k, ∃ t : STree (VMono T), t.IsShuffle ∧
        toBar t = uncutRoot (xs (S.orderEmbOfFin hk j)) := fun j => by
      obtain ⟨-, -, h3, h4, h5⟩ := hx _ (hxS j)
      have h6 := h5 _ e c rfl
      exact exists_toBar N _ (by rw [weight_uncutRoot]; omega) ((isShuffle_uncutRoot _).2 h3)
        (by rw [labels_uncutRoot]; exact Multiset.nodup_of_le h4 hnd) (rootF_uncutRoot _)
    choose t ht1 ht2 using hch
    refine ⟨.node ⟨⟨_, hm0s, hm0l⟩, hk2⟩ t, ⟨by omega, ht1, fun i j hij => ?_⟩, ?_⟩
    · show (t i).first < (t j).first
      rw [← first_toBar _ (ht1 i), ← first_toBar _ (ht1 j), ht2, ht2, first_uncutRoot,
        first_uncutRoot, (hx _ (hxS i)).2.1, (hx _ (hxS j)).2.1]
      exact (S.orderEmbOfFin hk).strictMono hij
    · rw [toBar_node, fl_false]
      show (allF ((STree.node e₀ c₀).subst fun a => STree.leaf (r a))).subst (kids t) = _
      rw [allF_subst, subst_subst, ← hsub]
      refine subst_congr _ fun a ha => ?_
      rw [labels_allF] at ha
      obtain ⟨hlt, h1⟩ := hFr a (hmemS.2 ha)
      show kids t (r a) = xs a
      rw [kids_of_lt t hlt, ht2, cutRoot_uncutRoot (hx _ (hxS _)).1, h1]

end Surj

end Trees

/-! ## Keys and signs -/

section Keys

variable {T : ℕ → Type}

/-- **The key of a vertex** of a shuffle tree of monomials: the key of the root of its bar tree,
the least leaf and the number of generators above the vertex. -/
def wkey (t : STree (VMono T)) : ℕ ×ₗ ℕ := STree.key (toBar t)

/-- **The keys of the vertices in preorder**: the root, then the children from left to right. -/
def wKeys : STree (VMono T) → List (ℕ ×ₗ ℕ)
  | STree.leaf _ => []
  | t@(STree.node _ ch) => wkey t :: (List.ofFn fun j => wKeys (ch j)).flatten

lemma length_wKeys : ∀ t : STree (VMono T), (wKeys t).length = t.weight
  | .leaf _ => rfl
  | .node _ ch => by
    simp only [wKeys, List.length_cons, List.length_flatten, List.map_ofFn, List.sum_ofFn,
      STree.weight, Function.comp_def, length_wKeys]
    omega

variable (K : Type u) [CommRing K]

/-- **The sign of a shuffle tree of monomials**: the sign of the permutation from the preorder of
its vertices other than the root, the order of composition in `FreeGrL`, to the order of their
keys, the order of the cut edges in `STree.Bar.d`. -/
def wsign (t : STree (VMono T)) : K := (-1) ^ inv (wKeys t).tail

lemma isUnit_wsign (t : STree (VMono T)) : IsUnit (wsign K t) :=
  (isUnit_neg_one (α := K)).pow _

lemma wsign_mul_self (t : STree (VMono T)) : wsign K t * wsign K t = 1 := by
  rw [wsign, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

end Keys

/-! ## The comparison `Φ` -/

section Equiv

open STree

variable {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]

variable (T) in
/-- **The bar trees of the bar construction in arity `n`**: the shuffle bar trees on
`0, …, n - 1` with no cut above the root. -/
def barSet (n : ℕ) : Set (SMono (BE T) (Finset.range n)) := {X | rootF X.1 = false}

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma toBar_mem {Y : Finset ℕ} (t : SMono (VMono T) Y) :
    (toBar t.1).IsShuffle ∧ (toBar t.1).labels = Y.val :=
  ⟨isShuffle_toBar _ t.2.1, by rw [labels_toBar, t.2.2]⟩

/-- **The shuffle trees of monomials on `0, …, n - 1` are the bar trees of the bar construction**
in arity `n`, by `toBar`. -/
noncomputable def treeEquiv (n : ℕ) : SMono (VMono T) (Finset.range n) ≃ barSet T n :=
  Equiv.ofBijective (fun t => ⟨⟨toBar t.1, toBar_mem t⟩, rootF_toBar _⟩)
    ⟨fun t t' h => Subtype.ext (toBar_injective t.2.1 t'.2.1
        (congrArg (fun X : barSet T n => X.1.1) h)),
      fun X => by
        obtain ⟨t, ht, hb⟩ := exists_toBar X.1.1.weight X.1.1 le_rfl X.1.2.1
          (by rw [X.1.2.2]; exact Finset.nodup _) X.2
        refine ⟨⟨t, ht, ?_⟩, Subtype.ext (Subtype.ext hb)⟩
        rw [← labels_toBar, hb, X.1.2.2]⟩

@[simp] lemma treeEquiv_apply {n : ℕ} (t : SMono (VMono T) (Finset.range n)) :
    ((treeEquiv n t : barSet T n) : SMono (BE T) (Finset.range n)).1 = toBar t.1 := rfl

end Equiv

section Phi

open STree

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- The shuffle basis of the bar construction in arity `n`, on the leaves `0, …, n - 1`. -/
noncomputable def barBasisN (n : ℕ) :
    Module.Basis (SMono (VMono T) (Finset.range n)) K (BarCoop (Ibar K E c hc) (Fin n)) :=
  (barBasis c hc (Fin n)).reindex (smonoCast (by rw [Fintype.card_fin]))

omit [IsEmpty (T 1)] in
lemma barBasisN_apply (n : ℕ) (t : SMono (VMono T) (Finset.range n)) :
    barBasisN c hc n t = barBasis c hc (Fin n) (t.cast (by rw [Fintype.card_fin])) := by
  rw [barBasisN, Module.Basis.reindex_apply]
  rfl

/-- The shuffle basis twisted by the signs. -/
noncomputable def signedBasis (n : ℕ) :
    Module.Basis (SMono (VMono T) (Finset.range n)) K (BarCoop (Ibar K E c hc) (Fin n)) :=
  (barBasisN c hc n).isUnitSMul fun t => isUnit_wsign K t.1

/-- **The comparison of the bar constructions**: `B(T, Ī)(Fin n)`, for `T` the free graded operad
on even generators of any arity, is the span of the bar trees of arity `n` in the bar
construction of the free shuffle operad on the same generators, a shuffle basis vector `t` going
to `sign t` times its bar tree (`Φ_barBasisN`). -/
noncomputable def Φ (n : ℕ) :
    BarCoop (Ibar K E c hc) (Fin n) ≃ₗ[K] Finsupp.supported K K (barSet T n) :=
  (signedBasis c hc n).repr ≪≫ₗ Finsupp.domLCongr (treeEquiv n) ≪≫ₗ
    (Finsupp.supportedEquivFinsupp (barSet T n)).symm

/-- `Φ` as a linear map into the combinations of bar trees. -/
noncomputable def ΦL (n : ℕ) :
    BarCoop (Ibar K E c hc) (Fin n) →ₗ[K] (SMono (BE T) (Finset.range n) →₀ K) :=
  (Finsupp.supported K K (barSet T n)).subtype ∘ₗ (Φ c hc n).toLinearMap

lemma ΦL_injective (n : ℕ) : Function.Injective (ΦL c hc n) :=
  (Submodule.subtype_injective _).comp (Φ c hc n).injective

lemma ΦL_range (n : ℕ) : LinearMap.range (ΦL c hc n) = Finsupp.supported K K (barSet T n) := by
  rw [ΦL, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

lemma ΦL_signedBasis (n : ℕ) (t : SMono (VMono T) (Finset.range n)) :
    ΦL c hc n (signedBasis c hc n t) = Finsupp.single (treeEquiv n t : barSet T n).1 1 := by
  classical
  simp only [ΦL, Φ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, Module.Basis.repr_self, Finsupp.domLCongr_single,
    Submodule.coe_subtype]
  rw [Finsupp.supportedEquivFinsupp_symm_apply_coe, Finsupp.extendDomain_single]

/-- **`Φ` on the shuffle basis**: a basis vector goes to its bar tree, with the sign of the
tree. -/
theorem Φ_barBasisN (n : ℕ) (t : SMono (VMono T) (Finset.range n)) :
    ΦL c hc n (barBasisN c hc n t)
      = wsign K t.1 • Finsupp.single (treeEquiv n t : barSet T n).1 1 := by
  have : barBasisN c hc n t = wsign K t.1 • signedBasis c hc n t := by
    rw [signedBasis, Module.Basis.isUnitSMul_apply, smul_smul, wsign_mul_self, one_smul]
  rw [this, map_smul, ΦL_signedBasis]

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma exists_node_of_two_le {n : ℕ} (hn : 2 ≤ n) (t : SMono (VMono T) (Finset.range n)) :
    ∃ (k : ℕ) (m : VMono T k) (ch : Fin k → STree (VMono T)), t.1 = STree.node m ch := by
  rcases h : t.1 with a | ⟨m, ch⟩
  · have h1 := congrArg Multiset.card t.2.2
    rw [h, STree.labels_leaf, Multiset.card_singleton, Finset.range_val, Multiset.card_range] at h1
    omega
  · exact ⟨_, m, ch, rfl⟩

/-- **Degrees.** In arity `n ≥ 2`, the bar tree of a shuffle tree with `s` vertices has `s`
components. -/
theorem card_cuts_treeEquiv {n : ℕ} (hn : 2 ≤ n) (t : SMono (VMono T) (Finset.range n)) :
    (STree.cuts (treeEquiv n t : barSet T n).1).card + 1 = t.1.weight := by
  obtain ⟨k, m, ch, h⟩ := exists_node_of_two_le hn t
  show (cutKeys (toBar t.1)).card + 1 = _
  rw [h, card_cutKeys_toBar m ch (by rw [← h]; exact t.2.1)
    (by rw [← h, t.2.2]; exact Finset.nodup _)]

variable (T) in
/-- The bar trees of arity `n` with `s` components. -/
def compSet (n s : ℕ) : Set (SMono (BE T) (Finset.range n)) :=
  {X | rootF X.1 = false ∧ (STree.cuts X).card + 1 = s}

/-- **The vertex grading of the bar construction**: in arity `n`, the span of the shuffle basis
vectors whose trees have `s` vertices. -/
noncomputable def deg (n s : ℕ) : Submodule K (BarCoop (Ibar K E c hc) (Fin n)) :=
  Submodule.span K (barBasisN c hc n '' {t | t.1.weight = s})

/-- **`Φ` respects the degrees**: in arity `n ≥ 2` it sends the trees with `s` vertices onto the
bar trees with `s` components. -/
theorem map_ΦL_deg {n : ℕ} (hn : 2 ≤ n) (s : ℕ) :
    Submodule.map (ΦL c hc n) (deg c hc n s) = Finsupp.supported K K (compSet T n s) := by
  rw [deg, Submodule.map_span, Finsupp.supported_eq_span_single]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Φ_barBasisN c hc n t]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(treeEquiv n t : barSet T n).1, ?_, rfl⟩)
    exact ⟨(treeEquiv n t).2, (card_cuts_treeEquiv hn t).trans ht⟩
  · rw [Submodule.span_le]
    rintro _ ⟨X, hX, rfl⟩
    obtain ⟨t, ht⟩ := (treeEquiv n).surjective ⟨X, hX.1⟩
    have hX' : (treeEquiv n t : barSet T n).1 = X := congrArg Subtype.val ht
    have hw : t.1.weight = s := by
      rw [← card_cuts_treeEquiv hn t, hX']
      exact hX.2
    have hmem : ΦL c hc n (barBasisN c hc n t) ∈
        Submodule.span K (ΦL c hc n '' (barBasisN c hc n ''
          {t : SMono (VMono T) (Finset.range n) | t.1.weight = s})) :=
      Submodule.subset_span ⟨_, ⟨t, hw, rfl⟩, rfl⟩
    rw [Φ_barBasisN c hc n t, hX'] at hmem
    have := Submodule.smul_mem _ (wsign K t.1) hmem
    rwa [smul_smul, wsign_mul_self, one_smul] at this

omit [IsEmpty (T 1)] in
/-- **The degrees exhaust the bar construction.** -/
theorem iSup_deg (n : ℕ) : ⨆ s, deg c hc n s = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← (barBasisN c hc n).span_eq, Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  exact Submodule.mem_iSup_of_mem t.1.weight (Submodule.subset_span ⟨t, rfl, rfl⟩)

omit [IsEmpty (T 1)] in
/-- **A basis vector of a tree with `s` vertices has `s` vertices**: it lies in the eigenspace
`FreeGrL.vx s` of the vertex count. -/
theorem barBasisN_mem_vx (n : ℕ) (t : SMono (VMono T) (Finset.range n)) :
    barBasisN c hc n t ∈ FreeGrL.vx K (BarGen (Ibar K E c hc)) t.1.weight (Fin n) := by
  rw [barBasisN_apply, barBasis]
  erw [FreeGrL.shuffleBasis_apply (genBasis c hc) (par_genBasis c hc)]
  exact FreeGrL.map_mem_eig _ (FreeGrL.shEv_mem_vx (genBasis c hc) (par_genBasis c hc) _ t.1
    le_rfl t.2.1 _ _)

omit [IsEmpty (T 1)] in
lemma deg_le_vx (n s : ℕ) : deg c hc n s ≤ FreeGrL.vx K (BarGen (Ibar K E c hc)) s (Fin n) := by
  rw [deg, Submodule.span_le]
  rintro _ ⟨t, ht, rfl⟩
  have := barBasisN_mem_vx c hc n t
  rw [ht] at this
  exact this

variable [CharZero K]

omit [IsEmpty (T 1)] in
/-- **The vertex grading is the vertex count**: `deg n s` is the eigenspace `FreeGrL.vx s`, over
a field of characteristic zero. -/
theorem deg_eq_vx (n s : ℕ) : deg c hc n s = FreeGrL.vx K (BarGen (Ibar K E c hc)) s (Fin n) := by
  refine le_antisymm (deg_le_vx c hc n s) fun x hx => ?_
  have hx' : x ∈ deg c hc n s ⊔ ⨆ i, ⨆ (_ : i ≠ s), deg c hc n i := by
    rw [← iSup_split_single (fun i => deg c hc n i) s, iSup_deg]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
  have hzv : z ∈ FreeGrL.vx K (BarGen (Ibar K E c hc)) s (Fin n) := by
    have := Submodule.sub_mem _ hx (deg_le_vx c hc n s hy)
    rwa [add_sub_cancel_left] at this
  have hzo : z ∈ ⨆ i, ⨆ (_ : i ≠ s), FreeGrL.vx K (BarGen (Ibar K E c hc)) i (Fin n) :=
    (iSup₂_mono fun i _ => deg_le_vx c hc n i) hz
  have hind := iSupIndep_def.1 (iSupIndep_eigenspace_nat
    ((FreeGrL.derSp (GrSpEnd.id K (BarGen (Ibar K E c hc)))).app (Fin n))) s
  have hz0 : z = 0 := Submodule.disjoint_def.1 hind z hzv hzo
  rw [hz0, add_zero]
  exact hy

omit [IsEmpty (T 1)] in
/-- **The bar differential lowers the degree by one.** -/
theorem d_mem_deg {n s : ℕ} {x : BarCoop (Ibar K E c hc) (Fin n)} (hx : x ∈ deg c hc n (s + 1)) :
    Bar.d (Ibar K E c hc) (Fin n) x ∈ deg c hc n s := by
  rw [deg_eq_vx] at hx ⊢
  exact Bar.d_vx_succ hx

end Phi

end ShuffleAnySym

end Operad
