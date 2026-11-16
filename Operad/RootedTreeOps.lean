/-
# Operations on labelled rooted trees: grafting several trees, relabelling, insertion

Three operations on `RootedTree` (`Operad.RootedTree`), used for the composition of the pre-Lie
operad in the basis of trees (`Operad.PreLieInsertion`):

* **Grafting several trees at vertices of a tree.** `RootedTree.graftF S k U f` grafts the trees
  `U j` at the vertices `f j` of `S`, one after another; its vertex set is the union and its
  parents are those of the pieces, with the root of `U j` attached to `f j`
  (`RootedTree.graftF_S`, `RootedTree.graftF_par_of_mem`), and a tree with these data is the
  grafting (`RootedTree.eq_graftF_of`). Grafting one more tree inside one of the grafted trees is
  grafting into that tree (`RootedTree.graft_graftF_of_mem`).
* **Relabelling.** `RootedTree.map g hg T` relabels `T` along an injective map `g`; it is
  injective (`RootedTree.map_injective`) and commutes with grafting and joining
  (`RootedTree.map_graft`, `RootedTree.map_joinF`).
* **Insertion at a vertex.** `RootedTree.ins T S i g` replaces the vertex `i` of `T` by the tree
  `S`: the root of `S` takes the place of `i` below the parent of `i`, and each child `c` of `i`
  (`RootedTree.childrenOf`) is attached to the vertex `g c` of `S`. It is defined when `i` is a
  vertex of `T`, the vertex sets are disjoint and the children of `i` go to vertices of `S`
  (`RootedTree.InsOK`), and is `T` otherwise.
-/
import Operad.RootedTree

namespace Operad

namespace RootedTree

variable {A : Type*} [DecidableEq A]

/-- **Grafting trees at vertices of a tree**: `U j` at the vertex `f j` of `S`, one after
another. -/
def graftF (S : RootedTree A) : (k : ℕ) → (Fin k → RootedTree A) → (Fin k → A) → RootedTree A
  | 0, _, _ => S
  | k + 1, U, f => graft (graftF S k (Fin.init U) (Fin.init f)) (U (Fin.last k)) (f (Fin.last k))

/-- The conditions for grafting trees at vertices of `S`: the vertices are vertices of `S`, and
the vertex sets are pairwise disjoint and disjoint from that of `S`. -/
structure GraftOK (S : RootedTree A) {k : ℕ} (U : Fin k → RootedTree A) (f : Fin k → A) :
    Prop where
  mem : ∀ i, f i ∈ S.S
  disjS : ∀ i, Disjoint S.S (U i).S
  disj : ∀ i j, i ≠ j → Disjoint (U i).S (U j).S

omit [DecidableEq A] in
lemma GraftOK.init {S : RootedTree A} {k : ℕ} {U : Fin (k + 1) → RootedTree A}
    {f : Fin (k + 1) → A} (h : GraftOK S U f) : GraftOK S (Fin.init U) (Fin.init f) :=
  ⟨fun _ => h.mem _, fun _ => h.disjS _,
    fun _ _ hij => h.disj _ _ fun e => hij (Fin.castSucc_injective _ e)⟩

lemma graftF_S_root : ∀ {k : ℕ} {S : RootedTree A} {U : Fin k → RootedTree A} {f : Fin k → A},
    GraftOK S U f →
      (graftF S k U f).S = S.S ∪ Finset.univ.biUnion (fun i => (U i).S) ∧
        (graftF S k U f).root = S.root
  | 0, S, U, f, _ => by simp [graftF]
  | k + 1, S, U, f, h => by
    obtain ⟨hS, hR⟩ := graftF_S_root h.init
    have hd : Disjoint (graftF S k (Fin.init U) (Fin.init f)).S (U (Fin.last k)).S := by
      rw [hS, Finset.disjoint_union_left, Finset.disjoint_biUnion_left]
      exact ⟨h.disjS _, fun i _ => h.disj _ _ (Fin.castSucc_lt_last i).ne⟩
    have hv : f (Fin.last k) ∈ (graftF S k (Fin.init U) (Fin.init f)).S := by
      rw [hS]
      exact Finset.mem_union_left _ (h.mem _)
    refine ⟨?_, ?_⟩
    · show (graft (graftF S k (Fin.init U) (Fin.init f)) (U (Fin.last k)) (f (Fin.last k))).S = _
      rw [graft_S hd hv, hS]
      ext a
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Fin.exists_fin_succ', Fin.init]
      tauto
    · show (graft (graftF S k (Fin.init U) (Fin.init f)) (U (Fin.last k)) (f (Fin.last k))).root
        = _
      rw [graft_root hd hv, hR]

lemma graftF_S {k : ℕ} {S : RootedTree A} {U : Fin k → RootedTree A} {f : Fin k → A}
    (h : GraftOK S U f) : (graftF S k U f).S = S.S ∪ Finset.univ.biUnion (fun i => (U i).S) :=
  (graftF_S_root h).1

lemma graftF_root {k : ℕ} {S : RootedTree A} {U : Fin k → RootedTree A} {f : Fin k → A}
    (h : GraftOK S U f) : (graftF S k U f).root = S.root :=
  (graftF_S_root h).2

lemma disjoint_graftF_last {k : ℕ} {S : RootedTree A} {U : Fin (k + 1) → RootedTree A}
    {f : Fin (k + 1) → A} (h : GraftOK S U f) :
    Disjoint (graftF S k (Fin.init U) (Fin.init f)).S (U (Fin.last k)).S := by
  rw [graftF_S h.init, Finset.disjoint_union_left, Finset.disjoint_biUnion_left]
  exact ⟨h.disjS _, fun i _ => h.disj _ _ (Fin.castSucc_lt_last i).ne⟩

lemma last_mem_graftF {k : ℕ} {S : RootedTree A} {U : Fin (k + 1) → RootedTree A}
    {f : Fin (k + 1) → A} (h : GraftOK S U f) :
    f (Fin.last k) ∈ (graftF S k (Fin.init U) (Fin.init f)).S := by
  rw [graftF_S h.init]
  exact Finset.mem_union_left _ (h.mem _)

/-- **The parent function of the grafted tree, on the vertices of one of the grafted trees.** -/
lemma graftF_par_of_mem : ∀ {k : ℕ} {S : RootedTree A} {U : Fin k → RootedTree A}
    {f : Fin k → A}, GraftOK S U f → ∀ (i : Fin k) {a : A}, a ∈ (U i).S →
      (graftF S k U f).par a = if a = (U i).root then f i else (U i).par a
  | 0, _, _, _, _, i, _, _ => i.elim0
  | k + 1, S, U, f, h, i, a, ha => by
    show (graft (graftF S k (Fin.init U) (Fin.init f)) (U (Fin.last k)) (f (Fin.last k))).par a
      = _
    rw [graft_par (disjoint_graftF_last h) (last_mem_graftF h), graftPar]
    induction i using Fin.lastCases with
    | last =>
      by_cases h1 : a = (U (Fin.last k)).root
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1, if_pos ha]
    | cast i =>
      have hna : a ∉ (U (Fin.last k)).S :=
        Finset.disjoint_left.1 (h.disj _ _ (Fin.castSucc_lt_last i).ne) ha
      have hnr : a ≠ (U (Fin.last k)).root := fun e => hna (e ▸ (U (Fin.last k)).root_mem)
      rw [if_neg hnr, if_neg hna]
      exact graftF_par_of_mem h.init i ha

/-- **The parent function of the grafted tree, away from the grafted trees.** -/
lemma graftF_par_of_not_mem : ∀ {k : ℕ} {S : RootedTree A} {U : Fin k → RootedTree A}
    {f : Fin k → A}, GraftOK S U f → ∀ {a : A}, (∀ i, a ∉ (U i).S) →
      (graftF S k U f).par a = S.par a
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, S, U, f, h, a, ha => by
    show (graft (graftF S k (Fin.init U) (Fin.init f)) (U (Fin.last k)) (f (Fin.last k))).par a
      = _
    rw [graft_par (disjoint_graftF_last h) (last_mem_graftF h), graftPar]
    have hnr : a ≠ (U (Fin.last k)).root := fun e => ha _ (e ▸ (U (Fin.last k)).root_mem)
    rw [if_neg hnr, if_neg (ha _)]
    exact graftF_par_of_not_mem h.init fun i => ha _

/-- **A tree is a grafted tree** when it has the vertices, the root and the parent function of
one. -/
theorem eq_graftF_of {k : ℕ} {S : RootedTree A} {U : Fin k → RootedTree A} {f : Fin k → A}
    (h : GraftOK S U f) (T : RootedTree A)
    (hS : T.S = S.S ∪ Finset.univ.biUnion fun i => (U i).S) (hroot : T.root = S.root)
    (hpar : ∀ i a, a ∈ (U i).S → T.par a = if a = (U i).root then f i else (U i).par a)
    (hpar' : ∀ a, (∀ i, a ∉ (U i).S) → T.par a = S.par a) :
    T = graftF S k U f := by
  ext a
  · rw [hS, graftF_S h]
  · by_cases ha : ∃ i, a ∈ (U i).S
    · obtain ⟨i, hi⟩ := ha
      rw [hpar i a hi, graftF_par_of_mem h i hi]
    · simp only [not_exists] at ha
      rw [hpar' a ha, graftF_par_of_not_mem h ha]
  · rw [hroot, graftF_root h]

/-- **Grafting at a vertex of the base tree grafts one more tree.** -/
lemma graft_graftF_base {k : ℕ} (S : RootedTree A) (U : Fin k → RootedTree A) (f : Fin k → A)
    (W : RootedTree A) (v : A) :
    graft (graftF S k U f) W v
      = graftF S (k + 1) (Fin.snoc (α := fun _ => RootedTree A) U W)
          (Fin.snoc (α := fun _ => A) f v) := by
  show _ = graft (graftF S k (Fin.init (Fin.snoc (α := fun _ => RootedTree A) U W))
    (Fin.init (Fin.snoc (α := fun _ => A) f v)))
    (Fin.snoc (α := fun _ => RootedTree A) U W (Fin.last k))
    (Fin.snoc (α := fun _ => A) f v (Fin.last k))
  rw [Fin.init_snoc, Fin.init_snoc, Fin.snoc_last, Fin.snoc_last]

lemma GraftOK.snoc {k : ℕ} {S : RootedTree A} {U : Fin k → RootedTree A} {f : Fin k → A}
    (h : GraftOK S U f) {W : RootedTree A} {v : A} (hv : v ∈ S.S)
    (hW : Disjoint (graftF S k U f).S W.S) :
    GraftOK S (Fin.snoc (α := fun _ => RootedTree A) U W) (Fin.snoc (α := fun _ => A) f v) := by
  have hiW : ∀ i, Disjoint (U i).S W.S := fun i =>
    Finset.disjoint_of_subset_left (fun a ha => by
      rw [graftF_S h]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ha⟩)) hW
  have hSW : Disjoint S.S W.S := Finset.disjoint_of_subset_left (fun a ha => by
      rw [graftF_S h]
      exact Finset.mem_union_left _ ha) hW
  refine ⟨fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact hv
    | cast i => rw [Fin.snoc_castSucc]; exact h.mem i
  · induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact hSW
    | cast i => rw [Fin.snoc_castSucc]; exact h.disjS i
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j => rw [Fin.snoc_last, Fin.snoc_castSucc]; exact (hiW j).symm
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last, Fin.snoc_castSucc]; exact hiW i
      | cast j =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact h.disj _ _ fun e => hij (congrArg _ e)

/-- **Grafting inside one of the grafted trees.** -/
theorem graft_graftF_of_mem {k : ℕ} {S : RootedTree A} {U : Fin k → RootedTree A}
    {f : Fin k → A} {v : A} {W : RootedTree A} (h : GraftOK S U f) (j : Fin k)
    (hv : v ∈ (U j).S) (hW : Disjoint (graftF S k U f).S W.S) :
    GraftOK S (Function.update U j (graft (U j) W v)) f ∧
      graft (graftF S k U f) W v = graftF S k (Function.update U j (graft (U j) W v)) f := by
  have hiW : ∀ i, Disjoint (U i).S W.S := fun i =>
    Finset.disjoint_of_subset_left (fun a ha => by
      rw [graftF_S h]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ha⟩)) hW
  have hSW : Disjoint S.S W.S := Finset.disjoint_of_subset_left (fun a ha => by
      rw [graftF_S h]
      exact Finset.mem_union_left _ ha) hW
  have hvG : v ∈ (graftF S k U f).S := by
    rw [graftF_S h]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hv⟩)
  have hupd : ∀ i, (Function.update U j (graft (U j) W v) i).S
      = if i = j then (U j).S ∪ W.S else (U i).S := fun i => by
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, if_pos rfl, graft_S (hiW i) hv]
    · rw [Function.update_of_ne hij, if_neg hij]
  have hOK : GraftOK S (Function.update U j (graft (U j) W v)) f := by
    refine ⟨h.mem, fun i => ?_, fun i i' hii' => ?_⟩
    · rw [hupd]
      split_ifs
      · exact Finset.disjoint_union_right.2 ⟨h.disjS j, hSW⟩
      · exact h.disjS i
    · rw [hupd, hupd]
      split_ifs with h1 h2 h2
      · exact absurd (h1.trans h2.symm) hii'
      · subst h1
        exact Finset.disjoint_union_left.2 ⟨h.disj _ _ hii', (hiW i').symm⟩
      · subst h2
        exact Finset.disjoint_union_right.2 ⟨h.disj _ _ hii', hiW i⟩
      · exact h.disj _ _ hii'
  refine ⟨hOK, eq_graftF_of hOK _ ?_ ?_ ?_ ?_⟩
  · rw [graft_S hW hvG, graftF_S h]
    ext a
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, hupd]
    constructor
    · rintro ((h1 | ⟨i, hi⟩) | h1)
      · exact Or.inl h1
      · refine Or.inr ⟨i, ?_⟩
        split_ifs with hij
        · exact Finset.mem_union_left _ (hij ▸ hi)
        · exact hi
      · exact Or.inr ⟨j, by rw [if_pos rfl]; exact Finset.mem_union_right _ h1⟩
    · rintro (h1 | ⟨i, hi⟩)
      · exact Or.inl (Or.inl h1)
      · split_ifs at hi with hij
        · rcases Finset.mem_union.1 hi with h2 | h2
          · exact Or.inl (Or.inr ⟨j, h2⟩)
          · exact Or.inr h2
        · exact Or.inl (Or.inr ⟨i, hi⟩)
  · rw [graft_root hW hvG, graftF_root h]
  · intro i a ha
    rw [graft_par hW hvG, graftPar]
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self] at ha ⊢
      rw [graft_S (hiW i) hv] at ha
      rw [graft_root (hiW i) hv, graft_par (hiW i) hv, graftPar]
      by_cases hWr : a = W.root
      · have hne : a ≠ (U i).root := fun e =>
          Finset.disjoint_left.1 (hiW i) (e ▸ (U i).root_mem) (hWr ▸ W.root_mem)
        rw [if_pos hWr, if_neg hne, if_pos hWr]
      · by_cases haW : a ∈ W.S
        · have hne : a ≠ (U i).root := fun e =>
            Finset.disjoint_left.1 (hiW i) (e ▸ (U i).root_mem) haW
          rw [if_neg hWr, if_pos haW, if_neg hne, if_neg hWr, if_pos haW]
        · have haU : a ∈ (U i).S := (Finset.mem_union.1 ha).resolve_right haW
          rw [if_neg hWr, if_neg haW, graftF_par_of_mem h i haU]
          by_cases hr : a = (U i).root
          · rw [if_pos hr, if_pos hr]
          · rw [if_neg hr, if_neg hr, if_neg hWr, if_neg haW]
    · rw [Function.update_of_ne hij] at ha ⊢
      have haW : a ∉ W.S := Finset.disjoint_left.1 (hiW i) ha
      have hWr : a ≠ W.root := fun e => haW (e ▸ W.root_mem)
      rw [if_neg hWr, if_neg haW, graftF_par_of_mem h i ha]
  · intro a ha
    have haW : a ∉ W.S := fun h' => by
      have := ha j
      rw [hupd, if_pos rfl] at this
      exact this (Finset.mem_union_right _ h')
    have hWr : a ≠ W.root := fun e => haW (e ▸ W.root_mem)
    have ha' : ∀ i, a ∉ (U i).S := fun i h' => by
      have := ha i
      rw [hupd] at this
      split_ifs at this with hij
      · exact this (Finset.mem_union_left _ (hij ▸ h'))
      · exact this h'
    rw [graft_par hW hvG, graftPar, if_neg hWr, if_neg haW, graftF_par_of_not_mem h ha']

end RootedTree

/-! ## Relabelling trees -/

namespace RootedTree

section map

variable {A B : Type*}

open Classical in
/-- A function on `A` read along a map `g : A → B`: `f a` at `g a`, `d b` off the image. -/
noncomputable def lift {α : Type*} (g : A → B) (f : A → α) (d : B → α) (b : B) : α :=
  if h : ∃ a, g a = b then f h.choose else d b

lemma lift_apply {α : Type*} {g : A → B} (hg : Function.Injective g) (f : A → α) (d : B → α)
    (a : A) : lift g f d (g a) = f a := by
  have h : ∃ a', g a' = g a := ⟨_, rfl⟩
  unfold lift
  rw [dif_pos h, hg h.choose_spec]

lemma lift_of_not {α : Type*} {g : A → B} (f : A → α) (d : B → α) {b : B}
    (h : ¬ ∃ a, g a = b) : lift g f d b = d b := by
  unfold lift
  rw [dif_neg h]

/-- **Relabelling a tree along an injective map of the labels.** -/
noncomputable def map (g : A → B) (hg : Function.Injective g) (T : RootedTree A) :
    RootedTree B where
  S := T.S.map ⟨g, hg⟩
  par := lift g (g ∘ T.par) id
  root := g T.root
  root_mem := Finset.mem_map_of_mem _ T.root_mem
  par_root := by rw [lift_apply hg, Function.comp_apply, T.par_root]
  par_not_mem := by
    intro b hb
    by_cases h : ∃ a, g a = b
    · obtain ⟨a, rfl⟩ := h
      rw [lift_apply hg, Function.comp_apply,
        T.par_not_mem _ fun h' => hb (Finset.mem_map_of_mem ⟨g, hg⟩ h')]
    · exact lift_of_not _ _ h
  par_mem := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hb
    show lift g (g ∘ T.par) id (g a) ∈ _
    rw [lift_apply hg]
    exact Finset.mem_map_of_mem ⟨g, hg⟩ (T.par_mem a ha)
  acyc := by
    obtain ⟨d, hd⟩ := T.acyc
    refine ⟨lift g d fun _ => 0, fun b hb hr => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hb
    show lift g d _ (lift g (g ∘ T.par) id (g a)) < lift g d _ (g a)
    rw [lift_apply hg, Function.comp_apply, lift_apply hg, lift_apply hg]
    exact hd a ha fun e => hr (by rw [e]; rfl)

variable {g : A → B} {hg : Function.Injective g}

lemma map_S (T : RootedTree A) : (map g hg T).S = T.S.map ⟨g, hg⟩ := rfl

lemma map_root (T : RootedTree A) : (map g hg T).root = g T.root := rfl

lemma map_par_apply (T : RootedTree A) (a : A) : (map g hg T).par (g a) = g (T.par a) :=
  lift_apply hg _ _ a

lemma map_par_of_not (T : RootedTree A) {b : B} (h : ¬ ∃ a, g a = b) : (map g hg T).par b = b :=
  lift_of_not _ _ h

lemma mem_map_S {T : RootedTree A} {a : A} : g a ∈ (map g hg T).S ↔ a ∈ T.S := by
  rw [map_S, Finset.mem_map]
  exact ⟨fun ⟨a', ha', e⟩ => hg e ▸ ha', fun h => ⟨a, h, rfl⟩⟩

lemma map_vtx (a : A) : map g hg (vtx a) = vtx (g a) := by
  ext b
  · simp [map_S]
  · by_cases h : ∃ a', g a' = b
    · obtain ⟨a', rfl⟩ := h
      rw [map_par_apply]
      rfl
    · rw [map_par_of_not _ h]
      rfl
  · rfl

/-- **Relabelling along an injective map is injective.** -/
lemma map_injective : Function.Injective (map g hg) := by
  intro T U h
  ext a
  · have h1 := congrArg RootedTree.S h
    rw [map_S, map_S] at h1
    rw [Finset.map_inj.1 h1]
  · have h1 := congrArg (fun V : RootedTree B => V.par (g a)) h
    simp only [map_par_apply] at h1
    exact hg h1
  · exact hg (congrArg RootedTree.root h)

variable [DecidableEq A] [DecidableEq B]

/-- **Relabelling commutes with grafting.** -/
lemma map_graft {T U : RootedTree A} {v : A} (h : Disjoint T.S U.S) (hv : v ∈ T.S) :
    map g hg (graft T U v) = graft (map g hg T) (map g hg U) (g v) := by
  have h' : Disjoint (map g hg T).S (map g hg U).S := by
    rw [map_S, map_S]
    exact (Finset.disjoint_map _).2 h
  have hv' : g v ∈ (map g hg T).S := mem_map_S.2 hv
  ext b
  · rw [graft_S h' hv', map_S, map_S, map_S, graft_S h hv, Finset.map_union]
  · rw [graft_par h' hv', graftPar]
    by_cases hb : ∃ a, g a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [map_par_apply, graft_par h hv, graftPar, map_root]
      simp only [mem_map_S, hg.eq_iff]
      split_ifs <;> first | rfl | rw [map_par_apply]
    · have hS : b ∉ (map g hg U).S := fun hb' => by
        obtain ⟨a, _, e⟩ := Finset.mem_map.1 hb'
        exact hb ⟨a, e⟩
      have hr : b ≠ (map g hg U).root := fun e => hb ⟨U.root, e.symm⟩
      rw [if_neg hr, if_neg hS, map_par_of_not _ hb, map_par_of_not _ hb]
  · rw [graft_root h' hv', map_root, map_root, graft_root h hv]

omit [DecidableEq A] [DecidableEq B] in
/-- Relabelling preserves the conditions for joining. -/
lemma JoinOK.map {r : A} {k : ℕ} {U : Fin k → RootedTree A} (h : JoinOK r U) :
    JoinOK (g r) (fun i => RootedTree.map g hg (U i)) :=
  ⟨fun i h' => h.not_mem i (mem_map_S.1 h'), fun i j hij => by
    rw [map_S, map_S]
    exact (Finset.disjoint_map _).2 (h.disj i j hij)⟩

/-- **Relabelling commutes with joining.** -/
theorem map_joinF (r : A) : ∀ (k : ℕ) (U : Fin k → RootedTree A), JoinOK r U →
    map g hg (joinF r k U) = joinF (g r) k (fun i => map g hg (U i))
  | 0, _, _ => map_vtx r
  | k + 1, U, h => by
    show map g hg (graft (joinF r k (Fin.init U)) (U (Fin.last k)) r)
      = graft (joinF (g r) k (Fin.init fun i => map g hg (U i))) (map g hg (U (Fin.last k))) (g r)
    rw [map_graft (disjoint_joinF_last h) (root_mem_joinF_S h.init),
      map_joinF r k _ h.init]
    rfl

end map

end RootedTree

/-! ## Inserting a tree at a vertex -/

namespace RootedTree

variable {A : Type*} [DecidableEq A]

/-- **The children of a vertex.** -/
def childrenOf (T : RootedTree A) (i : A) : Finset A := T.S.filter fun c => c ≠ i ∧ T.par c = i

lemma mem_childrenOf {T : RootedTree A} {i c : A} :
    c ∈ childrenOf T i ↔ c ∈ T.S ∧ c ≠ i ∧ T.par c = i := by
  unfold childrenOf
  rw [Finset.mem_filter]

lemma childrenOf_root (T : RootedTree A) : childrenOf T T.root = children T := rfl

omit [DecidableEq A] in
/-- The depth decreases strictly from a descendant other than the vertex. -/
lemma depth_lt_of_mem_desc {T : RootedTree A} {d : A → ℕ}
    (hd : ∀ a ∈ T.S, a ≠ T.root → d (T.par a) < d a) {i a : A} (ha : a ∈ desc T i)
    (hai : a ≠ i) : d i < d a := by
  obtain ⟨haS, n, hn⟩ := mem_desc.1 ha
  induction n generalizing a with
  | zero => exact absurd hn hai
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hn
    have har : a ≠ T.root := fun h' => by
      rw [h', T.par_root, iterate_root] at hn
      exact hai (h'.trans hn)
    have h1 := hd a haS har
    by_cases hp : T.par a = i
    · rw [← hp]
      exact h1
    · exact (ih (mem_desc.2 ⟨T.par_mem a haS, n, hn⟩) hp (T.par_mem a haS) hn).trans h1

omit [DecidableEq A] in
/-- The parent of a vertex other than the root does not descend from it. -/
lemma par_not_mem_desc {T : RootedTree A} {i : A} (hi : i ∈ T.S) (hr : i ≠ T.root) :
    T.par i ∉ desc T i := fun h => by
  obtain ⟨d, hd⟩ := T.acyc
  have hne : T.par i ≠ i := par_ne_self hi hr
  exact absurd (depth_lt_of_mem_desc hd h hne) (not_lt.2 (hd i hi hr).le)

omit [DecidableEq A] in
lemma mem_desc_of_par {T : RootedTree A} {i a : A} (ha : a ∈ T.S) (h : T.par a ∈ desc T i) :
    a ∈ desc T i := by
  obtain ⟨_, n, hn⟩ := mem_desc.1 h
  exact mem_desc.2 ⟨ha, n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

/-- The raw parent function of the insertion of `S` at the vertex `i` of `T`, the children of
`i` attached by `g`. -/
def insPar (T S : RootedTree A) (i : A) (g : A → A) (a : A) : A :=
  if a ∈ S.S then (if a = S.root then (if i = T.root then a else T.par i) else S.par a)
  else if a ∈ childrenOf T i then g a
  else if a = i then a
  else T.par a

/-- The conditions for inserting `S` at the vertex `i` of `T`: `i` is a vertex of `T`, the vertex
sets are disjoint, and the children of `i` are attached to vertices of `S`. -/
structure InsOK (T S : RootedTree A) (i : A) (g : A → A) : Prop where
  mem : i ∈ T.S
  disj : Disjoint T.S S.S
  attach : ∀ c ∈ childrenOf T i, g c ∈ S.S

open Classical in
/-- **Inserting the tree `S` at the vertex `i` of `T`**: `S` replaces `i`, its root takes the
place of `i` below the parent of `i`, and each child `c` of `i` is attached to the vertex `g c`
of `S`; `T` when the conditions fail. -/
noncomputable def ins (T S : RootedTree A) (i : A) (g : A → A) : RootedTree A :=
  if h : InsOK T S i g then
    { S := T.S.erase i ∪ S.S
      par := insPar T S i g
      root := if i = T.root then S.root else T.root
      root_mem := by
        split_ifs with hi
        · exact Finset.mem_union_right _ S.root_mem
        · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨fun e => hi e.symm, T.root_mem⟩)
      par_root := by
        split_ifs with hi
        · unfold insPar
          rw [if_pos S.root_mem, if_pos rfl, if_pos hi]
        · have h1 : T.root ∉ S.S := Finset.disjoint_left.1 h.disj T.root_mem
          have h2 : T.root ∉ childrenOf T i := fun hc =>
            hi (((mem_childrenOf.1 hc).2.2).symm.trans T.par_root)
          unfold insPar
          rw [if_neg h1, if_neg h2, if_neg fun e => hi e.symm, T.par_root]
      par_not_mem := by
        intro a ha
        rw [Finset.mem_union, not_or, Finset.mem_erase, not_and_or, not_not] at ha
        have hc : a ∉ childrenOf T i := fun hc => by
          obtain ⟨h1, h2, _⟩ := mem_childrenOf.1 hc
          rcases ha.1 with h3 | h3
          · exact h2 h3
          · exact h3 h1
        unfold insPar
        rw [if_neg ha.2, if_neg hc]
        split_ifs with hai
        · rfl
        · rcases ha.1 with h3 | h3
          · exact absurd h3 hai
          · exact T.par_not_mem a h3
      par_mem := by
        intro a ha
        unfold insPar
        split_ifs with h1 h2 h3 h4 h5
        · exact Finset.mem_union_right _ h1
        · exact Finset.mem_union_left _ (Finset.mem_erase.2
            ⟨par_ne_self h.mem fun e => h3 e, T.par_mem i h.mem⟩)
        · exact Finset.mem_union_right _ (S.par_mem a h1)
        · exact Finset.mem_union_right _ (h.attach a h4)
        · exfalso
          rcases Finset.mem_union.1 ha with h6 | h6
          · exact (Finset.mem_erase.1 h6).1 h5
          · exact h1 h6
        · have haT : a ∈ T.S := by
            rcases Finset.mem_union.1 ha with h6 | h6
            · exact (Finset.mem_erase.1 h6).2
            · exact absurd h6 h1
          refine Finset.mem_union_left _ (Finset.mem_erase.2 ⟨fun e => h4 ?_, T.par_mem a haT⟩)
          exact mem_childrenOf.2 ⟨haT, h5, e⟩
      acyc := by
        obtain ⟨dT, hdT⟩ := T.acyc
        obtain ⟨dS, hdS⟩ := S.acyc
        refine ⟨fun a => if a ∈ S.S then dT i + dS a
          else if a ∈ desc T i then dT a + (S.S.sup dS + 1) else dT a, fun a ha har => ?_⟩
        beta_reduce
        unfold insPar
        by_cases h1 : a ∈ S.S
        · rw [if_pos h1]
          by_cases h2 : a = S.root
          · have h3 : ¬ i = T.root := fun h3 => har (by rw [if_pos h3, h2])
            rw [if_pos h2, if_neg h3, if_pos h1]
            have h4 : T.par i ∉ S.S := Finset.disjoint_left.1 h.disj (T.par_mem i h.mem)
            have h5 : T.par i ∉ desc T i := par_not_mem_desc h.mem fun e => h3 e
            simp only [h4, if_false, h5]
            have := hdT i h.mem fun e => h3 e
            omega
          · have h4 : S.par a ∈ S.S := S.par_mem a h1
            rw [if_neg h2]
            simp only [h4, h1, if_true]
            have := hdS a h1 h2
            omega
        · have haT : a ∈ T.S ∧ a ≠ i := by
            rcases Finset.mem_union.1 ha with h6 | h6
            · exact ⟨(Finset.mem_erase.1 h6).2, (Finset.mem_erase.1 h6).1⟩
            · exact absurd h6 h1
          rw [if_neg h1, if_neg h1]
          by_cases hc : a ∈ childrenOf T i
          · obtain ⟨-, -, hp⟩ := mem_childrenOf.1 hc
            have hgS : g a ∈ S.S := h.attach a hc
            have had : a ∈ desc T i := mem_desc.2 ⟨haT.1, 1, hp⟩
            have har' : a ≠ T.root := fun e => haT.2 (by rw [← hp, e, T.par_root])
            rw [if_pos hc, if_pos had]
            simp only [hgS, if_true]
            have h7 := hdT a haT.1 har'
            rw [hp] at h7
            have h8 : dS (g a) ≤ S.S.sup dS := Finset.le_sup hgS
            omega
          · rw [if_neg hc, if_neg haT.2]
            have har' : a ≠ T.root := fun e => har (by
              have hi : ¬ i = T.root := fun e' => haT.2 (e.trans e'.symm)
              rw [if_neg hi, e])
            have hpS : T.par a ∉ S.S := Finset.disjoint_left.1 h.disj (T.par_mem a haT.1)
            have h7 := hdT a haT.1 har'
            simp only [hpS, if_false]
            by_cases had : a ∈ desc T i
            · have hpd : T.par a ∈ desc T i := par_mem_desc had haT.2
              rw [if_pos hpd, if_pos had]
              omega
            · have hpd : T.par a ∉ desc T i := fun h' => had (mem_desc_of_par haT.1 h')
              rw [if_neg hpd, if_neg had]
              exact h7 }
  else T

end RootedTree

end Operad
