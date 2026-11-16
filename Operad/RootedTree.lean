/-
# Labelled rooted trees

A **rooted tree with vertices labelled by a finite subset `S` of `A`** (`RootedTree`) is its
vertex set, its root and its parent function, the identity outside `S` and at the root, mapping
`S` into itself, with a depth function decreasing along it away from the root. The tree with one
vertex is `RootedTree.vtx`.

* **Grafting.** `RootedTree.graft T U v` attaches the root of `U` to the vertex `v` of `T`, when
  their vertex sets are disjoint. Grafting at two vertices of `T` commutes
  (`RootedTree.graft_graft_comm`), and grafting into a grafted tree at a vertex of the grafted
  tree is grafting into it (`RootedTree.graft_graft_assoc`).
* **Descendants and subtrees.** Every vertex leads to the root (`RootedTree.exists_iterate_eq_root`)
  and descends from exactly one child of the root (`RootedTree.exists_child`,
  `RootedTree.child_unique`); `RootedTree.subtree` is the tree of the descendants of a vertex.
* **Joins.** `RootedTree.joinF r k U` joins the trees `U i` at a new root `r`, by grafting them
  one after another. Every tree is the join of its subtrees at the children of its root
  (`RootedTree.eq_joinF`); the children and subtrees of a join are the roots of the joined trees
  and the joined trees (`RootedTree.mem_children_joinF`, `RootedTree.subtree_joinF`); grafting at
  the root of a join, or inside one of the joined trees, is a join (`RootedTree.graft_joinF_root`,
  `RootedTree.graft_joinF_of_mem`).
-/
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Fin

namespace Operad

/-- **A rooted tree with vertices labelled by a finite subset of `A`**: the vertex set `S`, the
root, and the parent function `par`, the identity outside `S` and at the root, mapping `S` into
itself, with a depth function decreasing along `par` away from the root. -/
@[ext]
structure RootedTree (A : Type*) where
  /-- The vertex set. -/
  S : Finset A
  /-- The parent function. -/
  par : A → A
  /-- The root. -/
  root : A
  root_mem : root ∈ S
  par_root : par root = root
  par_not_mem : ∀ a, a ∉ S → par a = a
  par_mem : ∀ a ∈ S, par a ∈ S
  acyc : ∃ d : A → ℕ, ∀ a ∈ S, a ≠ root → d (par a) < d a

namespace RootedTree

variable {A : Type*}

/-- **The tree with one vertex.** -/
def vtx (a : A) : RootedTree A where
  S := {a}
  par := id
  root := a
  root_mem := Finset.mem_singleton_self a
  par_root := rfl
  par_not_mem _ _ := rfl
  par_mem _ h := h
  acyc := ⟨fun _ => 0, fun _ h h' => absurd (Finset.mem_singleton.1 h) h'⟩

@[simp] lemma vtx_S (a : A) : (vtx a).S = {a} := rfl
@[simp] lemma vtx_par (a : A) : (vtx a).par = id := rfl
@[simp] lemma vtx_root (a : A) : (vtx a).root = a := rfl

variable [DecidableEq A]

/-! ## Grafting -/

/-- The raw parent function of a graft of `U` at the vertex `v`. -/
def graftPar (T U : RootedTree A) (v : A) (a : A) : A :=
  if a = U.root then v else if a ∈ U.S then U.par a else T.par a

/-- **Grafting `U` at the vertex `v` of `T`**, when their vertex sets are disjoint and `v` is a
vertex of `T`; `T` otherwise. -/
def graft (T U : RootedTree A) (v : A) : RootedTree A :=
  if h : Disjoint T.S U.S ∧ v ∈ T.S then
    { S := T.S ∪ U.S
      par := graftPar T U v
      root := T.root
      root_mem := Finset.mem_union_left _ T.root_mem
      par_root := by
        have h1 : T.root ∉ U.S := Finset.disjoint_left.1 h.1 T.root_mem
        have h2 : T.root ≠ U.root := fun e => h1 (e ▸ U.root_mem)
        simp only [graftPar, if_neg h2, if_neg h1, T.par_root]
      par_not_mem := by
        intro a ha
        rw [Finset.mem_union, not_or] at ha
        have h2 : a ≠ U.root := fun e => ha.2 (e ▸ U.root_mem)
        simp only [graftPar, if_neg h2, if_neg ha.2, T.par_not_mem a ha.1]
      par_mem := by
        intro a ha
        unfold graftPar
        split_ifs with h1 h2
        · exact Finset.mem_union_left _ h.2
        · exact Finset.mem_union_right _ (U.par_mem a h2)
        · rcases Finset.mem_union.1 ha with ha | ha
          · exact Finset.mem_union_left _ (T.par_mem a ha)
          · exact absurd ha h2
      acyc := by
        obtain ⟨dT, hT⟩ := T.acyc
        obtain ⟨dU, hU⟩ := U.acyc
        refine ⟨fun a => if a ∈ U.S then dT v + 1 + dU a else dT a, fun a ha har => ?_⟩
        have hv : v ∉ U.S := Finset.disjoint_left.1 h.1 h.2
        unfold graftPar
        by_cases h1 : a = U.root
        · subst h1
          simp only [↓reduceIte, if_neg hv, if_pos U.root_mem]
          omega
        · by_cases h2 : a ∈ U.S
          · simp only [if_neg h1, if_pos h2, if_pos (U.par_mem a h2)]
            have := hU a h2 h1
            omega
          · have haT : a ∈ T.S := (Finset.mem_union.1 ha).resolve_right h2
            have h3 : T.par a ∉ U.S := Finset.disjoint_left.1 h.1 (T.par_mem a haT)
            simp only [if_neg h1, if_neg h2, if_neg h3]
            exact hT a haT har }
  else T

variable {T U : RootedTree A} {v : A}

lemma graft_of (h : Disjoint T.S U.S) (hv : v ∈ T.S) :
    (graft T U v).S = T.S ∪ U.S ∧ (graft T U v).par = graftPar T U v
      ∧ (graft T U v).root = T.root := by
  unfold graft
  rw [dif_pos ⟨h, hv⟩]
  exact ⟨rfl, rfl, rfl⟩

lemma graft_S (h : Disjoint T.S U.S) (hv : v ∈ T.S) : (graft T U v).S = T.S ∪ U.S :=
  (graft_of h hv).1

lemma graft_par (h : Disjoint T.S U.S) (hv : v ∈ T.S) : (graft T U v).par = graftPar T U v :=
  (graft_of h hv).2.1

lemma graft_root (h : Disjoint T.S U.S) (hv : v ∈ T.S) : (graft T U v).root = T.root :=
  (graft_of h hv).2.2

/-- **Grafting at two vertices of `T` commutes.** -/
theorem graft_graft_comm {W : RootedTree A} {w : A} (hTU : Disjoint T.S U.S)
    (hTW : Disjoint T.S W.S) (hUW : Disjoint U.S W.S) (hv : v ∈ T.S) (hw : w ∈ T.S) :
    graft (graft T U v) W w = graft (graft T W w) U v := by
  have h1 : Disjoint (graft T U v).S W.S := by
    rw [graft_S hTU hv]
    exact Finset.disjoint_union_left.2 ⟨hTW, hUW⟩
  have h2 : Disjoint (graft T W w).S U.S := by
    rw [graft_S hTW hw]
    exact Finset.disjoint_union_left.2 ⟨hTU, hUW.symm⟩
  have hw' : w ∈ (graft T U v).S := by rw [graft_S hTU hv]; exact Finset.mem_union_left _ hw
  have hv' : v ∈ (graft T W w).S := by rw [graft_S hTW hw]; exact Finset.mem_union_left _ hv
  ext a
  · rw [graft_S h1 hw', graft_S hTU hv, graft_S h2 hv', graft_S hTW hw]
    simp only [Finset.mem_union]
    tauto
  · rw [graft_par h1 hw', graft_par h2 hv', graftPar, graftPar, graft_par hTU hv,
      graft_par hTW hw, graftPar, graftPar]
    have hWr : W.root ∉ U.S := Finset.disjoint_right.1 hUW W.root_mem
    have hUr : U.root ∉ W.S := Finset.disjoint_left.1 hUW U.root_mem
    by_cases ha : a = W.root
    · subst ha
      have hne : W.root ≠ U.root := fun e => hWr (e ▸ U.root_mem)
      simp [hne, hWr]
    · by_cases hb : a = U.root
      · subst hb
        simp [ha, hUr]
      · by_cases hc : a ∈ W.S
        · have hcU : a ∉ U.S := Finset.disjoint_right.1 hUW hc
          simp [ha, hb, hc, hcU]
        · simp [ha, hb, hc]
  · rw [graft_root h1 hw', graft_root hTU hv, graft_root h2 hv', graft_root hTW hw]

/-- **Grafting into a grafted tree at a vertex of the grafted tree** is grafting into it. -/
theorem graft_graft_assoc {W : RootedTree A} {w : A} (hTU : Disjoint T.S U.S)
    (hTW : Disjoint T.S W.S) (hUW : Disjoint U.S W.S) (hv : v ∈ T.S) (hw : w ∈ U.S) :
    graft (graft T U v) W w = graft T (graft U W w) v := by
  have h1 : Disjoint (graft T U v).S W.S := by
    rw [graft_S hTU hv]
    exact Finset.disjoint_union_left.2 ⟨hTW, hUW⟩
  have h2 : Disjoint T.S (graft U W w).S := by
    rw [graft_S hUW hw]
    exact Finset.disjoint_union_right.2 ⟨hTU, hTW⟩
  have hw' : w ∈ (graft T U v).S := by rw [graft_S hTU hv]; exact Finset.mem_union_right _ hw
  ext a
  · rw [graft_S h1 hw', graft_S hTU hv, graft_S h2 hv, graft_S hUW hw]
    simp only [Finset.mem_union]
    tauto
  · rw [graft_par h1 hw', graft_par h2 hv, graftPar, graftPar, graft_par hTU hv,
      graft_par hUW hw, graft_S hUW hw, graft_root hUW hw, graftPar, graftPar]
    have hWr : W.root ∉ U.S := Finset.disjoint_right.1 hUW W.root_mem
    have hUr : U.root ∉ W.S := Finset.disjoint_left.1 hUW U.root_mem
    by_cases ha : a = W.root
    · subst ha
      have hne : W.root ≠ U.root := fun e => hWr (e ▸ U.root_mem)
      simp [hne, W.root_mem]
    · by_cases hb : a = U.root
      · subst hb
        simp [ha, hUr]
      · by_cases hc : a ∈ W.S
        · simp [ha, hb, hc]
        · simp [ha, hb, hc]
  · rw [graft_root h1 hw', graft_root hTU hv, graft_root h2 hv]

/-! ## Paths to the root, descendants and children -/

omit [DecidableEq A] in
lemma par_ne_self {a : A} (ha : a ∈ T.S) (hr : a ≠ T.root) : T.par a ≠ a := by
  obtain ⟨d, hd⟩ := T.acyc
  intro h
  have h1 := hd a ha hr
  rw [h] at h1
  exact lt_irrefl _ h1

omit [DecidableEq A] in
lemma iterate_mem {a : A} (ha : a ∈ T.S) (n : ℕ) : T.par^[n] a ∈ T.S := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (T.par_mem a ha)

omit [DecidableEq A] in
lemma iterate_root (n : ℕ) : T.par^[n] T.root = T.root :=
  Function.iterate_fixed T.par_root n

/-- **Every vertex leads to the root.** -/
theorem exists_iterate_eq_root {a : A} (ha : a ∈ T.S) : ∃ n, T.par^[n] a = T.root := by
  obtain ⟨d, hd⟩ := T.acyc
  induction h : d a using Nat.strong_induction_on generalizing a with
  | _ k ih =>
    by_cases hr : a = T.root
    · exact ⟨0, hr⟩
    · obtain ⟨n, hn⟩ := ih (d (T.par a)) (h ▸ hd a ha hr) (T.par_mem a ha) rfl
      exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

open Classical in
/-- **The descendants of `c`**: the vertices from which the parent function leads to `c`. -/
noncomputable def desc (T : RootedTree A) (c : A) : Finset A :=
  T.S.filter fun a => ∃ n, T.par^[n] a = c

omit [DecidableEq A] in
lemma mem_desc {c a : A} : a ∈ desc T c ↔ a ∈ T.S ∧ ∃ n, T.par^[n] a = c := by
  classical
  unfold desc
  rw [Finset.mem_filter]

omit [DecidableEq A] in
lemma desc_subset (c : A) : desc T c ⊆ T.S := fun _ h => (mem_desc.1 h).1

omit [DecidableEq A] in
lemma self_mem_desc {c : A} (hc : c ∈ T.S) : c ∈ desc T c := mem_desc.2 ⟨hc, 0, rfl⟩

omit [DecidableEq A] in
lemma root_not_mem_desc {c : A} (hc : c ≠ T.root) : T.root ∉ desc T c := fun h => by
  obtain ⟨_, n, hn⟩ := mem_desc.1 h
  rw [iterate_root] at hn
  exact hc hn.symm

omit [DecidableEq A] in
lemma par_mem_desc {c a : A} (ha : a ∈ desc T c) (hac : a ≠ c) : T.par a ∈ desc T c := by
  obtain ⟨haS, n, hn⟩ := mem_desc.1 ha
  cases n with
  | zero => exact absurd hn hac
  | succ n =>
    rw [Function.iterate_succ_apply] at hn
    exact mem_desc.2 ⟨T.par_mem a haS, n, hn⟩

/-- **The children of the root.** -/
def children (T : RootedTree A) : Finset A := T.S.filter fun c => c ≠ T.root ∧ T.par c = T.root

lemma mem_children {c : A} : c ∈ children T ↔ c ∈ T.S ∧ c ≠ T.root ∧ T.par c = T.root := by
  unfold children
  rw [Finset.mem_filter]

/-- **Every vertex other than the root descends from a child of the root.** -/
theorem exists_child {a : A} (ha : a ∈ T.S) (hr : a ≠ T.root) :
    ∃ c ∈ children T, a ∈ desc T c := by
  obtain ⟨d, hd⟩ := T.acyc
  induction h : d a using Nat.strong_induction_on generalizing a with
  | _ k ih =>
    by_cases hp : T.par a = T.root
    · exact ⟨a, mem_children.2 ⟨ha, hr, hp⟩, self_mem_desc ha⟩
    · obtain ⟨c, hc, hac⟩ := ih (d (T.par a)) (h ▸ hd a ha hr) (T.par_mem a ha) hp rfl
      obtain ⟨_, n, hn⟩ := mem_desc.1 hac
      exact ⟨c, hc, mem_desc.2 ⟨ha, n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩⟩

lemma eq_of_iterate {c c' a : A} (hc : c ∈ children T) (hc' : c' ∈ children T) {n m : ℕ}
    (hnm : n ≤ m) (hn : T.par^[n] a = c) (hm : T.par^[m] a = c') : c = c' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [add_comm, Function.iterate_add_apply, hn] at hm
  cases k with
  | zero => exact hm
  | succ k =>
    rw [Function.iterate_succ_apply, (mem_children.1 hc).2.2, iterate_root] at hm
    exact absurd hm.symm (mem_children.1 hc').2.1

/-- **A vertex descends from one child of the root only.** -/
theorem child_unique {c c' a : A} (hc : c ∈ children T) (hc' : c' ∈ children T)
    (ha : a ∈ desc T c) (ha' : a ∈ desc T c') : c = c' := by
  obtain ⟨_, n, hn⟩ := mem_desc.1 ha
  obtain ⟨_, m, hm⟩ := mem_desc.1 ha'
  rcases le_total n m with h | h
  · exact eq_of_iterate hc hc' h hn hm
  · exact (eq_of_iterate hc' hc h hm hn).symm

lemma disjoint_desc {c c' : A} (hc : c ∈ children T) (hc' : c' ∈ children T) (h : c ≠ c') :
    Disjoint (desc T c) (desc T c') :=
  Finset.disjoint_left.2 fun _ ha ha' => h (child_unique hc hc' ha ha')

/-! ## Subtrees -/

/-- **The subtree of the descendants of `c`.** -/
noncomputable def subtree (T : RootedTree A) (c : A) : RootedTree A :=
  if hc : c ∈ T.S then
    { S := desc T c
      par := fun a => if a ∈ desc T c ∧ a ≠ c then T.par a else a
      root := c
      root_mem := self_mem_desc hc
      par_root := by simp
      par_not_mem := fun a ha => by simp [ha]
      par_mem := fun a ha => by
        by_cases h : a ≠ c
        · rw [if_pos ⟨ha, h⟩]
          exact par_mem_desc ha h
        · rw [if_neg fun h' => h h'.2]
          exact ha
      acyc := by
        obtain ⟨d, hd⟩ := T.acyc
        refine ⟨d, fun a ha hac => ?_⟩
        rw [if_pos ⟨ha, hac⟩]
        refine hd a (desc_subset c ha) fun har => hac ?_
        obtain ⟨_, n, hn⟩ := mem_desc.1 ha
        rw [har, iterate_root] at hn
        exact har.trans hn }
  else T

lemma subtree_of {c : A} (hc : c ∈ T.S) :
    (subtree T c).S = desc T c ∧
      (subtree T c).par = (fun a => if a ∈ desc T c ∧ a ≠ c then T.par a else a) ∧
      (subtree T c).root = c := by
  unfold subtree
  rw [dif_pos hc]
  exact ⟨rfl, rfl, rfl⟩

lemma subtree_S {c : A} (hc : c ∈ T.S) : (subtree T c).S = desc T c := (subtree_of hc).1

lemma subtree_root {c : A} (hc : c ∈ T.S) : (subtree T c).root = c := (subtree_of hc).2.2

lemma subtree_par {c a : A} (hc : c ∈ T.S) :
    (subtree T c).par a = if a ∈ desc T c ∧ a ≠ c then T.par a else a := by
  rw [(subtree_of hc).2.1]

/-- The subtrees at the children of the root have fewer vertices. -/
lemma card_subtree_lt {c : A} (hc : c ∈ children T) : (subtree T c).S.card < T.S.card := by
  have hcS := (mem_children.1 hc).1
  rw [subtree_S hcS]
  exact Finset.card_lt_card ⟨desc_subset c, fun h =>
    root_not_mem_desc (mem_children.1 hc).2.1 (h T.root_mem)⟩

/-! ## Joining trees at a root -/

/-- **Joining trees at a new root `r`**: grafting them one after another at `r`. -/
def joinF (r : A) : (k : ℕ) → (Fin k → RootedTree A) → RootedTree A
  | 0, _ => vtx r
  | k + 1, U => graft (joinF r k (Fin.init U)) (U (Fin.last k)) r

/-- The conditions for joining trees at a root: their vertex sets are pairwise disjoint and do
not contain the root. -/
structure JoinOK (r : A) {k : ℕ} (U : Fin k → RootedTree A) : Prop where
  not_mem : ∀ i, r ∉ (U i).S
  disj : ∀ i j, i ≠ j → Disjoint (U i).S (U j).S

omit [DecidableEq A] in
lemma JoinOK.init {r : A} {k : ℕ} {U : Fin (k + 1) → RootedTree A} (h : JoinOK r U) :
    JoinOK r (Fin.init U) :=
  ⟨fun _ => h.not_mem _, fun _ _ hij => h.disj _ _ fun e => hij (Fin.castSucc_injective _ e)⟩

lemma joinF_S_root : ∀ {k : ℕ} {r : A} {U : Fin k → RootedTree A}, JoinOK r U →
    (joinF r k U).S = insert r (Finset.univ.biUnion fun i => (U i).S) ∧ (joinF r k U).root = r
  | 0, r, U, _ => by simp [joinF]
  | k + 1, r, U, h => by
    obtain ⟨hS, hR⟩ := joinF_S_root h.init
    have hd : Disjoint (joinF r k (Fin.init U)).S (U (Fin.last k)).S := by
      rw [hS, Finset.disjoint_insert_left, Finset.disjoint_biUnion_left]
      exact ⟨h.not_mem _, fun i _ => h.disj _ _ (Fin.castSucc_lt_last i).ne⟩
    have hr : r ∈ (joinF r k (Fin.init U)).S := by rw [hS]; exact Finset.mem_insert_self _ _
    refine ⟨?_, ?_⟩
    · show (graft (joinF r k (Fin.init U)) (U (Fin.last k)) r).S = _
      rw [graft_S hd hr, hS]
      ext a
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
        true_and, Fin.exists_fin_succ', Fin.init]
      tauto
    · show (graft (joinF r k (Fin.init U)) (U (Fin.last k)) r).root = r
      rw [graft_root hd hr, hR]

lemma joinF_S {k : ℕ} {r : A} {U : Fin k → RootedTree A} (h : JoinOK r U) :
    (joinF r k U).S = insert r (Finset.univ.biUnion fun i => (U i).S) :=
  (joinF_S_root h).1

lemma joinF_root {k : ℕ} {r : A} {U : Fin k → RootedTree A} (h : JoinOK r U) :
    (joinF r k U).root = r :=
  (joinF_S_root h).2

lemma mem_joinF_S {k : ℕ} {r : A} {U : Fin k → RootedTree A} (h : JoinOK r U) {i : Fin k} {a : A}
    (ha : a ∈ (U i).S) : a ∈ (joinF r k U).S := by
  rw [joinF_S h]
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ha⟩)

lemma root_mem_joinF_S {k : ℕ} {r : A} {U : Fin k → RootedTree A} (h : JoinOK r U) :
    r ∈ (joinF r k U).S := by
  rw [joinF_S h]
  exact Finset.mem_insert_self _ _

lemma disjoint_joinF_last {k : ℕ} {r : A} {U : Fin (k + 1) → RootedTree A} (h : JoinOK r U) :
    Disjoint (joinF r k (Fin.init U)).S (U (Fin.last k)).S := by
  rw [joinF_S h.init, Finset.disjoint_insert_left, Finset.disjoint_biUnion_left]
  exact ⟨h.not_mem _, fun i _ => h.disj _ _ (Fin.castSucc_lt_last i).ne⟩

/-- **The parent function of a joined tree, on the vertices of one of the trees.** -/
lemma joinF_par_of_mem : ∀ {k : ℕ} {r : A} {U : Fin k → RootedTree A}, JoinOK r U →
    ∀ (i : Fin k) {a : A}, a ∈ (U i).S →
      (joinF r k U).par a = if a = (U i).root then r else (U i).par a
  | 0, _, _, _, i, _, _ => i.elim0
  | k + 1, r, U, h, i, a, ha => by
    have hd := disjoint_joinF_last h
    show (graft (joinF r k (Fin.init U)) (U (Fin.last k)) r).par a = _
    rw [graft_par hd (root_mem_joinF_S h.init), graftPar]
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
      exact joinF_par_of_mem h.init i ha

/-- **The parent function of a joined tree, away from the trees.** -/
lemma joinF_par_of_not_mem : ∀ {k : ℕ} {r : A} {U : Fin k → RootedTree A}, JoinOK r U →
    ∀ {a : A}, (∀ i, a ∉ (U i).S) → (joinF r k U).par a = a
  | 0, _, _, _, _, _ => rfl
  | k + 1, r, U, h, a, ha => by
    have hd := disjoint_joinF_last h
    show (graft (joinF r k (Fin.init U)) (U (Fin.last k)) r).par a = _
    rw [graft_par hd (root_mem_joinF_S h.init), graftPar]
    have hnr : a ≠ (U (Fin.last k)).root := fun e => ha _ (e ▸ (U (Fin.last k)).root_mem)
    rw [if_neg hnr, if_neg (ha _)]
    exact joinF_par_of_not_mem h.init fun i => ha _

/-- **Every tree is the join of its subtrees at the children of the root.** -/
theorem eq_joinF (T : RootedTree A) {k : ℕ} (e : Fin k ≃ children T) :
    T = joinF T.root k (fun i => subtree T (e i)) := by
  have hcS : ∀ i, (e i).1 ∈ T.S := fun i => (mem_children.1 (e i).2).1
  have hOK : JoinOK T.root (fun i => subtree T (e i)) := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [subtree_S (hcS i)]
      exact root_not_mem_desc (mem_children.1 (e i).2).2.1
    · rw [subtree_S (hcS i), subtree_S (hcS j)]
      exact disjoint_desc (e i).2 (e j).2 fun h' => hij (e.injective (Subtype.ext h'))
  have hmem : ∀ a ∈ T.S, a ≠ T.root → ∃ i, a ∈ desc T (e i) := fun a ha hr => by
    obtain ⟨c, hc, hac⟩ := exists_child ha hr
    exact ⟨e.symm ⟨c, hc⟩, by rw [Equiv.apply_symm_apply]; exact hac⟩
  ext a
  · rw [joinF_S hOK]
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro ha
      by_cases hr : a = T.root
      · exact Or.inl hr
      · obtain ⟨i, hi⟩ := hmem a ha hr
        exact Or.inr ⟨i, by rw [subtree_S (hcS i)]; exact hi⟩
    · rintro (rfl | ⟨i, hi⟩)
      · exact T.root_mem
      · rw [subtree_S (hcS i)] at hi
        exact desc_subset _ hi
  · by_cases h : ∃ i, a ∈ desc T (e i)
    · obtain ⟨i, hi⟩ := h
      rw [joinF_par_of_mem hOK i (by rw [subtree_S (hcS i)]; exact hi), subtree_root (hcS i),
        subtree_par (hcS i)]
      by_cases hc : a = (e i).1
      · rw [if_pos hc, hc]
        exact (mem_children.1 (e i).2).2.2
      · rw [if_neg hc, if_pos ⟨hi, hc⟩]
    · simp only [not_exists] at h
      rw [joinF_par_of_not_mem hOK fun i => by rw [subtree_S (hcS i)]; exact h i]
      by_cases ha : a ∈ T.S
      · by_cases hr : a = T.root
        · rw [hr, T.par_root]
        · obtain ⟨i, hi⟩ := hmem a ha hr
          exact absurd hi (h i)
      · exact T.par_not_mem a ha
  · rw [joinF_root hOK]

/-- **Grafting at the root of a joined tree joins one more tree.** -/
lemma graft_joinF_root {k : ℕ} (r : A) (U : Fin k → RootedTree A) (W : RootedTree A) :
    graft (joinF r k U) W r = joinF r (k + 1) (Fin.snoc (α := fun _ => RootedTree A) U W) := by
  show _ = graft (joinF r k (Fin.init (Fin.snoc (α := fun _ => RootedTree A) U W)))
    (Fin.snoc (α := fun _ => RootedTree A) U W (Fin.last k)) r
  rw [Fin.init_snoc, Fin.snoc_last]

/-- **A tree is a join** when it has the vertices, the root and the parent function of one. -/
theorem eq_joinF_of {k : ℕ} {r : A} {U : Fin k → RootedTree A} (h : JoinOK r U) (T : RootedTree A)
    (hS : T.S = insert r (Finset.univ.biUnion fun i => (U i).S)) (hroot : T.root = r)
    (hpar : ∀ i a, a ∈ (U i).S → T.par a = if a = (U i).root then r else (U i).par a) :
    T = joinF r k U := by
  ext a
  · rw [hS, joinF_S h]
  · by_cases ha : ∃ i, a ∈ (U i).S
    · obtain ⟨i, hi⟩ := ha
      rw [hpar i a hi, joinF_par_of_mem h i hi]
    · simp only [not_exists] at ha
      rw [joinF_par_of_not_mem h ha]
      by_cases har : a = r
      · rw [har, ← hroot, T.par_root]
      · refine T.par_not_mem a fun haS => ?_
        rw [hS, Finset.mem_insert, Finset.mem_biUnion] at haS
        rcases haS with h1 | ⟨i, _, hi⟩
        · exact har h1
        · exact ha i hi
  · rw [hroot, joinF_root h]

/-- **Grafting inside one of the joined trees.** -/
theorem graft_joinF_of_mem {k : ℕ} {r v : A} {U : Fin k → RootedTree A} {W : RootedTree A}
    (h : JoinOK r U) (j : Fin k) (hv : v ∈ (U j).S) (hW : Disjoint (joinF r k U).S W.S) :
    JoinOK r (Function.update U j (graft (U j) W v)) ∧
      graft (joinF r k U) W v = joinF r k (Function.update U j (graft (U j) W v)) := by
  have hjW : Disjoint (U j).S W.S :=
    Finset.disjoint_of_subset_left (fun a ha => mem_joinF_S h ha) hW
  have hiW : ∀ i, Disjoint (U i).S W.S := fun i =>
    Finset.disjoint_of_subset_left (fun a ha => mem_joinF_S h ha) hW
  have hrW : r ∉ W.S := Finset.disjoint_left.1 hW (root_mem_joinF_S h)
  have hvJ : v ∈ (joinF r k U).S := mem_joinF_S h hv
  have hupd : ∀ i, (Function.update U j (graft (U j) W v) i).S
      = if i = j then (U j).S ∪ W.S else (U i).S := fun i => by
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, if_pos rfl, graft_S hjW hv]
    · rw [Function.update_of_ne hij, if_neg hij]
  have hOK : JoinOK r (Function.update U j (graft (U j) W v)) := by
    refine ⟨fun i => ?_, fun i i' hii' => ?_⟩
    · rw [hupd]
      split_ifs
      · exact fun h' => (Finset.mem_union.1 h').elim (h.not_mem j) hrW
      · exact h.not_mem i
    · rw [hupd, hupd]
      split_ifs with h1 h2 h2
      · exact absurd (h1.trans h2.symm) hii'
      · subst h1
        exact Finset.disjoint_union_left.2 ⟨h.disj _ _ hii', (hiW i').symm⟩
      · subst h2
        exact Finset.disjoint_union_right.2 ⟨h.disj _ _ hii', hiW i⟩
      · exact h.disj _ _ hii'
  refine ⟨hOK, eq_joinF_of hOK _ ?_ ?_ ?_⟩
  · rw [graft_S hW hvJ, joinF_S h]
    ext a
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
      true_and, hupd]
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
  · rw [graft_root hW hvJ, joinF_root h]
  · intro i a ha
    rw [graft_par hW hvJ, graftPar]
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self] at ha ⊢
      rw [graft_S hjW hv] at ha
      rw [graft_root hjW hv, graft_par hjW hv, graftPar]
      by_cases hWr : a = W.root
      · have hne : a ≠ (U i).root := fun e =>
          Finset.disjoint_left.1 (hiW i) (e ▸ (U i).root_mem) (hWr ▸ W.root_mem)
        rw [if_pos hWr, if_neg hne, if_pos hWr]
      · by_cases haW : a ∈ W.S
        · have hne : a ≠ (U i).root := fun e =>
            Finset.disjoint_left.1 (hiW i) (e ▸ (U i).root_mem) haW
          rw [if_neg hWr, if_pos haW, if_neg hne, if_neg hWr, if_pos haW]
        · have haU : a ∈ (U i).S := (Finset.mem_union.1 ha).resolve_right haW
          rw [if_neg hWr, if_neg haW, joinF_par_of_mem h i haU]
          by_cases hr : a = (U i).root
          · rw [if_pos hr, if_pos hr]
          · rw [if_neg hr, if_neg hr, if_neg hWr, if_neg haW]
    · rw [Function.update_of_ne hij] at ha ⊢
      have haW : a ∉ W.S := Finset.disjoint_left.1 (hiW i) ha
      have hWr : a ≠ W.root := fun e => haW (e ▸ W.root_mem)
      rw [if_neg hWr, if_neg haW, joinF_par_of_mem h i ha]

/-- In a joined tree, the root of each tree leads its vertices to it. -/
lemma mem_desc_joinF {k : ℕ} {r : A} {U : Fin k → RootedTree A} (h : JoinOK r U) (i : Fin k)
    {a : A} (ha : a ∈ (U i).S) : a ∈ desc (joinF r k U) (U i).root := by
  refine mem_desc.2 ⟨mem_joinF_S h ha, ?_⟩
  obtain ⟨d, hd⟩ := (U i).acyc
  induction hk : d a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    by_cases hr : a = (U i).root
    · exact ⟨0, hr⟩
    · obtain ⟨m, hm⟩ := ih (d ((U i).par a)) (hk ▸ hd a ha hr) ((U i).par_mem a ha) rfl
      refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply, joinF_par_of_mem h i ha, if_neg hr]
      exact hm

/-- **The children of the root of a joined tree are the roots of the joined trees.** -/
theorem mem_children_joinF {k : ℕ} {r : A} {U : Fin k → RootedTree A} (h : JoinOK r U) {c : A} :
    c ∈ children (joinF r k U) ↔ ∃ i, c = (U i).root := by
  rw [mem_children, joinF_root h]
  constructor
  · rintro ⟨hc, hcr, hp⟩
    rw [joinF_S h, Finset.mem_insert, Finset.mem_biUnion] at hc
    obtain ⟨i, _, hi⟩ := hc.resolve_left hcr
    refine ⟨i, ?_⟩
    rw [joinF_par_of_mem h i hi] at hp
    by_contra hne
    rw [if_neg hne] at hp
    exact h.not_mem i (hp ▸ (U i).par_mem c hi)
  · rintro ⟨i, rfl⟩
    refine ⟨mem_joinF_S h (U i).root_mem, fun e => h.not_mem i (e ▸ (U i).root_mem), ?_⟩
    rw [joinF_par_of_mem h i (U i).root_mem, if_pos rfl]

/-- **The descendants of the root of a joined tree are its vertices.** -/
theorem desc_joinF {k : ℕ} {r : A} {U : Fin k → RootedTree A} (h : JoinOK r U) (i : Fin k) :
    desc (joinF r k U) (U i).root = (U i).S := by
  ext a
  refine ⟨fun ha => ?_, mem_desc_joinF h i⟩
  have haS := (mem_desc.1 ha).1
  rw [joinF_S h, Finset.mem_insert, Finset.mem_biUnion] at haS
  rcases haS with rfl | ⟨i', _, hi'⟩
  · obtain ⟨_, n, hn⟩ := mem_desc.1 ha
    have hr : (joinF a k U).par a = a := by
      have := (joinF a k U).par_root
      rwa [joinF_root h] at this
    rw [Function.iterate_fixed hr] at hn
    exact absurd (hn ▸ (U i).root_mem) (h.not_mem i)
  · by_cases hii : i' = i
    · exact hii ▸ hi'
    · have hc : (U i).root ∈ children (joinF r k U) := (mem_children_joinF h).2 ⟨i, rfl⟩
      have hc' : (U i').root ∈ children (joinF r k U) := (mem_children_joinF h).2 ⟨i', rfl⟩
      have e := child_unique hc hc' ha (mem_desc_joinF h i' hi')
      have h1 : (U i').root ∈ (U i).S := e ▸ (U i).root_mem
      exact absurd (U i').root_mem (Finset.disjoint_right.1 (h.disj _ _ hii) h1)

/-- **The subtree at the root of a joined tree is that tree.** -/
theorem subtree_joinF {k : ℕ} {r : A} {U : Fin k → RootedTree A} (h : JoinOK r U) (i : Fin k) :
    subtree (joinF r k U) (U i).root = U i := by
  have hm : (U i).root ∈ (joinF r k U).S := mem_joinF_S h (U i).root_mem
  ext a
  · rw [subtree_S hm, desc_joinF h i]
  · rw [subtree_par hm, desc_joinF h i]
    by_cases ha : a ∈ (U i).S ∧ a ≠ (U i).root
    · rw [if_pos ha, joinF_par_of_mem h i ha.1, if_neg ha.2]
    · rw [if_neg ha]
      by_cases haS : a ∈ (U i).S
      · have hr : a = (U i).root := by_contra fun h' => ha ⟨haS, h'⟩
        rw [hr, (U i).par_root]
      · exact ((U i).par_not_mem a haS).symm
  · rw [subtree_root hm]

end RootedTree

end Operad
