/-
# The composition of `PreLie` in the basis of trees: insertion at a vertex

`Operad.PreLieTrees` identifies an operation of the pre-Lie operad with inputs `A` with a
combination of rooted trees with vertex set `A` (`PreLie.treeAct`, `PreLie.treeEquiv`). This file
proves that **the composition is insertion of trees at a vertex, over every way of attaching the
children of the vertex** (Chapoton and Livernet):

* **`PreLie.treeAct_comp`.** The trees of `comp i p q`, relabelled into `Option C` for
  `C = (A ∖ i) ⊔ B`, are the sum, over the trees `T` of `p` and `S` of `q` with their
  coefficients, of `RootedTree.insSum R T' S' none`: the insertions of `S` at the vertex `i` of
  `T`, `i` renamed `none`, one for each map from the children of `i` to the vertices of `S`.
  On basis trees this is `PreLie.treeAct_comp_trees`. Relabelling along `some` is injective
  (`RootedTree.map_injective`, `Finsupp.mapDomain_injective`), so the formula determines the
  composite.
* **`PreLie.treeAct_map`.** Relabelling an operation relabels its trees.

The proof:

* **Actions as tree values** (`PreLie.act_eq_tv`). In the grafting algebra an operation acts on
  any family by the values of its trees, by the multiplicativity of tree values
  (`PreLie.act_supp_tv`); the values of relabelled trees with one vertex are the relabelled trees
  (`PreLieBrace.treeVal_map`, `PreLie.tv_vtx_map`).
* **Linearity at a vertex** (`PreLieBrace.treeVal_update_finsupp`): the value of a tree is linear
  in the value of each vertex.
* **Substitution** (`RootedTree.treeVal_update_single`): in the grafting algebra, the value of `T`
  with the tree `S` at the vertex `i` and the trees with one vertex elsewhere is the sum of the
  insertions. By induction on `T` decomposed at its root: at the root, the braces of `S` with the
  subtrees are the graftings of the subtrees at the vertices of `S`
  (`RootedTree.brace_single_graftF`), which are the insertions (`RootedTree.ins_root_eq`); below
  the root, insertion happens in one subtree (`RootedTree.ins_joinF`).

Limits: the operad of rooted trees is not constructed as an operad in its own right; its
composition is the transported one, which these theorems compute.
-/
import Operad.PreLieTrees
import Operad.RootedTreeOps

universe u

namespace Operad

open Sym

/-! ## More on the values of trees -/

namespace PreLieBrace

variable {R : Type*} [CommRing R] {L : Type*} [AddCommGroup L] [Module R L]
  (m : L →ₗ[R] L →ₗ[R] L)

/-- **The braces are additive in the first entry.** -/
lemma brace_add_left : ∀ (k : ℕ) (x x' : L) (Y : Fin k → L),
    brace m k (x + x') Y = brace m k x Y + brace m k x' Y
  | 0, _, _, _ => rfl
  | k + 1, x, x', Y => by
    simp only [brace_succ, brace_add_left k, map_add, LinearMap.add_apply,
      Finset.sum_add_distrib]
    abel

/-- **The braces are homogeneous in the first entry.** -/
lemma brace_smul_left : ∀ (k : ℕ) (c : R) (x : L) (Y : Fin k → L),
    brace m k (c • x) Y = c • brace m k x Y
  | 0, _, _, _ => rfl
  | k + 1, c, x, Y => by
    simp only [brace_succ, brace_smul_left k, map_smul, LinearMap.smul_apply, smul_sub,
      Finset.smul_sum]

variable {A : Type*} [DecidableEq A]

open RootedTree

/-- **The value of a tree only depends on the values of its vertices.** -/
theorem treeVal_congr {x y : A → L} :
    ∀ (n : ℕ) (T : RootedTree A), T.S.card = n → (∀ a ∈ T.S, x a = y a) →
      treeVal m x T = treeVal m y T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn h
    rw [treeVal_eq, treeVal_eq, h _ T.root_mem]
    congr 1
    funext c
    have hc := (mem_children.1 c.2).1
    refine ih _ (hn ▸ card_subtree_lt c.2) _ rfl fun a ha => h a ?_
    rw [subtree_S hc] at ha
    exact desc_subset _ ha

variable (hpl : ∀ x y z : L, m (m x y) z - m x (m y z) = m (m x z) y - m x (m z y))
include hpl

/-- **The value of a tree is additive in the value of one vertex.** -/
theorem treeVal_update_add (x : A → L) (i : A) (u v : L) :
    ∀ (n : ℕ) (T : RootedTree A), T.S.card = n → i ∈ T.S →
      treeVal m (Function.update x i (u + v)) T
        = treeVal m (Function.update x i u) T + treeVal m (Function.update x i v) T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn hi
    classical
    let k := Fintype.card ↥(children T)
    let e : Fin k ≃ ↥(children T) := (Fintype.equivFin _).symm
    have hOK := joinOK_subtrees T e
    have hT : T = joinF T.root k (fun j => subtree T (e j)) := eq_joinF T e
    have hcS : ∀ j, (e j).1 ∈ T.S := fun j => (mem_children.1 (e j).2).1
    have hsub : ∀ j, (subtree T (e j)).S ⊆ T.S := fun j => by
      rw [subtree_S (hcS j)]
      exact desc_subset _
    have hval : ∀ w : L, treeVal m (Function.update x i w) T = brace m k
        (Function.update x i w T.root) fun j => treeVal m (Function.update x i w) (subtree T (e j))
        := fun w => by
      conv_lhs => rw [hT]
      exact treeVal_joinF m hpl _ hOK
    rw [hval, hval, hval]
    by_cases hr : i = T.root
    · have hc : ∀ (w : L) j, treeVal m (Function.update x i w) (subtree T (e j))
          = treeVal m x (subtree T (e j)) := fun w j =>
        treeVal_congr m _ _ rfl fun a ha => Function.update_of_ne (fun e' => hOK.not_mem j
          (by rw [← hr, ← e']; exact ha)) _ _
      simp only [hc]
      rw [← hr, Function.update_self, Function.update_self, Function.update_self, brace_add_left]
    · obtain ⟨c, hc, hic⟩ := exists_child hi hr
      set j := e.symm ⟨c, hc⟩
      have hj : i ∈ (subtree T (e j)).S := by
        rw [subtree_S (hcS j)]
        simpa [j] using hic
      have hroot : ∀ w : L, Function.update x i w T.root = x T.root := fun w =>
        Function.update_of_ne (Ne.symm hr) _ _
      have hother : ∀ (w : L) j', j' ≠ j → treeVal m (Function.update x i w) (subtree T (e j'))
          = treeVal m x (subtree T (e j')) := fun w j' hj' =>
        treeVal_congr m _ _ rfl fun a ha => Function.update_of_ne (fun e' =>
          Finset.disjoint_left.1 (hOK.disj j j' (Ne.symm hj')) hj (by rw [← e']; exact ha)) _ _
      have hfam : ∀ w : L, (fun j' => treeVal m (Function.update x i w) (subtree T (e j')))
          = Function.update (fun j' => treeVal m x (subtree T (e j'))) j
              (treeVal m (Function.update x i w) (subtree T (e j))) := fun w => by
        funext j'
        by_cases hj' : j' = j
        · subst hj'
          rw [Function.update_self]
        · rw [Function.update_of_ne hj', hother w j' hj']
      rw [hroot, hroot, hroot, hfam, hfam, hfam,
        ih _ (hn ▸ card_subtree_lt (e j).2) _ rfl hj, brace_update_add]

/-- **The value of a tree is homogeneous in the value of one vertex.** -/
theorem treeVal_update_smul (x : A → L) (i : A) (c : R) (u : L) :
    ∀ (n : ℕ) (T : RootedTree A), T.S.card = n → i ∈ T.S →
      treeVal m (Function.update x i (c • u)) T = c • treeVal m (Function.update x i u) T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn hi
    classical
    let k := Fintype.card ↥(children T)
    let e : Fin k ≃ ↥(children T) := (Fintype.equivFin _).symm
    have hOK := joinOK_subtrees T e
    have hT : T = joinF T.root k (fun j => subtree T (e j)) := eq_joinF T e
    have hcS : ∀ j, (e j).1 ∈ T.S := fun j => (mem_children.1 (e j).2).1
    have hval : ∀ w : L, treeVal m (Function.update x i w) T = brace m k
        (Function.update x i w T.root) fun j => treeVal m (Function.update x i w) (subtree T (e j))
        := fun w => by
      conv_lhs => rw [hT]
      exact treeVal_joinF m hpl _ hOK
    rw [hval, hval]
    by_cases hr : i = T.root
    · have hc : ∀ (w : L) j, treeVal m (Function.update x i w) (subtree T (e j))
          = treeVal m x (subtree T (e j)) := fun w j =>
        treeVal_congr m _ _ rfl fun a ha => Function.update_of_ne (fun e' => hOK.not_mem j
          (by rw [← hr, ← e']; exact ha)) _ _
      simp only [hc]
      rw [← hr, Function.update_self, Function.update_self, brace_smul_left]
    · obtain ⟨c', hc', hic⟩ := exists_child hi hr
      set j := e.symm ⟨c', hc'⟩
      have hj : i ∈ (subtree T (e j)).S := by
        rw [subtree_S (hcS j)]
        simpa [j] using hic
      have hroot : ∀ w : L, Function.update x i w T.root = x T.root := fun w =>
        Function.update_of_ne (Ne.symm hr) _ _
      have hother : ∀ (w : L) j', j' ≠ j → treeVal m (Function.update x i w) (subtree T (e j'))
          = treeVal m x (subtree T (e j')) := fun w j' hj' =>
        treeVal_congr m _ _ rfl fun a ha => Function.update_of_ne (fun e' =>
          Finset.disjoint_left.1 (hOK.disj j j' (Ne.symm hj')) hj (by rw [← e']; exact ha)) _ _
      have hfam : ∀ w : L, (fun j' => treeVal m (Function.update x i w) (subtree T (e j')))
          = Function.update (fun j' => treeVal m x (subtree T (e j'))) j
              (treeVal m (Function.update x i w) (subtree T (e j))) := fun w => by
        funext j'
        by_cases hj' : j' = j
        · subst hj'
          rw [Function.update_self]
        · rw [Function.update_of_ne hj', hother w j' hj']
      rw [hroot, hroot, hfam, hfam, ih _ (hn ▸ card_subtree_lt (e j).2) _ rfl hj,
        brace_update_smul]

end PreLieBrace

namespace PreLieBrace

variable {R : Type*} [CommRing R] {L : Type*} [AddCommGroup L] [Module R L]
  (m : L →ₗ[R] L →ₗ[R] L)
  (hpl : ∀ x y z : L, m (m x y) z - m x (m y z) = m (m x z) y - m x (m z y))
include hpl

open RootedTree

/-- **The value of a relabelled tree** is the value of the tree with the relabelled values. -/
theorem treeVal_map {A B : Type*} [DecidableEq A] [DecidableEq B] (x : B → L) (g : A → B)
    (hg : Function.Injective g) :
    ∀ (n : ℕ) (T : RootedTree A), T.S.card = n →
      treeVal m x (RootedTree.map g hg T) = treeVal m (x ∘ g) T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn
    classical
    let k := Fintype.card ↥(children T)
    let e : Fin k ≃ ↥(children T) := (Fintype.equivFin _).symm
    have hOK := joinOK_subtrees T e
    have hT : T = joinF T.root k (fun i => subtree T (e i)) := eq_joinF T e
    rw [hT, map_joinF _ _ _ hOK, treeVal_joinF m hpl _ (hOK.map (hg := hg)),
      treeVal_joinF m hpl _ hOK]
    have hU : (fun i => treeVal m x (RootedTree.map g hg (subtree T (e i))))
        = fun i => treeVal m (x ∘ g) (subtree T (e i)) := by
      funext i
      exact ih _ (hn ▸ card_subtree_lt (e i).2) _ rfl
    rw [hU]
    rfl

end PreLieBrace

/-! ## Braces of a tree with trees -/

namespace RootedTree

variable {R : Type u} [CommRing R] {Λ : Type} [DecidableEq Λ]

/-- Sums over the maps from `Fin (k + 1)`, by the last value. -/
lemma sum_fin_succ_fun {α : Type*} [Fintype α] {M : Type*} [AddCommMonoid M] (k : ℕ)
    (F : (Fin (k + 1) → α) → M) :
    ∑ f : Fin (k + 1) → α, F f
      = ∑ g : Fin k → α, ∑ v : α, F (Fin.snoc (α := fun _ => α) g v) := by
  rw [← (Fin.snocEquiv fun _ => α).sum_comp, Fintype.sum_prod_type_right]
  rfl

/-- **The braces of a tree with trees are the sums of the graftings of the trees at the vertices
of the tree**, in the grafting algebra. -/
theorem brace_single_graftF (S : RootedTree Λ) :
    ∀ (k : ℕ) (U : Fin k → RootedTree Λ), (∀ i, Disjoint S.S (U i).S) →
      (∀ i j, i ≠ j → Disjoint (U i).S (U j).S) →
      PreLieBrace.brace (graftMul R) k (Finsupp.single S 1) (fun i => Finsupp.single (U i) 1)
        = ∑ f : Fin k → ↥S.S, Finsupp.single (graftF S k U fun i => (f i).1) 1
  | 0, U, _, _ => by
    rw [Fintype.sum_unique]
    rfl
  | k + 1, U, hS, hU => by
    have hSi : ∀ i, Disjoint S.S (Fin.init U i).S := fun i => hS _
    have hUi : ∀ i j, i ≠ j → Disjoint (Fin.init U i).S (Fin.init U j).S :=
      fun i j hij => hU _ _ fun e => hij (Fin.castSucc_injective _ e)
    have hIH := brace_single_graftF S k (Fin.init U) hSi hUi
    have hOK : ∀ g : Fin k → ↥S.S, GraftOK S (Fin.init U) fun i => (g i).1 := fun g =>
      ⟨fun i => (g i).2, hSi, hUi⟩
    have hdl : ∀ g : Fin k → ↥S.S,
        Disjoint (graftF S k (Fin.init U) fun i => (g i).1).S (U (Fin.last k)).S := by
      intro g
      rw [graftF_S (hOK g), Finset.disjoint_union_left, Finset.disjoint_biUnion_left]
      exact ⟨hS _, fun i _ => hU _ _ (Fin.castSucc_lt_last i).ne⟩
    -- the graftings of the last tree at the vertices of the base tree
    have hbase : ∀ g : Fin k → ↥S.S, ∑ v ∈ S.S,
        Finsupp.single (graft (graftF S k (Fin.init U) fun i => (g i).1) (U (Fin.last k)) v)
          (1 : R)
        = ∑ v : ↥S.S, Finsupp.single (graftF S (k + 1) U
            fun i => (Fin.snoc (α := fun _ => ↥S.S) g v i).1) 1 := by
      intro g
      rw [← Finset.sum_coe_sort S.S]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [graft_graftF_base]
      congr 2
      · exact Fin.snoc_init_self U
      · funext i
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last, Fin.snoc_last]
        | cast i => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    -- the graftings of the last tree inside the grafted trees
    have hinner : ∀ i : Fin k,
        PreLieBrace.brace (graftMul R) k (Finsupp.single S 1)
          (Function.update (fun j => Finsupp.single (Fin.init U j) (1 : R)) i
            (graftMul R (Finsupp.single (Fin.init U i) 1) (Finsupp.single (U (Fin.last k)) 1)))
        = ∑ g : Fin k → ↥S.S, ∑ v ∈ (Fin.init U i).S, Finsupp.single
            (graft (graftF S k (Fin.init U) fun j => (g j).1) (U (Fin.last k)) v) 1 := by
      intro i
      have hiW : Disjoint (Fin.init U i).S (U (Fin.last k)).S :=
        hU _ _ (Fin.castSucc_lt_last i).ne
      rw [graftMul_single]
      unfold graftProd
      rw [if_pos hiW, PreLieBrace.brace_update_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hOK' := (graft_graftF_of_mem (hOK (fun _ => ⟨S.root, S.root_mem⟩)) i hv
        (hdl _)).1
      have hSu : ∀ j, Disjoint S.S (Function.update (Fin.init U) i
          (graft (Fin.init U i) (U (Fin.last k)) v) j).S := hOK'.disjS
      have hUu := hOK'.disj
      have e1 : (Function.update (fun j => Finsupp.single (Fin.init U j) (1 : R)) i
          (Finsupp.single (graft (Fin.init U i) (U (Fin.last k)) v) 1))
          = fun j => Finsupp.single (Function.update (Fin.init U) i
              (graft (Fin.init U i) (U (Fin.last k)) v) j) 1 := by
        funext j
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      rw [e1, brace_single_graftF S k _ hSu hUu]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [(graft_graftF_of_mem (hOK g) i hv (hdl g)).2]
    rw [PreLieBrace.brace_succ]
    have hinit : (Fin.init fun i => Finsupp.single (U i) (1 : R))
        = fun j => Finsupp.single (Fin.init U j) 1 := rfl
    rw [hinit, hIH, Finset.sum_congr rfl fun i _ => hinner i, map_sum, LinearMap.sum_apply]
    have hprod : ∀ g : Fin k → ↥S.S,
        graftMul R (Finsupp.single (graftF S k (Fin.init U) fun i => (g i).1) 1)
          (Finsupp.single (U (Fin.last k)) 1)
        = ∑ v ∈ S.S, Finsupp.single
            (graft (graftF S k (Fin.init U) fun i => (g i).1) (U (Fin.last k)) v) 1
          + ∑ i : Fin k, ∑ v ∈ (Fin.init U i).S, Finsupp.single
            (graft (graftF S k (Fin.init U) fun j => (g j).1) (U (Fin.last k)) v) 1 := by
      intro g
      rw [graftMul_single]
      unfold graftProd
      rw [if_pos (hdl g), graftF_S (hOK g), Finset.sum_union, Finset.sum_biUnion]
      · intro i _ j _ hij
        exact hUi i j hij
      · rw [Finset.disjoint_biUnion_right]
        exact fun i _ => hSi i
    rw [Finset.sum_congr rfl fun g _ => hprod g, Finset.sum_add_distrib, Finset.sum_comm
      (s := Finset.univ) (t := Finset.univ) (f := fun i g => ∑ v ∈ (Fin.init U i).S, _),
      add_sub_cancel_right, sum_fin_succ_fun]
    exact Finset.sum_congr rfl fun g _ => hbase g

end RootedTree

/-! ## Inserting a tree: the vertex sets and the parents -/

namespace RootedTree

variable {A : Type*} [DecidableEq A]

lemma ins_of {T S : RootedTree A} {i : A} {g : A → A} (h : InsOK T S i g) :
    (ins T S i g).S = T.S.erase i ∪ S.S ∧ (ins T S i g).par = insPar T S i g ∧
      (ins T S i g).root = if i = T.root then S.root else T.root := by
  unfold ins
  rw [dif_pos h]
  exact ⟨rfl, rfl, rfl⟩

/-- **Inserting at the root** grafts the subtrees at the children of the root at vertices of
`S`. -/
theorem ins_root_eq {T S : RootedTree A} {k : ℕ} (e : Fin k ≃ ↥(children T)) {g : A → A}
    (hd : Disjoint T.S S.S) (hg : ∀ c ∈ children T, g c ∈ S.S) :
    ins T S T.root g = graftF S k (fun j => subtree T (e j)) fun j => g (e j) := by
  have hOK := joinOK_subtrees T e
  have hcS : ∀ j, (e j).1 ∈ T.S := fun j => (mem_children.1 (e j).2).1
  have hsub : ∀ j, (subtree T (e j)).S ⊆ T.S := fun j => by
    rw [subtree_S (hcS j)]
    exact desc_subset _
  have hTS : T.S = insert T.root (Finset.univ.biUnion fun j => (subtree T (e j)).S) := by
    have h1 := congrArg RootedTree.S (eq_joinF T e)
    rw [joinF_S hOK] at h1
    exact h1
  have hnot : ∀ a, (∀ j, a ∉ (subtree T (e j)).S) → a ∈ T.S → a = T.root := fun a ha h1 => by
    rw [hTS, Finset.mem_insert] at h1
    rcases h1 with h1 | h1
    · exact h1
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 h1
      exact absurd hj (ha j)
  obtain ⟨hS, hpar, hroot⟩ := ins_of (show InsOK T S T.root g from ⟨T.root_mem, hd, hg⟩)
  have hGOK : GraftOK S (fun j => subtree T (e j)) fun j => g (e j) :=
    ⟨fun j => hg _ (e j).2, fun j => (Finset.disjoint_of_subset_left (hsub j) hd).symm,
      hOK.disj⟩
  refine eq_graftF_of hGOK _ ?_ ?_ ?_ ?_
  · have hr : T.root ∉ Finset.univ.biUnion fun j => (subtree T (e j)).S := fun h1 => by
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 h1
      exact hOK.not_mem j hj
    rw [hS, hTS, Finset.erase_insert hr, Finset.union_comm]
  · rw [hroot, if_pos rfl]
  · intro j a ha
    have haS : a ∉ S.S := Finset.disjoint_left.1 hd (hsub j ha)
    rw [hpar, subtree_root (hcS j)]
    unfold insPar
    rw [if_neg haS]
    by_cases hae : a = e j
    · have hc : a ∈ childrenOf T T.root := by
        rw [hae, childrenOf_root]
        exact (e j).2
      rw [if_pos hae, if_pos hc, hae]
    · have hd' : a ∈ desc T (e j) := by
        rw [← subtree_S (hcS j)]
        exact ha
      have hnc : a ∉ childrenOf T T.root := fun hc => hae
        (child_unique hc (e j).2 (self_mem_desc (mem_children.1 hc).1) hd')
      have hnr : a ≠ T.root := fun h' => hOK.not_mem j (by rw [← h']; exact ha)
      rw [if_neg hae, subtree_par (hcS j), if_neg hnc, if_neg hnr, if_pos ⟨hd', hae⟩]
  · intro a ha
    rw [hpar]
    unfold insPar
    by_cases haS : a ∈ S.S
    · rw [if_pos haS]
      by_cases har : a = S.root
      · rw [if_pos har, if_pos rfl, har, S.par_root]
      · rw [if_neg har]
    · have hnc : a ∉ childrenOf T T.root := fun hc => by
        obtain ⟨h1, h2, -⟩ := mem_childrenOf.1 hc
        exact h2 (hnot a ha h1)
      rw [if_neg haS, if_neg hnc, S.par_not_mem a haS]
      by_cases har : a = T.root
      · rw [if_pos har]
      · rw [if_neg har]
        exact T.par_not_mem a fun h1 => har (hnot a ha h1)

/-- **Inserting at a vertex of a subtree at the root** inserts in that subtree. -/
theorem ins_joinF {r : A} {k : ℕ} {U : Fin k → RootedTree A} (h : JoinOK r U) {j₀ : Fin k}
    {i : A} (hi : i ∈ (U j₀).S) {S : RootedTree A} (hd : Disjoint (joinF r k U).S S.S) :
    childrenOf (joinF r k U) i = childrenOf (U j₀) i ∧
      ∀ g : A → A, (∀ c ∈ childrenOf (U j₀) i, g c ∈ S.S) →
        JoinOK r (Function.update U j₀ (ins (U j₀) S i g)) ∧
          ins (joinF r k U) S i g = joinF r k (Function.update U j₀ (ins (U j₀) S i g)) := by
  set J := joinF r k U with hJ
  have hJS : J.S = insert r (Finset.univ.biUnion fun j => (U j).S) := joinF_S h
  have hJr : J.root = r := joinF_root h
  have hUJ : ∀ j, (U j).S ⊆ J.S := fun j _ ha => mem_joinF_S h ha
  have hri : r ≠ i := fun e => h.not_mem j₀ (by rw [e]; exact hi)
  have hUS : ∀ j, Disjoint (U j).S S.S := fun j => Finset.disjoint_of_subset_left (hUJ j) hd
  have hrS : r ∉ S.S := Finset.disjoint_left.1 hd (root_mem_joinF_S h)
  have hnotin : ∀ j, j ≠ j₀ → i ∉ (U j).S := fun j hj h1 =>
    Finset.disjoint_left.1 (h.disj j j₀ hj) h1 hi
  have hch : childrenOf J i = childrenOf (U j₀) i := by
    ext c
    rw [mem_childrenOf, mem_childrenOf]
    constructor
    · rintro ⟨hcJ, hci, hpc⟩
      rw [hJS, Finset.mem_insert] at hcJ
      rcases hcJ with hcr | hcJ
      · rw [hcr, ← hJr, J.par_root, hJr] at hpc
        exact absurd hpc hri
      · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hcJ
        rw [joinF_par_of_mem h j hj] at hpc
        by_cases hcr : c = (U j).root
        · rw [if_pos hcr] at hpc
          exact absurd hpc hri
        · rw [if_neg hcr] at hpc
          have hj0 : j = j₀ := by
            by_contra hne
            exact hnotin j hne (by rw [← hpc]; exact (U j).par_mem c hj)
          subst hj0
          exact ⟨hj, hci, hpc⟩
    · rintro ⟨hc, hci, hpc⟩
      refine ⟨hUJ j₀ hc, hci, ?_⟩
      rw [joinF_par_of_mem h j₀ hc]
      have hcr : c ≠ (U j₀).root := fun e => by
        rw [e, (U j₀).par_root] at hpc
        exact hci (e.trans hpc)
      rw [if_neg hcr, hpc]
  refine ⟨hch, fun g hg => ?_⟩
  have hok0 : InsOK (U j₀) S i g := ⟨hi, hUS j₀, hg⟩
  obtain ⟨hS0, hpar0, hroot0⟩ := ins_of hok0
  obtain ⟨hS, hpar, hroot⟩ := ins_of (show InsOK J S i g from
    ⟨hUJ j₀ hi, hd, by rw [hch]; exact hg⟩)
  have hJ' : JoinOK r (Function.update U j₀ (ins (U j₀) S i g)) := by
    have hsub : ∀ j, (Function.update U j₀ (ins (U j₀) S i g) j).S ⊆ (U j).S ∪ S.S := by
      intro j a ha
      by_cases hj : j = j₀
      · rw [hj, Function.update_self, hS0] at ha
        rw [hj]
        rcases Finset.mem_union.1 ha with ha | ha
        · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase ha)
        · exact Finset.mem_union_right _ ha
      · rw [Function.update_of_ne hj] at ha
        exact Finset.mem_union_left _ ha
    refine ⟨fun j h1 => ?_, fun j j' hjj => ?_⟩
    · rcases Finset.mem_union.1 (hsub j h1) with h1 | h1
      · exact h.not_mem j h1
      · exact hrS h1
    · by_cases hj : j = j₀
      · have hj' : j' ≠ j₀ := fun e => hjj (hj.trans e.symm)
        rw [hj, Function.update_self, Function.update_of_ne hj', hS0,
          Finset.disjoint_union_left]
        exact ⟨Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
          (h.disj _ _ (Ne.symm hj')), (hUS j').symm⟩
      · by_cases hj' : j' = j₀
        · rw [hj', Function.update_self, Function.update_of_ne hj, hS0,
            Finset.disjoint_union_right]
          exact ⟨Finset.disjoint_of_subset_right (Finset.erase_subset _ _) (h.disj _ _ hj),
            hUS j⟩
        · rw [Function.update_of_ne hj, Function.update_of_ne hj']
          exact h.disj j j' hjj
  refine ⟨hJ', eq_joinF_of hJ' _ ?_ ?_ ?_⟩
  · ext a
    rw [hS, hJS, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_biUnion, Finset.mem_biUnion]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hai, har | ⟨j, hj⟩⟩ | haS)
      · exact Or.inl har
      · by_cases hj0 : j = j₀
        · refine Or.inr ⟨j₀, ?_⟩
          rw [Function.update_self, hS0, Finset.mem_union, Finset.mem_erase]
          exact Or.inl ⟨hai, hj0 ▸ hj⟩
        · exact Or.inr ⟨j, by rw [Function.update_of_ne hj0]; exact hj⟩
      · refine Or.inr ⟨j₀, ?_⟩
        rw [Function.update_self, hS0]
        exact Finset.mem_union_right _ haS
    · rintro (har | ⟨j, hj⟩)
      · exact Or.inl ⟨fun e => hri (har.symm.trans e), Or.inl har⟩
      · by_cases hj0 : j = j₀
        · rw [hj0, Function.update_self, hS0, Finset.mem_union, Finset.mem_erase] at hj
          rcases hj with ⟨hai, haU⟩ | haS
          · exact Or.inl ⟨hai, Or.inr ⟨j₀, haU⟩⟩
          · exact Or.inr haS
        · rw [Function.update_of_ne hj0] at hj
          exact Or.inl ⟨fun e => hnotin j hj0 (by rw [← e]; exact hj), Or.inr ⟨j, hj⟩⟩
  · rw [hroot, if_neg (by rw [hJr]; exact fun e => hri e.symm), hJr]
  · intro j a ha
    rw [hpar]
    by_cases hj : j = j₀
    · rw [hj, Function.update_self] at ha ⊢
      rw [hS0] at ha
      rw [hroot0, hpar0]
      unfold insPar
      have hJi : J.par i = if i = (U j₀).root then r else (U j₀).par i :=
        joinF_par_of_mem h j₀ hi
      have hiJ : ¬ i = J.root := by
        rw [hJr]
        exact fun e => hri e.symm
      rw [if_neg hiJ, hch, hJi]
      by_cases haS : a ∈ S.S
      · have haU : a ≠ (U j₀).root := fun e => Finset.disjoint_left.1 (hUS j₀)
          (by rw [e]; exact (U j₀).root_mem) haS
        rw [if_pos haS, if_pos haS]
        by_cases h0 : i = (U j₀).root
        · rw [if_pos h0, if_pos h0, if_pos h0]
          by_cases har : a = S.root
          · rw [if_pos har, if_pos har]
          · rw [if_neg har, if_neg har, if_neg har]
        · rw [if_neg h0, if_neg h0, if_neg haU, if_neg h0]
      · have haU : a ∈ (U j₀).S ∧ a ≠ i := by
          rcases Finset.mem_union.1 ha with ha | ha
          · exact ⟨Finset.mem_of_mem_erase ha, Finset.ne_of_mem_erase ha⟩
          · exact absurd ha haS
        have haSr : a ≠ S.root := fun e => haS (by rw [e]; exact S.root_mem)
        rw [if_neg haS, if_neg haS, if_neg haU.2, if_neg haU.2,
          joinF_par_of_mem h j₀ haU.1]
        by_cases hc : a ∈ childrenOf (U j₀) i
        · have hcr : a ≠ (U j₀).root := fun e => by
            obtain ⟨-, hci, hpc⟩ := mem_childrenOf.1 hc
            rw [e, (U j₀).par_root] at hpc
            exact hci (e.trans hpc)
          rw [if_pos hc, if_pos hc]
          by_cases h0 : i = (U j₀).root
          · rw [if_pos h0, if_neg haSr]
          · rw [if_neg h0, if_neg hcr]
        · rw [if_neg hc, if_neg hc]
          by_cases h0 : i = (U j₀).root
          · have har : a ≠ (U j₀).root := fun e => haU.2 (e.trans h0.symm)
            rw [if_pos h0, if_neg har, if_neg haSr]
          · rw [if_neg h0]
    · rw [Function.update_of_ne hj] at ha ⊢
      have haS : a ∉ S.S := Finset.disjoint_left.1 (hUS j) ha
      have hai : a ≠ i := fun e => hnotin j hj (by rw [← e]; exact ha)
      have hnc : a ∉ childrenOf J i := fun hc => by
        rw [hch] at hc
        exact Finset.disjoint_left.1 (h.disj j j₀ hj) ha (mem_childrenOf.1 hc).1
      unfold insPar
      rw [if_neg haS, if_neg hnc, if_neg hai, joinF_par_of_mem h j ha]

end RootedTree

/-! ## The value of a tree with a tree at one vertex -/

namespace PreLieBrace

variable {R : Type*} [CommRing R] {L : Type*} [AddCommGroup L] [Module R L]
  (m : L →ₗ[R] L →ₗ[R] L) {A : Type*} [DecidableEq A]
  (hpl : ∀ x y z : L, m (m x y) z - m x (m y z) = m (m x z) y - m x (m z y))
include hpl

/-- **The value of a tree is linear in the value of one vertex.** -/
theorem treeVal_update_finsupp {ι : Type*} (x : A → L) (i : A) (T : RootedTree A)
    (hi : i ∈ T.S) (Q : ι →₀ R) (s : ι → L) :
    treeVal m (Function.update x i (Q.sum fun t b => b • s t)) T
      = Q.sum fun t b => b • treeVal m (Function.update x i (s t)) T := by
  let F : L →ₗ[R] L :=
    { toFun := fun w => treeVal m (Function.update x i w) T
      map_add' := fun u v => treeVal_update_add m hpl x i u v _ T rfl hi
      map_smul' := fun c u => treeVal_update_smul m hpl x i c u _ T rfl hi }
  have h := map_finsuppSum F Q fun t b => b • s t
  simp only [map_smul] at h
  exact h

end PreLieBrace

namespace RootedTree

section attach

variable {A : Type*} [DecidableEq A] [Fintype A]

open Classical in
/-- The maps sending the labels in `K` into `V` and fixing the other labels. -/
noncomputable def attachMaps (K V : Finset A) : Finset (A → A) :=
  Finset.univ.filter fun g => (∀ c ∈ K, g c ∈ V) ∧ ∀ c, c ∉ K → g c = c

lemma mem_attachMaps {K V : Finset A} {g : A → A} :
    g ∈ attachMaps K V ↔ (∀ c ∈ K, g c ∈ V) ∧ ∀ c, c ∉ K → g c = c := by
  unfold attachMaps
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- Sums over the maps attaching the children of the root, as sums over the families. -/
lemma sum_attachMaps_children {M : Type*} [AddCommMonoid M] (T : RootedTree A) (V : Finset A)
    {k : ℕ} (e : Fin k ≃ ↥(children T)) (F : (Fin k → A) → M) :
    ∑ g ∈ attachMaps (children T) V, F (fun j => g (e j))
      = ∑ f : Fin k → ↥V, F fun j => (f j).1 := by
  refine Finset.sum_bij' (fun g hg j => ⟨g (e j), (mem_attachMaps.1 hg).1 _ (e j).2⟩)
    (fun f _ a => if h : a ∈ children T then (f (e.symm ⟨a, h⟩)).1 else a) ?_ ?_ ?_ ?_ ?_
  · intro g _
    exact Finset.mem_univ _
  · intro f _
    rw [mem_attachMaps]
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · dsimp only
      rw [dif_pos hc]
      exact (f _).2
    · dsimp only
      rw [dif_neg hc]
  · intro g hg
    funext a
    dsimp only
    by_cases ha : a ∈ children T
    · rw [dif_pos ha]
      simp
    · rw [dif_neg ha, (mem_attachMaps.1 hg).2 a ha]
  · intro f _
    funext j
    apply Subtype.ext
    simp
  · intro g _
    rfl

end attach

section subst

variable {R : Type u} [CommRing R] {Λ : Type} [Fintype Λ] [DecidableEq Λ]

variable (R) in
/-- **The insertions of `S` at the vertex `i` of `T`**, one for each way of attaching the
children of `i` to vertices of `S`. -/
noncomputable def insSum (T S : RootedTree Λ) (i : Λ) : RootedTree Λ →₀ R :=
  ∑ g ∈ attachMaps (childrenOf T i) S.S, Finsupp.single (ins T S i g) 1

/-- **Substituting a tree at a vertex**: in the grafting algebra, the value of `T` with the tree
`S` at the vertex `i` and the trees with one vertex elsewhere is the sum of the insertions of `S`
at `i`. -/
theorem treeVal_update_single (S : RootedTree Λ) (i : Λ) :
    ∀ (n : ℕ) (T : RootedTree Λ), T.S.card = n → i ∈ T.S → Disjoint T.S S.S →
      PreLieBrace.treeVal (graftMul R)
        (Function.update (fun a => Finsupp.single (vtx a) 1) i (Finsupp.single S 1)) T
        = insSum R T S i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn hi hd
    classical
    set x := Function.update (fun a => Finsupp.single (vtx a) (1 : R)) i (Finsupp.single S 1)
      with hx
    let k := Fintype.card ↥(children T)
    let e : Fin k ≃ ↥(children T) := (Fintype.equivFin _).symm
    have hOK := joinOK_subtrees T e
    have hT : T = joinF T.root k (fun j => subtree T (e j)) := eq_joinF T e
    have hcS : ∀ j, (e j).1 ∈ T.S := fun j => (mem_children.1 (e j).2).1
    have hsub : ∀ j, (subtree T (e j)).S ⊆ T.S := fun j => by
      rw [subtree_S (hcS j)]
      exact desc_subset _
    have hval : PreLieBrace.treeVal (graftMul R) x T = PreLieBrace.brace (graftMul R) k (x T.root)
        fun j => PreLieBrace.treeVal (graftMul R) x (subtree T (e j)) := by
      conv_lhs => rw [hT]
      exact PreLieBrace.treeVal_joinF (graftMul R) graft_preLie _ hOK
    have hfree : ∀ j, i ∉ (subtree T (e j)).S →
        PreLieBrace.treeVal (graftMul R) x (subtree T (e j)) = Finsupp.single (subtree T (e j)) 1 :=
      fun j hj => by
        have h' : ∀ a ∈ (subtree T (e j)).S, x a = Finsupp.single (vtx a) (1 : R) :=
          fun a ha => Function.update_of_ne (fun e' => hj (by rw [← e']; exact ha)) _ _
        rw [PreLieBrace.treeVal_congr (graftMul R) _ _ rfl h']
        exact treeVal_single _ _ rfl
    by_cases hr : i = T.root
    · have hxr : x T.root = Finsupp.single S 1 := by
        rw [hx, ← hr, Function.update_self]
      have hU : (fun j => PreLieBrace.treeVal (graftMul R) x (subtree T (e j)))
          = fun j => Finsupp.single (subtree T (e j)) 1 :=
        funext fun j => hfree j fun h' => hOK.not_mem j (by rw [← hr]; exact h')
      rw [hval, hxr, hU, brace_single_graftF S k _
        (fun j => (Finset.disjoint_of_subset_left (hsub j) hd).symm) hOK.disj]
      unfold insSum
      rw [hr, childrenOf_root]
      exact (sum_attachMaps_children T S.S e
        fun f => Finsupp.single (graftF S k (fun j => subtree T (e j)) f) (1 : R)).symm.trans
        (Finset.sum_congr rfl fun g hg => congrArg (fun T' => Finsupp.single T' (1 : R))
          (ins_root_eq e hd (mem_attachMaps.1 hg).1).symm)
    · obtain ⟨c, hc, hic⟩ := exists_child hi hr
      set j₀ := e.symm ⟨c, hc⟩ with hj₀
      have hej : (e j₀).1 = c := by rw [hj₀, Equiv.apply_symm_apply]
      have hi₀ : i ∈ (subtree T (e j₀)).S := by
        rw [hej, subtree_S (mem_children.1 hc).1]
        exact hic
      have hxr : x T.root = Finsupp.single (vtx T.root) 1 := Function.update_of_ne (Ne.symm hr) _ _
      have hfam : (fun j => PreLieBrace.treeVal (graftMul R) x (subtree T (e j)))
          = Function.update (fun j => Finsupp.single (subtree T (e j)) (1 : R)) j₀
              (insSum R (subtree T (e j₀)) S i) := by
        funext j
        by_cases hj : j = j₀
        · rw [hj, Function.update_self]
          exact ih _ (hn ▸ card_subtree_lt (e j₀).2) _ rfl hi₀
            (Finset.disjoint_of_subset_left (hsub j₀) hd)
        · rw [Function.update_of_ne hj]
          exact hfree j fun h' => Finset.disjoint_left.1 (hOK.disj j₀ j (Ne.symm hj)) hi₀ h'
      have hL2 := ins_joinF hOK hi₀ (S := S) (by rw [← hT]; exact hd)
      rw [← hT] at hL2
      rw [hval, hxr, hfam]
      unfold insSum
      rw [PreLieBrace.brace_update_sum, hL2.1]
      refine Finset.sum_congr rfl fun g hg => ?_
      obtain ⟨hJ, hE⟩ := hL2.2 g (mem_attachMaps.1 hg).1
      rw [hE, ← brace_single_joinF T.root k _ hJ]
      congr 1
      funext j
      by_cases hj : j = j₀
      · rw [hj, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]

end subst

end RootedTree

/-! ## The composition in the basis of trees -/

namespace PreLie

open RootedTree

variable {R : Type u} [CommRing R] {Λ : Type} [DecidableEq Λ]

variable (R Λ) in
/-- The product of the grafting algebra is the grafting product. -/
lemma toBilin_graftAlg : EndOp.toBilin (PreLie.algebraEquiv (graftAlg R Λ)).mul = graftMul R := by
  refine LinearMap.ext₂ fun x y => ?_
  have h1 := act_mu (graftAlg R Λ) ![x, y]
  rw [graftAlg_act_mu] at h1
  exact h1.symm

/-- **In the grafting algebra, an operation acts by the values of its trees.** -/
theorem act_eq_tv {A : Type} [Fintype A] [DecidableEq A] (p : PreLie R A)
    (x : A → RootedTree Λ →₀ R) :
    (graftAlg R Λ).act p x = tv (graftMul R) x (treeAct R A p) := by
  have h := (act_supp_tv (graftAlg R Λ) x p (fun a => {a}) (fun a => Finsupp.single (vtx a) 1)
    (fun a => single_mem_supp rfl) fun a a' h => Finset.disjoint_singleton.2 h).2
  rw [toBilin_graftAlg] at h
  rw [treeAct_apply, h]
  congr 1
  funext a
  rw [tv_single, PreLieBrace.treeVal_vtx]

/-- **The values of the relabelled trees with one vertex** are the relabelled trees. -/
lemma tv_vtx_map {B : Type} [DecidableEq B] (g : B → Λ) (hg : Function.Injective g)
    (P : RootedTree B →₀ R) :
    tv (graftMul R) (fun b => Finsupp.single (vtx (g b)) (1 : R)) P
      = Finsupp.mapDomain (RootedTree.map g hg) P := by
  induction P using Finsupp.induction_linear with
  | zero => simp
  | add P Q hP hQ => rw [map_add, hP, hQ, Finsupp.mapDomain_add]
  | single T c =>
    rw [tv, Finsupp.linearCombination_single, Finsupp.mapDomain_single]
    have h1 := PreLieBrace.treeVal_map (graftMul R) graft_preLie
      (fun a => Finsupp.single (vtx a) (1 : R)) g hg _ T rfl
    rw [treeVal_single _ (RootedTree.map g hg T) rfl] at h1
    have h3 : PreLieBrace.treeVal (graftMul R) (fun b => Finsupp.single (vtx (g b)) (1 : R)) T
        = Finsupp.single (RootedTree.map g hg T) 1 := h1.symm
    rw [h3, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The labels of a composite with the composition input `none`. -/
lemma feed_some_injective {A B : Type} [DecidableEq A] (i : A) :
    Function.Injective (feed i (fun c : Without A i ⊕ B => some c) none) := by
  intro a a' h
  by_cases ha : a = i
  · by_cases ha' : a' = i
    · rw [ha, ha']
    · rw [ha, feed_self, feed_of_ne ha'] at h
      exact absurd h (Option.some_ne_none _).symm
  · by_cases ha' : a' = i
    · rw [ha', feed_self, feed_of_ne ha] at h
      exact absurd h (Option.some_ne_none _)
    · rw [feed_of_ne ha, feed_of_ne ha'] at h
      exact congrArg Subtype.val (Sum.inl_injective (Option.some_injective _ h))

lemma some_inr_injective {A B : Type} [DecidableEq A] (i : A) :
    Function.Injective fun b : B => (some (Sum.inr b) : Option (Without A i ⊕ B)) :=
  fun _ _ h => Sum.inr_injective (Option.some_injective _ h)

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma treeAct_S (p : PreLie R A) {T : RootedTree A} (hT : T ∈ (treeAct R A p).support) :
    T.S = Finset.univ := by
  have h1 : treeAct R A p ∈ supp R (Finset.univ : Finset A) := by
    rw [← range_treeAct]
    exact LinearMap.mem_range_self _ p
  exact (Finsupp.mem_supported R _).1 h1 hT

/-- **The composition of `PreLie` is insertion of trees**: in the trees on the inputs of
`comp i p q` together with a new label `none` for `i`, a composite is the sum, over the trees `T`
of `p` and `S` of `q`, of the insertions of `S` at the vertex `i` of `T`, with every way of
attaching the children of `i` to the vertices of `S`. -/
theorem treeAct_comp (i : A) (p : PreLie R A) (q : PreLie R B) :
    Finsupp.mapDomain (RootedTree.map (fun c : Without A i ⊕ B => some c)
        (Option.some_injective _)) (treeAct R (Without A i ⊕ B) (SymOperad.comp (R := R) i p q))
      = (treeAct R A p).sum fun T a => (treeAct R B q).sum fun S b =>
          (a * b) • insSum R (RootedTree.map _ (feed_some_injective (B := B) i) T)
            (RootedTree.map _ (some_inr_injective i) S) none := by
  set φ : A → Option (Without A i ⊕ B) := feed i (fun c => some c) none with hφ
  set ψ : B → Option (Without A i ⊕ B) := fun b => some (Sum.inr b) with hψ
  set Q := treeAct R B q
  rw [← tv_vtx_map, ← act_eq_tv, SymAlgebra.act_comp]
  have hQ : (graftAlg R (Option (Without A i ⊕ B))).act q
      (fun b => Finsupp.single (vtx (some (Sum.inr b) : Option (Without A i ⊕ B))) (1 : R))
      = Q.sum fun S b => b • Finsupp.single (RootedTree.map ψ (some_inr_injective i) S) 1 := by
    rw [act_eq_tv]
    refine (tv_vtx_map ψ (some_inr_injective i) Q).trans ?_
    rw [Finsupp.mapDomain]
    exact Finsupp.sum_congr fun S _ => by rw [Finsupp.smul_single_one]
  rw [hQ, act_eq_tv, tv, Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun T hT => ?_
  have hY : feed i (fun c => Finsupp.single (vtx (some c)) (1 : R))
      (Q.sum fun S b => b • Finsupp.single (RootedTree.map ψ (some_inr_injective i) S) 1)
      = Function.update (fun l => Finsupp.single (vtx l) 1) none
          (Q.sum fun S b => b • Finsupp.single (RootedTree.map ψ (some_inr_injective i) S) 1)
        ∘ φ := by
    funext a
    by_cases ha : a = i
    · rw [ha, feed_self, Function.comp_apply, hφ, feed_self, Function.update_self]
    · rw [feed_of_ne ha, Function.comp_apply, hφ, feed_of_ne ha,
        Function.update_of_ne (Option.some_ne_none _)]
  have hiT : φ i ∈ (RootedTree.map φ (feed_some_injective i) T).S :=
    mem_map_S.2 (by rw [treeAct_S p hT]; exact Finset.mem_univ i)
  have hφi : φ i = none := by rw [hφ, feed_self]
  rw [hY, ← PreLieBrace.treeVal_map (graftMul R) graft_preLie _ φ (feed_some_injective i) _ T rfl]
  rw [hφi] at hiT
  rw [PreLieBrace.treeVal_update_finsupp (graftMul R) graft_preLie _ none _ hiT, Finsupp.smul_sum]
  refine Finsupp.sum_congr fun S _ => ?_
  have hdisj : Disjoint (RootedTree.map φ (feed_some_injective i) T).S
      (RootedTree.map ψ (some_inr_injective i) S).S := by
    rw [map_S, map_S]
    refine Finset.disjoint_left.2 fun l h1 h2 => ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 h1
    obtain ⟨b, -, hb⟩ := Finset.mem_map.1 h2
    simp only [Function.Embedding.coeFn_mk] at hb
    by_cases ha : a = i
    · rw [ha, hφi] at hb
      exact Option.some_ne_none _ hb
    · rw [hφ, feed_of_ne ha] at hb
      exact Sum.inr_ne_inl (Option.some_injective _ hb)
  rw [treeVal_update_single (RootedTree.map ψ (some_inr_injective i) S) none _ _ rfl hiT hdisj,
    smul_smul]

/-- The trees of an operation are those of its coordinates in the basis of trees. -/
lemma treeAct_eq_mapDomain (p : PreLie R A) :
    treeAct R A p = Finsupp.mapDomain Subtype.val (treeEquiv R A p) := by
  ext U
  by_cases hU : U.S = Finset.univ
  · show treeAct R A p (⟨U, hU⟩ : RTree A).1
      = Finsupp.mapDomain Subtype.val (treeEquiv R A p) (⟨U, hU⟩ : RTree A).1
    rw [Finsupp.mapDomain_apply Subtype.val_injective, treeEquiv_apply]
  · rw [Finsupp.mapDomain_notin_range _ _ fun ⟨V, hV⟩ => hU (hV ▸ V.2)]
    by_contra h
    exact hU (treeAct_S p (Finsupp.mem_support_iff.2 h))

/-- **The composite of two trees is the sum of the insertions** of the second at the vertex `i`
of the first, in the basis of trees of `PreLie`. -/
theorem treeAct_comp_trees (i : A) (T : RTree A) (S : RTree B) :
    Finsupp.mapDomain (RootedTree.map (fun c : Without A i ⊕ B => some c)
        (Option.some_injective _)) (treeAct R (Without A i ⊕ B) (SymOperad.comp (R := R) i
          ((treeEquiv R A).symm (Finsupp.single T 1)) ((treeEquiv R B).symm (Finsupp.single S 1))))
      = insSum R (RootedTree.map _ (feed_some_injective (B := B) i) T.1)
          (RootedTree.map _ (some_inr_injective i) S.1) none := by
  rw [treeAct_comp, treeAct_eq_mapDomain, treeAct_eq_mapDomain, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    Finsupp.sum_single_index, Finsupp.sum_single_index, one_mul, one_smul]
  · simp
  · simp

/-- **Relabelling an operation relabels its trees.** -/
theorem treeAct_map (σ : A ≃ B) (p : PreLie R A) :
    treeAct R B (SymOperad.map (R := R) σ p)
      = Finsupp.mapDomain (RootedTree.map σ σ.injective) (treeAct R A p) := by
  rw [treeAct_apply, SymAlgebra.act_map, act_eq_tv, tv_vtx_map]

end PreLie

end Operad
