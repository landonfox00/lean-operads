/-
# Evaluating rooted trees in a pre-Lie algebra

For a pre-Lie product `m` on `L` and values `x : A → L` of the vertices, **the value of a rooted
tree** (`PreLieBrace.treeVal`) is the braces of the value of the root with the values of the
subtrees at its children, independent of their order by the symmetry of the braces. The value of
a join is the braces of the value of the root with the values of the joined trees
(`PreLieBrace.treeVal_joinF`).

* **The values are multiplicative** (`PreLieBrace.treeVal_graft`): the sum over the vertices `v`
  of `T` of the values of `T` with `W` grafted at `v` is `m (value T) (value W)`, for disjoint
  vertex sets. By induction on the vertices: the grafting at the root adds an entry to the
  braces, the graftings inside a subtree replace its value by its product with the value of `W`,
  and the brace recursion recombines them.
-/
import Operad.PreLieBrace
import Operad.RootedTree

namespace Operad

namespace RootedTree

variable {A : Type*} [DecidableEq A]

/-- The subtrees of a tree at the children of its root can be joined back. -/
lemma joinOK_subtrees (T : RootedTree A) {k : ℕ} (e : Fin k ≃ children T) :
    JoinOK T.root (fun i => subtree T (e i)) := by
  have hcS : ∀ i, (e i).1 ∈ T.S := fun i => (mem_children.1 (e i).2).1
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [subtree_S (hcS i)]
    exact root_not_mem_desc (mem_children.1 (e i).2).2.1
  · rw [subtree_S (hcS i), subtree_S (hcS j)]
    exact disjoint_desc (e i).2 (e j).2 fun h' => hij (e.injective (Subtype.ext h'))

lemma joinOK_snoc {r : A} {k : ℕ} {U : Fin k → RootedTree A} (h : JoinOK r U) {W : RootedTree A}
    (hW : Disjoint (joinF r k U).S W.S) :
    JoinOK r (Fin.snoc (α := fun _ => RootedTree A) U W) := by
  have hiW : ∀ i, Disjoint (U i).S W.S := fun i =>
    Finset.disjoint_of_subset_left (fun a ha => mem_joinF_S h ha) hW
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact Finset.disjoint_left.1 hW (root_mem_joinF_S h)
    | cast i => rw [Fin.snoc_castSucc]; exact h.not_mem i
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

end RootedTree

namespace PreLieBrace

open RootedTree

variable {R : Type*} [CommRing R] {L : Type*} [AddCommGroup L] [Module R L]
  (m : L →ₗ[R] L →ₗ[R] L) {A : Type*} [DecidableEq A]

/-- **The value of a rooted tree** in a pre-Lie algebra, for values `x` of the vertices: the
braces of the value of the root with the values of the subtrees. -/
noncomputable def treeVal (x : A → L) (T : RootedTree A) : L :=
  braceT m (x T.root) (fun c : ↥(children T) => treeVal x (subtree T c.1))
termination_by T.S.card
decreasing_by exact card_subtree_lt c.2

lemma treeVal_eq (x : A → L) (T : RootedTree A) :
    treeVal m x T = braceT m (x T.root) (fun c : ↥(children T) => treeVal m x (subtree T c.1)) := by
  rw [treeVal]

variable (hpl : ∀ x y z : L, m (m x y) z - m x (m y z) = m (m x z) y - m x (m z y))
include hpl

/-- **The value of a joined tree** is the braces of the value of the root with the values of the
joined trees. -/
theorem treeVal_joinF (x : A → L) {r : A} {k : ℕ} {U : Fin k → RootedTree A} (h : JoinOK r U) :
    treeVal m x (joinF r k U) = brace m k (x r) (fun i => treeVal m x (U i)) := by
  have hinj : Function.Injective (fun i => (U i).root) := fun i j hij => by
    by_contra hne
    have hij' : (U i).root = (U j).root := hij
    exact Finset.disjoint_left.1 (h.disj i j hne) (U i).root_mem
      (by rw [hij']; exact (U j).root_mem)
  let e : Fin k ≃ ↥(children (joinF r k U)) := Equiv.ofBijective
    (fun i => ⟨(U i).root, (mem_children_joinF h).2 ⟨i, rfl⟩⟩)
    ⟨fun i j hij => hinj (congrArg Subtype.val hij), fun c => by
      obtain ⟨i, hi⟩ := (mem_children_joinF h).1 c.2
      exact ⟨i, Subtype.ext hi.symm⟩⟩
  rw [treeVal_eq, joinF_root h, braceT_eq m hpl _ _ e]
  congr 1
  funext i
  exact congrArg (treeVal m x) (subtree_joinF h i)

omit hpl in
/-- The value of a tree with one vertex. -/
lemma treeVal_vtx (x : A → L) (a : A) : treeVal m x (vtx a) = x a := by
  rw [treeVal_eq]
  have h0 : Fintype.card ↥(children (vtx a)) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun c => ?_⟩
    have h1 := mem_children.1 c.2
    exact h1.2.1 (Finset.mem_singleton.1 h1.1)
  unfold braceT
  have key : ∀ (k : ℕ), k = 0 → ∀ y : Fin k → L, brace m k (x a) y = x a := by
    intro k hk y
    subst hk
    rfl
  exact key _ h0 _

/-- **The values of trees are multiplicative**: the value of the sum of the graftings of `W` at
the vertices of `T` is the product of the values. -/
theorem treeVal_graft_sum (x : A → L) :
    ∀ (n : ℕ) (T : RootedTree A), T.S.card = n → ∀ (W : RootedTree A), Disjoint T.S W.S →
      ∑ v ∈ T.S, treeVal m x (graft T W v) = m (treeVal m x T) (treeVal m x W) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn W hTW
    classical
    let k := Fintype.card ↥(children T)
    let e : Fin k ≃ ↥(children T) := (Fintype.equivFin _).symm
    have hOK := joinOK_subtrees T e
    set U : Fin k → RootedTree A := fun i => subtree T (e i)
    have hT : T = joinF T.root k U := eq_joinF T e
    set r := T.root
    have hJW : Disjoint (joinF r k U).S W.S := hT ▸ hTW
    have hcard : ∀ i, (U i).S.card < n := fun i => hn ▸ card_subtree_lt (e i).2
    have hiW : ∀ i, Disjoint (U i).S W.S := fun i =>
      Finset.disjoint_of_subset_left (fun a ha => mem_joinF_S hOK ha) hJW
    have hY : treeVal m x T = brace m k (x r) (fun i => treeVal m x (U i)) := by
      rw [hT]
      exact treeVal_joinF m hpl x hOK
    -- the sum over the vertices: the root, then the vertices of each subtree
    have hS : T.S = insert r (Finset.univ.biUnion fun i => (U i).S) := by
      rw [hT]
      exact joinF_S hOK
    have hrn : r ∉ Finset.univ.biUnion fun i => (U i).S := by
      rw [Finset.mem_biUnion]
      rintro ⟨i, _, hi⟩
      exact hOK.not_mem i hi
    have hpd : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        fun i => (U i).S := fun i _ j _ hij => hOK.disj i j hij
    -- the term at the root
    have hroot : treeVal m x (graft T W r)
        = brace m (k + 1) (x r) (Fin.snoc (α := fun _ => L)
            (fun i => treeVal m x (U i)) (treeVal m x W)) := by
      have hsn := joinOK_snoc hOK hJW
      rw [hT, graft_joinF_root, treeVal_joinF m hpl x hsn]
      congr 1
      funext i
      induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last, Fin.snoc_last]
      | cast i => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    -- the terms at the vertices of a subtree
    have hsub : ∀ i, ∑ v ∈ (U i).S, treeVal m x (graft T W v)
        = brace m k (x r) (Function.update (fun j => treeVal m x (U j)) i
            (m (treeVal m x (U i)) (treeVal m x W))) := by
      intro i
      have hv : ∀ v ∈ (U i).S, treeVal m x (graft T W v)
          = brace m k (x r) (Function.update (fun j => treeVal m x (U j)) i
              (treeVal m x (graft (U i) W v))) := by
        intro v hv
        obtain ⟨hOK', heq⟩ := graft_joinF_of_mem hOK i hv hJW
        rw [hT, heq, treeVal_joinF m hpl x hOK']
        congr 1
        funext j
        by_cases hij : j = i
        · subst hij
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hij, Function.update_of_ne hij]
      rw [Finset.sum_congr rfl hv, ← brace_update_sum,
        ih _ (hcard i) (U i) rfl W (hiW i)]
    rw [hS, Finset.sum_insert hrn, Finset.sum_biUnion hpd, hroot,
      Finset.sum_congr rfl fun i _ => hsub i, brace_snoc, hY]
    abel

/-- **The value of a tree grafted with another**, summed over its vertices, as a product. -/
theorem treeVal_graft (x : A → L) (T W : RootedTree A) (h : Disjoint T.S W.S) :
    ∑ v ∈ T.S, treeVal m x (graft T W v) = m (treeVal m x T) (treeVal m x W) :=
  treeVal_graft_sum m hpl x _ T rfl W h

end PreLieBrace

end Operad
