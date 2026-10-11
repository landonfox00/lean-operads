/-
# The free symmetric operad is the free shuffle operad on the relabelled generators

For generators `T` without operations of arity zero, the underlying shuffle operad of the free
symmetric operad `Lin R (FreeSet T)` is the free shuffle operad on the generators with a
permutation of their inputs, `T k × Perm (Fin k)` (`Operad.FreeSet.shuffleIso`). So on every finite
linear order the free symmetric operad has a basis indexed by the shuffle monomials
(`Operad.FreeSet.shuffleBasis`).

* **Labelled planar trees** (`Operad.PTree`) with leaves labelled by `A` form a monad, and those
  whose leaves are the elements of `A`, each once, form a symmetric set operad (`Operad.LT`) into
  which the free set operad maps (`Operad.FreeSet.toLT`).
* **Sorting** (`Operad.PTree.sortTree`): a planar tree with distinct natural-number leaves becomes
  a shuffle tree once the children of every vertex are sorted by their least leaves, the vertex
  recording the sorting permutation. Sorting commutes with strictly increasing relabellings
  (`Operad.PTree.sortTree_map`) and with substitutions increasing with the least leaves
  (`Operad.PTree.sortTree_bind`), so it is a morphism of shuffle operads from the linearized
  labelled trees to the free shuffle operad (`Operad.LT.sortHom`).
* The lift of the relabelled generators and the sorting are inverse morphisms of shuffle operads,
  by the uniqueness parts of the two universal properties (`Operad.FreeSh.hom_ext`,
  `Operad.Pres.shuffle_hom_ext`).
-/
import Operad.ShuffleFreeUniv
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

universe u v

namespace Operad

/-! ## Labelled planar trees -/

/-- **Planar trees with labelled leaves**: vertices of arity `k` labelled by `T k`, leaves by
`A`. -/
inductive PTree (T : ℕ → Type v) (A : Type) : Type v
  /-- A leaf. -/
  | leaf (a : A) : PTree T A
  /-- A vertex with its children. -/
  | node {k : ℕ} (e : T k) (c : Fin k → PTree T A) : PTree T A

namespace PTree

variable {T : ℕ → Type v} {A B C : Type}

/-- **Relabelling** the leaves. -/
def map (f : A → B) : PTree T A → PTree T B
  | leaf a => leaf (f a)
  | node e c => node e fun j => (c j).map f

/-- **Substitution** of trees for the leaves. -/
def bind : PTree T A → (A → PTree T B) → PTree T B
  | leaf a, f => f a
  | node e c, f => node e fun j => (c j).bind f

/-- **The leaves.** -/
def leaves : PTree T A → Multiset A
  | leaf a => {a}
  | node _ c => ∑ j, (c j).leaves

@[simp] lemma map_leaf (f : A → B) (a : A) : (leaf a : PTree T A).map f = leaf (f a) := rfl

@[simp] lemma map_node (f : A → B) {k : ℕ} (e : T k) (c : Fin k → PTree T A) :
    (node e c).map f = node e fun j => (c j).map f := rfl

@[simp] lemma leaf_bind (a : A) (f : A → PTree T B) : (leaf a).bind f = f a := rfl

@[simp] lemma node_bind {k : ℕ} (e : T k) (c : Fin k → PTree T A) (f : A → PTree T B) :
    (node e c).bind f = node e fun j => (c j).bind f := rfl

@[simp] lemma leaves_leaf (a : A) : (leaf a : PTree T A).leaves = {a} := rfl

@[simp] lemma leaves_node {k : ℕ} (e : T k) (c : Fin k → PTree T A) :
    (node e c).leaves = ∑ j, (c j).leaves := rfl

lemma map_map (f : A → B) (g : B → C) : ∀ t : PTree T A, (t.map f).map g = t.map (g ∘ f)
  | leaf _ => rfl
  | node e c => by
    simp only [map_node]
    congr 1
    funext j
    exact map_map f g (c j)

lemma map_id' : ∀ t : PTree T A, t.map (fun a => a) = t
  | leaf _ => rfl
  | node e c => by
    simp only [map_node]
    congr 1
    funext j
    exact map_id' (c j)

lemma map_congr {f g : A → B} : ∀ (t : PTree T A), (∀ a ∈ t.leaves, f a = g a) →
    t.map f = t.map g
  | leaf a, h => by simp [h a (Multiset.mem_singleton_self a)]
  | node e c, h => by
    simp only [map_node]
    congr 1
    funext j
    exact map_congr (c j) fun a ha => h a (Multiset.mem_sum.2 ⟨j, Finset.mem_univ j, ha⟩)

lemma bind_leaf : ∀ t : PTree T A, t.bind leaf = t
  | leaf _ => rfl
  | node e c => by
    simp only [node_bind]
    congr 1
    funext j
    exact bind_leaf (c j)

lemma bind_bind (f : A → PTree T B) (g : B → PTree T C) :
    ∀ t : PTree T A, (t.bind f).bind g = t.bind fun a => (f a).bind g
  | leaf _ => rfl
  | node e c => by
    simp only [node_bind]
    congr 1
    funext j
    exact bind_bind f g (c j)

lemma map_bind (f : A → PTree T B) (g : B → C) :
    ∀ t : PTree T A, (t.bind f).map g = t.bind fun a => (f a).map g
  | leaf _ => rfl
  | node e c => by
    simp only [node_bind, map_node]
    congr 1
    funext j
    exact map_bind f g (c j)

lemma bind_map (f : A → B) (g : B → PTree T C) :
    ∀ t : PTree T A, (t.map f).bind g = t.bind fun a => g (f a)
  | leaf _ => rfl
  | node e c => by
    simp only [node_bind, map_node]
    congr 1
    funext j
    exact bind_map f g (c j)

lemma map_eq_bind (f : A → B) (t : PTree T A) : t.map f = t.bind fun a => leaf (f a) := by
  rw [← bind_map, bind_leaf]

lemma bind_congr {f g : A → PTree T B} : ∀ (t : PTree T A), (∀ a ∈ t.leaves, f a = g a) →
    t.bind f = t.bind g
  | leaf a, h => h a (Multiset.mem_singleton_self a)
  | node e c, h => by
    simp only [node_bind]
    congr 1
    funext j
    exact bind_congr (c j) fun a ha => h a (Multiset.mem_sum.2 ⟨j, Finset.mem_univ j, ha⟩)

lemma leaves_map (f : A → B) : ∀ t : PTree T A, (t.map f).leaves = t.leaves.map f
  | leaf _ => rfl
  | node e c => by
    rw [map_node, leaves_node, leaves_node, ← Multiset.mapAddMonoidHom_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ => leaves_map f (c j)

lemma sum_bind {ι α β : Type*} (s : Finset ι) (g : ι → Multiset α) (f : α → Multiset β) :
    (∑ i ∈ s, g i).bind f = ∑ i ∈ s, (g i).bind f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Multiset.add_bind, ih]

lemma leaves_bind (f : A → PTree T B) :
    ∀ t : PTree T A, (t.bind f).leaves = t.leaves.bind fun a => (f a).leaves
  | leaf a => by simp
  | node e c => by
    rw [node_bind, leaves_node, leaves_node, sum_bind]
    exact Finset.sum_congr rfl fun j _ => leaves_bind f (c j)

lemma mem_leaves_node {k : ℕ} {e : T k} {c : Fin k → PTree T A} {a : A} :
    a ∈ (node e c).leaves ↔ ∃ j, a ∈ (c j).leaves := by
  simp [Multiset.mem_sum]

lemma leaves_child_le {k : ℕ} (e : T k) (c : Fin k → PTree T A) (j : Fin k) :
    (c j).leaves ≤ (node e c).leaves := by
  rw [leaves_node, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  exact Multiset.le_add_right _ _

end PTree

/-! ## The set operad of labelled trees -/

open PTree Sym

/-- **Labelled trees on `A`**: planar trees whose leaves are the elements of `A`, each once. -/
@[nolint unusedArguments]
def LT (T : ℕ → Type v) (A : Type) [Fintype A] [DecidableEq A] : Type v :=
  {t : PTree T A // t.leaves = (Finset.univ : Finset A).val}

namespace LT

section CompFun

variable {T : ℕ → Type v} {A B : Type} [DecidableEq A]

/-- The substitution of a partial composition at `i`. -/
def compFun (i : A) (y : PTree T B) (a : A) : PTree T (Without A i ⊕ B) :=
  if h : a = i then y.map Sum.inr else leaf (Sum.inl ⟨a, h⟩)

lemma compFun_self (i : A) (y : PTree T B) : compFun i y i = y.map Sum.inr := dif_pos rfl

lemma compFun_ne (i : A) (y : PTree T B) {a : A} (h : a ≠ i) :
    compFun i y a = leaf (Sum.inl ⟨a, h⟩) := dif_neg h

end CompFun

variable {T : ℕ → Type v} {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype D] [DecidableEq D]

lemma eq_univ_iff {s : Multiset A} : s = (Finset.univ : Finset A).val ↔ ∀ a, s.count a = 1 := by
  constructor
  · rintro rfl a
    exact Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ a)
  · intro h
    ext a
    rw [h a, Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ a)]

lemma leaves_map_equiv (e : A ≃ B) {t : PTree T A}
    (ht : t.leaves = (Finset.univ : Finset A).val) :
    (t.map e).leaves = (Finset.univ : Finset B).val := by
  rw [leaves_map, ht, eq_univ_iff]
  intro b
  rw [← e.apply_symm_apply b, Multiset.count_map_eq_count' _ _ e.injective]
  exact Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _)

lemma leaves_comp (i : A) {x : PTree T A} (hx : x.leaves = (Finset.univ : Finset A).val)
    {y : PTree T B} (hy : y.leaves = (Finset.univ : Finset B).val) :
    (x.bind (compFun i y)).leaves = (Finset.univ : Finset (Without A i ⊕ B)).val := by
  rw [eq_univ_iff]
  intro c
  rw [leaves_bind, hx, Multiset.count_bind]
  change ∑ a, Multiset.count c (compFun i y a).leaves = 1
  rcases c with ⟨a₀, ha₀⟩ | b
  · rw [Finset.sum_eq_single a₀]
    · rw [compFun_ne i y ha₀, leaves_leaf, Multiset.count_singleton_self]
    · intro a _ ha
      by_cases hai : a = i
      · rw [hai, compFun_self, leaves_map, Multiset.count_eq_zero]
        simp
      · rw [compFun_ne i y hai, leaves_leaf, Multiset.count_singleton]
        exact if_neg fun h => ha (congrArg Subtype.val (Sum.inl_injective h)).symm
    · exact fun h => (h (Finset.mem_univ _)).elim
  · rw [Finset.sum_eq_single i]
    · rw [compFun_self, leaves_map, Multiset.count_map_eq_count' _ _ Sum.inr_injective, hy]
      exact Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ b)
    · intro a _ ha
      rw [compFun_ne i y ha, leaves_leaf, Multiset.count_singleton]
      exact if_neg Sum.inr_ne_inl
    · exact fun h => (h (Finset.mem_univ _)).elim

/-- **Labelled trees form a symmetric set operad**: relabelling the leaves, and substituting at
a leaf. -/
instance instSetOperad : SetOperad (LT T) where
  map e x := ⟨x.1.map e, leaves_map_equiv e x.2⟩
  map_refl x := Subtype.ext (PTree.map_id' x.1)
  map_trans e f x := Subtype.ext (PTree.map_map e f x.1).symm
  one := ⟨leaf (), rfl⟩
  comp i x y := ⟨x.1.bind (compFun i y.1), leaves_comp i x.2 y.2⟩
  map_comp σ τ i x y := Subtype.ext (by
    show (x.1.bind (compFun i y.1)).map (compEquiv σ τ i) =
      (x.1.map σ).bind (compFun (σ i) (y.1.map τ))
    rw [PTree.map_bind, PTree.bind_map]
    congr 1
    funext a
    by_cases h : a = i
    · subst h
      rw [compFun_self, compFun_self, PTree.map_map, PTree.map_map]
      rfl
    · rw [compFun_ne i _ h, compFun_ne (σ i) _ fun h' => h (σ.injective h')]
      rfl)
  comp_one i x := Subtype.ext (by
    show (x.1.bind (compFun i (leaf ()))).map (rightUnitEquiv i) = x.1
    rw [PTree.map_bind]
    conv_rhs => rw [← PTree.bind_leaf x.1]
    congr 1
    funext a
    by_cases h : a = i
    · subst h
      rw [compFun_self]
      rfl
    · rw [compFun_ne i _ h]
      rfl)
  one_comp {B} _ _ y := Subtype.ext (by
    show ((leaf ()).bind (compFun () y.1)).map (leftUnitEquiv B) = y.1
    rw [leaf_bind, compFun_self, PTree.map_map]
    exact PTree.map_id' y.1)
  comp_assoc_seq {A B D} _ _ _ _ _ _ i j x y z := Subtype.ext (by
    show ((x.1.bind (compFun i y.1)).bind (compFun (Sum.inr j) z.1)).map (seqEquiv i j D) =
      x.1.bind (compFun i (y.1.bind (compFun j z.1)))
    rw [PTree.bind_bind, PTree.map_bind]
    congr 1
    funext a
    by_cases h : a = i
    · subst h
      rw [compFun_self, compFun_self, PTree.bind_map, PTree.map_bind, PTree.map_bind]
      congr 1
      funext b
      by_cases hb : b = j
      · subst hb
        rw [compFun_self, compFun_self, PTree.map_map, PTree.map_map]
        rfl
      · rw [compFun_ne (Sum.inr j) _ fun h => hb (Sum.inr_injective h), compFun_ne j _ hb]
        rfl
    · rw [compFun_ne i y.1 h, compFun_ne i _ h, leaf_bind,
        compFun_ne (Sum.inr j) _ Sum.inl_ne_inr]
      rfl)
  comp_assoc_par {A B D} _ _ _ _ _ _ i k hik x y z := Subtype.ext (by
    show ((x.1.bind (compFun i y.1)).bind (compFun (Sum.inl ⟨k, Ne.symm hik⟩) z.1)).map
        (parEquiv hik B D) =
      (x.1.bind (compFun k z.1)).bind (compFun (Sum.inl ⟨i, hik⟩) y.1)
    rw [PTree.bind_bind, PTree.bind_bind, PTree.map_bind]
    congr 1
    funext a
    by_cases hai : a = i
    · subst hai
      rw [compFun_self, compFun_ne k _ hik, leaf_bind, compFun_self, PTree.bind_map,
        PTree.map_bind, PTree.map_eq_bind]
      congr 1
    · by_cases hak : a = k
      · subst hak
        rw [compFun_ne i _ hai, leaf_bind, compFun_self, compFun_self, PTree.bind_map,
          PTree.map_eq_bind, PTree.bind_map]
        congr 1
      · have h3 : (Sum.inl ⟨a, hai⟩ : Without A i ⊕ B) ≠ Sum.inl ⟨k, Ne.symm hik⟩ := fun h =>
          hak (congrArg Subtype.val (Sum.inl_injective h))
        have h4 : (Sum.inl ⟨a, hak⟩ : Without A k ⊕ D) ≠ Sum.inl ⟨i, hik⟩ := fun h =>
          hai (congrArg Subtype.val (Sum.inl_injective h))
        rw [compFun_ne i _ hai, compFun_ne k _ hak, leaf_bind, leaf_bind, compFun_ne _ _ h3,
          compFun_ne _ _ h4]
        rfl)

@[simp] lemma map_val (e : A ≃ B) (x : LT T A) : (SetOperad.map e x).1 = x.1.map e := rfl

@[simp] lemma comp_val (i : A) (x : LT T A) (y : LT T B) :
    (SetOperad.comp i x y).1 = x.1.bind (compFun i y.1) := rfl

@[simp] lemma one_val : (SetOperad.one : LT T Unit).1 = leaf () := rfl

/-- **A corolla**: a generator with its inputs in order. -/
def corolla {k : ℕ} (e : T k) : LT T (Fin k) :=
  ⟨node e fun j => leaf j, by
    rw [leaves_node]
    simp only [leaves_leaf]
    exact Multiset.sum_map_singleton _⟩

end LT

/-- **The free set operad maps to the labelled trees**, a generator going to its corolla. -/
def FreeSet.toLT (T : ℕ → Type v) : SetOperadHom (FreeSet T) (LT T) :=
  FreeSet.homEquiv.symm fun _ e => LT.corolla e

/-! ## Sorting -/

/-- **The relabelled generators**: a generator with a permutation of its inputs. -/
abbrev SGen (T : ℕ → Type v) (k : ℕ) : Type v := T k × Equiv.Perm (Fin k)

namespace PTree

variable {T : ℕ → Type v}

/-- Sorting is unchanged by a strictly increasing function of the values. -/
lemma sort_comp_strictMonoOn {n : ℕ} (w : Fin n → ℕ) {g : ℕ → ℕ}
    (hg : StrictMonoOn g (Set.range w)) : Tuple.sort (fun j => g (w j)) = Tuple.sort w := by
  refine (Tuple.eq_sort_iff.2 ⟨fun i j hij => ?_, fun i j hij h => ?_⟩).symm
  · exact hg.monotoneOn ⟨_, rfl⟩ ⟨_, rfl⟩ (Tuple.monotone_sort w hij)
  · exact (Tuple.eq_sort_iff.1 rfl).2 i j hij (hg.injOn ⟨_, rfl⟩ ⟨_, rfl⟩ h)

/-- **Sorting a planar tree**: the children of every vertex sorted by their least leaves, the
vertex recording the sorting permutation. -/
noncomputable def sortTree : PTree T ℕ → STree (SGen T)
  | leaf a => STree.leaf a
  | node e c => STree.node (e, Tuple.sort fun j => (sortTree (c j)).first)
      fun j => sortTree (c (Tuple.sort (fun j => (sortTree (c j)).first) j))

@[simp] lemma sortTree_leaf (a : ℕ) : sortTree (leaf a : PTree T ℕ) = STree.leaf a := rfl

lemma sortTree_node {k : ℕ} (e : T k) (c : Fin k → PTree T ℕ) :
    sortTree (node e c) = STree.node (e, Tuple.sort fun j => (sortTree (c j)).first)
      fun j => sortTree (c (Tuple.sort (fun j => (sortTree (c j)).first) j)) := by
  rw [sortTree]

/-- **Sorting keeps the leaves.** -/
lemma labels_sortTree : ∀ t : PTree T ℕ, (sortTree t).labels = t.leaves
  | leaf _ => rfl
  | node e c => by
    rw [sortTree_node, STree.labels_node, leaves_node]
    exact (Equiv.sum_comp _ fun j => (sortTree (c j)).labels).trans
      (Finset.sum_congr rfl fun j _ => labels_sortTree (c j))

lemma nodup_child {k : ℕ} {e : T k} {c : Fin k → PTree T ℕ} (h : (node e c).leaves.Nodup)
    (j : Fin k) : (c j).leaves.Nodup :=
  Multiset.nodup_of_le (leaves_child_le e c j) h

lemma disjoint_child {k : ℕ} {e : T k} {c : Fin k → PTree T ℕ} (h : (node e c).leaves.Nodup)
    {i j : Fin k} (hij : i ≠ j) : Disjoint (c i).leaves (c j).leaves := by
  have hle : (c i).leaves + (c j).leaves ≤ (node e c).leaves := by
    rw [leaves_node, ← Finset.sum_pair (f := fun x => (c x).leaves) hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => Multiset.zero_le _
  exact (Multiset.nodup_add.1 (Multiset.nodup_of_le hle h)).2.2

lemma pos_of_node [IsEmpty (T 0)] {k : ℕ} (e : T k) : 0 < k :=
  Nat.pos_of_ne_zero fun h => by
    subst h
    exact IsEmpty.false e

lemma first_mem_leaves {t : PTree T ℕ} (h : (sortTree t).IsShuffle) :
    (sortTree t).first ∈ t.leaves := by
  have := STree.first_mem h
  rwa [labels_sortTree] at this

variable [IsEmpty (T 0)]

/-- **A sorted tree with distinct leaves is a shuffle tree.** -/
theorem isShuffle_sortTree : ∀ t : PTree T ℕ, t.leaves.Nodup → (sortTree t).IsShuffle
  | leaf _, _ => trivial
  | node e c, hn => by
    have hc : ∀ j, (sortTree (c j)).IsShuffle := fun j =>
      isShuffle_sortTree (c j) (nodup_child hn j)
    have hinj : Function.Injective fun j => (sortTree (c j)).first := fun i j h => by
      by_contra hij
      have h' : (sortTree (c i)).first = (sortTree (c j)).first := h
      have hj := first_mem_leaves (hc j)
      rw [← h'] at hj
      exact Multiset.disjoint_left.1 (disjoint_child hn hij) (first_mem_leaves (hc i)) hj
    rw [sortTree_node]
    exact ⟨pos_of_node e, fun j => hc _,
      (Tuple.monotone_sort _).strictMono_of_injective (hinj.comp (Equiv.injective _))⟩

/-- **Sorting commutes with strictly increasing relabellings.** -/
theorem sortTree_map (f : ℕ → ℕ) : ∀ t : PTree T ℕ, t.leaves.Nodup →
    StrictMonoOn f {a | a ∈ t.leaves} → sortTree (t.map f) = (sortTree t).relabel f
  | leaf _, _, _ => rfl
  | node e c, hn, hf => by
    have hcf : ∀ j, StrictMonoOn f {a | a ∈ (c j).leaves} := fun j =>
      hf.mono fun a ha => Multiset.mem_of_le (leaves_child_le e c j) ha
    have ih : ∀ j, sortTree ((c j).map f) = (sortTree (c j)).relabel f := fun j =>
      sortTree_map f (c j) (nodup_child hn j) (hcf j)
    have hv : ∀ j, (sortTree ((c j).map f)).first = f (sortTree (c j)).first := fun j => by
      rw [ih j, STree.first_relabel f (isShuffle_sortTree (c j) (nodup_child hn j))]
    have hσ : Tuple.sort (fun j => f (sortTree (c j)).first) =
        Tuple.sort fun j => (sortTree (c j)).first := by
      refine sort_comp_strictMonoOn _ (hf.mono ?_)
      rintro _ ⟨j, rfl⟩
      exact Multiset.mem_of_le (leaves_child_le e c j)
        (first_mem_leaves (isShuffle_sortTree (c j) (nodup_child hn j)))
    rw [map_node, sortTree_node, sortTree_node]
    simp only [hv]
    simp only [hσ, ih]
    rfl

/-- **Sorting commutes with substitutions increasing with the least leaves.** -/
theorem sortTree_bind (xs : ℕ → PTree T ℕ) : ∀ t : PTree T ℕ, t.leaves.Nodup →
    StrictMonoOn (fun a => (sortTree (xs a)).first) {a | a ∈ t.leaves} →
    sortTree (t.bind xs) = (sortTree t).subst fun a => sortTree (xs a)
  | leaf _, _, _ => rfl
  | node e c, hn, hm => by
    have hcm : ∀ j, StrictMonoOn (fun a => (sortTree (xs a)).first) {a | a ∈ (c j).leaves} :=
      fun j => hm.mono fun a ha => Multiset.mem_of_le (leaves_child_le e c j) ha
    have ih : ∀ j, sortTree ((c j).bind xs) = (sortTree (c j)).subst fun a => sortTree (xs a) :=
      fun j => sortTree_bind xs (c j) (nodup_child hn j) (hcm j)
    have hv : ∀ j, (sortTree ((c j).bind xs)).first =
        (sortTree (xs (sortTree (c j)).first)).first := fun j => by
      rw [ih j, STree.first_subst (isShuffle_sortTree (c j) (nodup_child hn j))]
    have hσ : Tuple.sort (fun j => (sortTree (xs (sortTree (c j)).first)).first) =
        Tuple.sort fun j => (sortTree (c j)).first := by
      refine sort_comp_strictMonoOn (fun j => (sortTree (c j)).first)
        (g := fun a => (sortTree (xs a)).first) (hm.mono ?_)
      rintro _ ⟨j, rfl⟩
      exact Multiset.mem_of_le (leaves_child_le e c j)
        (first_mem_leaves (isShuffle_sortTree (c j) (nodup_child hn j)))
    rw [node_bind, sortTree_node, sortTree_node]
    simp only [hv]
    simp only [hσ, ih]
    rfl

end PTree

/-! ## Sorting as a morphism of shuffle operads -/

namespace LT

open PTree STree FreeSh

variable {T : ℕ → Type v}

lemma leaves_map_opos {A : Type} [Fintype A] [LinearOrder A] {t : PTree T A}
    (ht : t.leaves = (Finset.univ : Finset A).val) :
    (t.map opos).leaves = (Finset.range (Fintype.card A)).val := by
  rw [leaves_map, ht]
  refine (Multiset.Nodup.ext (Multiset.Nodup.map opos_injective Finset.univ.nodup)
    (Finset.range _).nodup).2 fun n => ?_
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Finset.mem_range]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ opos_lt_card a, fun h => ⟨oelt n h, opos_oelt n h⟩⟩

variable [IsEmpty (T 0)]

/-- **The sorted monomial** of a labelled tree on a finite linear order, its leaves relabelled by
their positions. -/
noncomputable def sorted {A : Type} [Fintype A] [LinearOrder A] (x : LT T A) :
    SMono (SGen T) (Finset.range (Fintype.card A)) :=
  ⟨sortTree (x.1.map opos), isShuffle_sortTree _ (by
    rw [leaves_map_opos x.2]
    exact (Finset.range _).nodup), by rw [labels_sortTree, leaves_map_opos x.2]⟩

@[simp] lemma sorted_val {A : Type} [Fintype A] [LinearOrder A] (x : LT T A) :
    (sorted x).1 = sortTree (x.1.map opos) := rfl

lemma sorted_map {A B : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    (e : A ≃o B) (x : LT T A) :
    sorted (SetOperad.map e.toEquiv x) =
      (sorted x).cast (congrArg Finset.range (Fintype.card_congr e.toEquiv)) := by
  refine Subtype.ext ?_
  simp only [sorted_val, SMono.cast_val, map_val, PTree.map_map]
  congr 2
  funext a
  exact opos_orderIso e a

lemma sorted_one : sorted (SetOperad.one : LT T Unit) = oneM := by
  refine Subtype.ext ?_
  simp only [sorted_val, one_val, PTree.map_leaf, sortTree_leaf, opos_unit]
  rfl

/-- **Sorting a partial composition along a shuffle** is grafting the sorted monomials. -/
lemma sorted_comp {A B C : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    [Fintype C] [LinearOrder C] (i : A) {e : Without A i ⊕ B ≃ C} (he : Operad.IsShuffle i e)
    (x : LT T A) (y : LT T B) :
    sorted (SetOperad.map e (SetOperad.comp i x y)) = graft he (sorted x) (sorted y) := by
  set g : ℕ → PTree T ℕ := fun n =>
    if n = opos i then (y.1.map opos).map (posR i e) else leaf (posL i e n) with hg
  have hy : (y.1.map opos).leaves.Nodup := by
    rw [leaves_map_opos y.2]
    exact (Finset.range _).nodup
  have hyR : StrictMonoOn (posR i e) {m | m ∈ (y.1.map opos).leaves} := fun m hm m' hm' h =>
    strictMonoOn_posR he (show m < Fintype.card B by
      rw [Set.mem_setOf_eq, leaves_map_opos y.2] at hm
      exact Finset.mem_range.1 hm) (show m' < Fintype.card B by
      rw [Set.mem_setOf_eq, leaves_map_opos y.2] at hm'
      exact Finset.mem_range.1 hm') h
  have hsg : ∀ n, sortTree (g n) = graftFam i e (sortTree (y.1.map opos)) n := fun n => by
    simp only [hg, graftFam]
    split_ifs
    · exact sortTree_map _ _ hy hyR
    · rfl
  have htree : ((x.1.bind (compFun i y.1)).map e).map opos = (x.1.map opos).bind g := by
    rw [PTree.map_map, PTree.map_bind, PTree.bind_map]
    congr 1
    funext a
    by_cases h : a = i
    · subst h
      rw [compFun_self, PTree.map_map]
      simp only [hg, if_pos rfl, PTree.map_map]
      congr 1
      funext b
      exact (posR_opos _ e b).symm
    · rw [compFun_ne i _ h]
      simp only [hg, if_neg fun h' => h (opos_injective h'), PTree.map_leaf]
      exact congrArg PTree.leaf (posL_opos i e ⟨a, h⟩).symm
  have hfirst : ∀ n, (sortTree (g n)).first = fL i e n := fun n => by
    rw [hsg, fL, graftFam]
    split_ifs with hn
    · have h0 : (sortTree (y.1.map opos)).first = 0 :=
        (first_eq_zero (sorted y).isShuffle (sorted y).labels_eq).1
      rw [first_relabel _ (isShuffle_sortTree _ hy), h0]
    · rfl
  have hmono : StrictMonoOn (fun n => (sortTree (g n)).first) {a | a ∈ (x.1.map opos).leaves} := by
    intro n hn n' hn' h
    rw [Set.mem_setOf_eq, leaves_map_opos x.2, Finset.mem_val, Finset.mem_range] at hn hn'
    simp only [hfirst]
    exact strictMonoOn_fL he (sorted y).isShuffle (sorted y).labels_eq hn hn' h
  refine Subtype.ext ?_
  show sortTree (((x.1.bind (compFun i y.1)).map e).map opos) =
    (sortTree (x.1.map opos)).subst (graftFam i e (sortTree (y.1.map opos)))
  rw [htree, sortTree_bind g _ (by rw [leaves_map_opos x.2]; exact (Finset.range _).nodup) hmono]
  congr 1
  funext n
  exact hsg n

variable (R : Type u) [CommRing R] (T)

/-- **Sorting, as a morphism of shuffle operads** from the linearized labelled trees to the free
shuffle operad on the relabelled generators. -/
noncomputable def sortHom : ShuffleOperadHom R (Shuf (Lin R (LT T))) (FreeSh R (SGen T)) where
  app A _ _ := Finsupp.lmapDomain R R sorted
  app_map e x := by
    show Finsupp.mapDomain sorted (Lin.mapL R e.toEquiv x) = mapM e (Finsupp.mapDomain sorted x)
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, Finsupp.mapDomain_add, Finsupp.mapDomain_add, map_add, hx, hy]
    | single s r =>
      rw [Lin.mapL_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single, mapM_single,
        sorted_map]
  app_one := by
    show Finsupp.mapDomain sorted (Finsupp.single SetOperad.one 1) = Finsupp.single oneM 1
    rw [Finsupp.mapDomain_single, sorted_one]
  app_comp i e he x y := by
    show Finsupp.mapDomain sorted (Lin.mapL R e (Lin.compL R i x y)) =
      bil (graft he) (Finsupp.mapDomain sorted x) (Finsupp.mapDomain sorted y)
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' =>
      rw [map_add, LinearMap.add_apply, map_add, Finsupp.mapDomain_add, hx, hx',
        Finsupp.mapDomain_add, map_add, LinearMap.add_apply]
    | single s r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' =>
        rw [map_add, map_add, Finsupp.mapDomain_add, hy, hy', Finsupp.mapDomain_add, map_add]
      | single t r' =>
        rw [Lin.compL_single, Lin.mapL_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
          Finsupp.mapDomain_single, bil_single, sorted_comp i he]

end LT

/-! ## The free symmetric operad as a free shuffle operad -/

namespace FreeSet

open PTree LT STree FreeSh

variable (R : Type u) [CommRing R] (T : ℕ → Type v)

lemma toLT_gen {k : ℕ} (e : T k) : (toLT T).app (Fin k) (Pres.gen e) = LT.corolla e := rfl

/-- **The lift of the relabelled generators**: a generator `e` with a permutation `σ` of its
inputs goes to `e` relabelled by `σ⁻¹`. -/
noncomputable def fromSh : ShuffleOperadHom R (FreeSh R (SGen T)) (Shuf (Lin R (FreeSet T))) :=
  FreeSh.lift R (Shuf (Lin R (FreeSet T))) fun _ g =>
    Finsupp.single (SetOperad.map g.2.symm (Pres.gen g.1)) 1

lemma fromSh_gen {k : ℕ} (hk : 0 < k) (g : SGen T k) :
    (fromSh R T).app (Fin k) (Finsupp.single (FreeSh.genM hk g) 1) =
      Finsupp.single (SetOperad.map g.2.symm (Pres.gen g.1)) 1 :=
  FreeSh.lift_gen _ hk g

variable [IsEmpty (T 0)]

/-- **Sorting the free symmetric operad**: an operation as a labelled tree, sorted. -/
noncomputable def toSh : ShuffleOperadHom R (Shuf (Lin R (FreeSet T))) (FreeSh R (SGen T)) :=
  (LT.sortHom T R).comp ((toLT T).lin R).toShuffle

variable {T}

/-- **The sorted corolla** of a relabelled generator. -/
lemma sorted_corolla {k : ℕ} (hk : 0 < k) (σ : Equiv.Perm (Fin k)) (e : T k) :
    sorted (SetOperad.map σ (LT.corolla e)) = FreeSh.genM hk (e, σ.symm) := by
  have hv : Tuple.sort (fun j => (sortTree (leaf (σ j).1 : PTree T ℕ)).first) = σ.symm := by
    refine (Tuple.eq_sort_iff.2 ⟨fun i j hij => ?_, fun i j hij h => ?_⟩).symm
    · simp only [Function.comp_apply, sortTree_leaf, STree.first_leaf, Equiv.apply_symm_apply]
      exact hij
    · simp only [sortTree_leaf, STree.first_leaf, Equiv.apply_symm_apply] at h
      exact absurd (Fin.ext h) hij.ne
  refine Subtype.ext ?_
  show sortTree (((PTree.node e fun j => PTree.leaf j).map σ).map opos) = STree.node (e, σ.symm) _
  simp only [PTree.map_node, PTree.map_leaf, opos_fin]
  rw [sortTree_node, hv]
  simp only [sortTree_leaf, Equiv.apply_symm_apply]

lemma toSh_gen {k : ℕ} (hk : 0 < k) (σ : Equiv.Perm (Fin k)) (e : T k) :
    (toSh R T).app (Fin k) (Finsupp.single (SetOperad.map σ (Pres.gen e)) 1) =
      Finsupp.single (FreeSh.genM hk (e, σ.symm)) 1 := by
  show Finsupp.mapDomain sorted (Finsupp.mapDomain ((toLT T).app (Fin k))
    (Finsupp.single (SetOperad.map σ (Pres.gen e)) (1 : R))) = _
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, (toLT T).app_map, toLT_gen,
    sorted_corolla hk]

/-- **Sorting is a left inverse of the lift.** -/
theorem toSh_comp_fromSh : (toSh R T).comp (fromSh R T) = ShuffleOperadHom.id :=
  ShuffleOperadHom.ext fun A _ _ x => FreeSh.hom_ext (fun k hk g => by
    show (toSh R T).app (Fin k) ((fromSh R T).app (Fin k) (Finsupp.single (FreeSh.genM hk g) 1))
      = Finsupp.single (FreeSh.genM hk g) 1
    rw [fromSh_gen, toSh_gen R hk, Equiv.symm_symm]) A x

/-- **Sorting is a right inverse of the lift**: the underlying shuffle operad of the free
symmetric operad is generated by the relabelled generators. -/
theorem fromSh_comp_toSh : (fromSh R T).comp (toSh R T) = ShuffleOperadHom.id :=
  Pres.shuffle_hom_ext fun n g σ => by
    show (fromSh R T).app (Fin n) ((toSh R T).app (Fin n)
      (Finsupp.single (SetOperad.map σ (Pres.gen g)) 1)) = _
    rw [toSh_gen R (pos_of_node g), fromSh_gen, Equiv.symm_symm]
    rfl

lemma toSh_fromSh (A : Type) [Fintype A] [LinearOrder A] (x : FreeSh R (SGen T) A) :
    (toSh R T).app A ((fromSh R T).app A x) = x :=
  congrArg (fun φ : ShuffleOperadHom R (FreeSh R (SGen T)) (FreeSh R (SGen T)) => φ.app A x)
    (toSh_comp_fromSh R)

lemma fromSh_toSh (A : Type) [Fintype A] [LinearOrder A] (x : Lin R (FreeSet T) A) :
    (fromSh R T).app A ((toSh R T).app A x) = x :=
  congrArg (fun φ : ShuffleOperadHom R (Shuf (Lin R (FreeSet T))) (Shuf (Lin R (FreeSet T))) =>
    φ.app A x) (fromSh_comp_toSh R)

/-- **The free symmetric operad is the free shuffle operad on the relabelled generators**, on
every finite linear order. -/
noncomputable def shuffleEquiv (A : Type) [Fintype A] [LinearOrder A] :
    Lin R (FreeSet T) A ≃ₗ[R] FreeSh R (SGen T) A :=
  LinearEquiv.ofLinear ((toSh R T).app A) ((fromSh R T).app A)
    (LinearMap.ext fun x => congrArg (fun φ : ShuffleOperadHom R (FreeSh R (SGen T))
      (FreeSh R (SGen T)) => φ.app A x) (toSh_comp_fromSh R))
    (LinearMap.ext fun x => congrArg (fun φ : ShuffleOperadHom R (Shuf (Lin R (FreeSet T)))
      (Shuf (Lin R (FreeSet T))) => φ.app A x) (fromSh_comp_toSh R))

/-- **The shuffle-tree basis of the free symmetric operad**: on a finite linear order, the
shuffle monomials with vertices the relabelled generators, through the lift. -/
noncomputable def shuffleBasis (A : Type) [Fintype A] [LinearOrder A] :
    Module.Basis (SMono (SGen T) (Finset.range (Fintype.card A))) R (Lin R (FreeSet T) A) :=
  Finsupp.basisSingleOne.map (shuffleEquiv R A).symm

theorem shuffleBasis_apply (A : Type) [Fintype A] [LinearOrder A]
    (m : SMono (SGen T) (Finset.range (Fintype.card A))) :
    shuffleBasis R A m = (fromSh R T).app A (Finsupp.single m 1) := by
  rw [shuffleBasis, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  rfl

end FreeSet

end Operad
