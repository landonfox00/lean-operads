/-
# The bar differential on trees with at most two vertices

Step (2b) of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin), continued from
`ShuffleBarSym.lean`: the comparison `ShuffleBarSym.ΦL` of the bar construction `B(T, Ī)` of
`T = FreeGrL K E`, `E` even with the basis `c` indexed by `BinGen G`, with the bar construction of
the free shuffle operad on `G` intertwines the two differentials on the trees with one or two
vertices.

* **Relabelling and splitting evaluations** (any homogeneous basis, as in step 2a): relabelling
  the leaves of a tree along a bijection relabels its evaluation (`FreeGrL.shEv_relabel`); a
  corolla whose children are leaves evaluates to a relabelled generator
  (`FreeGrL.exists_shEv_corolla`); and the evaluation of a shuffle tree is, up to the Koszul sign
  `σ(|c j| · aft(first (c j)))` and relabelling, the composite at its least leaf of the evaluation
  of the tree with the child `j` cut off and the evaluation of that child (`FreeGrL.shEv_split`).
* **Merging generators** (any graded operad and ideal): the bar differential kills a relabelled
  generator (`Bar.d_map_ι`), and the merge-composite of two relabelled odd generators is the
  relabelled merged generator `Bar.msVal` (`Bar.mc_map_ι`).
* **Composing in `T`** (`ShuffleBarSym.comp_tBasis`): two basis vectors of `T`, relabelled along
  bijections with finite sets of leaves, compose to the evaluation of the merged monomial
  `ShuffleBarSym.mergeMono`, the second monomial grafted on a leaf of the first, without sign since
  `T` is even.
* **Trees with two vertices** (`ShuffleBarSym.exists_two`): a root whose children are leaves except
  one, a vertex whose children are leaves. Its bar differential is the basis vector of the corolla
  of the merged monomial `ShuffleBarSym.twoMono` (`ShuffleBarSym.d_shEv_two`,
  `ShuffleBarSym.d_barBasisN_two`), a monomial on the leaves of the tree
  (`ShuffleBarSym.twoMono_mem`). On the side of `ShuffleBar`, the bar tree has the single cut edge
  `ShuffleBarSym.twoKey` (`ShuffleBarSym.cutKeys_toBar_two`), and merging it gives the bar tree of
  that corolla (`ShuffleBarSym.mergeK_toBar_two`, `ShuffleBarSym.toBar_corolla`). Both trees have
  sign one (`ShuffleBarSym.sign_eq_one_of_weight_le_two`).
* **The identity in degrees one and two**: for every `n`,
  `ΦL (Bar.d x) = ShuffleBar.d (ΦL x)` for `x` a basis vector of a tree with one vertex, where both
  sides vanish (`ShuffleBarSym.ΦL_d_barBasisN_of_weight_one`), or with two vertices
  (`ShuffleBarSym.ΦL_d_barBasisN_of_weight_two`), hence on `deg n 1` and `deg n 2`
  (`ShuffleBarSym.ΦL_d_of_mem_deg`).

The sign convention `ShuffleBarSym.sign` of `ShuffleBarSym.lean` is kept. A script checked it on
random trees with up to nine leaves against the expansion of the bar differential that
`Bar.d_comp` gives (checked by hand on trees with three vertices): the sum over the edges of
`(-1)^p` times the merged tree, `p` the position of the lower vertex in the preorder counted from
one, times the Koszul sign of sorting the children of the merged vertex, the odd blocks being the
subtrees with an odd number of vertices. This sign times `sign t` and the sign of the merged tree is
`(-1)` to the number of cut edges of smaller key, as in `ShuffleBar.sgn`.

On trees with three or more vertices, `ShuffleBarSymSign.lean` merges an edge at any depth as a
shuffle tree of monomials, its leaves relabelled by rank (`ShuffleBarSym.mergeT`), proves the sign
identity above (`ShuffleBarSym.sign_mergeT`), and derives `ΦL ∘ Bar.d = ShuffleBar.d ∘ ΦL` from the
expansion of `Bar.d` over the edges (`ShuffleBarSym.ΦL_d_of_expansion`), and `ShuffleBarSymExp.lean`
proves the expansion on every tree (`ShuffleBarSym.dExpansion`, `ShuffleBarSym.ΦL_d`).
-/
import Operad.ShuffleBarSym

universe u v w

namespace Operad

open Function Sym GerBV GrComposite STree

namespace FreeGrL

variable {R : Type u} [CommRing R]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {B : ℕ → Type w} (b : ∀ k, Module.Basis (B k) R (W (Fin k)))

/-- **Relabelling the leaves of a tree** relabels its evaluation. -/
theorem shEv_relabel (f : ℕ → ℕ) : ∀ (t : STree B) (Y : Finset ℕ) (h : t.labels = Y.val)
    (Y' : Finset ℕ) (h' : (t.relabel f).labels = Y'.val) (e : Lab Y ≃ Lab Y')
    (_ : ∀ x, (e x).1 = f x.1),
    shEv b (t.relabel f) Y' h' = GrOperad.map (R := R) e (shEv b t Y h)
  | .leaf a, Y, h, Y', h', e, _ => by
    show shEv b (.leaf (f a)) Y' h' = _
    rw [shEv_leaf, shEv_leaf, map_unitL]
  | .node (k := k) β c, Y, h, Y', h', e, he => by
    have h'' : (STree.node β fun j => (c j).relabel f).labels = Y'.val := h'
    show shEv b (.node β fun j => (c j).relabel f) Y' h'' = _
    have hown : own h ∘ e.symm = own h'' := by
      funext s'
      refine (own_eq h'' ?_).symm
      have hs := mem_own h (e.symm s')
      have : f (e.symm s').1 = s'.1 := by rw [← he, Equiv.apply_symm_apply]
      rw [← this, labels_relabel]
      exact Multiset.mem_map_of_mem f hs
    rw [shEv_node, shEv_node, ← graft_map, map_mk_ownGen, mk_ownGen_congr _ _ hown]
    congr 3
    funext j
    let ej : Lab (cLab c j) ≃ Lab (cLab (fun j => (c j).relabel f) j) :=
      (childEquiv h j).trans ((fibMap e (own h) j).trans
        ((Equiv.subtypeEquivRight fun s => by rw [hown]).trans (childEquiv h'' j).symm))
    have hej : ∀ x, (ej x).1 = f x.1 := fun x => he _
    rw [shEv_relabel f (c j) (cLab c j) (labels_child h j) _ (labels_child h'' j) ej hej]
    simp only [GrOperad.toGrSpecies_map, ← GrOperad.map_trans]
    apply gmap_congr
    intro x
    simp only [ej, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- **A corolla** whose leaves are given by a function: its evaluation is a relabelled generator. -/
theorem exists_shEv_corolla {k : ℕ} (β : B k) (c : Fin k → STree B) (Y : Finset ℕ)
    (h : (STree.node β c).labels = Y.val) (hall : ∀ j, ∃ a, c j = .leaf a) :
    ∃ θ : Fin k ≃ Lab Y, (∀ j, c j = .leaf (θ j).1) ∧
      shEv b (.node β c) Y h = GrOperad.map (R := R) θ ((ι R W).app (Fin k) (b k β)) := by
  choose a ha using hall
  have hnd : (STree.node β c).labels.Nodup := h ▸ Y.nodup
  have hmem : ∀ j, a j ∈ Y := fun j => by
    rw [← Finset.mem_val, ← h]
    exact mem_labels_node.2 ⟨j, by rw [ha j]; simp⟩
  have hinj : Injective a := fun i j hij => by
    by_contra hne
    have := disjoint_of_node hnd hne
    rw [ha i, ha j, hij] at this
    simp at this
  have hsurj : ∀ y : Lab Y, ∃ j, a j = y.1 := fun y => by
    have hy : y.1 ∈ (STree.node β c).labels := by rw [h]; exact y.2
    obtain ⟨j, hj⟩ := mem_labels_node.1 hy
    rw [ha j] at hj
    exact ⟨j, (Multiset.mem_singleton.1 hj).symm⟩
  let θ : Fin k ≃ Lab Y := Equiv.ofBijective (fun j => ⟨a j, hmem j⟩)
    ⟨fun i j hij => hinj (congrArg Subtype.val hij), fun y => by
      obtain ⟨j, hj⟩ := hsurj y
      exact ⟨j, Subtype.ext hj⟩⟩
  have hc : c = fun j => STree.leaf (θ j).1 := funext fun j => ha j
  refine ⟨θ, fun j => congrFun hc j, ?_⟩
  subst hc
  exact shEv_corolla b β Y θ h

variable {p : ∀ k, B k → Bool}
  (hb : ∀ k (β : B k), GrSpecies.par (R := R) (p k β) (b k β) = b k β)
include hb

/-- **Splitting off a child**: the evaluation of a shuffle tree is, up to the Koszul sign and
relabelling, the evaluation of the tree with the child `j` cut off at its least leaf, composed at
that leaf with the evaluation of the child. -/
theorem shEv_split {k : ℕ} (β : B k) (c : Fin k → STree B) (ht : (STree.node β c).IsShuffle)
    (Y : Finset ℕ) (h : (STree.node β c).labels = Y.val) (j : Fin k) :
    ∃ (Y₁ Y₂ : Finset ℕ) (h₁ : (STree.node β (update c j (.leaf (c j).first))).labels = Y₁.val)
      (h₂ : (c j).labels = Y₂.val) (hm : (c j).first ∈ Y₁)
      (E : Lab Y ≃ Without (Lab Y₁) ⟨(c j).first, hm⟩ ⊕ Lab Y₂), (∀ x, sval (E x) = x.1) ∧
      GrOperad.comp (R := R) (⟨(c j).first, hm⟩ : Lab Y₁)
          (shEv b (.node β (update c j (.leaf (c j).first))) Y₁ h₁) (shEv b (c j) Y₂ h₂)
        = σ R (vpar p (c j) && vaft p (.node β (update c j (.leaf (c j).first))) (c j).first)
          • GrOperad.map (R := R) E (shEv b (.node β c) Y h) := by
  have hnd : (STree.node β c).labels.Nodup := h ▸ Y.nodup
  set t₂ := c j with ht₂
  set m := t₂.first with hm_def
  have hjs : t₂.IsShuffle := ht.child j
  have hmj : m ∈ t₂.labels := first_mem hjs
  let c₁ : Fin k → STree B := update c j (.leaf m)
  let t₁ : STree B := .node β c₁
  have hle : t₁.labels ≤ (STree.node β c).labels := by
    simp only [t₁, labels_node]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hij : i = j
    · subst hij
      simp only [c₁, update_self, labels_leaf]
      exact Multiset.singleton_le.2 hmj
    · simp only [c₁, update_of_ne hij]
      exact le_rfl
  have hnd₁ : t₁.labels.Nodup := Multiset.nodup_of_le hle hnd
  have hnd₂ : t₂.labels.Nodup := nodup_of_node hnd j
  set Y₁ := t₁.labels.toFinset
  set Y₂ := t₂.labels.toFinset
  have h₁ : t₁.labels = Y₁.val := labels_eq_toFinset hnd₁
  have h₂ : t₂.labels = Y₂.val := labels_eq_toFinset hnd₂
  have hm₁ : m ∈ Y₁ := Multiset.mem_toFinset.2
    (mem_labels_node.2 ⟨j, by simp [c₁]⟩)
  have hother : ∀ i, i ≠ j → ∀ x ∈ (c i).labels, x ∉ t₂.labels := fun i hij x hx hx' =>
    Multiset.disjoint_left.1 (disjoint_of_node hnd hij) hx hx'
  have hsub : t₁.subst (update STree.leaf m t₂) = STree.node β c := by
    simp only [t₁, subst_node]
    congr 1
    funext i
    by_cases hij : i = j
    · subst hij
      simp [c₁, ht₂]
    · simp only [c₁, update_of_ne hij]
      rw [subst_congr (ys := STree.leaf) (c i) fun x hx => update_of_ne
        (fun hxm => hother i hij x hx (by rw [hxm]; exact hmj)) _ _, subst_leaf]
  have hY : ∀ x, x ∈ Y ↔ (x ∈ Y₁ ∧ x ≠ m) ∨ x ∈ Y₂ := fun x => by
    rw [← Finset.mem_val, ← h, ← hsub, labels_subst, h₁]
    simp only [Multiset.mem_bind, Finset.mem_val]
    constructor
    · rintro ⟨y, hy, hxy⟩
      by_cases hym : y = m
      · subst hym
        rw [update_self] at hxy
        exact Or.inr (Multiset.mem_toFinset.2 hxy)
      · rw [update_of_ne hym, labels_leaf, Multiset.mem_singleton] at hxy
        subst hxy
        exact Or.inl ⟨hy, hym⟩
    · rintro (⟨hx, hxm⟩ | hx)
      · exact ⟨x, hx, by rw [update_of_ne hxm]; simp⟩
      · exact ⟨m, hm₁, by rw [update_self]; exact Multiset.mem_toFinset.1 hx⟩
  have hd : ∀ x ∈ Y₁, x ≠ m → x ∉ Y₂ := fun x hx hxm hx₂ => by
    obtain ⟨i, hi⟩ := mem_labels_node.1 (Multiset.mem_toFinset.1 hx)
    by_cases hij : i = j
    · subst hij
      simp [c₁] at hi
      exact hxm hi
    · simp only [c₁, update_of_ne hij] at hi
      exact hother i hij x hi (Multiset.mem_toFinset.1 hx₂)
  have hh : (t₁.subst (update STree.leaf m t₂)).labels = Y.val := by rw [hsub, h]
  let E := labSplit hm₁ hY hd
  have hcomp := comp_shEv b hb t₂ Y₂ h₂ t₁ Y₁ h₁ m hm₁ Y hh E (sval_labSplit hm₁ hY hd)
  have hev := map_shEv b hsub rfl hh h (Equiv.refl _) fun _ => rfl
  rw [GrOperad.map_refl] at hev
  rw [hev] at hcomp
  exact ⟨Y₁, Y₂, h₁, h₂, hm₁, E, sval_labSplit hm₁ hY hd, hcomp⟩

end FreeGrL

namespace Bar

open FreeGr

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (I : GrOperadIdeal R P)

/-- **The bar differential kills a relabelled generator.** -/
lemma d_map_ι {k : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (θ : Fin k ≃ Y)
    (g : BarGen I (Fin k)) :
    d I Y (GrOperad.map (R := R) θ ((FreeGrL.ι R (BarGen I)).app (Fin k) g)) = 0 := by
  rw [d_map, d_ι, map_zero]

lemma mergeSp_fn_eq {k l : ℕ} (g₁ : GrGen R (BarGen I) k) (g₂ : GrGen R (BarGen I) l)
    (q : Fin k) (N : ℕ) (hN : N + 1 = k + l) :
    (mergeSp I).fn k l g₁ q g₂ N
      = ⟨(msVal I g₁.1.2 g₁.1.1 q g₂.1.1 N hN, !(xor g₁.1.2 g₂.1.2)),
          (mergeSp I).par _ _ _ _ _ _ _ g₁.2 g₂.2⟩ :=
  Subtype.ext (Prod.ext ((mergeSp I).fn_val g₁ g₂ ⟨q.2, hN⟩) ((mergeSp I).fn_par g₁ g₂))

/-- **Merging two relabelled odd generators** gives the relabelled merged generator. -/
theorem mc_map_ι {k l : ℕ} {Y₁ Y₂ : Type} [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂]
    [DecidableEq Y₂] (θ₁ : Fin k ≃ Y₁) (θ₂ : Fin l ≃ Y₂) (q : Fin k) (g₁ : BarGen I (Fin k))
    (g₂ : BarGen I (Fin l)) (hg₁ : GrSpecies.par (R := R) true g₁ = g₁)
    (hg₂ : GrSpecies.par (R := R) true g₂ = g₂) (N : ℕ) (hN : N + 1 = k + l) :
    (mergeSp I).mc (θ₁ q) (GrOperad.map (R := R) θ₁ ((FreeGrL.ι R (BarGen I)).app (Fin k) g₁))
        (GrOperad.map (R := R) θ₂ ((FreeGrL.ι R (BarGen I)).app (Fin l) g₂))
      = GrOperad.map (R := R) ((posEquivF q l N hN).symm.trans (compEquiv θ₁ θ₂ q))
          ((FreeGrL.ι R (BarGen I)).app (Fin N) (msVal I true g₁ q g₂ N hN)) := by
  rw [MergeSp.mc_map, FreeGrL.ι_app_hom hg₁, FreeGrL.ι_app_hom hg₂]
  erw [MergeSp.mc_gen (mergeSp I) ⟨(g₁, true), hg₁⟩ q ⟨(g₂, true), hg₂⟩ N hN]
  rw [mergeSp_fn_eq, GrOperad.map_trans]
  congr 2
  exact (FreeGrL.ι_app_hom _).symm

end Bar

namespace STree

/-- **A corolla has no vertices after a leaf.** -/
lemma vaft_corolla {B : ℕ → Type w} (p : ∀ k, B k → Bool) {k : ℕ} (β : B k)
    (c : Fin k → STree B) (hall : ∀ j, ∃ a, c j = .leaf a) (m : ℕ) :
    vaft p (.node β c) m = false := by
  rw [vaft_node, GrEnd.tot]
  rw [Finset.sum_eq_zero fun j _ => by obtain ⟨a, ha⟩ := hall j; simp [ha]]
  rfl

end STree

namespace LTree

lemma toBinSTree_plug {G : Type*} (ins : ℕ → LTree G) : ∀ m : LTree G,
    toBinSTree (m.plug ins) = (toBinSTree m).subst fun a => toBinSTree (ins a)
  | leaf _ => rfl
  | node e l r => by
    simp only [plug, toBinSTree, STree.subst_node]
    congr 1
    funext i
    fin_cases i
    · exact toBinSTree_plug ins l
    · exact toBinSTree_plug ins r

end LTree

namespace ShuffleBarSym

open LTree

section CompT

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- **The merged monomial**: the monomial `m₂`, its leaves relabelled by `f₂`, grafted on the leaf
`q` of the monomial `m₁`, the other leaves of `m₁` relabelled by `f₁`. -/
def mergeMono (m₁ : LTree G) (q : ℕ) (m₂ : LTree G) (f₁ f₂ : ℕ → ℕ) : LTree G :=
  m₁.plug fun a => if a = q then m₂.plug (fun i => LTree.leaf (f₂ i)) else LTree.leaf (f₁ a)

omit [Fintype G] [DecidableEq G] in
/-- The values of a bijection between finite sets of natural numbers. -/
lemma val_map_of_equiv {Y Y' : Finset ℕ} {f : ℕ → ℕ} (e : Lab Y ≃ Lab Y')
    (he : ∀ x, (e x).1 = f x.1) : Y.val.map f = Y'.val := by
  have hinj : ∀ x ∈ Y.val, ∀ y ∈ Y.val, f x = f y → x = y := fun x hx y hy hxy => by
    have : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext (by rw [he, he]; exact hxy)
    exact congrArg Subtype.val (e.injective this)
  refine (Multiset.Nodup.ext (Multiset.Nodup.map_on hinj Y.nodup) Y'.nodup).2 fun x => ?_
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← he ⟨y, hy⟩]
    exact (e ⟨y, hy⟩).2
  · intro hx
    exact ⟨(e.symm ⟨x, hx⟩).1, (e.symm ⟨x, hx⟩).2, by rw [← he, Equiv.apply_symm_apply]⟩

lemma labels_toBinSTree_mono {k : ℕ} (m : LTree G)
    (hm : m ∈ LTree.monomials (Fintype.card (Fin k))) :
    (toBinSTree m).labels = (Finset.range (Fintype.card (Fin k))).val :=
  (binMonoEquiv _ ⟨m, hm⟩).2.2

lemma val_symm_posEquiv {k : ℕ} (x : Lab (Finset.range (Fintype.card (Fin k)))) :
    ((FreeGrL.posEquiv (Fin k)).symm x : ℕ) = x.1 := by
  conv_rhs => rw [← (FreeGrL.posEquiv (Fin k)).apply_symm_apply x]
  rw [FreeGrL.posEquiv_apply, opos_fin]

lemma labels_relabel_mono {k : ℕ} (m : LTree G) (hm : m ∈ LTree.monomials (Fintype.card (Fin k)))
    {Y : Finset ℕ} (θ : Fin k ≃ Lab Y) (f : ℕ → ℕ) (hf : ∀ j : Fin k, (θ j).1 = f j) :
    ((toBinSTree m).relabel f).labels = Y.val := by
  rw [STree.labels_relabel, labels_toBinSTree_mono m hm]
  exact val_map_of_equiv ((FreeGrL.posEquiv (Fin k)).symm.trans θ) fun x => by
    rw [Equiv.trans_apply, hf, val_symm_posEquiv]

/-- **A relabelled basis vector** of the free graded operad is the evaluation of the relabelled
tree. -/
lemma map_tBasis {k : ℕ} (m : LTree G) (hm : m ∈ LTree.monomials (Fintype.card (Fin k)))
    {Y : Finset ℕ} (θ : Fin k ≃ Lab Y) (f : ℕ → ℕ) (hf : ∀ j : Fin k, (θ j).1 = f j)
    (h : ((toBinSTree m).relabel f).labels = Y.val) :
    GrOperad.map (R := K) θ (tBasis c hc (Fin k) ⟨m, hm⟩)
      = FreeGrL.shEv c ((toBinSTree m).relabel f) Y h := by
  rw [tBasis_apply, FreeGrL.shuffleBasis_apply, ← GrOperad.map_trans]
  refine (FreeGrL.shEv_relabel c f _ _ _ Y h _ fun x => ?_).symm
  rw [Equiv.trans_apply, hf, val_symm_posEquiv]

/-- **Composing two basis vectors** of the free graded operad on even binary generators, relabelled
along bijections with finite sets: the evaluation of the merged monomial, without sign. -/
theorem comp_tBasis {k l : ℕ} (m₁ : LTree G) (hm₁ : m₁ ∈ LTree.monomials (Fintype.card (Fin k)))
    (m₂ : LTree G) (hm₂ : m₂ ∈ LTree.monomials (Fintype.card (Fin l))) {Y₁ Y₂ Y : Finset ℕ}
    (θ₁ : Fin k ≃ Lab Y₁) (θ₂ : Fin l ≃ Lab Y₂) (f₁ f₂ : ℕ → ℕ)
    (hf₁ : ∀ j : Fin k, (θ₁ j).1 = f₁ j) (hf₂ : ∀ i : Fin l, (θ₂ i).1 = f₂ i) (q : Fin k)
    (hY : (toBinSTree (mergeMono m₁ q m₂ f₁ f₂)).labels = Y.val)
    (E' : Lab Y ≃ Without (Lab Y₁) (θ₁ q) ⊕ Lab Y₂) (hE : ∀ x, FreeGrL.sval (E' x) = x.1) :
    GrOperad.comp (R := K) (θ₁ q) (GrOperad.map (R := K) θ₁ (tBasis c hc (Fin k) ⟨m₁, hm₁⟩))
        (GrOperad.map (R := K) θ₂ (tBasis c hc (Fin l) ⟨m₂, hm₂⟩))
      = GrOperad.map (R := K) E'
          (FreeGrL.shEv c (toBinSTree (mergeMono m₁ q m₂ f₁ f₂)) Y hY) := by
  have h₁ := labels_relabel_mono m₁ hm₁ θ₁ f₁ hf₁
  have h₂ := labels_relabel_mono m₂ hm₂ θ₂ f₂ hf₂
  rw [map_tBasis c hc m₁ hm₁ θ₁ f₁ hf₁ h₁, map_tBasis c hc m₂ hm₂ θ₂ f₂ hf₂ h₂]
  have hlt : ∀ a ∈ (toBinSTree m₁).labels, a < k := fun a ha => by
    rw [labels_toBinSTree_mono m₁ hm₁, Finset.mem_val, Finset.mem_range,
      Fintype.card_fin] at ha
    exact ha
  have hsub : ((toBinSTree m₁).relabel f₁).subst
      (Function.update STree.leaf (θ₁ q).1 ((toBinSTree m₂).relabel f₂))
        = toBinSTree (mergeMono m₁ q m₂ f₁ f₂) := by
    rw [mergeMono, toBinSTree_plug, STree.relabel, STree.subst_subst]
    refine STree.subst_congr _ fun a ha => ?_
    rw [STree.subst_leaf']
    by_cases haq : a = q
    · rw [if_pos haq, haq, ← hf₁ q, Function.update_self, toBinSTree_plug]
      rfl
    · rw [if_neg haq]
      have hne : f₁ a ≠ (θ₁ q).1 := fun h' => by
        have h'' : θ₁ ⟨a, hlt a ha⟩ = θ₁ q := Subtype.ext (by rw [hf₁]; exact h')
        exact haq (congrArg Fin.val (θ₁.injective h''))
      rw [Function.update_of_ne hne]
      rfl
  have hY' : (((toBinSTree m₁).relabel f₁).subst
      (Function.update STree.leaf (θ₁ q).1 ((toBinSTree m₂).relabel f₂))).labels = Y.val := by
    rw [hsub]
    exact hY
  have := FreeGrL.comp_shEv c (p := fun _ _ => false) hc ((toBinSTree m₂).relabel f₂) Y₂ h₂
    ((toBinSTree m₁).relabel f₁) Y₁ h₁ (θ₁ q).1 (θ₁ q).2 Y hY' E' hE
  rw [vpar_false, Bool.false_and, σ_false, one_smul] at this
  rw [this, ← FreeGrL.map_shEv c hsub rfl hY' hY (Equiv.refl _) fun _ => rfl, GrOperad.map_refl]

end CompT

section Two

open STree

variable {K : Type u} [CommRing K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- The least leaves of the children of a vertex, as a function of the positions. -/
def firstFn {B : ℕ → Type*} {k : ℕ} (ch : Fin k → STree B) (a : ℕ) : ℕ :=
  if h : a < k then (ch ⟨a, h⟩).first else 0

omit [Fintype G] [DecidableEq G] in
lemma firstFn_fin {B : ℕ → Type*} {k : ℕ} (ch : Fin k → STree B) (j : Fin k) :
    firstFn ch j = (ch j).first := by
  rw [firstFn, dif_pos j.2]

/-- **The merged monomial of a tree with two vertices**: the monomial of the child `j₀` grafted on
the leaf `j₀` of the monomial of the root, all leaves named by the leaves of the tree. -/
def twoMono {k l : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j₀ : Fin k)
    (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)) : LTree G :=
  mergeMono m₁.1 j₀ m₂.1 (firstFn ch) (firstFn c₂)

/-- The merge step of `d_shEv_two`, for a composite of two relabelled generators at a variable
input. -/
lemma d_eq_of_comp_two {k l N : ℕ} {Y₁ Y₂ : Finset ℕ} (m₁ : VMono G k) (m₂ : VMono G l)
    (θ₁ : Fin k ≃ Lab Y₁) (θ₂ : Fin l ≃ Lab Y₂) (j₀ : Fin k) (i : Lab Y₁) (hq : θ₁ j₀ = i)
    (f₁ f₂ : ℕ → ℕ) (hf₁ : ∀ j : Fin k, (θ₁ j).1 = f₁ j) (hf₂ : ∀ i : Fin l, (θ₂ i).1 = f₂ i)
    (hN : N + 1 = k + l) (hM : mergeMono m₁.1 j₀ m₂.1 f₁ f₂ ∈ LTree.monomials N ∧ 2 ≤ N)
    (X : FreeGrL K (BarGen (Ibar K E c hc)) (Lab (Finset.range (Fintype.card (Fin N)))))
    (E' : Lab (Finset.range (Fintype.card (Fin N))) ≃ Without (Lab Y₁) i ⊕ Lab Y₂)
    (hE : ∀ x, FreeGrL.sval (E' x) = x.1)
    (hcomp : GrOperad.comp (R := K) i
        (GrOperad.map (R := K) θ₁ ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin k)
          (genBasis c hc k m₁)))
        (GrOperad.map (R := K) θ₂ ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin l)
          (genBasis c hc l m₂)))
      = GrOperad.map (R := K) E' X) :
    Bar.d (Ibar K E c hc) _ X = GrOperad.map (R := K) (FreeGrL.posEquiv (Fin N))
      ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin N) (genBasis c hc N ⟨_, hM⟩)) := by
  subst hq
  have hA := Bar.d_map_ι (Ibar K E c hc) θ₁ (genBasis c hc k m₁)
  have hA' := Bar.d_map_ι (Ibar K E c hc) θ₂ (genBasis c hc l m₂)
  have hd := Bar.d_comp (Ibar K E c hc) (θ₁ j₀)
    (GrOperad.map (R := K) θ₁ ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin k)
      (genBasis c hc k m₁)))
    (GrOperad.map (R := K) θ₂ ((FreeGrL.ι K (BarGen (Ibar K E c hc))).app (Fin l)
      (genBasis c hc l m₂)))
  have hdm := Bar.d_map (I := Ibar K E c hc) E' X
  have hmc := Bar.mc_map_ι _ θ₁ θ₂ j₀ (genBasis c hc k m₁) (genBasis c hc l m₂)
    (par_genBasis c hc k m₁) (par_genBasis c hc l m₂) N hN
  simp only [hcomp, hdm, hA, hA', hmc, map_zero, LinearMap.zero_apply, zero_add] at hd
  have hY : (toBinSTree (mergeMono m₁.1 j₀ m₂.1 f₁ f₂)).labels
      = (Finset.range (Fintype.card (Fin N))).val :=
    labels_toBinSTree_mono _ (by rw [Fintype.card_fin]; exact hM.1)
  have hB := comp_tBasis c hc m₁.1 (by simpa using m₁.2.1) m₂.1 (by simpa using m₂.2.1) θ₁ θ₂
    f₁ f₂ hf₁ hf₂ j₀ hY E' hE
  have hmerge : Bar.msVal (Ibar K E c hc) true (genBasis c hc k m₁) j₀ (genBasis c hc l m₂) N hN
      = SymSpecies.map (R := K) ((FreeGrL.posEquiv (Fin N)).trans (E'.trans
          ((compEquiv θ₁ θ₂ j₀).symm.trans (posEquivF j₀ l N hN)))) (genBasis c hc N ⟨_, hM⟩) := by
    refine IdealSp.ext _ ?_
    rw [Bar.val_msVal]
    show _ = GrOperad.map (R := K) _ (idealBasis c hc N ⟨_, hM⟩ : FreeGrL K E (Fin N))
    rw [Bool.not_true, σ_false, one_smul]
    show GrOperad.map (R := K) _ (GrOperad.comp (R := K) j₀
      (idealBasis c hc k m₁ : FreeGrL K E (Fin k)) (idealBasis c hc l m₂ : FreeGrL K E (Fin l)))
      = _
    rw [idealBasis_apply, idealBasis_apply, idealBasis_apply, tBasis_apply c hc (Fin N),
      FreeGrL.shuffleBasis_apply]
    have hc' := GrOperad.map_comp (R := K) (P := FreeGrL K E) θ₁ θ₂ j₀
      (tBasis c hc (Fin k) ⟨m₁.1, by simpa using m₁.2.1⟩)
      (tBasis c hc (Fin l) ⟨m₂.1, by simpa using m₂.2.1⟩)
    rw [hB] at hc'
    have hc'' := congrArg (GrOperad.map (R := K) (compEquiv θ₁ θ₂ j₀).symm) hc'
    rw [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl] at hc''
    rw [hc'', ← GrOperad.map_trans, ← GrOperad.map_trans, ← GrOperad.map_trans]
    apply gmap_congr
    intro x
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  have happ := (FreeGrL.ι K (BarGen (Ibar K E c hc))).app_map ((FreeGrL.posEquiv (Fin N)).trans
    (E'.trans ((compEquiv θ₁ θ₂ j₀).symm.trans (posEquivF j₀ l N hN)))) (genBasis c hc N ⟨_, hM⟩)
  simp only [hmerge, happ] at hd
  have hd' := congrArg (GrOperad.map (R := K) E'.symm) hd
  simp only [GrOperad.toGrSpecies_map, ← GrOperad.map_trans, Equiv.self_trans_symm,
    GrOperad.map_refl] at hd'
  refine hd'.trans (gmap_congr (fun x => ?_) _)
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- **The bar differential of a tree with two vertices**: the evaluation of the corolla of the
merged monomial, without sign. -/
theorem d_shEv_two {k l N : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j₀ : Fin k)
    (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)) (hj₀ : ch j₀ = .node m₂ c₂)
    (hl₁ : ∀ j, j ≠ j₀ → ∃ a, ch j = .leaf a) (hl₂ : ∀ i, ∃ a, c₂ i = .leaf a)
    (ht : (STree.node m₁ ch).IsShuffle)
    (h : (STree.node m₁ ch).labels = (Finset.range (Fintype.card (Fin N))).val)
    (hM : twoMono m₁ ch j₀ m₂ c₂ ∈ LTree.monomials N ∧ 2 ≤ N)
    (h' : (STree.node (⟨_, hM⟩ : VMono G N) fun j : Fin N => .leaf j.1).labels
      = (Finset.range (Fintype.card (Fin N))).val) :
    Bar.d (Ibar K E c hc) _ (FreeGrL.shEv (genBasis c hc) (.node m₁ ch) _ h)
      = FreeGrL.shEv (genBasis c hc) (.node (⟨_, hM⟩ : VMono G N) fun j : Fin N => .leaf j.1)
          _ h' := by
  obtain ⟨Y₁, Y₂, h₁, h₂, hm, E', hE, hcomp⟩ :=
    FreeGrL.shEv_split (genBasis c hc) (par_genBasis c hc) m₁ ch ht _ h j₀
  have hall₁ : ∀ j, ∃ a, Function.update ch j₀ (.leaf (ch j₀).first) j = .leaf a := fun j => by
    by_cases hj : j = j₀
    · subst hj
      exact ⟨_, Function.update_self _ _ _⟩
    · rw [Function.update_of_ne hj]
      exact hl₁ j hj
  have hv : STree.vaft (fun _ _ => true) (STree.node m₁ (Function.update ch j₀
      (.leaf (ch j₀).first))) (ch j₀).first = false := STree.vaft_corolla _ _ _ hall₁ _
  simp only [hv, Bool.and_false, σ_false, one_smul] at hcomp
  obtain ⟨θ₁, hθ₁, hev₁⟩ := FreeGrL.exists_shEv_corolla (genBasis c hc) m₁ _ Y₁ h₁ hall₁
  have h₂' : (STree.node m₂ c₂).labels = Y₂.val := hj₀ ▸ h₂
  obtain ⟨θ₂, hθ₂, hev₂⟩ := FreeGrL.exists_shEv_corolla (genBasis c hc) m₂ c₂ Y₂ h₂' hl₂
  have hev₂' : FreeGrL.shEv (genBasis c hc) (ch j₀) Y₂ h₂
      = FreeGrL.shEv (genBasis c hc) (.node m₂ c₂) Y₂ h₂' := by
    have := FreeGrL.map_shEv (genBasis c hc) hj₀ rfl h₂ h₂' (Equiv.refl _) fun _ => rfl
    rwa [GrOperad.map_refl] at this
  replace hcomp := (congrArg₂ (fun x y => GrOperad.comp (R := K) (⟨(ch j₀).first, hm⟩ : Lab Y₁) x y)
    hev₁ (hev₂'.trans hev₂)).symm.trans hcomp
  have hq : θ₁ j₀ = ⟨(ch j₀).first, hm⟩ := Subtype.ext (by
    have := hθ₁ j₀
    rw [Function.update_self] at this
    exact (STree.leaf.inj this).symm)
  have hf₁ : ∀ j : Fin k, (θ₁ j).1 = firstFn ch j := fun j => by
    rw [firstFn_fin]
    by_cases hj : j = j₀
    · subst hj
      rw [hq]
    · have := hθ₁ j
      rw [Function.update_of_ne hj] at this
      rw [this]
      rfl
  have hf₂ : ∀ i : Fin l, (θ₂ i).1 = firstFn c₂ i := fun i => by
    rw [firstFn_fin, hθ₂ i]
    rfl
  have hN : N + 1 = k + l := by
    have h1 := Fintype.card_congr E'
    rw [Fintype.card_sum, Reg.card_without, ← Fintype.card_congr θ₁,
      ← Fintype.card_congr θ₂] at h1
    simp only [Fintype.card_coe, Finset.card_range, Fintype.card_fin] at h1
    have := j₀.pos
    omega
  refine (d_eq_of_comp_two c hc m₁ m₂ θ₁ θ₂ j₀ _ hq (firstFn ch) (firstFn c₂) hf₁ hf₂ hN hM _ E'
    hE hcomp).trans ?_
  have hπ : (fun j : Fin N => STree.leaf (FreeGrL.posEquiv (Fin N) j).1)
      = fun j : Fin N => (STree.leaf j.1 : STree (VMono G)) :=
    funext fun j => by rw [FreeGrL.posEquiv_apply, opos_fin]
  have h'' : (STree.node (E := VMono G) (k := N) ⟨_, hM⟩
      fun j : Fin N => STree.leaf (FreeGrL.posEquiv (Fin N) j).1).labels
        = (Finset.range (Fintype.card (Fin N))).val := by rw [hπ]; exact h'
  have e1 := FreeGrL.shEv_corolla (genBasis c hc) (⟨_, hM⟩ : VMono G N) _
    (FreeGrL.posEquiv (Fin N)) h''
  have e2 := FreeGrL.map_shEv (genBasis c hc) (congrArg (STree.node _) hπ) rfl h'' h'
    (Equiv.refl _) fun _ => rfl
  exact e1.symm.trans ((GrOperad.map_refl _).symm.trans e2)

end Two

/-! ## Trees with two vertices -/

section TwoTrees

open ShuffleBar STree

variable {G : Type} [Fintype G] [DecidableEq G]

lemma length_preKeys {B : ℕ → Type*} : ∀ t : STree B, (preKeys t).length = t.weight
  | .leaf _ => rfl
  | .node _ ch => by
    simp only [preKeys, List.length_cons, List.length_flatten, List.map_ofFn, List.sum_ofFn,
      STree.weight, Function.comp_def, length_preKeys]
    omega

lemma inv_eq_zero_of_length_le_one {α : Type*} [LinearOrder α] :
    ∀ {l : List α}, l.length ≤ 1 → inv l = 0
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => by simp at h

/-- **The sign of a tree with at most two vertices** is one. -/
lemma sign_eq_one_of_weight_le_two (K : Type u) [CommRing K] {B : ℕ → Type*} (t : STree B)
    (h : t.weight ≤ 2) : sign K t = 1 := by
  rw [sign, inv_eq_zero_of_length_le_one, pow_zero]
  rw [List.length_tail, length_preKeys]
  omega

omit [Fintype G] [DecidableEq G] in
lemma exists_leaf_of_weight_eq_zero {B : ℕ → Type*} :
    ∀ {t : STree B}, t.weight = 0 → ∃ a, t = .leaf a
  | .leaf a, _ => ⟨a, rfl⟩
  | .node _ _, h => by simp [STree.weight] at h

omit [Fintype G] [DecidableEq G] in
lemma exists_corolla_of_weight_eq_one {B : ℕ → Type*} :
    ∀ {t : STree B}, t.weight = 1 → ∃ (l : ℕ) (m : B l) (c : Fin l → STree B),
      t = .node m c ∧ ∀ i, ∃ a, c i = .leaf a
  | .leaf _, h => by simp [STree.weight] at h
  | .node m c, h => by
    simp only [STree.weight, add_eq_left, Finset.sum_eq_zero_iff, Finset.mem_univ,
      true_implies] at h
    exact ⟨_, m, c, rfl, fun i => exists_leaf_of_weight_eq_zero (h i)⟩

omit [Fintype G] [DecidableEq G] in
/-- **The shape of a tree with two vertices**: a root with one child that is a vertex, all of
whose children are leaves, the other children of the root being leaves. -/
lemma exists_two {B : ℕ → Type*} : ∀ {t : STree B}, t.weight = 2 →
    ∃ (k : ℕ) (m₁ : B k) (ch : Fin k → STree B) (j₀ : Fin k) (l : ℕ) (m₂ : B l)
      (c₂ : Fin l → STree B), t = .node m₁ ch ∧ ch j₀ = .node m₂ c₂ ∧
        (∀ j, j ≠ j₀ → ∃ a, ch j = .leaf a) ∧ ∀ i, ∃ a, c₂ i = .leaf a
  | .leaf _, h => by simp [STree.weight] at h
  | .node (k := k) m₁ ch, h => by
    have hs : ∑ j, (ch j).weight = 1 := by
      simp only [STree.weight] at h
      omega
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, (ch j₀).weight ≠ 0 := by
      by_contra hne
      push Not at hne
      rw [Finset.sum_eq_zero fun j _ => hne j] at hs
      exact zero_ne_one hs
    have hle : (ch j₀).weight ≤ 1 := by
      have := Finset.single_le_sum (f := fun j => (ch j).weight) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ j₀)
      rw [hs] at this
      exact this
    have h1 : (ch j₀).weight = 1 := by omega
    have hrest : ∑ j ∈ Finset.univ.erase j₀, (ch j).weight = 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), h1] at hs
      omega
    obtain ⟨l, m₂, c₂, hc, hl⟩ := exists_corolla_of_weight_eq_one h1
    refine ⟨k, m₁, ch, j₀, l, m₂, c₂, rfl, hc, fun j hj => ?_, hl⟩
    exact exists_leaf_of_weight_eq_zero
      ((Finset.sum_eq_zero_iff.1 hrest) j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩))

omit [Fintype G] [DecidableEq G] in
lemma liftW_false_eq (x : LTree G) : liftW false x = unflag x := by
  cases x <;> rfl

omit [Fintype G] [DecidableEq G] in
lemma liftW_false_plug (m : LTree G) (ins : ℕ → LTree G) :
    liftW false (m.plug ins) = (liftW false m).plug fun a => liftW false (ins a) := by
  simp only [liftW_false_eq]
  exact (plug_mapDec _ ins m).symm

omit [Fintype G] [DecidableEq G] in
lemma plug_leaf_eq {X : Type*} : ∀ t : LTree X, t.plug LTree.leaf = t
  | LTree.leaf _ => rfl
  | LTree.node e l r => by rw [plug, plug_leaf_eq l, plug_leaf_eq r]

/-- **The bar tree of a corolla** is its monomial, uncut. -/
lemma toBar_corolla {n : ℕ} (M : VMono G n) :
    toBar (STree.node M fun j : Fin n => .leaf j.1) = liftW false M.1 := by
  rw [toBar_node]
  conv_rhs => rw [← plug_leaf_eq (liftW false M.1)]
  refine plug_congr fun a _ => ?_
  unfold kids
  split_ifs <;> rfl

section Shape

variable {k l : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G)) (j₀ : Fin k) (m₂ : VMono G l)
  (c₂ : Fin l → STree (VMono G))

lemma kids_of_leaf {a : ℕ} (ha : a < k) {x : ℕ} (hx : ch ⟨a, ha⟩ = .leaf x) :
    kids ch a = LTree.leaf x := by
  rw [kids_of_lt ch ha, hx]
  rfl

lemma firstFn_of_leaf {a : ℕ} (ha : a < k) {x : ℕ} (hx : ch ⟨a, ha⟩ = .leaf x) :
    firstFn ch a = x := by
  rw [firstFn, dif_pos ha, hx]
  rfl

/-- **The key of the cut edge of a tree with two vertices**: the key of the child. -/
def twoKey : ℕ ×ₗ ℕ := key (kids ch j₀)

variable {m₁ ch j₀ m₂ c₂}
variable (hj₀ : ch j₀ = .node m₂ c₂) (hl₁ : ∀ j, j ≠ j₀ → ∃ a, ch j = .leaf a)
  (hl₂ : ∀ i, ∃ a, c₂ i = .leaf a)
include hj₀ hl₂

lemma kids_child_two :
    kids ch j₀ = (liftW true m₂.1).plug fun i => LTree.leaf (firstFn c₂ i) := by
  obtain ⟨e₂, l₂, r₂, h₂⟩ := m₂.exists_node
  rw [kids_fin, hj₀, toBar_node, h₂]
  show (liftW true (LTree.node e₂ l₂ r₂)).plug (kids c₂) = _
  rw [← h₂]
  refine plug_congr fun a ha => ?_
  rw [labels_liftW] at ha
  have hal := m₂.lt ha
  obtain ⟨x, hx⟩ := hl₂ ⟨a, hal⟩
  rw [kids_of_leaf c₂ hal hx, firstFn_of_leaf c₂ hal hx]

/-- **Merging the cut edge of a tree with two vertices** gives the bar tree of the corolla of the
merged monomial. -/
theorem mergeK_toBar_two (hl₁ : ∀ j, j ≠ j₀ → ∃ a, ch j = .leaf a) :
    mergeK (toBar (STree.node m₁ ch)) (twoKey ch j₀) = liftW false (twoMono m₁ ch j₀ m₂ c₂) := by
  obtain ⟨e, l, r, h⟩ := m₁.exists_node
  obtain ⟨e₂, l₂, r₂, h₂⟩ := m₂.exists_node
  rw [toBar_node, twoMono, mergeMono, liftW_false_plug, h,
    mergeK_plug_liftW (kids ch) false e l r _ (by simp), ← h]
  refine plug_congr fun a ha => ?_
  rw [labels_liftW] at ha
  have hak := m₁.lt ha
  by_cases ha0 : a = j₀
  · subst ha0
    rw [if_pos rfl, kids_child_two hj₀ hl₂, liftW_false_plug, h₂,
      mergeK_plug_liftW_root _ true e₂ l₂ r₂ _ ⟨rfl, by rw [twoKey, kids_child_two hj₀ hl₂, h₂]⟩]
    rfl
  · rw [if_neg ha0]
    have hne : (⟨a, hak⟩ : Fin k) ≠ j₀ := fun h' => ha0 (by rw [← h'])
    obtain ⟨x, hx⟩ := hl₁ _ hne
    rw [kids_of_leaf ch hak hx, firstFn_of_leaf ch hak hx]
    rfl

/-- **A tree with two vertices has one cut edge.** -/
theorem cutKeys_toBar_two (hnd : (STree.node m₁ ch).labels.Nodup)
    (hw : (STree.node m₁ ch).weight = 2) :
    ShuffleBar.cutKeys (toBar (STree.node m₁ ch)) = {twoKey ch j₀} := by
  have hc := card_cutKeys_toBar m₁ ch hnd
  rw [hw] at hc
  obtain ⟨κ, hκ⟩ := Finset.card_eq_one.1
    (show (ShuffleBar.cutKeys (toBar (STree.node m₁ ch))).card = 1 by omega)
  rw [hκ, Finset.singleton_inj]
  have hmem : twoKey ch j₀ ∈ ShuffleBar.cutKeys (toBar (STree.node m₁ ch)) := by
    rw [cutKeys_toBar_node]
    refine Finset.mem_biUnion.2 ⟨j₀, Finset.mem_range.2 j₀.2, ?_⟩
    rw [twoKey, kids_child_two hj₀ hl₂]
    obtain ⟨e₂, l₂, r₂, h₂⟩ := m₂.exists_node
    rw [h₂, cutKeys_plug_liftW, if_pos rfl]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  rw [hκ] at hmem
  exact (Finset.mem_singleton.1 hmem).symm

omit hj₀ hl₂ in
lemma strictOn_firstFn {k' : ℕ} (m : VMono G k') {c : Fin k' → STree (VMono G)}
    (hmono : StrictMono fun j => (c j).first) : StrictOn (firstFn c) m.1 := by
  intro a ha b hb hab
  rw [firstFn, dif_pos (m.lt ha), firstFn, dif_pos (m.lt hb)]
  exact hmono (show (⟨a, m.lt ha⟩ : Fin k') < ⟨b, m.lt hb⟩ from hab)

/-- **The merged monomial of a tree with two vertices is a monomial** on the leaves of the tree. -/
theorem twoMono_mem (hl₁ : ∀ j, j ≠ j₀ → ∃ a, ch j = .leaf a) {n : ℕ}
    (ht : (STree.node m₁ ch).IsShuffle) (hlab : (STree.node m₁ ch).labels = (Finset.range n).val) :
    twoMono m₁ ch j₀ m₂ c₂ ∈ LTree.monomials n ∧ 2 ≤ n := by
  have ht₂ : (STree.node m₂ c₂).IsShuffle := hj₀ ▸ ht.2.1 j₀
  have hs₂ : StrictOn (fun i => (LTree.leaf (firstFn c₂ i) : LTree G).minLabel) m₂.1 :=
    strictOn_firstFn m₂ ht₂.2.2
  have hmin : ∀ a ∈ m₁.1.labels, (if a = (j₀ : ℕ) then
      m₂.1.plug (fun i => LTree.leaf (firstFn c₂ i)) else LTree.leaf (firstFn ch a)).minLabel
        = firstFn ch a := fun a _ => by
    by_cases ha0 : a = j₀
    · subst ha0
      rw [if_pos rfl, minLabel_plug_of_strictOn _ hs₂, m₂.minLabel, firstFn_fin, hj₀,
        first_node _ _ ht₂.1]
      rw [firstFn, dif_pos ht₂.1]
      rfl
    · rw [if_neg ha0]
      rfl
  have hshuf : (twoMono m₁ ch j₀ m₂ c₂).IsShuffle := by
    refine isShuffle_plug_of_strictOn _ m₁.isShuffle (fun a ha b hb hab => ?_) fun a _ => ?_
    · beta_reduce
      rw [hmin a ha, hmin b hb]
      exact strictOn_firstFn m₁ ht.2.2 a ha b hb hab
    · beta_reduce
      split_ifs
      · exact isShuffle_plug_of_strictOn _ m₂.isShuffle hs₂ fun _ _ => trivial
      · trivial
  have hlabs : ((twoMono m₁ ch j₀ m₂ c₂).labels : Multiset ℕ) = (STree.node m₁ ch).labels := by
    rw [twoMono, mergeMono, labels_plug, ← Multiset.coe_bind, bind_kids m₁, STree.labels]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀
    · subst hj
      rw [if_pos rfl, labels_plug_leaf, ← Multiset.map_coe, hj₀, STree.labels]
      rw [show Multiset.map (firstFn c₂) (m₂.1.labels : Multiset ℕ)
        = Multiset.bind (m₂.1.labels : Multiset ℕ) fun a => {firstFn c₂ a} by
          rw [Multiset.bind_singleton], bind_kids m₂]
      refine Finset.sum_congr rfl fun i _ => ?_
      obtain ⟨x, hx⟩ := hl₂ i
      rw [firstFn_fin, hx]
      rfl
    · rw [if_neg (fun h' => hj (Fin.ext h'))]
      obtain ⟨x, hx⟩ := hl₁ j hj
      rw [firstFn_fin, hx]
      rfl
  refine ⟨(LTree.mem_monomials n _).2 ⟨hshuf, Multiset.coe_eq_coe.1 ?_⟩, ?_⟩
  · rw [hlabs, hlab, Finset.range_val, Multiset.coe_range]
  · have hc := congrArg Multiset.card hlab
    rw [STree.labels, Multiset.card_sum, Finset.range_val, Multiset.card_range] at hc
    have hk : ∑ _j : Fin k, 1 ≤ ∑ j, Multiset.card (ch j).labels :=
      Finset.sum_le_sum fun j _ => Multiset.card_pos.2 (FreeGrL.labels_ne_zero (ht.2.1 j))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hk
    have := m₁.2.2
    omega

end Shape

end TwoTrees

/-! ## The differential identity on trees with at most two vertices -/

section PhiTwo

open ShuffleBar STree

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)

lemma labels_corolla {n : ℕ} (M : VMono G n) :
    (STree.node M fun j : Fin n => STree.leaf j.1).labels = (Finset.range n).val := by
  rw [STree.labels]
  simp only [STree.labels_leaf]
  rw [Fin.sum_univ_eq_sum_range (fun i => ({i} : Multiset ℕ)) n, Finset.sum_eq_multiset_sum,
    Multiset.sum_map_singleton]

lemma isShuffle_corolla {n : ℕ} (M : VMono G n) :
    (STree.node M fun j : Fin n => STree.leaf j.1).IsShuffle :=
  ⟨by have := M.2.2; omega, fun _ => trivial, fun _ _ h => h⟩

/-- **The corolla of a monomial**, as a shuffle tree of monomials. -/
def corollaS {n : ℕ} (M : VMono G n) : SMono (VMono G) (Finset.range n) :=
  ⟨STree.node M fun j : Fin n => STree.leaf j.1, isShuffle_corolla M, labels_corolla M⟩

lemma barBasisN_eq_shEv (n : ℕ) (t : SMono (VMono G) (Finset.range n))
    (h : t.1.labels = (Finset.range (Fintype.card (Fin n))).val) :
    barBasisN c hc n t = GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm
      (FreeGrL.shEv (genBasis c hc) t.1 _ h) := by
  rw [barBasisN_apply, barBasis]
  exact FreeGrL.shuffleBasis_apply (genBasis c hc) (par_genBasis c hc) (Fin n) _

/-- **The bar differential of a tree with two vertices** is the basis vector of the corolla of its
merged monomial. -/
theorem d_barBasisN_two {n : ℕ} {k l : ℕ} (m₁ : VMono G k) (ch : Fin k → STree (VMono G))
    (j₀ : Fin k) (m₂ : VMono G l) (c₂ : Fin l → STree (VMono G)) (hj₀ : ch j₀ = .node m₂ c₂)
    (hl₁ : ∀ j, j ≠ j₀ → ∃ a, ch j = .leaf a) (hl₂ : ∀ i, ∃ a, c₂ i = .leaf a)
    (ht : (STree.node m₁ ch).IsShuffle) (hlab : (STree.node m₁ ch).labels = (Finset.range n).val) :
    Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n ⟨_, ht, hlab⟩)
      = barBasisN c hc n (corollaS ⟨_, twoMono_mem hj₀ hl₂ hl₁ ht hlab⟩) := by
  have hM := twoMono_mem hj₀ hl₂ hl₁ ht hlab
  have h₁ : (STree.node m₁ ch).labels = (Finset.range (Fintype.card (Fin n))).val := by
    rw [Fintype.card_fin]
    exact hlab
  have h₂ : (corollaS (⟨_, hM⟩ : VMono G n)).1.labels
      = (Finset.range (Fintype.card (Fin n))).val := by
    rw [Fintype.card_fin]
    exact labels_corolla _
  have e1 := barBasisN_eq_shEv c hc n ⟨_, ht, hlab⟩ h₁
  have e2 := barBasisN_eq_shEv c hc n (corollaS ⟨_, hM⟩) h₂
  have e3 := d_shEv_two c hc m₁ ch j₀ m₂ c₂ hj₀ hl₁ hl₂ ht h₁ hM h₂
  have e4 := Bar.d_map (I := Ibar K E c hc) (FreeGrL.posEquiv (Fin n)).symm
    (FreeGrL.shEv (genBasis c hc) (STree.node m₁ ch) _ h₁)
  refine (congrArg (Bar.d (Ibar K E c hc) (Fin n)) e1).trans (e4.trans ?_)
  exact (congrArg (GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm) e3).trans e2.symm

/-- **`Φ` intertwines the differentials on the trees with two vertices.** -/
theorem ΦL_d_barBasisN_of_weight_two {n : ℕ} (t : SMono (VMono G) (Finset.range n))
    (hw : t.1.weight = 2) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n t))
      = ShuffleBar.d K (ΦL c hc n (barBasisN c hc n t)) := by
  obtain ⟨t, ht, hlab⟩ := t
  obtain ⟨k, m₁, ch, j₀, l, m₂, c₂, rfl, hj₀, hl₁, hl₂⟩ := exists_two hw
  have hnd : (STree.node m₁ ch).labels.Nodup := by
    rw [hlab]
    exact Finset.nodup _
  have hs1 : sign K (STree.node m₁ ch) = 1 := sign_eq_one_of_weight_le_two K _ (le_of_eq hw)
  have hs2 : sign K (corollaS (⟨_, twoMono_mem hj₀ hl₂ hl₁ ht hlab⟩ : VMono G n)).1 = 1 :=
    sign_eq_one_of_weight_le_two K _ (by simp [corollaS, STree.weight])
  rw [d_barBasisN_two c hc m₁ ch j₀ m₂ c₂ hj₀ hl₁ hl₂ ht hlab, Φ_barBasisN, Φ_barBasisN, hs2]
  dsimp only
  rw [hs1, one_smul, one_smul, ShuffleBar.d_single, one_smul, ShuffleBar.dTree,
    cutKeys_toBar_two hj₀ hl₂ hnd hw, Finset.sum_singleton, ShuffleBar.sgn,
    cutKeys_toBar_two hj₀ hl₂ hnd hw, Finset.filter_singleton, if_neg (lt_irrefl _),
    Finset.card_empty, pow_zero, one_smul, mergeK_toBar_two hj₀ hl₂ hl₁]
  exact congrArg (fun x => Finsupp.single x (1 : K)) (toBar_corolla _)

/-- **The bar differential kills the corollas.** -/
theorem d_barBasisN_of_weight_one {n : ℕ} (t : SMono (VMono G) (Finset.range n))
    (hw : t.1.weight = 1) :
    Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n t) = (0 : BarCoop (Ibar K E c hc) (Fin n)) := by
  obtain ⟨t, ht, hlab⟩ := t
  obtain ⟨l, m, ch, rfl, hl⟩ := exists_corolla_of_weight_eq_one hw
  have h₁ : (STree.node m ch).labels = (Finset.range (Fintype.card (Fin n))).val := by
    rw [Fintype.card_fin]
    exact hlab
  obtain ⟨θ, -, hev⟩ := FreeGrL.exists_shEv_corolla (genBasis c hc) m ch _ h₁ hl
  have e1 := barBasisN_eq_shEv c hc n ⟨_, ht, hlab⟩ h₁
  have e2 := Bar.d_map (I := Ibar K E c hc) (FreeGrL.posEquiv (Fin n)).symm
    (FreeGrL.shEv (genBasis c hc) (STree.node m ch) _ h₁)
  refine (congrArg (Bar.d (Ibar K E c hc) (Fin n)) e1).trans (e2.trans ?_)
  rw [hev, Bar.d_map_ι, map_zero]
  rfl

/-- **`Φ` intertwines the differentials on the corollas**: both vanish. -/
theorem ΦL_d_barBasisN_of_weight_one {n : ℕ} (t : SMono (VMono G) (Finset.range n))
    (hw : t.1.weight = 1) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) (barBasisN c hc n t))
      = ShuffleBar.d K (ΦL c hc n (barBasisN c hc n t)) := by
  rw [d_barBasisN_of_weight_one c hc t hw, map_zero, Φ_barBasisN, map_smul, ShuffleBar.d_single,
    one_smul]
  obtain ⟨t, ht, hlab⟩ := t
  obtain ⟨l, m, ch, rfl, hl⟩ := exists_corolla_of_weight_eq_one hw
  have hnd : (STree.node m ch).labels.Nodup := by
    rw [hlab]
    exact Finset.nodup _
  have hc0 := card_cutKeys_toBar m ch hnd
  have hw' : (STree.node m ch).weight = 1 := hw
  rw [hw', Nat.add_eq_right, Finset.card_eq_zero] at hc0
  dsimp only
  rw [ShuffleBar.dTree, hc0, Finset.sum_empty, smul_zero]

/-- **`Φ` intertwines the differentials in vertex degrees one and two**: on the span of the trees
with one or two vertices, `ΦL ∘ Bar.d = ShuffleBar.d ∘ ΦL`. -/
theorem ΦL_d_of_mem_deg {n s : ℕ} (hs : s = 1 ∨ s = 2) {x : BarCoop (Ibar K E c hc) (Fin n)}
    (hx : x ∈ deg c hc n s) :
    ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) x) = ShuffleBar.d K (ΦL c hc n x) := by
  let D : BarCoop (Ibar K E c hc) (Fin n) →ₗ[K] BarCoop (Ibar K E c hc) (Fin n) :=
    Bar.d (Ibar K E c hc) (Fin n)
  have hle : deg c hc n s ≤
      LinearMap.eqLocus ((ΦL c hc n).comp D) ((ShuffleBar.d K).comp (ΦL c hc n)) := by
    rw [deg, Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    rcases hs with rfl | rfl
    · exact ΦL_d_barBasisN_of_weight_one c hc t ht
    · exact ΦL_d_barBasisN_of_weight_two c hc t ht
  exact hle hx

end PhiTwo

end ShuffleBarSym

end Operad
