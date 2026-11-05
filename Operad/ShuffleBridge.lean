/-
# The bridge between the binary and the any-arity shuffle operads

The binary shuffle machinery (`Operad.ShuffleNormal`, `Operad.ShuffleKoszul`) works with binary
trees `LTree E`; the machinery for generators of any arity (`Operad.ShuffleAnyGroebner`,
`Operad.ShuffleAnyKoszul`) with trees `STree F`, where `F k` are the generators of arity `k`.
This file translates the first into the second for a family `F` with generators of arity two
only (`Operad.BinaryGens`), the binary decorations being `F 2`.

* **Monomials.** A binary tree is a tree with generators of any arity (`ShuffleBridge.toS`,
  inverse `ShuffleBridge.ofS`), with the same leaves, its least label as least leaf, one vertex
  fewer than leaves, and the same shuffle condition (`ShuffleBridge.isShuffle_toS_iff`). So the
  binary shuffle monomials of arity `n` are the shuffle monomials on `0, …, n - 1`
  (`ShuffleBridge.monoEquiv`). The translation respects composition: grafting onto the leaves is
  substitution (`ShuffleBridge.toS_plug`), replacing at a path is replacing at its position
  (`ShuffleBridge.toS_replaceAt`), and substituting at a window is replacing by a substituted
  monomial (`ShuffleBridge.toS_substAt`).
* **Edges are contexts.** Substituting at an edge of a binary monomial is a context of the
  shuffle monomials (`ShuffleBridge.exists_ctx_of_edge`); conversely, every context from the
  monomials on `0, 1, 2` is substitution at the edge of a binary monomial whose window is the
  monomial it is applied to (`ShuffleBridge.exists_edge_of_ctx`).
* **Ideals.** Binary relators `R`, functions on the monomials of arity three, and rules `G` on
  the leaves `0, 1, 2` correspond when the vectors of the rules span the image of `R`
  (`ShuffleBridge.ruleVec`, the hypothesis `hR`). Then the binary ideal of `R` in arity `n` is the
  ideal of the rules on `0, …, n - 1` (`ShuffleBridge.map_idealOf`), and the two presented
  operads are linearly equivalent arity by arity (`ShuffleBridge.quotEquiv`).
* **Gröbner bases.** When the leading monomials of the rules are the set `L`, the normal
  monomials correspond (`ShuffleBridge.normal_iff`). A binary quadratic Gröbner basis
  (`LTree.IsGroebner`) makes the normal monomials independent modulo the ideal of the rules on
  `0, …, n - 1` (`ShuffleBridge.disjoint_range`), hence on every set of leaves, relabelling
  along the positions (`ShuffleBridge.disjoint_of_range`). So the rules are resolvable
  (`ShuffleBridge.resolvable_of_isGroebner`), and **a binary quadratic Gröbner basis gives
  `Rules.IsKoszul`** (`ShuffleBridge.isKoszul_of_isGroebner`), together with
  `ShuffleBar.IsKoszul` (`ShuffleBridge.isKoszul_and_of_isGroebner`). Conversely, resolvable
  rules give a binary quadratic Gröbner basis once every monomial of `L` leads a relator for the
  path-lexicographic key (`ShuffleBridge.isGroebner_of_resolvable`), and so `ShuffleBar.IsKoszul`
  (`ShuffleBridge.shuffleBar_isKoszul_of_resolvable`).
* **The commutative and associative operads** pass through the bridge: their binary relators
  and rules correspond (`ComBin.map_rel`, `AssBin.map_rel`), their ideals agree arity by arity
  (`ComBin.map_idealOf_rel`, `AssBin.map_idealOf_rel`), and the binary Gröbner bases alone give
  both Koszulness predicates (`ComBin.isKoszul_and_bridge`, `AssBin.isKoszul_and_bridge`).

**Open: the bar complexes.** `ShuffleBar.IsKoszul K R ↔ G.IsKoszul` is not proved. It needs the
bar trees and differentials compared (`BarTree (F 2)` is `LTree (BE F 2)` and `BE F` has binary
generators, so `toS` applies, but the keys `(minLabel, arity)` and `(first, weight)` of the
vertices differ by one and `mergeK` clears only flagged vertices), the binary relator
subcomplex `ShuffleBar.J`, spanned at uncut edges of valid bar trees of every arity, compared
with the ideal of the flagged rules `Rules.bar` on `0, …, n - 1`, and the any-arity bar complex
on an arbitrary set of leaves relabelled onto `0, …, n - 1`.
-/
import Operad.ShuffleBinCom
import Operad.ShuffleBinAss
import Operad.ShuffleFreeAny
import Operad.ShuffleVData

universe v

namespace Operad

/-- **Binary generators**: a family of generators with no generator of arity other than two. -/
class BinaryGens (F : ℕ → Type v) : Prop where
  /-- there is no generator of arity other than two -/
  isEmpty_of_ne : ∀ k, k ≠ 2 → IsEmpty (F k)

namespace ShuffleBridge

variable {F : ℕ → Type v}

/-! ## Binary trees as trees with generators of any arity -/

/-- **A binary tree as a tree with generators of any arity.** -/
def toS : LTree (F 2) → STree F
  | .leaf a => .leaf a
  | .node e l r => .node e ![toS l, toS r]

/-- **A tree with binary generators as a binary tree.** -/
def ofS : STree F → LTree (F 2)
  | .leaf a => .leaf a
  | @STree.node _ 2 e c => .node e (ofS (c 0)) (ofS (c 1))
  | .node _ _ => .leaf 0

@[simp] lemma toS_leaf (a : ℕ) : toS (.leaf a : LTree (F 2)) = .leaf a := rfl

@[simp] lemma toS_node (e : F 2) (l r : LTree (F 2)) :
    toS (.node e l r) = .node e ![toS l, toS r] := rfl

@[simp] lemma ofS_leaf (a : ℕ) : ofS (.leaf a : STree F) = .leaf a := rfl

lemma ofS_node (e : F 2) (c : Fin 2 → STree F) :
    ofS (.node e c) = .node e (ofS (c 0)) (ofS (c 1)) := rfl

@[simp] lemma ofS_toS : ∀ t : LTree (F 2), ofS (toS t) = t
  | .leaf _ => rfl
  | .node e l r => by
    rw [toS_node, ofS_node]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ofS_toS l, ofS_toS r]

lemma toS_injective : Function.Injective (toS : LTree (F 2) → STree F) :=
  Function.LeftInverse.injective ofS_toS

lemma node_eq_of_two (e : F 2) (c : Fin 2 → STree F) : STree.node e c = .node e ![c 0, c 1] := by
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] lemma toS_ofS [BinaryGens F] : ∀ t : STree F, toS (ofS t) = t
  | .leaf _ => rfl
  | @STree.node _ k e c => by
    have ih : ∀ i, toS (ofS (c i)) = c i := fun i => toS_ofS (c i)
    by_cases hk : k = 2
    · subst hk
      rw [ofS_node, toS_node, ih 0, ih 1, ← node_eq_of_two]
    · exact ((BinaryGens.isEmpty_of_ne k hk).false e).elim

lemma ofS_injective [BinaryGens F] : Function.Injective (ofS : STree F → LTree (F 2)) :=
  Function.LeftInverse.injective toS_ofS

/-! ### Leaves, weight and the shuffle condition -/

lemma labels_toS : ∀ t : LTree (F 2), (toS t).labels = (t.labels : Multiset ℕ)
  | .leaf _ => rfl
  | .node e l r => by
    rw [toS_node, STree.labels_node, Fin.sum_univ_two, LTree.labels_node, ← Multiset.coe_add]
    exact congrArg₂ (· + ·) (labels_toS l) (labels_toS r)

lemma weight_toS : ∀ t : LTree (F 2), (toS t).weight + 1 = t.arity
  | .leaf _ => rfl
  | .node e l r => by
    have hl := weight_toS l
    have hr := weight_toS r
    rw [toS_node, STree.weight_node, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, LTree.arity]
    omega

lemma first_toS : ∀ t : LTree (F 2), t.IsShuffle → (toS t).first = t.minLabel
  | .leaf _, _ => rfl
  | .node e l r, h => by
    rw [toS_node, STree.first_node _ _ (by omega), LTree.minLabel_node_of_shuffle h]
    exact first_toS l h.2.1

lemma isShuffle_toS_iff : ∀ t : LTree (F 2), (toS t).IsShuffle ↔ t.IsShuffle
  | .leaf _ => Iff.rfl
  | .node e l r => by
    rw [toS_node, STree.isShuffle_node, LTree.isShuffle_node, Fin.forall_fin_two,
      Fin.strictMono_iff_lt_succ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, isShuffle_toS_iff l,
      isShuffle_toS_iff r, Fin.forall_fin_one]
    constructor
    · rintro ⟨-, ⟨hl, hr⟩, h⟩
      refine ⟨?_, hl, hr⟩
      have h' : (toS l).first < (toS r).first := h
      rwa [first_toS l hl, first_toS r hr] at h'
    · rintro ⟨h, hl, hr⟩
      refine ⟨by omega, ⟨hl, hr⟩, ?_⟩
      show (toS l).first < (toS r).first
      rwa [first_toS l hl, first_toS r hr]

/-! ### Composition: grafting, positions and replacement -/

/-- **Grafting onto the leaves is substitution.** -/
lemma toS_plug (ins : ℕ → LTree (F 2)) :
    ∀ m : LTree (F 2), toS (m.plug ins) = (toS m).subst fun a => toS (ins a)
  | .leaf _ => rfl
  | .node e l r => by
    show STree.node e ![toS (l.plug ins), toS (r.plug ins)] = _
    rw [toS_node, STree.subst_node, toS_plug ins l, toS_plug ins r]
    congr 1
    funext j
    fin_cases j <;> rfl

/-- **A binary path as a position**: `false` is the child `0`, `true` the child `1`. -/
def bpath (p : List Bool) : List ℕ := p.map Bool.toNat

@[simp] lemma bpath_nil : bpath [] = [] := rfl

@[simp] lemma bpath_cons (b : Bool) (p : List Bool) : bpath (b :: p) = b.toNat :: bpath p := rfl

/-- **Replacing at a path is replacing at its position.** -/
lemma toS_replaceAt : ∀ (t : LTree (F 2)) (p : List Bool) (u : LTree (F 2)),
    toS (t.replaceAt p u) = (toS t).replace (bpath p) (toS u)
  | t, [], u => by rw [LTree.replaceAt_nil, bpath_nil, STree.replace_nil]
  | .leaf _, _ :: _, _ => rfl
  | .node e l r, false :: p, u => by
    show STree.node e ![toS (l.replaceAt p u), toS r] = _
    rw [toS_node, bpath_cons, STree.replace_node_cons, toS_replaceAt l p u]
    congr 1
    funext j
    fin_cases j <;> rfl
  | .node e l r, true :: p, u => by
    show STree.node e ![toS l, toS (r.replaceAt p u)] = _
    rw [toS_node, bpath_cons, STree.replace_node_cons, toS_replaceAt r p u]
    congr 1
    funext j
    fin_cases j <;> rfl

/-- **The subtree at a path is the subtree at its position**, when it is a vertex. -/
lemma get?_toS : ∀ (t : LTree (F 2)) (p : List Bool) {e : F 2} {l r : LTree (F 2)},
    t.subtreeAt p = .node e l r → (toS t).get? (bpath p) = some (toS (.node e l r))
  | t, [], _, _, _, h => by
    rw [LTree.subtreeAt_nil] at h
    rw [h]
    rfl
  | .leaf _, _ :: _, _, _, _, h => by cases h
  | .node _ l' _, false :: p, _, _, _, h => by
    rw [toS_node, bpath_cons, STree.get?_node_cons, dif_pos (by decide)]
    exact get?_toS l' p h
  | .node _ _ r', true :: p, _, _, _, h => by
    rw [toS_node, bpath_cons, STree.get?_node_cons, dif_pos (by decide)]
    exact get?_toS r' p h

/-- **Every position of a binary tree is a path.** -/
lemma exists_path : ∀ (t : LTree (F 2)) (q : List ℕ) {w : STree F}, (toS t).get? q = some w →
    ∃ p, bpath p = q ∧ toS (t.subtreeAt p) = w
  | t, [], w, h => by
    rw [STree.get?_nil, Option.some_inj] at h
    exact ⟨[], rfl, by rw [LTree.subtreeAt_nil, h]⟩
  | .leaf _, _ :: _, _, h => by simp at h
  | .node e l r, i :: q, w, h => by
    rw [toS_node, STree.get?_node_cons_eq_some] at h
    obtain ⟨hi, h⟩ := h
    match i, hi, h with
    | 0, _, h =>
      obtain ⟨p, hp, hw⟩ := exists_path l q h
      exact ⟨false :: p, by rw [bpath_cons, hp]; rfl, hw⟩
    | 1, _, h =>
      obtain ⟨p, hp, hw⟩ := exists_path r q h
      exact ⟨true :: p, by rw [bpath_cons, hp]; rfl, hw⟩

/-- **Substitution at a window is replacement by a substituted monomial.** -/
lemma toS_substAt (t : LTree (F 2)) (p : List Bool) (s : Bool) (m : LTree (F 2)) :
    toS (t.substAt p s m) =
      (toS t).replace (bpath p) ((toS m).subst fun a => toS ((t.subtreeAt p).winIns s a)) := by
  rw [LTree.substAt, toS_replaceAt, toS_plug]

end ShuffleBridge

namespace LTree

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **A monomial of arity three with inputs grafted**, in increasing order of least labels, has
the monomial as the window of an edge at the root, and the inputs as the inputs of the
window. -/
lemma exists_window_plug {m : LTree E} (hm : m ∈ monomials 3) {ys : ℕ → LTree E}
    (h01 : (ys 0).minLabel < (ys 1).minLabel) (h12 : (ys 1).minLabel < (ys 2).minLabel) :
    ∃ s, (m.plug ys).IsEdgeRoot s ∧ (m.plug ys).windowRoot s = m ∧
      ∀ a < 3, (m.plug ys).winIns s a = ys a := by
  have hm' := (mem_monomials 3 m).1 hm
  obtain ⟨e, f, h | h | h⟩ := mono3_cases hm'.1 hm'.2 <;> subst h
  · refine ⟨false, trivial, ?_, fun a ha => ?_⟩
    · have e0 : rank3 (ys 0).minLabel (ys 1).minLabel (ys 2).minLabel (ys 0).minLabel = 0 := by
        simp only [rank3]; split_ifs <;> omega
      have e1 : rank3 (ys 0).minLabel (ys 1).minLabel (ys 2).minLabel (ys 1).minLabel = 1 := by
        simp only [rank3]; split_ifs <;> omega
      have e2 : rank3 (ys 0).minLabel (ys 1).minLabel (ys 2).minLabel (ys 2).minLabel = 2 := by
        simp only [rank3]; split_ifs <;> omega
      simp [plug, windowRoot, window, e0, e1, e2]
    · interval_cases a <;> simp [plug, winIns, winInputs, ins3, h12]
  · refine ⟨false, trivial, ?_, fun a ha => ?_⟩
    · have e0 : rank3 (ys 0).minLabel (ys 2).minLabel (ys 1).minLabel (ys 0).minLabel = 0 := by
        simp only [rank3]; split_ifs <;> omega
      have e1 : rank3 (ys 0).minLabel (ys 2).minLabel (ys 1).minLabel (ys 2).minLabel = 2 := by
        simp only [rank3]; split_ifs <;> omega
      have e2 : rank3 (ys 0).minLabel (ys 2).minLabel (ys 1).minLabel (ys 1).minLabel = 1 := by
        simp only [rank3]; split_ifs <;> omega
      simp [plug, windowRoot, window, e0, e1, e2]
    · have h21 : ¬ (ys 2).minLabel < (ys 1).minLabel := by omega
      interval_cases a <;> simp [plug, winIns, winInputs, ins3, h21]
  · have hw : winInputs (node e (ys 0) (node f (ys 1) (ys 2))) true = (ys 0, ys 1, ys 2) := by
      cases ys 0 <;> rfl
    have hwr : windowRoot (node e (ys 0) (node f (ys 1) (ys 2))) true =
        window e f true (ys 1).minLabel (ys 2).minLabel (ys 0).minLabel := by
      cases ys 0 <;> rfl
    refine ⟨true, ?_, ?_, fun a ha => ?_⟩
    · show IsEdgeRoot (node e (ys 0) (node f (ys 1) (ys 2))) true
      cases ys 0 <;> trivial
    · show windowRoot (node e (ys 0) (node f (ys 1) (ys 2))) true = _
      have e0 : rank3 (ys 1).minLabel (ys 2).minLabel (ys 0).minLabel (ys 0).minLabel = 0 := by
        simp only [rank3]; split_ifs <;> omega
      have e1 : rank3 (ys 1).minLabel (ys 2).minLabel (ys 0).minLabel (ys 1).minLabel = 1 := by
        simp only [rank3]; split_ifs <;> omega
      have e2 : rank3 (ys 1).minLabel (ys 2).minLabel (ys 0).minLabel (ys 2).minLabel = 2 := by
        simp only [rank3]; split_ifs <;> omega
      rw [hwr]
      simp [window, e0, e1, e2]
    · change winIns (node e (ys 0) (node f (ys 1) (ys 2))) true a = ys a
      rw [winIns, hw]
      interval_cases a <;> rfl

end LTree

namespace ShuffleBridge

open STree

variable {F : ℕ → Type v} [Fintype (F 2)] [DecidableEq (F 2)]

/-! ## Monomials -/

lemma toS_mem {n : ℕ} (t : LTree.Mono (F 2) n) :
    (toS t.1).IsShuffle ∧ (toS t.1).labels = (Finset.range n).val := by
  have h := (LTree.mem_monomials n t.1).1 t.2
  refine ⟨(isShuffle_toS_iff _).2 h.1, ?_⟩
  rw [labels_toS, Finset.range_val, ← Multiset.coe_range]
  exact Multiset.coe_eq_coe.2 h.2

lemma ofS_mem [BinaryGens F] {n : ℕ} (g : SMono F (Finset.range n)) :
    ofS g.1 ∈ LTree.monomials n := by
  rw [LTree.mem_monomials]
  have hs : (toS (ofS g.1)).IsShuffle := by
    rw [toS_ofS]
    exact g.isShuffle
  refine ⟨(isShuffle_toS_iff _).1 hs, ?_⟩
  have h1 : ((ofS g.1).labels : Multiset ℕ) = Multiset.range n := by
    rw [← labels_toS, toS_ofS]
    exact g.labels_eq
  exact Multiset.coe_eq_coe.1 (h1.trans (Multiset.coe_range n).symm)

variable (F) in
/-- **The binary shuffle monomials of arity `n` are the shuffle monomials** on `0, …, n - 1`
with binary generators. -/
def monoEquiv [BinaryGens F] (n : ℕ) : LTree.Mono (F 2) n ≃ SMono F (Finset.range n) where
  toFun t := ⟨toS t.1, toS_mem t⟩
  invFun g := ⟨ofS g.1, ofS_mem g⟩
  left_inv t := Subtype.ext (ofS_toS t.1)
  right_inv g := Subtype.ext (toS_ofS g.1)

@[simp] lemma monoEquiv_val [BinaryGens F] {n : ℕ} (t : LTree.Mono (F 2) n) :
    (monoEquiv F n t).1 = toS t.1 := rfl

@[simp] lemma monoEquiv_symm_val [BinaryGens F] {n : ℕ} (g : SMono F (Finset.range n)) :
    ((monoEquiv F n).symm g).1 = ofS g.1 := rfl

/-! ## Edges and contexts -/

/-- **The context of an edge**: substituting at an edge of a binary monomial is a context of
the shuffle monomials. -/
theorem exists_ctx_of_edge [BinaryGens F] {n : ℕ} (t : LTree.Mono (F 2) n) {p : List Bool}
    {s : Bool} (he : t.1.IsEdge p s) :
    ∃ f : SMono F (Finset.range 3) → SMono F (Finset.range n), IsSCtx f ∧
      ∀ σ : LTree.Mono (F 2) 3, f (monoEquiv F 3 σ) =
        monoEquiv F n ⟨t.1.substAt p s σ.1, LTree.substAt_mem_monomials t.2 he σ.2⟩ := by
  have ht := (LTree.mem_monomials n t.1).1 t.2
  have hnd : t.1.labels.Nodup := ht.2.nodup_iff.2 List.nodup_range
  have hw := LTree.winSpec_of_edge he ht.1 hnd
  refine ⟨fun g => monoEquiv F n ⟨t.1.substAt p s (ofS g.1),
      LTree.substAt_mem_monomials t.2 he (ofS_mem g)⟩,
    ⟨toS t.1, bpath p, fun a => toS ((t.1.subtreeAt p).winIns s a), ?_, ⟨fun a _ => ?_,
      fun a ha b hb => ?_, fun a ha b hb hab => ?_⟩, fun g => ?_⟩, fun σ => ?_⟩
  · obtain ⟨e, l, r, h⟩ := he.exists_node
    rw [get?_toS t.1 p h]
    rfl
  · exact (isShuffle_toS_iff _).2 (hw.shuffle a)
  · rw [labels_toS, Multiset.mem_coe] at hb
    have ha3 : a < 3 := Finset.mem_range.1 ha
    have hb' : b ∈ (t.1.subtreeAt p).labels := by
      refine hw.perm.symm.subset ?_
      simp only [List.mem_append]
      interval_cases a
      · exact Or.inl (Or.inl hb)
      · exact Or.inl (Or.inr hb)
      · exact Or.inr hb
    exact Finset.mem_range.2
      (List.mem_range.1 (ht.2.subset (LTree.labels_subtreeAt_subset _ _ hb')))
  · simp only
    rw [first_toS _ (hw.shuffle a), first_toS _ (hw.shuffle b)]
    exact hw.mono a b hab (Finset.mem_range.1 hb)
  · show toS (t.1.substAt p s (ofS g.1)) = _
    rw [toS_substAt, toS_ofS]
  · apply Subtype.ext
    show toS (t.1.substAt p s (ofS (toS σ.1))) = toS (t.1.substAt p s σ.1)
    rw [ofS_toS]

/-- **The edge of a context**: a context of the shuffle monomials with binary generators, from
those on `0, 1, 2`, is the substitution at an edge of a binary monomial, the edge whose window
is the monomial it is applied to. -/
theorem exists_edge_of_ctx [BinaryGens F] {B : Finset ℕ}
    {f : SMono F (Finset.range 3) → SMono F B} (hf : IsSCtx f)
    (σ₀ : SMono F (Finset.range 3)) :
    ∃ p s, (ofS (f σ₀).1).IsEdge p s ∧ (ofS (f σ₀).1).windowAt p s = ofS σ₀.1 ∧
      ∀ g, ofS (f g).1 = (ofS (f σ₀).1).substAt p s (ofS g.1) := by
  obtain ⟨q, xs, hget, hin, hrep⟩ := IsSCtx.normal hf σ₀
  have hTS : toS (ofS (f σ₀).1) = (f σ₀).1 := toS_ofS _
  rw [← hTS] at hget
  obtain ⟨p, rfl, hp⟩ := exists_path _ q hget
  have hxs : ∀ a ∈ Finset.range 3, toS (ofS (xs a)) = xs a := fun a _ => toS_ofS _
  have hsub : (ofS (f σ₀).1).subtreeAt p = (ofS σ₀.1).plug fun a => ofS (xs a) := by
    apply toS_injective
    rw [hp, toS_plug, toS_ofS]
    exact subst_congr _ fun a ha => (hxs a (σ₀.mem_labels.1 ha)).symm
  have hmin : ∀ a ∈ Finset.range 3, (ofS (xs a)).minLabel = (xs a).first := fun a ha => by
    have hs : (ofS (xs a)).IsShuffle := by
      rw [← isShuffle_toS_iff, hxs a ha]
      exact hin.shuffle a ha
    rw [← first_toS _ hs, hxs a ha]
  have h3 : ∀ a < 3, a ∈ Finset.range 3 := fun a ha => Finset.mem_range.2 ha
  have h01 : (ofS (xs 0)).minLabel < (ofS (xs 1)).minLabel := by
    rw [hmin 0 (h3 0 (by norm_num)), hmin 1 (h3 1 (by norm_num))]
    exact hin.mono (h3 0 (by norm_num)) (h3 1 (by norm_num)) (by norm_num)
  have h12 : (ofS (xs 1)).minLabel < (ofS (xs 2)).minLabel := by
    rw [hmin 1 (h3 1 (by norm_num)), hmin 2 (h3 2 (by norm_num))]
    exact hin.mono (h3 1 (by norm_num)) (h3 2 (by norm_num)) (by norm_num)
  obtain ⟨s, hedge, hwin, hins⟩ :=
    LTree.exists_window_plug (ys := fun a => ofS (xs a)) (ofS_mem σ₀) h01 h12
  refine ⟨p, s, ?_, ?_, fun g => ?_⟩
  · show ((ofS (f σ₀).1).subtreeAt p).IsEdgeRoot s
    rw [hsub]
    exact hedge
  · show ((ofS (f σ₀).1).subtreeAt p).windowRoot s = _
    rw [hsub]
    exact hwin
  · apply toS_injective
    rw [toS_ofS, hrep g, toS_substAt, hTS, hsub, toS_ofS]
    congr 1
    refine subst_congr _ fun a ha => ?_
    have ha3 := Finset.mem_range.1 (g.mem_labels.1 ha)
    rw [hins a ha3, hxs a (h3 a ha3)]

/-! ## Ideals -/

section Ideal

variable (K : Type*) [Field K]

variable (F) in
/-- **The vectors of binary monomials as combinations of shuffle monomials**, along
`monoEquiv`. -/
noncomputable def vecEquiv [BinaryGens F] (n : ℕ) :
    (LTree.Mono (F 2) n → K) ≃ₗ[K] (SMono F (Finset.range n) →₀ K) :=
  (Finsupp.linearEquivFunOnFinite K K (LTree.Mono (F 2) n)).symm ≪≫ₗ
    Finsupp.domLCongr (monoEquiv F n)

variable [BinaryGens F]

lemma vecEquiv_apply {n : ℕ} (v : LTree.Mono (F 2) n → K) (g : SMono F (Finset.range n)) :
    vecEquiv F K n v g = v ((monoEquiv F n).symm g) := by
  simp [vecEquiv, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply]

lemma vecEquiv_symm_apply {n : ℕ} (w : SMono F (Finset.range n) →₀ K) (x : LTree.Mono (F 2) n) :
    (vecEquiv F K n).symm w x = w (monoEquiv F n x) := by
  have := vecEquiv_apply K ((vecEquiv F K n).symm w) (monoEquiv F n x)
  rw [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply] at this
  exact this.symm

lemma vecEquiv_eq_sum {n : ℕ} (v : LTree.Mono (F 2) n → K) :
    vecEquiv F K n v = ∑ x, v x • Finsupp.single (monoEquiv F n x) 1 := by
  classical
  ext g
  rw [vecEquiv_apply, Finsupp.finsetSum_apply,
    Finset.sum_eq_single ((monoEquiv F n).symm g) (fun x _ hx => ?_) (by simp)]
  · simp
  · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
    intro h
    exact hx (by rw [← h, Equiv.symm_apply_apply])

lemma vecEquiv_vecOf {n : ℕ} {t : LTree (F 2)} (ht : t ∈ LTree.monomials n) :
    vecEquiv F K n (LTree.vecOf K n t) = Finsupp.single (monoEquiv F n ⟨t, ht⟩) 1 := by
  classical
  ext g
  rw [vecEquiv_apply, Finsupp.single_apply, LTree.vecOf]
  by_cases h : monoEquiv F n ⟨t, ht⟩ = g
  · rw [if_pos h, if_pos]
    rw [← h, Equiv.symm_apply_apply]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [← Equiv.apply_symm_apply (monoEquiv F n) g]
    exact congrArg _ (Subtype.ext h'.symm)

/-- **The substitution of a relator at an edge is the image of the relator under the context of
the edge.** -/
lemma vecEquiv_substVec {n : ℕ} (t : LTree.Mono (F 2) n) {p : List Bool} {s : Bool}
    (he : t.1.IsEdge p s) (r : LTree.Mono (F 2) 3 → K)
    {f : SMono F (Finset.range 3) → SMono F (Finset.range n)}
    (hf : ∀ σ : LTree.Mono (F 2) 3, f (monoEquiv F 3 σ) =
      monoEquiv F n ⟨t.1.substAt p s σ.1, LTree.substAt_mem_monomials t.2 he σ.2⟩) :
    vecEquiv F K n (LTree.substVec K n t.1 p s r) = Finsupp.mapDomain f (vecEquiv F K 3 r) := by
  rw [vecEquiv_eq_sum K (n := 3), Finsupp.mapDomain_finsetSum, LTree.substVec, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_smul, vecEquiv_vecOf K (LTree.substAt_mem_monomials t.2 he σ.2),
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single, hf σ]

variable {K} {ρ : Type*} {O : AdmOrder F} (G : Rules K ρ O.toCtxOrder)

/-- **The vector of a rule**, leading monomial minus tail, on the leaves `0, 1, 2`. -/
noncomputable def ruleVec (hsrc : ∀ r, G.src r = Finset.range 3) (r : ρ) :
    SMono F (Finset.range 3) →₀ K :=
  Finsupp.mapDomain (SMono.cast (hsrc r)) (Finsupp.single (G.lead r) 1 - G.tail r)

omit [Fintype (F 2)] [DecidableEq (F 2)] [BinaryGens F] in
lemma ruleVec_mem (hsrc : ∀ r, G.src r = Finset.range 3) (r : ρ) :
    ruleVec G hsrc r ∈ (G.rw (Finset.range 3)).ideal :=
  G.ideal_cast (hsrc r) ((G.rw (G.src r)).sub_mem_ideal
    ⟨r, id, O.toCtxOrder.ctx_id _, rfl, (Finsupp.mapDomain_id).symm⟩)

omit [Fintype (F 2)] [DecidableEq (F 2)] [BinaryGens F] in
lemma cast_rfl {A : Finset ℕ} : (SMono.cast (rfl : A = A) : SMono F A → SMono F A) = id :=
  funext fun _ => Subtype.ext rfl

/-- **A context from the leaves `0, 1, 2` maps the relators into the binary ideal.** -/
theorem mapDomain_mem_map_idealOf (R : Submodule K (LTree.Mono (F 2) 3 → K)) {n : ℕ}
    {C : Finset ℕ} (hC : C = Finset.range 3)
    {f : SMono F C → SMono F (Finset.range n)} (hf : IsSCtx f) {v : SMono F C →₀ K}
    (hv : Finsupp.mapDomain (SMono.cast hC) v ∈ R.map (vecEquiv F K 3).toLinearMap) :
    Finsupp.mapDomain f v ∈ (LTree.idealOf K R n).map (vecEquiv F K n).toLinearMap := by
  subst hC
  rw [cast_rfl, Finsupp.mapDomain_id] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  by_cases hne : Nonempty (SMono F (Finset.range 3))
  · obtain ⟨σ₀⟩ := hne
    obtain ⟨p, s, he, -, hall⟩ := exists_edge_of_ctx hf σ₀
    set t : LTree.Mono (F 2) n := (monoEquiv F n).symm (f σ₀)
    have hfσ : ∀ σ : LTree.Mono (F 2) 3, f (monoEquiv F 3 σ) =
        monoEquiv F n ⟨t.1.substAt p s σ.1, LTree.substAt_mem_monomials t.2 he σ.2⟩ :=
      fun σ => Subtype.ext (ofS_injective (by
        rw [hall]
        simp only [monoEquiv_val, ofS_toS]
        rfl))
    show Finsupp.mapDomain f (vecEquiv F K 3 w) ∈ _
    rw [← vecEquiv_substVec K t he w hfσ]
    exact Submodule.mem_map_of_mem (LTree.substVec_mem_idealOf K R t he hw)
  · have : vecEquiv F K 3 w = 0 := by
      ext g
      exact (hne ⟨g⟩).elim
    show Finsupp.mapDomain f (vecEquiv F K 3 w) ∈ _
    rw [this, Finsupp.mapDomain_zero]
    exact Submodule.zero_mem _

/-- **The ideals correspond**: for rules of arity three whose vectors span the binary relators,
the ideal of the binary relators in arity `n` is the ideal generated by the rules on the leaves
`0, …, n - 1`, under `vecEquiv`. -/
theorem map_idealOf (hsrc : ∀ r, G.src r = Finset.range 3)
    (R : Submodule K (LTree.Mono (F 2) 3 → K))
    (hR : R.map (vecEquiv F K 3).toLinearMap = Submodule.span K (Set.range (ruleVec G hsrc)))
    (n : ℕ) :
    (LTree.idealOf K R n).map (vecEquiv F K n).toLinearMap = (G.rw (Finset.range n)).ideal := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 ?_)) ?_
  · rintro _ ⟨t, p, s, r, hr, he, rfl⟩
    obtain ⟨f, hf, hfσ⟩ := exists_ctx_of_edge t he
    rw [SetLike.mem_coe, Submodule.mem_comap]
    show vecEquiv F K n (LTree.substVec K n t.1 p s r) ∈ (G.rw (Finset.range n)).ideal
    rw [vecEquiv_substVec K t he r hfσ]
    refine G.mapDomain_mem_ideal hf ?_
    have h3 : vecEquiv F K 3 r ∈ R.map (vecEquiv F K 3).toLinearMap :=
      Submodule.mem_map_of_mem hr
    rw [hR] at h3
    exact Submodule.span_le.2 (by rintro _ ⟨r', rfl⟩; exact ruleVec_mem G hsrc r') h3
  · rw [Rules.ideal_eq_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨r, f, hf, rfl⟩
    refine mapDomain_mem_map_idealOf R (hsrc r) hf ?_
    rw [hR]
    exact Submodule.subset_span ⟨r, rfl⟩

/-- **The presented operads are linearly equivalent** arity by arity: the quotient of the binary
relators and that of the rules. -/
noncomputable def quotEquiv (hsrc : ∀ r, G.src r = Finset.range 3)
    (R : Submodule K (LTree.Mono (F 2) 3 → K))
    (hR : R.map (vecEquiv F K 3).toLinearMap = Submodule.span K (Set.range (ruleVec G hsrc)))
    (n : ℕ) :
    ((LTree.Mono (F 2) n → K) ⧸ LTree.idealOf K R n) ≃ₗ[K]
      ((SMono F (Finset.range n) →₀ K) ⧸ (G.rw (Finset.range n)).ideal) :=
  Submodule.Quotient.equiv _ _ (vecEquiv F K n) (map_idealOf G hsrc R hR n)


end Ideal

/-! ## Relabelling the leaves -/

section Relabel

variable {E : ℕ → Type v}

/-- **Relabel a monomial** along a map strictly increasing on its leaves, onto new leaves. -/
def relabelM {A B : Finset ℕ} (φ : ℕ → ℕ) (hφ : StrictMonoOn φ A) (himg : A.image φ = B)
    (g : SMono E A) : SMono E B :=
  ⟨g.1.relabel φ, isShuffle_relabel g.isShuffle
      (fun _ ha _ hb hab => hφ (g.mem_labels.1 ha) (g.mem_labels.1 hb) hab), by
    rw [labels_relabel, g.labels_eq, ← himg, Finset.image_val_of_injOn hφ.injOn]⟩

lemma isSCtx_relabelM {A B : Finset ℕ} (φ : ℕ → ℕ) (hφ : StrictMonoOn φ A)
    (himg : A.image φ = B) : IsSCtx (relabelM (E := E) φ hφ himg) :=
  ⟨leaf 0, [], fun a => leaf (φ a), rfl,
    ⟨fun _ _ => trivial, fun a ha b hb => by
      rw [labels_leaf, Multiset.mem_singleton] at hb
      rw [hb, ← himg]
      exact Finset.mem_image_of_mem φ ha, fun _ ha _ hb hab => hφ ha hb hab⟩,
    fun _ => by rw [replace_nil]; rfl⟩

/-- **The position** of an element in a finite set of natural numbers. -/
noncomputable def posIn (C : Finset ℕ) (a : ℕ) : ℕ :=
  if h : a ∈ C then ((C.orderIsoOfFin rfl).symm ⟨a, h⟩ : ℕ) else 0

/-- **The element at a position** in a finite set of natural numbers. -/
noncomputable def eltIn (C : Finset ℕ) (b : ℕ) : ℕ :=
  if h : b < C.card then (C.orderIsoOfFin rfl ⟨b, h⟩ : ℕ) else 0

lemma posIn_lt {C : Finset ℕ} {a : ℕ} (ha : a ∈ C) : posIn C a < C.card := by
  rw [posIn, dif_pos ha]
  exact Fin.is_lt _

lemma eltIn_mem {C : Finset ℕ} {b : ℕ} (hb : b < C.card) : eltIn C b ∈ C := by
  rw [eltIn, dif_pos hb]
  exact Subtype.prop _

lemma eltIn_posIn {C : Finset ℕ} {a : ℕ} (ha : a ∈ C) : eltIn C (posIn C a) = a := by
  rw [eltIn, dif_pos (posIn_lt ha)]
  simp only [posIn, dif_pos ha, Fin.eta, OrderIso.apply_symm_apply]

lemma posIn_eltIn {C : Finset ℕ} {b : ℕ} (hb : b < C.card) : posIn C (eltIn C b) = b := by
  rw [posIn, dif_pos (eltIn_mem hb)]
  simp only [eltIn, dif_pos hb, Subtype.coe_eta, OrderIso.symm_apply_apply]

lemma strictMonoOn_posIn (C : Finset ℕ) : StrictMonoOn (posIn C) C := by
  intro a ha a' ha' h
  simp only [posIn, dif_pos (show a ∈ C from ha), dif_pos (show a' ∈ C from ha')]
  exact (C.orderIsoOfFin rfl).symm.lt_iff_lt.2 (Subtype.mk_lt_mk.2 h)

lemma strictMonoOn_eltIn (C : Finset ℕ) :
    StrictMonoOn (eltIn C) (Finset.range C.card : Set ℕ) := by
  intro b hb b' hb' h
  have hb₁ : b < C.card := Finset.mem_range.1 hb
  have hb₂ : b' < C.card := Finset.mem_range.1 hb'
  simp only [eltIn, dif_pos hb₁, dif_pos hb₂]
  exact Subtype.mk_lt_mk.1 ((C.orderIsoOfFin rfl).lt_iff_lt.2 (Fin.mk_lt_mk.2 h))

lemma image_posIn (C : Finset ℕ) : C.image (posIn C) = Finset.range C.card := by
  ext b
  simp only [Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨a, ha, hab⟩ => hab ▸ posIn_lt ha, fun hb => ⟨_, eltIn_mem hb, posIn_eltIn hb⟩⟩

lemma image_eltIn (C : Finset ℕ) : (Finset.range C.card).image (eltIn C) = C := by
  ext a
  simp only [Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨b, hb, hab⟩ => hab ▸ eltIn_mem hb, fun ha => ⟨_, posIn_lt ha, eltIn_posIn ha⟩⟩

variable {K : Type*} [CommRing K] {ρ : Type*} {O : AdmOrder E} (G : Rules K ρ O.toCtxOrder)

/-- **A context with a left inverse context keeps the normal monomials normal.** -/
lemma normal_of_leftInverse {A B : Finset ℕ} {α : SMono E A → SMono E B}
    {β : SMono E B → SMono E A} (hβ : IsSCtx β) (hβα : ∀ t, β (α t) = t) {t : SMono E A}
    (ht : G.Normal t) : G.Normal (α t) :=
  fun r h hh heq => ht r (β ∘ h) (isSCtx_comp hβ hh) (by rw [Function.comp_apply, heq, hβα])

/-- **Independence of the normal monomials passes along a context with a left inverse
context.** -/
lemma disjoint_of_leftInverse {A B : Finset ℕ} {α : SMono E A → SMono E B}
    {β : SMono E B → SMono E A} (hα : IsSCtx α) (hβ : IsSCtx β) (hβα : ∀ t, β (α t) = t)
    (h : Disjoint (Finsupp.supported K K {t : SMono E B | G.Normal t}) (G.rw B).ideal) :
    Disjoint (Finsupp.supported K K {t : SMono E A | G.Normal t}) (G.rw A).ideal := by
  classical
  rw [Submodule.disjoint_def] at h ⊢
  intro w hw₁ hw₂
  apply Finsupp.mapDomain_injective (Function.LeftInverse.injective hβα)
  rw [Finsupp.mapDomain_zero]
  refine h _ ((Finsupp.mem_supported K _).2 fun y hy => ?_) (G.mapDomain_mem_ideal hα hw₂)
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
  exact normal_of_leftInverse G hβ hβα ((Finsupp.mem_supported K w).1 hw₁ hx)

/-- **Independence of the normal monomials on every set of leaves** follows from it on the
leaves `0, …, n - 1`, relabelling along the positions. -/
theorem disjoint_of_range
    (h : ∀ n, Disjoint (Finsupp.supported K K {t : SMono E (Finset.range n) | G.Normal t})
      (G.rw (Finset.range n)).ideal) (C : Finset ℕ) :
    Disjoint (Finsupp.supported K K {t : SMono E C | G.Normal t}) (G.rw C).ideal :=
  disjoint_of_leftInverse G (isSCtx_relabelM _ (strictMonoOn_posIn C) (image_posIn C))
    (isSCtx_relabelM _ (strictMonoOn_eltIn C) (image_eltIn C))
    (fun t => Subtype.ext (by
      show (t.1.relabel (posIn C)).relabel (eltIn C) = t.1
      rw [relabel_relabel]
      exact relabel_id fun a ha => eltIn_posIn (t.mem_labels.1 ha)))
    (h C.card)

end Relabel

/-! ## Normal monomials and the Gröbner condition -/

section Groebner

variable {K : Type*} [Field K] {ρ : Type*} {O : AdmOrder F} (G : Rules K ρ O.toCtxOrder)

omit [Fintype (F 2)] [DecidableEq (F 2)] in
lemma isSCtx_cast {A B : Finset ℕ} (h : A = B) :
    IsSCtx (SMono.cast h : SMono F A → SMono F B) := by
  subst h
  rw [cast_rfl]
  exact isSCtx_id _

variable [BinaryGens F]

/-- **The normal monomials correspond**: when the leading monomials of the rules are those of
`L`, a shuffle monomial is normal for the rules exactly when its binary monomial has no window
in `L`. -/
theorem normal_iff (hsrc : ∀ r, G.src r = Finset.range 3) {L : Set (LTree (F 2))}
    (hL : L = Set.range fun r => ofS (G.lead r).1) {n : ℕ} (g : SMono F (Finset.range n)) :
    G.Normal g ↔ LTree.IsNormal L (ofS g.1) := by
  constructor
  · intro hg
    by_contra hn
    obtain ⟨p, s, he, hw⟩ := LTree.not_isNormal_iff.1 hn
    rw [hL] at hw
    obtain ⟨r, hr⟩ := hw
    obtain ⟨f, hf, hfσ⟩ := exists_ctx_of_edge ((monoEquiv F n).symm g) he
    refine hg r (f ∘ SMono.cast (hsrc r)) (isSCtx_comp hf (isSCtx_cast _)) ?_
    have hσ : SMono.cast (hsrc r) (G.lead r) =
        monoEquiv F 3 ⟨ofS (G.lead r).1, ofS_mem (SMono.cast (hsrc r) (G.lead r))⟩ :=
      Subtype.ext (toS_ofS _).symm
    have hm := (LTree.mem_monomials n (ofS g.1)).1 (ofS_mem g)
    rw [Function.comp_apply, hσ, hfσ]
    apply Subtype.ext
    show toS ((ofS g.1).substAt p s (ofS (G.lead r).1)) = g.1
    have hr' : ofS (G.lead r).1 = (ofS g.1).windowAt p s := hr
    rw [hr', LTree.substAt_windowAt he hm.1 (hm.2.nodup_iff.2 List.nodup_range), toS_ofS]
  · intro hn r f hf hfg
    have hf' : IsSCtx (f ∘ SMono.cast (hsrc r).symm) := isSCtx_comp hf (isSCtx_cast _)
    have h0 : (f ∘ SMono.cast (hsrc r).symm) (SMono.cast (hsrc r) (G.lead r)) = g := hfg
    obtain ⟨p, s, he, hw, -⟩ := exists_edge_of_ctx hf' (SMono.cast (hsrc r) (G.lead r))
    rw [h0] at he hw
    exact LTree.not_isNormal_iff.2 ⟨p, s, he, by rw [hL, hw]; exact ⟨r, rfl⟩⟩ hn

/-- **A binary quadratic Gröbner basis makes the normal monomials independent** modulo the
ideal of the rules, on the leaves `0, …, n - 1`. -/
theorem disjoint_range {rk : F 2 → ℕ} {L : Set (LTree (F 2))}
    {R : Submodule K (LTree.Mono (F 2) 3 → K)} (hG : LTree.IsGroebner K rk L R)
    (hsrc : ∀ r, G.src r = Finset.range 3)
    (hR : R.map (vecEquiv F K 3).toLinearMap = Submodule.span K (Set.range (ruleVec G hsrc)))
    (hL : L = Set.range fun r => ofS (G.lead r).1) (n : ℕ) :
    Disjoint (Finsupp.supported K K {t : SMono F (Finset.range n) | G.Normal t})
      (G.rw (Finset.range n)).ideal := by
  rw [Submodule.disjoint_def]
  intro w hw₁ hw₂
  rw [← map_idealOf G hsrc R hR n] at hw₂
  obtain ⟨v, hv, rfl⟩ := hw₂
  have hv0 : v = 0 := hG.indep n v hv fun x hx => by
    have h : (vecEquiv F K n v) (monoEquiv F n x) = 0 := by
      by_contra h
      have hN := (Finsupp.mem_supported K _).1 hw₁ (Finsupp.mem_support_iff.2 h)
      rw [Set.mem_setOf_eq, normal_iff G hsrc hL, monoEquiv_val, ofS_toS] at hN
      exact hx hN
    rwa [vecEquiv_apply, Equiv.symm_apply_apply] at h
  rw [hv0, map_zero]

omit [Fintype (F 2)] [DecidableEq (F 2)] in
/-- A monomial on three leaves with binary generators has two vertices. -/
lemma weight_eq_two {C : Finset ℕ} (hC : C = Finset.range 3) (g : SMono F C) :
    g.1.weight = 2 := by
  have h1 := weight_toS (ofS g.1)
  rw [toS_ofS] at h1
  have h2 : (ofS g.1).arity = 3 := by
    rw [← LTree.length_labels, ← Multiset.coe_card, ← labels_toS, toS_ofS, g.labels_eq, hC]
    rfl
  omega

/-- **A binary quadratic Gröbner basis gives Koszulness with generators of any arity**: if the
binary relators `R` are a quadratic Gröbner basis for the leading monomials `L`, the rules with
the same leading monomials whose vectors span the relators present a Koszul shuffle operad. -/
theorem isKoszul_of_isGroebner {rk : F 2 → ℕ} {L : Set (LTree (F 2))}
    {R : Submodule K (LTree.Mono (F 2) 3 → K)} (hG : LTree.IsGroebner K rk L R)
    (hsrc : ∀ r, G.src r = Finset.range 3)
    (hR : R.map (vecEquiv F K 3).toLinearMap = Submodule.span K (Set.range (ruleVec G hsrc)))
    (hL : L = Set.range fun r => ofS (G.lead r).1) : G.IsKoszul :=
  G.isKoszul_of_critical (fun r => weight_eq_two (hsrc r) _)
    (fun r m _ => weight_eq_two (hsrc r) m)
    fun B _ => B.res_of_isCompl (disjoint_of_range G (disjoint_range G hG hsrc hR hL) _)

/-- **Independence of the normal monomials with generators of any arity gives it on the binary
side**: a vector of the binary ideal supported on the normal monomials vanishes. -/
theorem indep_of_disjoint {L : Set (LTree (F 2))} {R : Submodule K (LTree.Mono (F 2) 3 → K)}
    (hsrc : ∀ r, G.src r = Finset.range 3)
    (hR : R.map (vecEquiv F K 3).toLinearMap = Submodule.span K (Set.range (ruleVec G hsrc)))
    (hL : L = Set.range fun r => ofS (G.lead r).1) {n : ℕ}
    (h : Disjoint (Finsupp.supported K K {t : SMono F (Finset.range n) | G.Normal t})
      (G.rw (Finset.range n)).ideal)
    (v : LTree.Mono (F 2) n → K) (hv : v ∈ LTree.idealOf K R n)
    (hs : v ∈ supportedOn K (LTree.normalSet L n)) : v = 0 := by
  have h0 : vecEquiv F K n v = 0 := by
    refine Submodule.disjoint_def.1 h _ ((Finsupp.mem_supported K _).2 fun y hy => ?_) ?_
    · have hy' : v ((monoEquiv F n).symm y) ≠ 0 := by
        rwa [Finset.mem_coe, Finsupp.mem_support_iff, vecEquiv_apply] at hy
      have hN : LTree.IsNormal L ((monoEquiv F n).symm y).1 := by
        by_contra hN
        exact hy' (hs _ hN)
      rw [monoEquiv_symm_val, ← normal_iff G hsrc hL] at hN
      exact hN
    · rw [← map_idealOf G hsrc R hR n]
      exact Submodule.mem_map_of_mem hv
  exact (vecEquiv F K n).map_eq_zero_iff.1 h0

/-- **A binary quadratic Gröbner basis makes the rules resolvable** on every set of leaves. -/
theorem resolvable_of_isGroebner {rk : F 2 → ℕ} {L : Set (LTree (F 2))}
    {R : Submodule K (LTree.Mono (F 2) 3 → K)} (hG : LTree.IsGroebner K rk L R)
    (hsrc : ∀ r, G.src r = Finset.range 3)
    (hR : R.map (vecEquiv F K 3).toLinearMap = Submodule.span K (Set.range (ruleVec G hsrc)))
    (hL : L = Set.range fun r => ofS (G.lead r).1) (C : Finset ℕ) : (G.rw C).Resolvable :=
  Rewriting.resolvable_of_disjoint (by
    rw [G.irr_eq]
    exact disjoint_of_range G (disjoint_range G hG hsrc hR hL) C)

/-- **Conversely, resolvable rules give a binary quadratic Gröbner basis**, when every monomial
of `L` leads a relator: the independence of the normal monomials passes from the rules to the
relators. -/
theorem isGroebner_of_resolvable {rk : F 2 → ℕ} {L : Set (LTree (F 2))}
    {R : Submodule K (LTree.Mono (F 2) 3 → K)} (hsrc : ∀ r, G.src r = Finset.range 3)
    (hR : R.map (vecEquiv F K 3).toLinearMap = Submodule.span K (Set.range (ruleVec G hsrc)))
    (hL : L = Set.range fun r => ofS (G.lead r).1) (hmem : ∀ ℓ ∈ L, ℓ ∈ LTree.monomials 3)
    (hlead : ∀ ℓ (hℓ : ℓ ∈ L), ∃ r ∈ R, r ⟨ℓ, hmem ℓ hℓ⟩ ≠ 0 ∧
      ∀ σ : LTree.Mono (F 2) 3, σ.1 ≠ ℓ → r σ ≠ 0 → LTree.pathKey rk 3 σ.1 < LTree.pathKey rk 3 ℓ)
    (hres : ∀ C, (G.rw C).Resolvable) : LTree.IsGroebner K rk L R where
  mem := hmem
  lead := hlead
  indep n v hv hs := indep_of_disjoint G hsrc hR hL (by
    rw [← G.irr_eq]
    exact (hres _).isCompl.disjoint) v hv hs

/-- **One binary Gröbner basis gives both Koszulness predicates**: the binary shuffle operad of
the relators, by the criterion of Dotsenko and Khoroshkin, and the shuffle operad of the rules,
through the bridge. -/
theorem isKoszul_and_of_isGroebner {rk : F 2 → ℕ} {L : Set (LTree (F 2))}
    {R : Submodule K (LTree.Mono (F 2) 3 → K)} (hG : LTree.IsGroebner K rk L R)
    (hsrc : ∀ r, G.src r = Finset.range 3)
    (hR : R.map (vecEquiv F K 3).toLinearMap = Submodule.span K (Set.range (ruleVec G hsrc)))
    (hL : L = Set.range fun r => ofS (G.lead r).1) : ShuffleBar.IsKoszul K R ∧ G.IsKoszul :=
  ⟨ShuffleBar.isKoszul K rk hG, isKoszul_of_isGroebner G hG hsrc hR hL⟩

/-- **Resolvable rules make the binary relators Koszul**, when every monomial of `L` leads a
relator for the path-lexicographic key of `rk`. -/
theorem shuffleBar_isKoszul_of_resolvable {rk : F 2 → ℕ} {L : Set (LTree (F 2))}
    {R : Submodule K (LTree.Mono (F 2) 3 → K)} (hsrc : ∀ r, G.src r = Finset.range 3)
    (hR : R.map (vecEquiv F K 3).toLinearMap = Submodule.span K (Set.range (ruleVec G hsrc)))
    (hL : L = Set.range fun r => ofS (G.lead r).1) (hmem : ∀ ℓ ∈ L, ℓ ∈ LTree.monomials 3)
    (hlead : ∀ ℓ (hℓ : ℓ ∈ L), ∃ r ∈ R, r ⟨ℓ, hmem ℓ hℓ⟩ ≠ 0 ∧
      ∀ σ : LTree.Mono (F 2) 3, σ.1 ≠ ℓ → r σ ≠ 0 → LTree.pathKey rk 3 σ.1 < LTree.pathKey rk 3 ℓ)
    (hres : ∀ C, (G.rw C).Resolvable) : ShuffleBar.IsKoszul K R :=
  ShuffleBar.isKoszul K rk (isGroebner_of_resolvable G hsrc hR hL hmem hlead hres)

/-- **The vector of a rule with a single tail monomial**, through the bridge. -/
lemma ruleVec_eq (hsrc : ∀ r, G.src r = Finset.range 3) (r : ρ) {a b : LTree (F 2)}
    (ha : a ∈ LTree.monomials 3) (hb : b ∈ LTree.monomials 3) (hlead : ofS (G.lead r).1 = a)
    {τ : SMono F (G.src r)} (htail : G.tail r = Finsupp.single τ 1) (hτ : ofS τ.1 = b) :
    ruleVec G hsrc r = vecEquiv F K 3 (LTree.vecOf K 3 a - LTree.vecOf K 3 b) := by
  rw [map_sub, vecEquiv_vecOf K ha, vecEquiv_vecOf K hb, ruleVec, htail, Finsupp.mapDomain_sub,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  congr 2
  · exact Subtype.ext (by
      show (G.lead r).1 = toS a
      rw [← hlead, toS_ofS])
  · exact Subtype.ext (by
      show τ.1 = toS b
      rw [← hτ, toS_ofS])

end Groebner

/-! ## The commutative and associative operads through the bridge -/

instance : BinaryGens ComGen := ⟨fun _ hk => ⟨fun e => by cases e; exact hk rfl⟩⟩

instance : BinaryGens AssShGen := ⟨fun _ hk => ⟨fun e => by cases e <;> exact hk rfl⟩⟩

end ShuffleBridge

namespace ComBin

open ShuffleBridge

variable (K : Type*) [Field K]

lemma src_rules (r : Bool) : (ComGen.rules K).src r = Finset.range 3 := rfl

lemma leads_eq : leads = Set.range fun r => ofS ((ComGen.rules K).lead r).1 := by
  ext ℓ
  constructor
  · rintro (rfl | rfl)
    exacts [⟨true, rfl⟩, ⟨false, rfl⟩]
  · rintro ⟨_ | _, rfl⟩
    exacts [Or.inr rfl, Or.inl rfl]

lemma map_rel :
    (rel K).map (vecEquiv ComGen K 3).toLinearMap =
      Submodule.span K (Set.range (ruleVec (ComGen.rules K) (src_rules K))) := by
  have hl : ruleVec (ComGen.rules K) (src_rules K) true =
      vecEquiv ComGen K 3 (LTree.vecOf K 3 lcomb - LTree.vecOf K 3 rcomb) :=
    ruleVec_eq _ _ true lcomb_mem rcomb_mem rfl rfl rfl
  have ht : ruleVec (ComGen.rules K) (src_rules K) false =
      vecEquiv ComGen K 3 (LTree.vecOf K 3 tcomb - LTree.vecOf K 3 rcomb) :=
    ruleVec_eq _ _ false tcomb_mem rcomb_mem rfl rfl rfl
  rw [rel_eq_span, Submodule.map_span, Set.image_pair]
  congr 1
  ext v
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Bool.exists_bool, ← hl,
    ← ht, LinearEquiv.coe_coe]
  exact ⟨fun h => h.elim (fun h => Or.inr h.symm) fun h => Or.inl h.symm,
    fun h => h.elim (fun h => Or.inr h.symm) fun h => Or.inl h.symm⟩

/-- **The commutative operad is Koszul in both shuffle senses, through the bridge**: the binary
Gröbner basis `ComBin.isGroebner` alone gives `ComBin.isKoszul_and` again. -/
theorem isKoszul_and_bridge : ShuffleBar.IsKoszul K (rel K) ∧ (ComGen.rules K).IsKoszul :=
  isKoszul_and_of_isGroebner _ (isGroebner K) (src_rules K) (map_rel K) (leads_eq K)

/-- **The two presentations of the commutative operad agree** arity by arity. -/
theorem map_idealOf_rel (n : ℕ) :
    (LTree.idealOf K (rel K) n).map (vecEquiv ComGen K n).toLinearMap =
      ((ComGen.rules K).rw (Finset.range n)).ideal :=
  ShuffleBridge.map_idealOf _ (src_rules K) _ (map_rel K) n

end ComBin

namespace AssBin

open ShuffleBridge AssShGen

variable (K : Type*) [Field K]

lemma src_rules (r : Rule) : (AssShGen.rules K).src r = Finset.range 3 := rfl

lemma ofS_leadOf (e f : AssShGen 2) (s : Bool) : ofS (leadOf e f s).1 = lead3 e f s := by
  cases s <;> rfl

lemma ofS_tailOf (e f : AssShGen 2) (s : Bool) : ofS (tailOf e f s).1 = tail3 e f s := by
  cases e <;> cases f <;> cases s <;> rfl

lemma leads_eq : leads = Set.range fun r => ofS ((AssShGen.rules K).lead r).1 := by
  ext ℓ
  constructor
  · rintro ⟨e, f, s, hef, rfl⟩
    exact ⟨(⟨(e, f), hef⟩, s), ofS_leadOf e f s⟩
  · rintro ⟨⟨⟨⟨e, f⟩, hef⟩, s⟩, rfl⟩
    exact ⟨e, f, s, hef, ofS_leadOf e f s⟩

lemma map_rel :
    (rel K).map (vecEquiv AssShGen K 3).toLinearMap =
      Submodule.span K (Set.range (ruleVec (AssShGen.rules K) (src_rules K))) := by
  rw [rel_eq_span, Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span K) (congrArg Set.range (funext fun r => ?_))
  exact (ruleVec_eq _ _ r (lead3_mem _ _ _) (tail3_mem _ _ _)
    (ofS_leadOf r.1.1.1 r.1.1.2 r.2) rfl (ofS_tailOf r.1.1.1 r.1.1.2 r.2)).symm

/-- **The associative operad is Koszul in both shuffle senses, through the bridge**: the binary
Gröbner basis `AssBin.isGroebner` alone gives `AssBin.isKoszul_and` again. -/
theorem isKoszul_and_bridge : ShuffleBar.IsKoszul K (rel K) ∧ (AssShGen.rules K).IsKoszul :=
  isKoszul_and_of_isGroebner _ (isGroebner K) (src_rules K) (map_rel K) (leads_eq K)

/-- **The two presentations of the associative operad agree** arity by arity. -/
theorem map_idealOf_rel (n : ℕ) :
    (LTree.idealOf K (rel K) n).map (vecEquiv AssShGen K n).toLinearMap =
      ((AssShGen.rules K).rw (Finset.range n)).ideal :=
  ShuffleBridge.map_idealOf _ (src_rules K) _ (map_rel K) n

end AssBin

end Operad
