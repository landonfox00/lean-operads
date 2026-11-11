/-
# The relator ideal of the bar construction in shuffle coordinates

Step (2c) of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin), last part.
Let `E` be a graded linear species over a field `K` with an even basis `c k` of each `E (Fin k)`
indexed by `BinGen G k`, `T = FreeGrL K E`, `Ī` its ideal of the operations with at least two
inputs, and relators `r` concentrated in arity three, spanning a subspace of `T (Fin 3)` stable
under the permutations of `Fin 3`. This file proves the identification `hJ` of
`ShuffleBarSym.isKoszul_iff_shuffle_of_J`, `ΦL (Krel) = ShuffleBar.J K (Rsh c hc r) ⊓ supported
(barSet G n)` (`ShuffleBarSym.map_ΦL_Krel`), hence **the bridge**
`ShuffleBarSym.isKoszul_iff_shuffle`: over a field of characteristic zero, `Pres K E r` is Koszul
iff the shuffle operad presented by `Rsh c hc r` is (`ShuffleBar.IsKoszul`).

* **The sign does not see the vertex labels** (`ShuffleBarSym.sign_mapV`,
  `ShuffleBarSym.sign_replace`): `preKeys` uses only the leaves of the subtrees.
* **Uncut edges** (`ShuffleBarSym.toBar_replace_substAt`, `ShuffleBarSym.exists_of_isUncut`): the
  edges `(p, s)` of the monomial at the vertex `q` of a shuffle tree `t` are the uncut edges of
  `toBar t`, at the position `ShuffleBarSym.barPath t q p`, and substituting a monomial of arity
  three there in the vertex monomial is substituting it at that uncut edge of the bar tree
  (`ShuffleBar.substBar`); every uncut edge of `toBar t` arises so.
* **A vertex labelled by an operation** (`ShuffleBarSym.Tq`): the trees with the vertex at `q`
  labelled by each basis monomial, with the coordinates of an operation `y ∈ T (Fin k)`. For `y` in
  the ideal `(r)` they lie in the relator ideal `Krel` (`ShuffleBarSym.Tq_mem_Krel`: the
  projection `B(T, Ī) → B(P, Ī_P)` is linear in the label of one vertex,
  `FreeGrL.mapSp_sum_shEv_replace`), and `ΦL` sends them into `ShuffleBar.J`
  (`ShuffleBarSym.ΦL_Tq_mem_J`: in shuffle coordinates `y` is a combination of relators in
  contexts, `ShuffleBarSym.span_le_relIdeal`, and a relator substituted in the vertex monomial is
  a substituted relator of the bar tree, `ShuffleBarSym.ΦL_Tq_relator`).
* **The kernel of the projection** is spanned by these trees: choosing basis monomials `S k` whose
  images form a basis of `sĪ_P (Fin k)` (`ShuffleBarSym.exists_sel`), the projection is injective
  on the trees with all vertex labels in `S` (`ShuffleBarSym.eq_zero_of_mem_sel`, their images
  being the shuffle basis of `B(P, Ī_P)`), and every tree is a combination of those modulo the trees
  labelled at one vertex by `(r)` (`ShuffleBarSym.barBasisN_mem_sup`, by induction on the number of
  vertices with labels outside `S`, `ShuffleBarSym.nS`).
* **The relator subcomplex comes from the relator ideal**: a substituted relator at an uncut edge
  of `toBar t` is `ΦL` of the trees labelled at that vertex by the relator in the context of the
  vertex monomial, which lies in `(r)` (`ShuffleBarSym.ShIT_le`).
-/
import Operad.ShuffleRelIdeal

universe u v w x

namespace Operad

open Function Sym GerBV STree

namespace STree

variable {B : ℕ → Type w} {B' : ℕ → Type x}

/-- **Relabelling the vertices commutes with replacing a subtree.** -/
lemma mapV_replace (g : ∀ k, B k → B' k) :
    ∀ (q : List ℕ) (t u : STree B), (t.replace q u).mapV g = (t.mapV g).replace q (u.mapV g)
  | [], t, u => by simp
  | _ :: _, leaf _, _ => rfl
  | i :: q, node β c, u => by
    rw [replace_node_cons, mapV_node, mapV_node, replace_node_cons]
    congr 1
    funext j
    split_ifs
    · exact mapV_replace g q (c j) u
    · rfl

end STree

namespace ShuffleBarSym

open LTree ShuffleBar

/-! ## The sign does not see the vertex labels -/

section Sign

variable {B : ℕ → Type w} {B' : ℕ → Type x}

lemma vkey_mapV (g : ∀ k, B k → B' k) (t : STree B) : vkey (t.mapV g) = vkey t := by
  simp only [vkey, first_mapV, labels_mapV]

lemma preKeys_mapV (g : ∀ k, B k → B' k) : ∀ t : STree B, preKeys (t.mapV g) = preKeys t
  | .leaf _ => rfl
  | .node β c => by
    rw [mapV_node, preKeys_node, preKeys_node, ← mapV_node, vkey_mapV]
    exact congrArg _ (congrArg _ (List.ofFn_inj.2 (funext fun j => preKeys_mapV g (c j))))

variable (K : Type u) [CommRing K]

/-- **The sign of a tree does not see its vertex labels.** -/
lemma sign_mapV (g : ∀ k, B k → B' k) (t : STree B) : sign K (t.mapV g) = sign K t := by
  rw [sign, sign, preKeys_mapV]

/-- **Relabelling one vertex keeps the sign.** -/
lemma sign_replace {k : ℕ} (q : List ℕ) (t : STree B) (β β' : B k) (ch : Fin k → STree B) :
    sign K (t.replace q (.node β ch)) = sign K (t.replace q (.node β' ch)) := by
  rw [← sign_mapV K (fun _ _ => ()) (t.replace q _),
    ← sign_mapV K (fun _ _ => ()) (t.replace q (.node β' ch)), mapV_replace, mapV_replace]
  rfl

end Sign

/-! ## Counting the vertices outside a set of labels -/

section Count

variable {G : Type} [Fintype G] [DecidableEq G] (S : ∀ k, Set (VMono G k))

open Classical in
/-- **The number of vertices whose label is not in `S`.** -/
noncomputable def nS : STree (VMono G) → ℕ
  | .leaf _ => 0
  | .node (k := k) m ch => (if m ∈ S k then 0 else 1) + ∑ j, nS (ch j)

open Classical in
lemma nS_node {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G)) :
    nS S (.node m ch) = (if m ∈ S k then 0 else 1) + ∑ j, nS S (ch j) := by
  rw [nS]

lemma mem_of_nS_node {k : ℕ} {m : VMono G k} {ch : Fin k → STree (VMono G)}
    (h : nS S (.node m ch) = 0) : m ∈ S k := by
  classical
  rw [nS_node] at h
  by_contra hm
  rw [if_neg hm] at h
  omega

lemma nS_child {k : ℕ} {m : VMono G k} {ch : Fin k → STree (VMono G)}
    (h : nS S (.node m ch) = 0) (j : Fin k) : nS S (ch j) = 0 := by
  rw [nS_node] at h
  exact (Finset.sum_eq_zero_iff.1 (Nat.add_eq_zero_iff.1 h).2) j (Finset.mem_univ j)

open Classical in
/-- **Relabelling one vertex** changes the count by the membership of the two labels. -/
lemma nS_replace {k : ℕ} (m m' : VMono G k) (ch : Fin k → STree (VMono G)) :
    ∀ (q : List ℕ) (t : STree (VMono G)), t.get? q = some (.node m ch) →
      nS S (t.replace q (.node m' ch)) + (if m ∈ S k then 0 else 1)
        = nS S t + (if m' ∈ S k then 0 else 1)
  | [], t, ht => by
    rw [get?_nil, Option.some_inj] at ht
    subst ht
    rw [replace_nil, nS_node, nS_node]
    omega
  | _ :: _, .leaf _, ht => by simp at ht
  | i :: q, .node (k := k') γ c, ht => by
    obtain ⟨hi, hc⟩ := get?_node_cons_eq_some.1 ht
    have ih := nS_replace m m' ch q _ hc
    rw [replace_node_cons, nS_node, nS_node]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨i, hi⟩ : Fin k')),
      ← Finset.add_sum_erase _ (fun j => nS S (c j)) (Finset.mem_univ (⟨i, hi⟩ : Fin k'))]
    have hrest : ∑ j ∈ Finset.univ.erase (⟨i, hi⟩ : Fin k'), nS S (if (j : ℕ) = i then
        (c j).replace q (.node m' ch) else c j)
          = ∑ j ∈ Finset.univ.erase (⟨i, hi⟩ : Fin k'), nS S (c j) :=
      Finset.sum_congr rfl fun j hj => by
        rw [if_neg fun h => Finset.ne_of_mem_erase hj (Fin.ext h)]
    rw [hrest, if_pos rfl]
    omega

/-- **A tree with a vertex outside `S` has one at some position.** -/
lemma exists_get?_not_mem : ∀ t : STree (VMono G), nS S t ≠ 0 →
    ∃ (q : List ℕ) (k : ℕ) (m : VMono G k) (ch : Fin k → STree (VMono G)),
      t.get? q = some (.node m ch) ∧ m ∉ S k
  | .leaf _, h => absurd rfl h
  | .node (k := k) m ch, h => by
    by_cases hm : m ∈ S k
    · obtain ⟨j, hj⟩ : ∃ j, nS S (ch j) ≠ 0 := by
        by_contra hall
        exact h (by
          classical
          rw [nS_node, if_pos hm, Finset.sum_eq_zero fun j _ => not_not.1 fun hj => hall ⟨j, hj⟩]
          rfl)
      obtain ⟨q, k', m', ch', hq, hm'⟩ := exists_get?_not_mem (ch j) hj
      exact ⟨j.1 :: q, k', m', ch', by rw [get?_node_cons_fin]; exact hq, hm'⟩
    · exact ⟨[], k, m, ch, get?_nil _, hm⟩

/-- **The tree over `S` of a tree with all vertices in `S`.** -/
noncomputable def liftS : (t : STree (VMono G)) → nS S t = 0 → STree fun k => ↥(S k)
  | .leaf a, _ => .leaf a
  | .node m ch, h => .node ⟨m, mem_of_nS_node S h⟩ fun j => liftS (ch j) (nS_child S h j)

lemma mapV_liftS : ∀ (t : STree (VMono G)) (h : nS S t = 0),
    (liftS S t h).mapV (fun _ m => m.1) = t
  | .leaf _, _ => rfl
  | .node m ch, h => by
    show STree.node m (fun j => (liftS S (ch j) (nS_child S h j)).mapV _) = _
    congr 1
    funext j
    exact mapV_liftS (ch j) _

end Count

end ShuffleBarSym

namespace ShuffleBarSym

open LTree ShuffleBar

/-! ## Uncut edges of the bar tree and edges of the vertex monomials -/

section BarPath

variable {G : Type}

lemma isEdgeRoot_cutRoot (y : BarTree G) (s : Bool) :
    (cutRoot y).IsEdgeRoot s ↔ y.IsEdgeRoot s := by
  rcases y with _ | ⟨d, l, r⟩
  · exact Iff.rfl
  · rcases l with _ | _ <;> rcases r with _ | _ <;> rcases s with _ | _ <;> exact Iff.rfl

lemma subtreeAt_cutRoot (y : BarTree G) {P : List Bool} (hP : P ≠ []) :
    (cutRoot y).subtreeAt P = y.subtreeAt P := by
  rcases y with _ | ⟨d, l, r⟩
  · rfl
  · rcases P with _ | ⟨_ | _, P⟩
    · exact absurd rfl hP
    · rfl
    · rfl

lemma isEdge_cutRoot (y : BarTree G) (P : List Bool) (s : Bool) :
    (cutRoot y).IsEdge P s ↔ y.IsEdge P s := by
  unfold IsEdge
  rcases P with _ | P
  · rw [subtreeAt_nil, subtreeAt_nil, isEdgeRoot_cutRoot]
  · rw [subtreeAt_cutRoot y (List.cons_ne_nil _ _)]

lemma isUncut_cutRoot {y : BarTree G} {P : List Bool} {s : Bool} :
    IsUncut (cutRoot y) P s ↔ IsUncut y P s := by
  unfold IsUncut flagAt
  rw [isEdge_cutRoot, subtreeAt_cutRoot y (by simp)]

lemma winIns_cutRoot {y : BarTree G} {s : Bool} (h : y.IsEdgeRoot s) :
    (cutRoot y).winIns s = y.winIns s := by
  match y, s, h with
  | LTree.node d (LTree.node f a b) c, false, _ => rfl
  | LTree.node d c (LTree.node f a b), true, _ => cases c <;> rfl

lemma rootFlag_liftW_node (c : Bool) {σ : LTree G} (hσ : ∃ e l r, σ = node e l r) :
    rootFlag (liftW c σ) = c := by
  obtain ⟨e, l, r, rfl⟩ := hσ
  rfl

/-- **Cutting the root commutes with substituting at an uncut edge.** -/
lemma cutRoot_substBar {y : BarTree G} {P : List Bool} {s : Bool} (he : y.IsEdge P s)
    {σ : LTree G} (hσ : ∃ e l r, σ = node e l r) :
    cutRoot (substBar y P s σ) = substBar (cutRoot y) P s σ := by
  obtain ⟨d, l, r, hy⟩ : ∃ d l r, y = node d l r := by
    rcases y with _ | ⟨d, l, r⟩
    · exfalso
      unfold IsEdge at he
      rw [subtreeAt_leaf] at he
      rcases s <;> exact he
    · exact ⟨d, l, r, rfl⟩
  subst hy
  obtain ⟨e, a, b, rfl⟩ := hσ
  rcases P with _ | ⟨_ | _, P⟩
  · have hw := winIns_cutRoot (y := node d l r) (s := s) he
    simp only [substBar, substAt, flagAt, subtreeAt_nil, replaceAt_nil, hw]
    rfl
  · rfl
  · rfl

lemma flagAt_plug_liftW {m : LTree G} {P : List Bool} (F : ℕ → BarTree G)
    (h : ∃ e l r, m.subtreeAt P = node e l r) : flagAt ((liftW false m).plug F) P = false := by
  obtain ⟨e, l, r, h⟩ := h
  have hv : ValidPath (liftW false m) P := validPath_of_node _ P (by
    rw [liftW_false_eq, unflag, subtreeAt_mapDec, h]
    exact ⟨_, _, _, rfl⟩)
  unfold flagAt
  rw [subtreeAt_plug F _ P hv, liftW_false_eq, unflag, subtreeAt_mapDec, h]
  rfl

lemma exists_node_slot {u : LTree G} {s : Bool} (h : u.IsEdgeRoot s) :
    ∃ e l r, u.subtreeAt [s] = node e l r := by
  match u, s, h with
  | LTree.node _ (LTree.node e l r) _, false, _ => exact ⟨e, l, r, rfl⟩
  | LTree.node _ _ (LTree.node e l r), true, _ => exact ⟨e, l, r, rfl⟩

variable [Fintype G] [DecidableEq G]

/-- The edge monomial `m[(p, s) := σ]` of a vertex label with an edge `(p, s)`. -/
def VMono.substAt {k : ℕ} (m : VMono G k) {p : List Bool} {s : Bool}
    (he : m.1.IsEdge p s) (σ : Mono G 3) : VMono G k :=
  ⟨m.1.substAt p s σ.1, substAt_mem_monomials m.2.1 he σ.2, m.2.2⟩

/-- **The position in the bar tree of an edge of a vertex monomial**: through the leaves of the
monomials above it, down to the vertex at `q`, then along the path `p` of the edge in its
monomial. -/
def barPath : STree (VMono G) → List ℕ → List Bool → List Bool
  | _, [], p => p
  | .leaf _, _ :: _, p => p
  | .node (k := k) m ch, i :: q, p =>
    if h : i < k then leafPos i (liftW false m.1) ++ barPath (ch ⟨i, h⟩) q p else p

lemma nodup_liftW {k : ℕ} (m : VMono G k) : (liftW false m.1).labels.Nodup := by
  rw [labels_liftW]
  exact m.perm.nodup_iff.2 List.nodup_range

/-- **An edge of a vertex monomial is an uncut edge of the bar tree**, and substituting a monomial
of arity three in the vertex monomial is substituting it at that edge of the bar tree. -/
theorem toBar_replace_substAt {k : ℕ} (m : VMono G k) (ch : Fin k → STree (VMono G))
    {p : List Bool} {s : Bool} (he : m.1.IsEdge p s) :
    ∀ (q : List ℕ) (t : STree (VMono G)), t.IsShuffle → t.get? q = some (.node m ch) →
      IsUncut (toBar t) (barPath t q p) s ∧ ∀ σ : Mono G 3,
        toBar (t.replace q (.node (m.substAt he σ) ch)) = substBar (toBar t) (barPath t q p) s σ.1
  | [], t, ht, hq => by
    rw [get?_nil, Option.some_inj] at hq
    subst hq
    have hmono := strictOn_kids m (fun j => minLabel_toBar (ch j) (ht.child j)) ht.mono
    have he' : (liftW false m.1).IsEdge p s := by
      rw [liftW_false_eq, unflag, isEdge_mapDec]
      exact he
    have hslot : ∃ e l r, m.1.subtreeAt (p ++ [s]) = node e l r := by
      rw [subtreeAt_append]
      exact exists_node_slot he
    show IsUncut ((liftW false m.1).plug (kids ch)) p s ∧ ∀ σ : Mono G 3,
      (liftW false (m.1.substAt p s σ.1)).plug (kids ch)
        = substBar ((liftW false m.1).plug (kids ch)) p s σ.1
    refine ⟨⟨by simpa using isEdge_ctx (M := LTree.leaf 0) (q := []) trivial (kids ch) he',
      flagAt_plug_liftW _ hslot⟩, fun σ => ?_⟩
    rw [substBar, flagAt_plug_liftW _ he.exists_node]
    have := substAt_ctx (M := LTree.leaf 0) (q := []) trivial (kids ch) he' hmono
      (liftW false σ.1)
    simp only [replaceAt_nil, List.nil_append] at this
    rw [this, liftW_false_eq, liftW_false_eq, liftW_false_eq, unflag, unflag, unflag,
      substAt_mapDec _ _ _ _ he]
  | _ :: _, .leaf _, _, hq => by simp at hq
  | i :: q, .node (k := k') γ c, ht, hq => by
    obtain ⟨hi, hc⟩ := get?_node_cons_eq_some.1 hq
    let ii : Fin k' := ⟨i, hi⟩
    obtain ⟨hU, heq⟩ := toBar_replace_substAt m ch he q (c ii) (ht.child ii) hc
    have hP : barPath (.node γ c) (i :: q) p = leafPos i (liftW false γ.1) ++ barPath (c ii) q p :=
      dif_pos hi
    have hj : i ∈ (liftW false γ.1).labels := by
      rw [labels_liftW]
      exact γ.mem hi
    have hki : kids c i = cutRoot (toBar (c ii)) := kids_of_lt c hi
    rw [hP]
    show IsUncut ((liftW false γ.1).plug (kids c)) _ s ∧ ∀ σ : Mono G 3,
      toBar (.node γ fun j => if (j : ℕ) = i then (c j).replace q _ else c j) = _
    have hU' : IsUncut (kids c i) (barPath (c ii) q p) s := by
      rw [hki, isUncut_cutRoot]
      exact hU
    refine ⟨⟨by simpa using isEdge_ctx_ins (M := LTree.leaf 0) (q := []) trivial (kids c) hj hU'.1,
      ?_⟩, fun σ => ?_⟩
    · unfold flagAt
      rw [List.append_assoc, subtreeAt_plug_leafPos (kids c) hj]
      exact hU'.2
    · simp only [toBar_node, substBar]
      have hfl : flagAt ((liftW false γ.1).plug (kids c))
          (leafPos i (liftW false γ.1) ++ barPath (c ii) q p)
            = flagAt (kids c i) (barPath (c ii) q p) := by
        unfold flagAt
        rw [subtreeAt_plug_leafPos (kids c) hj]
      have := substAt_ctx_ins (M := LTree.leaf 0) (q := []) trivial (kids c) (nodup_liftW γ) hj
        (barPath (c ii) q p) s (liftW (flagAt (kids c i) (barPath (c ii) q p)) σ.1)
      simp only [replaceAt_nil, List.nil_append] at this
      rw [hfl, this]
      refine LTree.plug_congr fun a ha => ?_
      rw [labels_liftW] at ha
      have ha' := γ.lt ha
      by_cases hai : a = i
      · subst hai
        rw [update_self, kids_of_lt _ ha', if_pos rfl, heq σ, hki,
          cutRoot_substBar hU.1 (ShuffleBar.mono_shape σ).2.2]
        rfl
      · rw [update_of_ne hai, kids_of_lt _ ha', kids_of_lt _ ha', if_neg hai]

lemma isEdgeRoot_false_iff {X : Type*} (e : X) (l r : LTree X) :
    (LTree.node e l r).IsEdgeRoot false ↔ ∃ e' a b, l = LTree.node e' a b := by
  rcases l with _ | ⟨e', a, b⟩
  · rcases r with _ | _ <;> simp [IsEdgeRoot]
  · simp [IsEdgeRoot]

lemma isEdgeRoot_true_iff {X : Type*} (e : X) (l r : LTree X) :
    (LTree.node e l r).IsEdgeRoot true ↔ ∃ e' a b, r = LTree.node e' a b := by
  rcases r with _ | ⟨e', a, b⟩
  · rcases l with _ | _ <;> simp [IsEdgeRoot]
  · exact iff_of_true (isEdgeRoot_true _ _ _ _ _) ⟨e', a, b, rfl⟩

/-- **A grafted input which is a vertex is cut above.** -/
lemma rootFlag_kids {k : ℕ} (ch : Fin k → STree (VMono G)) (j : ℕ)
    (h : ∃ e a b, kids ch j = LTree.node e a b) : rootFlag (kids ch j) = true := by
  obtain ⟨e, a, b, h⟩ := h
  unfold kids at h ⊢
  by_cases hj : j < k
  · rw [dif_pos hj] at h ⊢
    revert h
    rcases toBar (ch ⟨j, hj⟩) with _ | ⟨d, l, r⟩
    · intro h
      simp [cutRoot] at h
    · intro _
      rfl
  · rw [dif_neg hj] at h
    cases h

/-- **Every uncut edge of the bar tree is an edge of a vertex monomial.** -/
theorem exists_of_isUncut : ∀ (t : STree (VMono G)), t.IsShuffle → ∀ {P : List Bool} {s : Bool},
    IsUncut (toBar t) P s → ∃ (q : List ℕ) (k : ℕ) (m : VMono G k)
      (ch : Fin k → STree (VMono G)) (p : List Bool),
      t.get? q = some (.node m ch) ∧ m.1.IsEdge p s ∧ P = barPath t q p
  | .leaf _, _, P, s, h => by
    exfalso
    have := h.1
    unfold IsEdge at this
    rw [show toBar (STree.leaf _ : STree (VMono G)) = LTree.leaf _ from rfl, subtreeAt_leaf]
      at this
    rcases s <;> exact this
  | .node (k := k) m ch, ht, P, s, h => by
    rw [toBar_node] at h
    have hnd := nodup_liftW m
    rcases pos_cases (liftW false m.1) P hnd with ⟨e, l, r, hPn⟩ | ⟨j, hj, d, rfl⟩
    · refine ⟨[], k, m, ch, P, get?_nil _, ?_, rfl⟩
      have hv : ValidPath (liftW false m.1) P := validPath_of_node _ P ⟨e, l, r, hPn⟩
      have hX : ((liftW false m.1).plug (kids ch)).subtreeAt P
          = LTree.node e (l.plug (kids ch)) (r.plug (kids ch)) := by
        rw [subtreeAt_plug _ _ P hv, hPn]
        rfl
      have hE := h.1
      unfold IsEdge at hE
      rw [hX] at hE
      have hfl := h.2
      unfold flagAt at hfl
      rw [subtreeAt_append, hX] at hfl
      rw [← isEdge_mapDec (·, false), ← unflag, ← liftW_false_eq]
      unfold IsEdge
      rw [hPn]
      have hslot : ∀ w : BarTree G, (∃ e' a b, w.plug (kids ch) = LTree.node e' a b) →
          rootFlag (w.plug (kids ch)) = false → ∃ e' a b, w = LTree.node e' a b := by
        intro w hw hf
        rcases w with ⟨a⟩ | ⟨e', a, b⟩
        · have h1 : rootFlag (kids ch a) = true := rootFlag_kids ch a hw
          have h2 : rootFlag (kids ch a) = false := hf
          rw [h1] at h2
          exact absurd h2 (by decide)
        · exact ⟨e', a, b, rfl⟩
      rcases s with _ | _
      · rw [isEdgeRoot_false_iff] at hE ⊢
        exact hslot l hE (by simpa [subtreeAt] using hfl)
      · rw [isEdgeRoot_true_iff] at hE ⊢
        exact hslot r hE (by simpa [subtreeAt] using hfl)
    · rw [labels_liftW] at hj
      have hjk := m.lt hj
      let jj : Fin k := ⟨j, hjk⟩
      have hj' : j ∈ (liftW false m.1).labels := by rwa [labels_liftW]
      have hU : IsUncut (kids ch j) d s := by
        refine ⟨?_, ?_⟩
        · have := h.1
          unfold IsEdge at this ⊢
          rwa [subtreeAt_plug_leafPos _ hj'] at this
        · have := h.2
          unfold flagAt at this ⊢
          rwa [List.append_assoc, subtreeAt_plug_leafPos _ hj'] at this
      rw [kids_of_lt ch hjk, isUncut_cutRoot] at hU
      obtain ⟨q, k', m', ch', p, hq, he, hd⟩ := exists_of_isUncut (ch jj) (ht.child jj) hU
      refine ⟨j :: q, k', m', ch', p, by rw [get?_node_cons, dif_pos hjk]; exact hq, he, ?_⟩
      show _ = (if h : j < k then _ else _)
      rw [dif_pos hjk, hd]

end BarPath

end ShuffleBarSym

namespace ShuffleBarSym

open LTree ShuffleBar

/-! ## A vertex labelled by an operation -/

section Vertex

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))

local notation "𝒥" => GrOperadIdeal.span K r

variable {n : ℕ} (t : SMono (VMono G) (Finset.range n)) {q : List ℕ} {k : ℕ} {m₀ : VMono G k}
  {ch : Fin k → STree (VMono G)} (hq : t.1.get? q = some (.node m₀ ch))

/-- **The tree with the vertex at `q` relabelled by `m`.** -/
def replT (m : VMono G k) : SMono (VMono G) (Finset.range n) :=
  ⟨t.1.replace q (.node m ch), isShuffle_replace t.2.1 hq
    (isShuffle_get? t.2.1 hq : (STree.node m₀ ch).IsShuffle) rfl,
    (labels_replace_of_eq (v := .node m ch) hq rfl).trans t.2.2⟩

lemma get?_replT (m : VMono G k) : (replT t hq m).1.get? q = some (.node m ch) :=
  get?_replace (by rw [hq]; rfl) _

lemma replT_replT (m m' : VMono G k) :
    replT (replT t hq m) (get?_replT t hq m) m' = replT t hq m' :=
  Subtype.ext (replace_replace _ _ _ _)

/-- A monomial of arity `k`, as an index of `tBasis`. -/
abbrev tIdx (m : VMono G k) : {t // t ∈ LTree.monomials (E := G) (Fintype.card (Fin k))} :=
  ⟨m.1, by simpa using m.2.1⟩

/-- **The trees with the vertex at `q` labelled by an operation of arity `k`**: the operation
written in the basis `tBasis`, each basis monomial labelling the vertex. -/
noncomputable def Tq : FreeGrL K E (Fin k) →ₗ[K] BarCoop (Ibar K E c hc) (Fin n) :=
  (tBasis c hc (Fin k)).constr K fun i => barBasisN c hc n (replT t hq ⟨i.1, by simpa using i.2,
    m₀.2.2⟩)

lemma Tq_tBasis (m : VMono G k) :
    Tq c hc t hq (tBasis c hc (Fin k) (tIdx m)) = barBasisN c hc n (replT t hq m) := by
  rw [Tq, Module.Basis.constr_basis]

/-- **The trees labelled by an operation of the relator ideal lie in the relator ideal of the bar
construction.** -/
theorem Tq_mem_Krel {y : FreeGrL K E (Fin k)} (hy : y ∈ (𝒥).sub (Fin k)) :
    Tq c hc t hq y ∈ (Krel K E c hc r).sub (Fin n) := by
  refine (mem_Krel_iff c hc r (A := Fin n) (Tq c hc t hq y)).2 ?_
  let βs : {t // t ∈ LTree.monomials (E := G) (Fintype.card (Fin k))} → VMono G k :=
    fun i => ⟨i.1, by simpa using i.2, m₀.2.2⟩
  let a := fun i => (tBasis c hc (Fin k)).repr y i
  have hlab : ∀ i, (t.1.replace q (.node (βs i) ch)).labels
      = (Finset.range (Fintype.card (Fin n))).val := fun i =>
    (replT t hq (βs i)).2.2.trans (by rw [Fintype.card_fin])
  have hsum : Tq c hc t hq y = ∑ i, a i • GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm
      (FreeGrL.shEv (genBasis c hc) (t.1.replace q (.node (βs i) ch)) _ (hlab i)) := by
    rw [Tq, Module.Basis.constr_apply_fintype]
    exact Finset.sum_congr rfl fun i _ => congrArg₂ _
      (congrFun ((tBasis c hc (Fin k)).equivFun_apply y) i) (barBasisN_eq_shEv c hc n _ (hlab i))
  have hz : IdealSp.val _ (∑ i, a i • genBasis c hc k (βs i)) = y := by
    show ((∑ i, a i • idealBasis c hc k (βs i) : (Ibar K E c hc).sub (Fin k)) :
      FreeGrL K E (Fin k)) = y
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, idealBasis_apply]
    exact (tBasis c hc (Fin k)).sum_repr y
  have hv : ∑ i ∈ Finset.univ, a i • (barProjGen c hc r).app (Fin k) (genBasis c hc k (βs i))
      = 0 := by
    simp only [← map_smul, ← map_sum]
    rw [barProjGen_eq_zero_iff]
    convert hy using 1
  exact (congrArg ((FreeGrL.mapSp (barProjGen c hc r)).app (Fin n)) hsum).trans
    (FreeGrL.mapSp_sum_shEv_replace (genBasis c hc) (barProjGen c hc r) Finset.univ a βs ch hv q
      t.1 m₀ hq _ hlab)

/-- **A relator substituted in the vertex monomial**: the trees with the vertex at `q` labelled
by the relator `ρ` substituted at an edge of the monomial `u` are, through `ΦL`, the relator
substituted at the corresponding uncut edge of the bar tree. -/
theorem ΦL_Tq_relator (u : VMono G k) {p : List Bool} {s : Bool} (he : u.1.IsEdge p s)
    (ρ : Mono G 3 → K) :
    ΦL c hc n (Tq c hc t hq (∑ σ : Mono G 3, ρ σ • tBasis c hc (Fin k) (tIdx (u.substAt he σ))))
      = sign K (replT t hq u).1 • substRel K (toBar (replT t hq u).1)
        (barPath (replT t hq u).1 q p) s ρ := by
  obtain ⟨-, heq⟩ := toBar_replace_substAt u ch he q (replT t hq u).1 (replT t hq u).2.1
    (get?_replT t hq u)
  have hL : ΦL c hc n (Tq c hc t hq (∑ σ : Mono G 3, ρ σ • tBasis c hc (Fin k)
      (tIdx (u.substAt he σ)))) = ((ΦL c hc n).comp (Tq c hc t hq)) (∑ σ : Mono G 3,
        ρ σ • tBasis c hc (Fin k) (tIdx (u.substAt he σ))) := rfl
  rw [hL, map_sum, substRel, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_smul, LinearMap.comp_apply, Tq_tBasis, Φ_barBasisN]
  have hs : sign K (replT t hq (u.substAt he σ)).1 = sign K (replT t hq u).1 :=
    sign_replace K q t.1 _ _ ch
  have hb : toBar (replT t hq (u.substAt he σ)).1
      = substBar (toBar (replT t hq u).1) (barPath (replT t hq u).1 q p) s σ.1 := by
    rw [← heq σ]
    exact congrArg toBar (replace_replace _ _ _ _).symm
  rw [hs, hb, smul_comm]

lemma ΦL_Tq_relator_mem (u : VMono G k) {p : List Bool} {s : Bool} (he : u.1.IsEdge p s)
    {ρ : Mono G 3 → K} (hρ : ρ ∈ Rsh c hc r) :
    ΦL c hc n (Tq c hc t hq (∑ σ : Mono G 3, ρ σ • tBasis c hc (Fin k) (tIdx (u.substAt he σ))))
      ∈ ShuffleBar.J K (Rsh c hc r) := by
  rw [ΦL_Tq_relator]
  obtain ⟨hU, -⟩ := toBar_replace_substAt u ch he q (replT t hq u).1 (replT t hq u).2.1
    (get?_replT t hq u)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, s, ρ, valid_toBar _, hU, hρ, rfl⟩)

omit [Fintype G] [DecidableEq G] in
lemma mem_monomials_of_isMonY [Fintype G] [DecidableEq G] {u : LTree G}
    (hu : IsMonY (Finset.range (Fintype.card (Fin k))) u) : u ∈ LTree.monomials k := by
  rw [mem_monomials]
  refine ⟨hu.1, ?_⟩
  have := hu.2
  rw [Finset.range_val, Fintype.card_fin, ← Multiset.coe_range, Multiset.coe_eq_coe] at this
  exact this

/-- A monomial with leaves `0, …, k - 1`, `2 ≤ k`, as a vertex label. -/
def vmonoOf {u : LTree G} (hu : IsMonY (Finset.range (Fintype.card (Fin k))) u) (hk : 2 ≤ k) :
    VMono G k :=
  ⟨u, mem_monomials_of_isMonY hu, hk⟩

/-- **A relator in a context, on the positions of `Fin k`**, written in the basis `tBasis`. -/
lemma map_relGen {u : LTree G} (hu : IsMonY (Finset.range (Fintype.card (Fin k))) u)
    (hk : 2 ≤ k) {p : List Bool} {s : Bool} (he : u.IsEdge p s) (ρ : Mono G 3 → K) :
    GrOperad.map (R := K) (FreeGrL.posEquiv (Fin k)).symm (relGen c hc hu he ρ)
      = ∑ σ : Mono G 3, ρ σ • tBasis c hc (Fin k) (tIdx ((vmonoOf hu hk).substAt he σ)) := by
  simp only [relGen, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => congrArg _ ?_
  rw [labBasis, FreeGrL.shBasisLab_apply, tBasis_apply, FreeGrL.shuffleBasis_apply]
  rfl

include r in
/-- **The trees labelled by an operation of the relator ideal give relators of the shuffle bar
construction**, for relators of arity three stable under the permutations of `Fin 3`. -/
theorem ΦL_Tq_mem_J (hr3 : ∀ n ≠ 3, r n = ∅)
    (hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ r 3,
      GrOperad.map (R := K) σ x ∈ Submodule.span K (r 3))
    {y : FreeGrL K E (Fin k)} (hy : y ∈ (𝒥).sub (Fin k)) :
    ΦL c hc n (Tq c hc t hq y) ∈ ShuffleBar.J K (Rsh c hc r) := by
  have h1 := (mem_relIdeal c hc r).1 (span_le_relIdeal hr3 hrS (Fin k) hy) _
    (FreeGrL.posEquiv (Fin k))
  have hy' : y = GrOperad.map (R := K) (FreeGrL.posEquiv (Fin k)).symm
      (GrOperad.map (R := K) (FreeGrL.posEquiv (Fin k)) y) := by
    rw [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]
  rw [hy']
  have hle : ShIT c hc r (Finset.range (Fintype.card (Fin k))) ≤ (ShuffleBar.J K (Rsh c hc r)).comap
      ((ΦL c hc n).comp ((Tq c hc t hq).comp
        (GrOperad.map (R := K) (FreeGrL.posEquiv (Fin k)).symm))) := by
    rw [ShIT, Submodule.span_le]
    rintro _ ⟨u, hu, p, s, he, ρ, hρ, rfl⟩
    show ΦL c hc n (Tq c hc t hq (GrOperad.map (R := K) (FreeGrL.posEquiv (Fin k)).symm
      (relGen c hc hu he ρ))) ∈ ShuffleBar.J K (Rsh c hc r)
    rw [map_relGen c hc hu m₀.2.2 he ρ]
    exact ΦL_Tq_relator_mem c hc r t hq _ he hρ
  exact hle h1

end Vertex

end ShuffleBarSym

namespace FreeGrL

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]

/-- **A morphism of generators sending basis vectors to basis vectors** sends the evaluation of
a tree whose vertices are relabelled to the evaluation of the tree. -/
theorem mapSp_map_shEv_mapV {B : ℕ → Type x} {B' : ℕ → Type*}
    (b : ∀ k, Module.Basis (B k) R (V (Fin k))) (b' : ∀ k, Module.Basis (B' k) R (W (Fin k)))
    (g : ∀ k, B' k → B k) (f : GrSpeciesHom R V W)
    (hf : ∀ k β, f.app (Fin k) (b k (g k β)) = b' k β)
    (t' : STree B') {Y : Finset ℕ} {A : Type} [Fintype A] [DecidableEq A] (e : Lab Y ≃ A)
    (h : (t'.mapV g).labels = Y.val) (h' : t'.labels = Y.val) :
    (mapSp f).app A (GrOperad.map (R := R) e (shEv b (t'.mapV g) Y h))
      = GrOperad.map (R := R) e (shEv b' t' Y h') := by
  rw [GrOperadHom.app_map, shEv_eq_shEvF, mapSp_shEvF, shEvF_mapV _ g t' Y h' h, shEv_eq_shEvF]
  congr 2
  funext k β
  exact hf k β

end FreeGrL

namespace ShuffleBarSym

open LTree ShuffleBar

/-! ## The kernel of the projection of the bar constructions -/

section Kernel

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))

local notation "𝒥" => GrOperadIdeal.span K r

/-- The images in `sĪ_P` of the basis vectors of `sĪ`. -/
noncomputable abbrev projGen (k : ℕ) (m : VMono G k) : BarGen (Ipres K E c hc r) (Fin k) :=
  (barProjGen c hc r).app (Fin k) (genBasis c hc k m)

/-- **A basis of `sĪ_P` among the images of the basis of `sĪ`.** -/
lemma exists_sel (k : ℕ) : ∃ S : Set (VMono G k),
    LinearIndependent K (fun m : S => projGen c hc r k m.1) ∧
      ⊤ ≤ Submodule.span K (Set.range fun m : S => projGen c hc r k m.1) := by
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K (projGen c hc r k)
  refine ⟨Set.range a, (linearIndependent_equiv (Equiv.ofInjective a ha)
    (f := fun m : Set.range a => projGen c hc r k m.1)).1 hli, ?_⟩
  have hr : (Set.range fun m : Set.range a => projGen c hc r k m.1)
      = Set.range (projGen c hc r k ∘ a) := by
    ext x
    constructor
    · rintro ⟨⟨_, y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨a y, y, rfl⟩, rfl⟩
  rw [hr, hsp, show (projGen c hc r k) = (barProjGen c hc r).app (Fin k) ∘ genBasis c hc k from rfl,
    Set.range_comp, Submodule.span_image, (genBasis c hc k).span_eq, Submodule.map_top,
    LinearMap.range_eq_top.2 (barProjGen_surjective c hc r (Fin k))]

variable (S : ∀ k, Set (VMono G k))
  (hli : ∀ k, LinearIndependent K (fun m : S k => projGen c hc r k m.1))
  (hsp : ∀ k, ⊤ ≤ Submodule.span K (Set.range fun m : S k => projGen c hc r k m.1))

/-- The chosen basis of `sĪ_P`. -/
noncomputable def selBasis (k : ℕ) : Module.Basis (S k) K (BarGen (Ipres K E c hc r) (Fin k)) :=
  Module.Basis.mk (hli k) (hsp k)

include hli hsp in
lemma selBasis_apply (k : ℕ) (j : S k) : selBasis c hc r S hli hsp k j = projGen c hc r k j.1 :=
  Module.Basis.mk_apply _ _ _

include hli hsp in
lemma par_selBasis (k : ℕ) (j : S k) :
    GrSpecies.par (R := K) ((fun _ _ => true) k j) (selBasis c hc r S hli hsp k j)
      = selBasis c hc r S hli hsp k j := by
  rw [selBasis_apply, projGen, ← (barProjGen c hc r).app_par]
  exact congrArg _ (par_genBasis c hc k j.1)

/-- **A linear map independent on a family is injective on its span.** -/
lemma _root_.Operad.eq_zero_of_linearIndependent_comp {R M N ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (π : M →ₗ[R] N) (v : ι → M)
    (h : LinearIndependent R (π ∘ v)) {x : M} (hx : x ∈ Submodule.span R (Set.range v))
    (hπ : π x = 0) : x = 0 := by
  obtain ⟨l, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
  have hl : l = 0 := linearIndependent_iff.1 h l (by
    rw [Finsupp.linearCombination_apply, ← hπ, map_finsuppSum]
    simp only [map_smul, Function.comp_apply])
  rw [hl, Finsupp.sum_zero_index]

include hli hsp in
/-- **The projection is injective on the trees with all vertices in `S`.** -/
theorem eq_zero_of_mem_sel {n : ℕ} {x : BarCoop (Ibar K E c hc) (Fin n)}
    (hx : x ∈ Submodule.span K (Set.range fun t : {t : SMono (VMono G) (Finset.range n) //
      nS S t.1 = 0} => barBasisN c hc n t.1))
    (hπ : (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n) x = 0) : x = 0 := by
  haveI : IsEmpty (S 0) := ⟨fun m => isEmptyElim m.1⟩
  let φ : {t : SMono (VMono G) (Finset.range n) // nS S t.1 = 0} →
      SMono (fun k => S k) (Finset.range (Fintype.card (Fin n))) := fun t =>
    ⟨liftS S t.1.1 t.2, (isShuffle_mapV _ _).1 (by rw [mapV_liftS]; exact t.1.2.1), by
      rw [← labels_mapV (fun _ m => m.1), mapV_liftS, t.1.2.2, Fintype.card_fin]⟩
  have hφ : Function.Injective φ := fun t t' h => by
    have h' := congrArg (fun T => T.1.mapV (fun _ m => m.1)) h
    simp only [φ, mapV_liftS] at h'
    exact Subtype.ext (Subtype.ext h')
  have hπb : ∀ t, (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n) (barBasisN c hc n t.1)
      = FreeGrL.shuffleBasis (selBasis c hc r S hli hsp) (par_selBasis c hc r S hli hsp) (Fin n)
        (φ t) := fun t => by
    have h₁ : t.1.1.labels = (Finset.range (Fintype.card (Fin n))).val := by
      rw [t.1.2.2, Fintype.card_fin]
    have h₂ : ((liftS S t.1.1 t.2).mapV fun _ m => m.1).labels
        = (Finset.range (Fintype.card (Fin n))).val := by
      rw [mapV_liftS]
      exact h₁
    exact (congrArg ((FreeGrL.mapSp (barProjGen c hc r)).app (Fin n))
      (barBasisN_eq_shEv c hc n _ h₁)).trans ((congrArg (fun z =>
        (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n)
          (GrOperad.map (R := K) (FreeGrL.posEquiv (Fin n)).symm z))
        (shEv_congr c hc (mapV_liftS S t.1.1 t.2).symm _ h₁ h₂)).trans
        ((FreeGrL.mapSp_map_shEv_mapV (genBasis c hc) (selBasis c hc r S hli hsp)
          (fun _ m => m.1) (barProjGen c hc r)
          (fun k j => (selBasis_apply c hc r S hli hsp k j).symm) _ _ h₂ (φ t).2.2).trans
          (FreeGrL.shuffleBasis_apply _ _ _ (φ t)).symm))
  have hli' : LinearIndependent K fun t : {t : SMono (VMono G) (Finset.range n) // nS S t.1 = 0}
      => (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n) (barBasisN c hc n t.1) := by
    rw [show (fun t : {t : SMono (VMono G) (Finset.range n) // nS S t.1 = 0} =>
        (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n) (barBasisN c hc n t.1))
      = (FreeGrL.shuffleBasis (selBasis c hc r S hli hsp) (par_selBasis c hc r S hli hsp) (Fin n))
        ∘ φ from funext hπb]
    exact (Module.Basis.linearIndependent _).comp φ hφ
  exact eq_zero_of_linearIndependent_comp _ _ hli' hx hπ

/-- **The trees labelled at one vertex by an operation of the relator ideal.** -/
def relTrees (n : ℕ) : Set (BarCoop (Ibar K E c hc) (Fin n)) :=
  {x | ∃ (t : SMono (VMono G) (Finset.range n)) (q : List ℕ) (k : ℕ) (m₀ : VMono G k)
    (ch : Fin k → STree (VMono G)) (hq : t.1.get? q = some (.node m₀ ch))
    (y : FreeGrL K E (Fin k)), y ∈ (𝒥).sub (Fin k) ∧ x = Tq c hc t hq y}

include hli hsp in
/-- **Every tree is a combination of trees with all vertices in `S` modulo the trees labelled at one
vertex by the relator ideal**, by induction on the number of vertices outside `S`. -/
theorem barBasisN_mem_sup {n : ℕ} : ∀ (N : ℕ) (t : SMono (VMono G) (Finset.range n)),
    nS S t.1 ≤ N → barBasisN c hc n t ∈ Submodule.span K (relTrees c hc r n) ⊔
      Submodule.span K (Set.range fun t : {t : SMono (VMono G) (Finset.range n) //
        nS S t.1 = 0} => barBasisN c hc n t.1) := by
  intro N
  induction N with
  | zero =>
    intro t ht
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨⟨t, by omega⟩, rfl⟩)
  | succ N ih =>
    intro t ht
    by_cases h0 : nS S t.1 = 0
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨⟨t, h0⟩, rfl⟩)
    obtain ⟨q, k, m, ch, hq, hm⟩ := exists_get?_not_mem S t.1 h0
    let d := (selBasis c hc r S hli hsp k).repr (projGen c hc r k m)
    have hfm : projGen c hc r k m = d.sum fun j a => a • projGen c hc r k j.1 := by
      conv_lhs => rw [← (selBasis c hc r S hli hsp k).linearCombination_repr (projGen c hc r k m)]
      rw [Finsupp.linearCombination_apply]
      simp only [selBasis_apply]
      rfl
    let y : FreeGrL K E (Fin k) := tBasis c hc (Fin k) (tIdx m) -
      d.sum fun j a => a • tBasis c hc (Fin k) (tIdx j.1)
    have hy : y ∈ (𝒥).sub (Fin k) := by
      let z : BarGen (Ibar K E c hc) (Fin k) := genBasis c hc k m -
        d.sum fun j a => a • genBasis c hc k j.1
      have hz : IdealSp.val _ z = y := by
        show ((idealBasis c hc k m - d.sum fun j a => a • idealBasis c hc k j.1 :
          (Ibar K E c hc).sub (Fin k)) : FreeGrL K E (Fin k)) = y
        rw [Submodule.coe_sub, idealBasis_apply, Finsupp.sum, Submodule.coe_sum]
        simp only [Submodule.coe_smul, idealBasis_apply]
        rfl
      rw [← hz, ← barProjGen_eq_zero_iff, map_sub, map_finsuppSum]
      simp only [map_smul]
      rw [← hfm]
      exact sub_self _
    have hTq : Tq c hc t hq y = barBasisN c hc n t
        - d.sum fun j a => a • barBasisN c hc n (replT t hq j.1) := by
      simp only [y, map_sub, map_finsuppSum, map_smul, Tq_tBasis]
      rw [show replT t hq m = t from Subtype.ext (replace_self hq)]
    have hdecomp : barBasisN c hc n t = Tq c hc t hq y
        + d.sum fun j a => a • barBasisN c hc n (replT t hq j.1) := by
      rw [hTq, sub_add_cancel]
    rw [hdecomp]
    refine add_mem (Submodule.mem_sup_left (Submodule.subset_span
      ⟨t, q, k, m, ch, hq, y, hy, rfl⟩)) (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (ih _ ?_))
    classical
    have := nS_replace S m j.1 ch q t.1 hq
    rw [if_neg hm, if_pos j.2] at this
    show nS S (t.1.replace q (.node j.1 ch)) ≤ N
    omega

end Kernel

/-! ## The relator ideal of the bar construction in shuffle coordinates -/

section HJ

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  {r : ∀ n : ℕ, Set (FreeGrL K E (Fin n))}

local notation "𝒥" => GrOperadIdeal.span K r

/-- **`ΦL` maps the relator ideal of the bar construction onto the relator subcomplex of the
shuffle bar construction**, for relators of arity three stable under the permutations of
`Fin 3`. -/
theorem map_ΦL_Krel (hr3 : ∀ n ≠ 3, r n = ∅)
    (hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ r 3,
      GrOperad.map (R := K) σ x ∈ Submodule.span K (r 3)) (n : ℕ) :
    Submodule.map (ΦL c hc n) ((Krel K E c hc r).sub (Fin n))
      = ShuffleBar.J K (Rsh c hc r) ⊓ Finsupp.supported K K (barSet G n) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, by rw [← ΦL_range c hc n]; exact LinearMap.mem_range_self _ x⟩
    choose S hli hsp using exists_sel c hc r
    have htop : ⊤ ≤ Submodule.span K (relTrees c hc r n) ⊔
        Submodule.span K (Set.range fun t : {t : SMono (VMono G) (Finset.range n) //
          nS S t.1 = 0} => barBasisN c hc n t.1) := by
      rw [← (barBasisN c hc n).span_eq, Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact barBasisN_mem_sup c hc r S hli hsp _ t le_rfl
    obtain ⟨q₁, hq₁, s₁, hs₁, hqs⟩ := Submodule.mem_sup.1 (htop Submodule.mem_top (x := x))
    have hQK : Submodule.span K (relTrees c hc r n) ≤ (Krel K E c hc r).sub (Fin n) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, q, k, m₀, ch, hq, y, hy, rfl⟩
      exact Tq_mem_Krel c hc r t hq hy
    have hQJ : Submodule.span K (relTrees c hc r n) ≤
        (ShuffleBar.J K (Rsh c hc r)).comap (ΦL c hc n) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, q, k, m₀, ch, hq, y, hy, rfl⟩
      exact ΦL_Tq_mem_J c hc r t hq hr3 hrS hy
    have hsK : s₁ ∈ (Krel K E c hc r).sub (Fin n) := by
      have := sub_mem hx (hQK hq₁)
      rwa [← hqs, add_sub_cancel_left] at this
    have hs0 : s₁ = 0 := eq_zero_of_mem_sel c hc r S hli hsp hs₁
      ((mem_Krel_iff c hc r (A := Fin n) s₁).1 hsK)
    rw [← hqs, hs0, add_zero]
    exact hQJ hq₁
  · rw [J_inf_supported K (Rsh c hc r) (barSet G n) fun x y _ hy hxy hx => ⟨hy,
      hxy.symm.trans hx.2⟩, Submodule.span_le]
    rintro _ ⟨x, P, s, ρ, hx, hxS, hU, hρ, rfl⟩
    let t := (treeEquiv n).symm ⟨x, hxS⟩
    have ht : toBar t.1 = x := congrArg Subtype.val ((treeEquiv n).apply_symm_apply ⟨x, hxS⟩)
    rw [← ht] at hU ⊢
    obtain ⟨q, k, m, ch, p, hq, he, rfl⟩ := exists_of_isUncut t.1 t.2.1 hU
    have hu : IsMonY (Finset.range (Fintype.card (Fin k))) m.1 := by
      have h := (LTree.mem_monomials k m.1).1 m.2.1
      refine ⟨h.1, ?_⟩
      rw [Finset.range_val, Fintype.card_fin, ← Multiset.coe_range, Multiset.coe_eq_coe]
      exact h.2
    have hrel : ∑ σ : Mono G 3, ρ σ • tBasis c hc (Fin k) (tIdx (m.substAt he σ))
        ∈ (𝒥).sub (Fin k) := by
      have h1 := ShIT_le c hc (GrOperadIdeal.span K r) r (fun y hy =>
        GrOperadIdeal.subset_span (R := K) 3 hy) _ (relGen_mem_ShIT c hc r hu he hρ)
      have h2 := (GrOperadIdeal.span K r).map_mem (FreeGrL.posEquiv (Fin k)).symm h1
      rwa [map_relGen c hc hu m.2.2 he ρ] at h2
    refine ⟨sign K t.1 • Tq c hc t hq (∑ σ : Mono G 3, ρ σ • tBasis c hc (Fin k)
      (tIdx (m.substAt he σ))), Submodule.smul_mem _ _ (Tq_mem_Krel c hc r t hq hrel), ?_⟩
    have hself : replT t hq m = t := Subtype.ext (replace_self hq)
    rw [map_smul, ΦL_Tq_relator, hself, smul_smul, sign_mul_self, one_smul]

/-- **The bridge** (step 2c of Dotsenko–Khoroshkin): for an even binary graded linear species `E`
over a field of characteristic zero and relators concentrated in arity three, spanning a subspace
stable under the permutations of `Fin 3`, the presented operad is Koszul iff the shuffle operad
presented by the coordinates `Rsh` of the relators is Koszul in the sense of
`ShuffleBar.IsKoszul`. -/
theorem isKoszul_iff_shuffle [CharZero K] (hr3 : ∀ n ≠ 3, r n = ∅)
    (hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ r 3,
      GrOperad.map (R := K) σ x ∈ Submodule.span K (r 3)) :
    Koszul.IsKoszul K E r ↔ ShuffleBar.IsKoszul K (Rsh c hc r) :=
  isKoszul_iff_shuffle_of_J c hc (fun n hn => hr3 n (by omega)) (Rsh c hc r)
    fun n _ => map_ΦL_Krel c hc hr3 hrS n

end HJ

end ShuffleBarSym

end Operad
