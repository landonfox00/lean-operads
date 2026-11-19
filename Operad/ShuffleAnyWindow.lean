/-
# Windows of the bar tree and of the vertex monomials, for generators of any arity

Step (2c) of the symmetric–shuffle bridge for generators of any arity, seventh part. A bar tree
`toBar t` is made of the monomials of the vertices of `t`; this file locates the positions of
the bar tree in those monomials.

* **The position of a vertex** (`ShuffleAnySym.bp`): the subtree of `toBar t` at `bp t q` is the
  bar tree of the subtree of `t` at `q`, with the edge above it cut
  (`ShuffleAnySym.get?_toBar_bp`), and replacing the subtree of `t` at `q` replaces it
  (`ShuffleAnySym.toBar_replace`).
* **Windows**: a position `p₀` of the monomial of the vertex at `q` is the position
  `bp t q ++ p₀` of the bar tree, where the subtree is that of the monomial, flagged at its root
  (`ShuffleAnySym.wflag`), with the bar trees of the children substituted
  (`ShuffleAnySym.get?_toBar_window`); replacing the subtree of the monomial replaces it
  (`ShuffleAnySym.toBar_replace_window`).
* **Every position of the bar tree which is not a leaf arises so** (`ShuffleAnySym.exists_bp`).
* **Factoring through the top component** (`ShuffleAnySym.exists_subst_of_hang`): a tree with
  trees substituted which is a tree with hanging trees substituted factors through it.
-/
import Operad.ShuffleAnyKer

universe u

namespace Operad

open Function Sym GerBV GrComposite STree FreeGr Bar

namespace ShuffleAnySym

open ShuffleBarSym

section BarPos

open STree

variable {T : ℕ → Type}

/-- **The position in the bar tree of the root of the vertex at `q`**: the positions of the
leaves of the monomials along the path. -/
noncomputable def bp : STree (VMono T) → List ℕ → List ℕ
  | .leaf _, _ => []
  | .node _ _, [] => []
  | .node (k := k) M ch, a :: q => if h : a < k then M.1.1.pos a ++ bp (ch ⟨a, h⟩) q else []

@[simp] lemma bp_nil (t : STree (VMono T)) : bp t [] = [] := by
  cases t <;> rfl

lemma bp_cons {k : ℕ} (M : VMono T k) (ch : Fin k → STree (VMono T)) {a : ℕ} (ha : a < k)
    (q : List ℕ) : bp (.node M ch) (a :: q) = M.1.1.pos a ++ bp (ch ⟨a, ha⟩) q := by
  rw [bp, dif_pos ha]

/-- Cut the edge above the root, except at the root of the tree. -/
def cr (q : List ℕ) (y : STree (BE T)) : STree (BE T) := if q = [] then y else cutRoot y

@[simp] lemma cr_nil (y : STree (BE T)) : cr [] y = y := if_pos rfl

lemma cr_of_ne {q : List ℕ} (hq : q ≠ []) (y : STree (BE T)) : cr q y = cutRoot y := if_neg hq

lemma cutRoot_replace {y : STree (BE T)} {p : List ℕ} (hp : p ≠ []) (u : STree (BE T)) :
    cutRoot (y.replace p u) = (cutRoot y).replace p u := by
  cases p with
  | nil => exact absurd rfl hp
  | cons i p =>
    cases y with
    | leaf a => rfl
    | node d c => rfl

lemma get?_cutRoot {y : STree (BE T)} {p : List ℕ} (hp : p ≠ []) :
    (cutRoot y).get? p = y.get? p := by
  cases p with
  | nil => exact absurd rfl hp
  | cons i p =>
    cases y with
    | leaf a => rfl
    | node d c => rfl

lemma VMono.nodup {k : ℕ} (M : VMono T k) : M.1.1.labels.Nodup := by
  rw [M.labels]
  exact Multiset.nodup_range k

lemma VMono.get?_pos {k : ℕ} (M : VMono T k) {a : ℕ} (ha : a < k) :
    M.1.1.get? (M.1.1.pos a) = some (.leaf a) := STree.get?_pos (M.mem ha)

lemma VMono.pos_ne_nil {k : ℕ} (M : VMono T k) {a : ℕ} (ha : a < k) : M.1.1.pos a ≠ [] := by
  intro h
  have h1 := M.get?_pos ha
  rw [h, get?_nil, Option.some_inj] at h1
  obtain ⟨l, e, c, h2⟩ := M.exists_node
  rw [h2] at h1
  cases h1

/-- The subtree of the bar tree at the position of a leaf of the root monomial. -/
lemma get?_toBar_pos {k : ℕ} (M : VMono T k) (ch : Fin k → STree (VMono T)) {a : ℕ}
    (ha : a < k) : (toBar (.node M ch)).get? (M.1.1.pos a) = some (kids ch a) := by
  rw [toBar_node, fl_false]
  have h1 : (allF M.1.1).get? (M.1.1.pos a) = some (.leaf a) := by
    rw [allF, get?_mapG, M.get?_pos ha]
    rfl
  exact get?_subst h1 (kids ch)

/-- Replacing a child of the root replaces the subtree of the bar tree at the position of its
leaf. -/
lemma toBar_update {k : ℕ} (M : VMono T k) (ch : Fin k → STree (VMono T)) (a : Fin k)
    (u' : STree (VMono T)) :
    toBar (.node M (update ch a u'))
      = (toBar (.node M ch)).replace (M.1.1.pos a) (cutRoot (toBar u')) := by
  rw [toBar_node, toBar_node, fl_false]
  have h1 : (allF M.1.1).get? (M.1.1.pos a) = some (.leaf a) := by
    rw [allF, get?_mapG, M.get?_pos a.2]
    rfl
  have hn : (allF M.1.1).labels.Nodup := by
    rw [labels_allF]
    exact M.nodup
  rw [← subst_update hn h1 (kids ch) (cutRoot (toBar u'))]
  refine subst_congr _ fun b hb => ?_
  rw [labels_allF] at hb
  have hbk := M.lt hb
  by_cases hba : b = a
  · rw [hba, update_self, kids_fin, update_self]
  · have hne : (⟨b, hbk⟩ : Fin k) ≠ a := fun h => hba (congrArg Fin.val h)
    rw [update_of_ne hba, kids_of_lt _ hbk, kids_of_lt _ hbk, update_of_ne hne]

lemma bp_ne_nil : ∀ {t u : STree (VMono T)} {q : List ℕ}, t.get? q = some u → q ≠ [] →
    bp t q ≠ []
  | _, _, [], _, hq => absurd rfl hq
  | .leaf _, _, _ :: _, h, _ => by simp at h
  | .node M ch, _, a :: q, h, _ => by
    obtain ⟨ha, -⟩ := get?_node_cons_eq_some.1 h
    rw [bp_cons M ch ha]
    exact fun h' => M.pos_ne_nil ha (List.append_eq_nil_iff.1 h').1

/-- **The subtree of the bar tree at the vertex `q`** is the bar tree of the subtree at `q`, with
the edge above it cut. -/
theorem get?_toBar_bp : ∀ (t : STree (VMono T)) (q : List ℕ) {u : STree (VMono T)},
    t.get? q = some u → (toBar t).get? (bp t q) = some (cr q (toBar u))
  | t, [], u, h => by
    rw [get?_nil, Option.some_inj] at h
    rw [bp_nil, get?_nil, cr_nil, h]
  | .leaf _, _ :: _, _, h => by simp at h
  | .node M ch, a :: q, u, h => by
    obtain ⟨ha, h'⟩ := get?_node_cons_eq_some.1 h
    rw [bp_cons M ch ha, get?_append_of (get?_toBar_pos M ch ha), kids_of_lt ch ha,
      cr_of_ne (List.cons_ne_nil a q)]
    by_cases hq : q = []
    · subst hq
      rw [get?_nil, Option.some_inj] at h'
      rw [bp_nil, get?_nil, h']
    · rw [get?_cutRoot (bp_ne_nil h' hq), get?_toBar_bp (ch ⟨a, ha⟩) q h', cr_of_ne hq]

/-- **Replacing the subtree at the vertex `q`** replaces the subtree of the bar tree at the
position of that vertex. -/
theorem toBar_replace : ∀ (t : STree (VMono T)) (q : List ℕ) {u : STree (VMono T)},
    t.get? q = some u → ∀ u' : STree (VMono T),
      toBar (t.replace q u') = (toBar t).replace (bp t q) (cr q (toBar u'))
  | t, [], _, _, u' => by rw [replace_nil, bp_nil, replace_nil, cr_nil]
  | .leaf _, _ :: _, _, h, _ => by simp at h
  | .node M ch, a :: q, u, h, u' => by
    obtain ⟨ha, h'⟩ := get?_node_cons_eq_some.1 h
    have e1 : (STree.node M ch).replace (a :: q) u'
        = .node M (update ch ⟨a, ha⟩ ((ch ⟨a, ha⟩).replace q u')) := by
      rw [replace_node_cons]
      congr 1
      funext j
      by_cases hj : j = ⟨a, ha⟩
      · subst hj
        rw [update_self, if_pos rfl]
      · rw [update_of_ne hj, if_neg fun h'' => hj (Fin.ext h'')]
    rw [e1, toBar_update, toBar_replace (ch ⟨a, ha⟩) q h' u', bp_cons M ch ha,
      replace_append (get?_toBar_pos M ch ha), kids_of_lt ch ha,
      cr_of_ne (List.cons_ne_nil a q)]
    congr 1
    by_cases hq : q = []
    · subst hq
      rw [bp_nil, replace_nil, replace_nil, cr_nil]
    · rw [cutRoot_replace (bp_ne_nil h' hq), cr_of_ne hq]

/-! ## Windows -/

lemma get?_toBar_node {k : ℕ} (M : VMono T k) (ch : Fin k → STree (VMono T)) {p₀ : List ℕ}
    {Mp : STree T} (h : M.1.1.get? p₀ = some Mp) :
    (toBar (.node M ch)).get? p₀ = some ((allF Mp).subst (kids ch)) := by
  rw [toBar_node, fl_false]
  exact get?_subst (by rw [allF, get?_mapG, h]; rfl) (kids ch)

lemma toBar_node_replace {k : ℕ} (M M' : VMono T k) (ch : Fin k → STree (VMono T))
    {p₀ : List ℕ} {Mp U : STree T} (h : M.1.1.get? p₀ = some Mp)
    (hM' : M'.1.1 = M.1.1.replace p₀ U) :
    toBar (.node M' ch) = (toBar (.node M ch)).replace p₀ ((allF U).subst (kids ch)) := by
  rw [toBar_node, toBar_node, fl_false, fl_false, hM', allF_replace,
    replace_subst (by rw [allF, get?_mapG, h]; rfl)]

/-- **The flag of a window** at the position `p₀` of the monomial of the vertex `q`: cut iff the
window is at the root of the monomial of a vertex other than the root. -/
def wflag (q p₀ : List ℕ) : Bool := decide (q ≠ [] ∧ p₀ = [])

lemma wflag_nil (p₀ : List ℕ) : wflag [] p₀ = false := by simp [wflag]

lemma wflag_of_ne {p₀ : List ℕ} (hp : p₀ ≠ []) (q : List ℕ) : wflag q p₀ = false := by
  simp [wflag, hp]

lemma wflag_of_ne_nil {q : List ℕ} (hq : q ≠ []) : wflag q [] = true := by simp [wflag, hq]

lemma cutRoot_allF_subst {U : STree T} (hU : ∀ a, U ≠ .leaf a) (xs : ℕ → STree (BE T)) :
    cutRoot ((allF U).subst xs) = (fl true U).subst xs := by
  cases U with
  | leaf a => exact absurd rfl (hU a)
  | node e c => rfl

/-- **The window of the bar tree** at a position of the monomial of a vertex. -/
theorem get?_toBar_window {t : STree (VMono T)} {q : List ℕ} {k : ℕ} {M : VMono T k}
    {ch : Fin k → STree (VMono T)} (hq : t.get? q = some (.node M ch)) {p₀ : List ℕ}
    {Mp : STree T} (h : M.1.1.get? p₀ = some Mp) (hMp : ∀ a, Mp ≠ .leaf a) :
    (toBar t).get? (bp t q ++ p₀) = some ((fl (wflag q p₀) Mp).subst (kids ch)) := by
  rw [get?_append_of (get?_toBar_bp t q hq)]
  by_cases hq0 : q = []
  · subst hq0
    rw [cr_nil, wflag_nil, fl_false]
    exact get?_toBar_node M ch h
  · rw [cr_of_ne hq0]
    by_cases hp : p₀ = []
    · subst hp
      rw [get?_nil, Option.some_inj] at h
      rw [get?_nil, wflag_of_ne_nil hq0, ← h, toBar_node, fl_false,
        cutRoot_allF_subst (h ▸ hMp)]
    · rw [get?_cutRoot hp, wflag_of_ne hp, fl_false]
      exact get?_toBar_node M ch h

/-- **Replacing a window of the monomial of a vertex** replaces the window of the bar tree. -/
theorem toBar_replace_window {t : STree (VMono T)} {q : List ℕ} {k : ℕ} {M : VMono T k}
    {ch : Fin k → STree (VMono T)} (hq : t.get? q = some (.node M ch)) {p₀ : List ℕ}
    {Mp U : STree T} (h : M.1.1.get? p₀ = some Mp) (M' : VMono T k)
    (hM' : M'.1.1 = M.1.1.replace p₀ U) (hU : ∀ a, U ≠ .leaf a) :
    toBar (t.replace q (.node M' ch))
      = (toBar t).replace (bp t q ++ p₀) ((fl (wflag q p₀) U).subst (kids ch)) := by
  rw [toBar_replace t q hq, replace_append (get?_toBar_bp t q hq),
    toBar_node_replace M M' ch h hM']
  congr 1
  by_cases hq0 : q = []
  · subst hq0
    rw [cr_nil, cr_nil, wflag_nil, fl_false]
  · rw [cr_of_ne hq0, cr_of_ne hq0]
    by_cases hp : p₀ = []
    · subst hp
      rw [replace_nil, replace_nil, wflag_of_ne_nil hq0, cutRoot_allF_subst hU]
    · rw [cutRoot_replace hp, wflag_of_ne hp, fl_false]

/-- **Every position of the bar tree which is not a leaf is a position of the monomial of a
vertex.** -/
theorem exists_bp : ∀ (t : STree (VMono T)) {p : List ℕ} {Z : STree (BE T)},
    (toBar t).get? p = some Z → (∀ a, Z ≠ .leaf a) →
    ∃ (q : List ℕ) (k : ℕ) (M : VMono T k) (ch : Fin k → STree (VMono T)) (p₀ : List ℕ)
      (Mp : STree T), t.get? q = some (.node M ch) ∧ M.1.1.get? p₀ = some Mp ∧
        p = bp t q ++ p₀ ∧ ∀ a, Mp ≠ .leaf a
  | .leaf b, p, Z, h, hZ => by
    cases p with
    | nil =>
      rw [get?_nil, Option.some_inj] at h
      exact absurd h.symm (hZ b)
    | cons i p => simp [toBar] at h
  | .node (k := k) M ch, p, Z, h, hZ => by
    rw [toBar_node, fl_false] at h
    rcases get?_subst_cases h with ⟨u, hu, rfl⟩ | ⟨q₀, i, q', a, rfl, h₀, h'⟩
    · rw [allF, get?_mapG] at hu
      obtain ⟨Mp, hMp, rfl⟩ := Option.map_eq_some_iff.1 hu
      by_cases hl : ∃ a, Mp = .leaf a
      · obtain ⟨a, rfl⟩ := hl
        have ha : a < k := M.lt (mem_labels_of_get? hMp)
        have hp : M.1.1.pos a = p := pos_eq M.nodup hMp
        rcases hc : ch ⟨a, ha⟩ with x | ⟨M₂, c₂⟩
        · refine absurd ?_ (hZ x)
          show kids ch a = .leaf x
          rw [kids_of_lt ch ha, hc]
          rfl
        · refine ⟨[a], _, M₂, c₂, [], M₂.1.1, ?_, get?_nil _, ?_, fun b hb => ?_⟩
          · rw [get?_node_cons, dif_pos ha, get?_nil, hc]
          · rw [bp_cons M ch ha, bp_nil, List.append_nil, List.append_nil, hp]
          · obtain ⟨l, e, c, h2⟩ := M₂.exists_node
            rw [h2] at hb
            cases hb
      · exact ⟨[], k, M, ch, p, Mp, get?_nil _, hMp, by rw [bp_nil, List.nil_append],
          fun a ha => hl ⟨a, ha⟩⟩
    · rw [allF, get?_mapG] at h₀
      obtain ⟨Ml, hMl, hleaf⟩ := Option.map_eq_some_iff.1 h₀
      have hMl' : Ml = .leaf a := by
        cases Ml with
        | leaf b =>
          have hb : STree.leaf b = (STree.leaf a : STree (BE T)) := hleaf
          injection hb with hb
          rw [hb]
        | node e c => cases hleaf
      rw [hMl'] at hMl
      have ha : a < k := M.lt (mem_labels_of_get? hMl)
      have hq₀ : M.1.1.pos a = q₀ := pos_eq M.nodup hMl
      rw [kids_of_lt ch ha, get?_cutRoot (List.cons_ne_nil i q')] at h'
      obtain ⟨q, k', M', ch', p₀, Mp, h1, h2, h3, h4⟩ := exists_bp (ch ⟨a, ha⟩) h' hZ
      refine ⟨a :: q, k', M', ch', p₀, Mp, ?_, h2, ?_, h4⟩
      · rw [get?_node_cons, dif_pos ha]
        exact h1
      · rw [bp_cons M ch ha, hq₀, h3, List.append_assoc]

lemma exists_glueT {k : ℕ} {e : T k} {c : Fin k → STree T}
    (hn : (STree.node e c).labels.Nodup) (F : Fin k → ℕ → STree T) :
    ∃ G : ℕ → STree T, ∀ i, ∀ a ∈ (c i).labels, G a = F i a := by
  classical
  refine ⟨fun a => if h : ∃ i, a ∈ (c i).labels then F h.choose a else .leaf a,
    fun i a ha => ?_⟩
  have h : ∃ i, a ∈ (c i).labels := ⟨i, ha⟩
  dsimp only
  rw [dif_pos h]
  by_cases hi : h.choose = i
  · rw [hi]
  · exact absurd ha (not_mem_of_node hn hi h.choose_spec)

/-- **A window over hanging trees factors through the top component**: if a tree `g` with trees
`xs` substituted is a tree `Mp` with hanging trees `K` substituted, then `Mp` is `g` with trees
`xs₀` substituted, and each `xs a` is `xs₀ a` with the hanging trees substituted. -/
theorem exists_subst_of_hang : ∀ (g : STree T), g.labels.Nodup → ∀ (Mp : STree T)
    (xs K : ℕ → STree (BE T)), (∀ a, IsHang (K a)) → (allF g).subst xs = (allF Mp).subst K →
    ∃ xs₀ : ℕ → STree T, Mp = g.subst xs₀ ∧ ∀ a ∈ g.labels, xs a = (allF (xs₀ a)).subst K
  | .leaf a, _, Mp, xs, K, _, h => ⟨fun _ => Mp, rfl, fun b hb => by
      rw [Multiset.mem_singleton.1 hb]
      exact h⟩
  | .node (k := k) e c, hn, Mp, xs, K, hK, h => by
    rcases Mp with a' | ⟨e', c'⟩
    · exact absurd h.symm (hK a' k e _)
    · have h' : STree.node (e, false) (fun i => (allF (c i)).subst xs)
          = STree.node (e', false) (fun i => (allF (c' i)).subst K) := h
      injection h' with hk he hc
      subst hk
      have he' : e = e' := congrArg Prod.fst (eq_of_heq he)
      subst he'
      have hc' := eq_of_heq hc
      have ih := fun i => exists_subst_of_hang (c i) (nodup_of_node hn i) (c' i) xs K hK
        (congrFun hc' i)
      choose xs₀ h1 h2 using ih
      obtain ⟨G, hG⟩ := exists_glueT hn xs₀
      refine ⟨G, ?_, fun a ha => ?_⟩
      · rw [subst_node]
        congr 1
        funext i
        rw [h1 i]
        exact subst_congr _ fun a ha => (hG i a ha).symm
      · obtain ⟨i, hi⟩ := mem_labels_node.1 ha
        rw [hG i a hi]
        exact h2 i a hi

end BarPos

end ShuffleAnySym

end Operad
