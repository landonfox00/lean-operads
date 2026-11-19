/-
# The relator ideal of the bar construction in shuffle coordinates, for generators of any arity

Step (2c) of the symmetric–shuffle bridge for generators of any arity, eighth part; the binary
case is `Operad.ShuffleBarJ`. Setting as in `Operad.ShuffleAnyProj`, with rules `G` on the shuffle
monomials (`Operad.ShuffleAnyGroebner`) whose leading monomials are not leaves, whose tails have
as many generators as their leading monomials, and whose ideal is the ideal of the relators in
shuffle coordinates:
`y ∈ (r) (Fin k) ↔ (tBasisN k).repr y ∈ (G.rw (range k)).ideal` for every `k` (hypothesis `hR`).

* **Signs**: replacing the monomial of a vertex by one with as many generators keeps the keys of
  the vertices and the sign (`ShuffleAnySym.wKeys_replace`, `ShuffleAnySym.wsign_replace`).
* **Contexts**: a context of the monomial of a vertex is a context of the bar tree
  (`ShuffleAnySym.exists_barCtx`), and a context of the bar trees with no cut above the root is
  a context of the monomial of a vertex (`ShuffleAnySym.exists_ctx_of_barCtx`).
* Hence a rule in a context at a vertex is the flagged rule in a bar context, up to sign
  (`ShuffleAnySym.linearCombination_tqΦ_rule`), and **`ΦL x` lies in the ideal of the flagged
  rules iff `x` lies in the relator ideal `Krel`** (`ShuffleAnySym.ΦL_mem_ideal_of_mem_krel`,
  `ShuffleAnySym.mem_krel_of_ΦL_mem`).
* **The ideal of the flagged rules is stable under the projections onto the bidegrees**
  (`ShuffleAnySym.prS_mem_ideal`).
* **The bridge on the leaves `0, …, n - 1`** (`ShuffleAnySym.isKoszul_iff_rules_range`), by
  `ShuffleAnySym.isKoszul_iff_shuffle_of_J`.

Not proved here: the hypothesis `hR` for relators stable under the symmetric groups and rules
spanning their shuffle coordinates, the any-arity version of `Operad.ShuffleRelIdeal`.
-/
import Operad.ShuffleAnyWindow

universe u

namespace Operad

open Function Sym GerBV GrComposite STree FreeGr Bar

namespace ShuffleAnySym

open ShuffleBarSym

/-! ## The keys do not see a monomial replaced by one with as many generators -/

section Keys

open STree

variable {T : ℕ → Type}

lemma replace_cons_eq_update {k : ℕ} (M : VMono T k) (ch : Fin k → STree (VMono T)) {a : ℕ}
    (ha : a < k) (q : List ℕ) (u' : STree (VMono T)) :
    (STree.node M ch).replace (a :: q) u'
      = .node M (update ch ⟨a, ha⟩ ((ch ⟨a, ha⟩).replace q u')) := by
  rw [replace_node_cons]
  congr 1
  funext j
  by_cases hj : j = ⟨a, ha⟩
  · subst hj
    rw [update_self, if_pos rfl]
  · rw [update_of_ne hj, if_neg fun h'' => hj (Fin.ext h'')]

lemma VMono.pos {k : ℕ} (M : VMono T k) : 0 < k := by
  have := M.2
  omega

/-- The key of a vertex: the least leaf of its first child, and the generators above it. -/
lemma wkey_node_eq {k : ℕ} (M : VMono T k) (ch : Fin k → STree (VMono T)) :
    wkey (.node M ch) = toLex ((toBar (ch ⟨0, M.pos⟩)).first,
      M.1.1.weight + ∑ j, (toBar (ch j)).weight) := by
  have h1 : (toBar (.node M ch)).first = (toBar (ch ⟨0, M.pos⟩)).first := by
    rw [toBar_node, fl_false, first_subst ((isShuffle_allF _).2 M.isShuffle), first_allF,
      M.first, kids_of_lt ch M.pos, first_cutRoot]
  rw [wkey, STree.key, h1, weight_toBar_node]

/-- **Replacing the monomial of a vertex by one with as many generators keeps the key of the
tree.** -/
theorem wkey_replace : ∀ (t : STree (VMono T)) (q : List ℕ) {k : ℕ} {M M' : VMono T k}
    {ch : Fin k → STree (VMono T)}, t.get? q = some (.node M ch) →
    M'.1.1.weight = M.1.1.weight → wkey (t.replace q (.node M' ch)) = wkey t
  | t, [], k, M, M', ch, h, hw => by
    rw [get?_nil, Option.some_inj] at h
    rw [replace_nil, h, wkey_node_eq, wkey_node_eq, hw]
  | .leaf _, _ :: _, _, _, _, _, h, _ => by simp at h
  | .node M₀ c₀, a :: q, k, M, M', ch, h, hw => by
    obtain ⟨ha, h'⟩ := get?_node_cons_eq_some.1 h
    have ih := wkey_replace (c₀ ⟨a, ha⟩) q h' hw
    have ih1 : (toBar ((c₀ ⟨a, ha⟩).replace q (.node M' ch))).first
        = (toBar (c₀ ⟨a, ha⟩)).first := congrArg (fun κ : ℕ ×ₗ ℕ => (ofLex κ).1) ih
    have ih2 : (toBar ((c₀ ⟨a, ha⟩).replace q (.node M' ch))).weight
        = (toBar (c₀ ⟨a, ha⟩)).weight := congrArg (fun κ : ℕ ×ₗ ℕ => (ofLex κ).2) ih
    have hch : ∀ j, (toBar (update c₀ ⟨a, ha⟩ ((c₀ ⟨a, ha⟩).replace q (.node M' ch)) j)).first
          = (toBar (c₀ j)).first ∧
        (toBar (update c₀ ⟨a, ha⟩ ((c₀ ⟨a, ha⟩).replace q (.node M' ch)) j)).weight
          = (toBar (c₀ j)).weight := fun j => by
      by_cases hj : j = ⟨a, ha⟩
      · subst hj
        rw [update_self]
        exact ⟨ih1, ih2⟩
      · rw [update_of_ne hj]
        exact ⟨rfl, rfl⟩
    rw [replace_cons_eq_update M₀ c₀ ha, wkey_node_eq, wkey_node_eq, (hch _).1,
      Finset.sum_congr rfl fun j _ => (hch j).2]

/-- **Replacing the monomial of a vertex by one with as many generators keeps the keys of the
vertices.** -/
theorem wKeys_replace : ∀ (t : STree (VMono T)) (q : List ℕ) {k : ℕ} {M M' : VMono T k}
    {ch : Fin k → STree (VMono T)}, t.get? q = some (.node M ch) →
    M'.1.1.weight = M.1.1.weight → wKeys (t.replace q (.node M' ch)) = wKeys t
  | t, [], k, M, M', ch, h, hw => by
    have hk := wkey_replace t [] h hw
    rw [get?_nil, Option.some_inj] at h
    rw [replace_nil] at hk ⊢
    rw [h, wKeys_node, wKeys_node, ← h, hk, h]
  | .leaf _, _ :: _, _, _, _, _, h, _ => by simp at h
  | .node M₀ c₀, a :: q, k, M, M', ch, h, hw => by
    have hk := wkey_replace _ _ h hw (M' := M')
    obtain ⟨ha, h'⟩ := get?_node_cons_eq_some.1 h
    have ih := wKeys_replace (c₀ ⟨a, ha⟩) q h' hw (M' := M')
    rw [replace_cons_eq_update M₀ c₀ ha] at hk ⊢
    rw [wKeys_node, wKeys_node, hk]
    congr 3
    funext j
    by_cases hj : j = ⟨a, ha⟩
    · subst hj
      rw [update_self, ih]
    · rw [update_of_ne hj]

/-- **Replacing the monomial of a vertex by one with as many generators keeps the sign.** -/
theorem wsign_replace (K : Type u) [CommRing K] (t : STree (VMono T)) (q : List ℕ) {k : ℕ}
    {M M' : VMono T k} {ch : Fin k → STree (VMono T)} (h : t.get? q = some (.node M ch))
    (hw : M'.1.1.weight = M.1.1.weight) :
    wsign K (t.replace q (.node M' ch)) = wsign K t := by
  rw [wsign, wsign, wKeys_replace t q h hw]

end Keys

/-! ## One-vertex relators in shuffle coordinates -/

section Coord

open STree

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)

/-- **The basis of `T(E) (Fin k)`** of the shuffle trees on `0, …, k - 1`. -/
noncomputable def tBasisN (k : ℕ) :
    Module.Basis (SMono T (Finset.range k)) K (FreeGrL K E (Fin k)) :=
  (tBasis c hc (Fin k)).reindex (smonoCast (by rw [Fintype.card_fin]))

omit [IsEmpty (T 1)] in
lemma tBasisN_apply (k : ℕ) (m : SMono T (Finset.range k)) :
    tBasisN c hc k m = tBasis c hc (Fin k) (m.cast (by rw [Fintype.card_fin])) := by
  rw [tBasisN, Module.Basis.reindex_apply]
  rfl

variable {n : ℕ} (t : SMono (VMono T) (Finset.range n)) {q : List ℕ} {k : ℕ} {m₀ : VMono T k}
  {ch : Fin k → STree (VMono T)} (hq : t.1.get? q = some (.node m₀ ch))

omit [IsEmpty (T 1)] in
lemma Tq_tBasisN (m : SMono T (Finset.range k)) :
    Tq c hc t hq (tBasisN c hc k m) = barBasisN c hc n (replT t hq ⟨m, m₀.2⟩) := by
  rw [tBasisN_apply]
  exact Tq_tBasis c hc t hq ⟨m, m₀.2⟩

/-- The bar tree of the tree with the vertex at `q` relabelled by `m`, with its sign. -/
noncomputable def tqΦ (m : SMono T (Finset.range k)) : SMono (BE T) (Finset.range n) →₀ K :=
  ΦL c hc n (barBasisN c hc n (replT t hq ⟨m, m₀.2⟩))

lemma tqΦ_eq (m : SMono T (Finset.range k)) :
    tqΦ c hc t hq m = wsign K (replT t hq ⟨m, m₀.2⟩).1
      • Finsupp.single (treeEquiv n (replT t hq ⟨m, m₀.2⟩) : barSet T n).1 1 :=
  Φ_barBasisN c hc n _

/-- **`ΦL` of the trees labelled at a vertex by an operation**, in the coordinates of the
operation. -/
theorem ΦL_Tq (y : FreeGrL K E (Fin k)) :
    ΦL c hc n (Tq c hc t hq y)
      = Finsupp.linearCombination K (tqΦ c hc t hq) ((tBasisN c hc k).repr y) := by
  have h : (ΦL c hc n) ∘ₗ (Tq c hc t hq) = (Finsupp.linearCombination K (tqΦ c hc t hq)) ∘ₗ
      ((tBasisN c hc k).repr : FreeGrL K E (Fin k) →ₗ[K] _) :=
    (tBasisN c hc k).ext fun m => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Tq_tBasisN, LinearEquiv.coe_coe,
        Module.Basis.repr_self, Finsupp.linearCombination_single, one_smul]
      rfl
  exact LinearMap.congr_fun h y

/-- **A one-vertex relator is a relator in a bar context**, up to sign: if a bar context `F`
applied to the flagged monomials `h` is the bar tree of the tree with the vertex at `q`
relabelled by `f h`, then the combination of those trees along a rule in the context `f` is the
rule flagged in the context `F`. -/
theorem linearCombination_tqΦ_rule {C : Finset ℕ} (f : SMono T C → SMono T (Finset.range k))
    (F : SMono (BE T) C → SMono (BE T) (Finset.range n)) (β : Bool) (L : SMono T C)
    (v : SMono T C →₀ K)
    (hf : ∀ h : SMono T C, h.1.weight = L.1.weight → (f h).1.weight = (f L).1.weight)
    (hF : ∀ h : SMono T C, h.1.weight = L.1.weight →
      F (flM β h) = (treeEquiv n (replT t hq ⟨f h, m₀.2⟩) : barSet T n).1)
    (hv : ∀ m ∈ v.support, m.1.weight = L.1.weight) :
    Finsupp.linearCombination K (tqΦ c hc t hq)
        (Finsupp.single (f L) 1 - Finsupp.mapDomain f v)
      = wsign K (replT t hq ⟨f L, m₀.2⟩).1 • (Finsupp.single (F (flM β L)) 1
          - Finsupp.mapDomain F (Finsupp.mapDomain (flM β) v)) := by
  have hφ : ∀ h : SMono T C, h.1.weight = L.1.weight → tqΦ c hc t hq (f h)
      = wsign K (replT t hq ⟨f L, m₀.2⟩).1 • Finsupp.single (F (flM β h)) 1 := fun h hh => by
    rw [tqΦ_eq, hF h hh]
    congr 1
    have h1 : (replT t hq ⟨f h, m₀.2⟩).1
        = (replT t hq ⟨f L, m₀.2⟩).1.replace q (.node ⟨f h, m₀.2⟩ ch) :=
      (replace_replace _ _ _ _).symm
    rw [h1]
    exact wsign_replace K _ q (get?_replT t hq ⟨f L, m₀.2⟩) (hf h hh)
  rw [map_sub, Finsupp.linearCombination_single, one_smul, hφ L rfl, smul_sub,
    Finsupp.linearCombination_mapDomain, ← Finsupp.mapDomain_comp,
    Finsupp.linearCombination_apply, Finsupp.mapDomain, Finsupp.smul_sum]
  congr 1
  refine Finsupp.sum_congr fun m hm => ?_
  rw [Function.comp_apply, hφ m (hv m hm), smul_comm, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

end Coord

/-! ## Contexts of the vertex monomials and contexts of the bar trees -/

section Ctx

open STree

variable {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma subst_ne_leaf {g : STree T} (hg : ∀ a, g ≠ .leaf a) (xs : ℕ → STree T) (a : ℕ) :
    g.subst xs ≠ .leaf a := by
  cases g with
  | leaf b => exact absurd rfl (hg b)
  | node e c => exact fun h => by cases h

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
/-- A flagged monomial with the bar trees of the children substituted in a substitution. -/
lemma fl_subst_subst (β : Bool) {g : STree T} (hg : ∀ a, g ≠ .leaf a) (xs₀ : ℕ → STree T)
    (K : ℕ → STree (BE T)) :
    (fl β (g.subst xs₀)).subst K = (fl β g).subst fun a => (allF (xs₀ a)).subst K := by
  rw [fl_subst β hg, subst_subst]

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma fl_subst_inj {g g' : STree T} (hg : ∀ a, g ≠ .leaf a) (hg' : ∀ a, g' ≠ .leaf a)
    {b b' : Bool} {xs xs' : ℕ → STree (BE T)} (h : (fl b g).subst xs = (fl b' g').subst xs') :
    b = b' ∧ (allF g).subst xs = (allF g').subst xs' := by
  cases g with
  | leaf a => exact absurd rfl (hg a)
  | node e c =>
    cases g' with
    | leaf a => exact absurd rfl (hg' a)
    | node e' c' =>
      have h' : STree.node (e, b) (fun i => (allF (c i)).subst xs)
          = STree.node (e', b') (fun i => (allF (c' i)).subst xs') := h
      injection h' with hk he hc
      subst hk
      have he' := eq_of_heq he
      have hc' := eq_of_heq hc
      have h1 : e = e' := congrArg Prod.fst he'
      have h2 : b = b' := congrArg Prod.snd he'
      subst h1
      refine ⟨h2, ?_⟩
      show STree.node (e, false) (fun i => (allF (c i)).subst xs)
        = STree.node (e, false) (fun i => (allF (c' i)).subst xs')
      rw [hc']

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
/-- The least leaves of the trees over the leaves of a window, through the bar trees of the
children of the vertex. -/
lemma strictMonoOn_first_subst_kids {C : Finset ℕ} {k : ℕ} {M : VMono T k}
    {ch : Fin k → STree (VMono T)} (hs : (STree.node M ch).IsShuffle) {xs₀ : ℕ → STree T}
    (hsh : ∀ a ∈ C, (xs₀ a).IsShuffle) (hlt : ∀ a ∈ C, (xs₀ a).first < k) :
    StrictMonoOn (fun a => (xs₀ a).first) (C : Set ℕ) ↔
      StrictMonoOn (fun a => ((allF (xs₀ a)).subst (kids ch)).first) (C : Set ℕ) := by
  have hf : ∀ a ∈ C, ((allF (xs₀ a)).subst (kids ch)).first = (kids ch (xs₀ a).first).first :=
    fun a ha => by rw [first_subst ((isShuffle_allF _).2 (hsh a ha)), first_allF]
  have hk := strictMonoOn_first_kids hs
  constructor
  · intro h a ha a' ha' haa
    show ((allF (xs₀ a)).subst (kids ch)).first < ((allF (xs₀ a')).subst (kids ch)).first
    rw [hf a ha, hf a' ha']
    exact hk (hlt a ha) (hlt a' ha') (h ha ha' haa)
  · intro h a ha a' ha' haa
    have h1 := h ha ha' haa
    change ((allF (xs₀ a)).subst (kids ch)).first < ((allF (xs₀ a')).subst (kids ch)).first
      at h1
    rw [hf a ha, hf a' ha'] at h1
    show (xs₀ a).first < (xs₀ a').first
    by_contra hcon
    rcases Nat.eq_or_lt_of_le (not_lt.1 hcon) with he | hl
    · rw [he] at h1
      exact lt_irrefl _ h1
    · exact lt_asymm h1 (hk (hlt a' ha') (hlt a ha) hl)

variable {n : ℕ} (t : SMono (VMono T) (Finset.range n)) {q : List ℕ} {k : ℕ} {m₀ : VMono T k}
  {ch : Fin k → STree (VMono T)} (hq : t.1.get? q = some (.node m₀ ch))

/-- **A context of the monomial of a vertex is a context of the bar tree**: the bar trees of the
trees with the vertex at `q` relabelled by `f h`, `f` a context, are a bar context applied to
`h` flagged at the root. -/
theorem exists_barCtx {C : Finset ℕ} {f : SMono T C → SMono T (Finset.range k)} (hf : IsSCtx f)
    (L : SMono T C) (hL : ∀ a, L.1 ≠ .leaf a) :
    ∃ (F : SMono (BE T) C → SMono (BE T) (Finset.range n)) (β : Bool), IsSCtx F ∧
      ∀ h : SMono T C, (∀ a, h.1 ≠ .leaf a) →
        F (flM β h) = (treeEquiv n (replT t hq ⟨f h, m₀.2⟩) : barSet T n).1 := by
  obtain ⟨p₀, xs₀, hget, hin, hrep⟩ := IsSCtx.normal hf L
  have hqL := get?_replT t hq ⟨f L, m₀.2⟩
  have hs : (STree.node (⟨f L, m₀.2⟩ : VMono T k) ch).IsShuffle :=
    isShuffle_get? (replT t hq ⟨f L, m₀.2⟩).2.1 hqL
  have hlt : ∀ a ∈ C, (xs₀ a).first < k := fun a ha =>
    Finset.mem_range.1 (hin.labels a ha _ (first_mem (hin.shuffle a ha)))
  have hmono := (strictMonoOn_first_subst_kids hs hin.shuffle hlt).1 hin.mono
  have hget' : ((treeEquiv n (replT t hq ⟨f L, m₀.2⟩) : barSet T n).1).1.get?
      (bp (replT t hq ⟨f L, m₀.2⟩).1 q ++ p₀)
        = some ((flM (wflag q p₀) L).1.subst fun a => (allF (xs₀ a)).subst (kids ch)) := by
    have := get?_toBar_window hqL hget (subst_ne_leaf hL xs₀)
    rw [fl_subst_subst _ hL] at this
    exact this
  refine ⟨ctxOf _ _ (flM (wflag q p₀) L) _ hget' hmono, wflag q p₀, isSCtx_ctxOf _ _ _ _ _ _,
    fun h hh => Subtype.ext ?_⟩
  have h1 : (replT t hq ⟨f h, m₀.2⟩).1
      = (replT t hq ⟨f L, m₀.2⟩).1.replace q (.node ⟨f h, m₀.2⟩ ch) :=
    (replace_replace _ _ _ _).symm
  show ((treeEquiv n (replT t hq ⟨f L, m₀.2⟩) : barSet T n).1).1.replace _
      ((fl (wflag q p₀) h.1).subst fun a => (allF (xs₀ a)).subst (kids ch))
    = toBar (replT t hq ⟨f h, m₀.2⟩).1
  rw [h1, toBar_replace_window hqL hget ⟨f h, m₀.2⟩ (hrep h) (subst_ne_leaf hh xs₀),
    fl_subst_subst _ hh]
  rfl

/-- **A context of the bar trees with no cut above the root is a context of the monomial of a
vertex**: the bar trees `F (flM b h)`, `F` a bar context, are the bar trees of the trees with one
vertex relabelled by `f h`, `f` a context. -/
theorem exists_ctx_of_barCtx {C : Finset ℕ} {F : SMono (BE T) C → SMono (BE T) (Finset.range n)}
    (hF : IsSCtx F) (b : Bool) (L : SMono T C) (hL : ∀ a, L.1 ≠ .leaf a)
    (hr : rootF (F (flM b L)).1 = false) :
    ∃ (t : SMono (VMono T) (Finset.range n)) (q : List ℕ) (k : ℕ) (m₀ : VMono T k)
      (ch : Fin k → STree (VMono T)) (hq : t.1.get? q = some (.node m₀ ch))
      (f : SMono T C → SMono T (Finset.range k)), IsSCtx f ∧
        ∀ h : SMono T C, (∀ a, h.1 ≠ .leaf a) →
          F (flM b h) = (treeEquiv n (replT t hq ⟨f h, m₀.2⟩) : barSet T n).1 := by
  obtain ⟨t, ht⟩ := (treeEquiv n).surjective ⟨F (flM b L), hr⟩
  have hX : toBar t.1 = (F (flM b L)).1 := congrArg (fun X : barSet T n => X.1.1) ht
  obtain ⟨p, xs, hget, hin, hrep⟩ := IsSCtx.normal hF (flM b L)
  rw [← hX] at hget
  have hZ : ∀ a, (flM b L).1.subst xs ≠ .leaf a := fun a => by
    obtain ⟨l, e, c', hLn⟩ : ∃ (l : ℕ) (e : T l) (c' : Fin l → STree T), L.1 = .node e c' := by
      rcases hLc : L.1 with a' | ⟨e, c'⟩
      · exact absurd hLc (hL a')
      · exact ⟨_, e, c', rfl⟩
    rw [flM_val, hLn]
    exact fun h => by cases h
  obtain ⟨q, k, M, ch, p₀, Mp, h1, h2, h3, h4⟩ := exists_bp t.1 hget hZ
  have hw := get?_toBar_window h1 h2 h4
  rw [← h3, hget, Option.some_inj] at hw
  obtain ⟨hb, heq⟩ := fl_subst_inj hL h4 hw
  obtain ⟨xs₀, hMp, hxs⟩ := exists_subst_of_hang L.1 L.nodup Mp xs (kids ch) (isHang_kids ch) heq
  have hget₀ : M.1.1.get? p₀ = some (L.1.subst xs₀) := hMp ▸ h2
  have hs : (STree.node M ch).IsShuffle := isShuffle_get? t.2.1 h1
  have hMps : (L.1.subst xs₀).IsShuffle := isShuffle_get? M.isShuffle hget₀
  have hxa : ∀ a ∈ C, (L.1.subst xs₀).get? (L.1.pos a) = some (xs₀ a) := fun a ha =>
    get?_subst (STree.get?_pos (L.mem_labels.2 ha)) xs₀
  have hsh : ∀ a ∈ C, (xs₀ a).IsShuffle := fun a ha => isShuffle_get? hMps (hxa a ha)
  have hlt : ∀ a ∈ C, (xs₀ a).first < k := fun a ha =>
    M.lt (Multiset.mem_of_le ((labels_get?_le (hxa a ha)).trans (labels_get?_le hget₀))
      (first_mem (hsh a ha)))
  have hmono : StrictMonoOn (fun a => (xs₀ a).first) (C : Set ℕ) := by
    refine (strictMonoOn_first_subst_kids hs hsh hlt).2 fun a ha a' ha' haa => ?_
    show ((allF (xs₀ a)).subst (kids ch)).first < ((allF (xs₀ a')).subst (kids ch)).first
    rw [← hxs a (L.mem_labels.2 ha), ← hxs a' (L.mem_labels.2 ha')]
    exact hin.mono ha ha' haa
  refine ⟨t, q, k, M, ch, h1, ctxOf M.1 p₀ L xs₀ hget₀ hmono, isSCtx_ctxOf _ _ _ _ _ _,
    fun h hh => Subtype.ext ?_⟩
  show (F (flM b h)).1 = toBar (t.1.replace q (.node ⟨ctxOf M.1 p₀ L xs₀ hget₀ hmono h, M.2⟩ ch))
  rw [hrep (flM b h), ← hX, toBar_replace_window h1 h2 ⟨ctxOf M.1 p₀ L xs₀ hget₀ hmono h, M.2⟩
    rfl (subst_ne_leaf hh xs₀), fl_subst_subst _ hh, h3, ← hb, flM_val]
  congr 1
  refine subst_congr _ fun a ha => ?_
  rw [labels_fl, h.labels_eq, ← L.labels_eq] at ha
  exact hxs a ha

end Ctx

/-! ## The relator ideal and the ideal of the flagged rules -/

section Rules

open STree

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))
  {ρ : Type*} {O : STree.AdmOrder T} (G : Rules K ρ O.toCtxOrder)
  (hlead : ∀ i a, (G.lead i).1 ≠ .leaf a)
  (hom : ∀ i, ∀ m ∈ (G.tail i).support, m.1.weight = (G.lead i).1.weight)
  (hR : ∀ k (y : FreeGrL K E (Fin k)), y ∈ (GrOperadIdeal.span K r).sub (Fin k) ↔
    (tBasisN c hc k).repr y ∈ (G.rw (Finset.range k)).ideal)

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
/-- A context keeps equal numbers of generators equal. -/
lemma weight_ctx {C B : Finset ℕ} {f : SMono T C → SMono T B} (hf : IsSCtx f) {h L : SMono T C}
    (hw : h.1.weight = L.1.weight) : (f h).1.weight = (f L).1.weight := by
  obtain ⟨p, xs, hget, -, hrep⟩ := IsSCtx.normal hf L
  rw [hrep h]
  refine weight_replace hget ?_
  rw [weight_subst, weight_subst, hw, h.labels_eq, L.labels_eq]

include hlead hom in
/-- **A relation of the rules at a vertex is a relation of the flagged rules.** -/
theorem linearCombination_tqΦ_mem {n : ℕ} (t : SMono (VMono T) (Finset.range n)) {q : List ℕ}
    {k : ℕ} {m₀ : VMono T k} {ch : Fin k → STree (VMono T)}
    (hq : t.1.get? q = some (.node m₀ ch)) {v : SMono T (Finset.range k) →₀ K}
    (hv : v ∈ (G.rw (Finset.range k)).ideal) :
    Finsupp.linearCombination K (tqΦ c hc t hq) v ∈ (G.bar.rw (Finset.range n)).ideal := by
  refine Submodule.span_induction (p := fun x _ => Finsupp.linearCombination K
    (tqΦ c hc t hq) x ∈ (G.bar.rw (Finset.range n)).ideal) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨m, -, v', ⟨i, f, hf, rfl, rfl⟩, rfl⟩
    obtain ⟨F, β, hF, hFf⟩ := exists_barCtx t hq hf (G.lead i) (hlead i)
    rw [linearCombination_tqΦ_rule c hc t hq f F β (G.lead i) (G.tail i)
      (fun h hh => weight_ctx hf hh)
      (fun h hh => hFf h (not_leaf_of_weight hh (hlead i))) (hom i)]
    exact Submodule.smul_mem _ _
      ((G.bar.rw (Finset.range n)).sub_mem_ideal ⟨(i, β), F, hF, rfl, rfl⟩)
  · beta_reduce
    rw [map_zero]
    exact zero_mem _
  · intro x y _ _ hx hy
    beta_reduce at hx hy ⊢
    rw [map_add]
    exact add_mem hx hy
  · intro a x _ hx
    beta_reduce at hx ⊢
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

include hlead hom hR in
/-- **`ΦL` maps the relator ideal into the ideal of the flagged rules.** -/
theorem ΦL_mem_ideal_of_mem_krel {n : ℕ} {x : BarCoop (Ibar K E c hc) (Fin n)}
    (hx : x ∈ (Krel K E c hc r).sub (Fin n)) :
    ΦL c hc n x ∈ (G.bar.rw (Finset.range n)).ideal := by
  rw [krel_eq_span] at hx
  refine Submodule.span_induction (p := fun x _ => ΦL c hc n x
    ∈ (G.bar.rw (Finset.range n)).ideal) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨t, q, k, m₀, ch, hq, y, hy, rfl⟩
    rw [ΦL_Tq]
    exact linearCombination_tqΦ_mem c hc G hlead hom t hq ((hR k y).1 hy)
  · beta_reduce
    rw [map_zero]
    exact zero_mem _
  · intro x y _ _ hx hy
    beta_reduce at hx hy ⊢
    rw [map_add]
    exact add_mem hx hy
  · intro a x _ hx
    beta_reduce at hx ⊢
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

/-- **`ΦL` of the relator ideal.** -/
noncomputable def krelW (n : ℕ) : Submodule K (SMono (BE T) (Finset.range n) →₀ K) where
  carrier := {w | ∃ x : BarCoop (Ibar K E c hc) (Fin n),
    x ∈ (Krel K E c hc r).sub (Fin n) ∧ ΦL c hc n x = w}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, add_mem hx hy, map_add _ _ _⟩
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  smul_mem' := by
    rintro a _ ⟨x, hx, rfl⟩
    exact ⟨a • x, Submodule.smul_mem _ a hx, map_smul _ _ _⟩

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
include hlead hom in
/-- The monomials of a flagged rule in a context have the same flag at the root, number of
generators and cut edges. -/
lemma rule_mem_supported {A : Finset ℕ} (i : ρ) (b : Bool)
    {F : SMono (BE T) (G.src i) → SMono (BE T) A} (hF : IsSCtx F) :
    Finsupp.single (F (flM b (G.lead i))) (1 : K)
        - Finsupp.mapDomain F (Finsupp.mapDomain (flM b) (G.tail i))
      ∈ Finsupp.supported K K {X : SMono (BE T) A |
        rootF X.1 = rootF (F (flM b (G.lead i))).1 ∧
          X.1.weight = (F (flM b (G.lead i))).1.weight ∧
            cuts X = cuts (F (flM b (G.lead i)))} := by
  classical
  obtain ⟨fk, b', -, H⟩ := exists_merge_ctx hF (G.lead i) (hlead i) b
  refine sub_mem (Finsupp.single_mem_supported K _ ⟨rfl, rfl, rfl⟩) ?_
  rw [← Finsupp.mapDomain_comp]
  refine (Finsupp.mem_supported K _).2 fun y hy => ?_
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support (Finset.mem_coe.1 hy))
  obtain ⟨h1, h2, h3, -⟩ := H m (hom i m hm)
  exact ⟨h2, h3, h1⟩

include hlead hom hR in
/-- **A flagged rule in a context with no cut above the root is `ΦL` of an element of the
relator ideal.** -/
theorem prS_rule_mem {n : ℕ} (i : ρ) (b : Bool)
    {F : SMono (BE T) (G.src i) → SMono (BE T) (Finset.range n)} (hF : IsSCtx F) :
    prS (barSet T n) (Finsupp.single (F (flM b (G.lead i))) (1 : K)
        - Finsupp.mapDomain F (Finsupp.mapDomain (flM b) (G.tail i))) ∈ krelW c hc r n := by
  have hsupp := rule_mem_supported G hlead hom i b hF
  by_cases hr0 : rootF (F (flM b (G.lead i))).1 = false
  · have hg : prS (barSet T n) (Finsupp.single (F (flM b (G.lead i))) (1 : K)
        - Finsupp.mapDomain F (Finsupp.mapDomain (flM b) (G.tail i)))
        = Finsupp.single (F (flM b (G.lead i))) (1 : K)
          - Finsupp.mapDomain F (Finsupp.mapDomain (flM b) (G.tail i)) :=
      prS_of_mem (Finsupp.supported_mono (fun X hX => hX.1.trans hr0) hsupp)
    rw [hg]
    obtain ⟨t, q, k, m₀, ch, hq, f, hf, hFf⟩ :=
      exists_ctx_of_barCtx hF b (G.lead i) (hlead i) hr0
    have hrule := linearCombination_tqΦ_rule c hc t hq f F b (G.lead i) (G.tail i)
      (fun h hh => weight_ctx hf hh)
      (fun h hh => hFf h (not_leaf_of_weight hh (hlead i))) (hom i)
    have hy : (tBasisN c hc k).repr.symm (Finsupp.single (f (G.lead i)) 1
        - Finsupp.mapDomain f (G.tail i)) ∈ (GrOperadIdeal.span K r).sub (Fin k) :=
      (hR k _).2 (by
        rw [LinearEquiv.apply_symm_apply]
        exact (G.rw (Finset.range k)).sub_mem_ideal ⟨i, f, hf, rfl, rfl⟩)
    refine ⟨wsign K (replT t hq ⟨f (G.lead i), m₀.2⟩).1 • Tq c hc t hq _,
      Submodule.smul_mem _ _ (Tq_mem_Krel c hc r t hq hy), ?_⟩
    rw [map_smul, ΦL_Tq, LinearEquiv.apply_symm_apply, hrule, smul_smul, wsign_mul_self,
      one_smul]
  · have hg : prS (barSet T n) (Finsupp.single (F (flM b (G.lead i))) (1 : K)
        - Finsupp.mapDomain F (Finsupp.mapDomain (flM b) (G.tail i))) = 0 :=
      prS_of_disjoint hsupp fun X hX hX' => hr0 (hX.1.symm.trans hX')
    rw [hg]
    exact zero_mem _

include hlead hom hR in
/-- **`ΦL` reflects the relator ideal**: an element of `B(T, Ī)` whose image lies in the ideal of
the flagged rules lies in the relator ideal. -/
theorem mem_krel_of_ΦL_mem {n : ℕ} {x : BarCoop (Ibar K E c hc) (Fin n)}
    (hx : ΦL c hc n x ∈ (G.bar.rw (Finset.range n)).ideal) :
    x ∈ (Krel K E c hc r).sub (Fin n) := by
  have hle : ∀ v ∈ (G.bar.rw (Finset.range n)).ideal, prS (barSet T n) v ∈ krelW c hc r n :=
    fun v hv => by
      refine Submodule.span_induction (p := fun v _ => prS (barSet T n) v ∈ krelW c hc r n)
        ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨m, -, v', ⟨⟨i, b⟩, F, hF, rfl, rfl⟩, rfl⟩
        exact prS_rule_mem c hc r G hlead hom hR i b hF
      · beta_reduce
        rw [map_zero]
        exact zero_mem _
      · intro x y _ _ hx hy
        beta_reduce at hx hy ⊢
        rw [map_add]
        exact add_mem hx hy
      · intro a x _ hx
        beta_reduce at hx ⊢
        rw [map_smul]
        exact Submodule.smul_mem _ _ hx
  have h1 := hle _ hx
  have h2 : prS (barSet T n) (ΦL c hc n x) = ΦL c hc n x :=
    prS_of_mem (ΦL_mem_supported c hc n x)
  rw [h2] at h1
  obtain ⟨x', hx', he⟩ := h1
  rwa [← ΦL_injective c hc n he]

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
include hlead hom in
/-- **The ideal of the flagged rules is stable under the projections onto the bidegrees.** -/
theorem prS_mem_ideal {A : Finset ℕ} (w s : ℕ) {v : SMono (BE T) A →₀ K}
    (hv : v ∈ (G.bar.rw A).ideal) : prS (Bar.P A w s) v ∈ (G.bar.rw A).ideal := by
  refine Submodule.span_induction (p := fun v _ => prS (Bar.P A w s) v ∈ (G.bar.rw A).ideal)
    ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨m, -, v', ⟨⟨i, b⟩, F, hF, rfl, rfl⟩, rfl⟩
    have hsupp := rule_mem_supported G hlead hom i b hF
    show prS (Bar.P A w s) (Finsupp.single (F (flM b (G.lead i))) (1 : K)
      - Finsupp.mapDomain F (Finsupp.mapDomain (flM b) (G.tail i))) ∈ (G.bar.rw A).ideal
    by_cases hP : F (flM b (G.lead i)) ∈ Bar.P A w s
    · have hg : prS (Bar.P A w s) (Finsupp.single (F (flM b (G.lead i))) (1 : K)
          - Finsupp.mapDomain F (Finsupp.mapDomain (flM b) (G.tail i)))
          = Finsupp.single (F (flM b (G.lead i))) (1 : K)
            - Finsupp.mapDomain F (Finsupp.mapDomain (flM b) (G.tail i)) :=
        prS_of_mem (Finsupp.supported_mono (show _ ⊆ Bar.P A w s from fun X hX =>
          ⟨hX.1.trans hP.1, hX.2.1.trans hP.2.1,
            (congrArg (fun S : Finset (ℕ ×ₗ ℕ) => S.card + 1) hX.2.2).trans hP.2.2⟩) hsupp)
      rw [hg]
      exact (G.bar.rw A).sub_mem_ideal ⟨(i, b), F, hF, rfl, rfl⟩
    · have hg : prS (Bar.P A w s) (Finsupp.single (F (flM b (G.lead i))) (1 : K)
          - Finsupp.mapDomain F (Finsupp.mapDomain (flM b) (G.tail i))) = 0 :=
        prS_of_disjoint hsupp fun X hX hX' => hP ⟨hX.1.symm.trans hX'.1,
          hX.2.1.symm.trans hX'.2.1,
          (congrArg (fun S : Finset (ℕ ×ₗ ℕ) => S.card + 1) hX.2.2).symm.trans hX'.2.2⟩
      rw [hg]
      exact zero_mem _
  · beta_reduce
    rw [map_zero]
    exact zero_mem _
  · intro x y _ _ hx hy
    beta_reduce at hx hy ⊢
    rw [map_add]
    exact add_mem hx hy
  · intro a x _ hx
    beta_reduce at hx ⊢
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

include hlead hom hR in
/-- **The bridge on the leaves `0, …, n - 1`**: for quadratic relators on generators of any
arity over a field of characteristic zero, and homogeneous rules whose ideal is the ideal of the
relators in shuffle coordinates, the presented operad is Koszul iff in every arity `n ≥ 2` the
homology of the bar construction of the free shuffle operad modulo the flagged rules vanishes
below the diagonal. -/
theorem isKoszul_iff_rules_range [CharZero K] (hq : Koszul.IsQuadratic K E r) :
    Koszul.IsKoszul K E r ↔ ∀ n, 2 ≤ n → ∀ w s, s < w →
      ∀ v ∈ Bar.C K (Finset.range n) w s, STree.Bar.d K v ∈ (G.bar.rw (Finset.range n)).ideal →
        ∃ u ∈ Bar.C K (Finset.range n) w (s + 1),
          v - STree.Bar.d K u ∈ (G.bar.rw (Finset.range n)).ideal :=
  isKoszul_iff_shuffle_of_J c hc r hq (fun n => (G.bar.rw (Finset.range n)).ideal)
    (fun _ w s _ hv => prS_mem_ideal G hlead hom w s hv)
    (fun _ _ _ => ⟨mem_krel_of_ΦL_mem c hc r G hlead hom hR,
      ΦL_mem_ideal_of_mem_krel c hc r G hlead hom hR⟩)

end Rules

end ShuffleAnySym

end Operad
