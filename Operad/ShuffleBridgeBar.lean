/-
# The bridge between the binary and the any-arity bar constructions

`Operad.ShuffleBridge` translates binary shuffle monomials into shuffle monomials with binary
generators. A binary bar tree `ShuffleBar.BarTree (F 2)` is a binary tree on `F 2 × Bool`, and
`BE F` again has binary generators, so the same translation `ShuffleBridge.toS` carries bar trees
to the bar trees `STree (BE F)` of `Operad.ShuffleAnyBar`.

* **Keys.** The binary key of a vertex, its least label and number of leaves, is the any-arity
  key, its least leaf and number of vertices, with one added to the second entry
  (`ShuffleBridge.kup`, `ShuffleBridge.key_toS`); so the cut edges correspond
  (`ShuffleBridge.cutKeys_toS`), merging is clearing a flag (`ShuffleBridge.toS_mergeK`), and the
  signs agree (`ShuffleBridge.sgn_toS`).
* **The differentials agree** under the map of bar monomials to binary bar trees
  (`ShuffleBridge.barMap`, `ShuffleBridge.barMap_d`), and the binary bar construction in arity
  `n` and degree `s` is the image of the any-arity one on `0, …, n - 1`
  (`ShuffleBridge.C_le_map`, `ShuffleBridge.map_C_le`).
* **The relator subcomplex and the ideal of the flagged rules.** Under the hypotheses `hsrc` and
  `hR` of `Operad.ShuffleBridge`, a bar monomial combination whose image lies in `ShuffleBar.J`
  lies in the ideal of `Rules.bar` (`ShuffleBridge.mem_ideal_of_barMap`), and the ideal of
  `Rules.bar`, on combinations whose roots are not cut, maps into `ShuffleBar.J`
  (`ShuffleBridge.barMap_mem_J`). The generators of either side are homogeneous, in the leaves
  for `ShuffleBar.J` and in the root flag for `Rules.bar` (`ShuffleBridge.rootF_ctx`), so a
  projection onto the relevant monomials (`ShuffleBridge.proj`) keeps them in the span.
* Hence **`Rules.IsKoszul` gives `ShuffleBar.IsKoszul`**
  (`ShuffleBridge.shuffleBar_isKoszul_of_isKoszul`).
* **Relabelling.** Relabelling the leaves along a map strictly increasing on them moves the least
  leaf of every key (`ShuffleBridge.rkey`, `ShuffleBridge.cutKeys_relabel`,
  `ShuffleBridge.setF_relabel`), keeps the bar trees of each weight and degree
  (`ShuffleBridge.mem_P_relabelM`) and commutes with the differential
  (`ShuffleBridge.d_relabelM`). Relabelling along the positions is a context with an inverse
  context, so it carries the any-arity bar construction on any set of leaves, with the ideal of
  the flagged rules, onto the one on `0, …, n - 1`.
* Hence **binary Koszulness gives `Rules.IsKoszul`** (`ShuffleBridge.isKoszul_of_shuffleBar`,
  through `ShuffleBridge.exact_range`), and **the two predicates agree**:
  `ShuffleBar.IsKoszul K R ↔ G.IsKoszul` under `hsrc` and `hR` alone
  (`ShuffleBridge.isKoszul_iff`). For the commutative and associative operads:
  `ComBin.isKoszul_iff`, `AssBin.isKoszul_iff`.
-/
import Operad.ShuffleBridge

universe v

namespace Operad

namespace ShuffleBridge

open STree

variable {F : ℕ → Type v}

instance [BinaryGens F] : BinaryGens (BE F) :=
  ⟨fun k hk => ⟨fun d => ((BinaryGens.isEmpty_of_ne k hk).false d.1).elim⟩⟩

/-! ## Keys, cuts and merges -/

/-- **The binary key of an any-arity key**: a vertex with `w` vertices below and including it has
`w + 1` leaves. -/
def kup (k : ℕ ×ₗ ℕ) : ℕ ×ₗ ℕ := toLex ((ofLex k).1, (ofLex k).2 + 1)

lemma kup_injective : Function.Injective kup := fun a b h => by
  have h' := congrArg ofLex h
  simp only [kup, ofLex_toLex, Prod.mk.injEq, Nat.add_right_cancel_iff] at h'
  exact ofLex.injective (Prod.ext h'.1 h'.2)

lemma kup_lt_kup {a b : ℕ ×ₗ ℕ} : kup a < kup b ↔ a < b := by
  rw [kup, kup, Prod.Lex.toLex_lt_toLex, ← toLex_ofLex a, ← toLex_ofLex b,
    Prod.Lex.toLex_lt_toLex]
  simp only [ofLex_toLex, Nat.add_lt_add_iff_right]

lemma key_toS (t : LTree (F 2)) (ht : t.IsShuffle) : LTree.key t = kup (STree.key (toS t)) := by
  have hw := weight_toS t
  rw [LTree.key, STree.key, kup, ofLex_toLex, first_toS t ht, hw]

lemma rootF_toS (x : ShuffleBar.BarTree (F 2)) :
    rootF (toS (F := BE F) x) = ShuffleBar.rootFlag x := by
  cases x <;> rfl

lemma univ_fin_two : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide

lemma cutKeys_toS : ∀ x : ShuffleBar.BarTree (F 2), x.IsShuffle →
    ShuffleBar.cutKeys x = (cutKeys (toS (F := BE F) x)).image kup
  | .leaf _, _ => rfl
  | .node d l r, h => by
    have hl := cutKeys_toS l h.2.1
    have hr := cutKeys_toS r h.2.2
    have hk := key_toS (F := BE F) (.node d l r) h
    rw [ShuffleBar.cutKeys, toS_node, STree.cutKeys, univ_fin_two, Finset.biUnion_insert,
      Finset.singleton_biUnion, Finset.image_union, Finset.image_union, hl, hr, ← toS_node]
    congr 1
    split_ifs <;> simp [hk]

lemma toS_mergeK : ∀ x : ShuffleBar.BarTree (F 2), x.IsShuffle → ∀ k : ℕ ×ₗ ℕ,
    toS (F := BE F) (ShuffleBar.mergeK x (kup k)) = setF k false (toS (F := BE F) x)
  | .leaf _, _, _ => rfl
  | .node d l r, h, k => by
    have hkey := key_toS (F := BE F) (.node d l r) h
    have hw := weight_toS (F := BE F) (.node d l r)
    by_cases hk : STree.key (toS (F := BE F) (.node d l r)) = k
    · have hkw : (ofLex k).2 + 1 = (LTree.node d l r).arity := by
        rw [← hk, STree.key, ofLex_toLex]
        exact hw
      have hal : l.arity < (ofLex (kup k)).2 := by
        simp only [kup, ofLex_toLex, LTree.arity] at hkw ⊢
        have := LTree.arity_pos r
        omega
      have har : r.arity < (ofLex (kup k)).2 := by
        simp only [kup, ofLex_toLex, LTree.arity] at hkw ⊢
        have := LTree.arity_pos l
        omega
      have hwl : ∀ t : ShuffleBar.BarTree (F 2), t.IsShuffle → t.arity < (ofLex (kup k)).2 →
          setF k false (toS (F := BE F) t) = toS t := fun t ht hlt => by
        refine setF_of_notMem false fun hm => ?_
        have h1 :=
          (mem_vkeys (t := toS (F := BE F) t) ((isShuffle_toS_iff (F := BE F) t).2 ht) hm).2
        have h2 := weight_toS (F := BE F) t
        simp only [kup, ofLex_toLex] at hlt
        omega
      have hml := ShuffleBar.mergeK_of_not_mem l (ShuffleBar.not_mem_cutKeys_of_arity hal)
      have hmr := ShuffleBar.mergeK_of_not_mem r (ShuffleBar.not_mem_cutKeys_of_arity har)
      rw [toS_node, setF_node, ← toS_node, if_pos hk]
      have hc : (fun i => setF k false ((![toS (F := BE F) l, toS r] : Fin 2 → _) i)) =
          ![toS (F := BE F) l, toS r] := by
        funext i
        fin_cases i
        · exact hwl l h.2.1 hal
        · exact hwl r h.2.2 har
      rw [hc]
      by_cases hd : d.2 = true
      · rw [ShuffleBar.mergeK, if_pos ⟨hd, by rw [hkey, hk]⟩]
        rfl
      · rw [ShuffleBar.mergeK, if_neg (fun h' => hd h'.1), hml, hmr, toS_node]
        congr 1
        exact Prod.ext rfl (by simpa using hd)
    · rw [ShuffleBar.mergeK, if_neg (fun h' => hk (kup_injective (hkey ▸ h'.2))), toS_node,
        toS_node, setF_node,
        if_neg (show ¬ (STree.node d ![toS (F := BE F) l, toS (F := BE F) r]).key = k from hk),
        toS_mergeK l h.2.1 k, toS_mergeK r h.2.2 k]
      congr 1
      funext i
      fin_cases i <;> rfl

lemma sgn_toS (K : Type*) [CommRing K] (x : ShuffleBar.BarTree (F 2)) (hx : x.IsShuffle)
    (k : ℕ ×ₗ ℕ) :
    ShuffleBar.sgn K x (kup k) = CutComplex.sgn K (cutKeys (toS (F := BE F) x)) k := by
  rw [ShuffleBar.sgn, CutComplex.sgn, cutKeys_toS x hx, Finset.filter_image,
    Finset.card_image_of_injective _ kup_injective]
  simp only [kup_lt_kup]

/-! ## The bar constructions -/

variable (K : Type*) [CommRing K]

/-- **Bar monomials as binary bar trees.** -/
noncomputable def barMap (A : Finset ℕ) :
    (SMono (BE F) A →₀ K) →ₗ[K] (ShuffleBar.BarTree (F 2) →₀ K) :=
  Finsupp.lmapDomain K K fun X => ofS X.1

lemma barMap_single {A : Finset ℕ} (X : SMono (BE F) A) (c : K) :
    barMap K A (Finsupp.single X c) = Finsupp.single (ofS X.1) c := by
  rw [barMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

variable [BinaryGens F]

lemma barMap_injective (A : Finset ℕ) : Function.Injective (barMap (F := F) K A) :=
  Finsupp.mapDomain_injective fun X Y h => Subtype.ext (by
    rw [← toS_ofS X.1, ← toS_ofS Y.1]
    exact congrArg toS h)

lemma isShuffle_ofS {A : Finset ℕ} (X : SMono (BE F) A) : (ofS X.1).IsShuffle := by
  rw [← isShuffle_toS_iff, toS_ofS]
  exact X.isShuffle

/-- **The differentials agree.** -/
theorem barMap_d (A : Finset ℕ) (v : SMono (BE F) A →₀ K) :
    barMap K A (Bar.d K v) = ShuffleBar.d K (barMap K A v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single X c =>
    rw [Bar.d, CutComplex.d_single, barMap_single, ShuffleBar.d_single, map_smul,
      CutComplex.dX, ShuffleBar.dTree, cutKeys_toS _ (isShuffle_ofS X), toS_ofS,
      Finset.sum_image fun a _ b _ h => kup_injective h, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, barMap_single, sgn_toS K _ (isShuffle_ofS X), toS_ofS]
    congr 2
    apply toS_injective
    rw [toS_mergeK _ (isShuffle_ofS X), toS_ofS, toS_ofS]
    rfl

/-! ## Flags -/

omit [BinaryGens F] in
lemma toS_unflag : ∀ m : LTree (F 2),
    toS (F := BE F) (m.mapDec (·, false)) = allF (toS m)
  | .leaf _ => rfl
  | .node e l r => by
    rw [LTree.mapDec_node, toS_node, toS_node, allF_node, toS_unflag l, toS_unflag r]
    congr 1
    funext i
    fin_cases i <;> rfl

omit [BinaryGens F] in
lemma toS_liftW (b : Bool) : ∀ m : LTree (F 2),
    toS (F := BE F) (ShuffleBar.liftW b m) = fl b (toS m)
  | .leaf _ => rfl
  | .node e l r => by
    show STree.node (e, b) ![toS (F := BE F) (l.mapDec (·, false)), toS (r.mapDec (·, false))] = _
    rw [toS_node, fl_node, toS_unflag, toS_unflag]
    congr 1
    funext i
    fin_cases i <;> rfl

lemma ofS_fl (b : Bool) (t : STree F) : ofS (F := BE F) (fl b t) = ShuffleBar.liftW b (ofS t) :=
  toS_injective (by rw [toS_ofS, toS_liftW, toS_ofS])

omit [BinaryGens F] in
/-- **The flags of a window lifted from a monomial**: the upper vertex carries the flag of the
lift, the lower one is not cut. -/
lemma flags_of_windowRoot {E : Type*} : ∀ (u : ShuffleBar.BarTree E) (s : Bool), u.IsEdgeRoot s →
    ∀ (b : Bool) (m : LTree E), u.windowRoot s = ShuffleBar.liftW b m →
      ShuffleBar.rootFlag u = b ∧ ShuffleBar.rootFlag (u.subtreeAt [s]) = false
  | .node (e, c) (.node (f, c') a a') d, false, _, b, m, h => by
    cases m with
    | leaf _ => simp [LTree.windowRoot, LTree.window, ShuffleBar.liftW] at h
    | node e' l r =>
      cases l with
      | leaf _ => simp [LTree.windowRoot, LTree.window, ShuffleBar.liftW] at h
      | node f' l' r' =>
        simp only [LTree.windowRoot, LTree.window, ShuffleBar.liftW, LTree.mapDec_node,
          Bool.false_eq_true, if_false, LTree.node.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.2, h.2.1.1.2⟩
  | .node (e, c) d (.node (f, c') a a'), true, _, b, m, h => by
    have hw : LTree.windowRoot (.node (e, c) d (.node (f, c') a a')) true =
        LTree.window (e, c) (f, c') true a.minLabel a'.minLabel d.minLabel := by cases d <;> rfl
    rw [hw] at h
    cases m with
    | leaf _ => simp [LTree.window, ShuffleBar.liftW] at h
    | node e' l r =>
      cases r with
      | leaf _ => simp [LTree.window, ShuffleBar.liftW] at h
      | node f' l' r' =>
        simp only [LTree.window, ShuffleBar.liftW, LTree.mapDec_node, if_true,
          LTree.node.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.2, h.2.2.1.2⟩
  | .leaf _, false, he, _, _, _ => absurd he (by simp [LTree.IsEdgeRoot])
  | .leaf _, true, he, _, _, _ => absurd he (by simp [LTree.IsEdgeRoot])
  | .node _ (.leaf _) _, false, he, _, _, _ => absurd he (by simp [LTree.IsEdgeRoot])
  | .node _ _ (.leaf _), true, he, _, _, _ =>
    absurd he (by cases ‹LTree _› <;> simp [LTree.IsEdgeRoot])

omit [BinaryGens F] in
lemma rootF_subst_of_ne_leaf {E : ℕ → Type v} {t : STree (BE E)} (ht : ∀ a, t ≠ leaf a)
    (xs : ℕ → STree (BE E)) : rootF (t.subst xs) = rootF t := by
  cases t with
  | leaf a => exact absurd rfl (ht a)
  | node d c => rfl

omit [BinaryGens F] in
/-- **A context keeps the root flags equal.** -/
lemma rootF_ctx {E : ℕ → Type v} {A B : Finset ℕ} {f : SMono (BE E) A → SMono (BE E) B}
    (hf : IsSCtx f) {X Y : SMono (BE E) A} (hX : ∀ a, X.1 ≠ leaf a) (hY : ∀ a, Y.1 ≠ leaf a)
    (h : rootF X.1 = rootF Y.1) : rootF (f X).1 = rootF (f Y).1 := by
  obtain ⟨T, p, xs, -, -, hfe⟩ := hf
  rw [hfe, hfe]
  rcases p with _ | ⟨i, p⟩
  · rw [replace_nil, replace_nil, rootF_subst_of_ne_leaf hX, rootF_subst_of_ne_leaf hY, h]
  · rw [rootF_replace T (List.cons_ne_nil _ _), rootF_replace T (List.cons_ne_nil _ _)]

/-! ## Projections onto a set of monomials -/

section Proj

variable {X : Type*} (P : X → Prop)

open Classical in
/-- **The projection onto the combinations of the monomials satisfying `P`.** -/
noncomputable def proj : (X →₀ K) →ₗ[K] (X →₀ K) :=
  Finsupp.linearCombination K fun x => if P x then Finsupp.single x 1 else 0

omit [BinaryGens F] in
lemma proj_of_supported {v : X →₀ K} (hv : v ∈ Finsupp.supported K K {x | P x}) :
    proj K P v = v := by
  rw [Finsupp.supported_eq_span_single] at hv
  induction hv using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨x, hx, rfl⟩ := h
    rw [proj, Finsupp.linearCombination_single, if_pos (show P x from hx), one_smul]
  | zero => rw [map_zero]
  | add _ _ _ _ h₁ h₂ => rw [map_add, h₁, h₂]
  | smul c _ _ h => rw [map_smul, h]

omit [BinaryGens F] in
lemma proj_of_supported_not {v : X →₀ K} (hv : v ∈ Finsupp.supported K K {x | ¬ P x}) :
    proj K P v = 0 := by
  rw [Finsupp.supported_eq_span_single] at hv
  induction hv using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨x, hx, rfl⟩ := h
    rw [proj, Finsupp.linearCombination_single, if_neg (show ¬ P x from hx), smul_zero]
  | zero => rw [map_zero]
  | add _ _ _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
  | smul c _ _ h => rw [map_smul, h, smul_zero]

end Proj

omit [BinaryGens F] in
lemma mapDomain_mem_supported {X Y : Type*} {f : X → Y} {S : Set Y} (v : X →₀ K)
    (h : ∀ x ∈ v.support, f x ∈ S) : Finsupp.mapDomain f v ∈ Finsupp.supported K K S := by
  classical
  refine (Finsupp.mem_supported K _).2 fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
  exact h x hx

/-! ## Degrees -/

section Degrees

variable {K}

lemma labels_ofS {A : Finset ℕ} (X : SMono (BE F) A) :
    ((ofS X.1).labels : Multiset ℕ) = A.val := by
  rw [← labels_toS, toS_ofS]
  exact X.labels_eq

lemma adm_ofS {n w s : ℕ} {X : SMono (BE F) (Finset.range n)}
    (hX : X ∈ Bar.P (Finset.range n) w s) : ShuffleBar.Adm n s (ofS X.1) := by
  have hl := labels_ofS X
  refine ⟨⟨isShuffle_ofS X, ?_, ?_⟩, ?_, ?_⟩
  · rw [← Multiset.coe_nodup, hl]
    exact (Finset.range n).nodup
  · rw [← rootF_toS, toS_ofS]
    exact hX.1
  · have hl' : ((ofS X.1).labels : Multiset ℕ) = (List.range n : Multiset ℕ) := by
      rw [hl, Finset.range_val, Multiset.coe_range]
    exact Multiset.coe_eq_coe.1 hl'
  · rw [cutKeys_toS _ (isShuffle_ofS X), toS_ofS, Finset.card_image_of_injective _ kup_injective]
    exact hX.2.2

omit [BinaryGens F] in
lemma exists_of_adm {n s : ℕ} {y : ShuffleBar.BarTree (F 2)} (hy : ShuffleBar.Adm n s y) :
    ∃ X : SMono (BE F) (Finset.range n), X ∈ Bar.P (Finset.range n) (n - 1) s ∧ ofS X.1 = y := by
  have hl : (toS (F := BE F) y).labels = (Finset.range n).val := by
    rw [labels_toS, Finset.range_val, ← Multiset.coe_range]
    exact Multiset.coe_eq_coe.2 hy.2.1
  refine ⟨⟨toS y, (isShuffle_toS_iff _).2 hy.1.shuffle, hl⟩, ⟨?_, ?_, ?_⟩, ofS_toS (F := BE F) y⟩
  · show rootF (toS (F := BE F) y) = false
    rw [rootF_toS]
    exact hy.1.root
  · show (toS (F := BE F) y).weight = n - 1
    have h1 := weight_toS (F := BE F) y
    have h2 := hy.2.1.length_eq
    rw [LTree.length_labels, List.length_range] at h2
    omega
  · show (cutKeys (toS (F := BE F) y)).card + 1 = s
    have := hy.2.2
    rwa [cutKeys_toS y hy.1.shuffle, Finset.card_image_of_injective _ kup_injective] at this

variable (K : Type*) [Field K]

omit [BinaryGens F] in
lemma C_le_map (n s : ℕ) : ShuffleBar.C K n s ≤
    (Bar.C K (Finset.range n) (n - 1) s).map (barMap (F := F) K (Finset.range n)) := by
  rw [ShuffleBar.C, Finsupp.supported_eq_span_single, Submodule.span_le]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨X, hX, rfl⟩ := exists_of_adm (F := F) hy
  exact ⟨Finsupp.single X 1, Finsupp.single_mem_supported K _ hX, barMap_single K X 1⟩

lemma map_C_le (n w s : ℕ) :
    (Bar.C K (Finset.range n) w s).map (barMap (F := F) K (Finset.range n)) ≤
      ShuffleBar.C K n s := by
  rw [Bar.C, Finsupp.supported_eq_span_single, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, barMap_single]
  exact Finsupp.single_mem_supported K _ (adm_ofS hX)

end Degrees

end ShuffleBridge

namespace ShuffleBridge

open STree

section Ideals

variable {F : ℕ → Type v} [BinaryGens F] [Fintype (F 2)] [DecidableEq (F 2)]

/-- **The context of an edge**, on any set of leaves: substituting at an edge of a binary shuffle
tree with distinct leaves `B` is a context from the monomials on `0, 1, 2`. -/
theorem exists_ctx_of_edge' {B : Finset ℕ} (x : LTree (F 2)) (hxs : x.IsShuffle)
    (hxl : (x.labels : Multiset ℕ) = B.val) {p : List Bool} {s : Bool} (he : x.IsEdge p s) :
    ∃ f : SMono F (Finset.range 3) → SMono F B, IsSCtx f ∧
      ∀ g, (f g).1 = toS (x.substAt p s (ofS g.1)) := by
  have hnd : x.labels.Nodup := by
    rw [← Multiset.coe_nodup, hxl]
    exact B.nodup
  have hw := LTree.winSpec_of_edge he hxs hnd
  have hmem : ∀ g : SMono F (Finset.range 3), (toS (x.substAt p s (ofS g.1))).IsShuffle ∧
      (toS (x.substAt p s (ofS g.1))).labels = B.val := fun g => by
    have hg := (LTree.mem_monomials 3 _).1 (ofS_mem g)
    refine ⟨(isShuffle_toS_iff _).2 (LTree.isShuffle_substAt he hxs hnd hg.1 hg.2), ?_⟩
    rw [labels_toS, ← hxl]
    exact Multiset.coe_eq_coe.2 (LTree.perm_labels_substAt he hxs hnd hg.2)
  refine ⟨fun g => ⟨_, hmem g⟩,
    ⟨toS x, bpath p, fun a => toS ((x.subtreeAt p).winIns s a), ?_, ⟨fun a _ => ?_,
      fun a ha b hb => ?_, fun a ha b hb hab => ?_⟩, fun g => ?_⟩, fun g => rfl⟩
  · obtain ⟨e, l, r, h⟩ := he.exists_node
    rw [get?_toS x p h]
    rfl
  · exact (isShuffle_toS_iff _).2 (hw.shuffle a)
  · rw [labels_toS, Multiset.mem_coe] at hb
    have ha3 : a < 3 := Finset.mem_range.1 ha
    have hb' : b ∈ (x.subtreeAt p).labels := by
      refine hw.perm.symm.subset ?_
      simp only [List.mem_append]
      interval_cases a
      · exact Or.inl (Or.inl hb)
      · exact Or.inl (Or.inr hb)
      · exact Or.inr hb
    have : b ∈ (x.labels : Multiset ℕ) := Multiset.mem_coe.2 (LTree.labels_subtreeAt_subset _ _ hb')
    rw [hxl] at this
    exact this
  · simp only
    rw [first_toS _ (hw.shuffle a), first_toS _ (hw.shuffle b)]
    exact hw.mono a b hab (Finset.mem_range.1 hb)
  · show toS (x.substAt p s (ofS g.1)) = _
    rw [toS_substAt, toS_ofS]

/-! ## The relator subcomplex and the ideal of the flagged rules -/

variable {K : Type*} [Field K] {ρ : Type*} {O : AdmOrder F} (G : Rules K ρ O.toCtxOrder)
  (hsrc : ∀ r, G.src r = Finset.range 3) {R : Submodule K (LTree.Mono (F 2) 3 → K)}
  (hR : R.map (vecEquiv F K 3).toLinearMap = Submodule.span K (Set.range (ruleVec G hsrc)))

include hR in
/-- **A relator with its root flagged lies in the ideal of the flagged rules.** -/
lemma mapDomain_flM_mem {r : LTree.Mono (F 2) 3 → K} (hr : r ∈ R) (c : Bool) :
    Finsupp.mapDomain (flM c) (vecEquiv F K 3 r) ∈ (G.bar.rw (Finset.range 3)).ideal := by
  have h1 : vecEquiv F K 3 r ∈ Submodule.span K (Set.range (ruleVec G hsrc)) := by
    rw [← hR]
    exact Submodule.mem_map_of_mem hr
  suffices ∀ w ∈ Submodule.span K (Set.range (ruleVec G hsrc)),
      Finsupp.mapDomain (flM c) w ∈ (G.bar.rw (Finset.range 3)).ideal from this _ h1
  intro w hw
  induction hw using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨r', rfl⟩ := h
    have hcast : ∀ {A B : Finset ℕ} (h : A = B), (flM (E := F) c ∘ SMono.cast h) =
        SMono.cast h ∘ flM c := fun _ => funext fun _ => Subtype.ext rfl
    have : Finsupp.mapDomain (flM c) (ruleVec G hsrc r') =
        ruleVec G.bar (fun r => hsrc r.1) (r', c) := by
      rw [ruleVec, ruleVec, ← Finsupp.mapDomain_comp, hcast, Finsupp.mapDomain_comp,
        Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
      rfl
    rw [this]
    exact ruleVec_mem G.bar _ (r', c)
  | zero => rw [Finsupp.mapDomain_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h₁ h₂ => rw [Finsupp.mapDomain_add]; exact Submodule.add_mem _ h₁ h₂
  | smul a _ _ h => rw [Finsupp.mapDomain_smul]; exact Submodule.smul_mem _ a h

omit [Fintype (F 2)] [DecidableEq (F 2)] in
lemma flM_ne_leaf (b : Bool) (σ : SMono F (Finset.range 3)) (a : ℕ) : (flM b σ).1 ≠ leaf a := by
  have hw := weight_eq_two rfl σ
  intro h
  have := congrArg STree.weight h
  rw [flM_val, weight_fl] at this
  rw [this] at hw
  simp at hw

omit [Fintype (F 2)] [DecidableEq (F 2)] in
lemma rootF_flM (b : Bool) (σ : SMono F (Finset.range 3)) : rootF (flM b σ).1 = b := by
  rw [flM_val]
  cases h : σ.1 with
  | leaf a =>
    have hw := weight_eq_two rfl σ
    rw [h] at hw
    simp at hw
  | node e c => rfl

/-- **A generator of the ideal of the flagged rules with an unflagged root lies in the relator
subcomplex**, and the others are killed by the projection onto the unflagged roots. -/
lemma barMap_gen_mem {A C : Finset ℕ} (hC : C = Finset.range 3)
    {f : SMono (BE F) C → SMono (BE F) A} (hf : IsSCtx f) (b : Bool) {w : SMono F C →₀ K}
    (hw : Finsupp.mapDomain (SMono.cast hC) w ∈ R.map (vecEquiv F K 3).toLinearMap) :
    barMap K A (proj K (fun X : SMono (BE F) A => rootF X.1 = false)
      (Finsupp.mapDomain f (Finsupp.mapDomain (flM b) w))) ∈ ShuffleBar.J K R := by
  subst hC
  rw [cast_rfl, Finsupp.mapDomain_id] at hw
  obtain ⟨r, hr, rfl⟩ := hw
  by_cases hne : Nonempty (SMono F (Finset.range 3))
  swap
  · have : vecEquiv F K 3 r = 0 := by
      ext g
      exact (hne ⟨g⟩).elim
    show barMap K A (proj K _ (Finsupp.mapDomain f
      (Finsupp.mapDomain (flM b) (vecEquiv F K 3 r)))) ∈ _
    rw [this, Finsupp.mapDomain_zero, Finsupp.mapDomain_zero, map_zero, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨σ₀⟩ := hne
  show barMap K A (proj K _ (Finsupp.mapDomain f
    (Finsupp.mapDomain (flM b) (vecEquiv F K 3 r)))) ∈ _
  have hroot : ∀ σ : SMono F (Finset.range 3),
      rootF (f (flM b σ)).1 = rootF (f (flM b σ₀)).1 := fun σ =>
    rootF_ctx hf (flM_ne_leaf b σ) (flM_ne_leaf b σ₀) (by rw [rootF_flM, rootF_flM])
  rw [← Finsupp.mapDomain_comp]
  cases hc : rootF (f (flM b σ₀)).1
  swap
  · rw [proj_of_supported_not K _ (mapDomain_mem_supported K _ fun σ _ => by
      show ¬ rootF (f (flM b σ)).1 = false
      rw [hroot, hc]
      decide), map_zero]
    exact Submodule.zero_mem _
  rw [proj_of_supported K _ (mapDomain_mem_supported K _ fun σ _ => by
    show rootF (f (flM b σ)).1 = false
    rw [hroot, hc])]
  obtain ⟨p, s, he, hwin, hall⟩ := exists_edge_of_ctx (F := BE F) hf (flM b σ₀)
  rw [flM_val, ofS_fl] at hwin
  have hfl := flags_of_windowRoot _ s he b _ hwin
  have hflag : ShuffleBar.flagAt (ofS (F := BE F) (f (flM b σ₀)).1) p = b := hfl.1
  have huncut : ShuffleBar.IsUncut (ofS (F := BE F) (f (flM b σ₀)).1) p s :=
    ⟨he, by rw [ShuffleBar.flagAt, LTree.subtreeAt_append]; exact hfl.2⟩
  have hvalid : ShuffleBar.Valid (ofS (F := BE F) (f (flM b σ₀)).1) := by
    refine ⟨isShuffle_ofS _, ?_, ?_⟩
    · rw [← Multiset.coe_nodup, labels_ofS]
      exact A.nodup
    · rw [← rootF_toS, toS_ofS]
      exact hc
  refine Submodule.subset_span ⟨_, p, s, r, hvalid, huncut, hr, ?_⟩
  rw [vecEquiv_eq_sum, Finsupp.mapDomain_finsetSum, map_sum, ShuffleBar.substRel]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finsupp.mapDomain_smul, map_smul, Finsupp.mapDomain_single, barMap_single,
    Function.comp_apply, hall, flM_val, monoEquiv_val, ofS_fl, ofS_toS, ShuffleBar.substBar,
    hflag]

include hR in
/-- **The ideal of the flagged rules maps into the relator subcomplex**, on the combinations of
bar monomials whose root is not cut. -/
theorem barMap_mem_J {A : Finset ℕ} {v : SMono (BE F) A →₀ K} (hv : v ∈ (G.bar.rw A).ideal)
    (hr : v ∈ Finsupp.supported K K {X | rootF X.1 = false}) :
    barMap K A v ∈ ShuffleBar.J K R := by
  rw [← proj_of_supported K (fun X : SMono (BE F) A => rootF X.1 = false) hr]
  rw [Rules.ideal_eq_span] at hv
  refine (Submodule.span_le (p := (ShuffleBar.J K R).comap
    ((barMap K A).comp (proj K fun X : SMono (BE F) A => rootF X.1 = false)))).2 ?_ hv
  rintro _ ⟨r, f, hf, rfl⟩
  have hgen : Finsupp.single (G.bar.lead r) 1 - G.bar.tail r =
      Finsupp.mapDomain (flM r.2) (Finsupp.single (G.lead r.1) 1 - G.tail r.1) := by
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
    rfl
  rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.comp_apply]
  erw [hgen]
  exact barMap_gen_mem (hsrc r.1) hf r.2
    (by rw [hR]; exact Submodule.subset_span ⟨r.1, rfl⟩)

include hR in
/-- **The relator subcomplex pulls back into the ideal of the flagged rules.** -/
theorem mem_ideal_of_barMap {A : Finset ℕ} {v : SMono (BE F) A →₀ K}
    (hv : barMap K A v ∈ ShuffleBar.J K R) : v ∈ (G.bar.rw A).ideal := by
  set P : ShuffleBar.BarTree (F 2) → Prop := fun y => (y.labels : Multiset ℕ) = A.val
  have hπ : proj K P (barMap K A v) = barMap K A v :=
    proj_of_supported K P (mapDomain_mem_supported K v fun X _ => labels_ofS X)
  have hmem : barMap K A v ∈ (G.bar.rw A).ideal.map (barMap K A) := by
    rw [← hπ]
    refine (Submodule.span_le (p := ((G.bar.rw A).ideal.map (barMap K A)).comap
      (proj K P))).2 ?_ hv
    rintro _ ⟨x, p, s, r, hx, hu, hr, rfl⟩
    have hlab : ∀ σ : LTree.Mono (F 2) 3,
        ((ShuffleBar.substBar x p s σ.1).labels : Multiset ℕ) = x.labels := fun σ =>
      Multiset.coe_eq_coe.2
        (ShuffleBar.perm_labels_substBar hx.shuffle hx.nodup hu (ShuffleBar.mono_shape σ).2.1)
    rw [SetLike.mem_coe, Submodule.mem_comap]
    by_cases hxl : (x.labels : Multiset ℕ) = A.val
    · have hs : ShuffleBar.substRel K x p s r ∈ Finsupp.supported K K {y | P y} :=
        Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _
          (Finsupp.single_mem_supported K _ (show P _ from (hlab σ).trans hxl))
      rw [proj_of_supported K P hs]
      obtain ⟨f, hf, hfv⟩ := exists_ctx_of_edge' (F := BE F) x hx.shuffle hxl hu.1
      refine ⟨_, G.bar.mapDomain_mem_ideal hf
        (mapDomain_flM_mem G hsrc hR hr (ShuffleBar.flagAt x p)), ?_⟩
      rw [vecEquiv_eq_sum, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_finsetSum, map_sum,
        ShuffleBar.substRel]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_smul, map_smul, Finsupp.mapDomain_single,
        Finsupp.mapDomain_single, barMap_single, hfv, ofS_toS, flM_val, monoEquiv_val, ofS_fl,
        ofS_toS]
      rfl
    · have hs : ShuffleBar.substRel K x p s r ∈ Finsupp.supported K K {y | ¬ P y} :=
        Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _
          (Finsupp.single_mem_supported K _
            (show ¬ P _ from fun h => hxl ((hlab σ).symm.trans h)))
      rw [proj_of_supported_not K P hs]
      exact Submodule.zero_mem _
  obtain ⟨u, hu, he⟩ := hmem
  rwa [← barMap_injective K A he]

omit [BinaryGens F] [Fintype (F 2)] [DecidableEq (F 2)] in
lemma d_mem_C {A : Finset ℕ} {w s : ℕ} {u : SMono (BE F) A →₀ K}
    (hu : u ∈ Bar.C K A w (s + 1)) : Bar.d K u ∈ Bar.C K A w s := by
  rw [Bar.C, Finsupp.supported_eq_span_single] at hu
  induction hu using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨X, hX, rfl⟩ := h
    exact Bar.d_mem_P hX
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul a _ _ h => rw [map_smul]; exact Submodule.smul_mem _ a h

include hR in
/-- **Koszulness with generators of any arity gives binary Koszulness**: if the rules present a
Koszul shuffle operad, so do the binary relators whose span they are. -/
theorem shuffleBar_isKoszul_of_isKoszul (hK : G.IsKoszul) : ShuffleBar.IsKoszul K R := by
  intro n s hsn x hx hdx
  obtain ⟨v, hv, rfl⟩ := C_le_map (F := F) K n s hx
  have hdv : Bar.d K v ∈ (G.bar.rw (Finset.range n)).ideal :=
    mem_ideal_of_barMap G hsrc hR (by rw [barMap_d]; exact hdx)
  obtain ⟨u, hu, hvu⟩ := hK (Finset.range n) (n - 1) s (by omega) v hv hdv
  refine ⟨barMap K _ u, map_C_le K n (n - 1) (s + 1) ⟨u, hu, rfl⟩, ?_⟩
  rw [← barMap_d, ← map_sub]
  refine barMap_mem_J G hsrc hR hvu (Submodule.sub_mem _ ?_ ?_)
  · exact Finsupp.supported_mono (fun X hX => hX.1) hv
  · exact Finsupp.supported_mono (fun X hX => hX.1) (d_mem_C hu)

end Ideals

end ShuffleBridge

namespace ShuffleBridge

open STree

/-! ## Relabelling the bar construction -/

section RelabelBar

variable {E : ℕ → Type v}

/-- **A key relabelled**: its least leaf moved along `φ`. -/
def rkey (φ : ℕ → ℕ) (k : ℕ ×ₗ ℕ) : ℕ ×ₗ ℕ := toLex (φ (ofLex k).1, (ofLex k).2)

lemma relabel_node {k : ℕ} (d : E k) (c : Fin k → STree E) (φ : ℕ → ℕ) :
    (node d c).relabel φ = node d fun i => (c i).relabel φ := rfl

lemma weight_relabel (φ : ℕ → ℕ) (t : STree E) : (t.relabel φ).weight = t.weight := by
  rw [relabel, weight_subst]
  simp

lemma key_relabel (φ : ℕ → ℕ) {t : STree E} (ht : t.IsShuffle) :
    key (t.relabel φ) = rkey φ (key t) := by
  rw [key, key, rkey, ofLex_toLex, first_relabel φ ht, weight_relabel]

lemma rootF_relabel (φ : ℕ → ℕ) (t : STree (BE E)) : rootF (t.relabel φ) = rootF t := by
  cases t <;> rfl

lemma cutKeys_relabel (φ : ℕ → ℕ) : ∀ t : STree (BE E), t.IsShuffle →
    cutKeys (t.relabel φ) = (cutKeys t).image (rkey φ)
  | leaf _, _ => rfl
  | node d c, h => by
    have ih : ∀ i, cutKeys ((c i).relabel φ) = (cutKeys (c i)).image (rkey φ) :=
      fun i => cutKeys_relabel φ (c i) (h.child i)
    have hk := key_relabel φ h
    rw [relabel_node] at hk ⊢
    simp only [STree.cutKeys, Finset.image_union, ih, hk]
    congr 1
    · split_ifs <;> simp
    · ext x
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, y, hy, e⟩ => ⟨y, ⟨i, hy⟩, e⟩, fun ⟨y, ⟨i, hy⟩, e⟩ => ⟨i, y, hy, e⟩⟩

lemma rkey_eq_iff {φ : ℕ → ℕ} {S : Set ℕ} (hφ : Set.InjOn φ S) {k k' : ℕ ×ₗ ℕ}
    (hk : (ofLex k).1 ∈ S) (hk' : (ofLex k').1 ∈ S) : rkey φ k = rkey φ k' ↔ k = k' := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h' := congrArg ofLex h
  simp only [rkey, ofLex_toLex, Prod.mk.injEq] at h'
  exact ofLex.injective (Prod.ext (hφ hk hk' h'.1) h'.2)

lemma rkey_lt_iff {φ : ℕ → ℕ} {S : Set ℕ} (hφ : StrictMonoOn φ S) {k k' : ℕ ×ₗ ℕ}
    (hk : (ofLex k).1 ∈ S) (hk' : (ofLex k').1 ∈ S) : rkey φ k < rkey φ k' ↔ k < k' := by
  rw [rkey, rkey, Prod.Lex.toLex_lt_toLex, ← toLex_ofLex k, ← toLex_ofLex k',
    Prod.Lex.toLex_lt_toLex, ofLex_toLex, ofLex_toLex, hφ.lt_iff_lt hk hk',
    hφ.injOn.eq_iff hk hk']

lemma setF_relabel {φ : ℕ → ℕ} {S : Set ℕ} (hφ : Set.InjOn φ S) {k : ℕ ×ₗ ℕ}
    (hk : (ofLex k).1 ∈ S) (b : Bool) : ∀ t : STree (BE E), t.IsShuffle →
    (∀ a ∈ t.labels, a ∈ S) →
    setF (rkey φ k) b (t.relabel φ) = (setF k b t).relabel φ
  | leaf _, _, _ => rfl
  | node d c, h, hS => by
    have hkey := key_relabel φ h
    have hfirst : (ofLex (key (node d c))).1 ∈ S := hS _ (first_mem h)
    rw [relabel_node] at hkey ⊢
    rw [setF_node, setF_node, relabel_node, hkey]
    simp only [rkey_eq_iff hφ hfirst hk]
    congr 1
    funext i
    exact setF_relabel hφ hk b (c i) (h.child i)
      fun a ha => hS a (Multiset.mem_of_le (labels_le_node d c i) ha)

variable {A B : Finset ℕ} (φ : ℕ → ℕ) (hφ : StrictMonoOn φ A) (himg : A.image φ = B)

lemma cuts_relabelM (X : SMono (BE E) A) :
    cuts (relabelM φ hφ himg X) = (cuts X).image (rkey φ) :=
  cutKeys_relabel φ X.1 X.isShuffle

lemma mem_A_of_cut {X : SMono (BE E) A} {k : ℕ ×ₗ ℕ} (hk : k ∈ cuts X) : (ofLex k).1 ∈ A :=
  X.mem_labels.1 (mem_vkeys X.isShuffle (mem_vkeys_of_mem_cutKeys hk)).1

lemma setM_relabelM (X : SMono (BE E) A) {k : ℕ ×ₗ ℕ} (hk : (ofLex k).1 ∈ A) (b : Bool) :
    setM (rkey φ k) b (relabelM φ hφ himg X) = relabelM φ hφ himg (setM k b X) :=
  Subtype.ext (setF_relabel hφ.injOn (S := A) hk b X.1 X.isShuffle fun _ ha => X.mem_labels.1 ha)

lemma mem_P_relabelM {w s : ℕ} {X : SMono (BE E) A} (hX : X ∈ Bar.P A w s) :
    relabelM φ hφ himg X ∈ Bar.P B w s := by
  refine ⟨?_, ?_, ?_⟩
  · show rootF (X.1.relabel φ) = false
    rw [rootF_relabel]
    exact hX.1
  · show (X.1.relabel φ).weight = w
    rw [weight_relabel]
    exact hX.2.1
  · rw [cuts_relabelM, Finset.card_image_of_injOn fun k hk k' hk' h =>
      (rkey_eq_iff hφ.injOn (mem_A_of_cut hk) (mem_A_of_cut hk')).1 h]
    exact hX.2.2

variable (K : Type*) [CommRing K]

/-- **Relabelling commutes with the differential** of the bar construction. -/
theorem d_relabelM (v : SMono (BE E) A →₀ K) :
    Bar.d K (Finsupp.mapDomain (relabelM φ hφ himg) v) =
      Finsupp.mapDomain (relabelM φ hφ himg) (Bar.d K v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [Finsupp.mapDomain_add, map_add, hv, hw, map_add, Finsupp.mapDomain_add]
  | single X c =>
    have hinj : Set.InjOn (rkey φ) (cuts X : Set (ℕ ×ₗ ℕ)) := fun k hk k' hk' h =>
      (rkey_eq_iff hφ.injOn (mem_A_of_cut hk) (mem_A_of_cut hk')).1 h
    rw [Finsupp.mapDomain_single, Bar.d, CutComplex.d_single, Bar.d, CutComplex.d_single,
      Finsupp.mapDomain_smul, CutComplex.dX, CutComplex.dX, cuts_relabelM,
      Finset.sum_image hinj, Finsupp.mapDomain_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single,
      setM_relabelM φ hφ himg X (mem_A_of_cut hk), CutComplex.sgn, CutComplex.sgn,
      Finset.filter_image, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
    congr 3
    exact Finset.filter_congr fun k' hk' =>
      rkey_lt_iff hφ (mem_A_of_cut hk') (mem_A_of_cut hk)

end RelabelBar

/-! ## Binary Koszulness gives Koszulness with generators of any arity -/

section Converse

variable {F : ℕ → Type v} [BinaryGens F] [Fintype (F 2)] [DecidableEq (F 2)]
  {K : Type*} [Field K] {ρ : Type*} {O : AdmOrder F} (G : Rules K ρ O.toCtxOrder)
  (hsrc : ∀ r, G.src r = Finset.range 3) {R : Submodule K (LTree.Mono (F 2) 3 → K)}
  (hR : R.map (vecEquiv F K 3).toLinearMap = Submodule.span K (Set.range (ruleVec G hsrc)))

omit [Fintype (F 2)] [DecidableEq (F 2)] in
lemma weight_add_one {n : ℕ} (X : SMono (BE F) (Finset.range n)) : X.1.weight + 1 = n := by
  have h1 := weight_toS (F := BE F) (ofS X.1)
  rw [toS_ofS] at h1
  have h2 : (ofS (F := BE F) X.1).arity = n := by
    rw [← LTree.length_labels, ← Multiset.coe_card, labels_ofS, Finset.range_val,
      Multiset.card_range]
  omega

include hR in
/-- **Binary Koszulness gives exactness on the leaves `0, …, n - 1`.** -/
theorem exact_range (hK : ShuffleBar.IsKoszul K R) {n w s : ℕ} (hsw : s < w)
    {v : SMono (BE F) (Finset.range n) →₀ K} (hv : v ∈ Bar.C K (Finset.range n) w s)
    (hdv : Bar.d K v ∈ (G.bar.rw (Finset.range n)).ideal) :
    ∃ u ∈ Bar.C K (Finset.range n) w (s + 1),
      v - Bar.d K u ∈ (G.bar.rw (Finset.range n)).ideal := by
  by_cases hmain : w + 1 = n ∧ s ≠ 0
  · obtain ⟨hwn, hs⟩ := hmain
    obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
    have hx : barMap K _ v ∈ ShuffleBar.C K n (s' + 1) := map_C_le K n w (s' + 1) ⟨v, hv, rfl⟩
    have hdx : ShuffleBar.d K (barMap K _ v) ∈ ShuffleBar.J K R := by
      rw [← barMap_d]
      exact barMap_mem_J G hsrc hR hdv
        (Finsupp.supported_mono (fun X hX => hX.1) (d_mem_C hv))
    obtain ⟨y, hy, hxy⟩ := hK n (s' + 1) (by omega) _ hx hdx
    obtain ⟨u, hu, rfl⟩ := C_le_map (F := F) K n (s' + 1 + 1) hy
    refine ⟨u, by rwa [show w = n - 1 by omega], mem_ideal_of_barMap G hsrc hR ?_⟩
    rw [map_sub, barMap_d]
    exact hxy
  · have hv0 : v = 0 := by
      ext X
      by_contra hX
      obtain ⟨-, hXw, hXs⟩ := (Finsupp.mem_supported K v).1 hv (Finsupp.mem_support_iff.2 hX)
      have := weight_add_one X
      exact hmain ⟨by omega, by omega⟩
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [hv0, map_zero, sub_zero]
    exact Submodule.zero_mem _

include hR in
/-- **Binary Koszulness gives Koszulness with generators of any arity**: relabel an arbitrary
set of leaves onto `0, …, n - 1` along the positions, a context with an inverse context which
commutes with the differential. -/
theorem isKoszul_of_shuffleBar (hK : ShuffleBar.IsKoszul K R) : G.IsKoszul := by
  intro A w s hsw v hv hdv
  have hβα : ∀ X : SMono (BE F) A, relabelM (eltIn A) (strictMonoOn_eltIn A) (image_eltIn A)
      (relabelM (posIn A) (strictMonoOn_posIn A) (image_posIn A) X) = X := fun X =>
    Subtype.ext (by
      show (X.1.relabel (posIn A)).relabel (eltIn A) = X.1
      rw [relabel_relabel]
      exact relabel_id fun a ha => eltIn_posIn (X.mem_labels.1 ha))
  set α := relabelM (E := BE F) (posIn A) (strictMonoOn_posIn A) (image_posIn A)
  set β := relabelM (E := BE F) (eltIn A) (strictMonoOn_eltIn A) (image_eltIn A)
  have hv' : Finsupp.mapDomain α v ∈ Bar.C K (Finset.range A.card) w s :=
    mapDomain_mem_supported K v fun X hX =>
      mem_P_relabelM _ _ _ ((Finsupp.mem_supported K v).1 hv hX)
  have hdv' : Bar.d K (Finsupp.mapDomain α v) ∈ (G.bar.rw (Finset.range A.card)).ideal := by
    rw [d_relabelM]
    exact G.bar.mapDomain_mem_ideal (isSCtx_relabelM _ _ _) hdv
  obtain ⟨u, hu, hvu⟩ := exact_range G hsrc hR hK hsw hv' hdv'
  refine ⟨Finsupp.mapDomain β u, mapDomain_mem_supported K u fun X hX =>
    mem_P_relabelM _ _ _ ((Finsupp.mem_supported K u).1 hu hX), ?_⟩
  have hvβ : v = Finsupp.mapDomain β (Finsupp.mapDomain α v) := by
    rw [← Finsupp.mapDomain_comp, show β ∘ α = id from funext hβα, Finsupp.mapDomain_id]
  rw [hvβ, d_relabelM, ← Finsupp.mapDomain_sub]
  exact G.bar.mapDomain_mem_ideal (isSCtx_relabelM _ _ _) hvu

include hR in
/-- **The two shuffle Koszulness predicates agree** for binary relators and rules on the leaves
`0, 1, 2` whose vectors span them. -/
theorem isKoszul_iff : ShuffleBar.IsKoszul K R ↔ G.IsKoszul :=
  ⟨isKoszul_of_shuffleBar G hsrc hR, shuffleBar_isKoszul_of_isKoszul G hsrc hR⟩

end Converse

end ShuffleBridge

namespace ComBin

variable (K : Type*) [Field K]

/-- **The two Koszulness predicates of the commutative operad agree.** -/
theorem isKoszul_iff : ShuffleBar.IsKoszul K (rel K) ↔ (ComGen.rules K).IsKoszul :=
  ShuffleBridge.isKoszul_iff _ (src_rules K) (map_rel K)

end ComBin

namespace AssBin

variable (K : Type*) [Field K]

/-- **The two Koszulness predicates of the associative operad agree.** -/
theorem isKoszul_iff : ShuffleBar.IsKoszul K (rel K) ↔ (AssShGen.rules K).IsKoszul :=
  ShuffleBridge.isKoszul_iff _ (src_rules K) (map_rel K)

end AssBin

end Operad

