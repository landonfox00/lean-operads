/-
# The Koszul dual cooperad of a PBW shuffle operad, with generators of any arity

**The Koszul dual cooperad** (`Operad.Rules.KD`) of the shuffle operad presented by quadratic
rules `G`, on the leaves `A` and in weight `w`: the top homology of its bar construction — the
combinations of bar trees with every edge cut whose differential lies in the ideal of the flagged
rules. (There are no boundaries in the top degree, and the bar trees with every edge cut are
normal, so they are a basis of the bar construction in that degree.)

**The theorem** (`Operad.Rules.kdBasis`): when the rules are quadratic and resolvable — a
quadratic Gröbner basis, a PBW presentation — the Koszul dual cooperad has a basis indexed by the
**full monomials** (`Operad.Rules.IsFull`), those every edge of which is leading: each full
monomial `t`, with every edge cut, is the leading term of a cycle `κ t` (`Operad.Rules.kappa`),
equal to it up to trees over strictly smaller monomials, and these cycles are a basis. So the
dimension of the Koszul dual cooperad is the number of full monomials (`Operad.Rules.rank_KD`,
`Operad.Rules.finrank_KD`), with no finiteness assumption: the count of the PBW basis of the
Koszul dual operad, whose leading monomials are the complementary ones.

The proof:

* the bar trees with as many components as vertices are the monomials with every edge cut
  (`Operad.STree.Bar.eq_cutAllM_of_mem_P`), and these are normal
  (`Operad.Rules.mem_irr_of_mem_P`), the leading edges being edges
  (`Operad.Rules.leadKeys_subset_edgeKeys`);
* the leading part of the differential of a full monomial with every edge cut vanishes
  (`Operad.Rules.dL_cutAllM`), so its differential lies over strictly smaller monomials; by the
  exactness of the bar construction below the diagonal over the down-closed set of these
  monomials (`Operad.Rules.bar_exact_down`), it is the differential of a combination of trees
  over smaller monomials, and `κ t` is the difference (`Operad.Rules.exists_kappa`);
* the family is triangular, hence linearly independent
  (`Operad.Hoffbeck.linearIndependent_of_triangular`); and the leading monomial of a cycle is
  full (`Operad.Rules.isFull_of_mem_KD`) — its part over the leading monomial is a cycle of the
  leading part of the differential (`Operad.Hoffbeck.leading_cycle`), which cutting along an edge
  which is not leading would contract — so the family spans
  (`Operad.Hoffbeck.span_of_triangular`).
-/
import Operad.ShuffleAnyKoszul
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

universe u v

namespace Operad

namespace STree

variable {E : ℕ → Type v}

/-! ## Trees with every edge cut -/

/-- **Every vertex flagged**: every vertex flagged `true`. -/
def allT (t : STree E) : STree (BE E) := t.mapG fun _ e => (e, true)

/-- **Every edge cut**: the root flagged `false`, the other vertices `true`. -/
def cutAll : STree E → STree (BE E)
  | leaf a => leaf a
  | node e c => node (e, false) fun i => allT (c i)

@[simp] lemma allT_leaf (a : ℕ) : allT (leaf a : STree E) = leaf a := rfl

@[simp] lemma allT_node {k : ℕ} (e : E k) (c : Fin k → STree E) :
    allT (node e c) = node (e, true) fun i => allT (c i) := rfl

@[simp] lemma cutAll_leaf (a : ℕ) : cutAll (leaf a : STree E) = leaf a := rfl

@[simp] lemma cutAll_node {k : ℕ} (e : E k) (c : Fin k → STree E) :
    cutAll (node e c) = node (e, false) fun i => allT (c i) := rfl

@[simp] lemma forget_allT (t : STree E) : forget (allT t) = t := by
  rw [forget, allT, mapG_mapG]
  exact mapG_id t

@[simp] lemma forget_cutAll : ∀ t : STree E, forget (cutAll t) = t
  | leaf _ => rfl
  | node e c => by simp

@[simp] lemma rootF_cutAll : ∀ t : STree E, rootF (cutAll t) = false
  | leaf _ => rfl
  | node _ _ => rfl

lemma mem_cutKeys_allT : ∀ (t : STree E) (y : ℕ ×ₗ ℕ), y ∈ cutKeys (allT t) ↔ y ∈ t.vkeys
  | leaf _, y => by simp [cutKeys]
  | node e c, y => by
    rw [allT_node, mem_cutKeys_node, mem_vkeys_node]
    simp only [mem_cutKeys_allT, true_and]
    rw [show key (node (e, true) fun i => allT (c i)) = key (node e c) from key_mapG _ (node e c)]

/-- **The cut edges of a tree with every edge cut** are its edges. -/
theorem cutKeys_cutAll : ∀ t : STree E, cutKeys (cutAll t) = t.edgeKeys
  | leaf _ => rfl
  | node e c => by
    ext y
    rw [cutAll_node, mem_cutKeys_node, mem_edgeKeys_node]
    simp only [Bool.false_eq_true, false_and, false_or, mem_cutKeys_allT]

/-- **A bar tree with distinct keys all of whose vertices are cut** is its underlying tree with
every vertex flagged. -/
theorem eq_allT : ∀ {Y : STree (BE E)}, Y.vkeys.Nodup → (∀ y ∈ Y.vkeys, y ∈ cutKeys Y) →
    Y = allT (forget Y)
  | leaf _, _, _ => rfl
  | node d c, hn, h => by
    obtain ⟨hroot, hnc, hdisj⟩ := nodup_vkeys_children hn
    obtain ⟨e, b⟩ := d
    have hb : b = true := by
      rcases mem_cutKeys_node.1 (h _ (mem_vkeys_node.2 (Or.inl rfl))) with ⟨hb, -⟩ | ⟨i, hi⟩
      · exact hb
      · exact absurd ((Multiset.mem_sum (s := Finset.univ)).2
          ⟨i, Finset.mem_univ _, mem_vkeys_of_mem_cutKeys hi⟩) hroot
    subst hb
    rw [forget_node, allT_node]
    congr 1
    funext i
    refine eq_allT (hnc i) fun y hy => ?_
    rcases mem_cutKeys_node.1 (h y (mem_vkeys_node.2 (Or.inr ⟨i, hy⟩))) with ⟨-, rfl⟩ | ⟨j, hj⟩
    · exact absurd ((Multiset.mem_sum (s := Finset.univ)).2 ⟨i, Finset.mem_univ _, hy⟩) hroot
    · by_cases hij : j = i
      · subst hij
        exact hj
      · exact absurd hy (Multiset.disjoint_left.1 (hdisj j i hij) (mem_vkeys_of_mem_cutKeys hj))

/-- **A bar tree with distinct keys, not flagged at the root, all of whose edges are cut** is its
underlying tree with every edge cut. -/
theorem eq_cutAll : ∀ {X : STree (BE E)}, X.vkeys.Nodup → rootF X = false →
    X.edgeKeys ⊆ cutKeys X → X = cutAll (forget X)
  | leaf _, _, _, _ => rfl
  | node d c, hn, hr, h => by
    obtain ⟨-, hnc, hdisj⟩ := nodup_vkeys_children hn
    obtain ⟨e, b⟩ := d
    have hb : b = false := hr
    subst hb
    rw [forget_node, cutAll_node]
    congr 1
    funext i
    refine eq_allT (hnc i) fun y hy => ?_
    rcases mem_cutKeys_node.1 (h (mem_edgeKeys_node.2 ⟨i, hy⟩)) with ⟨hf, -⟩ | ⟨j, hj⟩
    · exact absurd hf Bool.false_ne_true
    · by_cases hij : j = i
      · subst hij
        exact hj
      · exact absurd hy (Multiset.disjoint_left.1 (hdisj j i hij) (mem_vkeys_of_mem_cutKeys hj))

/-! ## The leading edges are edges -/

lemma mem_vkeys_of_mem_wk (xs : ℕ → STree E) :
    ∀ (g : STree E) {y : ℕ ×ₗ ℕ}, y ∈ wk xs g → y ∈ (g.subst xs).vkeys
  | leaf _, _, h => absurd h (Finset.notMem_empty _)
  | node e c, y, h => by
    rw [wk_node, Finset.mem_insert, Finset.mem_biUnion] at h
    rw [subst_node, mem_vkeys_node]
    rcases h with rfl | ⟨i, -, hi⟩
    · left
      rw [subst_node]
    · exact Or.inr ⟨i, mem_vkeys_of_mem_wk xs (c i) hi⟩

/-- **The edges of a subtree are edges.** -/
theorem edgeKeys_subset_of_get? : ∀ {t s : STree E} {p : List ℕ}, t.get? p = some s →
    s.edgeKeys ⊆ t.edgeKeys
  | t, s, [], h => by
    rw [get?_nil, Option.some_inj] at h
    rw [h]
  | leaf _, _, _ :: _, h => by simp at h
  | node e c, s, i :: p, h => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    intro y hy
    rw [mem_edgeKeys_node]
    exact ⟨⟨i, hi⟩, edgeKeys_subset_vkeys (edgeKeys_subset_of_get? h hy)⟩

/-! ## Monomials with every edge cut -/

section BarMono

variable {A : Finset ℕ}

/-- **A monomial with every edge cut.** -/
def cutAllM (t : SMono E A) : SMono (BE E) A :=
  ⟨cutAll t.1, (isShuffle_forget _).1 (by rw [forget_cutAll]; exact t.isShuffle),
    by rw [← labels_forget, forget_cutAll]; exact t.labels_eq⟩

@[simp] lemma cutAllM_val (t : SMono E A) : (cutAllM t).1 = cutAll t.1 := rfl

@[simp] lemma forgetM_cutAllM (t : SMono E A) : forgetM (cutAllM t) = t :=
  Subtype.ext (forget_cutAll t.1)

lemma cutAllM_injective : Function.Injective (cutAllM : SMono E A → SMono (BE E) A) :=
  fun s t h => by rw [← forgetM_cutAllM s, h, forgetM_cutAllM]

lemma cuts_cutAllM (t : SMono E A) : cuts (cutAllM t) = t.1.edgeKeys := cutKeys_cutAll t.1

end BarMono

namespace Bar

variable {A : Finset ℕ} {w : ℕ}

/-- **In the top degree every edge is cut.** -/
theorem cuts_eq_of_mem_P {X : SMono (BE E) A} (hX : X ∈ P A w w) : cuts X = X.1.edgeKeys := by
  have hn := nodup_vkeys X.isShuffle X.nodup
  refine Finset.eq_of_subset_of_card_le (cutKeys_subset_edgeKeys hX.1) ?_
  rw [card_edgeKeys hn, hX.2.1]
  have := hX.2.2
  omega

/-- **The bar trees of the top degree are the monomials with every edge cut.** -/
theorem eq_cutAllM_of_mem_P {X : SMono (BE E) A} (hX : X ∈ P A w w) :
    X = cutAllM (forgetM X) :=
  Subtype.ext (eq_cutAll (nodup_vkeys X.isShuffle X.nodup) hX.1 fun y hy => by
    rw [show cutKeys X.1 = cuts X from rfl, cuts_eq_of_mem_P hX]
    exact hy)

theorem cutAllM_mem_P (hw : 0 < w) {t : SMono E A} (ht : t.1.weight = w) :
    cutAllM t ∈ P A w w := by
  refine ⟨rootF_cutAll t.1, ?_, ?_⟩
  · rw [cutAllM_val, ← weight_forget, forget_cutAll]
    exact ht
  · rw [cuts_cutAllM, card_edgeKeys (nodup_vkeys t.isShuffle t.nodup), ht]
    omega

end Bar

end STree

open STree

variable {E : ℕ → Type v} {K : Type u} [CommRing K] {ρ : Type*} {O : STree.AdmOrder E}
  (G : Rules K ρ O.toCtxOrder)

/-! ## The Koszul dual cooperad -/

/-- **The leading edges are edges.** -/
theorem Rules.leadKeys_subset_edgeKeys {A : Finset ℕ} (t : SMono E A) :
    G.leadKeys t ⊆ ↑t.1.edgeKeys := by
  rintro y ⟨r, p, xs₀, hp, -, hy⟩
  refine edgeKeys_subset_of_get? hp ?_
  rcases hL : (G.lead r).1 with a | ⟨e, c⟩
  · rw [hL] at hy
    exact absurd hy (Finset.notMem_empty _)
  · rw [hL] at hy
    rw [subst_node, mem_edgeKeys_node]
    rw [nwk_node, Finset.mem_biUnion] at hy
    obtain ⟨i, -, hi⟩ := hy
    exact ⟨i, mem_vkeys_of_mem_wk xs₀ (c i) hi⟩

/-- **The full monomials**: those every edge of which is leading — for a quadratic Gröbner basis,
the normal monomials of the Koszul dual operad. -/
def Rules.IsFull {A : Finset ℕ} (t : SMono E A) : Prop := ↑t.1.edgeKeys ⊆ G.leadKeys t

/-- **The full monomials of weight `w`** on the leaves `A`. -/
abbrev Rules.Full (A : Finset ℕ) (w : ℕ) : Type v :=
  {t : SMono E A // t.1.weight = w ∧ G.IsFull t}

/-- **The Koszul dual cooperad** of the shuffle operad presented by the rules, on the leaves `A`
and in weight `w`: the top homology of its bar construction, the combinations of bar trees with
every edge cut whose differential lies in the ideal of the flagged rules. -/
noncomputable def Rules.KD (A : Finset ℕ) (w : ℕ) : Submodule K (SMono (BE E) A →₀ K) :=
  Bar.C K A w w ⊓ (G.bar.rw A).ideal.comap (Bar.d K)

/-- **The leading part of the differential of a full monomial with every edge cut vanishes.** -/
lemma Rules.dL_cutAllM {A : Finset ℕ} {t : SMono E A} (ht : G.IsFull t) :
    G.dL A (Finsupp.single (cutAllM t) 1) = 0 := by
  classical
  rw [Rules.dL, CutComplex.dL_single, one_smul, CutComplex.dLX]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_filter, forgetM_cutAllM, cuts_cutAllM] at hk
  exact absurd (ht hk.1) hk.2

section Top

variable {G} (hquad : ∀ r, (G.lead r).1.weight = 2)
include hquad

/-- **The bar trees with every edge cut are normal.** -/
theorem Rules.mem_irr_of_mem_P {A : Finset ℕ} {w : ℕ} {X : SMono (BE E) A}
    (hX : X ∈ Bar.P A w w) : X ∈ (G.bar.rw A).Irr := by
  rw [G.bar.mem_irr_iff, G.bar_normal_iff_quad hquad, Bar.cuts_eq_of_mem_P hX]
  have h := G.leadKeys_subset_edgeKeys (forgetM X)
  rwa [forgetM_val, edgeKeys_forget] at h

variable (hom : ∀ r, ∀ m ∈ (G.tail r).support, m.1.weight = 2)
  (hres : ∀ C, (G.rw C).Resolvable)
include hom hres

/-- **The leading monomial of a cycle of the top degree is full.** -/
theorem Rules.isFull_of_mem_KD {A : Finset ℕ} {w : ℕ} {v : SMono (BE E) A →₀ K}
    (hv : v ∈ G.KD A w) {X : SMono (BE E) A} (hX : X ∈ v.support)
    (hmax : ∀ Y ∈ v.support, ¬ O.lt (forgetM X) (forgetM Y)) : G.IsFull (forgetM X) := by
  classical
  obtain ⟨hvC, hvd⟩ := Submodule.mem_inf.1 hv
  have hvP : ∀ Y ∈ v.support, Y ∈ Bar.P A w w := fun Y hY => (Finsupp.mem_supported K v).1 hvC hY
  have hXP := hvP X hX
  have hS : (G.bar.rw A).Resolvable :=
    G.bar_resolvable (G.hlead_of_quad hquad) (G.hom_of_quad hquad hom) hres A
  have hDv : (G.bar.rw A).nf (Bar.d K v) = 0 := hS.ideal_le_ker (Submodule.mem_comap.1 hvd)
  -- the part of `v` over its leading monomial is a cycle of the leading part
  have hvt : Finsupp.single X (v X) ∈ Finsupp.supported K K
      ((G.bar.rw A).Irr ∩ Bar.P A w w ∩ forgetM ⁻¹' {forgetM X}) :=
    Finsupp.single_mem_supported K _ ⟨⟨G.mem_irr_of_mem_P hquad hXP, hXP⟩, rfl⟩
  have hvr : v - Finsupp.single X (v X) ∈ Finsupp.supported K K ((G.bar.rw A).Irr ∩
      Bar.P A w w ∩ {Y | forgetM Y ≠ forgetM X ∧ ¬ O.lt (forgetM X) (forgetM Y)}) := by
    rw [Finsupp.mem_supported]
    intro Y hY
    rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.sub_apply] at hY
    have hYX : Y ≠ X := by
      rintro rfl
      rw [Finsupp.single_eq_same, sub_self] at hY
      exact hY rfl
    have hYv : Y ∈ v.support := by
      rw [Finsupp.mem_support_iff]
      rwa [Finsupp.single_eq_of_ne hYX, sub_zero] at hY
    have hYP := hvP Y hYv
    refine ⟨⟨G.mem_irr_of_mem_P hquad hYP, hYP⟩, fun h => hYX ?_, hmax Y hYv⟩
    rw [Bar.eq_cutAllM_of_mem_P hYP, Bar.eq_cutAllM_of_mem_P hXP, h]
  have h0 : G.dL A (Finsupp.single X (v X)) = 0 :=
    Hoffbeck.leading_cycle (fun x y => O.lt x y) forgetM (fun a => (O.wf A).irrefl.irrefl a)
      ((G.bar.rw A).nf ∘ₗ Bar.d K) (G.dL A) (fun Y hY => G.d_sub_dL_mem hquad hY.1)
      (fun Y _ => G.dL_mem_fib Y) hvt hvr (by rw [add_sub_cancel]; exact hDv)
  -- so every edge is leading: cutting along an edge which is not leading would contract it
  intro k₀ hk₀
  by_contra hk₀L
  have hc := G.dL_cut_add hk₀ hk₀L (Y := X) rfl
  have hcut : Bar.cut K k₀ (Finsupp.single X (1 : K)) = 0 := by
    rw [Bar.cut, CutComplex.hL_single, one_smul, CutComplex.hX, if_pos]
    rw [Bar.cuts_eq_of_mem_P hXP, ← edgeKeys_forget, ← forgetM_val]
    exact hk₀
  rw [hcut, map_zero, zero_add] at hc
  have e1 : Finsupp.single X (v X) = v X • Finsupp.single X (1 : K) := by
    rw [Finsupp.smul_single_one]
  have h2 : Finsupp.single X (v X) = 0 := by
    rw [e1, ← hc, ← map_smul, ← map_smul, ← e1, h0, map_zero]
  exact (Finsupp.mem_support_iff.1 hX) (Finsupp.single_eq_zero.1 h2)

/-- **The cycle of a full monomial**: a full monomial `t` of positive weight, with every edge cut,
is the leading term of a cycle of the top degree, up to trees over strictly smaller monomials. -/
theorem Rules.exists_kappa {A : Finset ℕ} {w : ℕ} (hw : 0 < w) {t : SMono E A}
    (ht : t.1.weight = w) (hfull : G.IsFull t) :
    ∃ κ ∈ G.KD A w, κ - Finsupp.single (cutAllM t) 1 ∈
      Finsupp.supported K K {Y | O.lt (forgetM Y) t} := by
  classical
  have hS : (G.bar.rw A).Resolvable :=
    G.bar_resolvable (G.hlead_of_quad hquad) (G.hom_of_quad hquad hom) hres A
  have hXP : cutAllM t ∈ Bar.P A w w := Bar.cutAllM_mem_P hw ht
  -- the differential of `t` with every edge cut lies over strictly smaller monomials
  have hDX : (G.bar.rw A).nf (Bar.d K (Finsupp.single (cutAllM t) 1)) ∈ Finsupp.supported K K
      ((G.bar.rw A).Irr ∩ Bar.P A w (w - 1) ∩ forgetM ⁻¹' {m | O.lt m t}) := by
    rw [Finsupp.supported_inter]
    refine ⟨G.nf_mem_P hquad hom (Bar.d_mem_P (n := w - 1) (by rwa [Nat.sub_add_cancel hw])), ?_⟩
    have h := G.d_sub_dL_mem hquad (G.mem_irr_of_mem_P hquad hXP)
    rwa [G.dL_cutAllM hfull, sub_zero, forgetM_cutAllM] at h
  have hDDX : (G.bar.rw A).nf (Bar.d K ((G.bar.rw A).nf
      (Bar.d K (Finsupp.single (cutAllM t) 1)))) = 0 := by
    rw [G.nf_d_nf hquad hom hres, Bar.d_d, map_zero]
  -- it is the boundary of a combination of trees over smaller monomials
  obtain ⟨u, hu, hDu⟩ := G.bar_exact_down hquad hom hres (s := w - 1) (by omega)
    (Z := {m | O.lt m t}) (fun m hm m' h => O.trans h hm) hDX hDDX
  rw [Nat.sub_add_cancel hw] at hu
  refine ⟨Finsupp.single (cutAllM t) 1 - u, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · exact Submodule.sub_mem _ (Finsupp.single_mem_supported K _ hXP)
      (Finsupp.supported_mono (fun Y hY => hY.1.2) hu)
  · rw [Submodule.mem_comap, ← hS.nf_eq_zero_iff, map_sub, map_sub, hDu, sub_self]
  · rw [sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Finsupp.supported_mono (fun Y hY => hY.2) hu)

/-- **The cycle of a full monomial** (`Operad.Rules.exists_kappa`). -/
noncomputable def Rules.kappa {A : Finset ℕ} {w : ℕ} (hw : 0 < w) (t : G.Full A w) :
    SMono (BE E) A →₀ K :=
  Classical.choose (G.exists_kappa hquad hom hres hw t.2.1 t.2.2)

variable {A : Finset ℕ} {w : ℕ} (hw : 0 < w)

lemma Rules.kappa_mem (t : G.Full A w) : G.kappa hquad hom hres hw t ∈ G.KD A w :=
  (Classical.choose_spec (G.exists_kappa hquad hom hres hw t.2.1 t.2.2)).1

lemma Rules.kappa_sub (t : G.Full A w) :
    G.kappa hquad hom hres hw t - Finsupp.single (cutAllM t.1) 1 ∈
      Finsupp.supported K K {Y | O.lt (forgetM Y) (forgetM (cutAllM t.1))} := by
  rw [forgetM_cutAllM]
  exact (Classical.choose_spec (G.exists_kappa hquad hom hres hw t.2.1 t.2.2)).2

/-- **The cycles of the full monomials are linearly independent**, being triangular. -/
theorem Rules.linearIndependent_kappa : LinearIndependent K (G.kappa hquad hom hres hw (A := A)) :=
  Hoffbeck.linearIndependent_of_triangular (fun x y => O.lt x y) forgetM
    (fun a => (O.wf A).irrefl.irrefl a) O.trans (e := fun t : G.Full A w => cutAllM t.1)
    (fun _ _ h => Subtype.ext (cutAllM_injective h)) (G.kappa_sub hquad hom hres hw)

/-- **The cycles of the full monomials span the Koszul dual cooperad.** -/
theorem Rules.KD_eq_span :
    G.KD A w = Submodule.span K (Set.range (G.kappa hquad hom hres hw (A := A))) := by
  refine le_antisymm (Hoffbeck.span_of_triangular (fun x y => O.lt x y) forgetM (O.wf A) O.trans
    (e := fun t : G.Full A w => cutAllM t.1) (G.kappa_mem hquad hom hres hw)
    (G.kappa_sub hquad hom hres hw) fun v hv X hX hmax => ?_)
    (Submodule.span_le.2 (Set.range_subset_iff.2 (G.kappa_mem hquad hom hres hw)))
  have hXP : X ∈ Bar.P A w w := (Finsupp.mem_supported K v).1 (Submodule.mem_inf.1 hv).1 hX
  refine ⟨⟨forgetM X, ?_, G.isFull_of_mem_KD hquad hom hres hv hX hmax⟩,
    (Bar.eq_cutAllM_of_mem_P hXP).symm⟩
  rw [forgetM_val, weight_forget]
  exact hXP.2.1

/-- **The Koszul dual cooperad of a PBW shuffle operad has a basis indexed by the full
monomials**: the cycles `κ t` of the full monomials `t`, each equal to `t` with every edge cut up
to trees over strictly smaller monomials. -/
noncomputable def Rules.kdBasis : Module.Basis (G.Full A w) K (G.KD A w) :=
  (Module.Basis.span (G.linearIndependent_kappa hquad hom hres hw)).map
    (LinearEquiv.ofEq _ _ (G.KD_eq_span hquad hom hres hw).symm)

theorem Rules.kdBasis_apply (t : G.Full A w) :
    (G.kdBasis hquad hom hres hw t : SMono (BE E) A →₀ K) = G.kappa hquad hom hres hw t := by
  simp [Rules.kdBasis]

include hw in
/-- **The dimension of the Koszul dual cooperad is the number of full monomials.** -/
theorem Rules.rank_KD [Nontrivial K] :
    Cardinal.lift.{v} (Module.rank K (G.KD A w)) =
      Cardinal.lift.{max u v} (Cardinal.mk (G.Full A w)) :=
  (G.kdBasis hquad hom hres hw).mk_eq_rank.symm

include hw in
/-- **The dimension of the Koszul dual cooperad is the number of full monomials**, as a natural
number (zero when there are infinitely many). -/
theorem Rules.finrank_KD [Nontrivial K] :
    Module.finrank K (G.KD A w) = Nat.card (G.Full A w) :=
  Module.finrank_eq_nat_card_basis (G.kdBasis hquad hom hres hw)

end Top

end Operad
