/-
# The dimension of the Koszul dual cooperad, from a quadratic Gröbner basis

For relators `R` of arity three, the **Koszul dual cooperad** of the shuffle operad they present is,
in arity `n`, the homology of its bar construction in the top degree `n - 1` (`KD`). In that
degree every edge is cut, so no relator is substituted there, and the homology is the space of the
chains whose differential lies in the relator subcomplex `J R`.

When `R` is a quadratic Gröbner basis with leading monomials `L`:

* **The normal bar trees are a basis of the bar construction modulo `J R`**, in each arity and
  degree (`normalized_eq`, `normalized_injective`): normalizing the components
  (`Operad.ShuffleBar.ΦL`) is a projection onto the normal bar trees with kernel `J R`, and the
  differential becomes `dN = ΦL ∘ d` on them (`dN_dN`).
* **That complex is exact below the diagonal** (`exact_dN`), by the criterion of Dotsenko and
  Khoroshkin (`Operad.ShuffleBar.isKoszul`), and its top homology is the Koszul dual (`KD_eq`).
* So its **Euler characteristic** gives the dimension of the Koszul dual (`finrank_KD`):
  `dim KD(n) = Σ_{s < n} (-1)^(n-1-s) · #{normal bar trees of arity n with s components}`.

This depends only on `L` (`finrank_KD_eq`): **two quadratic Gröbner bases with the same leading
monomials present Koszul operads whose Koszul dual cooperads have the same dimension in every
arity.** A bar tree is a monomial with a set of cut edges (`flagBy`, `flagBy_cutKeys`), normal when
every edge whose window is in `L` is cut, and inclusion and exclusion over the cut edges evaluates
the alternating sum (`sum_ncard_nrm`): **the dimension of the Koszul dual cooperad in arity `n` is
the number of monomials of arity `n` all of whose windows are in `L`** (`finrank_KD_eq_ncard`),
the count of the dual PBW basis.
-/
import Operad.ShuffleKoszul
import Operad.ShuffleRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Set.Card

universe u v

namespace Operad

namespace LTree

variable {E : Type v}

/-- **A tree from two decorations of one shape**: the decorations of the first tree, paired with
those of the second. -/
def zipDec : LTree E → LTree Bool → LTree (E × Bool)
  | leaf a, _ => leaf a
  | node e l r, leaf _ => node (e, false) (zipDec l (leaf 0)) (zipDec r (leaf 0))
  | node e l r, node b l' r' => node (e, b) (zipDec l l') (zipDec r r')

lemma zipDec_mapDec : ∀ x : LTree (E × Bool), zipDec (x.mapDec Prod.fst) (x.mapDec Prod.snd) = x
  | leaf _ => rfl
  | node d l r => by simp only [mapDec_node, zipDec, zipDec_mapDec l, zipDec_mapDec r]

end LTree

namespace ShuffleBar

open LTree Module

section Flags

variable {E : Type v}

/-- **The bar tree of a monomial with the edges of keys in `C` cut.** -/
def flagBy (C : Finset (ℕ ×ₗ ℕ)) : LTree E → BarTree E
  | leaf a => leaf a
  | node e l r => node (e, decide (key (node e l r) ∈ C)) (flagBy C l) (flagBy C r)

lemma full_flagBy (C : Finset (ℕ ×ₗ ℕ)) : ∀ m : LTree E, (flagBy C m).mapDec Prod.fst = m
  | leaf _ => rfl
  | node e l r => by rw [flagBy, mapDec_node, full_flagBy C l, full_flagBy C r]

lemma minLabel_flagBy (C : Finset (ℕ ×ₗ ℕ)) (m : LTree E) :
    (flagBy C m).minLabel = m.minLabel := by
  rw [← minLabel_mapDec Prod.fst, full_flagBy]

lemma arity_flagBy (C : Finset (ℕ ×ₗ ℕ)) (m : LTree E) : (flagBy C m).arity = m.arity := by
  rw [← arity_mapDec Prod.fst, full_flagBy]

lemma labels_flagBy (C : Finset (ℕ ×ₗ ℕ)) (m : LTree E) : (flagBy C m).labels = m.labels := by
  rw [← labels_mapDec Prod.fst, full_flagBy]

lemma key_flagBy_node (C : Finset (ℕ ×ₗ ℕ)) (b : Bool) (e : E) (l r : LTree E) :
    key (node (e, b) (flagBy C l) (flagBy C r)) = key (node e l r) := by
  simp only [key_node, minLabel_flagBy, arity_flagBy]

lemma cutKeys_flagBy (C : Finset (ℕ ×ₗ ℕ)) :
    ∀ m : LTree E, cutKeys (flagBy C m) = C ∩ m.nodeKeys
  | leaf _ => by simp [flagBy, cutKeys, nodeKeys]
  | node e l r => by
    rw [flagBy, cutKeys, cutKeys_flagBy C l, cutKeys_flagBy C r, nodeKeys, key_flagBy_node]
    ext k
    by_cases hk : key (node e l r) ∈ C
    · simp only [hk, decide_true, if_true, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro (rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨hk, Or.inl rfl⟩
        · exact ⟨h1, Or.inr (Or.inl h2)⟩
        · exact ⟨h1, Or.inr (Or.inr h2)⟩
      · rintro ⟨h1, rfl | h2 | h2⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · simp only [hk, decide_false, Bool.false_eq_true, if_false, Finset.empty_union,
        Finset.mem_union, Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, Or.inr (Or.inl h2)⟩
        · exact ⟨h1, Or.inr (Or.inr h2)⟩
      · rintro ⟨h1, rfl | h2 | h2⟩
        · exact absurd h1 hk
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩

lemma edgeKeys_subset_nodeKeys : ∀ m : LTree E, m.edgeKeys ⊆ m.nodeKeys
  | leaf _ => by simp [edgeKeys, edgeWins]
  | node e l r => by
    rw [edgeKeys_node, nodeKeys]
    exact Finset.subset_insert _ _

lemma key_not_mem_edgeKeys (e : E) (l r : LTree E) : key (node e l r) ∉ (node e l r).edgeKeys := by
  rw [edgeKeys_node, Finset.mem_union, not_or]
  exact ⟨key_not_mem_left e l r, key_not_mem_right e l r⟩

lemma rootFlag_flagBy {C : Finset (ℕ ×ₗ ℕ)} :
    ∀ {m : LTree E}, C ⊆ m.edgeKeys → rootFlag (flagBy C m) = false
  | leaf _, _ => rfl
  | node e l r, hC => by
    simp only [flagBy, rootFlag, decide_eq_false_iff_not]
    exact fun h => key_not_mem_edgeKeys e l r (hC h)

lemma flagBy_congr {C C' : Finset (ℕ ×ₗ ℕ)} :
    ∀ m : LTree E, (∀ k ∈ m.nodeKeys, k ∈ C ↔ k ∈ C') → flagBy C m = flagBy C' m
  | leaf _, _ => rfl
  | node e l r, h => by
    have hk := h _ (Finset.mem_insert_self _ _)
    rw [flagBy, flagBy,
      flagBy_congr l fun k hk' => h k (Finset.mem_insert_of_mem (Finset.mem_union_left _ hk')),
      flagBy_congr r fun k hk' => h k (Finset.mem_insert_of_mem (Finset.mem_union_right _ hk')),
      decide_eq_decide.2 hk]

/-- **A bar tree is its monomial with its cut edges cut.** -/
lemma flagBy_cutKeys : ∀ x : BarTree E, x.labels.Nodup → flagBy (cutKeys x) (x.mapDec Prod.fst) = x
  | leaf _, _ => rfl
  | node d l r, hnd => by
    have hnd' : (l.labels ++ r.labels).Nodup := by simpa using hnd
    have hl : l.labels.Nodup := (List.nodup_append.1 hnd').1
    have hr : r.labels.Nodup := (List.nodup_append.1 hnd').2.1
    have hdisj := disjoint_nodeKeys hnd
    have hkey : key (node d.1 (l.mapDec Prod.fst) (r.mapDec Prod.fst)) = key (node d l r) :=
      key_mapDec Prod.fst (node d l r)
    rw [mapDec_node, flagBy, hkey,
      flagBy_congr (l.mapDec Prod.fst) (C' := cutKeys l) ?_, flagBy_cutKeys l hl,
      flagBy_congr (r.mapDec Prod.fst) (C' := cutKeys r) ?_, flagBy_cutKeys r hr]
    · refine congrArg (fun b => node b l r) (Prod.ext rfl ?_)
      cases hd : d.2
      · rw [decide_eq_false_iff_not]
        intro h
        simp only [cutKeys, hd, Bool.false_eq_true, if_false, Finset.empty_union,
          Finset.mem_union] at h
        rcases h with h | h
        · exact key_not_mem_left d l r (cutKeys_subset l h)
        · exact key_not_mem_right d l r (cutKeys_subset r h)
      · rw [decide_eq_true_iff]
        simp [cutKeys, hd]
    · intro k hk
      rw [nodeKeys_mapDec] at hk
      have h1 : k ≠ key (node d l r) := fun h => key_not_mem_right d l r (by rw [← h]; exact hk)
      have h2 : k ∉ cutKeys l := fun h => Finset.disjoint_left.1 hdisj (cutKeys_subset l h) hk
      simp only [cutKeys, Finset.mem_union]
      split_ifs <;> simp [h1, h2]
    · intro k hk
      rw [nodeKeys_mapDec] at hk
      have h1 : k ≠ key (node d l r) := fun h => key_not_mem_left d l r (by rw [← h]; exact hk)
      have h2 : k ∉ cutKeys r := fun h => Finset.disjoint_left.1 hdisj hk (cutKeys_subset r h)
      simp only [cutKeys, Finset.mem_union]
      split_ifs <;> simp [h1, h2]

/-- **A monomial all of whose windows lie in `L`.** -/
def IsFull (L : Set (LTree E)) (m : LTree E) : Prop := ∀ kw ∈ m.edgeWins, kw.2 ∈ L

/-- The windows of the edges are the windows. -/
lemma edgeWins_map_snd : ∀ t : LTree E, t.edgeWins.map Prod.snd = t.windows
  | leaf _ => rfl
  | node e l r => by
    have hl := edgeWins_map_snd l
    have hr := edgeWins_map_snd r
    simp only [edgeWins, windows, List.map_append, hl, hr]
    cases l <;> cases r <;> rfl

lemma isFull_iff_windows {L : Set (LTree E)} {t : LTree E} :
    IsFull L t ↔ ∀ w ∈ t.windows, w ∈ L := by
  rw [← edgeWins_map_snd, IsFull, List.forall_mem_map]

lemma isFull_std {L : Set (LTree E)} {t : LTree E} : IsFull L (std t) ↔ IsFull L t := by
  simp only [isFull_iff_windows, std, mem_windows_relabel (strictOn_count t)]

end Flags

variable {E : Type v} [Fintype E] [DecidableEq E]

/-! ## Finiteness -/

/-- **The bar trees of arity `n`**, of every degree: a finite set. -/
def barTrees (n : ℕ) : Finset (BarTree E) :=
  ((monomials (E := E) n) ×ˢ (monomials (E := Bool) n)).image fun p => zipDec p.1 p.2

lemma mem_barTrees {n s : ℕ} {x : BarTree E} (hx : Adm n s x) : x ∈ barTrees n := by
  refine Finset.mem_image.2 ⟨(x.mapDec Prod.fst, x.mapDec Prod.snd),
    Finset.mem_product.2 ⟨full_mem_monomials hx, ?_⟩, zipDec_mapDec x⟩
  exact (mem_monomials _ _).2 ⟨(isShuffle_mapDec _ x).2 hx.1.shuffle, by simpa using hx.2.1⟩

lemma finite_adm (n s : ℕ) : {x : BarTree E | Adm n s x}.Finite :=
  (barTrees n).finite_toSet.subset fun _ hx => mem_barTrees hx

lemma finite_nrm (L : Set (LTree E)) (n s : ℕ) : (Nrm L n s).Finite :=
  (finite_adm n s).subset fun _ hx => hx.1

omit [Fintype E] [DecidableEq E] in
lemma nrm_zero (L : Set (LTree E)) (n : ℕ) : Nrm L n 0 = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hx => by have := hx.1.2.2; omega

omit [Fintype E] [DecidableEq E] in
/-- **In the top degree every bar tree is normal**: all its edges are cut. -/
lemma adm_top_normal (L : Set (LTree E)) {n : ℕ} {x : BarTree E} (hx : Adm n (n - 1) x) :
    NormalBar L x := by
  intro kw hkw hc
  exfalso
  have hsub := cutKeys_subset_edgeKeys hx.1.root
  have hlen : x.arity = n := by rw [← length_labels, hx.2.1.length_eq, List.length_range]
  cases x with
  | leaf a =>
    simp [mapDec, edgeWins] at hkw
  | node d l r =>
    have hnd : (node d.1 (l.mapDec Prod.fst) (r.mapDec Prod.fst)).labels.Nodup := by
      simpa using hx.1.nodup
    have hcard := card_edgeKeys hnd
    have harity : (node d.1 (l.mapDec Prod.fst) (r.mapDec Prod.fst)).arity = n := by
      rw [← hlen]
      simp [arity]
    have hc2 := hx.2.2
    simp only [mapDec_node] at hsub hkw
    have heq : cutKeys (node d l r) = (node d.1 (l.mapDec Prod.fst) (r.mapDec Prod.fst)).edgeKeys :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    exact hc (heq ▸ mem_edgeKeys.2 ⟨kw.2, hkw⟩)

/-! ## Dimensions -/

variable (K : Type u) [Field K]

omit [Fintype E] [DecidableEq E] in
lemma finiteDimensional_supported {S : Set (BarTree E)} (hS : S.Finite) :
    FiniteDimensional K (Finsupp.supported K K S) := by
  haveI := hS.fintype
  exact LinearEquiv.finiteDimensional (Finsupp.supportedEquivFinsupp S).symm

omit [Fintype E] [DecidableEq E] in
lemma finrank_supported {S : Set (BarTree E)} (hS : S.Finite) :
    finrank K (Finsupp.supported K K S) = S.ncard := by
  haveI := hS.fintype
  rw [(Finsupp.supportedEquivFinsupp S).finrank_eq, Module.finrank_finsupp_self,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

omit [Fintype E] [DecidableEq E] in
/-- **Rank and nullity** of a linear map on a subspace. -/
lemma finrank_eq_map_add {M M' : Type*} [AddCommGroup M] [Module K M] [AddCommGroup M']
    [Module K M'] (f : M →ₗ[K] M') (p : Submodule K M) [FiniteDimensional K p] :
    finrank K p = finrank K (p.map f) + finrank K (p ⊓ LinearMap.ker f : Submodule K M) := by
  have h := (f.domRestrict p).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h, ← Submodule.map_comap_subtype,
    ← (Submodule.equivMapOfInjective _ p.injective_subtype _).finrank_eq]

/-- An alternating sum, one step longer. -/
lemma altSum_succ (a : ℕ → ℤ) (m : ℕ) :
    ∑ s ∈ Finset.range (m + 2), (-1) ^ (m + 1 - s) * a s =
      a (m + 1) - ∑ s ∈ Finset.range (m + 1), (-1) ^ (m - s) * a s := by
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, sub_eq_add_neg, add_comm,
    ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  rw [show m + 1 - s = (m - s) + 1 by omega, pow_succ]
  ring

/-- **The Euler characteristic of an exact sequence**: dimensions `a s` split as cycles `z s` and
boundaries `b (s - 1)`, with no homology in the degrees `1 ≤ s < m`. -/
lemma euler (a z b : ℕ → ℤ) (top : ℕ) (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (ha : ∀ s, 1 ≤ s → s ≤ top → a s = z s + b (s - 1))
    (hz : ∀ s, 1 ≤ s → s < top → z s = b s) :
    ∀ m, 1 ≤ m → m ≤ top → ∑ s ∈ Finset.range (m + 1), (-1) ^ (m - s) * a s = z m := by
  intro m hm hmt
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · simp [Finset.sum_range_succ, ha0, ha 1 le_rfl hmt, hb0]
    · rw [altSum_succ, ih hm' (by omega), ha (m + 1) (by omega) hmt, Nat.add_sub_cancel,
        hz m hm' (by omega)]
      ring

/-! ## The Koszul dual cooperad -/

/-- **The Koszul dual cooperad** of the shuffle operad presented by `R`, in arity `n`: the
homology of the bar construction in the top degree `n - 1`, the chains of that degree whose
differential lies in the relator subcomplex. -/
noncomputable def KD (R : Submodule K (Mono E 3 → K)) (n : ℕ) : Submodule K (BarTree E →₀ K) :=
  C K n (n - 1) ⊓ (J K R).comap (d K)

omit [Fintype E] [DecidableEq E] in
lemma C_zero (n : ℕ) : C (E := E) K n 0 = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
  ext y
  by_contra h
  have := (Finsupp.mem_supported K v).1 hv (Finsupp.mem_support_iff.2 h)
  exact absurd this.2.2 (by omega)

lemma KD_of_lt_two (R : Submodule K (Mono E 3 → K)) {n : ℕ} (hn : n < 2) : KD K R n = ⊥ := by
  rw [KD, show n - 1 = 0 by omega, C_zero, bot_inf_eq]

variable (rk : E → ℕ) {L : Set (LTree E)} {R : Submodule K (Mono E 3 → K)}
  (hG : IsGroebner K rk L R)

/-- **The differential on the normal bar trees**: the differential followed by normalization. -/
noncomputable def dN : (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) := ΦL K hG.data ∘ₗ d K

include hG in
/-- A chain lies in the relator subcomplex exactly when its normalization vanishes. -/
lemma mem_J_iff {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n s) :
    v ∈ J K R ↔ ΦL K hG.data v = 0 := by
  refine ⟨ΦL_J K hG.data, fun h => ?_⟩
  have := (ΦL_spec K hG.data hv).2
  rwa [h, sub_zero] at this

omit [Fintype E] [DecidableEq E] in
lemma C_of_nrm {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K (Nrm L n s)) :
    v ∈ C K n s :=
  Finsupp.supported_mono (fun _ hy => hy.1) hv

include hG in
/-- **The normalization is a projection onto the normal bar trees with kernel `J R`**: a chain is
congruent to its normalization, which is normal. -/
lemma normalized_eq {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n s) :
    ΦL K hG.data v ∈ Finsupp.supported K K (Nrm L n s) ∧ v - ΦL K hG.data v ∈ J K R :=
  ΦL_spec K hG.data hv

include hG in
/-- **No nonzero normal chain lies in `J R`.** -/
lemma normalized_injective {n s : ℕ} {v : BarTree E →₀ K}
    (hv : v ∈ Finsupp.supported K K (Nrm L n s)) (hJ : v ∈ J K R) : v = 0 := by
  rw [← ΦL_normal K hG.data hv, ΦL_J K hG.data hJ]

include hG in
lemma dN_mem {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K (Nrm L n (s + 1))) :
    dN K rk hG v ∈ Finsupp.supported K K (Nrm L n s) :=
  (ΦL_spec K hG.data (d_mem_C K (C_of_nrm K hv))).1

include hG in
/-- **`dN` is a differential.** -/
lemma dN_dN {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K (Nrm L n (s + 2))) :
    dN K rk hG (dN K rk hG v) = 0 :=
  ΦL_d_ΦL_d K hG.data (C_of_nrm K hv)

include hG in
/-- **Exactness below the diagonal**: a normal cycle of degree `s + 1 < n - 1` is the boundary of
a normal chain. -/
lemma exact_dN {n s : ℕ} (hs : s + 2 < n) {v : BarTree E →₀ K}
    (hv : v ∈ Finsupp.supported K K (Nrm L n (s + 1))) (h : dN K rk hG v = 0) :
    ∃ w ∈ Finsupp.supported K K (Nrm L n (s + 2)), dN K rk hG w = v := by
  have hvC := C_of_nrm K hv
  have hdv : d K v ∈ J K R := (mem_J_iff K rk hG (d_mem_C K hvC)).2 h
  obtain ⟨y, hy, hvy⟩ := isKoszul K rk hG n (s + 1) (by omega) v hvC hdv
  obtain ⟨hyN, hyJ⟩ := ΦL_spec K hG.data hy
  refine ⟨ΦL K hG.data y, hyN, ?_⟩
  have h1 : ΦL K hG.data (d K y) = v := by
    have := ΦL_J K hG.data hvy
    rw [map_sub, ΦL_normal K hG.data hv, sub_eq_zero] at this
    exact this.symm
  have h2 : ΦL K hG.data (d K (y - ΦL K hG.data y)) = 0 := ΦL_J K hG.data (d_mem_J K R hyJ)
  rw [map_sub, map_sub, h1, sub_eq_zero] at h2
  exact h2.symm

include hG in
/-- **The Koszul dual is the top homology of the normal complex.** -/
lemma KD_eq {n : ℕ} (hn : 2 ≤ n) :
    KD K R n = Finsupp.supported K K (Nrm L n (n - 1)) ⊓ LinearMap.ker (dN K rk hG) := by
  have hC : C K n (n - 1) = Finsupp.supported K K (Nrm L n (n - 1)) :=
    le_antisymm (Finsupp.supported_mono fun x hx => ⟨hx, adm_top_normal L hx⟩)
      (Finsupp.supported_mono fun _ hx => hx.1)
  ext v
  simp only [KD, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker, hC]
  refine and_congr_right fun hv => ?_
  have hdv : d K v ∈ C K n (n - 2) :=
    d_mem_C K (n := n) (s := n - 2) (by rw [show n - 2 + 1 = n - 1 by omega, hC]; exact hv)
  exact mem_J_iff K rk hG hdv

include hG in
/-- **The dimension of the Koszul dual cooperad**, from the leading monomials: the Euler
characteristic of the bar construction modulo `J R`, whose basis is the normal bar trees. -/
theorem finrank_KD {n : ℕ} (hn : 2 ≤ n) :
    (finrank K (KD K R n) : ℤ) =
      ∑ s ∈ Finset.range n, (-1) ^ (n - 1 - s) * ((Nrm L n s).ncard : ℤ) := by
  set N : ℕ → Submodule K (BarTree E →₀ K) := fun s => Finsupp.supported K K (Nrm L n s)
  have hfd : ∀ s, FiniteDimensional K (N s) := fun s =>
    finiteDimensional_supported K (finite_nrm L n s)
  let a : ℕ → ℤ := fun s => (Nrm L n s).ncard
  let z : ℕ → ℤ := fun s => finrank K (N s ⊓ LinearMap.ker (dN K rk hG) : Submodule K _)
  let b : ℕ → ℤ := fun s => finrank K ((N (s + 1)).map (dN K rk hG))
  have hmap : ∀ s, (N (s + 1)).map (dN K rk hG) ≤ N s := by
    rintro s _ ⟨v, hv, rfl⟩
    exact dN_mem K rk hG hv
  have ha0 : a 0 = 0 := by simp [a, nrm_zero]
  have hb0 : b 0 = 0 := by
    have : (N 1).map (dN K rk hG) = ⊥ := by
      refine eq_bot_iff.2 ((hmap 0).trans ?_)
      simp [N, nrm_zero]
    simp [b, this]
  have ha : ∀ s, 1 ≤ s → s ≤ n - 1 → a s = z s + b (s - 1) := by
    intro s hs _
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have := finrank_eq_map_add K (dN K rk hG) (N (t + 1))
    rw [finrank_supported K (finite_nrm L n (t + 1))] at this
    simp only [a, z, b, Nat.add_sub_cancel, this]
    push_cast
    ring
  have hz : ∀ s, 1 ≤ s → s < n - 1 → z s = b s := by
    intro s hs hsn
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have : N (t + 1) ⊓ LinearMap.ker (dN K rk hG) = (N (t + 1 + 1)).map (dN K rk hG) := by
      refine le_antisymm ?_ ?_
      · rintro v ⟨hv, hdv⟩
        obtain ⟨w, hw, rfl⟩ := exact_dN K rk hG (by omega) hv hdv
        exact ⟨w, hw, rfl⟩
      · rintro _ ⟨w, hw, rfl⟩
        exact ⟨hmap (t + 1) ⟨w, hw, rfl⟩, dN_dN K rk hG hw⟩
    simp only [z, b]
    rw [this]
  have key := euler a z b (n - 1) ha0 hb0 ha hz (n - 1) (by omega) le_rfl
  rw [show n - 1 + 1 = n by omega] at key
  rw [key, KD_eq K rk hG hn]

include hG in
/-- **Two quadratic Gröbner bases with the same leading monomials present operads whose Koszul
dual cooperads have the same dimension in every arity.** -/
theorem finrank_KD_eq {R' : Submodule K (Mono E 3 → K)} (hG' : IsGroebner K rk L R') (n : ℕ) :
    finrank K (KD K R n) = finrank K (KD K R' n) := by
  rcases lt_or_ge n 2 with hn | hn
  · rw [KD_of_lt_two K R hn, KD_of_lt_two K R' hn]
  · have h := finrank_KD K rk hG hn
    rw [← finrank_KD K rk hG' hn] at h
    exact_mod_cast h

/-! ## The dimension as a number of monomials -/

omit [Fintype E] [DecidableEq E] in
/-- The keys of the edges of a monomial with distinct labels are distinct. -/
lemma nodup_edgeWins_keys {m : LTree E} (hnd : m.labels.Nodup) :
    (m.edgeWins.map Prod.fst).Nodup :=
  (List.nodup_append.1 ((perm_keyList m).nodup_iff.1 (nodup_keyList m hnd))).2.1

open Classical in
/-- **The normal bar trees of degree `s`**, counted by their monomial and their cut edges. -/
lemma ncard_nrm (L : Set (LTree E)) (n s : ℕ) :
    (Nrm L n s).ncard = ∑ m ∈ monomials (E := E) n, (m.edgeKeys.powerset.filter
      fun C => C.card + 1 = s ∧ ∀ kw ∈ m.edgeWins, kw.1 ∉ C → kw.2 ∉ L).card := by
  rw [← Finset.card_sigma]
  set T := (monomials (E := E) n).sigma fun m => m.edgeKeys.powerset.filter
    fun C => C.card + 1 = s ∧ ∀ kw ∈ m.edgeWins, kw.1 ∉ C → kw.2 ∉ L
  have hT : Nrm L n s = ↑(T.image fun p => flagBy p.2 p.1) := by
    ext x
    simp only [T, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_sigma,
      Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hx, hN⟩
      exact ⟨⟨x.mapDec Prod.fst, cutKeys x⟩, ⟨full_mem_monomials hx,
        cutKeys_subset_edgeKeys hx.1.root, hx.2.2, hN⟩, flagBy_cutKeys x hx.1.nodup⟩
    · rintro ⟨⟨m, C⟩, ⟨hm, hC, hs, hg⟩, rfl⟩
      obtain ⟨hms, hml⟩ := (mem_monomials _ _).1 hm
      have hcut : cutKeys (flagBy C m) = C :=
        (cutKeys_flagBy C m).trans (Finset.inter_eq_left.2 (hC.trans (edgeKeys_subset_nodeKeys m)))
      refine ⟨⟨⟨(isShuffle_mapDec Prod.fst _).1 (by rw [full_flagBy]; exact hms),
        by rw [labels_flagBy]; exact hml.nodup_iff.2 List.nodup_range, rootFlag_flagBy hC⟩,
        by rw [labels_flagBy]; exact hml, by rw [hcut]; exact hs⟩, ?_⟩
      intro kw hkw hk
      rw [full_flagBy] at hkw
      rw [hcut] at hk
      exact hg kw hkw hk
  rw [hT, Set.ncard_coe_finset, Finset.card_image_of_injOn]
  rintro ⟨m, C⟩ hp ⟨m', C'⟩ hp' h
  simp only [T, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_powerset] at hp hp' h
  have hm : m = m' := by rw [← full_flagBy C m, h, full_flagBy]
  subst hm
  have hC : C = C' := by
    have h1 := cutKeys_flagBy C m
    have h2 := cutKeys_flagBy C' m
    rw [h, h2, Finset.inter_eq_left.2 (hp'.2.1.trans (edgeKeys_subset_nodeKeys m)),
      Finset.inter_eq_left.2 (hp.2.1.trans (edgeKeys_subset_nodeKeys m))] at h1
    exact h1.symm
  rw [hC]

omit [Fintype E] [DecidableEq E] in
/-- **Inclusion and exclusion over the cut edges** of a monomial whose windows in `L` must be
cut. -/
lemma sum_good_sets (L : Set (LTree E)) {m : LTree E} (hnd : m.labels.Nodup) [DecidablePred
    fun C : Finset (ℕ ×ₗ ℕ) => ∀ kw ∈ m.edgeWins, kw.1 ∉ C → kw.2 ∉ L] [Decidable (IsFull L m)] :
    ∑ C ∈ m.edgeKeys.powerset.filter (fun C => ∀ kw ∈ m.edgeWins, kw.1 ∉ C → kw.2 ∉ L),
      (-1 : ℤ) ^ (m.edgeKeys \ C).card = if IsFull L m then 1 else 0 := by
  classical
  set Ed := m.edgeKeys
  set G := Ed.filter fun k => ∃ w, (k, w) ∈ m.edgeWins ∧ w ∈ L
  have hgood : ∀ C ⊆ Ed, (∀ kw ∈ m.edgeWins, kw.1 ∉ C → kw.2 ∉ L) ↔ G ⊆ C := by
    intro C _
    constructor
    · intro h k hk
      obtain ⟨-, w, hw, hwL⟩ := Finset.mem_filter.1 hk
      by_contra hkC
      exact h (k, w) hw hkC hwL
    · intro h kw hkw hkC hL
      exact hkC (h (Finset.mem_filter.2 ⟨mem_edgeKeys.2 ⟨kw.2, hkw⟩, kw.2, hkw, hL⟩))
  have hGEd : G ⊆ Ed := Finset.filter_subset _ _
  calc ∑ C ∈ Ed.powerset.filter (fun C => ∀ kw ∈ m.edgeWins, kw.1 ∉ C → kw.2 ∉ L),
        (-1 : ℤ) ^ (Ed \ C).card
      = ∑ D ∈ (Ed \ G).powerset, (-1 : ℤ) ^ D.card := by
        refine Finset.sum_nbij' (fun C => Ed \ C) (fun D => Ed \ D) ?_ ?_ ?_ ?_ ?_
        · intro C hC
          rw [Finset.mem_filter, Finset.mem_powerset] at hC
          rw [Finset.mem_powerset]
          exact Finset.sdiff_subset_sdiff (subset_refl _) ((hgood C hC.1).1 hC.2)
        · intro D hD
          rw [Finset.mem_powerset] at hD
          rw [Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.sdiff_subset, (hgood _ Finset.sdiff_subset).2 fun k hk => ?_⟩
          refine Finset.mem_sdiff.2 ⟨hGEd hk, fun hkD => ?_⟩
          exact (Finset.mem_sdiff.1 (hD hkD)).2 hk
        · intro C hC
          rw [Finset.mem_filter, Finset.mem_powerset] at hC
          exact Finset.sdiff_sdiff_eq_self hC.1
        · intro D hD
          rw [Finset.mem_powerset] at hD
          exact Finset.sdiff_sdiff_eq_self (hD.trans Finset.sdiff_subset)
        · intro C _
          rfl
    _ = if IsFull L m then 1 else 0 := by
        rw [Finset.sum_powerset_neg_one_pow_card]
        congr 1
        apply propext
        rw [Finset.sdiff_eq_empty_iff_subset]
        constructor
        · intro h kw hkw
          obtain ⟨-, w, hw, hwL⟩ := Finset.mem_filter.1 (h (mem_edgeKeys.2 ⟨kw.2, hkw⟩))
          have := List.inj_on_of_nodup_map (nodup_edgeWins_keys hnd) hkw hw rfl
          rw [this]
          exact hwL
        · intro h k hk
          obtain ⟨w, hw⟩ := mem_edgeKeys.1 hk
          exact Finset.mem_filter.2 ⟨hk, w, hw, h _ hw⟩

open Classical in
/-- **The Euler characteristic of the normal bar trees** is the number of monomials all of whose
windows lie in `L`. -/
theorem sum_ncard_nrm (L : Set (LTree E)) {n : ℕ} (hn : 2 ≤ n) :
    ∑ s ∈ Finset.range n, (-1 : ℤ) ^ (n - 1 - s) * ((Nrm L n s).ncard : ℤ) =
      (((monomials (E := E) n).filter (IsFull L)).card : ℤ) := by
  simp_rw [ncard_nrm, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨-, hml⟩ := (mem_monomials _ _).1 hm
  have hnd : m.labels.Nodup := hml.nodup_iff.2 List.nodup_range
  have hEd : m.edgeKeys.card + 2 = n := by
    cases m with
    | leaf a =>
      have := hml.length_eq
      simp at this
      omega
    | node e l r =>
      rw [card_edgeKeys hnd, ← length_labels, hml.length_eq, List.length_range]
  rw [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ← sum_good_sets L hnd]
  simp_rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun C hC => ?_
  rw [Finset.mem_powerset] at hC
  have hcard := Finset.card_le_card hC
  split_ifs with hg
  · rw [Finset.sum_congr rfl fun x _ => if_congr (and_iff_left hg) rfl rfl,
      Finset.sum_ite_eq (Finset.range n) (C.card + 1), if_pos (Finset.mem_range.2 (by omega)),
      Finset.card_sdiff_of_subset hC]
    congr 1
    omega
  · exact Finset.sum_eq_zero fun x _ => if_neg fun h => hg h.2

include hG in
/-- **The dimension of the Koszul dual cooperad is the number of monomials all of whose windows
are leading**, in every arity `n ≥ 2`. -/
theorem finrank_KD_eq_ncard {n : ℕ} (hn : 2 ≤ n) :
    finrank K (KD K R n) = {m | m ∈ monomials (E := E) n ∧ IsFull L m}.ncard := by
  classical
  have h := finrank_KD K rk hG hn
  rw [sum_ncard_nrm L hn] at h
  have hset : {m | m ∈ monomials (E := E) n ∧ IsFull L m} =
      ↑((monomials (E := E) n).filter (IsFull L)) := by
    ext m
    simp
  rw [hset, Set.ncard_coe_finset]
  exact_mod_cast h

end ShuffleBar

end Operad
