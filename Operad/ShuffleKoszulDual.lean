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
arity.**
-/
import Operad.ShuffleKoszul
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
noncomputable def dN : (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) := ΦL K hG ∘ₗ d K

include hG in
/-- A chain lies in the relator subcomplex exactly when its normalization vanishes. -/
lemma mem_J_iff {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n s) :
    v ∈ J K R ↔ ΦL K hG v = 0 := by
  refine ⟨ΦL_J K rk hG, fun h => ?_⟩
  have := (ΦL_spec K rk hG hv).2
  rwa [h, sub_zero] at this

omit [Fintype E] [DecidableEq E] in
lemma C_of_nrm {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K (Nrm L n s)) :
    v ∈ C K n s :=
  Finsupp.supported_mono (fun _ hy => hy.1) hv

include hG in
/-- **The normalization is a projection onto the normal bar trees with kernel `J R`**: a chain is
congruent to its normalization, which is normal. -/
lemma normalized_eq {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n s) :
    ΦL K hG v ∈ Finsupp.supported K K (Nrm L n s) ∧ v - ΦL K hG v ∈ J K R :=
  ΦL_spec K rk hG hv

include hG in
/-- **No nonzero normal chain lies in `J R`.** -/
lemma normalized_injective {n s : ℕ} {v : BarTree E →₀ K}
    (hv : v ∈ Finsupp.supported K K (Nrm L n s)) (hJ : v ∈ J K R) : v = 0 := by
  rw [← ΦL_normal K rk hG hv, ΦL_J K rk hG hJ]

include hG in
lemma dN_mem {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K (Nrm L n (s + 1))) :
    dN K rk hG v ∈ Finsupp.supported K K (Nrm L n s) :=
  (ΦL_spec K rk hG (d_mem_C K (C_of_nrm K hv))).1

include hG in
/-- **`dN` is a differential.** -/
lemma dN_dN {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ Finsupp.supported K K (Nrm L n (s + 2))) :
    dN K rk hG (dN K rk hG v) = 0 :=
  ΦL_d_ΦL_d K rk hG (C_of_nrm K hv)

include hG in
/-- **Exactness below the diagonal**: a normal cycle of degree `s + 1 < n - 1` is the boundary of
a normal chain. -/
lemma exact_dN {n s : ℕ} (hs : s + 2 < n) {v : BarTree E →₀ K}
    (hv : v ∈ Finsupp.supported K K (Nrm L n (s + 1))) (h : dN K rk hG v = 0) :
    ∃ w ∈ Finsupp.supported K K (Nrm L n (s + 2)), dN K rk hG w = v := by
  have hvC := C_of_nrm K hv
  have hdv : d K v ∈ J K R := (mem_J_iff K rk hG (d_mem_C K hvC)).2 h
  obtain ⟨y, hy, hvy⟩ := isKoszul K rk hG n (s + 1) (by omega) v hvC hdv
  obtain ⟨hyN, hyJ⟩ := ΦL_spec K rk hG hy
  refine ⟨ΦL K hG y, hyN, ?_⟩
  have h1 : ΦL K hG (d K y) = v := by
    have := ΦL_J K rk hG hvy
    rw [map_sub, ΦL_normal K rk hG hv, sub_eq_zero] at this
    exact this.symm
  have h2 : ΦL K hG (d K (y - ΦL K hG y)) = 0 := ΦL_J K rk hG (d_mem_J K R hyJ)
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

end ShuffleBar

end Operad
