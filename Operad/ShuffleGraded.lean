/-
# Weight gradings and the associated graded of the Koszul dual cooperad

A weight `W : α → ℕ` on a basis grades the free module `α →₀ K` (`Graded.wproj`, the component of
weight `N`). The **associated graded** of a subspace `V` for the filtration by weight is the span
of the top components `v_N` of the `v ∈ V` with no component of weight above `N` (`Graded.grW`),
and **it has the dimension of `V`** (`Graded.finrank_grW`).

For shuffle operads, a weight `w` on the generators weighs monomials and bar trees additively
(`LTree.wdeg`, `ShuffleBar.wdegB`): merging along a cut edge keeps the weight, so the differential
of the bar construction preserves it (`ShuffleBar.d_wproj`), and substituting a monomial at an
uncut edge adds its weight to that of the context (`ShuffleBar.wdegB_substBar`). Suppose the
relators `R₀` are spanned by the top components of relators of `R` (`ShuffleBar.wprojM`).

* The substituted relators of `R₀` are top components of substituted relators of `R`
  (`ShuffleBar.substRel_wproj`, `ShuffleBar.Jgen_le_grW`), and the relator subcomplex in an arity
  and a degree is spanned by the relators substituted at the bar trees of that arity and degree
  (`ShuffleBar.J_inf_C_le`): so **the relator subcomplex of `R₀` is the associated graded of that
  of `R`** when the two have the same dimension (`ShuffleBar.J_inf_C_eq_grW`).
* Then the top component of an element of the Koszul dual cooperad of `R` lies in that of `R₀`
  (`ShuffleBar.grW_KD_le`), and **the Koszul dual cooperad of `R₀` is the associated graded of
  that of `R`** when they have the same dimension (`ShuffleBar.KD_eq_grW`): the Rees family of the
  Koszul dual cooperad is flat, with special fiber the Koszul dual cooperad of `R₀`.
* Both dimension conditions hold for two quadratic Gröbner bases with the same leading monomials
  (`ShuffleBar.finrank_J_inf_C_add`, `ShuffleBar.KD_eq_grW_of_isGroebner`).
-/
import Operad.ShuffleRescale

universe u v

namespace Operad

namespace Graded

open Module

variable {α : Type*} (K : Type*) [Field K] (W : α → ℕ)

/-- **The component of weight `N`.** -/
noncomputable def wproj (N : ℕ) : (α →₀ K) →ₗ[K] (α →₀ K) where
  toFun v := v.filter fun x => W x = N
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

variable {K W}

lemma wproj_apply (N : ℕ) (v : α →₀ K) (x : α) :
    wproj K W N v x = if W x = N then v x else 0 := by
  simp [wproj, Finsupp.filter_apply]

lemma wproj_wproj (M N : ℕ) (v : α →₀ K) :
    wproj K W N (wproj K W M v) = if M = N then wproj K W N v else 0 := by
  ext x
  by_cases hMN : M = N
  · subst hMN
    simp only [wproj_apply, if_true]
    split_ifs <;> rfl
  · rw [if_neg hMN, wproj_apply, wproj_apply]
    split_ifs with h1 h2
    · exact absurd (h2.symm.trans h1) hMN
    · rfl
    · rfl

lemma wproj_single (N : ℕ) (x : α) (c : K) :
    wproj K W N (Finsupp.single x c) = if W x = N then Finsupp.single x c else 0 := by
  ext y
  rw [wproj_apply]
  by_cases hxy : x = y
  · subst hxy
    split_ifs <;> simp
  · split_ifs <;> simp [hxy]

/-- `v` has no component of weight above `N`. -/
def IsBelow (N : ℕ) (v : α →₀ K) : Prop := ∀ k, N < k → wproj K W k v = 0

variable (K W)

/-- **The filtration by weight**: the elements of `V` with no component above `N`. -/
noncomputable def filt (V : Submodule K (α →₀ K)) (N : ℕ) : Submodule K (α →₀ K) :=
  V ⊓ ⨅ (k : ℕ) (_ : N < k), LinearMap.ker (wproj K W k)

/-- **The associated graded** of `V`: the span of the top components of its elements. -/
noncomputable def grW (V : Submodule K (α →₀ K)) : Submodule K (α →₀ K) :=
  ⨆ N, (filt K W V N).map (wproj K W N)

variable {K W}

lemma mem_filt {V : Submodule K (α →₀ K)} {N : ℕ} {v : α →₀ K} :
    v ∈ filt K W V N ↔ v ∈ V ∧ IsBelow (K := K) (W := W) N v := by
  simp [filt, Submodule.mem_iInf, IsBelow]

lemma wproj_mem_grW {V : Submodule K (α →₀ K)} {N : ℕ} {v : α →₀ K} (hv : v ∈ V)
    (hN : IsBelow (K := K) (W := W) N v) : wproj K W N v ∈ grW K W V :=
  Submodule.mem_iSup_of_mem N (Submodule.mem_map_of_mem (mem_filt.2 ⟨hv, hN⟩))

/-- **`grW V` is spanned by the top components.** -/
lemma grW_le {V P : Submodule K (α →₀ K)}
    (h : ∀ N, ∀ v ∈ V, IsBelow (K := K) (W := W) N v → wproj K W N v ∈ P) : grW K W V ≤ P :=
  iSup_le fun N => Submodule.map_le_iff_le_comap.2 fun v hv =>
    h N v (mem_filt.1 hv).1 (mem_filt.1 hv).2

lemma filt_mono (V : Submodule K (α →₀ K)) {M N : ℕ} (h : M ≤ N) :
    filt K W V M ≤ filt K W V N := fun _ hv =>
  mem_filt.2 ⟨(mem_filt.1 hv).1, fun k hk => (mem_filt.1 hv).2 k (lt_of_le_of_lt h hk)⟩

variable (K W) in
/-- The pieces of weight at most `m` of the associated graded. -/
noncomputable def grLe (V : Submodule K (α →₀ K)) (m : ℕ) : Submodule K (α →₀ K) :=
  (Finset.range (m + 1)).sup fun N => (filt K W V N).map (wproj K W N)

lemma grLe_le_ker (V : Submodule K (α →₀ K)) (m : ℕ) :
    grLe K W V m ≤ LinearMap.ker (wproj K W (m + 1)) := by
  refine Finset.sup_le fun N hN => Submodule.map_le_iff_le_comap.2 fun _ _ => ?_
  rw [Submodule.mem_comap, LinearMap.mem_ker, wproj_wproj,
    if_neg (by rw [Finset.mem_range] at hN; omega)]

lemma disjoint_grLe (V : Submodule K (α →₀ K)) (m : ℕ) :
    grLe K W V m ⊓ (filt K W V (m + 1)).map (wproj K W (m + 1)) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  obtain ⟨hx1, v, -, rfl⟩ := hx
  have := grLe_le_ker V m hx1
  rwa [LinearMap.mem_ker, wproj_wproj, if_pos rfl] at this


section Finrank

variable (V : Submodule K (α →₀ K)) [FiniteDimensional K V]

instance (N : ℕ) : FiniteDimensional K (filt K W V N) :=
  Submodule.finiteDimensional_of_le inf_le_left

instance (m : ℕ) : FiniteDimensional K (grLe K W V m) := by
  unfold grLe
  infer_instance

omit [FiniteDimensional K V] in
lemma wproj_eq_self_of_filt_zero {v : α →₀ K} (hv : v ∈ filt K W V 0) : wproj K W 0 v = v := by
  ext x
  rw [wproj_apply]
  split_ifs with hx
  · rfl
  · have h := congrArg (fun f => f x) ((mem_filt.1 hv).2 (W x) (Nat.pos_of_ne_zero hx))
    simp only [wproj_apply, if_true, Finsupp.coe_zero, Pi.zero_apply] at h
    exact h.symm

/-- **The pieces of weight at most `m` of the associated graded have the dimension of the
filtration step `m`.** -/
lemma finrank_grLe (m : ℕ) : finrank K (grLe K W V m) = finrank K (filt K W V m) := by
  induction m with
  | zero =>
    have hG : grLe K W V 0 = filt K W V 0 := by
      rw [grLe, Finset.range_one, Finset.sup_singleton]
      ext x
      constructor
      · rintro ⟨v, hv, rfl⟩
        rw [wproj_eq_self_of_filt_zero V hv]
        exact hv
      · intro hx
        exact ⟨x, hx, wproj_eq_self_of_filt_zero V hx⟩
    rw [hG]
  | succ m ih =>
    have hG : grLe K W V (m + 1)
        = grLe K W V m ⊔ (filt K W V (m + 1)).map (wproj K W (m + 1)) := by
      rw [grLe, grLe, Finset.range_add_one, Finset.sup_insert, sup_comm]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (grLe K W V m)
      ((filt K W V (m + 1)).map (wproj K W (m + 1)))
    rw [disjoint_grLe, finrank_bot, add_zero, ← hG, ih] at h1
    have h2 := ShuffleBar.finrank_eq_map_add K (wproj K W (m + 1)) (filt K W V (m + 1))
    have hker : filt K W V (m + 1) ⊓ LinearMap.ker (wproj K W (m + 1)) = filt K W V m := by
      ext v
      simp only [Submodule.mem_inf, LinearMap.mem_ker]
      constructor
      · rintro ⟨hv, h0⟩
        refine mem_filt.2 ⟨(mem_filt.1 hv).1, fun k hk => ?_⟩
        rcases Nat.lt_or_ge (m + 1) k with h | h
        · exact (mem_filt.1 hv).2 k h
        · rwa [show k = m + 1 by omega]
      · intro h
        exact ⟨filt_mono V (Nat.le_succ m) h, (mem_filt.1 h).2 (m + 1) (Nat.lt_succ_self m)⟩
    rw [hker] at h2
    omega

/-- **The associated graded has the dimension of the space**, for a filtration by weight bounded
on `V`. -/
theorem finrank_grW {B : ℕ} (hB : ∀ v ∈ V, IsBelow (K := K) (W := W) B v) :
    finrank K (grW K W V) = finrank K V := by
  have h1 : grW K W V = grLe K W V B := by
    apply le_antisymm
    · refine iSup_le fun N => ?_
      by_cases hN : N ≤ B
      · exact Finset.le_sup (f := fun N => (filt K W V N).map (wproj K W N))
          (Finset.mem_range.2 (by omega))
      · rintro _ ⟨v, hv, rfl⟩
        rw [hB v (mem_filt.1 hv).1 N (by omega)]
        exact zero_mem _
    · exact Finset.sup_le fun N _ => le_iSup (fun N => (filt K W V N).map (wproj K W N)) N
  have h2 : filt K W V B = V := le_antisymm inf_le_left fun v hv => mem_filt.2 ⟨hv, hB v hv⟩
  rw [h1, finrank_grLe, h2]

end Finrank

end Graded

namespace LTree

variable {E : Type v}

/-- **The weight of a tree**: the sum of the weights of the decorations of its vertices. -/
def wdeg (w : E → ℕ) : LTree E → ℕ
  | leaf _ => 0
  | node e a b => w e + wdeg w a + wdeg w b

@[simp] lemma wdeg_leaf (w : E → ℕ) (a : ℕ) : wdeg w (leaf a : LTree E) = 0 := rfl

@[simp] lemma wdeg_node (w : E → ℕ) (e : E) (a b : LTree E) :
    wdeg w (node e a b) = w e + wdeg w a + wdeg w b := rfl

lemma wdeg_mapDec {F : Type*} (f : E → F) (w : F → ℕ) :
    ∀ t : LTree E, wdeg w (t.mapDec f) = wdeg (w ∘ f) t
  | leaf _ => rfl
  | node e a b => by
    simp only [mapDec_node, wdeg_node, wdeg_mapDec f w a, wdeg_mapDec f w b, Function.comp_apply]

lemma wdeg_plug (w : E → ℕ) (ins : ℕ → LTree E) :
    ∀ m : LTree E, wdeg w (m.plug ins) = wdeg w m + (m.labels.map fun a => wdeg w (ins a)).sum
  | leaf a => by simp [plug, labels]
  | node e a b => by
    simp only [plug, wdeg_node, wdeg_plug w ins a, wdeg_plug w ins b, labels, List.map_append,
      List.sum_append]
    ring

lemma wdeg_replaceAt (w : E → ℕ) :
    ∀ (t : LTree E) (p : List Bool), (∃ e a b, t.subtreeAt p = node e a b) →
      ∃ c : ℕ, ∀ u : LTree E, wdeg w (t.replaceAt p u) = c + wdeg w u
  | t, [], _ => ⟨0, fun u => by simp⟩
  | leaf _, _ :: _, h => by simp [subtreeAt] at h
  | node e a b, false :: p, h => by
    obtain ⟨c, hc⟩ := wdeg_replaceAt w a p h
    exact ⟨w e + wdeg w b + c, fun u => by simp only [replaceAt, wdeg_node, hc]; ring⟩
  | node e a b, true :: p, h => by
    obtain ⟨c, hc⟩ := wdeg_replaceAt w b p h
    exact ⟨w e + wdeg w a + c, fun u => by simp only [replaceAt, wdeg_node, hc]; ring⟩

/-- **Substituting at a window** adds the weight of the substituted monomial to that of the
context. -/
lemma wdeg_substAt (w : E → ℕ) {t : LTree E} {p : List Bool} {s : Bool} (h : t.IsEdge p s) :
    ∃ c : ℕ, ∀ m : LTree E, m.labels.Perm (List.range 3) →
      wdeg w (t.substAt p s m) = c + wdeg w m := by
  obtain ⟨c, hc⟩ := wdeg_replaceAt w t p h.exists_node
  refine ⟨c + (wdeg w ((t.subtreeAt p).winIns s 0) + wdeg w ((t.subtreeAt p).winIns s 1)
    + wdeg w ((t.subtreeAt p).winIns s 2)), fun m hm => ?_⟩
  rw [substAt, hc, wdeg_plug, (hm.map _).sum_eq]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring

end LTree

namespace ShuffleBar

open LTree Graded Module

variable {E : Type v}

/-- The weight of a bar tree: that of its monomial, the flags forgotten. -/
def wdegB (w : E → ℕ) (x : BarTree E) : ℕ := wdeg (w ∘ Prod.fst) x

/-- **Merging does not change the weight.** -/
lemma wdegB_mergeK (w : E → ℕ) : ∀ (x : BarTree E) (k : ℕ ×ₗ ℕ), wdegB w (mergeK x k) = wdegB w x
  | leaf _, _ => rfl
  | node d a b, k => by
    unfold mergeK
    split_ifs
    · rfl
    · have ha := wdegB_mergeK w a k
      have hb := wdegB_mergeK w b k
      simp only [wdegB, wdeg_node] at ha hb ⊢
      rw [ha, hb]

/-- **Substituting at an uncut edge** adds the weight of the monomial to that of the context. -/
lemma wdegB_substBar (w : E → ℕ) {x : BarTree E} {p : List Bool} {s : Bool} (h : x.IsEdge p s) :
    ∃ c : ℕ, ∀ σ : LTree E, σ.labels.Perm (List.range 3) →
      wdegB w (substBar x p s σ) = c + wdeg w σ := by
  obtain ⟨c, hc⟩ := wdeg_substAt (w ∘ Prod.fst) h
  refine ⟨c, fun σ hσ => ?_⟩
  rw [wdegB, substBar, hc _ (by rwa [labels_liftW])]
  congr 1
  rw [← wdeg_mapDec Prod.fst w, liftW_mapDec]

section Bar

variable [Fintype E] [DecidableEq E] (K : Type u) [Field K] (w : E → ℕ)

omit [Fintype E] [DecidableEq E] in
/-- **The differential preserves the weight.** -/
lemma d_wproj (N : ℕ) (v : BarTree E →₀ K) :
    d K (wproj K (wdegB w) N v) = wproj K (wdegB w) N (d K v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' => simp only [map_add, hv, hv']
  | single x c =>
    rw [wproj_single, d_single, dTree, Finset.smul_sum]
    simp only [map_sum, map_smul, wproj_single, wdegB_mergeK]
    split_ifs with hx
    · rw [d_single, dTree, Finset.smul_sum]
    · simp

variable {K}

omit [Fintype E] [DecidableEq E] in
lemma wproj_mem_supported {S : Set (BarTree E)} {v : BarTree E →₀ K}
    (hv : v ∈ Finsupp.supported K K S) (N : ℕ) :
    wproj K (wdegB w) N v ∈ Finsupp.supported K K S := by
  rw [Finsupp.mem_supported] at hv ⊢
  intro x hx
  rw [Finset.mem_coe, Finsupp.mem_support_iff, wproj_apply] at hx
  split_ifs at hx
  · exact hv (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hx))
  · exact absurd rfl hx

omit [Fintype E] [DecidableEq E] in
lemma wproj_mem_C {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n s) (N : ℕ) :
    wproj K (wdegB w) N v ∈ C K n s :=
  wproj_mem_supported w hv N

/-- **The weights on the bar construction of arity `n` and degree `s` are bounded.** -/
lemma exists_isBelow_C (n s : ℕ) :
    ∃ B, ∀ v ∈ C K n s, IsBelow (K := K) (W := wdegB w) B v := by
  refine ⟨(finite_adm (E := E) n s).toFinset.sup (wdegB w), fun v hv k hk => ?_⟩
  ext x
  rw [wproj_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with hx
  · by_contra h0
    have hxA : Adm n s x := hv (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 h0))
    have := Finset.le_sup (f := wdegB w) ((finite_adm (E := E) n s).mem_toFinset.2 hxA)
    omega
  · rfl

lemma substRel_add (x : BarTree E) (p : List Bool) (s : Bool) (r r' : Mono E 3 → K) :
    substRel K x p s (r + r') = substRel K x p s r + substRel K x p s r' := by
  simp only [substRel, Pi.add_apply, add_smul, Finset.sum_add_distrib]

lemma substRel_smul (x : BarTree E) (p : List Bool) (s : Bool) (c : K) (r : Mono E 3 → K) :
    substRel K x p s (c • r) = c • substRel K x p s r := by
  simp only [substRel, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma substRel_zero (x : BarTree E) (p : List Bool) (s : Bool) :
    substRel K x p s (0 : Mono E 3 → K) = 0 := by
  simp [substRel]

/-- **Admissibility is a property of the context**: substituting a monomial of arity three at an
uncut edge does not change the labels or the cut edges. -/
lemma adm_substBar_iff {x : BarTree E} (hx : Valid x) {p : List Bool} {s : Bool}
    (h : IsUncut x p s) (σ : Mono E 3) {n s' : ℕ} :
    Adm n s' (substBar x p s σ.1) ↔ Adm n s' x := by
  obtain ⟨-, hσ, hσn⟩ := mono_shape σ
  have hv := hx.substBar h σ
  have hl := perm_labels_substBar hx.shuffle hx.nodup h hσ
  have hc := cutKeys_substBar hx.shuffle hx.nodup h hσ hσn
  constructor
  · rintro ⟨-, hp, hk⟩
    exact ⟨hx, hl.symm.trans hp, by rwa [hc] at hk⟩
  · rintro ⟨-, hp, hk⟩
    exact ⟨hv, hl.trans hp, by rwa [hc]⟩

variable (K) in
/-- The substituted relators at the admissible bar trees of arity `n` and degree `s`. -/
noncomputable def Jgen (R : Submodule K (Mono E 3 → K)) (n s : ℕ) :
    Submodule K (BarTree E →₀ K) :=
  Submodule.span K {v | ∃ x p s' r, Adm n s x ∧ IsUncut x p s' ∧ r ∈ R ∧ v = substRel K x p s' r}

open Classical in
/-- The restriction to a set of bar trees. -/
noncomputable def restr (S : Set (BarTree E)) : (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) where
  toFun v := v.filter (· ∈ S)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

open Classical in
omit [Fintype E] [DecidableEq E] in
lemma restr_single (S : Set (BarTree E)) (x : BarTree E) (c : K) :
    restr S (Finsupp.single x c) = if x ∈ S then Finsupp.single x c else 0 := by
  classical
  ext y
  simp only [restr, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.filter_apply]
  by_cases hxy : x = y
  · subst hxy
    split_ifs <;> simp_all
  · split_ifs <;> simp_all

open Classical in
omit [Fintype E] [DecidableEq E] in
lemma restr_of_supported {S : Set (BarTree E)} {v : BarTree E →₀ K}
    (hv : v ∈ Finsupp.supported K K S) : restr S v = v := by
  classical
  ext y
  simp only [restr, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.filter_apply]
  split_ifs with hy
  · rfl
  · by_contra h0
    exact hy (hv (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 (Ne.symm h0))))

open Classical in
/-- **The relator subcomplex in arity `n` and degree `s`** is spanned by the relators substituted
at the admissible bar trees of that arity and degree. -/
lemma J_inf_C_le (R : Submodule K (Mono E 3 → K)) (n s : ℕ) : J K R ⊓ C K n s ≤ Jgen K R n s := by
  rintro y ⟨hyJ, hyC⟩
  rw [← restr_of_supported hyC]
  have : (J K R).map (restr {x | Adm n s x}) ≤ Jgen K R n s := by
    rw [J, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨x, p, s', r, hx, h, hr, rfl⟩, rfl⟩
    simp only [substRel, map_sum, map_smul, restr_single, Set.mem_setOf_eq,
      adm_substBar_iff hx h]
    split_ifs with hA
    · exact Submodule.subset_span ⟨x, p, s', r, hA, h, hr, by simp [substRel]⟩
    · simp
  exact this (Submodule.mem_map_of_mem hyJ)

end Bar

section Top

variable [Fintype E] [DecidableEq E] {K : Type u} [Field K] (w : E → ℕ)

/-- **The component of weight `N` of a relator.** -/
def wprojM (N : ℕ) (r : Mono E 3 → K) : Mono E 3 → K :=
  fun σ => if wdeg w σ.1 = N then r σ else 0

/-- The relator `r` has no component of weight above `N`. -/
def IsBelowM (N : ℕ) (r : Mono E 3 → K) : Prop := ∀ σ : Mono E 3, N < wdeg w σ.1 → r σ = 0

/-- **The components of a substituted relator** are the substituted components of the relator,
shifted by the weight of the context. -/
lemma substRel_wproj {x : BarTree E} {p : List Bool} {s : Bool} (h : IsUncut x p s) :
    ∃ c : ℕ, ∀ (M : ℕ) (r : Mono E 3 → K),
      wproj K (wdegB w) (c + M) (substRel K x p s r) = substRel K x p s (wprojM w M r) ∧
      (IsBelowM w M r → IsBelow (K := K) (W := wdegB w) (c + M) (substRel K x p s r)) := by
  obtain ⟨c, hc⟩ := wdegB_substBar w h.1
  have hc' : ∀ σ : Mono E 3, wdegB w (substBar x p s σ.1) = c + wdeg w σ.1 :=
    fun σ => hc σ.1 (mono_shape σ).2.1
  refine ⟨c, fun M r => ⟨?_, fun hr k hk => ?_⟩⟩
  · simp only [substRel, map_sum, map_smul, wproj_single, hc', wprojM]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hσ : wdeg w σ.1 = M
    · simp [hσ]
    · simp [hσ]
  · simp only [substRel, map_sum, map_smul, wproj_single, hc']
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_cases hσ : c + wdeg w σ.1 = k
    · rw [hr σ (by omega), zero_smul]
    · simp [hσ]

lemma substRel_mem_C {x : BarTree E} {p : List Bool} {s : Bool} {n s' : ℕ} (hA : Adm n s' x)
    (h : IsUncut x p s) (r : Mono E 3 → K) : substRel K x p s r ∈ C K n s' := by
  refine Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _
    (Finsupp.single_mem_supported K _ ?_)
  exact (adm_substBar_iff hA.1 h σ).2 hA

end Top

section Main

variable [Fintype E] [DecidableEq E] {K : Type u} [Field K] (w : E → ℕ)
  {ι : Type*} (sr : ι → Mono E 3 → K) (N : ι → ℕ)

/-- **The relators of the associated graded, substituted, are top components of substituted
relators**: if the `sr i` lie in `R` with no component above `N i`, the relator subcomplex of the
span of their components of weight `N i` lies in the associated graded of that of `R`. -/
theorem Jgen_le_grW (hs : ∀ i, IsBelowM w (N i) (sr i)) {R : Submodule K (Mono E 3 → K)}
    (hsR : ∀ i, sr i ∈ R) (n s : ℕ) :
    Jgen K (Submodule.span K (Set.range fun i => wprojM w (N i) (sr i))) n s ≤
      grW K (wdegB w) (J K R ⊓ C K n s) := by
  rw [Jgen, Submodule.span_le]
  rintro _ ⟨x, p, s', r, hA, h, hr, rfl⟩
  rw [SetLike.mem_coe]
  obtain ⟨c, hc⟩ := substRel_wproj (K := K) w h
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨i, rfl⟩ := hr
    rw [← (hc (N i) (sr i)).1]
    exact wproj_mem_grW ⟨Submodule.subset_span ⟨x, p, s', sr i, hA.1, h, hsR i, rfl⟩,
      substRel_mem_C hA h _⟩ ((hc (N i) (sr i)).2 (hs i))
  | zero => rw [substRel_zero]; exact zero_mem _
  | add r r' _ _ h1 h2 => rw [substRel_add]; exact add_mem h1 h2
  | smul a r _ h1 => rw [substRel_smul]; exact Submodule.smul_mem _ a h1

lemma finiteDimensional_C (n s : ℕ) : FiniteDimensional K (C (E := E) K n s) :=
  finiteDimensional_supported K (finite_adm n s)

omit [Fintype E] [DecidableEq E] in
lemma grW_le_C {V : Submodule K (BarTree E →₀ K)} {n s : ℕ} (hV : V ≤ C K n s) :
    grW K (wdegB w) V ≤ C K n s :=
  grW_le fun _ _ hv _ => wproj_mem_C w (hV hv) _

lemma finrank_grW_of_le_C {V : Submodule K (BarTree E →₀ K)} {n s : ℕ} (hV : V ≤ C K n s) :
    finrank K (grW K (wdegB w) V) = finrank K V := by
  haveI := finiteDimensional_C (K := K) (E := E) n s
  haveI : FiniteDimensional K V := Submodule.finiteDimensional_of_le hV
  obtain ⟨B, hB⟩ := exists_isBelow_C (K := K) w n s
  exact finrank_grW V fun v hv => hB v (hV hv)

/-- **The relator subcomplex of the associated graded is the associated graded of the relator
subcomplex**, in arity `n` and degree `s`, when they have the same dimension. -/
theorem J_inf_C_eq_grW (hs : ∀ i, IsBelowM w (N i) (sr i)) {R R₀ : Submodule K (Mono E 3 → K)}
    (hsR : ∀ i, sr i ∈ R) (hR₀ : R₀ = Submodule.span K (Set.range fun i => wprojM w (N i) (sr i)))
    (n s : ℕ) (hdim : finrank K (J K R ⊓ C K n s : Submodule K _) =
      finrank K (J K R₀ ⊓ C K n s : Submodule K _)) :
    J K R₀ ⊓ C K n s = grW K (wdegB w) (J K R ⊓ C K n s) := by
  haveI := finiteDimensional_C (K := K) (E := E) n s
  have hle : J K R₀ ⊓ C K n s ≤ grW K (wdegB w) (J K R ⊓ C K n s) :=
    (J_inf_C_le R₀ n s).trans (hR₀ ▸ Jgen_le_grW w sr N hs hsR n s)
  haveI : FiniteDimensional K (grW K (wdegB w) (J K R ⊓ C K n s)) :=
    Submodule.finiteDimensional_of_le (grW_le_C w inf_le_right)
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_grW_of_le_C w inf_le_right, hdim]

/-- **The associated graded of the Koszul dual cooperad lies in that of the associated graded.**
-/
theorem grW_KD_le {R R₀ : Submodule K (Mono E 3 → K)} {n : ℕ} (hn : 2 ≤ n)
    (hJ : J K R₀ ⊓ C K n (n - 2) = grW K (wdegB w) (J K R ⊓ C K n (n - 2))) :
    grW K (wdegB w) (KD K R n) ≤ KD K R₀ n := by
  refine grW_le fun M v hv hM => ?_
  rw [KD, Submodule.mem_inf] at hv ⊢
  refine ⟨wproj_mem_C w hv.1 M, ?_⟩
  rw [Submodule.mem_comap, d_wproj]
  have hdC : d K v ∈ C K n (n - 2) :=
    d_mem_C K (by rw [show n - 2 + 1 = n - 1 by omega]; exact hv.1)
  have hbelow : IsBelow (K := K) (W := wdegB w) M (d K v) := fun k hk => by
    rw [← d_wproj, hM k hk, map_zero]
  have := wproj_mem_grW (K := K) (W := wdegB w) (V := J K R ⊓ C K n (n - 2))
    ⟨Submodule.mem_comap.1 hv.2, hdC⟩ hbelow
  rw [← hJ] at this
  exact this.1

/-- **The Koszul dual cooperad of the associated graded is the associated graded of the Koszul
dual cooperad** (for the filtration by weight), when the relators `R₀` are spanned by the top
components of relators of `R` and the relator subcomplexes and the Koszul dual cooperads of `R`
and `R₀` have the same dimensions. -/
theorem KD_eq_grW (hs : ∀ i, IsBelowM w (N i) (sr i)) {R R₀ : Submodule K (Mono E 3 → K)}
    (hsR : ∀ i, sr i ∈ R) (hR₀ : R₀ = Submodule.span K (Set.range fun i => wprojM w (N i) (sr i)))
    {n : ℕ} (hn : 2 ≤ n) (hJ : finrank K (J K R ⊓ C K n (n - 2) : Submodule K _) =
      finrank K (J K R₀ ⊓ C K n (n - 2) : Submodule K _))
    (hKD : finrank K (KD K R n) = finrank K (KD K R₀ n)) :
    KD K R₀ n = grW K (wdegB w) (KD K R n) := by
  haveI := finiteDimensional_C (K := K) (E := E) n (n - 1)
  have hle := grW_KD_le w hn (J_inf_C_eq_grW w sr N hs hsR hR₀ n (n - 2) hJ)
  haveI : FiniteDimensional K (KD K R₀ n) := Submodule.finiteDimensional_of_le inf_le_left
  have hKDC : KD K R n ≤ C K n (n - 1) := inf_le_left
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_grW_of_le_C w hKDC, hKD]

end Main

section Groebner

variable [Fintype E] [DecidableEq E] {K : Type u} [Field K] (rk : E → ℕ) {L : Set (LTree E)}
  {R : Submodule K (Mono E 3 → K)}

/-- **The dimension of the relator subcomplex** from a quadratic Gröbner basis: the bar trees of
arity `n` and degree `s` which are not normal. -/
theorem finrank_J_inf_C_add (hG : IsGroebner K rk L R) (n s : ℕ) :
    finrank K (J K R ⊓ C K n s : Submodule K _) + (Nrm L n s).ncard =
      finrank K (C (E := E) K n s) := by
  haveI := finiteDimensional_C (K := K) (E := E) n s
  have h := finrank_eq_map_add K (ΦL K hG) (C K n s)
  have hmap : (C K n s).map (ΦL K hG) = Finsupp.supported K K (Nrm L n s) := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (normalized_eq K rk hG hv).1
    · intro v hv
      exact ⟨v, C_of_nrm K hv, ΦL_normal K rk hG hv⟩
  have hker : C K n s ⊓ LinearMap.ker (ΦL K hG) = J K R ⊓ C K n s := by
    ext v
    simp only [Submodule.mem_inf, LinearMap.mem_ker]
    exact ⟨fun ⟨hv, h0⟩ => ⟨(mem_J_iff K rk hG hv).2 h0, hv⟩,
      fun ⟨hJ, hv⟩ => ⟨hv, (mem_J_iff K rk hG hv).1 hJ⟩⟩
  rw [hmap, hker, finrank_supported K (finite_nrm L n s)] at h
  omega

/-- **For two quadratic Gröbner bases with the same leading monomials, the Koszul dual cooperad
of the second is the associated graded of that of the first**, when the second is spanned by the
top components of relators of the first. -/
theorem KD_eq_grW_of_isGroebner (w : E → ℕ) {ι : Type*} (sr : ι → Mono E 3 → K) (N : ι → ℕ)
    (hs : ∀ i, IsBelowM w (N i) (sr i)) {R₀ : Submodule K (Mono E 3 → K)}
    (hG : IsGroebner K rk L R) (hG₀ : IsGroebner K rk L R₀) (hsR : ∀ i, sr i ∈ R)
    (hR₀ : R₀ = Submodule.span K (Set.range fun i => wprojM w (N i) (sr i))) {n : ℕ}
    (hn : 2 ≤ n) : KD K R₀ n = grW K (wdegB w) (KD K R n) := by
  refine KD_eq_grW w sr N hs hsR hR₀ hn ?_ (finrank_KD_eq K rk hG hG₀ n)
  have h1 := finrank_J_inf_C_add rk hG n (n - 2)
  have h2 := finrank_J_inf_C_add rk hG₀ n (n - 2)
  omega

end Groebner

end ShuffleBar

end Operad
