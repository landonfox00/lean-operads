/-
# The associated graded of the Koszul dual operad

A weight `W` on a finite set grades the functions on it (`Graded.projF`, the component of weight
`N`), and the **associated graded** of a space of functions is the span of the top components of
its elements (`Graded.grF`), of the same dimension (`Graded.finrank_grF`). For a diagonal pairing,
**the orthogonal of the associated graded is the associated graded of the orthogonal for the
reversed weight** (`Graded.orthogonal_grF`): the top components of a space pair with the bottom
components of its orthogonal.

For shuffle operads, a weight `w` on the generators weighs the monomials. The Koszul dual cooperad
on the monomials (`ShuffleBar.KDmono`) is the image of the Koszul dual cooperad under the
identification of the fully cut bar trees with the monomials, which keeps the weight
(`ShuffleBar.toMono_wproj`): so if **the Koszul dual cooperad of `R₀` is the associated graded of
that of `R`** (`ShuffleBar.KD_eq_grW`), the same holds on the monomials
(`ShuffleBar.KDmono_eq_grF`), and taking orthogonals (`ShuffleBar.idealOf_dualRel_eq_orthogonal`):

* **the ideal of the Koszul dual relators of `R₀` is the associated graded of that of `R`**, for
  the reversed weight (`ShuffleBar.idealOf_dualRel_eq_grF`): the Koszul dual operad of `R₀` is the
  associated graded of that of `R` for the dual filtration, a PBW property;
* in arity three, where the ideal is the space of relators (`ShuffleBar.idealOf_three`), **the
  Koszul dual relators of `R₀` are the leading forms of those of `R`**
  (`ShuffleBar.dualRel_eq_grF`).

Both hold for two quadratic Gröbner bases with the same leading monomials, the second spanned by
top components of the first (`ShuffleBar.idealOf_dualRel_eq_grF_of_isGroebner`).
-/
import Operad.ShuffleKoszulOperad

universe u v

namespace Operad

namespace Graded

open Module

section Fun

variable {α : Type*} [Fintype α] (K : Type*) [Field K] (W : α → ℕ)

/-- **The component of weight `N` of a function.** -/
def projF (N : ℕ) : (α → K) →ₗ[K] (α → K) where
  toFun x a := if W a = N then x a else 0
  map_add' x y := by
    funext a
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

/-- `x` has no component of weight above `N`. -/
def IsBelowF (N : ℕ) (x : α → K) : Prop := ∀ a, N < W a → x a = 0

/-- **The associated graded** of a space of functions: the span of the top components of its
elements, as for the finitely supported functions. -/
noncomputable def grF (U : Submodule K (α → K)) : Submodule K (α → K) :=
  (grW K W (U.map (Finsupp.linearEquivFunOnFinite K K α).symm.toLinearMap)).map
    (Finsupp.linearEquivFunOnFinite K K α).toLinearMap

/-- The reversed weight. -/
def revW : α → ℕ := fun a => Finset.univ.sup W - W a

variable {K W}

omit [Fintype α] in
lemma projF_apply (N : ℕ) (x : α → K) (a : α) :
    projF K W N x a = if W a = N then x a else 0 := rfl

lemma linearEquivFunOnFinite_wproj (N : ℕ) (v : α →₀ K) :
    Finsupp.linearEquivFunOnFinite K K α (wproj K W N v) =
      projF K W N (Finsupp.linearEquivFunOnFinite K K α v) := by
  funext a
  simp [wproj_apply, projF_apply]

lemma isBelow_iff_isBelowF {N : ℕ} {v : α →₀ K} :
    IsBelow (K := K) (W := W) N v ↔ IsBelowF K W N (Finsupp.linearEquivFunOnFinite K K α v) := by
  constructor
  · intro h a ha
    have := congrArg (fun f => f a) (h (W a) ha)
    simpa [wproj_apply] using this
  · intro h k hk
    ext a
    rw [wproj_apply]
    split_ifs with ha
    · simpa using h a (ha ▸ hk)
    · rfl

/-- **The top components lie in the associated graded.** -/
lemma projF_mem_grF {U : Submodule K (α → K)} {N : ℕ} {x : α → K} (hx : x ∈ U)
    (hN : IsBelowF K W N x) : projF K W N x ∈ grF K W U := by
  set e := Finsupp.linearEquivFunOnFinite K K α
  refine ⟨wproj K W N (e.symm x), wproj_mem_grW ⟨x, hx, rfl⟩ ?_, ?_⟩
  · rw [isBelow_iff_isBelowF, LinearEquiv.apply_symm_apply]
    exact hN
  · show e (wproj K W N (e.symm x)) = _
    rw [linearEquivFunOnFinite_wproj, LinearEquiv.apply_symm_apply]

/-- **The associated graded is spanned by the top components.** -/
lemma grF_le {U P : Submodule K (α → K)}
    (h : ∀ N, ∀ x ∈ U, IsBelowF K W N x → projF K W N x ∈ P) : grF K W U ≤ P := by
  set e := Finsupp.linearEquivFunOnFinite K K α
  refine Submodule.map_le_iff_le_comap.2 (grW_le fun N v hv hN => ?_)
  obtain ⟨x, hx, rfl⟩ := hv
  rw [Submodule.mem_comap]
  show e (wproj K W N (e.symm x)) ∈ P
  rw [linearEquivFunOnFinite_wproj, LinearEquiv.apply_symm_apply]
  rw [isBelow_iff_isBelowF] at hN
  change IsBelowF K W N (e (e.symm x)) at hN
  rw [LinearEquiv.apply_symm_apply] at hN
  exact h N x hx hN

lemma le_sup_univ (a : α) : W a ≤ Finset.univ.sup W := Finset.le_sup (Finset.mem_univ a)

/-- **The associated graded has the dimension of the space.** -/
theorem finrank_grF (U : Submodule K (α → K)) : finrank K (grF K W U) = finrank K U := by
  set e := Finsupp.linearEquivFunOnFinite K K α
  rw [grF, LinearEquiv.finrank_map_eq]
  rw [finrank_grW (U.map e.symm.toLinearMap) (B := Finset.univ.sup W) fun v _ k hk => ?_]
  · exact LinearEquiv.finrank_map_eq e.symm U
  · ext a
    rw [wproj_apply]
    split_ifs with ha
    · have := le_sup_univ (W := W) a
      omega
    · rfl

/-- **The orthogonal of the associated graded is the associated graded of the orthogonal**, for a
diagonal pairing and the reversed weight. -/
theorem orthogonal_grF {c : α → K} (hc : ∀ a, c a ≠ 0) (U : Submodule K (α → K)) :
    (diagForm c).orthogonal (grF K W U) = grF K (revW W) ((diagForm c).orthogonal U) := by
  set B := Finset.univ.sup W with hB
  have hle : grF K (revW W) ((diagForm c).orthogonal U) ≤ (diagForm c).orthogonal (grF K W U) := by
    refine grF_le fun N' x' hx' hN' => ?_
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    revert z
    show grF K W U ≤ LinearMap.ker (LinearMap.flip (diagForm c) (projF K (revW W) N' x'))
    refine grF_le fun M x hx hM => ?_
    rw [LinearMap.mem_ker, LinearMap.flip_apply, diagForm_apply]
    have hxx' : ∑ a, c a * x a * x' a = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.1 hx') x hx
    have hterm : ∀ a, c a * projF K W M x a * projF K (revW W) N' x' a =
        if M + N' = B then c a * x a * x' a else 0 := by
      intro a
      have haB := le_sup_univ (W := W) a
      simp only [projF_apply, revW]
      by_cases h1 : W a = M
      · by_cases h2 : B - W a = N'
        · rw [if_pos h1, if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, mul_zero]
          split_ifs with h3
          · exact absurd (by omega) h2
          · rfl
      · rw [if_neg h1, mul_zero, zero_mul]
        split_ifs with h3
        · rcases Nat.lt_or_gt_of_ne h1 with h4 | h4
          · rw [hN' a (by simp only [revW]; omega), mul_zero]
          · rw [hM a h4, mul_zero, zero_mul]
        · rfl
    rw [Finset.sum_congr rfl fun a _ => hterm a]
    split_ifs
    · exact hxx'
    · simp
  have hnd := diagForm_nondegenerate hc
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_grF, LinearMap.BilinForm.finrank_orthogonal hnd,
    LinearMap.BilinForm.finrank_orthogonal hnd, finrank_grF]

end Fun

end Graded

namespace ShuffleBar

open LTree Graded Module

variable {E : Type v} [Fintype E] [DecidableEq E] {K : Type u} [Field K]

/-! ## The weight of the monomials, through the fully cut bar trees -/

/-- **The weight of a monomial of arity `n`.** -/
def wMono (w : E → ℕ) (n : ℕ) : Mono E n → ℕ := fun m => wdeg w m.1

omit [Fintype E] [DecidableEq E] in
lemma wdegB_fullBar (w : E → ℕ) (m : LTree E) : wdegB w (fullBar m) = wdeg w m := by
  rw [wdegB, ← wdeg_mapDec Prod.fst w, full_fullBar]

lemma toMono_wproj (w : E → ℕ) (n N : ℕ) (v : BarTree E →₀ K) :
    toMono K n (wproj K (wdegB w) N v) = projF K (wMono w n) N (toMono K n v) := by
  funext m
  show (tauS m.1 : K) * wproj K (wdegB w) N v (fullBar m.1) = _
  rw [wproj_apply, wdegB_fullBar, projF_apply]
  show _ = if wdeg w m.1 = N then (tauS m.1 : K) * v (fullBar m.1) else 0
  split_ifs <;> simp

lemma isBelowF_toMono (w : E → ℕ) {n N : ℕ} {v : BarTree E →₀ K}
    (hv : IsBelow (K := K) (W := wdegB w) N v) : IsBelowF K (wMono w n) N (toMono K n v) := by
  intro m hm
  have h := congrArg (fun f => f (fullBar m.1)) (hv (wMono w n m) hm)
  simp only [wproj_apply, wdegB_fullBar, wMono, if_true, Finsupp.coe_zero, Pi.zero_apply] at h
  show (tauS m.1 : K) * v (fullBar m.1) = 0
  rw [h, mul_zero]

lemma isBelow_of_isBelowF_toMono (w : E → ℕ) {n N : ℕ} {v : BarTree E →₀ K}
    (hvC : v ∈ C K n (n - 1)) (hv : IsBelowF K (wMono w n) N (toMono K n v)) :
    IsBelow (K := K) (W := wdegB w) N v := by
  intro k hk
  ext b
  rw [wproj_apply]
  split_ifs with hb
  · by_contra h0
    have hA : Adm n (n - 1) b := hvC (Finsupp.mem_support_iff.2 h0)
    have hm := full_mem_monomials hA
    have hb' := eq_fullBar_of_adm hA
    have h1 := hv ⟨_, hm⟩ (by
      show N < wdeg w (b.mapDec Prod.fst)
      rw [← wdegB_fullBar, ← hb']
      omega)
    change (tauS (b.mapDec Prod.fst) : K) * v (fullBar (b.mapDec Prod.fst)) = 0 at h1
    rw [← hb'] at h1
    have h2 := congrArg (fun z => (tauS (b.mapDec Prod.fst) : K) * z) h1
    simp only [mul_zero, ← mul_assoc, tauS_cast_mul_self, one_mul] at h2
    exact h0 h2
  · rfl

/-- **The fully cut bar trees carry the associated graded to the associated graded.** -/
lemma map_toMono_grW (w : E → ℕ) {n : ℕ} {V : Submodule K (BarTree E →₀ K)}
    (hV : V ≤ C K n (n - 1)) :
    (grW K (wdegB w) V).map (toMono K n) = grF K (wMono w n) (V.map (toMono K n)) := by
  apply le_antisymm
  · refine Submodule.map_le_iff_le_comap.2 (grW_le fun N v hv hN => ?_)
    rw [Submodule.mem_comap, toMono_wproj]
    exact projF_mem_grF ⟨v, hv, rfl⟩ (isBelowF_toMono w hN)
  · refine grF_le fun N x hx hN => ?_
    obtain ⟨v, hv, rfl⟩ := hx
    rw [← toMono_wproj]
    exact Submodule.mem_map_of_mem
      (wproj_mem_grW hv (isBelow_of_isBelowF_toMono w (hV hv) hN))

/-- **The Koszul dual cooperad on the monomials is the image of the Koszul dual cooperad.** -/
lemma KDmono_eq_map (R : Submodule K (Mono E 3 → K)) {n : ℕ} (hn : 2 ≤ n) :
    KDmono K R n = (KD K R n).map (toMono K n) := by
  ext x
  constructor
  · intro hx
    exact ⟨((KD_equiv_KDmono R hn).symm ⟨x, hx⟩).1, ((KD_equiv_KDmono R hn).symm ⟨x, hx⟩).2,
      congrArg Subtype.val ((KD_equiv_KDmono R hn).apply_symm_apply ⟨x, hx⟩)⟩
  · rintro ⟨v, hv, rfl⟩
    exact ((KD_equiv_KDmono R hn) ⟨v, hv⟩).2

/-- **If the Koszul dual cooperad of `R₀` is the associated graded of that of `R`, so are they on
the monomials.** -/
theorem KDmono_eq_grF (w : E → ℕ) {R R₀ : Submodule K (Mono E 3 → K)} {n : ℕ} (hn : 2 ≤ n)
    (h : KD K R₀ n = grW K (wdegB w) (KD K R n)) :
    KDmono K R₀ n = grF K (wMono w n) (KDmono K R n) := by
  rw [KDmono_eq_map R₀ hn, h,
    map_toMono_grW w (show KD K R n ≤ C K n (n - 1) from inf_le_left), ← KDmono_eq_map R hn]

/-- **The ideal of the Koszul dual relators is the orthogonal of the Koszul dual cooperad.** -/
theorem idealOf_dualRel_eq_orthogonal (R : Submodule K (Mono E 3 → K)) (n : ℕ) :
    idealOf K (dualRel K R) n =
      (diagForm fun _ : Mono E n => (1 : K)).orthogonal (KDmono K R n) := by
  rw [KDmono_eq_orthogonal, LinearMap.BilinForm.orthogonal_orthogonal
    (diagForm_nondegenerate fun _ => one_ne_zero) (diagForm_isRefl _)]

/-- **PBW for the Koszul dual operad**: if the Koszul dual cooperad of `R₀` is the associated
graded of that of `R`, the ideal of the Koszul dual relators of `R₀` is the associated graded of
that of `R`, for the reversed weight: the Koszul dual operad of `R₀` is the associated graded of
that of `R` for the dual filtration. -/
theorem idealOf_dualRel_eq_grF (w : E → ℕ) {R R₀ : Submodule K (Mono E 3 → K)} {n : ℕ}
    (hn : 2 ≤ n) (h : KD K R₀ n = grW K (wdegB w) (KD K R n)) :
    idealOf K (dualRel K R₀) n = grF K (revW (wMono w n)) (idealOf K (dualRel K R) n) := by
  rw [idealOf_dualRel_eq_orthogonal, KDmono_eq_grF w hn h,
    orthogonal_grF (fun _ => one_ne_zero), ← idealOf_dualRel_eq_orthogonal]

/-! ## Arity three -/

omit [Fintype E] [DecidableEq E] in
lemma three_le_arity_of_isEdgeRoot : ∀ {u : LTree E} {s : Bool}, u.IsEdgeRoot s → 3 ≤ u.arity
  | node _ (node _ a b) c, false, _ => by
    have := arity_pos a
    have := arity_pos b
    have := arity_pos c
    simp only [arity]
    omega
  | node _ c (node _ a b), true, _ => by
    have := arity_pos a
    have := arity_pos b
    have := arity_pos c
    simp only [arity]
    omega

omit [Fintype E] [DecidableEq E] in
lemma plug_leaf : ∀ t : LTree E, t.plug leaf = t
  | leaf _ => rfl
  | node e l r => by rw [plug, plug_leaf l, plug_leaf r]

/-- **Substituting at the edge of a monomial of arity three** gives the substituted monomial. -/
lemma substAt_of_mem_monomials_three {t : LTree E} (ht : t ∈ monomials 3) {p : List Bool}
    {s : Bool} (he : t.IsEdge p s) {σ : LTree E} (hσ : σ.labels.Perm (List.range 3)) :
    t.substAt p s σ = σ := by
  obtain ⟨hts, htl⟩ := (mem_monomials 3 t).1 ht
  have key : ∀ ins : ℕ → LTree E, (∀ i < 3, ins i = leaf i) → σ.plug ins = σ := fun ins hins => by
    conv_rhs => rw [← plug_leaf σ]
    exact plug_congr fun a ha => hins a (lt_three_of_perm hσ a ha)
  have h3 : t.arity = 3 := arity_of_mem_monomials ht
  have hp : p = [] := by
    rcases p with _ | ⟨b, q⟩
    · rfl
    · exfalso
      have h1 := three_le_arity_of_isEdgeRoot he
      cases t with
      | leaf => simp [arity] at h3
      | node e l r =>
        have h2 := arity_subtreeAt_cons_lt e l r b q
        omega
  subst hp
  obtain ⟨e, f, rfl | rfl | rfl⟩ := mono3_cases hts htl <;> cases s <;>
    first
    | (simp [IsEdge, IsEdgeRoot] at he; done)
    | (simp only [substAt, replaceAt_nil, subtreeAt_nil]
       refine key _ fun i hi => ?_
       interval_cases i <;> rfl)

/-- **In arity three the ideal is the space of relators.** -/
theorem idealOf_three (R' : Submodule K (Mono E 3 → K)) : idealOf K R' 3 = R' := by
  apply le_antisymm
  · rw [idealOf, Submodule.span_le]
    rintro _ ⟨t, p, s, r, hr, he, rfl⟩
    have : substVec K 3 t.1 p s r = r := by
      funext σ'
      simp only [substVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecOf]
      rw [Finset.sum_eq_single σ']
      · rw [substAt_of_mem_monomials_three t.2 he (mono_shape σ').2.1, if_pos rfl, mul_one]
      · intro σ _ hσ
        rw [substAt_of_mem_monomials_three t.2 he (mono_shape σ).2.1,
          if_neg fun h => hσ (Subtype.ext h).symm, mul_zero]
      · simp
    rw [SetLike.mem_coe, this]
    exact hr
  · intro r hr
    by_cases hne : Nonempty (Mono E 3)
    · obtain ⟨t⟩ := hne
      obtain ⟨-, -, e, l, r', ht⟩ := mono_shape t
      have hs := (mem_monomials 3 t.1).1 t.2
      have he : t.1.IsEdge [] (side3 t.1) := by
        obtain ⟨e', f', h | h | h⟩ := mono3_cases hs.1 hs.2 <;> rw [h] <;> trivial
      have : substVec K 3 t.1 [] (side3 t.1) r = r := by
        funext σ'
        simp only [substVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecOf]
        rw [Finset.sum_eq_single σ']
        · rw [substAt_of_mem_monomials_three t.2 he (mono_shape σ').2.1, if_pos rfl, mul_one]
        · intro σ _ hσ
          rw [substAt_of_mem_monomials_three t.2 he (mono_shape σ).2.1,
            if_neg fun h => hσ (Subtype.ext h).symm, mul_zero]
        · simp
      rw [← this]
      exact substVec_mem_idealOf K R' t he hr
    · have : r = 0 := funext fun σ => absurd ⟨σ⟩ hne
      rw [this]
      exact zero_mem _

/-- **The Koszul dual relators of `R₀` are the leading forms of those of `R`**, for the reversed
weight, when the Koszul dual cooperad of `R₀` is the associated graded of that of `R` in arity
three. -/
theorem dualRel_eq_grF (w : E → ℕ) {R R₀ : Submodule K (Mono E 3 → K)}
    (h : KD K R₀ 3 = grW K (wdegB w) (KD K R 3)) :
    dualRel K R₀ = grF K (revW (wMono w 3)) (dualRel K R) := by
  have := idealOf_dualRel_eq_grF w (by norm_num) h
  rwa [idealOf_three, idealOf_three] at this

/-! ## Quadratic Gröbner bases -/

/-- **PBW for the Koszul dual operad of two quadratic Gröbner bases with the same leading
monomials**, the second spanned by top components of relators of the first: the ideal of the
Koszul dual relators of the second is the associated graded of that of the first, for the
reversed weight, in every arity `n ≥ 2`. -/
theorem idealOf_dualRel_eq_grF_of_isGroebner (rk : E → ℕ) {L : Set (LTree E)}
    (w : E → ℕ) {ι : Type*} (sr : ι → Mono E 3 → K) (N : ι → ℕ)
    (hs : ∀ i, IsBelowM w (N i) (sr i)) {R R₀ : Submodule K (Mono E 3 → K)}
    (hG : IsGroebner K rk L R) (hG₀ : IsGroebner K rk L R₀) (hsR : ∀ i, sr i ∈ R)
    (hR₀ : R₀ = Submodule.span K (Set.range fun i => wprojM w (N i) (sr i))) {n : ℕ}
    (hn : 2 ≤ n) :
    idealOf K (dualRel K R₀) n = grF K (revW (wMono w n)) (idealOf K (dualRel K R) n) :=
  idealOf_dualRel_eq_grF w hn (KD_eq_grW_of_isGroebner rk w sr N hs hG hG₀ hsR hR₀ hn)

end ShuffleBar

end Operad
