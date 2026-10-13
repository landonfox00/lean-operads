/-
# The Koszul dual of a shuffle operad with a quadratic Gröbner basis is Koszul

Let `R` be relators of arity three which are a quadratic Gröbner basis (`LTree.IsGroebner`) with
leading monomials `L`, for the path-lexicographic key of a ranking of the generators. Their Koszul
dual relators `R^! = dualRel R`, the orthogonal of `R` for the pairing twisted by the signs of the
monomials of arity three, have Gröbner data for the **reversed** key, with leading monomials those
outside `L`:

* in arity three, every monomial `w ∉ L` is the **least** monomial of the support of a Koszul dual
  relator (`ShuffleBar.exists_dualRel_lead`): the coordinate of `w` in the normal form, twisted by
  the signs, vanishes on `R`, and on every monomial of `L` whose key does not exceed that of `w`,
  by induction along the relators which `L` leads;
* so for the reversed key every monomial with a window outside `L` leads a vector of the ideal of
  `R^!` (`ShuffleBar.isLeading_dual`), and the monomials all of whose windows lie in `L` span a
  complement of that ideal (`ShuffleBar.isCompl_dual`): they span modulo the ideal by reduction,
  and they are as many as the dimension of the Koszul dual operad
  (`ShuffleBar.finrank_quotient_dualRel_eq_ncard`);
* hence `R^!` has Gröbner data (`ShuffleBar.dualData`) and, by the criterion of Dotsenko and
  Khoroshkin, **the Koszul dual operad is Koszul** (`ShuffleBar.isKoszul_dualRel`).
-/
import Operad.ShuffleGradedDual

namespace Operad

namespace ShuffleBar

open LTree Module

variable {E : Type*} [Fintype E] [DecidableEq E] {K : Type*} [Field K]

/-! ## Arity three -/

/-- **The window of an edge of a monomial is a monomial of arity three.** -/
lemma windowAt_mem_three {n : ℕ} {t : LTree E} (ht : t ∈ monomials n) {p : List Bool}
    {s : Bool} (he : t.IsEdge p s) : t.windowAt p s ∈ monomials 3 := by
  have hm := (mem_monomials n t).1 ht
  obtain ⟨h1, h2, -⟩ := windowRoot_shape (t.subtreeAt p) s he (isShuffle_subtreeAt t p hm.1)
    (nodup_subtreeAt t p (hm.2.nodup_iff.2 List.nodup_range))
  exact (mem_monomials 3 _).2 ⟨h1, h2⟩

/-- **A monomial of arity three is its own window.** -/
lemma windowAt_three {σ : LTree E} (hσ : σ ∈ monomials 3) {p : List Bool} {s : Bool}
    (he : σ.IsEdge p s) : σ.windowAt p s = σ := by
  have hm := (mem_monomials 3 σ).1 hσ
  have h1 := substAt_windowAt he hm.1 (hm.2.nodup_iff.2 List.nodup_range)
  rwa [substAt_of_mem_monomials_three hσ he
    ((mem_monomials 3 _).1 (windowAt_mem_three hσ he)).2] at h1

/-- **A monomial of arity three is normal exactly when it is not leading.** -/
lemma isNormal_three {L : Set (LTree E)} {σ : LTree E} (hσ : σ ∈ monomials 3) :
    IsNormal L σ ↔ σ ∉ L := by
  have hm := (mem_monomials 3 σ).1 hσ
  have hedge : ∃ p s, σ.IsEdge p s := by
    obtain ⟨e, f, h | h | h⟩ := mono3_cases hm.1 hm.2 <;> subst h
    · exact ⟨[], false, trivial⟩
    · exact ⟨[], false, trivial⟩
    · exact ⟨[], true, trivial⟩
  rw [← not_iff_not, not_isNormal_iff, not_not]
  constructor
  · rintro ⟨p, s, he, hw⟩
    rwa [windowAt_three hσ he] at hw
  · intro h
    obtain ⟨p, s, he⟩ := hedge
    exact ⟨p, s, he, by rwa [windowAt_three hσ he]⟩

variable {rk : E → ℕ} {L : Set (LTree E)} {R : Submodule K (Mono E 3 → K)}

lemma eq_sum_vecOf {n : ℕ} (v : Mono E n → K) :
    v = ∑ ρ : Mono E n, v ρ • vecOf K n ρ.1 := by
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, vecOf, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single y (fun ρ _ hρ => if_neg fun h => hρ (Subtype.ext h).symm)
    (by simp), if_pos rfl]

/-- **Every monomial of arity three outside `L` is the least monomial of a Koszul dual relator**:
the coordinate of `w` in the normal form, twisted by the signs. -/
theorem exists_dualRel_lead (hG : IsGroebner K rk L R) (w : Mono E 3) (hw : w.1 ∉ L) :
    ∃ x ∈ dualRel K R, x w ≠ 0 ∧
      ∀ σ : Mono E 3, σ ≠ w → x σ ≠ 0 → pathKey rk 3 w.1 < pathKey rk 3 σ.1 := by
  set π := nfProj hG.isCompl 3 with hπ
  have hnormal : ∀ σ : Mono E 3, σ.1 ∉ L → π (vecOf K 3 σ.1) = vecOf K 3 σ.1 := fun σ hσ =>
    nfProj_eq_self hG.isCompl (by
      rw [mem_supportedOn]
      intro y hy
      simp only [vecOf]
      rw [if_neg]
      intro h
      exact hy (by rw [normalSet, Set.mem_setOf_eq, h]; exact (isNormal_three σ.2).2 hσ))
  -- the coordinate of `w` vanishes on the monomials of key at most that of `w`
  have hvan : ∀ σ : Mono E 3, σ ≠ w → pathKey rk 3 σ.1 ≤ pathKey rk 3 w.1 →
      π (vecOf K 3 σ.1) w = 0 := by
    letI := keyOrder rk 3
    intro σ
    induction σ using WellFoundedLT.induction with
    | _ σ ih =>
    intro hσw hσk
    by_cases hσL : σ.1 ∈ L
    · obtain ⟨r, hr, hrσ, hlt⟩ := hG.lead σ.1 hσL
      have hr0 : π r = 0 := nfProj_eq_zero hG.isCompl (by rw [idealOf_three]; exact hr)
      have hexp := congrFun (congrArg π (eq_sum_vecOf r)) w
      rw [hr0, map_sum] at hexp
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hexp
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ), Finset.sum_eq_zero, add_zero] at hexp
      · exact (mul_eq_zero.1 hexp.symm).resolve_left hrσ
      · intro ρ hρ
        by_cases hrρ : r ρ = 0
        · rw [hrρ, zero_mul]
        have hρσ : ρ ≠ σ := (Finset.mem_erase.1 hρ).1
        have hkey := hlt ρ (fun h => hρσ (Subtype.ext h)) hrρ
        have hρw : ρ ≠ w := by
          rintro rfl
          exact absurd (hkey.trans_le hσk) (lt_irrefl _)
        rw [ih ρ (keyOrder_lt hkey) hρw (hkey.le.trans hσk), mul_zero]
    · rw [hnormal σ hσL]
      simp only [vecOf]
      exact if_neg fun h => hσw (Subtype.ext h).symm
  refine ⟨fun σ => (chi3 σ.1 : K) * π (vecOf K 3 σ.1) w, ?_, ?_, fun σ hσ hxσ => ?_⟩
  · rw [dualRel, LinearMap.BilinForm.mem_orthogonal_iff]
    intro r hr
    show diagForm _ r _ = 0
    rw [diagForm_apply]
    have : ∀ σ : Mono E 3, (chi3 σ.1 : K) * r σ * ((chi3 σ.1 : K) * π (vecOf K 3 σ.1) w) =
        r σ * π (vecOf K 3 σ.1) w := fun σ => by
      have h' : (chi3 σ.1 : K) * (chi3 σ.1 : K) = 1 := by
        have := congrArg (fun z : ℤ => (z : K)) (chi3_sq σ.1)
        push_cast at this
        exact this
      linear_combination (r σ * π (vecOf K 3 σ.1) w) * h'
    simp only [this]
    have hr0 : π r = 0 := nfProj_eq_zero hG.isCompl (by rw [idealOf_three]; exact hr)
    have hexp := congrFun (congrArg π (eq_sum_vecOf r)) w
    rw [hr0, map_sum] at hexp
    simpa only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      eq_comm] using hexp
  · show (chi3 w.1 : K) * π (vecOf K 3 w.1) w ≠ 0
    rw [hnormal w hw]
    simp only [vecOf, if_true, mul_one]
    exact chi3_cast_ne_zero w.1
  · by_contra hk
    exact hxσ (by
      show (chi3 σ.1 : K) * π (vecOf K 3 σ.1) w = 0
      rw [hvan σ hσ (not_lt.1 hk), mul_zero])

/-! ## The reversed key -/

/-- **The reversed level** of a monomial of arity `n`: the number of monomials whose key is at least
its own. -/
noncomputable def lvRev (rk : E → ℕ) (n : ℕ) (t : LTree E) : ℕ :=
  ((monomials n).filter fun t' => pathKey rk n t ≤ pathKey rk n t').card

lemma lvRev_lt {n : ℕ} {t t' : LTree E} (ht : t ∈ monomials n)
    (h : pathKey rk n t < pathKey rk n t') : lvRev rk n t' < lvRev rk n t := by
  refine Finset.card_lt_card ⟨fun u hu => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, h.le.trans hu.2⟩
  · have := hsub (Finset.mem_filter.2 ⟨ht, le_rfl⟩)
    simp only [Finset.mem_filter] at this
    exact absurd this.2 (not_le.2 h)

/-- **The least monomial of a Koszul dual relator at a window outside `L`**: the other substitutions
raise the key. -/
theorem exists_dualRel_lead_at (hG : IsGroebner K rk L R) {n : ℕ} {t : LTree E}
    (ht : t ∈ monomials n) {p : List Bool} {s : Bool} (he : t.IsEdge p s)
    (hw : t.windowAt p s ∉ L) : ∃ x ∈ dualRel K R, ∃ w : Mono E 3, w.1 = t.windowAt p s ∧ x w ≠ 0 ∧
      ∀ σ : Mono E 3, σ ≠ w → x σ ≠ 0 → pathKey rk n t < pathKey rk n (t.substAt p s σ.1) := by
  obtain ⟨x, hx, hxw, hlt⟩ := exists_dualRel_lead hG ⟨_, windowAt_mem_three ht he⟩ hw
  refine ⟨x, hx, _, rfl, hxw, fun σ hσ hxσ => ?_⟩
  have hm := (mem_monomials n t).1 ht
  have hself := substAt_windowAt he hm.1 (hm.2.nodup_iff.2 List.nodup_range)
  have := pathKey_substAt_lt' rk ht he (windowAt_mem_three ht he) σ.2 (hlt σ hσ hxσ)
  rwa [hself] at this

/-- **The reversed order** on the monomials of arity `n`. -/
@[reducible] noncomputable def keyOrderRev (rk : E → ℕ) (n : ℕ) : LinearOrder (Mono E n) :=
  LinearOrder.lift'
    (fun y => OrderDual.toDual (toLex (pathKey rk n y.1, (Fintype.equivFin (Mono E n) y : ℕ))))
    fun x y h => by
      simp only [OrderDual.toDual_inj, toLex_inj, Prod.mk.injEq] at h
      exact (Fintype.equivFin (Mono E n)).injective (Fin.ext h.2)

lemma keyOrderRev_lt {n : ℕ} {x y : Mono E n} (h : pathKey rk n y.1 < pathKey rk n x.1) :
    (keyOrderRev rk n).lt x y := by
  show @LT.lt (Lex (List ℕ × ℕ))ᵒᵈ _
    (OrderDual.toDual (toLex (pathKey rk n x.1, ((Fintype.equivFin (Mono E n) x : ℕ)))))
    (OrderDual.toDual (toLex (pathKey rk n y.1, ((Fintype.equivFin (Mono E n) y : ℕ)))))
  exact OrderDual.toDual_lt_toDual.2 (Prod.Lex.toLex_lt_toLex.2 (Or.inl h))

/-- **For the reversed order, every monomial with a window outside `L` leads a vector of the ideal
of the Koszul dual relators.** -/
theorem isLeading_dual (hG : IsGroebner K rk L R) {n : ℕ} (y : Mono E n)
    (hy : ¬ IsNormal {w | w ∉ L} y.1) :
    letI := keyOrderRev rk n; IsLeading (idealOf K (dualRel K R) n : Set (Mono E n → K)) y := by
  letI := keyOrderRev rk n
  obtain ⟨p, s, he, hw⟩ := not_isNormal_iff.1 hy
  obtain ⟨x, hx, w, hww, hxw, hlt⟩ := exists_dualRel_lead_at hG y.2 he hw
  have hm := (mem_monomials n y.1).1 y.2
  have hself : y.1.substAt p s w.1 = y.1 := by
    rw [hww]
    exact substAt_windowAt he hm.1 (hm.2.nodup_iff.2 List.nodup_range)
  refine ⟨substVec K n y.1 p s x, substVec_mem_idealOf K _ y he hx, ?_, fun z hz => ?_⟩
  · simp only [substVec, Finset.sum_apply, Pi.smul_apply, vecOf, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single w (fun σ _ hσ => ?_) (by simp), if_pos hself.symm]
    · exact hxw
    · by_cases hxσ : x σ = 0
      · simp [hxσ]
      · rw [if_neg]
        intro h
        have := hlt σ hσ hxσ
        rw [← h] at this
        exact lt_irrefl _ this
  · simp only [substVec, Finset.sum_apply, Pi.smul_apply, vecOf, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    refine Finset.sum_eq_zero fun σ _ => ?_
    split_ifs with h
    · by_cases hσ : σ = w
      · subst hσ
        rw [hself] at h
        exact absurd (Subtype.ext h ▸ hz) (lt_irrefl _)
      · by_contra hxσ
        have hlt' := keyOrderRev_lt (rk := rk) (x := z) (y := y) (by rw [h]; exact hlt σ hσ hxσ)
        exact absurd (hz.trans hlt') (lt_irrefl _)
    · rfl

omit [Fintype E] [DecidableEq E] in
/-- **A monomial is normal for the monomials outside `L` exactly when all its windows lie in
`L`.** -/
lemma isNormal_compl_iff (m : LTree E) : IsNormal {w | w ∉ L} m ↔ IsFull L m := by
  unfold IsNormal IsFull
  rw [← edgeWins_map_snd]
  simp only [List.mem_map, Set.mem_setOf_eq, not_not]
  constructor
  · intro h kw hkw
    exact h kw.2 ⟨kw, hkw, rfl⟩
  · rintro h _ ⟨kw, hkw, rfl⟩
    exact h kw hkw

/-- An ideal of relators of arity three vanishes in arity below three. -/
lemma idealOf_eq_bot (R' : Submodule K (Mono E 3 → K)) {n : ℕ} (hn : n < 3) :
    idealOf K R' n = ⊥ := by
  rw [idealOf, Submodule.span_eq_bot]
  rintro _ ⟨t, p, s, r, -, he, rfl⟩
  exfalso
  have h1 := three_le_arity_of_isEdgeRoot he
  have h2 := arity_subtreeAt_le t.1 p
  have h3 := arity_of_mem_monomials t.2
  omega

/-- **The monomials all of whose windows lie in `L` span a complement of the ideal of the Koszul
dual relators**, in every arity. -/
theorem isCompl_dual (hG : IsGroebner K rk L R) (n : ℕ) :
    IsCompl (idealOf K (dualRel K R) n) (supportedOn K (normalSet {w | w ∉ L} n)) := by
  classical
  set I := idealOf K (dualRel K R) n with hI
  set S := supportedOn K (normalSet {w | w ∉ L} n) with hS
  have hsup : I ⊔ S = ⊤ := by
    letI := keyOrderRev rk n
    rw [eq_top_iff]
    intro v _
    obtain ⟨u, hu, hvu, -⟩ := exists_reduction I (normalSet {w | w ∉ L} n)
      (fun y hy => isLeading_dual hG y hy) v
    have : v = u + (v - u) := by abel
    rw [this]
    exact Submodule.add_mem_sup hu hvu
  refine ⟨?_, codisjoint_iff.2 hsup⟩
  rcases lt_or_ge n 3 with hn | hn
  · rw [hI, idealOf_eq_bot _ hn]
    exact disjoint_bot_left
  -- the normal vectors map onto the quotient, which has their dimension
  set f : S →ₗ[K] (Mono E n → K) ⧸ I := I.mkQ ∘ₗ S.subtype with hf
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective I q
    obtain ⟨u, hu, s', hs', hus⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : v ∈ I ⊔ S)
    refine ⟨⟨s', hs'⟩, ?_⟩
    simp only [hf, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      Submodule.mkQ_apply]
    rw [← hus, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero I).2 hu, zero_add]
  set N := Finset.univ.filter fun y : Mono E n => y ∈ normalSet {w | w ∉ L} n with hN
  have hSle : finrank K S ≤ N.card := by
    have hspan : S ≤ Submodule.span K ((N.image fun y => vecOf K n y.1 : Finset _) :
        Set (Mono E n → K)) := by
      intro v hv
      rw [eq_sum_vecOf v, ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun y => y ∈ normalSet {w | w ∉ L} n)]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun y hy => Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hy))))
        (Submodule.sum_mem _ fun y hy => ?_)
      rw [(mem_supportedOn.1 hv) y (Finset.mem_filter.1 hy).2, zero_smul]
      exact Submodule.zero_mem _
    exact (Submodule.finrank_mono hspan).trans
      ((finrank_span_finset_le_card _).trans Finset.card_image_le)
  have hQ : finrank K ((Mono E n → K) ⧸ I) = N.card := by
    rw [hI, finrank_quotient_dualRel_eq_ncard rk hG (by omega)]
    rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ Subtype.val_injective]
    congr 1
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, hN, Finset.mem_filter,
      Finset.mem_univ, true_and, normalSet, isNormal_compl_iff]
    constructor
    · rintro ⟨hm, hfull⟩
      exact ⟨⟨m, hm⟩, hfull, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  have hdim : finrank K S = finrank K ((Mono E n → K) ⧸ I) :=
    le_antisymm (hSle.trans hQ.ge) (LinearMap.finrank_range_le f |>.trans' (by
      rw [LinearMap.range_eq_top.2 hsurj, finrank_top]))
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  rw [Submodule.disjoint_def]
  intro v hvI hvS
  have : f ⟨v, hvS⟩ = f 0 := by
    simp only [hf, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      Submodule.mkQ_apply, map_zero]
    exact (Submodule.Quotient.mk_eq_zero I).2 hvI
  exact congrArg Subtype.val (hinj this)

/-! ## The Koszul dual is Koszul -/

/-- **The Gröbner data of the Koszul dual relators**: the leading monomials are those outside `L`,
and the level is reversed. -/
noncomputable def dualData (hG : IsGroebner K rk L R) :
    GroebnerData K {w | w ∉ L} (dualRel K R) where
  compl := isCompl_dual hG
  lv := lvRev rk
  lv_pos {n t} ht := Finset.card_pos.2 ⟨t, Finset.mem_filter.2 ⟨ht, le_rfl⟩⟩
  lv_le n t := Finset.card_filter_le _ _
  lead {n t} ht {p s} he hw := by
    obtain ⟨x, hx, w, hww, hxw, hlt⟩ := exists_dualRel_lead_at hG ht he hw
    exact ⟨x, hx, w, hww, hxw, fun σ hσ hxσ => lvRev_lt ht (hlt σ hσ hxσ)⟩

/-- **The Koszul dual of a shuffle operad with a quadratic Gröbner basis is Koszul**: the bar
construction of the operad presented by the Koszul dual relators has no homology below the
diagonal. -/
theorem isKoszul_dualRel (hG : IsGroebner K rk L R) : IsKoszul K (dualRel K R) :=
  isKoszul_of_data K (dualData hG)

end ShuffleBar

end Operad
