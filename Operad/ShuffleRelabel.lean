/-
# Relabelling the generators of a binary shuffle operad

An equivalence `π : E ≃ F` of the generators relabels the decorations of every tree
(`LTree.mapDec`). Substitution at an edge commutes with it (`LTree.substAt_mapDec`), and the
shuffle monomials of arity `n` correspond (`LTree.monoMap`). Rescaling the generators is
`Operad.ShuffleRescale`; this is the other half of a change of generators, a permutation.

* **Relators and ideals.** A vector on the monomials of arity `n` is relabelled by reading its
  coefficients back along `π` (`LTree.relabelVec`); it carries the substituted relators of `R`
  to those of the relabelled relators, so **the ideal of `R` maps onto the ideal of
  `R.map (relabelVec π 3)`** in every arity (`LTree.map_relabelVec_idealOf`) and the presented
  operads are linearly isomorphic arity by arity (`LTree.quotRelabelEquiv`).
* **The bar construction.** Relabelling the bar trees, the flags kept (`ShuffleBar.relabelBar`),
  keeps the cut keys, the merges and the signs, so it commutes with the differential
  (`ShuffleBar.d_relabelBar`); it keeps arity and degree (`ShuffleBar.relabelBar_mem_C`) and
  carries the relator subcomplex of `R` into that of the relabelled relators
  (`ShuffleBar.map_relabelBar_J_le`). Hence **Koszulness is invariant under relabelling the
  generators** (`ShuffleBar.isKoszul_relabel`).
-/
import Operad.ShuffleKoszul

namespace Operad

namespace LTree

variable {E F : Type*}

@[simp] lemma mem_monomials_mapDec [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (f : E → F) (n : ℕ) (t : LTree E) : t.mapDec f ∈ monomials n ↔ t ∈ monomials n := by
  rw [mem_monomials, mem_monomials, isShuffle_mapDec, labels_mapDec]

lemma mapDec_equiv_symm (π : E ≃ F) (t : LTree E) : (t.mapDec π).mapDec π.symm = t := by
  rw [mapDec_mapDec, show (π.symm ∘ π : E → E) = id from funext π.symm_apply_apply, mapDec_id]

lemma mapDec_symm_equiv (π : E ≃ F) (t : LTree F) : (t.mapDec π.symm).mapDec π = t := by
  simpa using mapDec_equiv_symm π.symm t

/-! ## Relabelling monomials and relators -/

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

/-- **Relabelling the monomials** of arity `n` along an equivalence of the generators. -/
def monoMap (π : E ≃ F) (n : ℕ) : Mono E n ≃ Mono F n where
  toFun t := ⟨t.1.mapDec π, (mem_monomials_mapDec π n t.1).2 t.2⟩
  invFun t := ⟨t.1.mapDec π.symm, (mem_monomials_mapDec π.symm n t.1).2 t.2⟩
  left_inv t := Subtype.ext (mapDec_equiv_symm π t.1)
  right_inv t := Subtype.ext (mapDec_symm_equiv π t.1)

@[simp] lemma monoMap_val (π : E ≃ F) (n : ℕ) (t : Mono E n) : (monoMap π n t).1 = t.1.mapDec π :=
  rfl

variable (K : Type*) [Field K]

/-- **Relabelling a vector of arity `n`** along an equivalence of the generators: its coefficient
at a monomial is the old coefficient of the monomial relabelled back. -/
noncomputable def relabelVec (π : E ≃ F) (n : ℕ) : (Mono E n → K) ≃ₗ[K] (Mono F n → K) :=
  LinearEquiv.funCongrLeft K K (monoMap π n).symm

variable {K}

lemma relabelVec_apply (π : E ≃ F) (n : ℕ) (v : Mono E n → K) (τ : Mono F n) :
    relabelVec K π n v τ = v ((monoMap π n).symm τ) := rfl

lemma relabelVec_symm_apply (π : E ≃ F) (n : ℕ) (v : Mono E n → K) :
    relabelVec K π.symm n (relabelVec K π n v) = v := by
  funext τ
  rw [relabelVec_apply, relabelVec_apply]
  exact congrArg v (Subtype.ext (mapDec_equiv_symm π τ.1))

lemma relabelVec_vecOf (π : E ≃ F) (n : ℕ) (t : LTree E) :
    relabelVec K π n (vecOf K n t) = vecOf K n (t.mapDec π) := by
  funext τ
  rw [relabelVec_apply]
  simp only [vecOf]
  congr 1
  apply propext
  constructor
  · intro h
    show τ.1 = t.mapDec π
    rw [← h]
    exact (mapDec_symm_equiv π τ.1).symm
  · intro h
    show τ.1.mapDec π.symm = t
    rw [h, mapDec_equiv_symm]

lemma relabelVec_substVec (π : E ≃ F) (n : ℕ) {t : LTree E} {p : List Bool} {s : Bool}
    (he : t.IsEdge p s) (r : Mono E 3 → K) :
    relabelVec K π n (substVec K n t p s r) =
      substVec K n (t.mapDec π) p s (relabelVec K π 3 r) := by
  rw [substVec, substVec, map_sum]
  refine (Fintype.sum_equiv (monoMap π 3) _ _ fun σ => ?_)
  rw [map_smul, relabelVec_vecOf, ← substAt_mapDec π t p s he, relabelVec_apply,
    Equiv.symm_apply_apply]
  rfl

theorem map_relabelVec_idealOf_le (π : E ≃ F) (R : Submodule K (Mono E 3 → K)) (n : ℕ) :
    (idealOf K R n).map (relabelVec K π n).toLinearMap ≤
      idealOf K (R.map (relabelVec K π 3).toLinearMap) n := by
  rw [Submodule.map_le_iff_le_comap, idealOf, Submodule.span_le]
  rintro _ ⟨t, p, s, r, hr, he, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, relabelVec_substVec π n he]
  exact substVec_mem_idealOf K _ (monoMap π n t) ((isEdge_mapDec π t.1 p s).2 he)
    (Submodule.mem_map_of_mem hr)

lemma map_relabelVec_symm (π : E ≃ F) (R : Submodule K (Mono E 3 → K)) :
    (R.map (relabelVec K π 3).toLinearMap).map (relabelVec K π.symm 3).toLinearMap = R := by
  rw [← Submodule.map_comp]
  convert Submodule.map_id R
  exact LinearMap.ext fun v => relabelVec_symm_apply π 3 v

/-- **Relabelling carries the ideal of `R` onto the ideal of the relabelled relators** in every
arity. -/
theorem map_relabelVec_idealOf (π : E ≃ F) (R : Submodule K (Mono E 3 → K)) (n : ℕ) :
    (idealOf K R n).map (relabelVec K π n).toLinearMap =
      idealOf K (R.map (relabelVec K π 3).toLinearMap) n := by
  refine le_antisymm (map_relabelVec_idealOf_le π R n) fun v hv => ?_
  have h := map_relabelVec_idealOf_le π.symm (R.map (relabelVec K π 3).toLinearMap) n
    (Submodule.mem_map_of_mem hv)
  rw [map_relabelVec_symm] at h
  refine ⟨_, h, ?_⟩
  simpa using relabelVec_symm_apply π.symm n v

variable (K) in
/-- **The presented operads are isomorphic in every arity** under a relabelling of the
generators. -/
noncomputable def quotRelabelEquiv (π : E ≃ F) (R : Submodule K (Mono E 3 → K)) (n : ℕ) :
    ((Mono E n → K) ⧸ idealOf K R n) ≃ₗ[K]
      ((Mono F n → K) ⧸ idealOf K (R.map (relabelVec K π 3).toLinearMap) n) :=
  Submodule.Quotient.equiv _ _ (relabelVec K π n) (map_relabelVec_idealOf π R n)

end LTree

namespace ShuffleBar

open LTree

variable {E F : Type*}

/-! ## Relabelling the bar construction -/

/-- The relabelling of the decorations of a bar tree, flags kept. -/
abbrev relDec (π : E ≃ F) : E × Bool → F × Bool := Prod.map π id

lemma cutKeys_mapDec (π : E ≃ F) : ∀ x : BarTree E, cutKeys (x.mapDec (relDec π)) = cutKeys x
  | leaf _ => rfl
  | node d l r => by
    show (if d.2 then {key ((node d l r).mapDec (relDec π))} else ∅) ∪
      (cutKeys (l.mapDec (relDec π)) ∪ cutKeys (r.mapDec (relDec π))) = _
    rw [key_mapDec, cutKeys_mapDec π l, cutKeys_mapDec π r]
    rfl

lemma mergeK_mapDec (π : E ≃ F) (k : ℕ ×ₗ ℕ) :
    ∀ x : BarTree E, mergeK (x.mapDec (relDec π)) k = (mergeK x k).mapDec (relDec π)
  | leaf _ => rfl
  | node d l r => by
    have hk : key (node (relDec π d) (l.mapDec (relDec π)) (r.mapDec (relDec π))) =
        key (node d l r) := key_mapDec _ (node d l r)
    rw [mapDec_node, mergeK, mergeK, hk]
    simp only [relDec, Prod.map_snd, id_eq]
    split_ifs
    · rfl
    · rw [mergeK_mapDec π k l, mergeK_mapDec π k r]
      rfl

lemma rootFlag_mapDec (π : E ≃ F) : ∀ x : BarTree E, rootFlag (x.mapDec (relDec π)) = rootFlag x
  | leaf _ => rfl
  | node _ _ _ => rfl

lemma flagAt_mapDec (π : E ≃ F) (x : BarTree E) (p : List Bool) :
    flagAt (x.mapDec (relDec π)) p = flagAt x p := by
  rw [flagAt, flagAt, subtreeAt_mapDec, rootFlag_mapDec]

lemma liftW_mapDec' (π : E ≃ F) (c : Bool) :
    ∀ σ : LTree E, liftW c (σ.mapDec π) = (liftW c σ).mapDec (relDec π)
  | leaf _ => rfl
  | node e l r => by
    simp only [mapDec_node, liftW, mapDec_mapDec]
    rfl

lemma substBar_mapDec (π : E ≃ F) {x : BarTree E} {p : List Bool} {s : Bool} (h : x.IsEdge p s)
    (σ : LTree E) :
    substBar (x.mapDec (relDec π)) p s (σ.mapDec π) = (substBar x p s σ).mapDec (relDec π) := by
  rw [substBar, substBar, liftW_mapDec', flagAt_mapDec, substAt_mapDec _ x p s h]

lemma isUncut_mapDec (π : E ≃ F) {x : BarTree E} {p : List Bool} {s : Bool} :
    IsUncut (x.mapDec (relDec π)) p s ↔ IsUncut x p s := by
  rw [IsUncut, IsUncut, isEdge_mapDec, flagAt_mapDec]

lemma valid_mapDec (π : E ≃ F) {x : BarTree E} (hx : Valid x) : Valid (x.mapDec (relDec π)) :=
  ⟨(isShuffle_mapDec _ x).2 hx.shuffle, by rw [labels_mapDec]; exact hx.nodup,
    by rw [rootFlag_mapDec]; exact hx.root⟩

variable (K : Type*) [Field K]

/-- **The relabelling of the bar construction.** -/
noncomputable def relabelBar (π : E ≃ F) : (BarTree E →₀ K) →ₗ[K] (BarTree F →₀ K) :=
  Finsupp.lmapDomain K K fun x => x.mapDec (relDec π)

variable {K}

lemma relabelBar_single (π : E ≃ F) (x : BarTree E) (c : K) :
    relabelBar K π (Finsupp.single x c) = Finsupp.single (x.mapDec (relDec π)) c := by
  simp [relabelBar]

lemma relabelBar_symm (π : E ≃ F) (v : BarTree E →₀ K) :
    relabelBar K π.symm (relabelBar K π v) = v := by
  rw [relabelBar, relabelBar, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
    ← Finsupp.mapDomain_comp]
  convert Finsupp.mapDomain_id
  funext x
  rw [Function.comp_apply, mapDec_mapDec]
  convert mapDec_id x
  funext d
  exact Prod.ext (π.symm_apply_apply d.1) rfl

/-- **The relabelling commutes with the differential**: merging and the signs only see the
labels and the flags. -/
theorem d_relabelBar (π : E ≃ F) (v : BarTree E →₀ K) :
    d K (relabelBar K π v) = relabelBar K π (d K v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single x c =>
    rw [relabelBar_single, d_single, d_single, map_smul, dTree, dTree, map_sum,
      cutKeys_mapDec]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, relabelBar_single, mergeK_mapDec, sgn, sgn, cutKeys_mapDec]

lemma adm_mapDec [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] (π : E ≃ F)
    {n s : ℕ} {x : BarTree E} (hx : Adm n s x) : Adm n s (x.mapDec (relDec π)) :=
  ⟨valid_mapDec π hx.1, by rw [labels_mapDec]; exact hx.2.1, by rw [cutKeys_mapDec]; exact hx.2.2⟩

lemma relabelBar_mem_C [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] (π : E ≃ F)
    {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n s) : relabelBar K π v ∈ C K n s := by
  rw [C, Finsupp.mem_supported] at hv ⊢
  intro y hy
  rw [relabelBar, Finsupp.lmapDomain_apply] at hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
  exact adm_mapDec π (hv hx)

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

lemma relabelBar_substRel (π : E ≃ F) {x : BarTree E} {p : List Bool} {s : Bool}
    (h : x.IsEdge p s) (r : Mono E 3 → K) :
    relabelBar K π (substRel K x p s r) =
      substRel K (x.mapDec (relDec π)) p s (relabelVec K π 3 r) := by
  rw [substRel, substRel, map_sum]
  refine (Fintype.sum_equiv (monoMap π 3) _ _ fun σ => ?_)
  rw [map_smul, relabelBar_single, relabelVec_apply, Equiv.symm_apply_apply, monoMap_val,
    substBar_mapDec π h]

/-- **The relabelling carries the relator subcomplex of `R` into that of the relabelled
relators.** -/
theorem map_relabelBar_J_le (π : E ≃ F) (R : Submodule K (Mono E 3 → K)) :
    (J K R).map (relabelBar K π) ≤ J K (R.map (relabelVec K π 3).toLinearMap) := by
  rw [Submodule.map_le_iff_le_comap, J, Submodule.span_le]
  rintro _ ⟨x, p, s, r, hx, h, hr, rfl⟩
  show relabelBar K π (substRel K x p s r) ∈ J K _
  rw [relabelBar_substRel π h.1]
  exact Submodule.subset_span ⟨_, p, s, _, valid_mapDec π hx, (isUncut_mapDec π).2 h,
    Submodule.mem_map_of_mem hr, rfl⟩

/-- **Koszulness is invariant under relabelling the generators.** -/
theorem isKoszul_relabel (π : E ≃ F) {R : Submodule K (Mono E 3 → K)} (hR : IsKoszul K R) :
    IsKoszul K (R.map (relabelVec K π 3).toLinearMap) := by
  intro n s hs x hx hdx
  have hdx' : d K (relabelBar K π.symm x) ∈ J K R := by
    rw [d_relabelBar, ← map_relabelVec_symm π R]
    exact map_relabelBar_J_le π.symm _ (Submodule.mem_map_of_mem hdx)
  obtain ⟨y, hy, hxy⟩ := hR n s hs _ (relabelBar_mem_C π.symm hx) hdx'
  refine ⟨relabelBar K π y, relabelBar_mem_C π hy, ?_⟩
  have := map_relabelBar_J_le π R (Submodule.mem_map_of_mem hxy)
  have hinv : relabelBar K π (relabelBar K π.symm x) = x := by
    simpa using relabelBar_symm π.symm x
  rwa [map_sub, hinv, ← d_relabelBar] at this

end ShuffleBar

end Operad
