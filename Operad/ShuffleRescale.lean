/-
# Rescaling the generators of a shuffle operad

Multiplying each generator `e` by a unit `λ e` multiplies a monomial by the product of the scalars
of its vertices (`LTree.wt`). On relators of arity three this is the linear automorphism
`ShuffleBar.rescale λ`, and the operad presented by the rescaled relators is isomorphic to the
original one; at the level of the bar construction:

* merging along a cut edge does not change the vertices (`wt_mergeK`), so the diagonal rescaling
  of the bar construction (`ShuffleBar.scaleBar`) commutes with its differential
  (`d_scaleBar`);
* substituting a monomial at a window multiplies the weight of the context by that of the
  monomial (`wt_substBar`), so the rescaling carries the relator subcomplex of `R` onto that of
  the rescaled relators (`map_scaleBar_J`);
* hence **the Koszul dual cooperads of `R` and of its rescaling are isomorphic in every arity**
  (`map_scaleBar_KD`, `finrank_KD_rescale`).
-/
import Operad.ShuffleKoszulDual

universe u v

namespace Operad

namespace LTree

variable {E : Type v} {K : Type u} [CommRing K]

/-- **The weight of a tree**: the product of the scalars of the decorations of its vertices. -/
def wt (l : E → K) : LTree E → K
  | leaf _ => 1
  | node e a b => l e * wt l a * wt l b

@[simp] lemma wt_leaf (l : E → K) (a : ℕ) : wt l (leaf a : LTree E) = 1 := rfl

@[simp] lemma wt_node (l : E → K) (e : E) (a b : LTree E) :
    wt l (node e a b) = l e * wt l a * wt l b := rfl

lemma wt_mapDec {F : Type*} (f : E → F) (l : F → K) :
    ∀ t : LTree E, wt l (t.mapDec f) = wt (l ∘ f) t
  | leaf _ => rfl
  | node e a b => by
    simp only [mapDec_node, wt_node, wt_mapDec f l a, wt_mapDec f l b, Function.comp_apply]

/-- **Plugging trees into the leaves** multiplies the weights. -/
lemma wt_plug (l : E → K) (ins : ℕ → LTree E) :
    ∀ m : LTree E, wt l (m.plug ins) = wt l m * (m.labels.map fun a => wt l (ins a)).prod
  | leaf a => by simp [plug, labels]
  | node e a b => by
    simp only [plug, wt_node, wt_plug l ins a, wt_plug l ins b, labels, List.map_append,
      List.prod_append]
    ring

/-- **Replacing a subtree** at a path ending at a vertex: the weight of the context times that of
the new subtree. -/
lemma wt_replaceAt (l : E → K) :
    ∀ (t : LTree E) (p : List Bool), (∃ e a b, t.subtreeAt p = node e a b) →
      ∃ c : K, ∀ u : LTree E, wt l (t.replaceAt p u) = c * wt l u
  | t, [], _ => ⟨1, fun u => by simp⟩
  | leaf _, _ :: _, h => by simp [subtreeAt] at h
  | node e a b, false :: p, h => by
    obtain ⟨c, hc⟩ := wt_replaceAt l a p h
    exact ⟨l e * wt l b * c, fun u => by simp only [replaceAt, wt_node, hc]; ring⟩
  | node e a b, true :: p, h => by
    obtain ⟨c, hc⟩ := wt_replaceAt l b p h
    exact ⟨l e * wt l a * c, fun u => by simp only [replaceAt, wt_node, hc]; ring⟩

/-- **Substituting at a window** multiplies the weight of the context by that of the
substituted monomial of arity three. -/
lemma wt_substAt (l : E → K) {t : LTree E} {p : List Bool} {s : Bool} (h : t.IsEdge p s) :
    ∃ c : K, ∀ m : LTree E, m.labels.Perm (List.range 3) →
      wt l (t.substAt p s m) = c * wt l m := by
  obtain ⟨c, hc⟩ := wt_replaceAt l t p h.exists_node
  refine ⟨c * (wt l ((t.subtreeAt p).winIns s 0) * wt l ((t.subtreeAt p).winIns s 1)
    * wt l ((t.subtreeAt p).winIns s 2)), fun m hm => ?_⟩
  rw [substAt, hc, wt_plug, (hm.map _).prod_eq]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

end LTree

namespace ShuffleBar

open LTree

variable {E : Type v} {K : Type u} [CommRing K]

/-- The weight of a bar tree: that of its monomial, the flags forgotten. -/
def wtB (l : E → K) (x : BarTree E) : K := wt (l ∘ Prod.fst) x

lemma wtB_eq (l : E → K) (x : BarTree E) : wtB l x = wt l (x.mapDec Prod.fst) := by
  rw [wtB, wt_mapDec]

/-- **Merging does not change the vertices.** -/
lemma wt_mergeK (l : E → K) : ∀ (x : BarTree E) (k : ℕ ×ₗ ℕ), wtB l (mergeK x k) = wtB l x
  | leaf _, _ => rfl
  | node d a b, k => by
    unfold mergeK
    split_ifs
    · rfl
    · have ha := wt_mergeK l a k
      have hb := wt_mergeK l b k
      simp only [wtB, wt_node] at ha hb ⊢
      rw [ha, hb]

/-- **Substituting at an uncut edge** multiplies the weight of the context by that of the
monomial. -/
lemma wt_substBar (l : E → K) {x : BarTree E} {p : List Bool} {s : Bool} (h : x.IsEdge p s) :
    ∃ c : K, ∀ σ : LTree E, σ.labels.Perm (List.range 3) →
      wtB l (substBar x p s σ) = c * wt l σ := by
  obtain ⟨c, hc⟩ := wt_substAt (l ∘ Prod.fst) h
  refine ⟨c, fun σ hσ => ?_⟩
  rw [wtB, substBar, hc _ (by rwa [labels_liftW])]
  congr 1
  rw [← wt_mapDec Prod.fst l, liftW_mapDec]

lemma wt_mul (l l' : E → K) : ∀ t : LTree E, wt (l * l') t = wt l t * wt l' t
  | leaf _ => by simp
  | node e a b => by
    simp only [wt_node, wt_mul l l' a, wt_mul l l' b, Pi.mul_apply]
    ring

lemma wt_one : ∀ t : LTree E, wt (1 : E → K) t = 1
  | leaf _ => rfl
  | node e a b => by simp [wt_one a, wt_one b]

variable (K : Type u) [Field K]

/-- **The rescaling of the bar construction**: each bar tree times its weight. -/
noncomputable def scaleBar (l : E → K) : (BarTree E →₀ K) →ₗ[K] (BarTree E →₀ K) :=
  Finsupp.linearCombination K fun x => wtB l x • Finsupp.single x 1

lemma scaleBar_single (l : E → K) (x : BarTree E) (c : K) :
    scaleBar K l (Finsupp.single x c) = (c * wtB l x) • Finsupp.single x 1 := by
  simp [scaleBar]

lemma scaleBar_scaleBar (l l' : E → K) (v : BarTree E →₀ K) :
    scaleBar K l (scaleBar K l' v) = scaleBar K (l * l') v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single x c =>
    rw [scaleBar_single, map_smul, scaleBar_single, scaleBar_single, smul_smul, wtB, wtB, wtB,
      show ((l * l') ∘ Prod.fst : E × Bool → K) = (l ∘ Prod.fst) * (l' ∘ Prod.fst) from rfl,
      wt_mul]
    ring_nf

lemma scaleBar_one (v : BarTree E →₀ K) : scaleBar K (1 : E → K) v = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single x c =>
    rw [scaleBar_single, wtB, show ((1 : E → K) ∘ Prod.fst : E × Bool → K) = 1 from rfl, wt_one,
      mul_one, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **The rescaling commutes with the differential**: merging keeps the vertices. -/
theorem d_scaleBar (l : E → K) (v : BarTree E →₀ K) :
    d K (scaleBar K l v) = scaleBar K l (d K v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single x c =>
    rw [scaleBar_single, map_smul, d_single, one_smul, d_single, map_smul]
    simp only [dTree, map_sum, Finset.smul_sum, map_smul, scaleBar_single, wt_mergeK, smul_smul,
      one_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring_nf

variable [Fintype E] [DecidableEq E]

/-- **The rescaling of the relators of arity three**: the coefficient of a monomial multiplied by
its weight. -/
noncomputable def rescale (l : E → K) : (Mono E 3 → K) →ₗ[K] (Mono E 3 → K) where
  toFun r σ := wt l σ.1 * r σ
  map_add' r r' := by funext σ; simp [mul_add]
  map_smul' c r := by funext σ; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma rescale_rescale (l l' : E → K) (r : Mono E 3 → K) :
    rescale K l (rescale K l' r) = rescale K (l * l') r := by
  funext σ
  simp only [rescale, LinearMap.coe_mk, AddHom.coe_mk, wt_mul]
  ring

lemma rescale_one (r : Mono E 3 → K) : rescale K (1 : E → K) r = r := by
  funext σ
  simp [rescale, wt_one]

omit [Fintype E] in
lemma scaleBar_mem_C (l : E → K) {n s : ℕ} {v : BarTree E →₀ K} (hv : v ∈ C K n s) :
    scaleBar K l v ∈ C K n s := by
  rw [C, Finsupp.mem_supported] at hv ⊢
  intro x hx
  rw [Finset.mem_coe, Finsupp.mem_support_iff] at hx
  refine hv (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 fun h0 => hx ?_))
  rw [scaleBar, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply']
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hxy : y = x
  · subst hxy
    simp [h0]
  · simp [hxy]

/-- **The rescaling of a substituted relator** is the substituted rescaled relator, times the
weight of the context. -/
lemma scaleBar_substRel (l : E → K) {x : BarTree E} {p : List Bool} {s : Bool}
    (h : IsUncut x p s) : ∃ c : K, ∀ r : Mono E 3 → K,
      scaleBar K l (substRel K x p s r) = c • substRel K x p s (rescale K l r) := by
  obtain ⟨c, hc⟩ := wt_substBar l h.1
  refine ⟨c, fun r => ?_⟩
  simp only [substRel, map_sum, map_smul, scaleBar_single, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hσ : σ.1.labels.Perm (List.range 3) := ((mem_monomials 3 σ.1).1 σ.2).2
  rw [hc σ.1 hσ]
  simp only [rescale, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
  ring_nf

/-- **The rescaling carries the relator subcomplex of `R` into that of the rescaled
relators.** -/
theorem map_scaleBar_J_le (l : E → K) (R : Submodule K (Mono E 3 → K)) :
    (J K R).map (scaleBar K l) ≤ J K (R.map (rescale K l)) := by
  rw [Submodule.map_le_iff_le_comap, J, Submodule.span_le]
  rintro _ ⟨x, p, s, r, hx, h, hr, rfl⟩
  obtain ⟨c, hc⟩ := scaleBar_substRel K l h
  show scaleBar K l (substRel K x p s r) ∈ J K _
  rw [hc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨x, p, s, rescale K l r, hx, h, Submodule.mem_map_of_mem hr, rfl⟩)

/-- **The rescaling carries the Koszul dual cooperad of `R` onto that of the rescaled
relators**, for nonzero scalars. -/
theorem map_scaleBar_KD (l : E → K) (hl : ∀ e, l e ≠ 0) (R : Submodule K (Mono E 3 → K))
    (n : ℕ) : (KD K R n).map (scaleBar K l) = KD K (R.map (rescale K l)) n := by
  have hinv : l⁻¹ * l = 1 := funext fun e => inv_mul_cancel₀ (hl e)
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro v hv
    rw [KD, Submodule.mem_inf, Submodule.mem_comap] at hv
    refine Submodule.mem_comap.2 (Submodule.mem_inf.2 ⟨scaleBar_mem_C K l hv.1, ?_⟩)
    rw [Submodule.mem_comap, d_scaleBar]
    exact map_scaleBar_J_le K l R (Submodule.mem_map_of_mem hv.2)
  · intro w hw
    rw [KD, Submodule.mem_inf, Submodule.mem_comap] at hw
    refine ⟨scaleBar K l⁻¹ w, ?_, by
      rw [scaleBar_scaleBar, show l * l⁻¹ = 1 from funext fun e => mul_inv_cancel₀ (hl e),
        scaleBar_one]⟩
    refine Submodule.mem_inf.2 ⟨scaleBar_mem_C K _ hw.1, ?_⟩
    rw [Submodule.mem_comap, d_scaleBar]
    have := map_scaleBar_J_le K l⁻¹ _ (Submodule.mem_map_of_mem hw.2)
    rwa [← Submodule.map_comp, show (rescale K l⁻¹).comp (rescale K l) = LinearMap.id from
      LinearMap.ext fun r => by
        rw [LinearMap.comp_apply, rescale_rescale, hinv, rescale_one, LinearMap.id_apply],
      Submodule.map_id] at this

/-- **The Koszul dual cooperads of `R` and of its rescaling have the same dimension** in every
arity. -/
theorem finrank_KD_rescale (l : E → K) (hl : ∀ e, l e ≠ 0) (R : Submodule K (Mono E 3 → K))
    (n : ℕ) : Module.finrank K (KD K (R.map (rescale K l)) n) = Module.finrank K (KD K R n) := by
  have hinv : l⁻¹ * l = 1 := funext fun e => inv_mul_cancel₀ (hl e)
  have hinj : Function.Injective (scaleBar K l) := fun v w h => by
    have := congrArg (scaleBar K l⁻¹) h
    rwa [scaleBar_scaleBar, scaleBar_scaleBar, hinv, scaleBar_one, scaleBar_one] at this
  rw [← map_scaleBar_KD K l hl R n]
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _).symm

end ShuffleBar

end Operad
