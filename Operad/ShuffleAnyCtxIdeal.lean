/-
# The symmetric–shuffle bridge for generators of any arity, from the relators and the rules

`Operad.ShuffleAnySym.isKoszul_iff_rules` assumes that an operation of `T(E)` is in the ideal of
the relators iff its coordinates in the basis of the shuffle trees lie in the ideal of the rules.
This file derives that hypothesis from conditions on the relators and on the rules, so that the
bridge has no hypothesis on the ideals.

* **Contexts preserve the ideals of the free operad** (`mapDomain_mem_IC`). Let `I` be an ideal
  of `T(E)` and `IC I Y` the combinations of shuffle monomials with leaves `Y` which are
  operations of `I`. A context of shuffle monomials is an increasing relabelling
  (`mapDomain_relabelM_mem`), then a substitution at the leaves of trees whose least leaf is the
  leaf replaced (`mapDomain_subst_mem`), then a replacement at a position of a tree
  (`mapDomain_replace_mem`). The second and the third are chains of partial compositions with a
  fixed monomial (`mapDomain_graftR_mem`, `mapDomain_graftL_mem`), one for each leaf substituted
  and one for each vertex along the position.
* **The ideal of the rules lies in the ideal of the relators** (`mem_span_of_repr_mem_ideal`),
  when each rule `lead - tail` is a relation of `T(E)/(r)`.
* **The two ideals agree** (`mem_span_iff_repr_mem_ideal`), with the other inclusion from
  `Operad.ShuffleAnyRelIdeal`.
* **The bridge** (`isKoszul_iff_rules_of_stable`): for quadratic relators `r` stable under the
  symmetric groups and homogeneous rules `G` such that the coordinates of each relator lie in the
  ideal of the rules and each rule is a relation of `T(E)/(r)`, over a field of characteristic
  zero, `Koszul.IsKoszul K E r ↔ G.IsKoszul`.
-/
import Operad.ShuffleAnyRelIdeal

universe u

namespace Operad

open Function Sym GerBV GrComposite STree FreeGr Bar

namespace ShuffleAnySym

open ShuffleBarSym

/-! ## Trees -/

section Trees

open STree

variable {T : ℕ → Type}

lemma subst_eq_self {t : STree T} {xs : ℕ → STree T} (h : ∀ a ∈ t.labels, xs a = .leaf a) :
    t.subst xs = t := by
  rw [subst_congr t h]
  exact subst_leaf t

/-- Grafting at the leaf replacing a child of the root puts the grafted tree in its place. -/
lemma subst_node_update_leaf {k : ℕ} (e : T k) (cc : Fin k → STree T) (i : Fin k) (a₀ : ℕ)
    (h : ∀ j, j ≠ i → a₀ ∉ (cc j).labels) (w : STree T) :
    (STree.node e (update cc i (.leaf a₀))).subst (update STree.leaf a₀ w)
      = .node e (update cc i w) := by
  rw [subst_node]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    rw [update_self, update_self, subst_leaf', update_self]
  · rw [update_of_ne hj, update_of_ne hj]
    exact subst_eq_self fun b hb =>
      update_of_ne (fun hba : b = a₀ => h j hj (hba ▸ hb)) _ _

lemma replace_node_cons_update {k : ℕ} (e : T k) (cc : Fin k → STree T) {i : ℕ} (hi : i < k)
    (p : List ℕ) (u : STree T) :
    (STree.node e cc).replace (i :: p) u
      = .node e (update cc ⟨i, hi⟩ ((cc ⟨i, hi⟩).replace p u)) := by
  rw [replace_node_cons]
  congr 1
  funext j
  by_cases hj : j = ⟨i, hi⟩
  · subst hj
    rw [update_self, if_pos rfl]
  · rw [update_of_ne hj, if_neg fun h'' => hj (Fin.ext h'')]

/-- In a nodup union of a family indexed by a nodup multiset, distinct members are disjoint. -/
lemma disjoint_of_nodup_bind {s : Multiset ℕ} {f : ℕ → Multiset ℕ} (h : (s.bind f).Nodup)
    {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) {x : ℕ} (hxa : x ∈ f a) : x ∉ f b := by
  obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem ha
  have hb' : b ∈ s' := (Multiset.mem_cons.1 hb).resolve_left (Ne.symm hab)
  obtain ⟨s'', rfl⟩ := Multiset.exists_cons_of_mem hb'
  rw [Multiset.cons_bind, Multiset.cons_bind] at h
  have hd := (Multiset.nodup_add.1 h).2.2
  exact fun hxb => Multiset.disjoint_left.1 hd hxa (Multiset.mem_add.2 (Or.inl hxb))

lemma labels_le_of_get? : ∀ {t u : STree T} {p : List ℕ}, t.get? p = some u →
    u.labels ≤ t.labels
  | t, u, [], h => by
    rw [get?_nil, Option.some_inj] at h
    rw [h]
  | .leaf _, _, _ :: _, h => by simp at h
  | .node e cc, u, i :: p, h => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    exact (labels_le_of_get? h).trans (labels_le_node e cc ⟨i, hi⟩)

lemma labels_subst_le : ∀ (t : STree T) {xs ys : ℕ → STree T},
    (∀ a ∈ t.labels, (xs a).labels ≤ (ys a).labels) → (t.subst xs).labels ≤ (t.subst ys).labels
  | .leaf a, _, _, h => h a (Multiset.mem_singleton_self a)
  | .node e cc, xs, ys, h => by
    rw [subst_node, subst_node, labels_node, labels_node]
    exact Finset.sum_le_sum fun i _ =>
      labels_subst_le (cc i) fun a ha => h a (mem_labels_node.2 ⟨i, ha⟩)

end Trees

/-! ## The coordinates of an ideal -/

section Coord

open STree

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)
  (I : GrOperadIdeal K (FreeGrL K E))

/-- **The coordinates of an ideal** on the leaves `Y`: the combinations of shuffle monomials
which are operations of the ideal. -/
noncomputable def IC (Y : Finset ℕ) : Submodule K (SMono T Y →₀ K) :=
  (I.sub (Lab Y)).comap
    ((labBasis c hc Y).repr.symm : (SMono T Y →₀ K) →ₗ[K] FreeGrL K E (Lab Y))

lemma mem_IC {Y : Finset ℕ} {v : SMono T Y →₀ K} :
    v ∈ IC c hc I Y ↔ (labBasis c hc Y).repr.symm v ∈ I.sub (Lab Y) := Iff.rfl

variable {Y₁ Y₂ Y : Finset ℕ}

/-- Grafting a monomial at a leaf preserves the ideal. -/
theorem mapDomain_graftR_mem (t₂ : SMono T Y₂) (i₁ : Lab Y₁) (hf : t₂.1.first = i₁.1)
    (Ψ : Without (Lab Y₁) i₁ ⊕ Lab Y₂ ≃ Lab Y) (hΨ : ∀ z, (Ψ z).1 = FreeGrL.sval z)
    {v : SMono T Y₁ →₀ K} (hv : v ∈ IC c hc I Y₁) :
    Finsupp.mapDomain (graftR t₂ i₁ hf Ψ hΨ) v ∈ IC c hc I Y := by
  have h := repr_comp_graftR c hc t₂ i₁ hf Ψ hΨ ((labBasis c hc Y₁).repr.symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [mem_IC, ← h, LinearEquiv.symm_apply_apply]
  exact I.map_mem Ψ (I.comp_mem_left i₁ _ hv)

/-- Grafting into a monomial at a leaf preserves the ideal. -/
theorem mapDomain_graftL_mem (t₁ : SMono T Y₁) (i₁ : Lab Y₁) (hi₂ : i₁.1 ∈ Y₂)
    (hmin : ∀ y ∈ Y₂, i₁.1 ≤ y) (Ψ : Without (Lab Y₁) i₁ ⊕ Lab Y₂ ≃ Lab Y)
    (hΨ : ∀ z, (Ψ z).1 = FreeGrL.sval z) {v : SMono T Y₂ →₀ K} (hv : v ∈ IC c hc I Y₂) :
    Finsupp.mapDomain (graftL t₁ i₁ hi₂ hmin Ψ hΨ) v ∈ IC c hc I Y := by
  have h := repr_comp_graftL c hc t₁ i₁ hi₂ hmin Ψ hΨ ((labBasis c hc Y₂).repr.symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [mem_IC, ← h, LinearEquiv.symm_apply_apply]
  exact I.map_mem Ψ (I.comp_mem_right i₁ _ hv)

/-- **Relabelling along an increasing map preserves the ideal.** -/
theorem mapDomain_relabelM_mem {C C' : Finset ℕ} (φ : ℕ → ℕ) (hφ : StrictMonoOn φ C)
    (himg : C.image φ = C') {v : SMono T C →₀ K} (hv : v ∈ IC c hc I C) :
    Finsupp.mapDomain (ShuffleBridge.relabelM φ hφ himg) v ∈ IC c hc I C' := by
  have hmem : ∀ x : Lab C, φ x.1 ∈ C' := fun x => himg ▸ Finset.mem_image_of_mem φ x.2
  let θ : Lab C ≃ Lab C' := Equiv.ofBijective (fun x => ⟨φ x.1, hmem x⟩)
    ⟨fun x y hxy => Subtype.ext (hφ.injOn x.2 y.2 (congrArg Subtype.val hxy)), fun y => by
      have hy : y.1 ∈ C.image φ := himg ▸ y.2
      obtain ⟨a, ha, hay⟩ := Finset.mem_image.1 hy
      exact ⟨⟨a, ha⟩, Subtype.ext hay⟩⟩
  have hrepr : ∀ x : FreeGrL K E (Lab C), (labBasis c hc C').repr (GrOperad.map (R := K) θ x)
      = Finsupp.mapDomain (ShuffleBridge.relabelM φ hφ himg) ((labBasis c hc C).repr x) := by
    have h : ((labBasis c hc C').repr : FreeGrL K E (Lab C') →ₗ[K] (SMono T C' →₀ K)) ∘ₗ
        (GrOperad.map (R := K) θ)
        = (Finsupp.lmapDomain K K (ShuffleBridge.relabelM φ hφ himg)) ∘ₗ
          ((labBasis c hc C).repr : FreeGrL K E (Lab C) →ₗ[K] (SMono T C →₀ K)) :=
      (labBasis c hc C).ext fun m => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
          Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
        have h1 : GrOperad.map (R := K) θ (labBasis c hc C m)
            = labBasis c hc C' (ShuffleBridge.relabelM φ hφ himg m) := by
          rw [labBasis, FreeGrL.shBasisLab_apply, FreeGrL.shBasisLab_apply]
          exact (FreeGrL.shEv_relabel c φ m.1 C m.2.2 C'
            (ShuffleBridge.relabelM φ hφ himg m).2.2 θ fun _ => rfl).symm
        rw [h1, Module.Basis.repr_self]
    exact fun x => LinearMap.congr_fun h x
  have h := hrepr ((labBasis c hc C).repr.symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [mem_IC, ← h, LinearEquiv.symm_apply_apply]
  exact I.map_mem θ hv

omit [IsEmpty (T 0)] in
lemma labels_bind_eq {C : Finset ℕ} (zs : ℕ → STree T) (h : SMono T C) :
    (h.1.subst zs).labels = C.val.bind fun a => (zs a).labels := by
  rw [labels_subst, h.2.2]

/-- A map of monomials which keeps the trees preserves the ideal. -/
theorem mapDomain_mem_of_val_eq {A B : Finset ℕ} (F : SMono T A → SMono T B)
    (hF : ∀ g, (F g).1 = g.1) {v : SMono T A →₀ K} (hv : v ∈ IC c hc I A) :
    Finsupp.mapDomain F v ∈ IC c hc I B := by
  rcases isEmpty_or_nonempty (SMono T A) with hA | ⟨⟨g₀⟩⟩
  · rw [Subsingleton.elim v 0, Finsupp.mapDomain_zero]
    exact zero_mem _
  · have hAB : A = B := Finset.val_inj.1
      (g₀.2.2.symm.trans ((congrArg STree.labels (hF g₀)).symm.trans (F g₀).2.2))
    subst hAB
    have hid : F = id := funext fun g => Subtype.ext (hF g)
    rw [hid, Finsupp.mapDomain_id]
    exact hv

/-- **Replacing the subtree at a position of a tree by a monomial preserves the ideal**: the
replacement is a chain of grafts into the corollas along the position. -/
theorem mapDomain_replace_mem {Y₂ : Finset ℕ} : ∀ (p : List ℕ) (U : STree T) {Y : Finset ℕ}
    (R : SMono T Y₂ → SMono T Y), (U.get? p).isSome → (∀ g, (R g).1 = U.replace p g.1) →
    ∀ {v : SMono T Y₂ →₀ K}, v ∈ IC c hc I Y₂ → Finsupp.mapDomain R v ∈ IC c hc I Y
  | [], U, Y, R, _, hR, v, hv =>
    mapDomain_mem_of_val_eq c hc I R (fun g => (hR g).trans (replace_nil _ _)) hv
  | i :: p, .leaf a, Y, R, hget, _, _, _ => by simp at hget
  | i :: p, @STree.node _ k e cc, Y, R, hget, hR, v, hv => by
    rcases isEmpty_or_nonempty (SMono T Y₂) with hE | ⟨⟨g₀⟩⟩
    · rw [Subsingleton.elim v 0, Finsupp.mapDomain_zero]
      exact zero_mem _
    obtain ⟨w₀, hw₀⟩ := Option.isSome_iff_exists.1 hget
    obtain ⟨hi, hw⟩ := get?_node_cons_eq_some.1 hw₀
    obtain ⟨i', hi'⟩ : ∃ j : Fin k, j = ⟨i, hi⟩ := ⟨_, rfl⟩
    rw [← hi'] at hw
    have hRu : ∀ g, (R g).1 = .node e (update cc i' ((cc i').replace p g.1)) := fun g => by
      rw [hR g, hi']
      exact replace_node_cons_update e cc hi p g.1
    have hsh : ∀ g : SMono T Y₂, (STree.node e (update cc i' ((cc i').replace p g.1))).IsShuffle :=
      fun g => hRu g ▸ (R g).2.1
    have hlab : ∀ g : SMono T Y₂,
        (STree.node e (update cc i' ((cc i').replace p g.1))).labels = Y.val :=
      fun g => hRu g ▸ (R g).2.2
    have hnd : (STree.node e (update cc i' ((cc i').replace p g₀.1))).labels.Nodup :=
      (hlab g₀).symm ▸ Y.nodup
    have hin_sh : ∀ g : SMono T Y₂, ((cc i').replace p g.1).IsShuffle := fun g => by
      have h := (hsh g).child i'
      rwa [update_self] at h
    have hin_nd : ((cc i').replace p g₀.1).labels.Nodup := by
      have h := nodup_of_node hnd i'
      rwa [update_self] at h
    obtain ⟨Y', hY'⟩ : ∃ Y' : Finset ℕ, Y'.val = ((cc i').replace p g₀.1).labels :=
      ⟨⟨_, hin_nd⟩, rfl⟩
    have hin_lab : ∀ g : SMono T Y₂, ((cc i').replace p g.1).labels = Y'.val := fun g => by
      have h1 := labels_replace hw g.1
      have h2 := labels_replace hw g₀.1
      rw [g.2.2] at h1
      rw [g₀.2.2] at h2
      rw [hY']
      exact add_right_cancel (h1.trans h2.symm)
    obtain ⟨R', hR'⟩ : ∃ R' : SMono T Y₂ → SMono T Y', ∀ g, (R' g).1 = (cc i').replace p g.1 :=
      ⟨fun g => ⟨(cc i').replace p g.1, hin_sh g, hin_lab g⟩, fun _ => rfl⟩
    have ih := mapDomain_replace_mem p (cc i') R' (by rw [hw]; rfl) hR' hv
    obtain ⟨a₀, ha₀⟩ : ∃ a, a = ((cc i').replace p g₀.1).first := ⟨_, rfl⟩
    have ha₀in : a₀ ∈ ((cc i').replace p g₀.1).labels := ha₀ ▸ first_mem (hin_sh g₀)
    have ha₀Y' : a₀ ∈ Y' := Finset.mem_def.2 (hY' ▸ ha₀in)
    have hmin : ∀ y ∈ Y', a₀ ≤ y := fun y hy => by
      rw [ha₀]
      exact first_le (hin_sh g₀) y (hY' ▸ Finset.mem_def.1 hy)
    have hfirst : ∀ j, (update cc i' (.leaf a₀) j).first
        = (update cc i' ((cc i').replace p g₀.1) j).first := fun j => by
      by_cases hj : j = i'
      · rw [hj, update_self, update_self, first_leaf, ha₀]
      · rw [update_of_ne hj, update_of_ne hj]
    have hout_sh : (STree.node e (update cc i' (.leaf a₀))).IsShuffle := by
      refine ⟨(hsh g₀).pos, fun j => ?_, fun a b hab => ?_⟩
      · by_cases hj : j = i'
        · rw [hj, update_self]
          trivial
        · rw [update_of_ne hj]
          have h := (hsh g₀).child j
          rwa [update_of_ne hj] at h
      · show (update cc i' (.leaf a₀) a).first < (update cc i' (.leaf a₀) b).first
        rw [hfirst, hfirst]
        exact (hsh g₀).mono hab
    have hout_le : (STree.node e (update cc i' (.leaf a₀))).labels
        ≤ (STree.node e (update cc i' ((cc i').replace p g₀.1))).labels := by
      rw [labels_node, labels_node]
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hj : j = i'
      · rw [hj, update_self, update_self, labels_leaf]
        exact Multiset.singleton_le.2 ha₀in
      · rw [update_of_ne hj, update_of_ne hj]
    obtain ⟨Y₁, hY₁⟩ : ∃ Y₁ : Finset ℕ,
        (STree.node e (update cc i' (.leaf a₀))).labels = Y₁.val :=
      ⟨⟨_, Multiset.nodup_of_le hout_le hnd⟩, rfl⟩
    have hdisj : ∀ j, j ≠ i' → ∀ x ∈ (cc j).labels, x ∉ Y' := fun j hj x hx hx' => by
      have h1 : x ∈ (update cc i' ((cc i').replace p g₀.1) j).labels := by
        rwa [update_of_ne hj]
      have h2 := not_mem_of_node hnd hj h1
      rw [update_self] at h2
      exact h2 (hY' ▸ Finset.mem_def.1 hx')
    have hmemY₁ : ∀ x, x ∈ Y₁ ↔ x = a₀ ∨ ∃ j, j ≠ i' ∧ x ∈ (cc j).labels := fun x => by
      rw [← Finset.mem_val, ← hY₁, mem_labels_node]
      constructor
      · rintro ⟨j, hj⟩
        by_cases hji : j = i'
        · rw [hji, update_self, labels_leaf, Multiset.mem_singleton] at hj
          exact Or.inl hj
        · rw [update_of_ne hji] at hj
          exact Or.inr ⟨j, hji, hj⟩
      · rintro (h | ⟨j, hji, hj⟩)
        · exact ⟨i', by rw [update_self, h]; exact Multiset.mem_singleton_self _⟩
        · exact ⟨j, by rwa [update_of_ne hji]⟩
    have hmemY : ∀ x, x ∈ Y ↔ x ∈ Y' ∨ ∃ j, j ≠ i' ∧ x ∈ (cc j).labels := fun x => by
      rw [← Finset.mem_val, ← hlab g₀, mem_labels_node]
      constructor
      · rintro ⟨j, hj⟩
        by_cases hji : j = i'
        · rw [hji, update_self, ← hY'] at hj
          exact Or.inl (Finset.mem_def.2 hj)
        · rw [update_of_ne hji] at hj
          exact Or.inr ⟨j, hji, hj⟩
      · rintro (h | ⟨j, hji, hj⟩)
        · exact ⟨i', by rw [update_self, ← hY']; exact Finset.mem_def.1 h⟩
        · exact ⟨j, by rwa [update_of_ne hji]⟩
    have ha₀Y₁ : a₀ ∈ Y₁ := (hmemY₁ a₀).2 (Or.inl rfl)
    obtain ⟨Ψ, hΨ⟩ := FreeGrL.exists_svalEquiv (Y₁ := Y₁) (Y₂ := Y') (Y := Y) ⟨a₀, ha₀Y₁⟩
      (fun x hx hne hx' => by
        rcases (hmemY₁ x).1 hx with h | ⟨j, hji, hj⟩
        · exact hne h
        · exact hdisj j hji x hj hx')
      (fun x => by
        rw [hmemY, hmemY₁]
        constructor
        · rintro (h | ⟨j, hji, hj⟩)
          · exact Or.inr h
          · exact Or.inl ⟨Or.inr ⟨j, hji, hj⟩, fun h => hdisj j hji x hj (h ▸ ha₀Y')⟩
        · rintro (⟨h | h, hne⟩ | h)
          · exact absurd h hne
          · exact Or.inr h
          · exact Or.inl h)
    let t₁ : SMono T Y₁ := ⟨.node e (update cc i' (.leaf a₀)), hout_sh, hY₁⟩
    have hfac : R = graftL t₁ ⟨a₀, ha₀Y₁⟩ ha₀Y' hmin Ψ hΨ ∘ R' :=
      funext fun g => Subtype.ext (by
        rw [hRu g]
        show _ = (STree.node e (update cc i' (.leaf a₀))).subst
          (update STree.leaf a₀ (R' g).1)
        rw [hR' g]
        exact (subst_node_update_leaf e cc i' a₀
          (fun j hj ha => hdisj j hj a₀ ha ha₀Y') _).symm)
    rw [hfac, Finsupp.mapDomain_comp]
    exact mapDomain_graftL_mem c hc I t₁ ⟨a₀, ha₀Y₁⟩ ha₀Y' hmin Ψ hΨ ih

/-- **Substituting monomials for the leaves of a monomial preserves the ideal**, when the tree
substituted for a leaf has that leaf for least leaf: the substitution is a chain of grafts, one
for each leaf of `S`. -/
theorem mapDomain_subst_mem {C : Finset ℕ} (S : Finset ℕ) : ∀ (ys : ℕ → STree T) {Y : Finset ℕ}
    (F : SMono T C → SMono T Y), (∀ b ∈ C, b ∉ S → ys b = .leaf b) →
    (∀ b ∈ C, (ys b).IsShuffle) → (∀ b ∈ C, (ys b).first = b) →
    (∀ h, (F h).1 = h.1.subst ys) →
    ∀ {v : SMono T C →₀ K}, v ∈ IC c hc I C → Finsupp.mapDomain F v ∈ IC c hc I Y := by
  induction S using Finset.induction_on with
  | empty =>
    intro ys Y F hS _ _ hF v hv
    exact mapDomain_mem_of_val_eq c hc I F (fun h => (hF h).trans
      (subst_eq_self fun a ha => hS a (h.mem_labels.1 ha) (Finset.notMem_empty a))) hv
  | insert b₀ S hb₀ ih =>
    intro ys Y F hS hsh hfst hF v hv
    by_cases hb₀C : b₀ ∈ C
    swap
    · exact ih ys F (fun b hb hbS => hS b hb fun h =>
        (Finset.mem_insert.1 h).elim (fun h' => hb₀C (h' ▸ hb)) hbS) hsh hfst hF hv
    rcases isEmpty_or_nonempty (SMono T C) with hE | ⟨⟨h₀⟩⟩
    · rw [Subsingleton.elim v 0, Finsupp.mapDomain_zero]
      exact zero_mem _
    have hnd : (C.val.bind fun a => (ys a).labels).Nodup := by
      rw [← labels_bind_eq ys h₀, ← hF h₀, (F h₀).2.2]
      exact Y.nodup
    have hdisj : ∀ a ∈ C, a ≠ b₀ → ∀ x ∈ (ys a).labels, x ∉ (ys b₀).labels :=
      fun a ha hab x hx => disjoint_of_nodup_bind hnd (Finset.mem_def.1 ha)
        (Finset.mem_def.1 hb₀C) hab hx
    have hb₀mem : b₀ ∈ (ys b₀).labels := by
      have h := first_mem (hsh b₀ hb₀C)
      rwa [hfst b₀ hb₀C] at h
    obtain ⟨ys', hy1, hy2⟩ : ∃ z : ℕ → STree T, z b₀ = .leaf b₀ ∧ ∀ a, a ≠ b₀ → z a = ys a :=
      ⟨update ys b₀ (.leaf b₀), update_self .., fun a ha => update_of_ne ha ..⟩
    have hys'le : ∀ a, (ys' a).labels ≤ (ys a).labels := fun a => by
      by_cases ha : a = b₀
      · rw [ha, hy1, labels_leaf]
        exact Multiset.singleton_le.2 hb₀mem
      · rw [hy2 a ha]
    have hnd' : (h₀.1.subst ys').labels.Nodup :=
      Multiset.nodup_of_le (labels_subst_le h₀.1 fun a _ => hys'le a)
        (by rw [labels_bind_eq]; exact hnd)
    obtain ⟨Y', hY'⟩ : ∃ Y' : Finset ℕ, Y'.val = (h₀.1.subst ys').labels := ⟨⟨_, hnd'⟩, rfl⟩
    have hsh' : ∀ b ∈ C, (ys' b).IsShuffle := fun b hb => by
      by_cases h : b = b₀
      · rw [h, hy1]
        trivial
      · rw [hy2 b h]
        exact hsh b hb
    have hfst' : ∀ b ∈ C, (ys' b).first = b := fun b hb => by
      by_cases h : b = b₀
      · rw [h, hy1, first_leaf]
      · rw [hy2 b h]
        exact hfst b hb
    obtain ⟨F', hF'⟩ : ∃ F' : SMono T C → SMono T Y', ∀ h, (F' h).1 = h.1.subst ys' :=
      ⟨fun h => ⟨h.1.subst ys',
        isShuffle_subst h.2.1 (fun a ha => hsh' a (h.mem_labels.1 ha)) (fun a ha b hb hab => by
          show (ys' a).first < (ys' b).first
          rw [hfst' a (h.mem_labels.1 ha), hfst' b (h.mem_labels.1 hb)]
          exact hab),
        by rw [hY', labels_bind_eq, labels_bind_eq]⟩, fun _ => rfl⟩
    have ih' := ih ys' F' (fun b hb hbS => by
      by_cases h : b = b₀
      · rw [h, hy1]
      · rw [hy2 b h]
        exact hS b hb fun h' => (Finset.mem_insert.1 h').elim h hbS) hsh' hfst' hF' hv
    have hndZ : (ys b₀).labels.Nodup :=
      Multiset.nodup_of_le
        (Multiset.le_bind (f := fun a => (ys a).labels) C.val (Finset.mem_def.1 hb₀C)) hnd
    obtain ⟨Z, hZ⟩ : ∃ Z : Finset ℕ, (ys b₀).labels = Z.val := ⟨⟨_, hndZ⟩, rfl⟩
    have hmemY' : ∀ x, x ∈ Y' ↔ x = b₀ ∨ ∃ a ∈ C, a ≠ b₀ ∧ x ∈ (ys a).labels := fun x => by
      rw [← Finset.mem_val, hY', labels_bind_eq, Multiset.mem_bind]
      constructor
      · rintro ⟨a, ha, hx⟩
        by_cases h : a = b₀
        · rw [h, hy1, labels_leaf, Multiset.mem_singleton] at hx
          exact Or.inl hx
        · rw [hy2 a h] at hx
          exact Or.inr ⟨a, Finset.mem_def.2 ha, h, hx⟩
      · rintro (h | ⟨a, ha, hab, hx⟩)
        · exact ⟨b₀, Finset.mem_def.1 hb₀C, by rw [hy1, h]; exact Multiset.mem_singleton_self _⟩
        · exact ⟨a, Finset.mem_def.1 ha, by rwa [hy2 a hab]⟩
    have hmemY : ∀ x, x ∈ Y ↔ ∃ a ∈ C, x ∈ (ys a).labels := fun x => by
      rw [← Finset.mem_val, ← (F h₀).2.2, hF h₀, labels_bind_eq, Multiset.mem_bind]
      exact Iff.rfl
    have hb₀Y' : b₀ ∈ Y' := (hmemY' b₀).2 (Or.inl rfl)
    obtain ⟨Ψ, hΨ⟩ := FreeGrL.exists_svalEquiv (Y₁ := Y') (Y₂ := Z) (Y := Y) ⟨b₀, hb₀Y'⟩
      (fun x hx hne hz => by
        rcases (hmemY' x).1 hx with h | ⟨a, ha, hab, hxa⟩
        · exact hne h
        · exact hdisj a ha hab x hxa (hZ ▸ Finset.mem_def.1 hz))
      (fun x => by
        rw [hmemY]
        constructor
        · rintro ⟨a, ha, hxa⟩
          by_cases h : a = b₀
          · exact Or.inr (Finset.mem_def.2 (hZ ▸ h ▸ hxa))
          · exact Or.inl ⟨(hmemY' x).2 (Or.inr ⟨a, ha, h, hxa⟩),
              fun hxb => hdisj a ha h x hxa (hxb ▸ hb₀mem)⟩
        · rintro (⟨hx, hne⟩ | hz)
          · rcases (hmemY' x).1 hx with h | ⟨a, ha, _, hxa⟩
            · exact absurd h hne
            · exact ⟨a, ha, hxa⟩
          · exact ⟨b₀, hb₀C, hZ ▸ Finset.mem_def.1 hz⟩)
    let t₂ : SMono T Z := ⟨ys b₀, hsh b₀ hb₀C, hZ⟩
    have hfac : F = graftR t₂ ⟨b₀, hb₀Y'⟩ (hfst b₀ hb₀C) Ψ hΨ ∘ F' :=
      funext fun h => Subtype.ext (by
        rw [hF h]
        show h.1.subst ys = (F' h).1.subst (update STree.leaf b₀ (ys b₀))
        rw [hF' h, subst_subst]
        refine subst_congr h.1 fun a ha => ?_
        show ys a = (ys' a).subst (update STree.leaf b₀ (ys b₀))
        by_cases hab : a = b₀
        · rw [hab, hy1, subst_leaf', update_self]
        · rw [hy2 a hab]
          exact (subst_eq_self fun x hx => update_of_ne
            (fun hxb : x = b₀ => hdisj a (h.mem_labels.1 ha) hab x hx (hxb ▸ hb₀mem)) _ _).symm)
    rw [hfac, Finsupp.mapDomain_comp]
    exact mapDomain_graftR_mem c hc I t₂ ⟨b₀, hb₀Y'⟩ (hfst b₀ hb₀C) Ψ hΨ ih'

/-- **Contexts preserve the ideals of the free operad**: a context of shuffle monomials is an
increasing relabelling, then a substitution at the leaves, then a replacement at a position, and
each of the three is a chain of partial compositions and a relabelling. -/
theorem mapDomain_mem_IC {C Y : Finset ℕ} {f : SMono T C → SMono T Y} (hf : IsSCtx f)
    {v : SMono T C →₀ K} (hv : v ∈ IC c hc I C) : Finsupp.mapDomain f v ∈ IC c hc I Y := by
  rcases isEmpty_or_nonempty (SMono T C) with hE | ⟨⟨ℓ⟩⟩
  · rw [Subsingleton.elim v 0, Finsupp.mapDomain_zero]
    exact zero_mem _
  obtain ⟨p, xs, hget, hin, hrep⟩ := hf.normal ℓ
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℕ → ℕ, ∀ a, φ a = (xs a).first := ⟨_, fun _ => rfl⟩
  have hφ : StrictMonoOn φ (C : Set ℕ) := fun a ha b hb hab => by
    rw [hφdef, hφdef]
    exact hin.mono ha hb hab
  obtain ⟨ys, hys⟩ : ∃ ys : ℕ → STree T, ∀ a ∈ C, ys (φ a) = xs a :=
    ⟨fun b => xs (invFunOn φ (C : Set ℕ) b), fun a ha => by
      show xs (invFunOn φ (C : Set ℕ) (φ a)) = xs a
      rw [hφ.injOn.leftInvOn_invFunOn (Finset.mem_coe.2 ha)]⟩
  obtain ⟨C', hC'⟩ : ∃ C', C.image φ = C' := ⟨_, rfl⟩
  have hmemC' : ∀ b ∈ C', ∃ a ∈ C, φ a = b := fun b hb => by
    rw [← hC'] at hb
    exact Finset.mem_image.1 hb
  have hsub : ∀ g : SMono T C,
      (ShuffleBridge.relabelM φ hφ hC' g).1.subst ys = g.1.subst xs := fun g => by
    show (g.1.relabel φ).subst ys = _
    rw [STree.relabel, subst_subst]
    exact subst_congr g.1 fun a ha => hys a (g.mem_labels.1 ha)
  have hnd₂ : (ℓ.1.subst xs).labels.Nodup :=
    Multiset.nodup_of_le (labels_le_of_get? hget) (by rw [(f ℓ).2.2]; exact Y.nodup)
  obtain ⟨Y₂, hY₂⟩ : ∃ Y₂ : Finset ℕ, (ℓ.1.subst xs).labels = Y₂.val := ⟨⟨_, hnd₂⟩, rfl⟩
  have hysh : ∀ b ∈ C', (ys b).IsShuffle := fun b hb => by
    obtain ⟨a, ha, rfl⟩ := hmemC' b hb
    rw [hys a ha]
    exact hin.shuffle a ha
  have hyfst : ∀ b ∈ C', (ys b).first = b := fun b hb => by
    obtain ⟨a, ha, rfl⟩ := hmemC' b hb
    rw [hys a ha, hφdef]
  have hMlab : ∀ h : SMono T C', (h.1.subst ys).labels = Y₂.val := fun h => by
    rw [← hY₂, ← hsub ℓ, labels_bind_eq, labels_bind_eq]
  obtain ⟨M, hM⟩ : ∃ M : SMono T C' → SMono T Y₂, ∀ h, (M h).1 = h.1.subst ys :=
    ⟨fun h => ⟨h.1.subst ys,
      isShuffle_subst h.2.1 (fun a ha => hysh a (h.mem_labels.1 ha)) (fun a ha b hb hab => by
        show (ys a).first < (ys b).first
        rw [hyfst a (h.mem_labels.1 ha), hyfst b (h.mem_labels.1 hb)]
        exact hab), hMlab h⟩, fun _ => rfl⟩
  have hRsh : ∀ g : SMono T Y₂, ((f ℓ).1.replace p g.1).IsShuffle := fun g =>
    isShuffle_replace (f ℓ).2.1 hget g.2.1
      (first_eq_of_labels_eq g.2.1 (hin.subst_isShuffle ℓ) (g.2.2.trans hY₂.symm))
  obtain ⟨R, hR⟩ : ∃ R : SMono T Y₂ → SMono T Y, ∀ g, (R g).1 = (f ℓ).1.replace p g.1 :=
    ⟨fun g => ⟨(f ℓ).1.replace p g.1, hRsh g,
      (labels_replace_of_eq hget (g.2.2.trans hY₂.symm)).trans (f ℓ).2.2⟩, fun _ => rfl⟩
  have hfac : f = R ∘ M ∘ ShuffleBridge.relabelM φ hφ hC' := funext fun g => Subtype.ext (by
    show (f g).1 = (R (M (ShuffleBridge.relabelM φ hφ hC' g))).1
    rw [hR, hM, hsub g, hrep g])
  rw [hfac, Finsupp.mapDomain_comp, Finsupp.mapDomain_comp]
  refine mapDomain_replace_mem c hc I p (f ℓ).1 R (by rw [hget]; rfl) hR ?_
  refine mapDomain_subst_mem c hc I C' ys M (fun b hb hnb => absurd hb hnb) hysh hyfst hM ?_
  exact mapDomain_relabelM_mem c hc I φ hφ hC' hv

end Coord

/-! ## The ideal of the rules lies in the ideal of the relators -/

section Converse

open STree

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))
  {ρ : Type*} {O : STree.AdmOrder T} (G : Rules K ρ O.toCtxOrder)
  (hrS : ∀ n (σ : Equiv.Perm (Fin n)), ∀ x ∈ r n,
    GrOperad.map (R := K) σ x ∈ Submodule.span K (r n))
  (hG : ∀ n, ∀ x ∈ r n, (tBasisN c hc n).repr x ∈ (G.rw (Finset.range n)).ideal)
  (hG1 : ∀ i, (labBasis c hc (G.src i)).repr.symm (Finsupp.single (G.lead i) 1 - G.tail i)
    ∈ (GrOperadIdeal.span K r).sub (Lab (G.src i)))

include hG1 in
/-- **The ideal of the rules lies in the coordinates of the ideal of the relators**, when each
rule is a relation of the presented operad. -/
theorem ideal_le_IC (Y : Finset ℕ) : (G.rw Y).ideal ≤ IC c hc (GrOperadIdeal.span K r) Y := by
  rw [G.ideal_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, f, hf, rfl⟩
  exact mapDomain_mem_IC c hc _ hf (hG1 i)

include hG1 in
/-- **An operation whose coordinates lie in the ideal of the rules is in the ideal of the
relators.** -/
theorem mem_span_of_repr_mem_ideal {k : ℕ} {y : FreeGrL K E (Fin k)}
    (hy : (tBasisN c hc k).repr y ∈ (G.rw (Finset.range k)).ideal) :
    y ∈ (GrOperadIdeal.span K r).sub (Fin k) := by
  have h1 := ideal_le_IC c hc r G hG1 (Finset.range k) hy
  rw [← repr_map_idLab c hc k y, mem_IC, LinearEquiv.symm_apply_apply] at h1
  have h2 := (GrOperadIdeal.span K r).map_mem (idLab k).symm h1
  rwa [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl] at h2

include hrS hG hG1 in
/-- **The ideal of the relators is the ideal of the rules, in shuffle coordinates**: for relators
stable under the symmetric groups whose coordinates lie in the ideal of the rules, and rules
which are relations of the presented operad, an operation is in the ideal of the relators iff
its coordinates in the basis of the shuffle trees lie in the ideal of the rules. -/
theorem mem_span_iff_repr_mem_ideal (k : ℕ) (y : FreeGrL K E (Fin k)) :
    y ∈ (GrOperadIdeal.span K r).sub (Fin k) ↔
      (tBasisN c hc k).repr y ∈ (G.rw (Finset.range k)).ideal :=
  ⟨repr_mem_ideal_of_mem_span c hc r G hrS hG, mem_span_of_repr_mem_ideal c hc r G hG1⟩

variable [IsEmpty (T 1)]
  (hlead : ∀ i a, (G.lead i).1 ≠ .leaf a)
  (hom : ∀ i, ∀ m ∈ (G.tail i).support, m.1.weight = (G.lead i).1.weight)

include hlead hom hrS hG hG1 in
/-- **The bridge for generators of any arity, from the relators and the rules**: for an even
graded linear species `E` with a basis indexed by `T`, without generators in arities zero and
one, over a field of characteristic zero, quadratic relators `r` stable under the symmetric
groups, and homogeneous rules `G` on shuffle monomials such that the coordinates of each relator
lie in the ideal of the rules and each rule is a relation of `T(E)/(r)`, the presented operad
`T(E)/(r)` is Koszul iff the shuffle operad presented by the rules is (`Rules.IsKoszul`). -/
theorem isKoszul_iff_rules_of_stable [CharZero K] (hq : Koszul.IsQuadratic K E r) :
    Koszul.IsKoszul K E r ↔ G.IsKoszul :=
  isKoszul_iff_rules c hc r G hlead hom (mem_span_iff_repr_mem_ideal c hc r G hrS hG hG1) hq

end Converse

end ShuffleAnySym

end Operad
