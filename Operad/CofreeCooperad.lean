/-
# The cofree conilpotent cooperad

The free set operad `FreeSet T` on generators of any arity has finite factorizations: it is the
regular operad of planar trees (`FreeReg.regIso`), and a planar tree is a graft `s ∘ₚ u` in
finitely many ways, all listed by `Tree.cuts` (`Tree.mem_cuts`). Its number of vertices is a
connected weight. So its decomposition cooperad, which cuts a tree in all possible ways,

  `Cofree R T = Lin R (FreeSet T)`,   `Δᵢ t = ∑_{t = p ∘ᵢ q} p ⊗ q`,

is coaugmented by the trivial tree and conilpotent (`Operad.Conilpotent`). It is **the cofree
conilpotent cooperad** on the cogenerators `T`: for a conilpotent cooperad `C`, a morphism of
coaugmented cooperads `C → Cofree R T` is the same as a family of linear maps
`C (Fin k) → R[T k]` killing the coaugmentation, by composing with the projection on the
corollas (`Cofree.homEquiv`).

The proof transposes. A morphism into a decomposition cooperad is a locally finite morphism of
set operads from `FreeSet T` to the dual operad `C*` (`Lin.coHomEquiv`), so by the universal
property of the free operad it is determined by the values on the generators, and the point is
that **on a conilpotent cooperad every family of generator values is locally finite**
(`Cofree.locallyFinite`): a tree with at least two vertices factors as a composite of two
nontrivial trees (`FreeSet.cases`), it pairs with a cooperation in the stage `n + 1` of the
coradical filtration through decompositions in `Fₙ ⊗ Fₙ`, and induction on `n` bounds the trees
pairing nontrivially with it.
-/
import Operad.Conilpotent
import Operad.PlanarFree

universe u v w

namespace Operad

open scoped TensorProduct

open Sym NSSetOperad

/-! ## Cutting planar trees -/

namespace Tree

variable {E : ℕ → Type v}

mutual

/-- **All the ways to cut a tree at a position**: the pairs `(s, u)` with `s.graft p u = t`, for
`p` a leaf of `s` (`mem_cuts`). -/
def cuts : Tree E → ℕ → List (Tree E × Tree E)
  | .leaf, p => if p = 0 then [(.leaf, .leaf)] else []
  | .node e f, p => (if p = 0 then [(.leaf, .node e f)] else []) ++
      (Forest.cutsF f p).map fun fu => (.node e fu.1, fu.2)

/-- The forest half of `cuts`. -/
def _root_.Operad.Forest.cutsF : ∀ {k : ℕ}, Forest E k → ℕ → List (Forest E k × Tree E)
  | _, .nil, _ => []
  | _, .cons t f, p =>
      ((cuts t p).filter fun su => decide (p < su.1.arity)).map (fun su => (.cons su.1 f, su.2)) ++
      (if t.arity ≤ p then (Forest.cutsF f (p - t.arity)).map fun fu => (.cons t fu.1, fu.2)
        else [])

end

mutual

/-- Every graft at a leaf is listed among the cuts of the result. -/
theorem mem_cuts : ∀ (s : Tree E) (p : ℕ) (u : Tree E), p < s.arity →
    (s, u) ∈ cuts (s.graft p u) p
  | .leaf, p, u, h => by
      obtain rfl : p = 0 := by simpa using h
      cases u with
      | leaf => simp [cuts]
      | node e f => simp [cuts]
  | .node e f, p, u, h => by
      simp only [graft_node, cuts, List.mem_append, List.mem_map]
      exact Or.inr ⟨(f, u), Forest.mem_cutsF f p u h, rfl⟩

/-- The forest half of `mem_cuts`. -/
theorem _root_.Operad.Forest.mem_cutsF : ∀ {k : ℕ} (f : Forest E k) (p : ℕ) (u : Tree E),
    p < f.arityF → (f, u) ∈ Forest.cutsF (f.graftF p u) p
  | _, .nil, _, _, h => by simp at h
  | _, .cons t f, p, u, h => by
      simp only [arityF_cons] at h
      by_cases hlt : p < t.arity
      · rw [graftF_cons_of_lt u hlt]
        simp only [Forest.cutsF, List.mem_append, List.mem_map, List.mem_filter,
          decide_eq_true_eq]
        exact Or.inl ⟨(t, u), ⟨mem_cuts t p u hlt, hlt⟩, rfl⟩
      · rw [graftF_cons_of_ge u (by omega)]
        simp only [Forest.cutsF, List.mem_append]
        rw [if_pos (by omega)]
        exact Or.inr (List.mem_map.2
          ⟨(f, u), Forest.mem_cutsF f (p - t.arity) u (by omega), rfl⟩)

end

/-- **A planar tree is a graft at a given position in finitely many ways.** -/
theorem finite_graft_fiber (t : Tree E) (p : ℕ) :
    {su : Tree E × Tree E | p < su.1.arity ∧ su.1.graft p su.2 = t}.Finite :=
  (cuts t p).finite_toSet.subset fun ⟨s, u⟩ ⟨h, ht⟩ => ht ▸ mem_cuts s p u h

end Tree

/-! ## Finite factorizations of the free operad -/

namespace SetOperad.FiniteFact

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {S' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S']

/-- Finite factorizations pull back along a morphism with injective components. -/
theorem of_injective [FiniteFact S'] (φ : SetOperadHom S S')
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Injective (φ.app A)) :
    FiniteFact S where
  finite {A B} _ _ _ _ i x := by
    have hinj : Function.Injective (Prod.map (φ.app A) (φ.app B)) := fun a b h =>
      Prod.ext (hφ A (congrArg Prod.fst h)) (hφ B (congrArg Prod.snd h))
    refine ((FiniteFact.finite i (φ.app _ x)).preimage
      (Set.injOn_of_injective hinj)).subset fun pq hpq => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hpq ⊢
    rw [Prod.map_fst, Prod.map_snd, ← φ.app_comp, hpq]

end SetOperad.FiniteFact

namespace TreeOfArity

variable {T : ℕ → Type v}

lemma arr_eq_toArr (X : Arr (TreeOfArity T)) : X = toArr X.2.1 :=
  arr_ext rfl

/-- The tree of a composite of planar operations is the graft of their trees. -/
lemma arr_comp_tree (X Y : Arr (TreeOfArity T)) {r : ℕ} (hr : r < X.1) :
    (Arr.comp X r Y).2.1 = X.2.1.graft r Y.2.1 := by
  have hr' : r < X.2.1.arity := by rw [X.2.2]; exact hr
  rw [arr_eq_toArr X, arr_eq_toArr Y, toArr_comp _ _ _ hr']
  rfl

end TreeOfArity

namespace FreeReg

open TreeOfArity

variable {T : ℕ → Type v}

/-- **The regular operad of planar trees has finite factorizations.** -/
instance instFiniteFactReg : SetOperad.FiniteFact (Reg (TreeOfArity T)) where
  finite {A B} _ _ _ _ i z := by
    let g : Reg (TreeOfArity T) A × Reg (TreeOfArity T) B →
        (LinOrd A × LinOrd B) × (Tree T × Tree T) := fun xy =>
      ((xy.1.1, xy.2.1), (xy.1.2.1.2.1, xy.2.2.1.2.1))
    have hg : Function.Injective g := by
      rintro ⟨x, y⟩ ⟨x', y'⟩ h
      simp only [g, Prod.mk.injEq] at h
      exact Prod.ext (Reg.ext h.1.1 (arr_ext h.2.1)) (Reg.ext h.1.2 (arr_ext h.2.2))
    have hfin : (Set.univ ×ˢ ⋃ r ∈ Finset.range (Fintype.card A),
        {su : Tree T × Tree T | r < su.1.arity ∧ su.1.graft r su.2 = z.2.1.2.1}).Finite :=
      (Set.finite_univ (α := LinOrd A × LinOrd B)).prod
        (Set.Finite.biUnion (Finset.finite_toSet _) fun r _ => Tree.finite_graft_fiber _ r)
    refine (hfin.preimage (Set.injOn_of_injective hg)).subset fun ⟨x, y⟩ hxy => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxy
    refine ⟨Set.mem_univ _, Set.mem_iUnion₂.2 ⟨x.1.rank i, ?_, ?_, ?_⟩⟩
    · exact Finset.mem_coe.2 (Finset.mem_range.2 (LinOrd.rank_lt_card _ _))
    · show x.1.rank i < x.2.1.2.1.arity
      rw [x.2.1.2.2]
      exact Reg.rank_lt x i
    · show x.2.1.2.1.graft (x.1.rank i) y.2.1.2.1 = z.2.1.2.1
      rw [← hxy, ← arr_comp_tree _ _ (Reg.rank_lt x i)]
      rfl

/-- The comparison with the regular operad of trees is injective. -/
lemma toReg_injective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective ((toReg (T := T)).app A) :=
  (regIso.equiv A).injective

/-- **The free set operad on generators of any arity has finite factorizations.** -/
instance instFiniteFactFreeSet : SetOperad.FiniteFact (FreeSet T) :=
  SetOperad.FiniteFact.of_injective toReg toReg_injective

/-- The generators of the free set operad are distinct. -/
lemma gen_injective (k : ℕ) :
    Function.Injective (Pres.gen (ρ := fun _ _ => False) : T k → FreeSet T (Fin k)) := by
  intro g g' h
  have h2 := congrArg (fun x => (x.2.1 : Arr (TreeOfArity T)).2.1) (congrArg (toReg.app (Fin k)) h)
  simp only [toReg_gen, Reg.std, corolla] at h2
  simpa using h2

end FreeReg

/-! ## Units in a set operad -/

namespace SetOperad

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Composing into a relabelled identity relabels. -/
lemma comp_unit_left (i : A) (e : Unit ≃ A) (y : S B) :
    ∃ E : B ≃ Without A i ⊕ B, comp i (map e one) y = map E y := by
  refine ⟨(leftUnitEquiv B).symm.trans (compEquiv e.symm (Equiv.refl B) i).symm, ?_⟩
  have h := map_comp e.symm (Equiv.refl B) i (map e one) y
  rw [map_symm_map, map_refl] at h
  have h' : comp (e.symm i) one y = map (leftUnitEquiv B).symm y := by
    rw [← one_comp y, map_symm_map, one_comp]
  rw [map_trans, ← h', ← h, map_symm_map]

/-- Composing a relabelled identity relabels. -/
lemma comp_unit_right (i : A) (x : S A) (e : Unit ≃ B) :
    ∃ E : A ≃ Without A i ⊕ B, comp i x (map e one) = map E x := by
  refine ⟨(rightUnitEquiv ((Equiv.refl A) i)).symm.trans
    (compEquiv (Equiv.refl A) e.symm i).symm, ?_⟩
  have h := map_comp (Equiv.refl A) e.symm i x (map e one)
  rw [map_symm_map, map_refl] at h
  have h' : comp ((Equiv.refl A) i) x one = map (rightUnitEquiv ((Equiv.refl A) i)).symm x := by
    rw [← comp_one ((Equiv.refl A) i) x, map_symm_map, comp_one]
  rw [map_trans, ← h', ← h, map_symm_map]

/-- A composite of relabelled identities is a relabelled identity. -/
lemma comp_unit_unit (i : A) (e₁ : Unit ≃ A) (e₂ : Unit ≃ B) :
    ∃ E : Unit ≃ Without A i ⊕ B, comp i (map e₁ one) (map e₂ one) = map E (one : S Unit) := by
  obtain ⟨E, hE⟩ := comp_unit_left i e₁ (map e₂ (one : S Unit))
  exact ⟨e₂.trans E, by rw [hE, map_trans]⟩

end SetOperad

/-! ## The number of vertices -/

namespace FreeSet

open SetOperad.ConnectedWeight

variable {T : ℕ → Type v} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The number of vertices** of a tree. -/
def vertices : SetOperadHom (FreeSet T) WtOp :=
  FreeSet.homEquiv.symm fun _ _ => (1 : ℕ)

@[simp] lemma vertices_gen {k : ℕ} (g : T k) :
    vertices.app (Fin k) (Pres.gen g : FreeSet T (Fin k)) = 1 :=
  rfl

lemma eq_unit_of_vertices (s : Syn T A) (h : vertices.app A (Pres.mk s : FreeSet T A) = 0) :
    ∃ e : Unit ≃ A, (Pres.mk s : FreeSet T A) = SetOperad.map e SetOperad.one := by
  induction s with
  | one => exact ⟨Equiv.refl _, (SetOperad.map_refl _).symm⟩
  | gen g => exact absurd h one_ne_zero
  | map e s ih =>
    rw [← Pres.map_mk, vertices.app_map] at h
    obtain ⟨e', he'⟩ := ih h
    exact ⟨e'.trans e, by rw [← Pres.map_mk, he', SetOperad.map_trans]⟩
  | comp i s s' ih ih' =>
    rw [← Pres.comp_mk, vertices.app_comp] at h
    obtain ⟨e₁, he₁⟩ := ih (Nat.eq_zero_of_add_eq_zero_right h)
    obtain ⟨e₂, he₂⟩ := ih' (Nat.eq_zero_of_add_eq_zero_left h)
    rw [← Pres.comp_mk, he₁, he₂]
    exact SetOperad.comp_unit_unit i e₁ e₂

/-- **The number of vertices is a connected weight**: the trees without vertices are the
relabellings of the trivial tree. -/
instance instConnectedWeight : SetOperad.ConnectedWeight (FreeSet T) where
  wt := vertices
  eq_unit t h := by
    obtain ⟨s, rfl⟩ := Pres.mk_surjective t
    exact eq_unit_of_vertices s h

lemma w_gen {k : ℕ} (g : T k) : w (Pres.gen g : FreeSet T (Fin k)) = 1 :=
  rfl

lemma gen_ne_unit {k : ℕ} (g : T k) (e : Unit ≃ Fin k) :
    (Pres.gen g : FreeSet T (Fin k)) ≠ SetOperad.map e SetOperad.one := fun h => by
  have := congrArg w h
  rw [w_map, w_one, w_gen] at this
  exact one_ne_zero this

/-! ## The shape of a tree -/

/-- **The shapes of trees**: a relabelled trivial tree, a relabelled corolla, or a relabelled
composite of two trees with vertices. -/
def Shape (t : FreeSet T A) : Prop :=
  (∃ e : Unit ≃ A, t = SetOperad.map e SetOperad.one) ∨
  (∃ (k : ℕ) (g : T k) (e : Fin k ≃ A), t = SetOperad.map e (Pres.gen g)) ∨
  (∃ (a b : ℕ) (i : Fin a) (p : FreeSet T (Fin a)) (q : FreeSet T (Fin b))
    (e : Without (Fin a) i ⊕ Fin b ≃ A), w p ≠ 0 ∧ w q ≠ 0 ∧
      t = SetOperad.map e (SetOperad.comp i p q))

lemma Shape.map {t : FreeSet T A} (h : Shape t) (E : A ≃ B) : Shape (SetOperad.map E t) := by
  rcases h with ⟨e, rfl⟩ | ⟨k, g, e, rfl⟩ | ⟨a, b, i, p, q, e, hp, hq, rfl⟩
  · exact Or.inl ⟨e.trans E, (SetOperad.map_trans _ _ _).symm⟩
  · exact Or.inr (Or.inl ⟨k, g, e.trans E, (SetOperad.map_trans _ _ _).symm⟩)
  · exact Or.inr (Or.inr ⟨a, b, i, p, q, e.trans E, hp, hq, (SetOperad.map_trans _ _ _).symm⟩)

/-- **Every tree has a shape**: it is trivial, a corolla, or a composite of two trees with
vertices. -/
theorem shape (t : FreeSet T A) : Shape t := by
  obtain ⟨s, rfl⟩ := Pres.mk_surjective t
  induction s with
  | one => exact Or.inl ⟨Equiv.refl _, (SetOperad.map_refl _).symm⟩
  | gen g => exact Or.inr (Or.inl ⟨_, g, Equiv.refl _, (SetOperad.map_refl _).symm⟩)
  | map e s ih =>
    rw [← Pres.map_mk]
    exact ih.map e
  | @comp A₁ B₁ _ _ _ _ i s s' ih ih' =>
    rw [← Pres.comp_mk]
    by_cases hx : w (Pres.mk s : FreeSet T A₁) = 0
    · obtain ⟨e₁, he₁⟩ := eq_unit _ hx
      obtain ⟨E, hE⟩ := SetOperad.comp_unit_left i e₁ (Pres.mk s' : FreeSet T B₁)
      rw [he₁, hE]
      exact ih'.map E
    by_cases hy : w (Pres.mk s' : FreeSet T B₁) = 0
    · obtain ⟨e₂, he₂⟩ := eq_unit _ hy
      obtain ⟨E, hE⟩ := SetOperad.comp_unit_right i (Pres.mk s : FreeSet T A₁) e₂
      rw [he₂, hE]
      exact ih.map E
    let σ := Fintype.equivFin A₁
    let τ := Fintype.equivFin B₁
    refine Or.inr (Or.inr ⟨_, _, σ i, SetOperad.map σ (Pres.mk s), SetOperad.map τ (Pres.mk s'),
      (compEquiv σ τ i).symm, by rwa [w_map], by rwa [w_map], ?_⟩)
    rw [← SetOperad.map_comp, SetOperad.map_symm_map]

end FreeSet

/-! ## Pairings with tensors of submodules -/

namespace SymCooperad

variable {R : Type u} [CommRing R]

/-- A pairing vanishes on a tensor of submodules when one of the two functionals vanishes on its
factor. -/
lemma pair_eq_zero_of_mem {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] {M : Submodule R X} {N : Submodule R Y} {f : Module.Dual R X}
    {g : Module.Dual R Y} (h : (∀ m ∈ M, f m = 0) ∨ (∀ n ∈ N, g n = 0)) {t : X ⊗[R] Y}
    (ht : t ∈ tensSub R M N) : pair f g t = 0 := by
  rw [tensSub, Submodule.map₂_eq_span_image2] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, n, hn, rfl⟩ := hx
    show pair f g (m ⊗ₜ[R] n) = 0
    rw [pair_tmul]
    rcases h with h | h
    · rw [h m hm, zero_mul]
    · rw [h n hn, mul_zero]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

/-- The pairs of functionals pairing nontrivially with an element of a tensor of submodules are
finitely many, when they are for elements of each factor. -/
lemma finite_support_pair {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] {PX PY : Type*} {M : Submodule R X} {N : Submodule R Y}
    (F : PX → Module.Dual R X) (G : PY → Module.Dual R Y)
    (hF : ∀ m ∈ M, (Function.support fun p => F p m).Finite)
    (hG : ∀ n ∈ N, (Function.support fun q => G q n).Finite) {t : X ⊗[R] Y}
    (ht : t ∈ tensSub R M N) :
    (Function.support fun pq : PX × PY => pair (F pq.1) (G pq.2) t).Finite := by
  rw [tensSub, Submodule.map₂_eq_span_image2] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, n, hn, rfl⟩ := hx
    refine ((hF m hm).prod (hG n hn)).subset fun pq hpq => ?_
    simp only [Function.mem_support, TensorProduct.mk_apply, pair_tmul] at hpq
    exact ⟨left_ne_zero_of_mul hpq, right_ne_zero_of_mul hpq⟩
  | zero => simp
  | add x y _ _ hx hy =>
    refine (hx.union hy).subset fun pq hpq => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
    exact hpq (by show pair _ _ (x + y) = 0; rw [map_add, hc.1, hc.2, add_zero])
  | smul r x _ hx =>
    refine hx.subset fun pq hpq => ?_
    simp only [Function.mem_support, map_smul, smul_eq_mul] at hpq ⊢
    exact right_ne_zero_of_mul hpq

end SymCooperad

lemma Finsupp.support_finite' {α M : Type*} [Zero M] (f : α →₀ M) :
    (Function.support f).Finite := by
  rw [Finsupp.fun_support_eq]
  exact f.support.finite_toSet

/-! ## The cofree conilpotent cooperad -/

/-- **The cofree conilpotent cooperad** on cogenerators `T`: the decomposition cooperad of the
free operad, whose cooperations are linear combinations of trees, decomposed by cutting. -/
abbrev Cofree (R : Type u) [CommRing R] (T : ℕ → Type v) :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type (max 1 v u) :=
  Lin R (FreeSet T)

namespace Cofree

open SymCooperad SetOperad.ConnectedWeight Lin

variable (R : Type u) [CommRing R] (T : ℕ → Type v)

/-- The projection of the cofree cooperad on its cogenerators: the coefficients of the
corollas. -/
noncomputable def proj (k : ℕ) : Cofree R T (Fin k) →ₗ[R] (T k →₀ R) :=
  finComap (Pres.gen (ρ := fun _ _ => False))
    (finite_preimage_of_injective (FreeReg.gen_injective k))

variable {R T}

@[simp] lemma proj_apply {k : ℕ} (x : Cofree R T (Fin k)) (g : T k) :
    proj R T k x g = x (Pres.gen g) :=
  rfl

variable {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [SymCooperad R C] [Coaug R C]

/-- **Trees with vertices pair trivially with the coaugmentation**, as soon as the generators
do. -/
theorem dualVal_eq_zero_of_coaug (Ψ : SetOperadHom (FreeSet T) (Und R (Dual R C)))
    (hgen : ∀ (k : ℕ) (g : T k), ∀ c ∈ coaugSpan R C (Fin k), dualVal Ψ (Pres.gen g) c = 0)
    {A : Type} [Fintype A] [DecidableEq A] (t : FreeSet T A) (ht : w t ≠ 0) :
    ∀ c ∈ coaugSpan R C A, dualVal Ψ t c = 0 := by
  obtain ⟨s, rfl⟩ := Pres.mk_surjective t
  induction s with
  | one => exact absurd w_one ht
  | gen g => exact hgen _ g
  | map e s ih =>
    intro c hc
    rw [← Pres.map_mk, w_map] at ht
    rw [← Pres.map_mk, dualVal_map]
    exact ih ht _ (map_mem_unitSpan _ e.symm hc)
  | comp i s s' ih ih' =>
    intro c hc
    rw [← Pres.comp_mk, w_comp] at ht
    rw [← Pres.comp_mk, dualVal_comp]
    refine pair_eq_zero_of_mem ?_ (decomp_mem_coaugSpan i hc)
    by_cases hx : w (Pres.mk s : FreeSet T _) = 0
    · exact Or.inr (ih' (by omega))
    · exact Or.inl (ih hx)

/-- The morphism from the free operad to the dual operad given by a family of maps into the
cogenerators. -/
noncomputable def genHom (φ : ∀ k, C (Fin k) →ₗ[R] (T k →₀ R)) :
    SetOperadHom (FreeSet T) (Und R (Dual R C)) :=
  FreeSet.homEquiv.symm fun k g => Und.of R (Dual R C) (Finsupp.lapply g ∘ₗ φ k)

omit [Coaug R C] in
@[simp] lemma dualVal_genHom_gen (φ : ∀ k, C (Fin k) →ₗ[R] (T k →₀ R)) {k : ℕ} (g : T k)
    (c : C (Fin k)) : dualVal (genHom φ) (Pres.gen g) c = φ k c g :=
  rfl

/-- The generators pair trivially with the coaugmentation when the maps kill it. -/
lemma genHom_gen_coaug (φ : ∀ k, C (Fin k) →ₗ[R] (T k →₀ R))
    (hφ : ∀ k (e : Unit ≃ Fin k), φ k (map (R := R) e (Coaug.one (R := R) (C := C))) = 0)
    (k : ℕ) (g : T k) : ∀ c ∈ coaugSpan R C (Fin k), dualVal (genHom φ) (Pres.gen g) c = 0 := by
  intro c hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    rw [dualVal_genHom_gen, hφ k e, Finsupp.coe_zero, Pi.zero_apply]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

/-- **On a conilpotent cooperad, a family of maps into the cogenerators killing the
coaugmentation defines a locally finite morphism**: a cooperation pairs nontrivially with only
finitely many trees. -/
theorem locallyFinite (hC : Conilpotent R C) (φ : ∀ k, C (Fin k) →ₗ[R] (T k →₀ R))
    (hφ : ∀ k (e : Unit ≃ Fin k), φ k (map (R := R) e (Coaug.one (R := R) (C := C))) = 0) :
    LocallyFinite (genHom φ) := by
  set Ψ := genHom φ with hΨ
  have hgen := genHom_gen_coaug φ hφ
  have hunit : ∀ {A : Type} [Fintype A] [DecidableEq A] (t : FreeSet T A), w t ≠ 0 →
      ∀ c ∈ coaugSpan R C A, dualVal Ψ t c = 0 :=
    fun t ht => dualVal_eq_zero_of_coaug Ψ hgen t ht
  suffices h : ∀ n (A : Type) [Fintype A] [DecidableEq A], ∀ c ∈ filt R C n A,
      (Function.support fun t : FreeSet T A => dualVal Ψ t c).Finite by
    intro A _ _ c
    obtain ⟨n, hn⟩ := hC A c
    exact h n A c hn
  intro n
  induction n with
  | zero =>
    intro A _ _ c hc
    refine (Set.finite_range fun e : Unit ≃ A =>
      (SetOperad.map e SetOperad.one : FreeSet T A)).subset fun t ht => ?_
    by_contra hne
    refine ht (hunit t (fun h0 => hne ?_) c hc)
    obtain ⟨e, he⟩ := eq_unit t h0
    exact ⟨e, he.symm⟩
  | succ n ih =>
    intro A _ _ c hc
    have hV : ∀ (B D : Type) [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D] (i : B)
        (e : Without B i ⊕ D ≃ A),
        {pq : FreeSet T B × FreeSet T D | w pq.1 ≠ 0 ∧ w pq.2 ≠ 0 ∧
          pair (dualVal Ψ pq.1) (dualVal Ψ pq.2)
            (decomp (R := R) i (map (R := R) e.symm c)) ≠ 0}.Finite := by
      intro B D _ _ _ _ i e
      obtain ⟨w₁₂, hw₁₂, w₃, hw₃, hsum⟩ := Submodule.mem_sup.1 (hc B D i e)
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 hw₁₂
      refine (finite_support_pair _ _ (fun m hm => ih B m hm) (fun m hm => ih D m hm)
        hw₃).subset fun pq ⟨hp, hq, hne⟩ => ?_
      rw [← hsum, map_add, map_add, pair_eq_zero_of_mem (Or.inl (hunit pq.1 hp)) hw₁,
        pair_eq_zero_of_mem (Or.inr (hunit pq.2 hq)) hw₂, zero_add, zero_add] at hne
      exact hne
    let U₀ : Set (FreeSet T A) := Set.range fun e : Unit ≃ A => SetOperad.map e SetOperad.one
    let U₁ : Set (FreeSet T A) := ⋃ e : Fin (Fintype.card A) ≃ A,
      (fun g => SetOperad.map e (Pres.gen g)) '' Function.support (φ _ (map (R := R) e.symm c))
    let U₂ : Set (FreeSet T A) := ⋃ a ∈ Finset.range (Fintype.card A + 2),
      ⋃ b ∈ Finset.range (Fintype.card A + 1), ⋃ i : Fin a, ⋃ e : Without (Fin a) i ⊕ Fin b ≃ A,
        (fun pq : FreeSet T (Fin a) × FreeSet T (Fin b) =>
          SetOperad.map e (SetOperad.comp i pq.1 pq.2)) ''
          {pq | w pq.1 ≠ 0 ∧ w pq.2 ≠ 0 ∧ pair (dualVal Ψ pq.1) (dualVal Ψ pq.2)
            (decomp (R := R) i (map (R := R) e.symm c)) ≠ 0}
    have h₀ : U₀.Finite := Set.finite_range _
    have h₁ : U₁.Finite :=
      Set.finite_iUnion fun e => (Finsupp.support_finite' _).image _
    have h₂ : U₂.Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) fun a _ =>
        Set.Finite.biUnion (Finset.finite_toSet _) fun b _ =>
          Set.finite_iUnion fun i => Set.finite_iUnion fun e => (hV _ _ i e).image _
    refine ((h₀.union h₁).union h₂).subset fun t ht => ?_
    rcases FreeSet.shape t with ⟨e, rfl⟩ | ⟨k, g, e, rfl⟩ | ⟨a, b, i, p, q, e, hp, hq, rfl⟩
    · exact Or.inl (Or.inl ⟨e, rfl⟩)
    · obtain rfl : k = Fintype.card A := by simpa using Fintype.card_congr e
      rw [Function.mem_support, dualVal_map, dualVal_genHom_gen] at ht
      exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨e, g, ht, rfl⟩))
    · have hcard := Fintype.card_congr e
      rw [Fintype.card_sum, Reg.card_without, Fintype.card_fin, Fintype.card_fin] at hcard
      have ha := i.pos
      rw [Function.mem_support, dualVal_map, dualVal_comp] at ht
      refine Or.inr (Set.mem_iUnion₂.2 ⟨a, ?_, Set.mem_iUnion₂.2 ⟨b, ?_, Set.mem_iUnion.2 ⟨i,
        Set.mem_iUnion.2 ⟨e, ⟨(p, q), ⟨hp, hq, ht⟩, rfl⟩⟩⟩⟩⟩)
      · exact Finset.mem_coe.2 (Finset.mem_range.2 (by omega))
      · exact Finset.mem_coe.2 (Finset.mem_range.2 (by omega))

variable (R T) in
/-- **The cofree cooperad is conilpotent.** -/
theorem conilpotent : Conilpotent R (Cofree R T) :=
  Lin.conilpotent

/-- **The universal property of the cofree conilpotent cooperad**: for a conilpotent cooperad
`C`, the morphisms of coaugmented cooperads `C → Cofree R T` are the families of linear maps
`C (Fin k) → R[T k]` killing the coaugmentation, by composition with the projection on the
corollas. -/
noncomputable def homEquiv (hC : Conilpotent R C) :
    {Φ : SymCooperadHom R C (Cofree R T) //
      Φ.app Unit (Coaug.one (R := R) (C := C)) = Coaug.one (R := R) (C := Cofree R T)} ≃
    {φ : ∀ k, C (Fin k) →ₗ[R] (T k →₀ R) //
      ∀ k (e : Unit ≃ Fin k), φ k (map (R := R) e (Coaug.one (R := R) (C := C))) = 0} where
  toFun Φ := ⟨fun k => proj R T k ∘ₗ Φ.1.app (Fin k), fun k e => Finsupp.ext fun g => by
    have h := LinearMap.congr_fun (Φ.1.app_map e) (Coaug.one (R := R) (C := C))
    simp only [LinearMap.comp_apply] at h
    rw [LinearMap.comp_apply, proj_apply, h, Φ.2, Lin.one_eq]
    show mapL R e (Finsupp.single SetOperad.one 1) (Pres.gen g) = 0
    rw [mapL_single, Finsupp.single_eq_of_ne (FreeSet.gen_ne_unit g e)]⟩
  invFun φ := ⟨Lin.ofTranspose (genHom φ.1) (locallyFinite hC φ.1 φ.2), Finsupp.ext fun t => by
    show dualVal (genHom φ.1) t (Coaug.one (R := R) (C := C))
      = Finsupp.single (SetOperad.one : FreeSet T Unit) (1 : R) t
    by_cases ht : t = SetOperad.one
    · subst ht
      rw [dualVal_one, Coaug.counit_one, Finsupp.single_eq_same]
    · have hw : w t ≠ 0 := fun h0 => ht (by
        obtain ⟨e, he⟩ := eq_unit t h0
        rw [he, Subsingleton.elim e (Equiv.refl Unit), SetOperad.map_refl])
      rw [Finsupp.single_eq_of_ne ht]
      exact dualVal_eq_zero_of_coaug _ (genHom_gen_coaug φ.1 φ.2) t hw _
        (Submodule.subset_span ⟨Equiv.refl Unit, map_refl (R := R) (C := C) _⟩)⟩
  left_inv Φ := by
    have h : genHom (fun k => proj R T k ∘ₗ Φ.1.app (Fin k)) = Lin.transpose Φ.1 :=
      Pres.hom_ext fun k g => congrArg (Und.of R (Dual R C)) (LinearMap.ext fun c => rfl)
    refine Subtype.ext (SymCooperadHom.ext fun A _ _ c => Finsupp.ext fun t => ?_)
    show dualVal (genHom (fun k => proj R T k ∘ₗ Φ.1.app (Fin k))) t c = Φ.1.app A c t
    rw [h, dualVal_transpose]
  right_inv φ := Subtype.ext (funext fun k => LinearMap.ext fun c => Finsupp.ext fun g => rfl)

@[simp] lemma homEquiv_apply (hC : Conilpotent R C)
    (Φ : {Φ : SymCooperadHom R C (Cofree R T) //
      Φ.app Unit (Coaug.one (R := R) (C := C)) = Coaug.one (R := R) (C := Cofree R T)})
    (k : ℕ) : (homEquiv hC Φ).1 k = proj R T k ∘ₗ Φ.1.app (Fin k) :=
  rfl

/-- **The cofree property**: on a conilpotent cooperad, every family of linear maps into the
cogenerators killing the coaugmentation lifts uniquely to a morphism of coaugmented cooperads
into the cofree cooperad. -/
theorem existsUnique_lift (hC : Conilpotent R C) (φ : ∀ k, C (Fin k) →ₗ[R] (T k →₀ R))
    (hφ : ∀ k (e : Unit ≃ Fin k), φ k (map (R := R) e (Coaug.one (R := R) (C := C))) = 0) :
    ∃! Φ : {Φ : SymCooperadHom R C (Cofree R T) //
        Φ.app Unit (Coaug.one (R := R) (C := C)) = Coaug.one (R := R) (C := Cofree R T)},
      ∀ k, proj R T k ∘ₗ Φ.1.app (Fin k) = φ k := by
  refine ⟨(homEquiv hC).symm ⟨φ, hφ⟩, fun k => ?_, fun Φ hΦ => ?_⟩
  · exact congrFun (congrArg Subtype.val ((homEquiv hC).apply_symm_apply ⟨φ, hφ⟩)) k
  · rw [Equiv.eq_symm_apply]
    exact Subtype.ext (funext hΦ)

end Cofree

end Operad
