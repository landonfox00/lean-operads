/-
# Inhomogeneous presentations: PBW bases and the associated graded

Rules whose tails have at most as many vertices as their leading monomials — for instance
quadratic-linear rules, with leading monomials of weight two and tails of weight one and two —
present a filtered operad. Their **leading part** `G.top` keeps the terms of the tails with as
many vertices as the leading monomial, and presents a weight-graded operad.

* **Contexts shift weights uniformly** (`STree.IsSCtx.weight_add`), so every admissible order has
  a **weight-graded refinement** (`STree.AdmOrder.byWeight`), comparing the numbers of vertices
  first.
* **The leading part of a resolvable presentation is resolvable** (`Operad.Rules.top_resolvable`):
  over a weight-graded order, the top-weight part of a resolution is a resolution. So for
  quadratic-linear rules with a PBW basis, **the quadratic part presents a Koszul operad**
  (`Operad.Rules.top_isKoszul`).
* **The PBW theorem** (`Operad.Rules.pbw`, `Operad.Rules.grEquiv`): a combination of monomials of
  weight `n` is congruent to one of lower weight modulo the relations if and only if it lies in
  the ideal of the leading part; that is, the associated graded of the filtered operad presented
  by `G` is the operad presented by `G.top`, weight by weight.
-/
import Operad.ShuffleAnyKoszul
import Mathlib.LinearAlgebra.Isomorphisms

universe v

namespace Operad

namespace STree

variable {E : ℕ → Type v}

/-! ## Contexts and weights -/

/-- **The number of vertices of a replaced tree.** -/
theorem weight_replace_add : ∀ {t u : STree E} {p : List ℕ}, t.get? p = some u →
    ∀ v : STree E, (t.replace p v).weight + u.weight = t.weight + v.weight
  | t, u, [], h, v => by
    rw [get?_nil, Option.some_inj] at h
    subst h
    rw [replace_nil, add_comm]
  | leaf _, _, _ :: _, h, _ => by simp at h
  | @node _ k e c, u, i :: p, h, v => by
    obtain ⟨hi, h⟩ := get?_node_cons_eq_some.1 h
    have key := weight_replace_add h v
    let c' : Fin k → STree E := fun j => if (j : ℕ) = i then (c j).replace p v else c j
    have h1 : ∀ j ∈ Finset.univ.erase (⟨i, hi⟩ : Fin k), (c' j).weight = (c j).weight :=
      fun j hj => by
        simp only [c']
        rw [if_neg fun h' => (Finset.mem_erase.1 hj).1 (Fin.ext h')]
    have h2 : c' ⟨i, hi⟩ = (c ⟨i, hi⟩).replace p v := if_pos rfl
    rw [replace_node_cons, weight_node, weight_node]
    change 1 + ∑ j, (c' j).weight + u.weight = 1 + ∑ j, (c j).weight + v.weight
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨i, hi⟩ : Fin k)),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨i, hi⟩ : Fin k)), Finset.sum_congr rfl h1,
      h2]
    omega

/-- **Contexts shift weights uniformly.** -/
theorem IsSCtx.weight_add {A B : Finset ℕ} {f : SMono E A → SMono E B} (hf : IsSCtx f)
    (g g' : SMono E A) : (f g).1.weight + g'.1.weight = (f g').1.weight + g.1.weight := by
  obtain ⟨T, p, xs, hp, -, hf⟩ := hf
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hp
  have e := fun h : SMono E A => weight_replace_add hw (h.1.subst xs)
  have e₁ := e g
  have e₂ := e g'
  rw [← hf, weight_subst, g.labels_eq] at e₁
  rw [← hf, weight_subst, g'.labels_eq] at e₂
  omega

/-- **The weight-graded refinement** of an admissible order: compare the numbers of vertices
first. -/
def AdmOrder.byWeight (O : AdmOrder E) : AdmOrder E where
  lt x y := x.1.weight < y.1.weight ∨ (x.1.weight = y.1.weight ∧ O.lt x y)
  wf A := Subrelation.wf (fun h => Prod.lex_def.2 h)
    (InvImage.wf (fun x : SMono E A => (x.1.weight, x))
      (WellFounded.prod_lex Nat.lt_wfRel.wf (O.wf A)))
  trans := by
    rintro A x y z (h | ⟨h, h'⟩) (k | ⟨k, k'⟩)
    · exact Or.inl (h.trans k)
    · exact Or.inl (k ▸ h)
    · exact Or.inl (h ▸ k)
    · exact Or.inr ⟨h.trans k, O.trans h' k'⟩
  lt_ctx hf x y h := by
    have e := IsSCtx.weight_add hf x y
    rcases h with h | ⟨h, h'⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, O.lt_ctx hf h'⟩

lemma AdmOrder.byWeight_weight (O : AdmOrder E) {A : Finset ℕ} {x y : SMono E A}
    (h : O.byWeight.lt x y) : x.1.weight ≤ y.1.weight := by
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

end STree

open STree

variable {E : ℕ → Type v} {K : Type*} [CommRing K] {ρ : Type*} {O : STree.AdmOrder E}
  (G : Rules K ρ O.toCtxOrder)

/-! ## The leading part -/

open Classical in
/-- **The leading part** of rules: the tails cut down to their terms with as many vertices as
the leading monomial. -/
noncomputable def Rules.top : Rules K ρ O.toCtxOrder where
  src := G.src
  lead := G.lead
  tail r := (G.tail r).filter fun m => m.1.weight = (G.lead r).1.weight
  tail_lt r m hm := G.tail_lt r m (by
    rw [Finsupp.support_filter, Finset.mem_filter] at hm
    exact hm.1)

open Classical in
/-- **The weight-`n` part** of a combination of monomials. -/
noncomputable def wpart {A : Finset ℕ} (n : ℕ) : (SMono E A →₀ K) →ₗ[K] (SMono E A →₀ K) where
  toFun v := v.filter fun m => m.1.weight = n
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

lemma filter_mapDomain {X Y : Type*} (f : X → Y) (v : X →₀ K) (p : Y → Prop)
    [DecidablePred p] [DecidablePred (p ∘ f)] :
    (Finsupp.mapDomain f v).filter p = Finsupp.mapDomain f (v.filter (p ∘ f)) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => rw [Finsupp.mapDomain_zero, Finsupp.filter_zero, Finsupp.filter_zero,
      Finsupp.mapDomain_zero]
  | add v w hv hw => rw [Finsupp.mapDomain_add, Finsupp.filter_add, hv, hw, Finsupp.filter_add,
      Finsupp.mapDomain_add]
  | single x c =>
    rw [Finsupp.mapDomain_single]
    by_cases h : p (f x)
    · rw [Finsupp.filter_single_of_pos p h,
        Finsupp.filter_single_of_pos (p ∘ f) h, Finsupp.mapDomain_single]
    · rw [Finsupp.filter_single_of_neg p h,
        Finsupp.filter_single_of_neg (p ∘ f) h, Finsupp.mapDomain_zero]

lemma filter_congr_support {X : Type*} {v : X →₀ K} {p q : X → Prop} [DecidablePred p]
    [DecidablePred q] (h : ∀ x ∈ v.support, p x ↔ q x) : v.filter p = v.filter q := by
  ext x
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases hx : x ∈ v.support
  · by_cases hp : p x
    · rw [if_pos hp, if_pos ((h x hx).1 hp)]
    · rw [if_neg hp, if_neg fun hq => hp ((h x hx).2 hq)]
  · rw [Finsupp.notMem_support_iff.1 hx, ite_self, ite_self]

lemma filter_eq_zero_of {X : Type*} {v : X →₀ K} {p : X → Prop} [DecidablePred p]
    (h : ∀ x ∈ v.support, ¬ p x) : v.filter p = 0 := by
  ext x
  rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hx : x ∈ v.support
  · rw [if_neg (h x hx)]
  · rw [Finsupp.notMem_support_iff.1 hx, ite_self]

section Weighted

variable {A : Finset ℕ}

lemma wpart_single_of_eq {n : ℕ} {m : SMono E A} (h : m.1.weight = n) (c : K) :
    wpart n (Finsupp.single m c) = Finsupp.single m c := by
  classical
  exact Finsupp.filter_single_of_pos _ h

lemma wpart_single_of_ne {n : ℕ} {m : SMono E A} (h : m.1.weight ≠ n) (c : K) :
    wpart n (Finsupp.single m c) = 0 := by
  classical
  exact Finsupp.filter_single_of_neg _ h

lemma wpart_mapDomain {B : Finset ℕ} (n : ℕ) (f : SMono E B → SMono E A) (v : SMono E B →₀ K) :
    wpart n (Finsupp.mapDomain f v) =
      Finsupp.mapDomain f (v.filter fun m => (f m).1.weight = n) := by
  classical
  exact filter_mapDomain f v _

/-- **The top part of a reduction** is the reduction by the leading part. -/
lemma wpart_tail_eq {r : ρ} {f : SMono E (G.src r) → SMono E A} (hf : IsSCtx f) {n : ℕ}
    (h : (f (G.lead r)).1.weight = n) :
    wpart n (Finsupp.mapDomain f (G.tail r)) = Finsupp.mapDomain f (G.top.tail r) := by
  classical
  rw [wpart_mapDomain]
  congr 1
  refine filter_congr_support fun m _ => ?_
  have e := IsSCtx.weight_add hf m (G.lead r)
  constructor <;> intro h' <;> omega

variable (hwt : ∀ r, ∀ m ∈ (G.tail r).support, m.1.weight ≤ (G.lead r).1.weight)
include hwt

/-- **A reduction lies below the weight of its monomial.** -/
lemma wpart_tail_lt {r : ρ} {f : SMono E (G.src r) → SMono E A} (hf : IsSCtx f) {n : ℕ}
    (h : (f (G.lead r)).1.weight < n) : wpart n (Finsupp.mapDomain f (G.tail r)) = 0 := by
  classical
  rw [wpart_mapDomain, filter_eq_zero_of fun m hm => ?_, Finsupp.mapDomain_zero]
  have e := IsSCtx.weight_add hf m (G.lead r)
  have := hwt r m hm
  omega

/-- **Reductions do not increase the number of vertices.** -/
lemma red_weight_le {X : SMono E A} {u : SMono E A →₀ K} (hu : u ∈ (G.rw A).red X) :
    u ∈ Finsupp.supported K K {Y | Y.1.weight ≤ X.1.weight} := by
  classical
  obtain ⟨r, f, hf, rfl, rfl⟩ := hu
  intro Y hY
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hY)
  have e := IsSCtx.weight_add hf m (G.lead r)
  have := hwt r m hm
  show (f m).1.weight ≤ (f (G.lead r)).1.weight
  omega

variable (hO : ∀ {A : Finset ℕ} {x y : SMono E A}, O.lt x y → x.1.weight ≤ y.1.weight)
include hO

/-- **The leading part of a resolvable presentation is resolvable**, over an order compatible
with the weight: the top-weight part of a resolution is a resolution. -/
theorem Rules.top_resolvable (hres : (G.rw A).Resolvable) : (G.top.rw A).Resolvable := by
  classical
  refine Rules.resolvable_iff.2 fun r₁ r₂ B => ?_
  let B' : G.Amb A r₁ r₂ := ⟨B.f₁, B.f₂, B.ctx₁, B.ctx₂, B.eq⟩
  have hB' := Rules.resolvable_iff.1 hres r₁ r₂ B'
  set n := B.top.1.weight with hn
  have key : ∀ x ∈ (G.rw A).idealOn ((G.rw A).below B'.top),
      wpart n x ∈ (G.top.rw A).idealOn ((G.top.rw A).below B.top) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, u, ⟨r, g, hg, rfl, rfl⟩, rfl⟩ := hx
      have hle : (g (G.lead r)).1.weight ≤ n := hO hm
      rcases hle.lt_or_eq with hlt | heq
      · rw [map_sub, wpart_single_of_ne hlt.ne, wpart_tail_lt G hwt hg hlt, sub_zero]
        exact Submodule.zero_mem _
      · rw [map_sub, wpart_single_of_eq heq, wpart_tail_eq G hg heq]
        exact (G.top.rw A).sub_mem_idealOn hm ⟨r, g, hg, rfl, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have h := key _ hB'
  have h₁ : wpart n (Finsupp.mapDomain B'.f₁ (G.tail r₁)) =
      Finsupp.mapDomain B.f₁ (G.top.tail r₁) := wpart_tail_eq G B.ctx₁ rfl
  have h₂ : wpart n (Finsupp.mapDomain B'.f₂ (G.tail r₂)) =
      Finsupp.mapDomain B.f₂ (G.top.tail r₂) :=
    wpart_tail_eq G B.ctx₂ (by rw [hn]; exact congrArg (fun X => X.1.weight) B.eq.symm)
  rw [map_sub, h₁, h₂] at h
  exact h

/-- **The top part of a normal form** is the normal form for the leading part, on the
combinations of monomials with `n` vertices. -/
theorem Rules.wpart_nf (hres : (G.rw A).Resolvable) {n : ℕ} {v : SMono E A →₀ K}
    (hv : v ∈ Finsupp.supported K K {m : SMono E A | m.1.weight = n}) :
    wpart n ((G.rw A).nf v) = (G.top.rw A).nf v := by
  classical
  set S := G.rw A
  set S' := G.top.rw A
  have hS' : S'.Resolvable := G.top_resolvable hwt hO hres
  have hlt : ∀ u ∈ Finsupp.supported K K {m : SMono E A | m.1.weight < n},
      wpart n (S.nf u) = 0 := fun u hu => by
    have hcl : ∀ X ∈ {m : SMono E A | m.1.weight < n}, ∀ w ∈ S.red X,
        w ∈ Finsupp.supported K K {m : SMono E A | m.1.weight < n} := fun X hX w hw => by
      have hsub : {Y : SMono E A | Y.1.weight ≤ X.1.weight} ⊆ {m | m.1.weight < n} :=
        fun Y hY => show Y.1.weight < n from lt_of_le_of_lt hY hX
      exact Finsupp.supported_mono hsub (red_weight_le G hwt hw)
    have h := S.nf_mem_of_closed hcl hu
    show (S.nf u).filter _ = 0
    exact filter_eq_zero_of fun Y hY => ((Finsupp.mem_supported K _).1 h hY).ne
  suffices hm : ∀ m : SMono E A, m.1.weight = n → wpart n (S.nfMono m) = S'.nfMono m by
    refine eq_of_supported (f := wpart n ∘ₗ S.nf) (g := S'.nf) (fun m hm' => ?_) hv
    rw [LinearMap.comp_apply, Rewriting.nf_single, Rewriting.nf_single, one_smul, one_smul]
    exact hm m hm'
  intro m
  induction m using (O.wf A).induction with
  | _ m ih =>
  intro hmn
  by_cases hred : (S.red m).Nonempty
  · obtain ⟨u, hu⟩ := hred
    obtain ⟨r, f, hf, hfm, rfl⟩ := hu
    have hu' : Finsupp.mapDomain f (G.top.tail r) ∈ S'.red m := ⟨r, f, hf, hfm, rfl⟩
    rw [← (G.top_resolvable hwt hO hres).nf_red m _ hu', ← hres.nf_red m _ ⟨r, f, hf, hfm, rfl⟩]
    have hsplit : G.tail r =
        (G.tail r).filter (fun m' => m'.1.weight = (G.lead r).1.weight) +
        (G.tail r).filter fun m' => ¬ m'.1.weight = (G.lead r).1.weight :=
      (Finsupp.filter_add_filter_not _ _).symm
    have hfL : (f (G.lead r)).1.weight = n := by rw [hfm]; exact hmn
    rw [hsplit, Finsupp.mapDomain_add, map_add, map_add, hlt (Finsupp.mapDomain f
      ((G.tail r).filter fun m' => ¬ m'.1.weight = (G.lead r).1.weight)) ?_, add_zero]
    · refine eq_of_supported (f := wpart n ∘ₗ S.nf) (g := S'.nf)
        (s := {Y | Y.1.weight = n ∧ O.lt Y m}) (fun Y hY => ?_) ?_
      · rw [LinearMap.comp_apply, Rewriting.nf_single, Rewriting.nf_single, one_smul, one_smul]
        exact ih Y hY.2 hY.1
      · intro Y hY
        obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hY)
        have hm'' := hm'
        simp only [Finsupp.support_filter, Finset.mem_filter] at hm''
        have e := IsSCtx.weight_add hf m' (G.lead r)
        refine ⟨by omega, ?_⟩
        rw [← hfm]
        exact O.lt_ctx hf (G.tail_lt r m' hm''.1)
    · intro Y hY
      obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hY)
      rw [Finsupp.support_filter, Finset.mem_filter] at hm'
      have e := IsSCtx.weight_add hf m' (G.lead r)
      have := hwt r m' hm'.1
      show (f m').1.weight < n
      omega
  · have hirr : m ∈ S.Irr := S.mem_irr_iff.2 hred
    have hirr' : m ∈ S'.Irr := by
      rw [G.top.mem_irr_iff]
      exact (G.mem_irr_iff.1 hirr : G.Normal m)
    rw [S.nfMono_of_irr hirr, S'.nfMono_of_irr hirr', wpart_single_of_eq hmn]

/-- **The PBW theorem for inhomogeneous presentations**: a combination of monomials with `n`
vertices is congruent, modulo the relations, to a combination of monomials with fewer vertices if
and only if it lies in the ideal of the leading part. So the associated graded of the filtered
operad presented by the rules is the operad presented by their leading part. -/
theorem Rules.pbw (hres : (G.rw A).Resolvable) {n : ℕ} {v : SMono E A →₀ K}
    (hv : v ∈ Finsupp.supported K K {m : SMono E A | m.1.weight = n}) :
    (∃ u ∈ Finsupp.supported K K {m : SMono E A | m.1.weight < n}, v - u ∈ (G.rw A).ideal) ↔
      v ∈ (G.top.rw A).ideal := by
  classical
  have hS' := G.top_resolvable hwt hO hres
  have hle : ∀ X ∈ {m : SMono E A | m.1.weight ≤ n}, ∀ w ∈ (G.rw A).red X,
      w ∈ Finsupp.supported K K {m : SMono E A | m.1.weight ≤ n} := fun X hX w hw => by
    have hsub : {Y : SMono E A | Y.1.weight ≤ X.1.weight} ⊆ {m | m.1.weight ≤ n} :=
      fun Y hY => show Y.1.weight ≤ n from le_trans hY hX
    exact Finsupp.supported_mono hsub (red_weight_le G hwt hw)
  have hlt : ∀ X ∈ {m : SMono E A | m.1.weight < n}, ∀ w ∈ (G.rw A).red X,
      w ∈ Finsupp.supported K K {m : SMono E A | m.1.weight < n} := fun X hX w hw => by
    have hsub : {Y : SMono E A | Y.1.weight ≤ X.1.weight} ⊆ {m | m.1.weight < n} :=
      fun Y hY => show Y.1.weight < n from lt_of_le_of_lt hY hX
    exact Finsupp.supported_mono hsub (red_weight_le G hwt hw)
  constructor
  · rintro ⟨u, hu, hvu⟩
    rw [← hS'.nf_eq_zero_iff, ← G.wpart_nf hwt hO hres hv, (hres.nf_eq_nf_iff).2 hvu]
    have h := (G.rw A).nf_mem_of_closed hlt hu
    show ((G.rw A).nf u).filter _ = 0
    exact filter_eq_zero_of fun Y hY =>
      (show Y.1.weight < n from (Finsupp.mem_supported K _).1 h hY).ne
  · intro hv'
    refine ⟨(G.rw A).nf v, ?_, ?_⟩
    · have hsub : {m : SMono E A | m.1.weight = n} ⊆ {m | m.1.weight ≤ n} :=
        fun Y hY => show Y.1.weight ≤ n from (show Y.1.weight = n from hY).le
      have h1 := (G.rw A).nf_mem_of_closed hle (Finsupp.supported_mono hsub hv)
      have h2 : wpart n ((G.rw A).nf v) = 0 := by
        rw [G.wpart_nf hwt hO hres hv]
        exact hS'.ideal_le_ker hv'
      intro Y hY
      have hY' : Y.1.weight ≤ n := (Finsupp.mem_supported K _).1 h1 hY
      show Y.1.weight < n
      rcases hY'.lt_or_eq with h | h
      · exact h
      · exfalso
        have : wpart n ((G.rw A).nf v) Y = ((G.rw A).nf v) Y := by
          show ((G.rw A).nf v).filter _ Y = _
          rw [Finsupp.filter_apply, if_pos h]
        rw [h2, Finsupp.coe_zero, Pi.zero_apply] at this
        exact (Finsupp.mem_support_iff.1 hY) this.symm
    · rw [← neg_sub]
      exact Submodule.neg_mem _ ((G.rw A).nf_sub_mem v)

end Weighted

/-! ## The associated graded -/

section Graded

variable (A : Finset ℕ) (n : ℕ)

/-- **The filtration** of the operad presented by the rules, by the number of vertices. -/
noncomputable def Rules.filt : Submodule K ((SMono E A →₀ K) ⧸ (G.rw A).ideal) :=
  (Finsupp.supported K K {m : SMono E A | m.1.weight ≤ n}).map (G.rw A).ideal.mkQ

/-- **The part of the filtration below `n`.** -/
noncomputable def Rules.filtLT : Submodule K ((SMono E A →₀ K) ⧸ (G.rw A).ideal) :=
  (Finsupp.supported K K {m : SMono E A | m.1.weight < n}).map (G.rw A).ideal.mkQ

/-- **The associated graded** of the filtered operad presented by the rules, in weight `n`. -/
abbrev Rules.gr : Type _ := G.filt A n ⧸ (G.filtLT A n).comap (G.filt A n).subtype

/-- **The operad presented by the leading part**, in weight `n`. -/
abbrev Rules.topW : Type _ := Finsupp.supported K K {m : SMono E A | m.1.weight = n} ⧸
  (G.top.rw A).ideal.comap (Finsupp.supported K K {m : SMono E A | m.1.weight = n}).subtype

/-- The class in the associated graded of a combination of monomials with `n` vertices. -/
noncomputable def Rules.toGr :
    Finsupp.supported K K {m : SMono E A | m.1.weight = n} →ₗ[K] G.gr A n :=
  (Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (G.filt A n)
    ((G.rw A).ideal.mkQ ∘ₗ (Finsupp.supported K K _).subtype) fun v =>
      Submodule.mem_map_of_mem (Finsupp.supported_mono (s := {m : SMono E A | m.1.weight = n})
        (t := {m : SMono E A | m.1.weight ≤ n})
        (fun Y hY => show Y.1.weight ≤ n from (show Y.1.weight = n from hY).le) v.2)

theorem Rules.toGr_surjective : Function.Surjective (G.toGr A n) := by
  classical
  intro x
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨w, hw, rfl⟩ := hy
  have hwn : wpart n w ∈ Finsupp.supported K K {m : SMono E A | m.1.weight = n} := by
    intro Y hY
    rw [Finset.mem_coe] at hY
    have := Finsupp.support_filter (p := fun m : SMono E A => m.1.weight = n) w ▸ hY
    exact (Finset.mem_filter.1 this).2
  refine ⟨⟨wpart n w, hwn⟩, (Submodule.Quotient.eq _).2 ?_⟩
  rw [Submodule.mem_comap, Submodule.coe_subtype]
  refine ⟨wpart n w - w, ?_, ?_⟩
  · intro Y hY
    have hle : Y.1.weight ≤ n := by
      by_contra h
      have h1 : (wpart n w - w) Y = 0 := by
        rw [Finsupp.sub_apply]
        show w.filter _ Y - w Y = 0
        rw [Finsupp.filter_apply, if_neg (by omega), Finsupp.notMem_support_iff.1
          fun h' => h ((Finsupp.mem_supported K w).1 hw h'), sub_zero]
      exact (Finsupp.mem_support_iff.1 hY) h1
    show Y.1.weight < n
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      apply Finsupp.mem_support_iff.1 hY
      rw [Finsupp.sub_apply]
      show w.filter _ Y - w Y = 0
      rw [Finsupp.filter_apply, if_pos h, sub_self]
  · rw [LinearMap.map_sub]
    rfl

variable (hwt : ∀ r, ∀ m ∈ (G.tail r).support, m.1.weight ≤ (G.lead r).1.weight)
  (hO : ∀ {A : Finset ℕ} {x y : SMono E A}, O.lt x y → x.1.weight ≤ y.1.weight)
  (hres : (G.rw A).Resolvable)
include hwt hO hres

theorem Rules.ker_toGr : LinearMap.ker (G.toGr A n) =
    (G.top.rw A).ideal.comap (Finsupp.supported K K {m : SMono E A | m.1.weight = n}).subtype := by
  ext ⟨v, hv⟩
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
  show Submodule.Quotient.mk _ = 0 ↔ v ∈ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    ← G.pbw hwt hO hres hv]
  constructor
  · rintro ⟨u, hu, hu'⟩
    refine ⟨u, hu, ?_⟩
    have := (Submodule.Quotient.eq _).1 hu'
    rw [← neg_sub]
    exact Submodule.neg_mem _ this
  · rintro ⟨u, hu, hu'⟩
    refine ⟨u, hu, (Submodule.Quotient.eq _).2 ?_⟩
    rw [← neg_sub]
    exact Submodule.neg_mem _ hu'

/-- **The associated graded of the filtered operad presented by the rules is the operad
presented by their leading part**, weight by weight: the PBW theorem for inhomogeneous
presentations with a PBW basis. -/
noncomputable def Rules.grEquiv : G.topW A n ≃ₗ[K] G.gr A n :=
  (Submodule.quotEquivOfEq _ _ (G.ker_toGr A n hwt hO hres).symm).trans
    ((G.toGr A n).quotKerEquivOfSurjective (G.toGr_surjective A n))

end Graded

/-- **The quadratic part of a quadratic-linear presentation with a PBW basis presents a Koszul
operad**: for rules with leading monomials of weight two and tails of weight at most two, over an
order compatible with the weight, if the rules are resolvable their quadratic part is Koszul. -/
theorem Rules.top_isKoszul (hquad : ∀ r, (G.lead r).1.weight = 2)
    (hwt : ∀ r, ∀ m ∈ (G.tail r).support, m.1.weight ≤ (G.lead r).1.weight)
    (hO : ∀ {A : Finset ℕ} {x y : SMono E A}, O.lt x y → x.1.weight ≤ y.1.weight)
    (hres : ∀ C, (G.rw C).Resolvable) : G.top.IsKoszul := by
  classical
  refine G.top.isKoszul_of_resolvable hquad (fun r m hm => ?_)
    fun C => G.top_resolvable hwt hO (hres C)
  simp only [Rules.top, Finsupp.support_filter] at hm
  have h2 := (Finset.mem_filter (s := (G.tail r).support)
    (p := fun x => x.1.weight = (G.lead r).1.weight) (a := m)).1 hm
  rw [h2.2]
  exact hquad r

end Operad
