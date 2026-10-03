/-
# The free shuffle operad on generators of any arity

The shuffle monomials on generators of any arity (`Operad.STree`, `Operad.STree.SMono`) form
**the free shuffle operad** (`Operad.FreeSh`): on a finite linear order `A`, the combinations of
shuffle monomials whose leaves are the positions `0, …, |A| - 1` of the elements of `A`.

* **Positions** in a finite linear order (`Operad.opos`, `Operad.oelt`): order isomorphisms
  preserve them (`Operad.opos_orderIso`).
* **Relabelling the leaves** of a tree (`Operad.STree.relabel`).
* **Grafting along a shuffle** (`Operad.STree.graft`): the monomial of the inner operation is
  substituted for the leaf at the position of the input `i`, its leaves and the other leaves of
  the outer monomial relabelled by the positions of their images under the shuffle. The shuffle
  condition makes the result a shuffle monomial.
* **The free shuffle operad** (`Operad.FreeSh`, an instance of `Operad.ShuffleOperad`): the
  relabelling along order isomorphisms leaves the monomials unchanged, the unit is the monomial
  with one leaf, and grafting is extended bilinearly; the axioms are those of substitution of
  trees (`Operad.STree.subst_subst`).
-/
import Operad.ShuffleOperad
import Operad.ShuffleAnyGroebner
import Mathlib.Data.Fintype.Sort

universe u v

namespace Operad

/-! ## Positions in a finite linear order -/

section Pos

variable {A : Type*} [Fintype A] [LinearOrder A]

/-- **The position** of an element of a finite linear order: the number of smaller elements. -/
def opos (a : A) : ℕ := (Finset.univ.filter (· < a)).card

lemma opos_lt_card (a : A) : opos a < Fintype.card A := by
  rw [opos, ← Finset.card_univ]
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := h (Finset.mem_univ a)
  simp at this

lemma opos_strictMono : StrictMono (opos : A → ℕ) := by
  intro a b hab
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans hab
  · have := h (Finset.mem_filter.2 ⟨Finset.mem_univ a, hab⟩)
    simp at this

lemma opos_injective : Function.Injective (opos : A → ℕ) := opos_strictMono.injective

lemma opos_lt_opos {a b : A} : opos a < opos b ↔ a < b := opos_strictMono.lt_iff_lt

/-- **Order isomorphisms preserve positions.** -/
lemma opos_orderIso {B : Type*} [Fintype B] [LinearOrder B] (σ : A ≃o B) (a : A) :
    opos (σ a) = opos a := by
  have h : Finset.univ.filter (· < σ a) =
      (Finset.univ.filter (· < a)).map σ.toEquiv.toEmbedding := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro hb
      exact ⟨σ.symm b, σ.symm_apply_lt.2 hb, σ.apply_symm_apply b⟩
    · rintro ⟨a', ha', rfl⟩
      exact σ.lt_iff_lt.2 ha'
  rw [opos, opos, h, Finset.card_map]

lemma opos_fin {k : ℕ} (x : Fin k) : opos x = x := by
  rw [opos, Finset.filter_gt_eq_Iio, Fin.card_Iio]

/-- **The element at a position** below the cardinality. -/
def oelt (n : ℕ) (h : n < Fintype.card A) : A := monoEquivOfFin A rfl ⟨n, h⟩

@[simp] lemma opos_oelt (n : ℕ) (h : n < Fintype.card A) : opos (oelt n h : A) = n := by
  rw [oelt, opos_orderIso, opos_fin]

@[simp] lemma oelt_opos (a : A) : oelt (opos a) (opos_lt_card a) = a :=
  opos_injective (opos_oelt _ _)

lemma oelt_eq_iff {n : ℕ} (h : n < Fintype.card A) {a : A} : oelt n h = a ↔ n = opos a := by
  constructor
  · rintro rfl
    rw [opos_oelt]
  · rintro rfl
    exact oelt_opos a

end Pos

namespace STree

variable {E : ℕ → Type v}

/-! ## Relabelling the leaves -/

/-- **Relabelling the leaves** of a tree along a map. -/
def relabel (f : ℕ → ℕ) (t : STree E) : STree E := t.subst fun a => leaf (f a)

lemma labels_relabel (f : ℕ → ℕ) (t : STree E) : (t.relabel f).labels = t.labels.map f := by
  rw [relabel, labels_subst]
  exact Multiset.bind_singleton _ _

lemma first_relabel (f : ℕ → ℕ) {t : STree E} (ht : t.IsShuffle) :
    (t.relabel f).first = f t.first := by
  rw [relabel, first_subst ht]
  rfl

lemma isShuffle_relabel {f : ℕ → ℕ} {t : STree E} (ht : t.IsShuffle)
    (hf : StrictMonoOn f {a | a ∈ t.labels}) : (t.relabel f).IsShuffle :=
  isShuffle_subst ht (fun _ _ => isShuffle_leaf _) hf

lemma relabel_relabel (f g : ℕ → ℕ) (t : STree E) :
    (t.relabel f).relabel g = t.relabel (g ∘ f) := by
  rw [relabel, relabel, relabel, subst_subst]
  rfl

lemma relabel_congr {f g : ℕ → ℕ} {t : STree E} (h : ∀ a ∈ t.labels, f a = g a) :
    t.relabel f = t.relabel g :=
  subst_congr t fun a ha => by rw [h a ha]

lemma relabel_id {f : ℕ → ℕ} {t : STree E} (h : ∀ a ∈ t.labels, f a = a) : t.relabel f = t := by
  rw [relabel_congr h, relabel]
  exact subst_leaf t

/-! ## Grafting along a shuffle -/

section Graft

variable {A B C : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
  [Fintype C] [LinearOrder C] (i : A) (e : Without A i ⊕ B ≃ C)

/-- The positions in the composite of the inputs of the inner operation. -/
def posR (n : ℕ) : ℕ :=
  if h : n < Fintype.card B then opos (e (Sum.inr (oelt n h))) else 0

/-- The positions in the composite of the other inputs of the outer operation. -/
def posL (n : ℕ) : ℕ :=
  if h : n < Fintype.card A then
    (if h' : oelt n h = i then 0 else opos (e (Sum.inl ⟨oelt n h, h'⟩)))
  else 0

omit [Fintype A] in
lemma posR_opos (b : B) : posR i e (opos b) = opos (e (Sum.inr b)) := by
  rw [posR, dif_pos (opos_lt_card b), oelt_opos]

omit [Fintype B] [LinearOrder B] in
lemma posL_opos (a : Without A i) : posL i e (opos a.1) = opos (e (Sum.inl a)) := by
  rw [posL, dif_pos (opos_lt_card a.1)]
  simp only [oelt_opos, dif_neg a.2]

/-- **The family substituted in a graft**: the relabelled inner monomial at the position of `i`,
and the relabelled other leaves. -/
def graftFam (t : STree E) (n : ℕ) : STree E :=
  if n = opos i then t.relabel (posR i e) else leaf (posL i e n)

variable {i e}

lemma graftFam_opos (t : STree E) : graftFam i e t (opos i) = t.relabel (posR i e) := if_pos rfl

lemma graftFam_ne (t : STree E) (a : A) (ha : a ≠ i) :
    graftFam i e t (opos a) = leaf (opos (e (Sum.inl ⟨a, ha⟩))) := by
  rw [graftFam, if_neg (fun h => ha (opos_injective h))]
  exact congrArg leaf (posL_opos i e ⟨a, ha⟩)

variable (he : Operad.IsShuffle i e)
include he

omit [Fintype A] in
/-- The positions of the inputs of the inner operation increase. -/
lemma strictMonoOn_posR : StrictMonoOn (posR i e) {m | m < Fintype.card B} := by
  intro m hm m' hm' hmm'
  rw [posR, posR, dif_pos (show m < Fintype.card B from hm),
    dif_pos (show m' < Fintype.card B from hm'), opos_lt_opos]
  refine he.mono_right ?_
  rw [← opos_lt_opos, opos_oelt, opos_oelt]
  exact hmm'

lemma isShuffle_graftFam {t : STree E} (ht : t.IsShuffle)
    (htl : t.labels = (Finset.range (Fintype.card B)).val) (n : ℕ) :
    (graftFam i e t n).IsShuffle := by
  unfold graftFam
  split_ifs
  · refine isShuffle_relabel ht fun m hm m' hm' hmm' => ?_
    simp only [Set.mem_setOf_eq, htl, Finset.mem_val, Finset.mem_range] at hm hm'
    exact strictMonoOn_posR he hm hm' hmm'
  · exact isShuffle_leaf _

/-- **The substituted family of a graft increases with its least leaves.** -/
lemma strictMonoOn_graftFam {t : STree E} (ht : t.IsShuffle)
    (htl : t.labels = (Finset.range (Fintype.card B)).val) :
    StrictMonoOn (fun n => (graftFam i e t n).first) {n | n < Fintype.card A} := by
  have hB : 0 < Fintype.card B := by
    have := first_mem ht
    rw [htl] at this
    exact Nat.zero_lt_of_lt (Finset.mem_range.1 this)
  have hft : t.first = 0 := by
    have h1 := first_mem ht
    have h2 : ∀ a ∈ t.labels, t.first ≤ a := first_le ht
    rw [htl] at h1 h2
    exact Nat.le_zero.1 (h2 0 (Finset.mem_range.2 hB))
  set b₀ : B := oelt 0 hB
  have hb₀ : ∀ b : B, b₀ ≤ b := fun b => by
    rw [← opos_strictMono.le_iff_le, opos_oelt]
    exact Nat.zero_le _
  -- the least leaves of the substituted trees
  have hfirst : ∀ a : A, (graftFam i e t (opos a)).first =
      if h : a = i then opos (e (Sum.inr b₀)) else opos (e (Sum.inl ⟨a, h⟩)) := by
    intro a
    by_cases h : a = i
    · subst h
      rw [graftFam_opos, dif_pos rfl, first_relabel _ ht, hft, posR, dif_pos hB]
    · rw [graftFam_ne t a h, dif_neg h, first_leaf]
  intro n h₁ n' h₂ hnn'
  obtain ⟨a, rfl⟩ : ∃ a : A, opos a = n := ⟨oelt n h₁, opos_oelt n h₁⟩
  obtain ⟨a', rfl⟩ : ∃ a : A, opos a = n' := ⟨oelt n' h₂, opos_oelt n' h₂⟩
  have haa' : a < a' := opos_lt_opos.1 hnn'
  simp only
  rw [hfirst, hfirst]
  by_cases ha : a = i
  · subst ha
    rw [dif_pos rfl, dif_neg (ne_of_gt haa'), opos_lt_opos]
    have := (he.pointed ⟨a', ne_of_gt haa'⟩ b₀ hb₀).not
    rw [not_lt, not_lt] at this
    exact lt_of_le_of_ne (this.1 haa'.le) fun h => Sum.inr_ne_inl (e.injective h)
  · by_cases ha' : a' = i
    · subst ha'
      rw [dif_neg ha, dif_pos rfl, opos_lt_opos]
      exact (he.pointed ⟨a, ha⟩ b₀ hb₀).1 haa'
    · rw [dif_neg ha, dif_neg ha', opos_lt_opos]
      exact he.mono_left (show (⟨a, ha⟩ : Without A i) < ⟨a', ha'⟩ from haa')

/-- **The graft of shuffle monomials along a shuffle is a shuffle tree.** -/
lemma isShuffle_graft {s t : STree E} (hs : s.IsShuffle) (hsl : s.labels = (Finset.range
    (Fintype.card A)).val) (ht : t.IsShuffle) (htl : t.labels = (Finset.range
    (Fintype.card B)).val) : (s.subst (graftFam i e t)).IsShuffle :=
  isShuffle_subst hs (fun n _ => isShuffle_graftFam he ht htl n) fun n hn n' hn' hnn' => by
    simp only [Set.mem_setOf_eq, hsl, Finset.mem_val, Finset.mem_range] at hn hn'
    exact strictMonoOn_graftFam he ht htl hn hn' hnn'

omit he in
/-- **The leaves of a substituted family member**: the positions of the images of the inputs
lying over `a`. -/
lemma mem_labels_graftFam {t : STree E} (htl : t.labels = (Finset.range (Fintype.card B)).val)
    (a : A) {c : ℕ} : c ∈ (graftFam i e t (opos a)).labels ↔
      ∃ y : Without A i ⊕ B, Sum.elim Subtype.val (fun _ => i) y = a ∧ c = opos (e y) := by
  by_cases ha : a = i
  · subst ha
    rw [graftFam_opos, labels_relabel, htl, Multiset.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hm' := Finset.mem_range.1 hm
      refine ⟨Sum.inr (oelt m hm'), rfl, ?_⟩
      rw [posR, dif_pos hm']
    · rintro ⟨y | b, hy, rfl⟩
      · exact absurd hy y.2
      · exact ⟨opos b, Finset.mem_range.2 (opos_lt_card b), posR_opos a e b⟩
  · rw [graftFam_ne t a ha, labels_leaf, Multiset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨Sum.inl ⟨a, ha⟩, rfl, rfl⟩
    · rintro ⟨y | b, hy, rfl⟩
      · have : y = ⟨a, ha⟩ := Subtype.ext hy
        rw [this]
      · exact absurd hy.symm ha

omit he in
/-- **The leaves of a graft** are the positions of the composite. -/
lemma labels_graft {s t : STree E} (hsl : s.labels = (Finset.range (Fintype.card A)).val)
    (htl : t.labels = (Finset.range (Fintype.card B)).val) :
    (s.subst (graftFam i e t)).labels = (Finset.range (Fintype.card C)).val := by
  have hA : (Finset.range (Fintype.card A)).val = (Finset.univ : Finset A).val.map opos := by
    refine (Multiset.Nodup.ext (Finset.range _).nodup
      (Multiset.Nodup.map opos_injective Finset.univ.nodup)).2 fun n => ?_
    rw [Finset.mem_val, Finset.mem_range, Multiset.mem_map]
    constructor
    · intro hn
      exact ⟨oelt n hn, Finset.mem_univ _, opos_oelt n hn⟩
    · rintro ⟨a, -, rfl⟩
      exact opos_lt_card a
  rw [labels_subst, hsl, hA, Multiset.bind_map]
  refine (Multiset.Nodup.ext ?_ (Finset.range _).nodup).2 fun c => ?_
  · rw [Multiset.nodup_bind]
    refine ⟨fun a _ => ?_, Multiset.Nodup.pairwise (fun a _ a' _ haa' => ?_) Finset.univ.nodup⟩
    · by_cases ha : a = i
      · subst ha
        rw [graftFam_opos, labels_relabel, htl]
        refine Multiset.Nodup.map_on (fun m hm m' hm' h => ?_) (Finset.range _).nodup
        have hm₁ := Finset.mem_range.1 hm
        have hm₂ := Finset.mem_range.1 hm'
        rw [posR, posR, dif_pos hm₁, dif_pos hm₂] at h
        have h2 := Sum.inr_injective (e.injective (opos_injective h))
        rw [oelt_eq_iff, opos_oelt] at h2
        exact h2
      · rw [graftFam_ne t a ha, labels_leaf]
        exact Multiset.nodup_singleton _
    · refine Multiset.disjoint_left.2 fun hc hc' => haa' ?_
      obtain ⟨y, hy, rfl⟩ := (mem_labels_graftFam htl a).1 hc
      obtain ⟨y', hy', hyy'⟩ := (mem_labels_graftFam htl a').1 hc'
      rw [← hy, ← hy', e.injective (opos_injective hyy')]
  · simp only [Multiset.mem_bind, Finset.mem_val, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨a, hc⟩
      obtain ⟨y, -, rfl⟩ := (mem_labels_graftFam htl a).1 hc
      exact opos_lt_card _
    · intro hc
      refine ⟨Sum.elim Subtype.val (fun _ => i) (e.symm (oelt c hc)),
        (mem_labels_graftFam htl _).2 ⟨e.symm (oelt c hc), rfl, ?_⟩⟩
      rw [e.apply_symm_apply, opos_oelt]

/-- **The graft of shuffle monomials along a shuffle.** -/
def graft (s : SMono E (Finset.range (Fintype.card A))) (t : SMono E (Finset.range
    (Fintype.card B))) : SMono E (Finset.range (Fintype.card C)) :=
  ⟨s.1.subst (graftFam i e t.1), isShuffle_graft he s.isShuffle s.labels_eq t.isShuffle
    t.labels_eq, labels_graft s.labels_eq t.labels_eq⟩

end Graft

/-! ## The laws of grafting -/

section Laws

lemma subst_congr_range {A : Type} [Fintype A] [LinearOrder A] {s : STree E}
    (hs : s.labels = (Finset.range (Fintype.card A)).val) {xs ys : ℕ → STree E}
    (h : ∀ a : A, xs (opos a) = ys (opos a)) : s.subst xs = s.subst ys :=
  subst_congr s fun n hn => by
    rw [hs, Finset.mem_val, Finset.mem_range] at hn
    rw [← opos_oelt n hn]
    exact h _

lemma relabel_congr_range {A : Type} [Fintype A] [LinearOrder A] {t : STree E}
    (ht : t.labels = (Finset.range (Fintype.card A)).val) {f g : ℕ → ℕ}
    (h : ∀ a : A, f (opos a) = g (opos a)) : t.relabel f = t.relabel g :=
  subst_congr_range ht fun a => by rw [h a]

lemma relabel_subst (f : ℕ → ℕ) (t : STree E) (ys : ℕ → STree E) :
    (t.relabel f).subst ys = t.subst fun a => ys (f a) := by
  rw [relabel, subst_subst]
  rfl

lemma subst_relabel (t : STree E) (xs : ℕ → STree E) (g : ℕ → ℕ) :
    (t.subst xs).relabel g = t.subst fun a => (xs a).relabel g := by
  rw [relabel, subst_subst]
  rfl

@[simp] lemma relabel_leaf (f : ℕ → ℕ) (a : ℕ) : (leaf a : STree E).relabel f = leaf (f a) :=
  rfl

@[simp] lemma opos_unit : opos () = 0 := by
  simp [opos]

/-- **Grafting is equivariant** under order isomorphisms. -/
theorem subst_graftFam_map {A A' B B' C C' : Type} [Fintype A] [LinearOrder A] [Fintype A']
    [LinearOrder A'] [Fintype B] [LinearOrder B] [Fintype B'] [LinearOrder B'] [Fintype C]
    [LinearOrder C] [Fintype C'] [LinearOrder C'] (σ : A ≃o A') (τ : B ≃o B') (ρ : C ≃o C')
    (i : A) (e : Without A i ⊕ B ≃ C) (e' : Without A' (σ i) ⊕ B' ≃ C')
    (h : ∀ c, ρ (e c) = e' (Sym.compEquiv σ.toEquiv τ.toEquiv i c)) {s t : STree E}
    (hs : s.labels = (Finset.range (Fintype.card A)).val)
    (ht : t.labels = (Finset.range (Fintype.card B)).val) :
    s.subst (graftFam i e t) = s.subst (graftFam (σ i) e' t) := by
  refine subst_congr_range hs fun a => ?_
  by_cases ha : a = i
  · subst ha
    rw [graftFam_opos, show opos a = opos (σ a) from (opos_orderIso σ a).symm, graftFam_opos]
    refine relabel_congr_range ht fun b => ?_
    have h2 : posR (σ a) e' (opos b) = opos (e (Sum.inr b)) := by
      rw [← opos_orderIso τ b, posR_opos, ← opos_orderIso ρ (e (Sum.inr b)), h]
      rfl
    rw [posR_opos, h2]
  · have hσ : σ a ≠ σ i := fun h' => ha (σ.injective h')
    rw [graftFam_ne t a ha, show opos a = opos (σ a) from (opos_orderIso σ a).symm,
      graftFam_ne t (σ a) hσ, ← opos_orderIso ρ (e (Sum.inl ⟨a, ha⟩)), h]
    rfl

/-- **The right unit law of grafting.** -/
theorem subst_graftFam_one {A C : Type} [Fintype A] [LinearOrder A] [Fintype C] [LinearOrder C]
    (i : A) (e : Without A i ⊕ Unit ≃ C) (φ : A ≃o C)
    (hφ : ∀ a, φ a = e ((Sym.rightUnitEquiv i).symm a)) {s : STree E}
    (hs : s.labels = (Finset.range (Fintype.card A)).val) :
    s.subst (graftFam i e (leaf 0)) = s := by
  conv_rhs => rw [← subst_leaf s]
  refine subst_congr_range hs fun a => ?_
  by_cases ha : a = i
  · subst ha
    rw [graftFam_opos, relabel_leaf, ← opos_unit, posR_opos, ← Sym.rightUnitEquiv_symm_self a,
      ← hφ, opos_orderIso]
  · rw [graftFam_ne _ a ha, ← Sym.rightUnitEquiv_symm_of_ne ha, ← hφ, opos_orderIso]

/-- **The left unit law of grafting.** -/
theorem subst_graftFam_one_left {B C : Type} [Fintype B] [LinearOrder B] [Fintype C]
    [LinearOrder C] (e : Without Unit () ⊕ B ≃ C) (φ : B ≃o C) (hφ : ∀ b, φ b = e (Sum.inr b))
    {t : STree E} (ht : t.labels = (Finset.range (Fintype.card B)).val) :
    (leaf 0).subst (graftFam () e t) = t := by
  rw [subst_leaf', ← opos_unit, graftFam_opos]
  refine (relabel_congr_range ht fun b => ?_).trans (relabel_id fun a _ => rfl)
  rw [posR_opos, ← hφ, opos_orderIso]

/-- **Sequential associativity of grafting.** -/
theorem subst_graftFam_seq {A B D C₁ C₃ C : Type} [Fintype A] [LinearOrder A] [Fintype B]
    [LinearOrder B] [Fintype D] [LinearOrder D] [Fintype C₁] [LinearOrder C₁] [Fintype C₃]
    [LinearOrder C₃] [Fintype C] [LinearOrder C] (i : A) (j : B) (e₁ : Without A i ⊕ B ≃ C₁)
    (e₂ : Without C₁ (e₁ (Sum.inr j)) ⊕ D ≃ C) (e₃ : Without B j ⊕ D ≃ C₃)
    (e₄ : Without A i ⊕ C₃ ≃ C)
    (h₁ : ∀ a : Without A i, e₂ (Sum.inl ⟨e₁ (Sum.inl a),
      fun h => Sum.inl_ne_inr (e₁.injective h)⟩) = e₄ (Sum.inl a))
    (h₂ : ∀ b : Without B j, e₂ (Sum.inl ⟨e₁ (Sum.inr b.1),
      fun h => b.2 (Sum.inr_injective (e₁.injective h))⟩) = e₄ (Sum.inr (e₃ (Sum.inl b))))
    (h₃ : ∀ d : D, e₂ (Sum.inr d) = e₄ (Sum.inr (e₃ (Sum.inr d)))) {s t u : STree E}
    (hs : s.labels = (Finset.range (Fintype.card A)).val)
    (ht : t.labels = (Finset.range (Fintype.card B)).val)
    (hu : u.labels = (Finset.range (Fintype.card D)).val) :
    (s.subst (graftFam i e₁ t)).subst (graftFam (e₁ (Sum.inr j)) e₂ u) =
      s.subst (graftFam i e₄ (t.subst (graftFam j e₃ u))) := by
  rw [subst_subst]
  refine subst_congr_range hs fun a => ?_
  by_cases ha : a = i
  · subst ha
    rw [graftFam_opos, graftFam_opos, relabel_subst, subst_relabel]
    refine subst_congr_range ht fun b => ?_
    by_cases hb : b = j
    · subst hb
      rw [posR_opos, graftFam_opos, graftFam_opos, relabel_relabel]
      refine relabel_congr_range hu fun d => ?_
      rw [Function.comp_apply, posR_opos, posR_opos, posR_opos, h₃ d]
    · have hb' : e₁ (Sum.inr b) ≠ e₁ (Sum.inr j) :=
        fun h => hb (Sum.inr_injective (e₁.injective h))
      rw [posR_opos, graftFam_ne u _ hb', graftFam_ne u b hb, relabel_leaf, posR_opos]
      exact congrArg (fun x => leaf (opos x)) (h₂ ⟨b, hb⟩)
  · have ha' : e₁ (Sum.inl ⟨a, ha⟩) ≠ e₁ (Sum.inr j) := fun h => Sum.inl_ne_inr (e₁.injective h)
    rw [graftFam_ne t a ha, subst_leaf', graftFam_ne u _ ha', graftFam_ne _ a ha]
    exact congrArg (fun x => leaf (opos x)) (h₁ ⟨a, ha⟩)

/-- **Parallel associativity of grafting.** -/
theorem subst_graftFam_par {A B D C₁ C₃ C : Type} [Fintype A] [LinearOrder A] [Fintype B]
    [LinearOrder B] [Fintype D] [LinearOrder D] [Fintype C₁] [LinearOrder C₁] [Fintype C₃]
    [LinearOrder C₃] [Fintype C] [LinearOrder C] {i k : A} (hik : i ≠ k)
    (e₁ : Without A i ⊕ B ≃ C₁) (e₂ : Without C₁ (e₁ (Sum.inl ⟨k, Ne.symm hik⟩)) ⊕ D ≃ C)
    (e₃ : Without A k ⊕ D ≃ C₃) (e₄ : Without C₃ (e₃ (Sum.inl ⟨i, hik⟩)) ⊕ B ≃ C)
    (h₁ : ∀ (a : A) (hai : a ≠ i) (hak : a ≠ k),
      e₂ (Sum.inl ⟨e₁ (Sum.inl ⟨a, hai⟩), fun h => hak (congrArg Subtype.val
        (Sum.inl_injective (e₁.injective h)))⟩)
        = e₄ (Sum.inl ⟨e₃ (Sum.inl ⟨a, hak⟩), fun h => hai (congrArg Subtype.val
          (Sum.inl_injective (e₃.injective h)))⟩))
    (h₂ : ∀ b : B, e₂ (Sum.inl ⟨e₁ (Sum.inr b), fun h => Sum.inr_ne_inl (e₁.injective h)⟩)
      = e₄ (Sum.inr b))
    (h₃ : ∀ d : D, e₂ (Sum.inr d)
      = e₄ (Sum.inl ⟨e₃ (Sum.inr d), fun h => Sum.inr_ne_inl (e₃.injective h)⟩))
    {s t u : STree E} (hs : s.labels = (Finset.range (Fintype.card A)).val)
    (ht : t.labels = (Finset.range (Fintype.card B)).val)
    (hu : u.labels = (Finset.range (Fintype.card D)).val) :
    (s.subst (graftFam i e₁ t)).subst (graftFam (e₁ (Sum.inl ⟨k, Ne.symm hik⟩)) e₂ u) =
      (s.subst (graftFam k e₃ u)).subst (graftFam (e₃ (Sum.inl ⟨i, hik⟩)) e₄ t) := by
  rw [subst_subst, subst_subst]
  refine subst_congr_range hs fun a => ?_
  by_cases hai : a = i
  · subst hai
    rw [graftFam_opos, relabel_subst, graftFam_ne u a hik, subst_leaf', graftFam_opos, relabel]
    refine subst_congr_range ht fun b => ?_
    rw [posR_opos, posR_opos, graftFam_ne u _ (fun h => Sum.inr_ne_inl (e₁.injective h))]
    exact congrArg (fun x => leaf (opos x)) (h₂ b)
  · by_cases hak : a = k
    · subst hak
      rw [graftFam_ne t a hai, subst_leaf', graftFam_opos, graftFam_opos, relabel_subst]
      conv_lhs => rw [relabel]
      refine subst_congr_range hu fun d => ?_
      rw [posR_opos, posR_opos, graftFam_ne t _ (fun h => Sum.inr_ne_inl (e₃.injective h))]
      exact congrArg (fun x => leaf (opos x)) (h₃ d)
    · rw [graftFam_ne t a hai, subst_leaf', graftFam_ne u a hak, subst_leaf',
        graftFam_ne u _ (fun h => hak (congrArg Subtype.val (Sum.inl_injective (e₁.injective h)))),
        graftFam_ne t _ (fun h => hai (congrArg Subtype.val (Sum.inl_injective (e₃.injective h))))]
      exact congrArg (fun x => leaf (opos x)) (h₁ a hai hak)

end Laws

/-- Transport a monomial along an equality of leaf sets. -/
def SMono.cast {A A' : Finset ℕ} (h : A = A') (t : SMono E A) : SMono E A' :=
  ⟨t.1, t.2.1, h ▸ t.2.2⟩

@[simp] lemma SMono.cast_val {A A' : Finset ℕ} (h : A = A') (t : SMono E A) :
    (t.cast h).1 = t.1 := rfl

end STree

open STree

/-! ## The free shuffle operad -/

section FreeSh

variable (K : Type u) [CommRing K] (E : ℕ → Type v)

/-- **The free shuffle operad** on the generators `E k` of arity `k`, on a finite linear order
`A`: the combinations of shuffle monomials whose leaves are the positions of the elements of
`A`. -/
@[nolint unusedArguments]
abbrev FreeSh (A : Type) [Fintype A] [LinearOrder A] : Type (max v u) :=
  SMono E (Finset.range (Fintype.card A)) →₀ K

namespace FreeSh

variable {K E}

/-- **The bilinear extension** of a map on pairs of basis elements. -/
noncomputable def bil {X Y Z : Type*} (f : X → Y → Z) :
    (X →₀ K) →ₗ[K] (Y →₀ K) →ₗ[K] (Z →₀ K) :=
  Finsupp.linearCombination K fun x => Finsupp.linearCombination K fun y =>
    Finsupp.single (f x y) (1 : K)

lemma bil_single {X Y Z : Type*} (f : X → Y → Z) (x : X) (y : Y) (a b : K) :
    bil f (Finsupp.single x a) (Finsupp.single y b) = Finsupp.single (f x y) (a * b) := by
  rw [bil, Finsupp.linearCombination_single, LinearMap.smul_apply,
    Finsupp.linearCombination_single, smul_smul, Finsupp.smul_single, smul_eq_mul, mul_one,
    mul_comm]

/-- **Relabelling along an order isomorphism**: the monomials are unchanged. -/
noncomputable def mapM {A B : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    (σ : A ≃o B) : FreeSh K E A →ₗ[K] FreeSh K E B :=
  Finsupp.lmapDomain K K (SMono.cast (congrArg Finset.range (Fintype.card_congr σ.toEquiv)))

lemma mapM_single {A B : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    (σ : A ≃o B) (x : SMono E (Finset.range (Fintype.card A))) (a : K) :
    mapM σ (Finsupp.single x a) = Finsupp.single (x.cast
      (congrArg Finset.range (Fintype.card_congr σ.toEquiv))) a :=
  Finsupp.mapDomain_single

/-- **The unit**: the monomial with one leaf. -/
def oneM : SMono E (Finset.range (Fintype.card Unit)) :=
  ⟨leaf 0, isShuffle_leaf 0, by simp⟩

/-- Bilinear identities are checked on basis elements. -/
lemma bil_ext {X Y M : Type*} [AddCommGroup M] [Module K M]
    {f g : (X →₀ K) →ₗ[K] (Y →₀ K) →ₗ[K] M}
    (h : ∀ x y, f (Finsupp.single x 1) (Finsupp.single y 1) =
      g (Finsupp.single x 1) (Finsupp.single y 1)) : f = g :=
  Finsupp.lhom_ext' fun x => LinearMap.ext_ring
    (Finsupp.lhom_ext' fun y => LinearMap.ext_ring (h x y))

lemma mapM_refl {A : Type} [Fintype A] [LinearOrder A] (x : FreeSh K E A) :
    mapM (OrderIso.refl A) x = x := by
  have : SMono.cast (E := E) (congrArg Finset.range
      (Fintype.card_congr (OrderIso.refl A).toEquiv)) = id := funext fun t => Subtype.ext rfl
  show Finsupp.mapDomain _ x = x
  rw [this, Finsupp.mapDomain_id]

lemma mapM_trans {A B C : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    [Fintype C] [LinearOrder C] (σ : A ≃o B) (τ : B ≃o C) (x : FreeSh K E A) :
    mapM (σ.trans τ) x = mapM τ (mapM σ x) := by
  show Finsupp.mapDomain _ x = Finsupp.mapDomain _ (Finsupp.mapDomain _ x)
  rw [← Finsupp.mapDomain_comp]
  rfl

section Comp

variable {A A' B B' C C' : Type} [Fintype A] [LinearOrder A] [Fintype A'] [LinearOrder A']
  [Fintype B] [LinearOrder B] [Fintype B'] [LinearOrder B'] [Fintype C] [LinearOrder C]
  [Fintype C'] [LinearOrder C']

lemma mapM_bil_graft (σ : A ≃o A') (τ : B ≃o B') (ρ : C ≃o C') (i : A)
    {e : Without A i ⊕ B ≃ C} (he : IsShuffle i e) {e' : Without A' (σ i) ⊕ B' ≃ C'}
    (he' : IsShuffle (σ i) e') (h : ∀ c, ρ (e c) = e' (Sym.compEquiv σ.toEquiv τ.toEquiv i c))
    (x : FreeSh K E A) (y : FreeSh K E B) :
    mapM ρ (bil (graft he) x y) = bil (graft he') (mapM σ x) (mapM τ y) := by
  have key := bil_ext (f := (bil (graft (E := E) he)).compr₂ (mapM (K := K) ρ))
    (g := (bil (graft he')).compl₁₂ (mapM σ) (mapM τ)) fun s t => by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, bil_single, mapM_single,
        mul_one]
      congr 1
      exact Subtype.ext (subst_graftFam_map σ τ ρ i e e' h s.labels_eq t.labels_eq)
  exact congrArg (fun F => F x y) key

lemma bil_graft_one (i : A) {e : Without A i ⊕ Unit ≃ C} (he : IsShuffle i e) (φ : A ≃o C)
    (hφ : ∀ a, φ a = e ((Sym.rightUnitEquiv i).symm a)) (x : FreeSh K E A) :
    bil (graft he) x (Finsupp.single oneM 1) = mapM φ x := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, LinearMap.zero_apply, map_zero]
  | add x x' hx hx' => rw [map_add, LinearMap.add_apply, hx, hx', map_add]
  | single s a =>
    rw [bil_single, mapM_single, mul_one]
    congr 1
    exact Subtype.ext (subst_graftFam_one i e φ hφ s.labels_eq)

lemma bil_one_graft {e : Without Unit () ⊕ B ≃ C} (he : IsShuffle () e) (φ : B ≃o C)
    (hφ : ∀ b, φ b = e (Sum.inr b)) (y : FreeSh K E B) :
    bil (graft he) (Finsupp.single oneM 1) y = mapM φ y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' => rw [map_add, hy, hy', map_add]
  | single t b =>
    rw [bil_single, mapM_single, one_mul]
    congr 1
    exact Subtype.ext (subst_graftFam_one_left e φ hφ t.labels_eq)

end Comp

end FreeSh

open FreeSh in
/-- **The free shuffle operad on generators of any arity.** -/
noncomputable instance FreeSh.instShuffleOperad : ShuffleOperad K (FreeSh K E) where
  map σ := mapM σ
  map_refl x := mapM_refl x
  map_trans σ τ x := mapM_trans σ τ x
  one := Finsupp.single oneM 1
  comp i e he := bil (graft he)
  map_comp σ τ ρ i e he e' he' h x y := mapM_bil_graft σ τ ρ i he he' h x y
  comp_one i e he φ hφ x := bil_graft_one i he φ hφ x
  one_comp e he φ hφ y := bil_one_graft he φ hφ y
  comp_assoc_seq i j e₁ he₁ e₂ he₂ e₃ he₃ e₄ he₄ h₁ h₂ h₃ x y z := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | single t b =>
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | single u c =>
      show bil (graft he₂) (bil (graft he₁) _ _) _ = bil (graft he₄) _ (bil (graft he₃) _ _)
      rw [bil_single, bil_single, bil_single, bil_single, mul_assoc]
      congr 1
      exact Subtype.ext (subst_graftFam_seq i j e₁ e₂ e₃ e₄ h₁ h₂ h₃ s.labels_eq t.labels_eq
        u.labels_eq)
  comp_assoc_par hik e₁ he₁ e₂ he₂ e₃ he₃ e₄ he₄ h₁ h₂ h₃ x y z := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | single t b =>
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
    | single u c =>
      show bil (graft he₂) (bil (graft he₁) _ _) _ = bil (graft he₄) (bil (graft he₃) _ _) _
      rw [bil_single, bil_single, bil_single, bil_single, mul_right_comm]
      congr 1
      exact Subtype.ext (subst_graftFam_par hik e₁ e₂ e₃ e₄ h₁ h₂ h₃ s.labels_eq t.labels_eq
        u.labels_eq)

end FreeSh

/-! ## Presentations -/

namespace STree

variable {E : ℕ → Type v} {A B C : Type} [Fintype A] [LinearOrder A] [Fintype B]
  [LinearOrder B] [Fintype C] [LinearOrder C] {i : A} {e : Without A i ⊕ B ≃ C}
  (he : Operad.IsShuffle i e)
include he

/-- **Grafting a fixed inner monomial is a context.** -/
theorem isSCtx_graft_left (t : SMono E (Finset.range (Fintype.card B))) :
    IsSCtx (fun s : SMono E (Finset.range (Fintype.card A)) => graft he s t) := by
  refine ⟨leaf 0, [], graftFam i e t.1, by rw [get?_nil]; rfl,
    ⟨fun n _ => isShuffle_graftFam he t.isShuffle t.labels_eq n, fun n hn c hc => ?_,
      fun n hn n' hn' hnn' => strictMonoOn_graftFam he t.isShuffle t.labels_eq
        (Finset.mem_range.1 hn) (Finset.mem_range.1 hn') hnn'⟩, fun s => ?_⟩
  · have hn' := Finset.mem_range.1 hn
    rw [← opos_oelt n hn'] at hc
    obtain ⟨y, -, rfl⟩ := (mem_labels_graftFam t.labels_eq _).1 hc
    exact Finset.mem_range.2 (opos_lt_card _)
  · rw [replace_nil]
    rfl

/-- **Grafting into a fixed outer monomial is a context.** -/
theorem isSCtx_graft_right (s : SMono E (Finset.range (Fintype.card A))) :
    IsSCtx (fun t : SMono E (Finset.range (Fintype.card B)) => graft he s t) := by
  have hi : opos i ∈ s.1.labels := by
    rw [s.labels_eq]
    exact Finset.mem_range.2 (opos_lt_card i)
  refine ⟨s.1.subst (graftFam i e (leaf 0)), s.1.pos (opos i), fun b => leaf (posR i e b), ?_,
    ⟨fun _ _ => isShuffle_leaf _, fun b hb c hc => ?_, fun b hb b' hb' h =>
      strictMonoOn_posR he (Finset.mem_range.1 hb) (Finset.mem_range.1 hb') h⟩, fun t => ?_⟩
  · rw [get?_subst (get?_pos hi)]
    rfl
  · rw [labels_leaf, Multiset.mem_singleton] at hc
    subst hc
    rw [posR, dif_pos (Finset.mem_range.1 hb)]
    exact Finset.mem_range.2 (opos_lt_card _)
  · show s.1.subst (graftFam i e t.1) = (s.1.subst (graftFam i e (leaf 0))).replace
      (s.1.pos (opos i)) (t.1.subst fun b => leaf (posR i e b))
    rw [← subst_update s.nodup (get?_pos hi)]
    congr 1
    funext n
    by_cases hn : n = opos i
    · subst hn
      rw [Function.update_self, graftFam_opos]
      rfl
    · rw [Function.update_of_ne hn]
      unfold graftFam
      rw [if_neg hn, if_neg hn]

end STree

namespace FreeSh

variable {K : Type u} [CommRing K]

lemma bil_single_right {X Y Z : Type*} (f : X → Y → Z) (x : X →₀ K) (y : Y) (b : K) :
    bil f x (Finsupp.single y b) = b • Finsupp.mapDomain (fun s => f s y) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [map_add, LinearMap.add_apply, hx, hx', Finsupp.mapDomain_add,
      smul_add]
  | single s a => rw [bil_single, Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul,
      mul_comm]

lemma bil_single_left {X Y Z : Type*} (f : X → Y → Z) (x : X) (a : K) (y : Y →₀ K) :
    bil f (Finsupp.single x a) y = a • Finsupp.mapDomain (f x) y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' => rw [map_add, hy, hy', Finsupp.mapDomain_add, smul_add]
  | single t b => rw [bil_single, Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul]

end FreeSh

open STree FreeSh

variable {K : Type u} [CommRing K] {E : ℕ → Type v} {ρ : Type*} {O : STree.AdmOrder E}
  (G : Rules K ρ O.toCtxOrder)

lemma Rules.ideal_cast {X Y : Finset ℕ} (h : X = Y) {v : SMono E X →₀ K}
    (hv : v ∈ (G.rw X).ideal) : Finsupp.mapDomain (SMono.cast h) v ∈ (G.rw Y).ideal := by
  subst h
  have : (SMono.cast rfl : SMono E X → SMono E X) = id := funext fun t => Subtype.ext rfl
  rwa [this, Finsupp.mapDomain_id]

/-- **The ideal of rules is an ideal of the free shuffle operad**: the rewriting ideal is stable
under relabelling and under grafting on either side, grafting being a context. -/
noncomputable def Rules.shuffleIdeal : ShuffleOperadIdeal K (FreeSh K E) where
  sub A := (G.rw (Finset.range (Fintype.card A))).ideal
  map_mem σ := fun hx => G.ideal_cast _ hx
  comp_mem_left i e he := fun y hx => by
    show bil (graft he) _ y ∈ _
    induction y using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y y' hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
    | single t b =>
      rw [bil_single_right]
      exact Submodule.smul_mem _ _ (G.mapDomain_mem_ideal (isSCtx_graft_left he t) hx)
  comp_mem_right i e he x := fun hy => by
    show bil (graft he) x _ ∈ _
    induction x using Finsupp.induction_linear with
    | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
    | add x x' hx hx' => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hx'
    | single s a =>
      rw [bil_single_left]
      exact Submodule.smul_mem _ _ (G.mapDomain_mem_ideal (isSCtx_graft_right he s) hy)

/-- **The shuffle operad presented by rules**: the free shuffle operad modulo the ideal of the
rules. -/
abbrev Rules.Presented := G.shuffleIdeal.Quot

/-- **The PBW basis** (Dotsenko–Khoroshkin): when the rules are resolvable — by the Buchberger
criterion, when their critical ambiguities are — the normal monomials are a basis of the shuffle
operad they present, on every finite linear order. -/
noncomputable def Rules.presentedBasis (hres : ∀ C, (G.rw C).Resolvable) (A : Type) [Fintype A]
    [LinearOrder A] :
    Module.Basis (G.rw (Finset.range (Fintype.card A))).Irr K (G.Presented A) :=
  (hres _).basis

theorem Rules.presentedBasis_apply (hres : ∀ C, (G.rw C).Resolvable) (A : Type) [Fintype A]
    [LinearOrder A] (m : (G.rw (Finset.range (Fintype.card A))).Irr) :
    G.presentedBasis hres A m = G.shuffleIdeal.proj A (Finsupp.single (m : SMono E _) 1) :=
  (hres _).basis_apply m

end Operad
