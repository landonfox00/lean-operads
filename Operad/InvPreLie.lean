/-
# The pre-Lie algebra of invariant families of a graded operad

An **invariant family** of a graded operad `Q` is an operation `q A ∈ Q A` for every finite type
`A`, compatible with all relabellings (`GrOperad.Inv`): the invariants of the symmetric groups,
arity by arity. Plugging one invariant family into another in all possible ways,

  `(q ⋆ q') X = ∑_{∅ ≠ S ⊆ X} q (X / S) ∘_S q' S`,

with `X / S` the inputs outside `S` and a new input for the composite, gives an invariant family
(`GrOperad.Inv.star`). For the convolution operad of a cooperad and an operad, the invariant
families are the equivariant maps, and this is the convolution product.

* **Splittings.** A subset `S` of `X` splits it into the inputs `SOut S = (X ∖ S) ⊔ {none}` of an
  outer operation and the inputs `SIn S = S` of an inner one (`splitEquiv`). Any composite
  `x ∘ᵢ y` relabelled onto `X` is the composite at the splitting by the inputs of `y`, of `x` and
  `y` relabelled (`GrOperad.map_comp_canon`).
* **The associator** `(q ⋆ q') ⋆ q'' - q ⋆ (q' ⋆ q'')` is the sum of the terms in which `q'` and
  `q''` are plugged into `q` at disjoint subsets (`GrOperad.Inv.assoc_eq_sum_disj`): the nested
  terms of the two products are the same, by sequential associativity. By parallel
  associativity, exchanging the two subsets together with `q'` and `q''` costs the Koszul sign
  (`GrOperad.Inv.disj_swap`), hence **the graded pre-Lie identity** (`GrOperad.Inv.preLie`), and
  **the associator with an odd family twice vanishes** (`GrOperad.Inv.assoc_odd`), without
  dividing by two: the terms cancel in pairs.
* The product adds parities (`GrOperad.Inv.isPar_star`), morphisms of graded operads preserve it
  (`GrOperad.Inv.appHom_star`), and **derivations are derivations of the product**
  (`GrOperad.Inv.appDer_star`).
-/
import Operad.GrDerivation

universe u v w

/- The input types of nested composites are nested sums of subtypes, which carry decidable
equality in their types: their instances grow exponentially with the nesting depth. -/
set_option synthInstance.maxSize 2048

namespace Operad

open Sym GerBV

/-! ## Splittings -/

section Split

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The inputs of the outer operation of the splitting of `X` by `S`: the elements outside `S`,
and a new input `none` for the inner operation. -/
abbrev SOut (S : Finset X) : Type := Option {x : X // x ∉ S}

/-- The finite type of outer inputs, as one instance: nested splittings would otherwise build
instances exponentially large in the depth. -/
instance (priority := high) instFintypeSOut (S : Finset X) : Fintype (SOut S) :=
  inferInstanceAs (Fintype (Option {x : X // x ∉ S}))

/-- Decidable equality of outer inputs, as one instance. -/
instance (priority := high) instDecidableEqSOut (S : Finset X) : DecidableEq (SOut S) :=
  inferInstanceAs (DecidableEq (Option {x : X // x ∉ S}))

/-- The inputs of the inner operation of the splitting of `X` by `S`. -/
abbrev SIn (S : Finset X) : Type := {x : X // x ∈ S}

/-- The finite type of inner inputs, as one instance. -/
instance (priority := high) instFintypeSIn (S : Finset X) : Fintype (SIn S) :=
  inferInstanceAs (Fintype {x : X // x ∈ S})

/-- Decidable equality of inner inputs, as one instance. -/
instance (priority := high) instDecidableEqSIn (S : Finset X) : DecidableEq (SIn S) :=
  inferInstanceAs (DecidableEq {x : X // x ∈ S})

/-- The element of `X` named by an input of the outer operation other than `none`. -/
def outVal {S : Finset X} : (o : SOut S) → o ≠ none → X
  | some x, _ => x.1
  | none, h => absurd rfl h

omit [Fintype X] [DecidableEq X] in
@[simp] lemma outVal_some {S : Finset X} (x : {x : X // x ∉ S}) (h : some x ≠ none) :
    outVal (some x) h = x.1 := rfl

omit [Fintype X] [DecidableEq X] in
lemma outVal_eq_of_eq {S : Finset X} {o : SOut S} (h : o ≠ none) {x : {x : X // x ∉ S}}
    (hx : o = some x) : outVal o h = x.1 := by
  subst hx
  rfl

omit [Fintype X] [DecidableEq X] in
lemma outVal_not_mem {S : Finset X} (o : SOut S) (h : o ≠ none) : outVal o h ∉ S := by
  cases o with
  | none => exact absurd rfl h
  | some x => exact x.2

/-- **The splitting of `X` by a subset `S`**: the inputs of `X` outside `S`, and those in `S`. -/
def splitEquiv (S : Finset X) : Without (SOut S) none ⊕ SIn S ≃ X where
  toFun z := Sum.elim (fun o => outVal o.1 o.2) (fun x => x.1) z
  invFun x := if h : x ∈ S then Sum.inr ⟨x, h⟩ else Sum.inl ⟨some ⟨x, h⟩, Option.some_ne_none _⟩
  left_inv := by
    rintro (⟨(_ | ⟨x, hx⟩), h⟩ | ⟨x, hx⟩)
    · exact absurd rfl h
    · simp [hx]
    · simp [hx]
  right_inv x := by
    by_cases h : x ∈ S <;> simp [h]

omit [Fintype X] in
@[simp] lemma splitEquiv_inl (S : Finset X) (o : Without (SOut S) none) :
    splitEquiv S (Sum.inl o) = outVal o.1 o.2 := rfl

omit [Fintype X] in
@[simp] lemma splitEquiv_inr (S : Finset X) (x : SIn S) : splitEquiv S (Sum.inr x) = x.1 := rfl

/-- The subset of the outer inputs of the splitting by `S` made of the elements of `T₀`, and of
the new input when `b`. -/
def liftOut (S : Finset X) (b : Bool) (T₀ : Finset X) : Finset (SOut S) :=
  Finset.univ.filter fun o => Option.elim o b (fun x => decide (x.1 ∈ T₀)) = true

@[simp] lemma none_mem_liftOut (S : Finset X) (b : Bool) (T₀ : Finset X) :
    (none : SOut S) ∈ liftOut S b T₀ ↔ b = true := by
  simp [liftOut]

@[simp] lemma some_mem_liftOut (S : Finset X) (b : Bool) (T₀ : Finset X) (x : {x : X // x ∉ S}) :
    (some x : SOut S) ∈ liftOut S b T₀ ↔ x.1 ∈ T₀ := by
  simp [liftOut]

/-- The subset of the inputs of the splitting by `V` made of the elements of `U₀`. -/
def restrIn (V U₀ : Finset X) : Finset (SIn V) := Finset.univ.filter fun v => v.1 ∈ U₀

omit [Fintype X] in
@[simp] lemma mem_restrIn (V U₀ : Finset X) (v : SIn V) : v ∈ restrIn V U₀ ↔ v.1 ∈ U₀ := by
  simp [restrIn]

/-- The elements of `X` named by a subset of the outer inputs of the splitting by `S`. -/
def projOut (S : Finset X) (T : Finset (SOut S)) : Finset X :=
  (Finset.eraseNone T).map (Function.Embedding.subtype _)

omit [Fintype X] [DecidableEq X] in
lemma mem_projOut {S : Finset X} {T : Finset (SOut S)} {x : X} :
    x ∈ projOut S T ↔ ∃ h : x ∉ S, (some ⟨x, h⟩ : SOut S) ∈ T := by
  simp [projOut]

omit [Fintype X] [DecidableEq X] in
lemma disjoint_projOut (S : Finset X) (T : Finset (SOut S)) : Disjoint S (projOut S T) :=
  Finset.disjoint_right.2 fun _ hx => (mem_projOut.1 hx).1

lemma projOut_liftOut {S T₀ : Finset X} (hd : Disjoint S T₀) (b : Bool) :
    projOut S (liftOut S b T₀) = T₀ := by
  ext x
  rw [mem_projOut]
  constructor
  · rintro ⟨_, h⟩
    exact (some_mem_liftOut _ _ _ _).1 h
  · intro hx
    exact ⟨Finset.disjoint_right.1 hd hx, (some_mem_liftOut _ _ _ _).2 hx⟩

lemma liftOut_projOut {S : Finset X} {T : Finset (SOut S)} {b : Bool}
    (hb : (none : SOut S) ∈ T ↔ b = true) : liftOut S b (projOut S T) = T := by
  ext o
  rcases o with (_ | ⟨x, hx⟩)
  · rw [none_mem_liftOut, hb]
  · rw [some_mem_liftOut, mem_projOut]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩

/-- The nonempty subsets. -/
abbrev nonempties (X : Type) [Fintype X] : Finset (Finset X) :=
  Finset.univ.filter fun S => S.Nonempty

/-- The pairs of disjoint nonempty subsets. -/
def disjPairs (X : Type) [Fintype X] [DecidableEq X] : Finset (Finset X × Finset X) :=
  (nonempties X ×ˢ nonempties X).filter fun p => Disjoint p.1 p.2

variable {M : Type*} [AddCommMonoid M]

/-- **A sum over the nonempty subsets of the outer inputs**: those containing the new input, and
those not. -/
lemma sum_nonempties_out (S : Finset X) (f : Finset (SOut S) → M) :
    ∑ T ∈ nonempties (SOut S), f T
      = ∑ T₀ ∈ Finset.univ.filter (fun T₀ => Disjoint S T₀), f (liftOut S true T₀)
        + ∑ T₀ ∈ (nonempties X).filter (fun T₀ => Disjoint S T₀), f (liftOut S false T₀) := by
  rw [← Finset.sum_filter_add_sum_filter_not (nonempties (SOut S)) (fun T => none ∈ T)]
  congr 1
  · symm
    refine Finset.sum_nbij' (liftOut S true) (projOut S) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro T₀ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨none, (none_mem_liftOut _ _ _).2 rfl⟩, (none_mem_liftOut _ _ _).2 rfl⟩
    · intro T _
      simpa using disjoint_projOut S T
    · intro T₀ hT₀
      exact projOut_liftOut (by simpa using hT₀) true
    · intro T hT
      simp only [Finset.mem_filter] at hT
      exact liftOut_projOut (by simpa using hT.2)
  · symm
    refine Finset.sum_nbij' (liftOut S false) (projOut S) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro T₀ hT₀
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT₀ ⊢
      obtain ⟨⟨x, hx⟩, hd⟩ := hT₀
      exact ⟨⟨some ⟨x, Finset.disjoint_right.1 hd hx⟩, (some_mem_liftOut _ _ _ _).2 hx⟩,
        by simp⟩
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      refine ⟨?_, disjoint_projOut S T⟩
      obtain ⟨⟨o, ho⟩, hn⟩ := hT
      rcases o with (_ | ⟨x, hx⟩)
      · exact absurd ho hn
      · exact ⟨x, mem_projOut.2 ⟨hx, ho⟩⟩
    · intro T₀ hT₀
      simp only [Finset.mem_filter] at hT₀
      exact projOut_liftOut hT₀.2 false
    · intro T hT
      simp only [Finset.mem_filter] at hT
      exact liftOut_projOut (by simpa using hT.2)

/-- **A sum over the nonempty subsets of the inner inputs**, as a sum over subsets of `X`. -/
lemma sum_nonempties_in (V : Finset X) (f : Finset (SIn V) → M) :
    ∑ U ∈ nonempties (SIn V), f U
      = ∑ U₀ ∈ (nonempties X).filter (· ⊆ V), f (restrIn V U₀) := by
  symm
  refine Finset.sum_nbij' (restrIn V) (fun U => U.map (Function.Embedding.subtype _)) ?_ ?_ ?_ ?_
    (fun _ _ => rfl)
  · intro U₀ hU₀
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU₀ ⊢
    obtain ⟨⟨x, hx⟩, hV⟩ := hU₀
    exact ⟨⟨x, hV hx⟩, (mem_restrIn _ _ _).2 hx⟩
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
    refine ⟨hU.map, fun x hx => ?_⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.1 hx
    exact v.2
  · intro U₀ hU₀
    simp only [Finset.mem_filter] at hU₀
    ext x
    simp only [Finset.mem_map, mem_restrIn, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨⟨x, hU₀.2 hx⟩, hx, rfl⟩
  · intro U _
    ext v
    simp only [mem_restrIn, Finset.mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨w, hw, hwv⟩
      rwa [← Subtype.ext hwv]
    · intro hv
      exact ⟨v, hv, rfl⟩

/-- **Reindexing the nested pairs**: a pair of disjoint subsets `S`, `T₀` is the pair
`S ⊆ S ∪ T₀`. -/
lemma sum_nested_pairs (F : Finset X → Finset X → M) :
    ∑ S ∈ nonempties X, ∑ T₀ ∈ Finset.univ.filter (fun T₀ => Disjoint S T₀), F (S ∪ T₀) S
      = ∑ V ∈ nonempties X, ∑ U₀ ∈ (nonempties X).filter (· ⊆ V), F V U₀ := by
  have h1 : ∀ S : Finset X, ∑ T₀ ∈ Finset.univ.filter (fun T₀ => Disjoint S T₀), F (S ∪ T₀) S
      = ∑ V ∈ Finset.univ.filter (fun V => S ⊆ V), F V S := fun S => by
    refine Finset.sum_nbij' (S ∪ ·) (· \ S) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro T₀ _
      simp
    · intro V _
      simp [Finset.disjoint_sdiff]
    · intro T₀ hT₀
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT₀
      exact Finset.union_sdiff_cancel_left hT₀
    · intro V hV
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV
      exact Finset.union_sdiff_of_subset hV
  rw [Finset.sum_congr rfl fun S _ => h1 S]
  refine Finset.sum_comm' fun S V => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hS, hSV⟩
    exact ⟨⟨hS, hSV⟩, hS.mono hSV⟩
  · rintro ⟨⟨hS, hSV⟩, _⟩
    exact ⟨hS, hSV⟩

/-- A double sum over the disjoint nonempty subsets, as a sum over their pairs. -/
lemma sum_disj_pairs (G : Finset X → Finset X → M) :
    ∑ S ∈ nonempties X, ∑ T₀ ∈ (nonempties X).filter (fun T₀ => Disjoint S T₀), G S T₀
      = ∑ p ∈ disjPairs X, G p.1 p.2 :=
  (Finset.sum_finset_product' _ _ _ fun p => by
    simp only [disjPairs, Finset.mem_filter, Finset.mem_product]
    tauto).symm

end Split

/-! ## Moving the slot of a composite -/

namespace GrOperad

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **Composites at equal inputs** are relabellings of each other. -/
lemma comp_slot {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {j j' : A}
    (h : j = j') (x : Q A) (y : Q B) :
    comp (R := R) j' x y = map (R := R) (slotEquiv (B := B) h) (comp (R := R) j x y) := by
  subst h
  have : slotEquiv (B := B) (rfl : j = j) = Equiv.refl _ := Equiv.ext fun z => by
    rcases z with (⟨a, ha⟩ | b) <;> rfl
  rw [this, map_refl]

/-- **A composite into a relabelled operation** is a relabelled composite. -/
lemma comp_map_left {A A' B : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] (σ : A ≃ A') (i : A) (j : A') (h : σ i = j) (x : Q A) (y : Q B) :
    comp (R := R) j (map (R := R) σ x) y
      = map (R := R) ((compEquiv σ (Equiv.refl B) i).trans (slotEquiv (B := B) h))
          (comp (R := R) i x y) := by
  rw [map_trans, map_comp, map_refl, ← comp_slot]

/-- **A composite of a relabelled operation** is a relabelled composite. -/
lemma comp_map_right {A B B' : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B'] (τ : B ≃ B') (i : A) (x : Q A) (y : Q B) :
    comp (R := R) i x (map (R := R) τ y)
      = map (R := R) (compEquiv (Equiv.refl A) τ i) (comp (R := R) i x y) := by
  rw [map_comp, map_refl]
  rfl

/-- Sequential associativity, solved for the composite on the left. -/
lemma comp_assoc_seq' {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) (x : Q A) (y : Q B) (z : Q D) :
    comp (R := R) (Sum.inr j) (comp (R := R) i x y) z
      = map (R := R) (seqEquiv i j D).symm (comp (R := R) i x (comp (R := R) j y z)) := by
  rw [← comp_assoc_seq i j x y z, ← map_trans, Equiv.self_trans_symm, map_refl]

/-- Parallel associativity, solved for the composite on the left. -/
lemma comp_assoc_par' {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (x : Q A) {q r : Bool} {y : Q B} {z : Q D}
    (hy : par (R := R) q y = y) (hz : par (R := R) r z = z) :
    comp (R := R) (Sum.inl ⟨k, Ne.symm hik⟩) (comp (R := R) i x y) z
      = σ R (q && r) • map (R := R) (parEquiv hik B D).symm
          (comp (R := R) (Sum.inl ⟨i, hik⟩) (comp (R := R) k x z) y) := by
  rw [← map_smul, ← comp_assoc_par hik x hy hz, ← map_trans, Equiv.self_trans_symm, map_refl]

/-! ## The canonical form of a composite -/

section Canon

variable {A B X : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype X]
  [DecidableEq X] {i : A} (e : Without A i ⊕ B ≃ X) (S : Finset X)
  (hS : ∀ x, x ∈ S ↔ ∃ b, e (Sum.inr b) = x)

omit [Fintype A] [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X] in
include hS in
lemma canon_not_mem {a : A} (ha : a ≠ i) : e (Sum.inl ⟨a, ha⟩) ∉ S := by
  rw [hS]
  rintro ⟨b, hb⟩
  exact Sum.inr_ne_inl (e.injective hb)

/-- The outer inputs of a composite, as the outer inputs of the splitting by the inputs of the
inner operation. -/
noncomputable def canonOut : A ≃ SOut S :=
  Equiv.ofBijective
    (fun a => if h : a = i then none else some ⟨e (Sum.inl ⟨a, h⟩), canon_not_mem e S hS h⟩)
    (by
      constructor
      · intro a a' haa'
        dsimp only at haa'
        by_cases h : a = i <;> by_cases h' : a' = i
        · rw [h, h']
        · rw [dif_pos h, dif_neg h'] at haa'
          simp at haa'
        · rw [dif_neg h, dif_pos h'] at haa'
          simp at haa'
        · rw [dif_neg h, dif_neg h'] at haa'
          have := e.injective (congrArg Subtype.val (Option.some.inj haa'))
          exact congrArg Subtype.val (Sum.inl.inj this)
      · rintro (_ | ⟨x, hx⟩)
        · exact ⟨i, by simp⟩
        · rcases hz : e.symm x with (⟨a, ha⟩ | b)
          · refine ⟨a, ?_⟩
            dsimp only
            rw [dif_neg ha]
            congr
            rw [← hz, Equiv.apply_symm_apply]
          · exact absurd ((hS x).2 ⟨b, by rw [← hz, Equiv.apply_symm_apply]⟩) hx)

/-- The inner inputs of a composite, as the inputs of the splitting by them. -/
noncomputable def canonIn : B ≃ SIn S :=
  Equiv.ofBijective (fun b => ⟨e (Sum.inr b), (hS _).2 ⟨b, rfl⟩⟩)
    (by
      constructor
      · intro b b' hbb'
        simpa using e.injective (congrArg Subtype.val hbb')
      · rintro ⟨x, hx⟩
        obtain ⟨b, hb⟩ := (hS x).1 hx
        exact ⟨b, Subtype.ext hb⟩)

omit [Fintype A] [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X] in
@[simp] lemma canonOut_self : canonOut e S hS i = none := by
  simp [canonOut]

omit [Fintype A] [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X] in
lemma canonOut_ne {a : A} (ha : a ≠ i) :
    canonOut e S hS a = some ⟨e (Sum.inl ⟨a, ha⟩), canon_not_mem e S hS ha⟩ := by
  simp [canonOut, ha]

omit [Fintype A] [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X] in
@[simp] lemma canonIn_apply (b : B) : (canonIn e S hS b).1 = e (Sum.inr b) := rfl

/-- **The canonical form of a composite**: a composite relabelled onto `X` is the composite at
the splitting of `X` by the inputs of the inner operation, of the two operations relabelled. -/
theorem map_comp_canon (x : Q A) (y : Q B) :
    map (R := R) e (comp (R := R) i x y)
      = map (R := R) (splitEquiv S) (comp (R := R) none (map (R := R) (canonOut e S hS) x)
          (map (R := R) (canonIn e S hS) y)) := by
  have hE : (compEquiv (canonOut e S hS) (canonIn e S hS) i).trans
      ((slotEquiv (B := SIn S) (canonOut_self e S hS)).trans (splitEquiv S)) = e := by
    ext z
    rcases z with (⟨a, ha⟩ | b)
    · simp only [Equiv.trans_apply, compEquiv_inl, slotEquiv_inl, splitEquiv_inl]
      exact outVal_eq_of_eq _ (canonOut_ne e S hS ha)
    · rfl
  rw [comp_slot (canonOut_self e S hS), ← map_comp, ← map_trans, ← map_trans, hE]

end Canon

/-! ## Invariant families and their product -/

variable (Q) in
/-- A family of operations, one for every finite input type. -/
abbrev Fam : Type (max 1 v) := ∀ (A : Type) [Fintype A] [DecidableEq A], Q A

variable (R Q) in
/-- **Invariant families**: the families of operations compatible with all relabellings. -/
def Inv : Submodule R (Fam Q) where
  carrier := {q | ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B), map (R := R) e (q A) = q B}
  add_mem' := by
    intro a b ha hb A B _ _ _ _ e
    show map (R := R) e (a A + b A) = a B + b B
    rw [map_add, ha, hb]
  zero_mem' := by
    intro A B _ _ _ _ e
    show map (R := R) e 0 = 0
    rw [map_zero]
  smul_mem' := by
    intro c a ha A B _ _ _ _ e
    show map (R := R) e (c • a A) = c • a B
    rw [map_smul, ha]

namespace Inv

/-- An invariant family is compatible with relabelling. -/
lemma map_apply (q : Inv R Q) {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (e : A ≃ B) : map (R := R) e (q.1 A) = q.1 B :=
  q.2 A B e

/-- The term of the product at a subset `S`: `q'` plugged into `q` at the inputs `S`. -/
def term (q q' : Fam Q) (X : Type) [Fintype X] [DecidableEq X] (S : Finset X) : Q X :=
  map (R := R) (splitEquiv S) (comp (R := R) none (q (SOut S)) (q' (SIn S)))

variable (R) in
/-- The product of two families: the sum of the terms at the nonempty subsets. -/
def starF (q q' : Fam Q) : Fam Q := fun X _ _ => ∑ S ∈ nonempties X, term (R := R) q q' X S

lemma starF_apply (q q' : Fam Q) (X : Type) [Fintype X] [DecidableEq X] :
    starF R q q' X = ∑ S ∈ nonempties X, term (R := R) q q' X S := rfl

/-- **Relabelling a term** is the term at the relabelled subset. -/
lemma map_term (q q' : Inv R Q) {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (e : X ≃ Y) (S : Finset X) :
    map (R := R) e (term (R := R) q.1 q'.1 X S) = term (R := R) q.1 q'.1 Y (S.map e.toEmbedding)
    := by
  have hS : ∀ y, y ∈ S.map e.toEmbedding ↔ ∃ b : SIn S, ((splitEquiv S).trans e) (Sum.inr b) = y :=
    fun y => by
      simp only [Finset.mem_map_equiv, Equiv.trans_apply, splitEquiv_inr]
      constructor
      · intro h
        exact ⟨⟨e.symm y, h⟩, by simp⟩
      · rintro ⟨b, rfl⟩
        simp [b.2]
  unfold term
  rw [← map_trans, map_comp_canon _ _ hS, map_apply, map_apply]

/-- **The product of invariant families is invariant.** -/
lemma starF_mem (q q' : Inv R Q) : starF R q.1 q'.1 ∈ Inv R Q := by
  intro X Y _ _ _ _ e
  simp only [starF_apply, map_sum, map_term]
  refine Finset.sum_nbij' (fun S => S.map e.toEmbedding) (fun S => S.map e.symm.toEmbedding)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro S hS
    simpa using hS
  · intro S hS
    simpa using hS
  · intro S _
    simp [Finset.map_map]
  · intro S _
    simp [Finset.map_map]

lemma term_add_left (q₁ q₂ q' : Fam Q) (X : Type) [Fintype X] [DecidableEq X] (S : Finset X) :
    term (R := R) (q₁ + q₂) q' X S = term (R := R) q₁ q' X S + term (R := R) q₂ q' X S := by
  simp only [term, Pi.add_apply, map_add, LinearMap.add_apply]

lemma term_add_right (q q'₁ q'₂ : Fam Q) (X : Type) [Fintype X] [DecidableEq X] (S : Finset X) :
    term (R := R) q (q'₁ + q'₂) X S = term (R := R) q q'₁ X S + term (R := R) q q'₂ X S := by
  simp only [term, Pi.add_apply, map_add]

lemma term_smul_left (c : R) (q q' : Fam Q) (X : Type) [Fintype X] [DecidableEq X]
    (S : Finset X) : term (R := R) (c • q) q' X S = c • term (R := R) q q' X S := by
  simp only [term, Pi.smul_apply, map_smul, LinearMap.smul_apply]

lemma term_smul_right (c : R) (q q' : Fam Q) (X : Type) [Fintype X] [DecidableEq X]
    (S : Finset X) : term (R := R) q (c • q') X S = c • term (R := R) q q' X S := by
  simp only [term, Pi.smul_apply, map_smul]

variable (R Q) in
/-- **The product of invariant families**: `(q ⋆ q') X = ∑_{∅ ≠ S ⊆ X} q (X / S) ∘_S q' S`. -/
def star : Inv R Q →ₗ[R] Inv R Q →ₗ[R] Inv R Q :=
  LinearMap.mk₂ R (fun q q' => ⟨starF R q.1 q'.1, starF_mem q q'⟩)
    (fun q₁ q₂ q' => Subtype.ext (funext fun X => funext fun _ => funext fun _ => by
      simp only [Submodule.coe_add, starF_apply, term_add_left, Finset.sum_add_distrib]
      rfl))
    (fun c q q' => Subtype.ext (funext fun X => funext fun _ => funext fun _ => by
      simp only [Submodule.coe_smul, starF_apply, term_smul_left, ← Finset.smul_sum]
      rfl))
    (fun q q'₁ q'₂ => Subtype.ext (funext fun X => funext fun _ => funext fun _ => by
      simp only [Submodule.coe_add, starF_apply, term_add_right, Finset.sum_add_distrib]
      rfl))
    (fun c q q' => Subtype.ext (funext fun X => funext fun _ => funext fun _ => by
      simp only [Submodule.coe_smul, starF_apply, term_smul_right, ← Finset.smul_sum]
      rfl))

lemma star_apply (q q' : Inv R Q) (X : Type) [Fintype X] [DecidableEq X] :
    (star R Q q q').1 X = ∑ S ∈ nonempties X, term (R := R) q.1 q'.1 X S := rfl

/-! ### The associator -/

/-- A term of `(q ⋆ q') ⋆ q''`: `q'` plugged into `q` at `T`, then `q''` at `S`. -/
def outerTerm (q q' q'' : Fam Q) (X : Type) [Fintype X] [DecidableEq X] (S : Finset X)
    (T : Finset (SOut S)) : Q X :=
  map (R := R) (splitEquiv S) (comp (R := R) none (term (R := R) q q' (SOut S) T) (q'' (SIn S)))

/-- A term of `q ⋆ (q' ⋆ q'')`: `q''` plugged into `q'` at `U`, then the result into `q` at `V`. -/
def innerTerm (q q' q'' : Fam Q) (X : Type) [Fintype X] [DecidableEq X] (V : Finset X)
    (U : Finset (SIn V)) : Q X :=
  map (R := R) (splitEquiv V) (comp (R := R) none (q (SOut V)) (term (R := R) q' q'' (SIn V) U))

lemma star_star_left (q q' q'' : Inv R Q) (X : Type) [Fintype X] [DecidableEq X] :
    (star R Q (star R Q q q') q'').1 X
      = ∑ S ∈ nonempties X, ∑ T ∈ nonempties (SOut S), outerTerm (R := R) q.1 q'.1 q''.1 X S T := by
  simp only [star_apply, term, outerTerm, map_sum, LinearMap.coe_sum, Finset.sum_apply]

lemma star_star_right (q q' q'' : Inv R Q) (X : Type) [Fintype X] [DecidableEq X] :
    (star R Q q (star R Q q' q'')).1 X
      = ∑ V ∈ nonempties X, ∑ U ∈ nonempties (SIn V), innerTerm (R := R) q.1 q'.1 q''.1 X V U := by
  simp only [star_apply, term, innerTerm, map_sum]

section Canon3

variable {A B D X : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
  [DecidableEq D] [Fintype X] [DecidableEq X]

/-- **The canonical form of a nested composite** of invariant families. -/
lemma nested_canon (q q' q'' : Inv R Q) {i : A} {j : B}
    (E : Without A i ⊕ (Without B j ⊕ D) ≃ X) (V U₀ : Finset X)
    (hV : ∀ x, x ∈ V ↔ ∃ w, E (Sum.inr w) = x)
    (hU : ∀ x, x ∈ U₀ ↔ ∃ d, E (Sum.inr (Sum.inr d)) = x) :
    map (R := R) E (comp (R := R) i (q.1 A) (comp (R := R) j (q'.1 B) (q''.1 D)))
      = innerTerm (R := R) q.1 q'.1 q''.1 X V (restrIn V U₀) := by
  have hU' : ∀ v, v ∈ restrIn V U₀ ↔ ∃ d, canonIn E V hV (Sum.inr d) = v := fun v => by
    rw [mem_restrIn, hU]
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨d, Subtype.ext hd⟩
    · rintro ⟨d, rfl⟩
      exact ⟨d, rfl⟩
  rw [map_comp_canon E V hV, map_apply, map_comp_canon _ _ hU', map_apply, map_apply]
  rfl

/-- **The canonical form of a composite at two disjoint inputs** of invariant families. -/
lemma disj_canon (q q' q'' : Inv R Q) {k : A} {l : Without A k ⊕ D}
    (hl : ∀ d, Sum.inr d ≠ l) (E : Without (Without A k ⊕ D) l ⊕ B ≃ X) (S T₀ : Finset X)
    (hT : ∀ x, x ∈ T₀ ↔ ∃ b, E (Sum.inr b) = x)
    (hS : ∀ x, x ∈ S ↔ ∃ d, E (Sum.inl ⟨Sum.inr d, hl d⟩) = x) :
    map (R := R) E (comp (R := R) l (comp (R := R) k (q.1 A) (q''.1 D)) (q'.1 B))
      = outerTerm (R := R) q.1 q''.1 q'.1 X T₀ (liftOut T₀ false S) := by
  have hS' : ∀ o, o ∈ liftOut T₀ false S ↔ ∃ d, canonOut E T₀ hT (Sum.inr d) = o := fun o => by
    rcases o with (_ | ⟨x, hx⟩)
    · simp only [none_mem_liftOut, Bool.false_eq_true, false_iff, not_exists]
      intro d
      rw [canonOut_ne E T₀ hT (hl d)]
      simp
    · rw [some_mem_liftOut, hS]
      constructor
      · rintro ⟨d, hd⟩
        refine ⟨d, ?_⟩
        rw [canonOut_ne E T₀ hT (hl d)]
        simp [hd]
      · rintro ⟨d, hd⟩
        rw [canonOut_ne E T₀ hT (hl d)] at hd
        exact ⟨d, by simpa using hd⟩
  rw [map_comp_canon E T₀ hT, map_apply, map_comp_canon _ _ hS', map_apply, map_apply]
  rfl

end Canon3

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The nested terms of `(q ⋆ q') ⋆ q''` are terms of `q ⋆ (q' ⋆ q'')`**, by sequential
associativity: plugging `q'` at `T₀` and the new input, then `q''` at `S`, is plugging `q''` into
`q'` at `S`, then the result into `q` at `S ∪ T₀`. -/
lemma outerTerm_nested (q q' q'' : Inv R Q) (S T₀ : Finset X) :
    outerTerm (R := R) q.1 q'.1 q''.1 X S (liftOut S true T₀)
      = innerTerm (R := R) q.1 q'.1 q''.1 X (S ∪ T₀) (restrIn (S ∪ T₀) S) := by
  have hnT : (none : SOut S) ∈ liftOut S true T₀ := (none_mem_liftOut _ _ _).2 rfl
  unfold outerTerm term
  rw [comp_map_left (splitEquiv (liftOut S true T₀)) (Sum.inr ⟨none, hnT⟩) none rfl,
    comp_assoc_seq', ← map_trans,
    ← map_trans, nested_canon q q' q'' _ (S ∪ T₀) S]
  · intro x
    constructor
    · intro hx
      by_cases hxS : x ∈ S
      · exact ⟨Sum.inr ⟨x, hxS⟩, rfl⟩
      · have hxT : x ∈ T₀ := by
          rcases Finset.mem_union.1 hx with h | h
          · exact absurd h hxS
          · exact h
        exact ⟨Sum.inl ⟨⟨some ⟨x, hxS⟩, (some_mem_liftOut _ _ _ _).2 hxT⟩,
          fun h => by simp at h⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      rcases w with (⟨⟨(_ | ⟨x, hx⟩), ho⟩, hne⟩ | ⟨x, hx⟩)
      · exact absurd (Subtype.ext rfl) hne
      · exact Finset.mem_union_right _ ((some_mem_liftOut _ _ _ _).1 ho)
      · exact Finset.mem_union_left _ hx
  · intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨d, rfl⟩
      exact d.2

/-- A family homogeneous of parity `b`. -/
def IsPar (b : Bool) (q : Inv R Q) : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A], par (R := R) b (q.1 A) = q.1 A

/-- **Exchanging the two disjoint subsets of a term of `(q ⋆ q') ⋆ q''`**, together with `q'` and
`q''`, costs the Koszul sign, by parallel associativity. -/
lemma outerTerm_disj (q q' q'' : Inv R Q) {p' p'' : Bool} (hq' : IsPar p' q') (hq'' : IsPar p'' q'')
    (S T₀ : Finset X) (hd : Disjoint S T₀) :
    outerTerm (R := R) q.1 q'.1 q''.1 X S (liftOut S false T₀)
      = σ R (p' && p'') • outerTerm (R := R) q.1 q''.1 q'.1 X T₀ (liftOut T₀ false S) := by
  have hnT : (none : SOut S) ∉ liftOut S false T₀ := by simp
  have hik : (none : SOut (liftOut S false T₀)) ≠ some ⟨none, hnT⟩ := by simp
  unfold outerTerm term
  rw [comp_map_left (splitEquiv (liftOut S false T₀))
      (Sum.inl ⟨some ⟨none, hnT⟩, Option.some_ne_none _⟩) none rfl,
    comp_assoc_par' hik _ (hq' _) (hq'' _), map_smul, map_smul, ← map_trans, ← map_trans,
    disj_canon q q' q'' (fun d => Sum.inr_ne_inl) _ S T₀]
  · rfl
  · intro x
    constructor
    · intro hx
      have hxS : x ∉ S := Finset.disjoint_right.1 hd hx
      exact ⟨⟨some ⟨x, hxS⟩, (some_mem_liftOut _ _ _ _).2 hx⟩, rfl⟩
    · rintro ⟨⟨(_ | ⟨x, hx⟩), ho⟩, rfl⟩
      · exact absurd ho hnT
      · exact (some_mem_liftOut _ _ _ _).1 ho
  · intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨d, rfl⟩
      exact d.2

/-! ### The graded pre-Lie identity -/

/-- **The associator is the sum of the terms at disjoint subsets**: the nested terms of
`(q ⋆ q') ⋆ q''` are those of `q ⋆ (q' ⋆ q'')`. -/
theorem assoc_eq_sum_disj (q q' q'' : Inv R Q) (X : Type) [Fintype X] [DecidableEq X] :
    (star R Q (star R Q q q') q'').1 X - (star R Q q (star R Q q' q'')).1 X
      = ∑ p ∈ disjPairs X, outerTerm (R := R) q.1 q'.1 q''.1 X p.1 (liftOut p.1 false p.2) := by
  have h1 : (star R Q (star R Q q q') q'').1 X
      = (∑ S ∈ nonempties X, ∑ T₀ ∈ Finset.univ.filter (fun T₀ => Disjoint S T₀),
          innerTerm (R := R) q.1 q'.1 q''.1 X (S ∪ T₀) (restrIn (S ∪ T₀) S))
        + ∑ S ∈ nonempties X, ∑ T₀ ∈ (nonempties X).filter (fun T₀ => Disjoint S T₀),
          outerTerm (R := R) q.1 q'.1 q''.1 X S (liftOut S false T₀) := by
    rw [star_star_left, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [sum_nonempties_out]
    congr 1
    exact Finset.sum_congr rfl fun T₀ _ => outerTerm_nested q q' q'' S T₀
  have h2 : (star R Q q (star R Q q' q'')).1 X
      = ∑ V ∈ nonempties X, ∑ U₀ ∈ (nonempties X).filter (· ⊆ V),
          innerTerm (R := R) q.1 q'.1 q''.1 X V (restrIn V U₀) := by
    rw [star_star_right]
    exact Finset.sum_congr rfl fun V _ => sum_nonempties_in V _
  rw [h1, h2, sum_nested_pairs (fun V U₀ => innerTerm (R := R) q.1 q'.1 q''.1 X V (restrIn V U₀)),
    add_sub_cancel_left, sum_disj_pairs]

lemma coe_sub_apply (a b : Inv R Q) (X : Type) [Fintype X] [DecidableEq X] :
    (a - b).1 X = a.1 X - b.1 X := rfl

lemma coe_smul_apply (c : R) (a : Inv R Q) (X : Type) [Fintype X] [DecidableEq X] :
    (c • a).1 X = c • a.1 X := rfl

/-- **The graded pre-Lie identity**: the associator is graded symmetric in its last two
arguments. -/
theorem preLie (q q' q'' : Inv R Q) {p' p'' : Bool} (hq' : IsPar p' q') (hq'' : IsPar p'' q'') :
    star R Q (star R Q q q') q'' - star R Q q (star R Q q' q'')
      = σ R (p' && p'') • (star R Q (star R Q q q'') q' - star R Q q (star R Q q'' q')) := by
  refine Subtype.ext (funext fun X => funext fun _ => funext fun _ => ?_)
  show (star R Q (star R Q q q') q'' - star R Q q (star R Q q' q'')).1 X
    = (σ R (p' && p'') • (star R Q (star R Q q q'') q' - star R Q q (star R Q q'' q'))).1 X
  rw [coe_smul_apply, coe_sub_apply, coe_sub_apply, assoc_eq_sum_disj, assoc_eq_sum_disj,
    Finset.smul_sum]
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) ?_
  · intro p hp
    simp only [disjPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
  · intro p hp
    simp only [disjPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
  · intro p hp
    simp only [disjPairs, Finset.mem_filter] at hp
    exact outerTerm_disj q q' q'' hq' hq'' p.1 p.2 hp.2

/-- **The associator with an odd family twice vanishes**: its terms at two disjoint subsets
cancel in pairs. -/
theorem assoc_odd (q α : Inv R Q) (hα : IsPar true α) :
    star R Q (star R Q q α) α = star R Q q (star R Q α α) := by
  rw [← sub_eq_zero]
  refine Subtype.ext (funext fun X => funext fun _ => funext fun _ => ?_)
  show (star R Q (star R Q q α) α - star R Q q (star R Q α α)).1 X = 0
  rw [coe_sub_apply, assoc_eq_sum_disj]
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p hp
    have hd : Disjoint p.1 p.2 := (Finset.mem_filter.1 hp).2
    show outerTerm (R := R) q.1 α.1 α.1 X p.1 (liftOut p.1 false p.2)
      + outerTerm (R := R) q.1 α.1 α.1 X p.2 (liftOut p.2 false p.1) = 0
    rw [outerTerm_disj q α α hα hα p.1 p.2 hd, Bool.and_self, σ_true, neg_one_smul,
      neg_add_cancel]
  · intro p hp _ h
    simp only [disjPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at hp
    have h12 : p.2 = p.1 := congrArg Prod.fst h
    obtain ⟨x, hx⟩ := hp.1.1
    have hx2 : x ∈ p.2 := by rw [h12]; exact hx
    exact Finset.disjoint_left.1 hp.2 hx hx2
  · intro p hp
    simp only [disjPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩

/-! ### Parities, morphisms and derivations -/

/-- **The product adds parities.** -/
theorem isPar_star {p p' : Bool} {q q' : Inv R Q} (hq : IsPar p q) (hq' : IsPar p' q') :
    IsPar (xor p p') (star R Q q q') := by
  intro X _ _
  show par (R := R) (xor p p') (∑ S ∈ nonempties X, term (R := R) q.1 q'.1 X S)
    = ∑ S ∈ nonempties X, term (R := R) q.1 q'.1 X S
  rw [map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [term, ← map_par]
  rw [par_comp_hom none rfl (hq _) (hq' _)]

variable {Q' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q' A)] [GrOperad R Q']

/-- A morphism of graded operads, applied to invariant families. -/
def appHom (φ : GrOperadHom R Q Q') : Inv R Q →ₗ[R] Inv R Q' where
  toFun q := ⟨fun A _ _ => φ.app A (q.1 A), fun A B _ _ _ _ e => by
    show map (R := R) e (φ.app A (q.1 A)) = φ.app B (q.1 B)
    rw [← φ.app_map, map_apply]⟩
  map_add' q q' := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_add (φ.app A) _ _)
  map_smul' c q := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_smul (φ.app A) _ _)

@[simp] lemma appHom_apply (φ : GrOperadHom R Q Q') (q : Inv R Q) (A : Type) [Fintype A]
    [DecidableEq A] : (appHom φ q).1 A = φ.app A (q.1 A) := rfl

/-- **Morphisms of graded operads preserve the product.** -/
theorem appHom_star (φ : GrOperadHom R Q Q') (q q' : Inv R Q) :
    appHom φ (star R Q q q') = star R Q' (appHom φ q) (appHom φ q') := by
  refine Subtype.ext (funext fun X => funext fun _ => funext fun _ => ?_)
  show φ.app X (∑ S ∈ nonempties X, term (R := R) q.1 q'.1 X S)
    = ∑ S ∈ nonempties X, term (R := R) (appHom φ q).1 (appHom φ q').1 X S
  rw [map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [term, φ.app_map, φ.app_comp, appHom_apply]

/-- A derivation, applied to invariant families. -/
def appDer {e : Bool} (D : GrDer (GrOperadHom.id R Q) e) : Inv R Q →ₗ[R] Inv R Q where
  toFun q := ⟨fun A _ _ => D.app A (q.1 A), fun A B _ _ _ _ σ' => by
    show map (R := R) σ' (D.app A (q.1 A)) = D.app B (q.1 B)
    rw [← D.app_map, map_apply]⟩
  map_add' q q' := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_add (D.app A) _ _)
  map_smul' c q := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_smul (D.app A) _ _)

@[simp] lemma appDer_apply {e : Bool} (D : GrDer (GrOperadHom.id R Q) e) (q : Inv R Q)
    (A : Type) [Fintype A] [DecidableEq A] : (appDer D q).1 A = D.app A (q.1 A) := rfl

/-- **A derivation shifts parities.** -/
theorem isPar_appDer {e p : Bool} (D : GrDer (GrOperadHom.id R Q) e) {q : Inv R Q}
    (hq : IsPar p q) : IsPar (xor p e) (appDer D q) := by
  intro A _ _
  show par (R := R) (xor p e) (D.app A (q.1 A)) = D.app A (q.1 A)
  rw [← D.app_par, hq A]

/-- **A derivation is a derivation of the product**, with the Koszul sign of the left factor. -/
theorem appDer_star {e p : Bool} (D : GrDer (GrOperadHom.id R Q) e) {q : Inv R Q}
    (hq : IsPar p q) (q' : Inv R Q) :
    appDer D (star R Q q q')
      = star R Q (appDer D q) q' + σ R (e && p) • star R Q q (appDer D q') := by
  refine Subtype.ext (funext fun X => funext fun _ => funext fun _ => ?_)
  show D.app X (∑ S ∈ nonempties X, term (R := R) q.1 q'.1 X S)
    = ∑ S ∈ nonempties X, term (R := R) (appDer D q).1 q'.1 X S
      + σ R (e && p) • ∑ S ∈ nonempties X, term (R := R) q.1 (appDer D q').1 X S
  rw [map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [term, D.app_map, D.app_comp, appDer_apply, GrOperadHom.id_app]
  rw [tw_hom e (hq _), map_smul, LinearMap.smul_apply, map_add, map_smul]

lemma neg_one_smul_inv (X : Inv R Q) : (-1 : R) • X = -X :=
  Subtype.ext (funext fun _ => funext fun _ => funext fun _ => neg_one_smul R _)

/-- **An odd derivation sending an odd family `α` to `-(α ⋆ α)` kills `α ⋆ α`**: its value there
is the associator of `α` with itself. -/
theorem appDer_star_self {α : Inv R Q} (hα : IsPar true α) (D : GrDer (GrOperadHom.id R Q) true)
    (hD : appDer D α = -star R Q α α) : appDer D (star R Q α α) = 0 := by
  rw [appDer_star D hα, hD, Bool.and_self, σ_true, neg_one_smul_inv, map_neg, map_neg,
    LinearMap.neg_apply, neg_neg, assoc_odd α α hα, neg_add_cancel]

end Inv

end GrOperad

end Operad
