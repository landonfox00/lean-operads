/-
# Leading monomials

A vector space with a finite basis of *monomials* `X`, linearly ordered, is `X → K`. The *leading
monomial* of a nonzero vector is the largest monomial of its support (`IsLeadingOf`), and the
leading monomials of a set of vectors are those of its members (`IsLeading`): for the relations of
an operad presented in a free shuffle operad with a monomial order, this is where a Gröbner basis
starts.

When an operad is the linearization of a set operad, or the associated graded of a filtered one,
the evaluation of the free operad sends every monomial to a basis element or to zero: it is the
linearization of a map `f : X → Option Y`, whose kernel is the space of vectors with vanishing sum
over every fiber (`fiberKer`). **The leading monomials of that kernel are the monomials sent to
zero and those which are not the least of their fiber** (`isLeading_fiberKer_iff`).

**A Gröbner criterion** (`isLeading_iff_of_supportedOn`, `isCompl_supportedOn`): if every monomial
outside a set `N` is the leading monomial of a vector of a space `I`, then every vector reduces
modulo `I` to one supported on `N` (`exists_reduction`, the division algorithm); if moreover no
nonzero vector of `I` is supported on `N` — for instance because a linear map killing `I` is
injective on the vectors supported on `N` — then the leading monomials of `I` are exactly the
monomials outside `N`, and the vectors supported on `N` are a complement of `I`. For `I` an
ideal of a free operad in some arity and `N` the monomials not divisible by the leading monomials
of a set of generators, this says that the generators are a Gröbner basis and that the normal
monomials are a basis of the quotient.
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Abel

namespace Operad

section Ring

variable {K : Type*} [Ring K] {X Y : Type*}

section Fiber

variable [Fintype X] [DecidableEq Y]

variable (K) in
/-- **The kernel of the linearization of a map** `f : X → Option Y`, which sends a monomial to the
basis vector of its value, or to zero: the vectors whose sum over each fiber `f⁻¹(y)` vanishes. -/
def fiberKer (f : X → Option Y) : Submodule K (X → K) where
  carrier := {v | ∀ y, ∑ x ∈ Finset.univ.filter (fun x => f x = some y), v x = 0}
  add_mem' := by
    intro a b ha hb y
    simp only [Set.mem_setOf_eq, Pi.add_apply, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha y, hb y, add_zero]
  zero_mem' := by
    intro y
    simp
  smul_mem' := by
    intro c v hv y
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
    rw [← Finset.mul_sum, hv y, mul_zero]

lemma mem_fiberKer {f : X → Option Y} {v : X → K} :
    v ∈ fiberKer K f ↔ ∀ y, ∑ x ∈ Finset.univ.filter (fun x => f x = some y), v x = 0 :=
  Iff.rfl

end Fiber

variable [LinearOrder X]

/-- `x` is **the leading monomial** of `v`: in the support of `v`, and above the rest of it. -/
def IsLeadingOf (v : X → K) (x : X) : Prop := v x ≠ 0 ∧ ∀ y, x < y → v y = 0

/-- A vector has at most one leading monomial. -/
lemma IsLeadingOf.unique {v : X → K} {x x' : X} (h : IsLeadingOf v x) (h' : IsLeadingOf v x') :
    x = x' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.1 (h.2 x' hlt)
  · exact h.1 (h'.2 x hlt)

/-- **The leading monomials of a set of vectors**: those of its members. -/
def IsLeading (V : Set (X → K)) (x : X) : Prop := ∃ v ∈ V, IsLeadingOf v x

variable [Fintype X] [DecidableEq Y]

/-- **The leading monomials of the kernel of a linearized map** are the monomials sent to zero and
those which are not the least of their fiber. -/
theorem isLeading_fiberKer_iff [Nontrivial K] (f : X → Option Y) (x : X) :
    IsLeading (fiberKer K f : Set (X → K)) x ↔ f x = none ∨ ∃ x' < x, f x' = f x := by
  constructor
  · rintro ⟨v, hv, hx, hmax⟩
    by_contra hcon
    simp only [not_or, not_exists, not_and] at hcon
    obtain ⟨hne, hmin⟩ := hcon
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hne
    have h0 := (mem_fiberKer.1 hv) y
    rw [Finset.sum_eq_single x] at h0
    · exact hx h0
    · intro z hz hzx
      rw [Finset.mem_filter] at hz
      rcases lt_or_gt_of_ne hzx with h | h
      · exact absurd (hz.2.trans hy.symm) (hmin z h)
      · exact hmax z h
    · intro hxs
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ x, hy⟩) hxs
  · rintro (h | ⟨x', hx', h⟩)
    · refine ⟨Pi.single x 1, fun y => ?_, by simp, fun z hz => ?_⟩
      · rw [Finset.sum_pi_single', if_neg]
        rw [Finset.mem_filter, h]
        simp
      · simp [hz.ne']
    · refine ⟨Pi.single x 1 - Pi.single x' 1, fun y => ?_, ?_, fun z hz => ?_⟩
      · simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single',
          Finset.mem_filter, Finset.mem_univ, true_and, h, sub_self]
      · simp [hx'.ne']
      · simp [hz.ne', (hx'.trans hz).ne']

end Ring

/-! ## A Gröbner criterion -/

section Field

variable {K : Type*} [Field K] {X : Type*}

variable (K) in
/-- The vectors supported on a set `N` of monomials. -/
def supportedOn (N : Set X) : Submodule K (X → K) where
  carrier := {v | ∀ x ∉ N, v x = 0}
  add_mem' ha hb x hx := by simp [ha x hx, hb x hx]
  zero_mem' _ _ := rfl
  smul_mem' c v hv x hx := by simp [hv x hx]

lemma mem_supportedOn {N : Set X} {v : X → K} : v ∈ supportedOn K N ↔ ∀ x ∉ N, v x = 0 :=
  Iff.rfl

variable [LinearOrder X] [Fintype X]

/-- **Reduction to normal monomials.** If every monomial outside `N` is the leading monomial of a
vector of `I`, every vector `v` is congruent modulo `I` to one supported on `N`, by subtracting
vectors of `I` whose leading monomials lie outside `N`: so the coefficients of `v` at the
monomials of `N` above all those of its support outside `N` are unchanged. -/
theorem exists_reduction (I : Submodule K (X → K)) (N : Set X)
    (hI : ∀ x ∉ N, IsLeading (I : Set (X → K)) x) (v : X → K) :
    ∃ u ∈ I, v - u ∈ supportedOn K N ∧
      ∀ x, (∀ y ∉ N, v y ≠ 0 → y < x) → u x = 0 := by
  classical
  suffices h : ∀ (b : WithTop X) (v : X → K), (∀ y ∉ N, v y ≠ 0 → (y : WithTop X) < b) →
      ∃ u ∈ I, v - u ∈ supportedOn K N ∧ ∀ x, (∀ y ∉ N, v y ≠ 0 → y < x) → u x = 0 from
    h ⊤ v fun _ _ _ => WithTop.coe_lt_top _
  intro b
  induction b using WellFoundedLT.induction with
  | _ b ih =>
  intro v hb
  by_cases hN : ∀ y ∉ N, v y = 0
  · exact ⟨0, I.zero_mem, by simpa using hN, fun _ _ => rfl⟩
  push Not at hN
  set D := Finset.univ.filter fun y => y ∉ N ∧ v y ≠ 0 with hD
  have hDne : D.Nonempty := by
    obtain ⟨y, hy, hy'⟩ := hN
    exact ⟨y, by simp [hD, hy, hy']⟩
  set y := D.max' hDne with hy
  have hyD : y ∈ D := D.max'_mem hDne
  have hymax : ∀ z ∉ N, v z ≠ 0 → z ≤ y := fun z hz hz' =>
    D.le_max' z (by simp [hD, hz, hz'])
  simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hyD
  obtain ⟨w, hw, hwy, hw0⟩ := hI y hyD.1
  set v' := v - (v y / w y) • w with hv'
  have hv'z : ∀ z, y < z → v' z = v z := fun z hz => by
    simp [hv', hw0 z hz]
  have hv'y : v' y = 0 := by
    simp [hv', div_mul_cancel₀ _ hwy]
  have hv'lt : ∀ z ∉ N, v' z ≠ 0 → z < y := by
    intro z hz hz'
    rcases lt_or_ge z y with h | h
    · exact h
    · rcases h.lt_or_eq with h | h
      · rw [hv'z z h] at hz'
        exact absurd (hymax z hz hz') (not_le.2 h)
      · exact absurd (h ▸ hv'y) hz'
  obtain ⟨u, hu, hvu, hux⟩ := ih (y : WithTop X) (hb y hyD.1 hyD.2) v'
    fun z hz hz' => WithTop.coe_lt_coe.2 (hv'lt z hz hz')
  refine ⟨u + (v y / w y) • w, I.add_mem hu (I.smul_mem _ hw), ?_, fun x hx => ?_⟩
  · have : v - (u + (v y / w y) • w) = v' - u := by
      simp only [hv']
      abel
    rw [this]
    exact hvu
  · have hyx : y < x := hx y hyD.1 hyD.2
    have hu0 : u x = 0 := hux x fun z hz hz' => (hv'lt z hz hz').trans hyx
    simp [hu0, hw0 x hyx]

/-- **A Gröbner criterion.** Let `I` be a space of vectors in which every monomial outside `N` is
a leading monomial, and suppose that no nonzero vector of `I` is supported on `N`. Then the
leading monomials of `I` are exactly the monomials outside `N`; and the vectors supported on `N`
are a complement of `I`. -/
theorem isLeading_iff_of_supportedOn (I : Submodule K (X → K)) (N : Set X)
    (hI : ∀ x ∉ N, IsLeading (I : Set (X → K)) x)
    (hN : ∀ v ∈ I, v ∈ supportedOn K N → v = 0) (x : X) :
    IsLeading (I : Set (X → K)) x ↔ x ∉ N := by
  refine ⟨fun ⟨v, hv, hvx, hmax⟩ hx => ?_, hI x⟩
  obtain ⟨u, hu, hvu, hux⟩ := exists_reduction I N hI v
  have h0 := hN (v - u) (I.sub_mem hv hu) hvu
  have hx' : u x = 0 := hux x fun y hy hy' => by
    rcases lt_or_ge y x with h | h
    · exact h
    · rcases h.lt_or_eq with h | h
      · exact absurd (hmax y h) hy'
      · exact absurd (h ▸ hx) hy
  have := congrFun h0 x
  simp only [Pi.sub_apply, hx', sub_zero, Pi.zero_apply] at this
  exact hvx this

theorem isCompl_supportedOn (I : Submodule K (X → K)) (N : Set X)
    (hI : ∀ x ∉ N, IsLeading (I : Set (X → K)) x)
    (hN : ∀ v ∈ I, v ∈ supportedOn K N → v = 0) : IsCompl I (supportedOn K N) := by
  refine ⟨Submodule.disjoint_def.2 fun v hv hv' => hN v hv hv', ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro v _
  obtain ⟨u, hu, hvu, -⟩ := exists_reduction I N hI v
  have : v = u + (v - u) := by abel
  rw [this]
  exact Submodule.add_mem_sup hu hvu

end Field

end Operad
