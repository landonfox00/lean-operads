/-
# The commutative operad on the binary side: a quadratic Gröbner basis and Koszulness

`Operad.ShuffleAnyCom` proves the commutative operad Koszul as a shuffle operad with generators of
any arity (`Operad.ComGen.isKoszul`, for `Operad.Rules.IsKoszul`). This file proves it Koszul as
a binary shuffle operad (`Operad.ShuffleBar.IsKoszul`), through the Gröbner criterion of
`Operad.ShuffleKoszul`, so that both shuffle predicates hold for the same operad
(`Operad.ComBin.isKoszul_and`). The generator is the same, the binary operation
`Operad.ComGen.mu`; `ComGen 2` has exactly one element.

In arity three there are three shuffle monomials: the left comb `μ(μ(0, 1), 2)`
(`ComBin.lcomb`), the twisted left comb `μ(μ(0, 2), 1)` (`ComBin.tcomb`) and the right comb
`μ(0, μ(1, 2))` (`ComBin.rcomb`), the same as on the any-arity side.

* **The relators** (`ComBin.rel`) are the vectors on the three monomials whose coefficients sum
  to zero: the kernel of the augmentation (`ComBin.aug`). They are spanned by the differences of
  the two left combs and the right comb (`ComBin.rel_eq_span`), the rules of
  `Operad.ComGen.rules`, leading monomial minus tail.
* **The augmentation vanishes on the ideal** (`ComBin.idealOf_le_ker`): substituting a monomial
  of arity three at an edge of a monomial gives a monomial.
* **There is at most one normal monomial in every arity** (`ComBin.normal_unique`): the leading
  monomials `ComBin.leads` are the two left combs, every window of an edge into the first slot, so
  the normal monomials are the right combs (`Operad.LTree.isNormal_iff`), one for each word in the
  single decoration.
* Hence **the relators are a quadratic Gröbner basis** (`ComBin.isGroebner`) for the
  path-lexicographic key, the augmentation separating the normal monomial from the ideal; by the
  criterion of Dotsenko and Khoroshkin **the operad is Koszul** (`ComBin.isKoszul`), and so is
  the operad of the Koszul dual relators (`ComBin.isKoszul_dualRel`).

`ComBin.isKoszul_dualRel` concerns the shuffle operad presented by `Operad.ShuffleBar.dualRel`
of the relators. `Operad.ShuffleKoszulDuals` identifies it: the Koszul dual relators are the
multiples of the Jacobi relator (`ComBin.dualRel_rel`), and the operad they present has dimension
`(n - 1)!` in arity `n ≥ 2` (`ComBin.finrank_quotient_jac`), that of `Lie`. It is not compared
with the symmetric `Operad.Lie`.

The two proofs here run in parallel. `Operad.ShuffleBridge` connects them: the relators and the
rules correspond (`Operad.ComBin.map_rel`), and the binary Gröbner basis alone gives both
Koszulness predicates (`Operad.ComBin.isKoszul_and_bridge`); `Operad.ShuffleBridgeBar` proves the
two predicates equivalent for these relators (`Operad.ComBin.isKoszul_iff`).
-/
import Operad.ShuffleKoszul
import Operad.ShuffleDualKoszul
import Operad.ShuffleAnyCom

namespace Operad

/-- `ComGen 2` has exactly one element, the binary operation `μ`. -/
instance : Unique (ComGen 2) where
  default := .mu
  uniq g := by cases g; rfl

instance : Fintype (ComGen 2) := Fintype.ofSubsingleton .mu

instance : DecidableEq (ComGen 2) := fun a b => isTrue (Subsingleton.elim a b)

namespace ComBin

open LTree ShuffleBar

/-! ## Arity three -/

/-- **The left comb** `μ(μ(0, 1), 2)`. -/
def lcomb : LTree (ComGen 2) := node .mu (node .mu (leaf 0) (leaf 1)) (leaf 2)

/-- **The twisted left comb** `μ(μ(0, 2), 1)`. -/
def tcomb : LTree (ComGen 2) := node .mu (node .mu (leaf 0) (leaf 2)) (leaf 1)

/-- **The right comb** `μ(0, μ(1, 2))`. -/
def rcomb : LTree (ComGen 2) := node .mu (leaf 0) (node .mu (leaf 1) (leaf 2))

lemma lcomb_mem : lcomb ∈ monomials 3 := (mem_monomials 3 _).2 ⟨by decide, by decide⟩

lemma tcomb_mem : tcomb ∈ monomials 3 := (mem_monomials 3 _).2 ⟨by decide, by decide⟩

lemma rcomb_mem : rcomb ∈ monomials 3 := (mem_monomials 3 _).2 ⟨by decide, by decide⟩

/-- **The shuffle monomials of arity three** are the three combs. -/
lemma mono3_eq (σ : Mono (ComGen 2) 3) : σ.1 = lcomb ∨ σ.1 = tcomb ∨ σ.1 = rcomb := by
  have hm := (mem_monomials 3 σ.1).1 σ.2
  obtain ⟨e, f, h | h | h⟩ := mono3_cases hm.1 hm.2 <;> cases e <;> cases f <;> simp [h, lcomb,
    tcomb, rcomb]

/-- **The leading monomials**: the two left combs. -/
def leads : Set (LTree (ComGen 2)) := {lcomb, tcomb}

/-- The ranking of the decoration, for the path-lexicographic key. -/
@[nolint unusedArguments]
def rk : ComGen 2 → ℕ := fun _ => 0

lemma key_rcomb_lt_lcomb : pathKey rk 3 rcomb < pathKey rk 3 lcomb := by decide

lemma key_rcomb_lt_tcomb : pathKey rk 3 rcomb < pathKey rk 3 tcomb := by decide

/-! ## The relators -/

variable (K : Type*) [Field K]

/-- **The augmentation** in arity `n`: the sum of the coefficients. -/
noncomputable def aug (n : ℕ) : (Mono (ComGen 2) n → K) →ₗ[K] K :=
  ∑ σ, LinearMap.proj σ

/-- **The relators of the commutative operad**: the vectors of arity three whose coefficients sum
to zero. -/
noncomputable def rel : Submodule K (Mono (ComGen 2) 3 → K) := LinearMap.ker (aug K 3)

variable {K}

lemma aug_apply {n : ℕ} (v : Mono (ComGen 2) n → K) : aug K n v = ∑ σ, v σ := by
  simp [aug]

/-- The augmentation of the vector of a monomial is `1`. -/
lemma aug_vecOf {n : ℕ} {t : LTree (ComGen 2)} (ht : t ∈ monomials n) :
    aug K n (vecOf K n t) = 1 := by
  rw [aug_apply, Finset.sum_eq_single ⟨t, ht⟩ (fun σ _ hσ => ?_) (by simp)]
  · simp [vecOf]
  · exact if_neg fun h => hσ (Subtype.ext h)

lemma vecOf_apply_ne {n : ℕ} {t : LTree (ComGen 2)} {σ : Mono (ComGen 2) n} (h : σ.1 ≠ t) :
    vecOf K n t σ = 0 := if_neg h

lemma vecOf_apply_of_eq {n : ℕ} {t : LTree (ComGen 2)} {σ : Mono (ComGen 2) n} (h : σ.1 = t) :
    vecOf K n t σ = 1 := if_pos h

/-- **The relators are spanned by the rules**: each left comb minus the right comb. -/
theorem rel_eq_span : rel K = Submodule.span K
    {vecOf K 3 lcomb - vecOf K 3 rcomb, vecOf K 3 tcomb - vecOf K 3 rcomb} := by
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.2 ?_)
  · have h0 : ∑ σ, v σ = 0 := by rw [← aug_apply]; exact hv
    set l : Mono (ComGen 2) 3 := ⟨lcomb, lcomb_mem⟩
    set t : Mono (ComGen 2) 3 := ⟨tcomb, tcomb_mem⟩
    set r : Mono (ComGen 2) 3 := ⟨rcomb, rcomb_mem⟩
    have huniv : (Finset.univ : Finset (Mono (ComGen 2) 3)) = {l, t, r} := by
      ext σ
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases mono3_eq σ with h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
    have hlt : l ≠ t := fun h => by simpa [l, t, lcomb, tcomb] using congrArg Subtype.val h
    have hlr : l ≠ r := fun h => by simpa [l, r, lcomb, rcomb] using congrArg Subtype.val h
    have htr : t ≠ r := fun h => by simpa [t, r, tcomb, rcomb] using congrArg Subtype.val h
    rw [huniv, Finset.sum_insert (by simp [hlt, hlr]), Finset.sum_insert (by simp [htr]),
      Finset.sum_singleton] at h0
    have hv : v = v l • (vecOf K 3 lcomb - vecOf K 3 rcomb) +
        v t • (vecOf K 3 tcomb - vecOf K 3 rcomb) := by
      funext σ
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rcases mono3_eq σ with h | h | h
      · rw [vecOf_apply_of_eq h, vecOf_apply_ne (by rw [h]; decide),
          vecOf_apply_ne (by rw [h]; decide), show σ = l from Subtype.ext h]
        ring
      · rw [vecOf_apply_of_eq h, vecOf_apply_ne (by rw [h]; decide),
          vecOf_apply_ne (by rw [h]; decide), show σ = t from Subtype.ext h]
        ring
      · rw [vecOf_apply_of_eq h, vecOf_apply_ne (by rw [h]; decide),
          vecOf_apply_ne (by rw [h]; decide), show σ = r from Subtype.ext h]
        linear_combination h0
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rintro _ (rfl | rfl) <;>
      simp [rel, map_sub, aug_vecOf lcomb_mem, aug_vecOf tcomb_mem, aug_vecOf rcomb_mem]

/-! ## The ideal and the normal monomials -/

/-- **The augmentation vanishes on the ideal**: the substitutions of a relator at an edge of a
monomial are monomials, so their combination has the coefficient sum of the relator. -/
theorem idealOf_le_ker (n : ℕ) : idealOf K (rel K) n ≤ LinearMap.ker (aug K n) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨t, p, s, r, hr, he, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, substVec, map_sum]
  have h1 : ∀ σ : Mono (ComGen 2) 3,
      aug K n (r σ • vecOf K n (t.1.substAt p s σ.1)) = r σ := fun σ => by
    rw [map_smul, aug_vecOf (substAt_mem_monomials t.2 he σ.2), smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun σ _ => h1 σ, ← aug_apply]
  exact hr

/-- Every window of an edge into the first slot is leading. -/
lemma leads_spec (e f : ComGen 2) :
    node e (node f (leaf 0) (leaf 1)) (leaf 2) ∈ leads ∧
      node e (node f (leaf 0) (leaf 2)) (leaf 1) ∈ leads := by
  cases e
  cases f
  exact ⟨Or.inl rfl, Or.inr rfl⟩

/-- **There is at most one normal monomial in every arity**: the right comb. -/
theorem normal_unique {n : ℕ} {x y : Mono (ComGen 2) n} (hx : IsNormal leads x.1)
    (hy : IsNormal leads y.1) : x = y := by
  have hxm := (mem_monomials n x.1).1 x.2
  have hym := (mem_monomials n y.1).1 y.2
  obtain ⟨w, hw, -⟩ := (isNormal_iff leads_spec hxm.1 hxm.2).1 hx
  obtain ⟨w', hw', -⟩ := (isNormal_iff leads_spec hym.1 hym.2).1 hy
  have hlen : w.length = w'.length := by
    have h1 := hxm.2.length_eq
    have h2 := hym.2.length_eq
    rw [hw, labels_rightComb] at h1
    rw [hw', labels_rightComb] at h2
    simp only [List.length_range'] at h1 h2
    omega
  have : w = w' := List.ext_getElem hlen fun _ _ _ => Subsingleton.elim _ _
  exact Subtype.ext (by rw [hw, hw', this])

/-! ## The Gröbner basis and Koszulness -/

variable (K) in
/-- **The relators are a quadratic Gröbner basis** for the path-lexicographic key, with the two
left combs leading. -/
theorem isGroebner : IsGroebner K rk leads (rel K) where
  mem ℓ hℓ := by
    rcases hℓ with rfl | rfl
    · exact lcomb_mem
    · exact tcomb_mem
  lead ℓ hℓ := by
    have hℓm : ℓ ∈ monomials 3 := by
      rcases hℓ with rfl | rfl
      · exact lcomb_mem
      · exact tcomb_mem
    have hℓr : ℓ ≠ rcomb := by rcases hℓ with rfl | rfl <;> decide
    have hkey : pathKey rk 3 rcomb < pathKey rk 3 ℓ := by
      rcases hℓ with rfl | rfl
      · exact key_rcomb_lt_lcomb
      · exact key_rcomb_lt_tcomb
    refine ⟨vecOf K 3 ℓ - vecOf K 3 rcomb, ?_, ?_, fun σ hσ hne => ?_⟩
    · simp [rel, map_sub, aug_vecOf hℓm, aug_vecOf rcomb_mem]
    · simp [vecOf, hℓr]
    · by_cases hσr : σ.1 = rcomb
      · rwa [hσr]
      · exact absurd (by simp [vecOf, hσ, hσr]) hne
  indep n v hv hN := by
    by_contra hne
    obtain ⟨y, hy⟩ : ∃ y, v y ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hyN : IsNormal leads y.1 := by
      by_contra h
      exact hy (hN y h)
    have h0 : aug K n v = 0 := idealOf_le_ker n hv
    rw [aug_apply, Finset.sum_eq_single y (fun σ _ hσ => ?_) (by simp)] at h0
    · exact hy h0
    · by_contra h
      exact hσ (normal_unique (by by_contra h'; exact h (hN σ h')) hyN)

variable (K) in
/-- **The commutative operad is Koszul as a binary shuffle operad**, by the criterion of
Dotsenko and Khoroshkin. -/
theorem isKoszul : ShuffleBar.IsKoszul K (rel K) :=
  ShuffleBar.isKoszul K rk (isGroebner K)

variable (K) in
/-- **The Koszul dual relators of the commutative operad present a Koszul operad.** -/
theorem isKoszul_dualRel : ShuffleBar.IsKoszul K (dualRel K (rel K)) :=
  ShuffleBar.isKoszul_dualRel (isGroebner K)

variable (K) in
/-- **The commutative operad is Koszul in both shuffle senses**: as a binary shuffle operad,
presented by `rel`, and as a shuffle operad with generators of any arity, presented by
`ComGen.rules`. The relators of the two are the same differences of combs (`rel_eq_span`); the
two Koszulness predicates are proved separately. -/
theorem isKoszul_and : ShuffleBar.IsKoszul K (rel K) ∧ (ComGen.rules K).IsKoszul :=
  ⟨isKoszul K, ComGen.isKoszul⟩

end ComBin

end Operad
