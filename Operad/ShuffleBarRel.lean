/-
# The relator ideal in shuffle coordinates

Step (2c) of the bridge between symmetric and shuffle operads (Dotsenko–Khoroshkin), fourth part:
toward the hypothesis `hJ` of `ShuffleBarSym.isKoszul_iff_shuffle_of_J`, the identification
`ΦL (Krel) = ShuffleBar.J K (Rsh c hc r) ⊓ supported (barSet G n)`.

* **The relator subcomplex on the bar trees of one arity** (`ShuffleBar.J_inf_supported`): a
  relator substituted at an uncut edge of a valid bar tree `x` is supported on the valid bar trees
  whose labels are a permutation of those of `x` (`ShuffleBar.substRel_mem_supported`); so for a
  set `S` of bar trees closed, among the valid ones, under permuting labels (such as
  `ShuffleBarSym.barSet G n`), `J R ⊓ supported S` is spanned by the relators substituted in the
  trees of `S`.

Open: the identification itself. Its two inclusions need the ideal `Krel` of `B(T, Ī)` in a basis
adapted to the suspended relators (trees with a vertex in `s((r))`), the multilinearity of the
evaluation of shuffle trees in the label of one vertex, the bar tree of a tree whose vertex
monomial has a window substituted (`ShuffleBar.substBar` of `ShuffleBarSym.toBar`), the
invariance of `ShuffleBarSym.sign` under changing vertex monomials, and the ideal `(r)` of
`T(E)(Fin k)` in `tBasis` coordinates as the shuffle ideal of `Rsh` (for `r` concentrated in arity
three and stable under the permutations of `Fin 3`).
-/
import Operad.ShuffleBarTop

universe u v

namespace Operad

namespace ShuffleBar

open LTree

variable {E : Type v} (K : Type u) [CommRing K] [Fintype E] [DecidableEq E]

/-- **A substituted relator is supported on the valid bar trees with the labels of the tree.** -/
lemma substRel_mem_supported {x : BarTree E} (hx : Valid x) {p : List Bool} {s : Bool}
    (h : IsUncut x p s) (r : Mono E 3 → K) :
    substRel K x p s r ∈ Finsupp.supported K K {y | Valid y ∧ y.labels.Perm x.labels} :=
  Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ (Finsupp.single_mem_supported K _
    ⟨hx.substBar h σ, perm_labels_substBar hx.shuffle hx.nodup h (mono_shape σ).2.1⟩)

/-- **The relator subcomplex on a set of bar trees closed under permuting labels**: for a set `S`
of bar trees such that, among valid bar trees, membership depends only on the labels up to
permutation, `J R ∩ span S` is spanned by the relators substituted in the trees of `S`. -/
theorem J_inf_supported (R : Submodule K (Mono E 3 → K)) (S : Set (BarTree E))
    (hS : ∀ x y : BarTree E, Valid x → Valid y → x.labels.Perm y.labels → x ∈ S → y ∈ S) :
    J K R ⊓ Finsupp.supported K K S = Submodule.span K
      {v | ∃ x p s r, Valid x ∧ x ∈ S ∧ IsUncut x p s ∧ r ∈ R ∧ v = substRel K x p s r} := by
  classical
  apply le_antisymm
  · rintro v ⟨hvJ, hvS⟩
    have key : ∀ w ∈ J K R, Finsupp.filter (· ∈ S) w ∈ Submodule.span K
        {v | ∃ x p s r, Valid x ∧ x ∈ S ∧ IsUncut x p s ∧ r ∈ R ∧ v = substRel K x p s r} := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ => Finsupp.filter (· ∈ S) w ∈ _) ?_ ?_ ?_ ?_
        hw
      · rintro _ ⟨x, p, s, r, hx, hp, hr, rfl⟩
        have hsupp : ∀ y, substRel K x p s r y ≠ 0 → Valid y ∧ y.labels.Perm x.labels :=
          fun y hy => substRel_mem_supported K hx hp r (Finsupp.mem_support_iff.2 hy)
        by_cases hxS : x ∈ S
        · rw [(Finsupp.filter_eq_self_iff _ _).2 fun y hy => hS x y hx (hsupp y hy).1
            (hsupp y hy).2.symm hxS]
          exact Submodule.subset_span ⟨x, p, s, r, hx, hxS, hp, hr, rfl⟩
        · rw [(Finsupp.filter_eq_zero_iff _ _).2 fun y hyS => by
            by_contra hy
            exact hxS (hS y x (hsupp y hy).1 hx (hsupp y hy).2 hyS)]
          exact zero_mem _
      · beta_reduce
        rw [Finsupp.filter_zero]
        exact zero_mem _
      · intro a b _ _ ha hb
        beta_reduce at ha hb ⊢
        rw [Finsupp.filter_add]
        exact add_mem ha hb
      · intro a w _ hw
        beta_reduce at hw ⊢
        rw [Finsupp.filter_smul]
        exact Submodule.smul_mem _ a hw
    have := key v hvJ
    rwa [(Finsupp.filter_eq_self_iff _ _).2 fun y hy => hvS (Finsupp.mem_support_iff.2 hy)] at this
  · rw [Submodule.span_le]
    rintro _ ⟨x, p, s, r, hx, hxS, hp, hr, rfl⟩
    refine ⟨Submodule.subset_span ⟨x, p, s, r, hx, hp, hr, rfl⟩, fun y hy => ?_⟩
    have := substRel_mem_supported K hx hp r hy
    exact hS x y hx this.1 this.2.symm hxS

end ShuffleBar

end Operad
