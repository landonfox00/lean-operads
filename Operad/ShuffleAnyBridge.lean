/-
# The bridge between the Koszulness of a presented operad and of its shuffle rules, any arity

Steps (2b) and (2c) of the symmetric–shuffle bridge (Dotsenko–Khoroshkin) for generators of any
arity, last part; the binary case is `ShuffleBarSym.isKoszul_iff_shuffle` with
`ShuffleBridge.isKoszul_iff`.

**`ShuffleAnySym.isKoszul_iff_rules`**: let `E` be a graded linear species over a field `K` of
characteristic zero with an even basis indexed by `T`, without generators in arities zero and
one; `r` quadratic relators in `T(E)`; and `G` rules on the shuffle monomials whose leading
monomials are not leaves, whose tails have as many generators as their leading monomials, and
whose ideal is the ideal of the relators in shuffle coordinates (`hR`). Then
`Koszul.IsKoszul K E r ↔ G.IsKoszul`.

The clauses of `Rules.IsKoszul` on any set of leaves follow from those on `0, …, n - 1` by
relabelling along the positions (`ShuffleAnySym.rules_clause_of_range`).

The hypothesis `hR` is not derived here from relators stable under the symmetric groups; see
`Operad.ShuffleAnyIdeal`.
-/
import Operad.ShuffleAnyIdeal
import Operad.ShuffleBridgeBar

universe u

namespace Operad

open Function Sym GerBV GrComposite STree FreeGr Bar

namespace ShuffleAnySym

open ShuffleBarSym ShuffleBridge

section Bridge

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))
  {ρ : Type*} {O : STree.AdmOrder T} (G : Rules K ρ O.toCtxOrder)
  (hlead : ∀ i a, (G.lead i).1 ≠ .leaf a)
  (hom : ∀ i, ∀ m ∈ (G.tail i).support, m.1.weight = (G.lead i).1.weight)
  (hR : ∀ k (y : FreeGrL K E (Fin k)), y ∈ (GrOperadIdeal.span K r).sub (Fin k) ↔
    (tBasisN c hc k).repr y ∈ (G.rw (Finset.range k)).ideal)

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
/-- **The clauses of `Rules.IsKoszul` on the leaves `0, …, n - 1` give the clauses on every set
of leaves with `n` elements**, by relabelling along the positions. -/
theorem rules_clause_of_range {A : Finset ℕ} {w s : ℕ}
    (hK : ∀ v ∈ Bar.C K (Finset.range A.card) w s,
      STree.Bar.d K v ∈ (G.bar.rw (Finset.range A.card)).ideal →
        ∃ u ∈ Bar.C K (Finset.range A.card) w (s + 1),
          v - STree.Bar.d K u ∈ (G.bar.rw (Finset.range A.card)).ideal)
    {v : SMono (BE T) A →₀ K} (hv : v ∈ Bar.C K A w s)
    (hdv : STree.Bar.d K v ∈ (G.bar.rw A).ideal) :
    ∃ u ∈ Bar.C K A w (s + 1), v - STree.Bar.d K u ∈ (G.bar.rw A).ideal := by
  have hβα : ∀ X : SMono (BE T) A, relabelM (ShuffleBridge.eltIn A) (strictMonoOn_eltIn A)
      (image_eltIn A)
      (relabelM (ShuffleBridge.posIn A) (strictMonoOn_posIn A) (image_posIn A) X) = X := fun X =>
    Subtype.ext (by
      show (X.1.relabel (ShuffleBridge.posIn A)).relabel (ShuffleBridge.eltIn A) = X.1
      rw [relabel_relabel]
      exact relabel_id fun a ha => eltIn_posIn (X.mem_labels.1 ha))
  set α := relabelM (E := BE T) (ShuffleBridge.posIn A) (strictMonoOn_posIn A) (image_posIn A)
  set β := relabelM (E := BE T) (ShuffleBridge.eltIn A) (strictMonoOn_eltIn A) (image_eltIn A)
  have hv' : Finsupp.mapDomain α v ∈ Bar.C K (Finset.range A.card) w s :=
    mapDomain_mem_supported K v fun X hX =>
      mem_P_relabelM _ _ _ ((Finsupp.mem_supported K v).1 hv hX)
  have hdv' : STree.Bar.d K (Finsupp.mapDomain α v)
      ∈ (G.bar.rw (Finset.range A.card)).ideal := by
    rw [d_relabelM]
    exact G.bar.mapDomain_mem_ideal (isSCtx_relabelM _ _ _) hdv
  obtain ⟨u, hu, hvu⟩ := hK _ hv' hdv'
  refine ⟨Finsupp.mapDomain β u, mapDomain_mem_supported K u fun X hX =>
    mem_P_relabelM _ _ _ ((Finsupp.mem_supported K u).1 hu hX), ?_⟩
  have hvβ : v = Finsupp.mapDomain β (Finsupp.mapDomain α v) := by
    rw [← Finsupp.mapDomain_comp, show β ∘ α = id from funext hβα, Finsupp.mapDomain_id]
  rw [hvβ, d_relabelM, ← Finsupp.mapDomain_sub]
  exact G.bar.mapDomain_mem_ideal (isSCtx_relabelM _ _ _) hvu

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
/-- A bar tree with a generator has at least two leaves. -/
lemma two_le_card_of_mem_P [IsEmpty (T 0)] [IsEmpty (T 1)] {A : Finset ℕ} {w s : ℕ}
    (hw : 0 < w) {X : SMono (BE T) A} (hX : X ∈ Bar.P A w s) : 2 ≤ A.card := by
  have h1 := hX.2.1
  rcases hXn : X.1 with a | ⟨e, c'⟩
  · rw [hXn] at h1
    simp only [STree.weight] at h1
    omega
  · have h2 := two_le_card_labels (T := BE T) (hXn ▸ X.isShuffle)
    rw [← hXn, X.labels_eq] at h2
    exact h2

include hlead hom hR in
/-- **The bridge for generators of any arity** (steps 2b and 2c of Dotsenko–Khoroshkin): for an
even graded linear species `E` with a basis indexed by `T`, without generators in arities zero
and one, over a field of characteristic zero, quadratic relators `r`, and homogeneous rules `G`
on shuffle monomials whose ideal is the ideal of the relators in shuffle coordinates, the
presented operad `T(E)/(r)` is Koszul iff the shuffle operad presented by the rules is
(`Rules.IsKoszul`). -/
theorem isKoszul_iff_rules [CharZero K] (hq : Koszul.IsQuadratic K E r) :
    Koszul.IsKoszul K E r ↔ G.IsKoszul := by
  rw [isKoszul_iff_rules_range c hc r G hlead hom hR hq]
  constructor
  · intro hK A w s hsw v hv hdv
    by_cases hA : 2 ≤ A.card
    · exact rules_clause_of_range G (hK A.card hA w s hsw) hv hdv
    · have h0 : v = 0 := eq_zero_of_mem_supported
        (fun X hX => hA (two_le_card_of_mem_P (by omega) hX)) hv
      refine ⟨0, zero_mem _, ?_⟩
      rw [h0, map_zero, sub_zero]
      exact zero_mem _
  · intro h n _ w s hsw v hv hdv
    exact h (Finset.range n) w s hsw v hv hdv

end Bridge

end ShuffleAnySym

end Operad
