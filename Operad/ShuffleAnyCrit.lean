/-
# The Koszul criterion in shuffle coordinates, for generators of any arity

Step (2c) of the symmetric–shuffle bridge for generators of any arity, fifth part. Setting as in
`Operad.ShuffleAnyTop`.

* **A criterion for a comparison map into a quotient of a bigraded complex**
  (`bigraded_criterion`): the map is a quasi-isomorphism iff the homology of the quotient
  vanishes below the diagonal, when the subspace divided out is stable under the projections onto
  the bidegrees and the cycles on the diagonal are the values of the map.
* **The bidegrees of the bar trees** (`STree.Bar.bideg`): the numbers of generators and of
  components; the projections onto them (`prS`) commute with the bar differential up to the shift
  of the number of components (`STree.Bar.prS_d`).
* **The Koszul criterion in shuffle coordinates, given the relator ideal**
  (`ShuffleAnySym.isKoszul_iff_shuffle_of_J`): for quadratic relators on generators of any arity
  over a field of characteristic zero, and subspaces `Id n` of the combinations of bar trees on
  `0, …, n - 1`, stable under the projections onto the bidegrees, with `ΦL x ∈ Id n ↔ x ∈ Krel`,
  **the presented operad is Koszul iff in every arity `n ≥ 2` every cycle modulo `Id n` with
  fewer components than generators is a boundary modulo `Id n`**.

Not proved here: that the ideal of the flagged rules of `Operad.ShuffleAnyKoszul` is such a
family `Id`, which would identify the right-hand side with `Rules.IsKoszul`. That identification,
the any-arity version of `ShuffleBarSym.map_ΦL_Krel`, is the remaining part of the bridge.
-/
import Operad.ShuffleAnyDiag

universe u

namespace Operad

open Function Sym GerBV GrComposite STree FreeGr Bar

/-! ## A criterion for a comparison map into a bigraded quotient complex -/

section Abstract

variable {K : Type*} [CommRing K] {V W Bm Pd Cm : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup Bm] [Module K Bm] [AddCommGroup Pd] [Module K Pd]
  [AddCommGroup Cm] [Module K Cm]

/-- **A comparison map into a quotient of a bigraded complex is a quasi-isomorphism iff the
homology of the quotient vanishes below the diagonal.** Here `π : V → B` is a surjective chain
map with kernel `𝒦`; `Φ : V → W` an injective chain map with `Φ x ∈ Id ↔ x ∈ 𝒦`, whose range
is the sum of the bidegrees `C (w, s)`, with projections `pr`; `d` lowers `s` by one; `Id` is
stable under the projections; the bidegrees with `s = 0` or `w < s` vanish; the diagonal `Dg`
contains the bidegrees `(w, w)`, is killed by the projections off the diagonal, and is the image
of a map `cut : C → B` (`g3`, `g4`) whose cycles come from `P` (`t1`), injectively. -/
theorem bigraded_criterion (Φ : V →ₗ[K] W) (π : V →ₗ[K] Bm) (dV : V →ₗ[K] V)
    (dW : W →ₗ[K] W) (dB : Bm →ₗ[K] Bm) (cut : Cm →ₗ[K] Bm) (incl : Pd →ₗ[K] Cm)
    (hΦ : Function.Injective Φ) (hπ : Function.Surjective π)
    (hΦd : ∀ x, Φ (dV x) = dW (Φ x)) (hπd : ∀ x, π (dV x) = dB (π x))
    (𝒦 : Submodule K V) (hker : ∀ x, x ∈ 𝒦 ↔ π x = 0) (Id : Submodule K W)
    (hJ : ∀ x, Φ x ∈ Id ↔ x ∈ 𝒦)
    (pr : ℕ × ℕ → W →ₗ[K] W) (C : ℕ × ℕ → Submodule K W)
    (p1 : ∀ p X, pr p X ∈ C p) (p2 : ∀ p X, X ∈ C p → pr p X = X)
    (p3 : ∀ x, ∃ F : Finset (ℕ × ℕ), Φ x = ∑ p ∈ F, pr p (Φ x))
    (p4 : ∀ w s x, pr (w, s) (dW (Φ x)) = dW (pr (w, s + 1) (Φ x)))
    (p5 : ∀ p, ∀ v ∈ Id, pr p v ∈ Id)
    (p6 : ∀ w s, w < s → ∀ X ∈ C (w, s), X = 0)
    (p7 : ∀ p, ∀ X ∈ C p, ∃ x, Φ x = X)
    (p8 : ∀ w, ∀ X ∈ C (w, 0), X = 0)
    (Dg : Submodule K W) (g1 : ∀ w s, s ≠ w → ∀ X ∈ Dg, pr (w, s) X = 0)
    (g2 : ∀ w, C (w, w) ≤ Dg)
    (g3 : ∀ y, ∃ v, π v = cut y ∧ Φ v ∈ Dg)
    (g4 : ∀ X ∈ Dg, ∃ v y, Φ v = X ∧ π v = cut y)
    (t1 : ∀ y, dB (cut y) = 0 → ∃ x, cut (incl x) = cut y)
    (hf : Function.Injective fun x => cut (incl x)) :
    ((∀ x b, cut (incl x) = dB b → x = 0) ∧
      ∀ z, dB z = 0 → ∃ x b, z = cut (incl x) + dB b) ↔
    ∀ w s, s < w → ∀ v ∈ C (w, s), dW v ∈ Id → ∃ u ∈ C (w, s + 1), v - dW u ∈ Id := by
  have hA : ∀ x b, cut (incl x) = dB b → x = 0 := by
    intro x b hxb
    obtain ⟨v, hv, hvD⟩ := g3 (incl x)
    obtain ⟨u0, rfl⟩ := hπ b
    have h1 : v - dV u0 ∈ 𝒦 := by rw [hker, map_sub, hπd, hv, hxb, sub_self]
    have h2 : Φ v - dW (Φ u0) ∈ Id := by
      rw [← hΦd, ← map_sub]
      exact (hJ _).2 h1
    have hcomp : ∀ p, pr p (Φ v) ∈ Id := by
      rintro ⟨w, s⟩
      by_cases hs : s = w
      · subst hs
        have h3 := p5 (s, s) _ h2
        rw [map_sub, p4, p6 s (s + 1) (Nat.lt_succ_self s) _ (p1 _ _), map_zero, sub_zero] at h3
        exact h3
      · rw [g1 w s hs _ hvD]
        exact zero_mem _
    obtain ⟨F, hF⟩ := p3 v
    have h3 : Φ v ∈ Id := by
      rw [hF]
      exact Submodule.sum_mem _ fun p _ => hcomp p
    have h4 : cut (incl x) = 0 := by rw [← hv, ← hker, ← hJ]; exact h3
    exact hf (h4.trans (by show (0 : Bm) = cut (incl 0); rw [map_zero, map_zero]))
  constructor
  · rintro ⟨-, hB⟩ w s hsw v hv hdv
    obtain ⟨v0, rfl⟩ := p7 _ _ hv
    have h1 : dV v0 ∈ 𝒦 := (hJ _).1 (by rw [hΦd]; exact hdv)
    obtain ⟨x, b, hxb⟩ := hB (π v0) (by rw [← hπd, ← hker]; exact h1)
    obtain ⟨v₁, hv₁, hv₁D⟩ := g3 (incl x)
    obtain ⟨u0, rfl⟩ := hπ b
    have h2 : v0 - v₁ - dV u0 ∈ 𝒦 := by
      rw [hker, map_sub, map_sub, hπd, hv₁, hxb]
      abel
    have h3 : Φ v0 - Φ v₁ - dW (Φ u0) ∈ Id := by
      rw [← hΦd, ← map_sub, ← map_sub]
      exact (hJ _).2 h2
    have h4 := p5 (w, s) _ h3
    rw [map_sub, map_sub, p2 _ _ hv, g1 w s (Nat.ne_of_lt hsw) _ hv₁D, sub_zero, p4] at h4
    exact ⟨_, p1 _ _, h4⟩
  · intro h
    refine ⟨hA, fun z hz => ?_⟩
    obtain ⟨z0, rfl⟩ := hπ z
    have h1 : dV z0 ∈ 𝒦 := by rw [hker, hπd]; exact hz
    have h2 : dW (Φ z0) ∈ Id := by rw [← hΦd]; exact (hJ _).2 h1
    have hzero : ∀ p, pr p (Φ z0) = 0 → ∃ v x b, Φ v = pr p (Φ z0) ∧ π v = cut (incl x) + dB b :=
      fun p hp => ⟨0, 0, 0, by rw [map_zero, hp], by simp⟩
    have hcomp : ∀ p, ∃ v x b, Φ v = pr p (Φ z0) ∧ π v = cut (incl x) + dB b := by
      rintro ⟨w, s⟩
      rcases s with _ | s
      · exact hzero _ (p8 w _ (p1 _ _))
      have hd : dW (pr (w, s + 1) (Φ z0)) ∈ Id := by
        rw [← p4]
        exact p5 _ _ h2
      rcases lt_trichotomy (s + 1) w with hlt | heq | hgt
      · obtain ⟨u, hu, hvu⟩ := h w (s + 1) hlt _ (p1 _ _) hd
        obtain ⟨v, hv⟩ := p7 _ _ (p1 (w, s + 1) (Φ z0))
        obtain ⟨u0, rfl⟩ := p7 _ _ hu
        refine ⟨v, 0, π u0, hv, ?_⟩
        have h3 : v - dV u0 ∈ 𝒦 := (hJ _).1 (by rw [map_sub, hΦd, hv]; exact hvu)
        rw [hker, map_sub, hπd, sub_eq_zero] at h3
        rw [h3, map_zero, map_zero, zero_add]
      · subst heq
        obtain ⟨v, y, hv, hy⟩ := g4 _ (g2 (s + 1) (p1 (s + 1, s + 1) (Φ z0)))
        have h3 : dV v ∈ 𝒦 := (hJ _).1 (by rw [hΦd, hv]; exact hd)
        obtain ⟨x, hx⟩ := t1 y (by rw [← hy, ← hπd, ← hker]; exact h3)
        exact ⟨v, x, 0, hv, by rw [hy, hx, map_zero, add_zero]⟩
      · exact hzero _ (p6 w (s + 1) hgt _ (p1 _ _))
    choose v x b hv hvx using hcomp
    obtain ⟨F, hF⟩ := p3 z0
    have h3 : z0 = ∑ p ∈ F, v p := hΦ (by
      rw [map_sum]
      exact hF.trans (Finset.sum_congr rfl fun p _ => (hv p).symm))
    refine ⟨∑ p ∈ F, x p, ∑ p ∈ F, b p, ?_⟩
    rw [h3, map_sum, map_sum, map_sum, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => hvx p

end Abstract

/-! ## Projections of combinations onto sets of basis elements -/

section PrS

variable {K : Type*} [CommRing K] {α : Type*}

/-- **The projection of a combination onto the basis elements in `S`.** -/
noncomputable def prS (S : Set α) : (α →₀ K) →ₗ[K] (α →₀ K) := by
  classical exact (Finsupp.supported K K S).subtype ∘ₗ Finsupp.restrictDom K K S

lemma prS_apply_of_mem (S : Set α) (v : α →₀ K) {x : α} (hx : x ∈ S) : prS S v x = v x := by
  classical
  simp [prS, Finsupp.restrictDom_apply, hx]

lemma prS_apply_of_notMem (S : Set α) (v : α →₀ K) {x : α} (hx : x ∉ S) : prS S v x = 0 := by
  classical
  simp [prS, Finsupp.restrictDom_apply, hx]

lemma prS_apply_of_eq_zero (S : Set α) {v : α →₀ K} {x : α} (hx : v x = 0) : prS S v x = 0 := by
  by_cases hS : x ∈ S
  · rw [prS_apply_of_mem S v hS, hx]
  · exact prS_apply_of_notMem S v hS

lemma prS_mem (S : Set α) (v : α →₀ K) : prS S v ∈ Finsupp.supported K K S :=
  (Finsupp.mem_supported K _).2 fun x hx => by
    by_contra h
    exact (Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hx)) (prS_apply_of_notMem S v h)

lemma prS_of_mem {S : Set α} {v : α →₀ K} (hv : v ∈ Finsupp.supported K K S) : prS S v = v := by
  ext x
  by_cases hx : x ∈ S
  · exact prS_apply_of_mem S v hx
  · rw [prS_apply_of_notMem S v hx]
    exact (Finsupp.notMem_support_iff.1 fun h =>
      hx ((Finsupp.mem_supported K v).1 hv (Finset.mem_coe.2 h))).symm

lemma prS_of_disjoint {S S' : Set α} {v : α →₀ K} (hv : v ∈ Finsupp.supported K K S')
    (hd : ∀ x ∈ S', x ∉ S) : prS S v = 0 := by
  ext x
  rw [Finsupp.zero_apply]
  by_cases hx : x ∈ S
  · rw [prS_apply_of_mem S v hx]
    exact Finsupp.notMem_support_iff.1 fun h =>
      hd x ((Finsupp.mem_supported K v).1 hv (Finset.mem_coe.2 h)) hx
  · exact prS_apply_of_notMem S v hx

lemma prS_congr {S S' : Set α} {v : α →₀ K} (h : ∀ x ∈ v.support, (x ∈ S ↔ x ∈ S')) :
    prS S v = prS S' v := by
  ext x
  by_cases hx : x ∈ v.support
  · by_cases hS : x ∈ S
    · rw [prS_apply_of_mem S v hS, prS_apply_of_mem S' v ((h x hx).1 hS)]
    · rw [prS_apply_of_notMem S v hS, prS_apply_of_notMem S' v fun h' => hS ((h x hx).2 h')]
  · have h0 : v x = 0 := Finsupp.notMem_support_iff.1 hx
    rw [prS_apply_of_eq_zero S h0, prS_apply_of_eq_zero S' h0]

/-- **A combination is the sum of its parts along a classification of the basis.** -/
lemma eq_sum_prS {ι : Type*} [DecidableEq ι] (κ : α → ι) (v : α →₀ K) :
    v = ∑ p ∈ v.support.image κ, prS {x | κ x = p} v := by
  ext x
  rw [Finsupp.finsetSum_apply]
  by_cases hx : x ∈ v.support
  · rw [Finset.sum_eq_single (κ x) (fun p _ hp => prS_apply_of_notMem _ v fun h => hp h.symm)
      (fun h => absurd (Finset.mem_image_of_mem κ hx) h)]
    exact (prS_apply_of_mem {y | κ y = κ x} v (rfl : κ x = κ x)).symm
  · have h0 : v x = 0 := Finsupp.notMem_support_iff.1 hx
    rw [h0]
    exact (Finset.sum_eq_zero fun p _ => prS_apply_of_eq_zero _ h0).symm

lemma eq_zero_of_mem_supported {S : Set α} (h : ∀ a, a ∉ S) {v : α →₀ K}
    (hv : v ∈ Finsupp.supported K K S) : v = 0 :=
  Finsupp.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem fun a ha =>
    h a ((Finsupp.mem_supported K v).1 hv (Finset.mem_coe.2 ha)))

end PrS

/-! ## The bidegrees of the bar trees -/

namespace STree.Bar

variable {E : ℕ → Type*} {K : Type*} [CommRing K] {A : Finset ℕ}

/-- The bidegree of a bar tree: its numbers of generators and of components. -/
def bideg (X : SMono (BE E) A) : ℕ × ℕ := (X.1.weight, (cuts X).card + 1)

lemma mem_P_iff {X : SMono (BE E) A} {w s : ℕ} :
    X ∈ P A w s ↔ rootF X.1 = false ∧ bideg X = (w, s) := by
  rw [bideg, Prod.mk.injEq]
  rfl

lemma mem_P_bideg {X : SMono (BE E) A} (hX : rootF X.1 = false) :
    X ∈ P A (bideg X).1 (bideg X).2 := ⟨hX, rfl, rfl⟩

lemma notMem_P_of_ne {X : SMono (BE E) A} {w s w' s' : ℕ} (h : (w', s') ≠ (w, s))
    (hX : X ∈ P A w' s') : X ∉ P A w s := fun hX' =>
  h ((mem_P_iff.1 hX).2.symm.trans (mem_P_iff.1 hX').2)

lemma notMem_P_zero (X : SMono (BE E) A) (w : ℕ) : X ∉ P A w 0 := fun h => by
  have := h.2.2
  omega

/-- **A combination of bar trees without a cut above the root is the sum of its bidegrees.** -/
lemma eq_sum_prS_P {v : SMono (BE E) A →₀ K}
    (hv : v ∈ Finsupp.supported K K {X : SMono (BE E) A | rootF X.1 = false}) :
    v = ∑ p ∈ v.support.image bideg, prS (P A p.1 p.2) v := by
  classical
  refine (eq_sum_prS bideg v).trans (Finset.sum_congr rfl fun p _ => prS_congr fun X hX => ?_)
  have hr : rootF X.1 = false := (Finsupp.mem_supported K v).1 hv (Finset.mem_coe.2 hX)
  rw [mem_P_iff]
  exact ⟨fun h => ⟨hr, h⟩, fun h => h.2⟩

/-- **The differential lowers the number of components**, bidegree by bidegree. -/
lemma prS_d_single {X : SMono (BE E) A} (hX : rootF X.1 = false) (w s : ℕ) :
    prS (P A w s) (d K (Finsupp.single X 1))
      = d K (prS (P A w (s + 1)) (Finsupp.single X (1 : K))) := by
  by_cases h : X ∈ P A w (s + 1)
  · rw [prS_of_mem (d_mem_P h), prS_of_mem (Finsupp.single_mem_supported K _ h)]
  · have h1 : prS (P A w (s + 1)) (Finsupp.single X (1 : K)) = 0 :=
      prS_of_disjoint (S' := {X}) (Finsupp.single_mem_supported K _ rfl) fun Y hY => by
        rw [Set.mem_singleton_iff.1 hY]
        exact h
    have h2 : X ∈ P A (bideg X).1 ((cuts X).card + 1) := mem_P_bideg hX
    have h3 : ∀ Y : SMono (BE E) A, Y ∈ P A (bideg X).1 (cuts X).card → Y ∉ P A w s :=
      fun Y hY hY' => by
      have e := (mem_P_iff.1 hY).2.symm.trans (mem_P_iff.1 hY').2
      rw [Prod.mk.injEq] at e
      exact h ⟨hX, e.1, by rw [← e.2]⟩
    rw [h1, map_zero, prS_of_disjoint (d_mem_P h2) h3]

lemma prS_d {v : SMono (BE E) A →₀ K}
    (hv : v ∈ Finsupp.supported K K {X : SMono (BE E) A | rootF X.1 = false}) (w s : ℕ) :
    prS (P A w s) (d K v) = d K (prS (P A w (s + 1)) v) := by
  have hle : Finsupp.supported K K {X : SMono (BE E) A | rootF X.1 = false}
      ≤ LinearMap.eqLocus (prS (P A w s) ∘ₗ d K) (d K ∘ₗ prS (P A w (s + 1))) := by
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨X, hX, rfl⟩
    exact prS_d_single hX w s
  exact hle hv

end STree.Bar

namespace ShuffleAnySym

open ShuffleBarSym

section Crit

variable {K : Type u} [Field K] [CharZero K]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))
  (hq : Koszul.IsQuadratic K E r)

omit [CharZero K] [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma barSet_eq (n : ℕ) :
    barSet T n = {X : SMono (BE T) (Finset.range n) | rootF X.1 = false} := rfl

omit [CharZero K] in
/-- In arity at least two a bar tree has at most as many components as generators. -/
lemma notMem_P_of_lt {n : ℕ} (hn : 2 ≤ n) {w s : ℕ} (hws : w < s)
    (X : SMono (BE T) (Finset.range n)) : X ∉ Bar.P (Finset.range n) w s := fun hX => by
  obtain ⟨t, ht⟩ := (treeEquiv n).surjective ⟨X, hX.1⟩
  have hX' : (treeEquiv n t : barSet T n).1 = X := congrArg Subtype.val ht
  have h1 := card_cuts_treeEquiv hn t
  have h2 := weight_le_weight_toBar t.1
  have h3 : (toBar t.1).weight = w := by
    have := hX.2.1
    rw [← hX'] at this
    exact this
  have h4 : (cuts (treeEquiv n t : barSet T n).1).card + 1 = s := by
    rw [hX']
    exact hX.2.2
  omega

omit [CharZero K] in
lemma ΦL_mem_supported (n : ℕ) (x : BarCoop (Ibar K E c hc) (Fin n)) :
    ΦL c hc n x ∈ Finsupp.supported K K
      {X : SMono (BE T) (Finset.range n) | rootF X.1 = false} := by
  have h : ΦL c hc n x ∈ LinearMap.range (ΦL c hc n) := LinearMap.mem_range_self _ x
  rw [ΦL_range] at h
  exact h

omit [CharZero K] in
lemma exists_ΦL_eq {n : ℕ} {w s : ℕ} {X : SMono (BE T) (Finset.range n) →₀ K}
    (hX : X ∈ Bar.C K (Finset.range n) w s) : ∃ x, ΦL c hc n x = X := by
  have h : X ∈ LinearMap.range (ΦL c hc n) := by
    rw [ΦL_range]
    exact Finsupp.supported_mono (fun Y hY => hY.1) hX
  exact LinearMap.mem_range.1 h

include hq in
/-- **The Koszul criterion in arity `n`, in shuffle coordinates**: for a subspace `Id` of the
combinations of bar trees, stable under the projections onto the bidegrees, whose preimage under
`ΦL` is the relator ideal `Krel`, the comparison morphism `P^¡(n) → B(P, Ī_P)(n)` is a
quasi-isomorphism iff every cycle modulo `Id` with fewer components than generators is a
boundary modulo `Id`. -/
theorem crit_fin {n : ℕ} (hn : 2 ≤ n) (Id : Submodule K (SMono (BE T) (Finset.range n) →₀ K))
    (hId : ∀ w s, ∀ v ∈ Id, prS (Bar.P (Finset.range n) w s) v ∈ Id)
    (hJ : ∀ x, ΦL c hc n x ∈ Id ↔ x ∈ (Krel K E c hc r).sub (Fin n)) :
    ((∀ x b, cutN c hc r n ((Koszul.dualSub K E r).incl (Fin n) x)
        = Bar.d (Ipres K E c hc r) (Fin n) b → x = 0) ∧
      ∀ z, Bar.d (Ipres K E c hc r) (Fin n) z = 0 →
        ∃ x b, z = cutN c hc r n ((Koszul.dualSub K E r).incl (Fin n) x)
          + Bar.d (Ipres K E c hc r) (Fin n) b) ↔
    ∀ w s, s < w → ∀ v ∈ Bar.C K (Finset.range n) w s, STree.Bar.d K v ∈ Id →
      ∃ u ∈ Bar.C K (Finset.range n) w (s + 1), v - STree.Bar.d K u ∈ Id :=
  bigraded_criterion (ΦL c hc n) (projN c hc r n) (Bar.d (Ibar K E c hc) (Fin n))
    (STree.Bar.d K) (Bar.d (Ipres K E c hc r) (Fin n)) (cutN c hc r n)
    ((Koszul.dualSub K E r).incl (Fin n)) (ΦL_injective c hc n)
    (barProj_surjective c hc r (Fin n)) (ΦL_d c hc) (barProj_d c hc r)
    ((Krel K E c hc r).sub (Fin n)) (mem_Krel_iff c hc r) Id hJ
    (fun p => prS (Bar.P (Finset.range n) p.1 p.2)) (fun p => Bar.C K (Finset.range n) p.1 p.2)
    (fun _ _ => prS_mem _ _) (fun _ _ hX => prS_of_mem hX)
    (fun x => ⟨_, Bar.eq_sum_prS_P (ΦL_mem_supported c hc n x)⟩)
    (fun w s x => Bar.prS_d (ΦL_mem_supported c hc n x) w s)
    (fun p v hv => hId p.1 p.2 v hv)
    (fun _ _ hws _ hX => eq_zero_of_mem_supported (notMem_P_of_lt hn hws) hX)
    (fun _ _ hX => exists_ΦL_eq c hc hX)
    (fun w _ hX => eq_zero_of_mem_supported (fun Y => Bar.notMem_P_zero Y w) hX)
    (Finsupp.supported K K (diagSet T n))
    (fun w s hsw _ hX => prS_of_disjoint hX fun Y hY hY' => hsw (by
      have h1 := hY.2
      have h2 := hY'.2.1
      have h3 := hY'.2.2
      omega))
    (fun w => Finsupp.supported_mono fun Y hY => ⟨hY.1, by
      have h2 := hY.2.1
      have h3 := hY.2.2
      omega⟩)
    (fun y => exists_diag_lift c hc r hq hn y)
    (fun _ hX => exists_cut_of_diag c hc r hq hn hX)
    (fun y hy => toBar_surj_diag c hc r hq y hy)
    (dualToBar_injective c hc r hq (Fin n))

include hq in
/-- **The Koszul criterion in shuffle coordinates, given the relator ideal**: for quadratic
relators on generators of any arity over a field of characteristic zero, and subspaces `Id n`
of the combinations of bar trees on `0, …, n - 1`, stable under the projections onto the
bidegrees, whose preimages under `ΦL` are the relator ideals `Krel`, the presented operad is
Koszul iff in every arity `n ≥ 2` every cycle modulo `Id n` with fewer components than
generators is a boundary modulo `Id n`. -/
theorem isKoszul_iff_shuffle_of_J
    (Id : ∀ n, Submodule K (SMono (BE T) (Finset.range n) →₀ K))
    (hId : ∀ n w s, ∀ v ∈ Id n, prS (Bar.P (Finset.range n) w s) v ∈ Id n)
    (hJ : ∀ n, 2 ≤ n → ∀ x, ΦL c hc n x ∈ Id n ↔ x ∈ (Krel K E c hc r).sub (Fin n)) :
    Koszul.IsKoszul K E r ↔ ∀ n, 2 ≤ n → ∀ w s, s < w →
      ∀ v ∈ Bar.C K (Finset.range n) w s, STree.Bar.d K v ∈ Id n →
        ∃ u ∈ Bar.C K (Finset.range n) w (s + 1), v - STree.Bar.d K u ∈ Id n := by
  refine (isKoszul_iff_toBar_fin c hc r hq).trans (forall_congr' fun n =>
    imp_congr_right fun hn => (Homology.map_zero_bijective_iff _ _).trans ?_)
  exact crit_fin c hc r hq hn (Id n) (hId n) (hJ n hn)

end Crit

end ShuffleAnySym

end Operad
