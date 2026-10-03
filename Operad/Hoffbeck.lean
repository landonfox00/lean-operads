/-
# Complexes of cuts and filtered acyclicity

Two abstract tools for proving that bar constructions are acyclic, as needed for Koszulness.

* **Complexes of cuts** (`CutComplex`): objects with a finite set of *cuts* in a linearly ordered
  set and an operation *merging* along a cut, which removes it. Merging along each cut with the
  sign of its position among the cuts is a differential (`CutComplex.d_d`). Restricted to the cuts
  outside a set `L`, and given an operation *cutting* along an element `k₀ ∉ L`, cutting along `k₀`
  is a contracting homotopy (`CutComplex.dL_hL_add`): this is the complex of the subsets of a
  finite set, the chains of a simplex.
* **Hoffbeck's filtration argument** (`Hoffbeck.exact_of_leading`): a linear map on a free module
  whose basis lies over a well-founded order, equal to its *leading part* — which preserves the
  fibres — up to terms over strictly smaller elements, and squaring to zero, is exact wherever
  its leading part is exact on every fibre. The induction runs over the finite sets of elements
  below which a cycle lies, ordered by the Dershowitz–Manna order.
-/
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Order.Preorder.Finite

namespace Operad

namespace CutComplex

open Finsupp

variable {N : Type*} [LinearOrder N] (R : Type*) [CommRing R]

/-! ## Signs -/

/-- **The sign of an element** `k` among the cuts `S`: `-1` to the number of smaller cuts. -/
def sgn (S : Finset N) (k : N) : R := (-1) ^ (S.filter (· < k)).card

variable {R}

lemma sgn_mul_self (S : Finset N) (k : N) : sgn R S k * sgn R S k = 1 := by
  rw [sgn, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

lemma sgn_erase_self (S : Finset N) (k : N) : sgn R (S.erase k) k = sgn R S k := by
  rw [sgn, sgn, Finset.filter_erase, Finset.erase_eq_of_notMem (by simp)]

lemma sgn_insert_self (S : Finset N) (k : N) : sgn R (insert k S) k = sgn R S k := by
  rw [sgn, sgn, Finset.filter_insert, if_neg (lt_irrefl k)]

lemma sgn_erase {S : Finset N} {k k' : N} (hk : k ∈ S) :
    sgn R (S.erase k) k' = if k < k' then -sgn R S k' else sgn R S k' := by
  rw [sgn, sgn, Finset.filter_erase]
  split_ifs with hlt
  · have hm : k ∈ S.filter (· < k') := Finset.mem_filter.2 ⟨hk, hlt⟩
    rw [← Finset.insert_erase hm, Finset.card_insert_of_notMem (Finset.notMem_erase k _),
      Finset.erase_insert (Finset.notMem_erase k _), pow_succ]
    ring
  · rw [Finset.erase_eq_of_notMem (by simp [hlt])]

lemma sgn_insert {S : Finset N} {k k' : N} (hk : k ∉ S) :
    sgn R (insert k S) k' = if k < k' then -sgn R S k' else sgn R S k' := by
  rw [sgn, sgn, Finset.filter_insert]
  split_ifs with hlt
  · rw [Finset.card_insert_of_notMem (by simp [hk]), pow_succ]
    ring
  · rfl

/-! ## The differential -/

variable {X : Type*} (cs : X → Finset N) (mg : N → X → X)

/-- **The differential of a complex of cuts** on a basis element: merge along each cut, with its
sign. -/
noncomputable def dX (x : X) : X →₀ R := ∑ k ∈ cs x, sgn R (cs x) k • single (mg k x) 1

/-- **The differential of a complex of cuts.** -/
noncomputable def d : (X →₀ R) →ₗ[R] (X →₀ R) := linearCombination R (dX cs mg)

lemma d_single (x : X) (r : R) : d cs mg (single x r) = r • dX cs mg x :=
  linearCombination_single R r x

/-- A double sum over the ordered pairs of distinct elements of an antisymmetric function
vanishes. -/
lemma sum_sum_erase_eq_zero {M : Type*} [AddCommGroup M] (S : Finset N) (g : N → N → M)
    (hg : ∀ k ∈ S, ∀ k' ∈ S, k ≠ k' → g k k' + g k' k = 0) :
    ∑ k ∈ S, ∑ k' ∈ S.erase k, g k k' = 0 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) (fun p hp => ?_) (fun p hp _ => ?_)
    (fun p hp => ?_) (fun p _ => rfl)
  · obtain ⟨hp₁, hp₂⟩ := Finset.mem_sigma.1 hp
    exact hg _ hp₁ _ (Finset.mem_of_mem_erase hp₂) (Finset.ne_of_mem_erase hp₂).symm
  · obtain ⟨hp₁, hp₂⟩ := Finset.mem_sigma.1 hp
    intro h
    exact Finset.ne_of_mem_erase hp₂ (congrArg Sigma.fst h)
  · obtain ⟨hp₁, hp₂⟩ := Finset.mem_sigma.1 hp
    exact Finset.mem_sigma.2 ⟨Finset.mem_of_mem_erase hp₂,
      Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hp₂).symm, hp₁⟩⟩

/-- **The differential of a complex of cuts squares to zero**, when merging removes the cut and
merges along different cuts commute. -/
theorem d_d (hcs : ∀ x, ∀ k ∈ cs x, cs (mg k x) = (cs x).erase k)
    (hmg : ∀ x, ∀ k ∈ cs x, ∀ k' ∈ cs x, mg k (mg k' x) = mg k' (mg k x)) (v : X →₀ R) :
    d cs mg (d cs mg v) = 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, map_add, hv, hw, add_zero]
  | single x r =>
    rw [d_single, map_smul]
    convert smul_zero r
    rw [dX, map_sum]
    simp_rw [map_smul, d_single, one_smul, dX, Finset.smul_sum, smul_smul]
    refine (Finset.sum_congr rfl fun k hk => Finset.sum_congr (hcs x k hk) fun _ _ => by
      rw [hcs x k hk]).trans (sum_sum_erase_eq_zero _ _ fun k hk k' hk' hne => ?_)
    rw [hmg x k hk k' hk', ← add_smul, sgn_erase hk, sgn_erase hk']
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_pos h, if_neg (not_lt.2 h.le)]
      ring_nf
      exact zero_smul R _
    · rw [if_neg (not_lt.2 h.le), if_pos h]
      ring_nf
      exact zero_smul R _

/-! ## The leading part and its contracting homotopy -/

variable {M : Type*} (u : X → M) (L : M → Set N)

open Classical in
/-- **The leading part** on a basis element: merge only along the cuts outside `L`. -/
noncomputable def dLX (x : X) : X →₀ R :=
  ∑ k ∈ (cs x).filter (· ∉ L (u x)), sgn R (cs x) k • single (mg k x) 1

/-- **The leading part of the differential**: merge only along the cuts outside `L`. -/
noncomputable def dL : (X →₀ R) →ₗ[R] (X →₀ R) := linearCombination R (dLX cs mg u L)

lemma dL_single (x : X) (r : R) : dL cs mg u L (single x r) = r • dLX cs mg u L x :=
  linearCombination_single R r x

variable (ct : N → X → X) (k₀ : N)

open Classical in
/-- **The contracting homotopy** on a basis element: cut along `k₀`. -/
noncomputable def hX (x : X) : X →₀ R :=
  if k₀ ∈ cs x then 0 else sgn R (cs x) k₀ • single (ct k₀ x) 1

/-- **The contracting homotopy**: cut along `k₀`. -/
noncomputable def hL : (X →₀ R) →ₗ[R] (X →₀ R) := linearCombination R (hX cs ct k₀)

lemma hL_single (x : X) (r : R) : hL cs ct k₀ (single x r) = r • hX cs ct k₀ x :=
  linearCombination_single R r x

variable {cs mg u L ct k₀}

/-- **Cutting along `k₀ ∉ L` is a contracting homotopy** of the leading part, over a fibre. -/
theorem dL_hL_add {t : M} (hk₀ : k₀ ∉ L t)
    (hu_ct : ∀ x, u (ct k₀ x) = u x)
    (hcs : ∀ x, u x = t → ∀ k ∈ cs x, cs (mg k x) = (cs x).erase k)
    (hcs_ct : ∀ x, u x = t → k₀ ∉ cs x → cs (ct k₀ x) = insert k₀ (cs x))
    (hmg_ct : ∀ x, u x = t → k₀ ∉ cs x → mg k₀ (ct k₀ x) = x)
    (hct_mg : ∀ x, u x = t → k₀ ∈ cs x → ct k₀ (mg k₀ x) = x)
    (hcomm : ∀ x, u x = t → k₀ ∉ cs x → ∀ k ∈ cs x, mg k (ct k₀ x) = ct k₀ (mg k x))
    {x : X} (hx : u x = t) :
    dL cs mg u L (hL cs ct k₀ (single x (1 : R))) +
      hL cs ct k₀ (dL cs mg u L (single x (1 : R))) = single x 1 := by
  classical
  rw [hL_single, dL_single, one_smul, one_smul]
  by_cases h₀ : k₀ ∈ cs x
  · -- the cut `k₀` is present: only merging along it survives
    rw [hX, if_pos h₀, map_zero, zero_add, dLX, map_sum, hx]
    have hk₀' : k₀ ∈ (cs x).filter (· ∉ L t) := Finset.mem_filter.2 ⟨h₀, hk₀⟩
    rw [← Finset.add_sum_erase _ _ hk₀']
    have h1 : ∑ k ∈ ((cs x).filter (· ∉ L t)).erase k₀,
        hL cs ct k₀ (sgn R (cs x) k • single (mg k x) (1 : R)) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      obtain ⟨hne, hk⟩ := Finset.mem_erase.1 hk
      rw [map_smul, hL_single, one_smul, hX, if_pos, smul_zero]
      rw [hcs x hx k (Finset.mem_filter.1 hk).1]
      exact Finset.mem_erase.2 ⟨Ne.symm hne, h₀⟩
    rw [h1, add_zero, map_smul, hL_single, one_smul, hX, if_neg, hcs x hx k₀ h₀, sgn_erase_self,
      smul_smul, sgn_mul_self, one_smul, hct_mg x hx h₀]
    rw [hcs x hx k₀ h₀]
    exact Finset.notMem_erase k₀ _
  · -- the cut `k₀` is absent: cutting then merging along it is the identity, and the other
    -- terms cancel
    rw [hX, if_neg h₀, map_smul, dL_single, one_smul, dLX, hu_ct, hx, hcs_ct x hx h₀]
    have hF : (insert k₀ (cs x)).filter (· ∉ L t) = insert k₀ ((cs x).filter (· ∉ L t)) := by
      rw [Finset.filter_insert, if_pos hk₀]
    rw [hF, Finset.sum_insert (fun h => h₀ (Finset.mem_filter.1 h).1), hmg_ct x hx h₀,
      sgn_insert_self, smul_add, smul_smul, sgn_mul_self, one_smul, add_assoc, add_eq_left,
      dLX, hx, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkS := (Finset.mem_filter.1 hk).1
    have hne : k ≠ k₀ := fun h => h₀ (h ▸ hkS)
    rw [map_smul, hL_single, one_smul, hX, if_neg (by
        rw [hcs x hx k hkS]
        exact fun h => h₀ (Finset.mem_of_mem_erase h)),
      hcs x hx k hkS, hcomm x hx h₀ k hkS, smul_smul, smul_smul, ← add_smul, sgn_insert h₀,
      sgn_erase hkS]
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_neg (not_lt.2 h.le), if_pos h]
      ring_nf
      exact zero_smul R _
    · rw [if_pos h, if_neg (not_lt.2 h.le)]
      ring_nf
      exact zero_smul R _

end CutComplex

namespace Hoffbeck

open Finsupp

variable {M : Type*} (lt : M → M → Prop)

/-- **A step in the Dershowitz–Manna order on finite sets**: removing an element `t` and adding
elements smaller than it. -/
lemma isDershowitzMannaLT_of_subset [Preorder M] (hlt : ∀ a b : M, a < b ↔ lt a b)
    {F F' : Finset M} {t : M} (ht : t ∈ F) (htt : ¬ lt t t)
    (h : ∀ m ∈ F', (m ∈ F ∧ m ≠ t) ∨ lt m t) :
    Multiset.IsDershowitzMannaLT F'.val F.val := by
  classical
  have ht' : t ∉ F' := fun h' => by
    rcases h t h' with ⟨-, h⟩ | h
    · exact h rfl
    · exact htt h
  refine ⟨F'.val.filter (· ∈ F), F'.val.filter (· ∉ F), F.val.filter (· ∉ F'), ?_,
    (Multiset.filter_add_not _ _).symm, ?_, fun y hy => ?_⟩
  · intro h0
    have : t ∈ F.val.filter (· ∉ F') := Multiset.mem_filter.2 ⟨ht, ht'⟩
    rw [h0] at this
    exact Multiset.notMem_zero t this
  · conv_lhs => rw [← Multiset.filter_add_not (· ∈ F') F.val]
    congr 1
    refine (Multiset.Nodup.ext (Multiset.Nodup.filter _ F.nodup)
      (Multiset.Nodup.filter _ F'.nodup)).2 fun a => ?_
    simp only [Multiset.mem_filter, Finset.mem_val]
    exact and_comm
  · obtain ⟨hy₁, hy₂⟩ := Multiset.mem_filter.1 hy
    refine ⟨t, Multiset.mem_filter.2 ⟨ht, ht'⟩, (hlt _ _).2 ?_⟩
    rcases h y hy₁ with ⟨h, -⟩ | h
    · exact absurd h hy₂
    · exact h

variable {R : Type*} [CommRing R] {X : Type*} (u : X → M)

/-- The part of an element over the fibre of `t`. -/
lemma filter_mem_supported {s : Set X} {v : X →₀ R} (hv : v ∈ supported R R s) (p : X → Prop)
    [DecidablePred p] : v.filter p ∈ supported R R (s ∩ {x | p x}) := by
  rw [mem_supported] at hv ⊢
  intro x hx
  rw [Finset.mem_coe, support_filter, Finset.mem_filter] at hx
  exact ⟨hv hx.1, hx.2⟩

/-- A linear map whose values on the basis elements of a set lie in a submodule maps the
combinations of these elements into it. -/
lemma map_mem_of_supported {X' : Type*} {s : Set X} (f : (X →₀ R) →ₗ[R] (X' →₀ R))
    {P : Submodule R (X' →₀ R)} (h : ∀ x ∈ s, f (single x 1) ∈ P) {v : X →₀ R}
    (hv : v ∈ supported R R s) : f v ∈ P := by
  rw [← Submodule.mem_comap]
  refine (supported_eq_span_single R s ▸ hv : v ∈ Submodule.span R _) |> fun hv' => ?_
  refine Submodule.span_le.2 ?_ hv'
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

/-- **The leading part of a cycle**: the part over `t` of a cycle of `D` whose other part lies
over elements other than `t` and not above it is a cycle of the leading part `D₀`. -/
lemma leading_cycle (irr : ∀ a, ¬ lt a a) {V : Set X} (D D₀ : (X →₀ R) →ₗ[R] (X →₀ R))
    (hlead : ∀ x ∈ V,
      D (single x 1) - D₀ (single x 1) ∈ supported R R {y | lt (u y) (u x)})
    (hfib : ∀ x ∈ V, D₀ (single x 1) ∈ supported R R {y | u y = u x}) {t : M}
    {vt vr : X →₀ R} (hvt : vt ∈ supported R R (V ∩ u ⁻¹' {t}))
    (hvr : vr ∈ supported R R (V ∩ {x | u x ≠ t ∧ ¬ lt t (u x)})) (hDv : D (vt + vr) = 0) :
    D₀ vt = 0 := by
  have h1 : D vt - D₀ vt ∈ supported R R {y | lt (u y) t} := by
    refine map_mem_of_supported (D - D₀) (fun x hx => ?_) hvt
    rw [LinearMap.sub_apply]
    have := hlead x hx.1
    rwa [show u x = t from hx.2] at this
  have h2 : D vr ∈ supported R R {y | u y ≠ t} := by
    refine map_mem_of_supported D (fun x hx => ?_) hvr
    have s1 : {y | lt (u y) (u x)} ⊆ {y | u y ≠ t} := fun y hy heq => by
      rw [Set.mem_setOf_eq, heq] at hy
      exact hx.2.2 hy
    have s2 : {y | u y = u x} ⊆ {y | u y ≠ t} := fun y hy heq => by
      rw [Set.mem_setOf_eq, heq] at hy
      exact hx.2.1 hy.symm
    rw [← sub_add_cancel (D (single x 1)) (D₀ (single x 1))]
    exact Submodule.add_mem _ (supported_mono s1 (hlead x hx.1)) (supported_mono s2 (hfib x hx.1))
  have hA : D₀ vt ∈ supported R R {y | u y = t} := by
    refine map_mem_of_supported D₀ (fun x hx => ?_) hvt
    have := hfib x hx.1
    rwa [show u x = t from hx.2] at this
  have hsum : D vt + D vr = 0 := by rw [← map_add, hDv]
  have hB : D₀ vt ∈ supported R R {y | u y ≠ t} := by
    have : D₀ vt = -(D vt - D₀ vt) - D vr := by rw [neg_sub, sub_sub, hsum, sub_zero]
    have s3 : {y | lt (u y) t} ⊆ {y | u y ≠ t} := fun y hy heq => by
      rw [Set.mem_setOf_eq, heq] at hy
      exact irr t hy
    rw [this]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (supported_mono s3 h1)) h2
  have hdisj : Disjoint {y | u y = t} {y | u y ≠ t} := Set.disjoint_left.2 fun _ h h' => h' h
  exact Submodule.disjoint_def.1 (disjoint_supported_supported hdisj) _ hA hB

/-- **Hoffbeck's filtration argument.** Let `D` be a linear map on the free module on `X`, squaring
to zero from `V'` and mapping `V'` to `V`, and `D₀` its leading part: over the well-founded order
`lt` on `M`, through `u : X → M`, `D` and `D₀` differ on `V ∪ V'` by terms over strictly smaller
elements, and `D₀` preserves the fibres on `V`. If on every fibre every cycle of `D₀` in `V` is
the boundary of an element of `V'`, then every cycle of `D` in `V` is the boundary of an element
of `V'`. -/
theorem exact_of_leading (wf : WellFounded lt) (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    {V V' : Set X} (D D₀ : (X →₀ R) →ₗ[R] (X →₀ R))
    (hD : ∀ x ∈ V', D (single x 1) ∈ supported R R V)
    (hDD : ∀ w ∈ supported R R V', D (D w) = 0)
    (hlead : ∀ x ∈ V ∪ V',
      D (single x 1) - D₀ (single x 1) ∈ supported R R {y | lt (u y) (u x)})
    (hfib : ∀ x ∈ V, D₀ (single x 1) ∈ supported R R {y | u y = u x})
    (hexact : ∀ t, ∀ v ∈ supported R R (V ∩ u ⁻¹' {t}), D₀ v = 0 →
      ∃ w ∈ supported R R (V' ∩ u ⁻¹' {t}), D₀ w = v) :
    ∀ v ∈ supported R R V, D v = 0 → ∃ w ∈ supported R R V', D w = v := by
  classical
  have irr : ∀ a, ¬ lt a a := fun a => wf.irrefl.irrefl a
  letI : Preorder M :=
    { le := fun a b => a = b ∨ lt a b
      lt := lt
      le_refl := fun _ => Or.inl rfl
      le_trans := by
        rintro a b c (rfl | hab) (rfl | hbc)
        · exact Or.inl rfl
        · exact Or.inr hbc
        · exact Or.inr hab
        · exact Or.inr (trans hab hbc)
      lt_iff_le_not_ge := fun a b => by
        refine ⟨fun h => ⟨Or.inr h, ?_⟩, ?_⟩
        · rintro (rfl | h')
          · exact irr _ h
          · exact irr _ (trans h h')
        · rintro ⟨rfl | h, h'⟩
          · exact absurd (Or.inl rfl) h'
          · exact h }
  haveI : WellFoundedLT M := ⟨wf⟩
  suffices key : ∀ U : Multiset M, ∀ v ∈ supported R R V, (v.support.image u).val = U →
      D v = 0 → ∃ w ∈ supported R R V', D w = v from fun v hv h => key _ v hv rfl h
  intro U
  have hwf := Multiset.wellFounded_isDershowitzMannaLT (α := M)
  induction U using hwf.induction with
  | _ U ih =>
  intro v hv hU hDv
  by_cases hv0 : v = 0
  · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, hv0]⟩
  -- a maximal element `t` of the elements under the support
  set F := v.support.image u with hF
  obtain ⟨t, htF, htmax⟩ := Finset.exists_maximal
    (Finset.image_nonempty.2 (Finsupp.support_nonempty_iff.2 hv0) : F.Nonempty)
  have hmax : ∀ x ∈ v.support, ¬ lt t (u x) := fun x hx h => by
    rcases htmax (Finset.mem_image_of_mem u hx) (Or.inr h) with h' | h'
    · rw [h'] at h
      exact irr _ h
    · exact irr _ (trans h h')
  -- the part over `t` and the rest
  set vt := v.filter (fun x => u x = t) with hvt
  set vr := v.filter (fun x => ¬ u x = t) with hvr
  have hvsplit : vt + vr = v := filter_add_filter_not v _
  have hvt : vt ∈ supported R R (V ∩ u ⁻¹' {t}) := filter_mem_supported hv _
  have hvr : vr ∈ supported R R {x | x ∈ v.support ∧ u x ≠ t} := by
    rw [mem_supported]
    intro x hx
    rw [Finset.mem_coe, support_filter, Finset.mem_filter] at hx
    exact hx
  -- the part of `D v` over `t` is `D₀ vt`, so `D₀ vt = 0`
  have s : {x | x ∈ v.support ∧ u x ≠ t} ⊆ V ∩ {x | u x ≠ t ∧ ¬ lt t (u x)} :=
    fun x hx => ⟨(mem_supported R v).1 hv hx.1, hx.2, hmax x hx.1⟩
  have hvr' : vr ∈ supported R R (V ∩ {x | u x ≠ t ∧ ¬ lt t (u x)}) := supported_mono s hvr
  have hD₀vt : D₀ vt = 0 := by
    refine leading_cycle lt u irr D D₀ (fun x hx => hlead x (Or.inl hx)) hfib hvt hvr' ?_
    rw [hvsplit]
    exact hDv
  -- a primitive over `t`, and what remains lies over smaller elements
  obtain ⟨wt, hwt, hD₀wt⟩ := hexact t vt hvt hD₀vt
  have hwtV' : wt ∈ supported R R V' := supported_mono Set.inter_subset_left hwt
  have h3 : D wt - D₀ wt ∈ supported R R {y | lt (u y) t} := by
    refine map_mem_of_supported (D - D₀) (fun x hx => ?_) hwt
    rw [LinearMap.sub_apply]
    have := hlead x (Or.inr hx.1)
    rwa [show u x = t from hx.2] at this
  have hv'V : v - D wt ∈ supported R R V := Submodule.sub_mem _ hv (map_mem_of_supported D hD hwtV')
  have hDv' : D (v - D wt) = 0 := by rw [map_sub, hDv, hDD wt hwtV', sub_zero]
  have hv'eq : v - D wt = vr - (D wt - D₀ wt) := by
    rw [← hvsplit, hD₀wt, sub_sub_eq_add_sub, add_comm vt vr]
  have hsupp : ∀ x ∈ (v - D wt).support, (x ∈ v.support ∧ u x ≠ t) ∨ lt (u x) t := by
    intro x hx
    have : v - D wt ∈ supported R R ({x | x ∈ v.support ∧ u x ≠ t} ∪ {y | lt (u y) t}) := by
      rw [hv'eq]
      exact Submodule.sub_mem _ (supported_mono Set.subset_union_left hvr)
        (supported_mono Set.subset_union_right h3)
    exact (mem_supported R _).1 this hx
  have hDM : Multiset.IsDershowitzMannaLT ((v - D wt).support.image u).val U := by
    rw [← hU]
    refine isDershowitzMannaLT_of_subset lt (fun _ _ => Iff.rfl) htF (irr t) fun m hm => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hm
    rcases hsupp x hx with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨Finset.mem_image_of_mem u h1, h2⟩
    · exact Or.inr h
  obtain ⟨w', hw', hDw'⟩ := ih _ hDM (v - D wt) hv'V rfl hDv'
  exact ⟨w' + wt, Submodule.add_mem _ hw' hwtV', by rw [map_add, hDw', sub_add_cancel]⟩

/-- **Hoffbeck's filtration argument over a down-closed set**: when the leading part also
preserves the fibres on `V'`, every cycle of `D` in `V` lying over a down-closed set `Z` is the
boundary of an element of `V'` lying over `Z`. -/
theorem exact_of_leading_down (wf : WellFounded lt)
    (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    {V V' : Set X} (D D₀ : (X →₀ R) →ₗ[R] (X →₀ R))
    (hD : ∀ x ∈ V', D (single x 1) ∈ supported R R V)
    (hDD : ∀ w ∈ supported R R V', D (D w) = 0)
    (hlead : ∀ x ∈ V ∪ V',
      D (single x 1) - D₀ (single x 1) ∈ supported R R {y | lt (u y) (u x)})
    (hfib : ∀ x ∈ V ∪ V', D₀ (single x 1) ∈ supported R R {y | u y = u x})
    (hexact : ∀ t, ∀ v ∈ supported R R (V ∩ u ⁻¹' {t}), D₀ v = 0 →
      ∃ w ∈ supported R R (V' ∩ u ⁻¹' {t}), D₀ w = v)
    {Z : Set M} (hZ : ∀ m ∈ Z, ∀ m', lt m' m → m' ∈ Z) :
    ∀ v ∈ supported R R (V ∩ u ⁻¹' Z), D v = 0 →
      ∃ w ∈ supported R R (V' ∩ u ⁻¹' Z), D w = v := by
  refine exact_of_leading lt u wf trans D D₀ (fun x hx => ?_)
    (fun w hw => hDD w (supported_mono Set.inter_subset_left hw)) (fun x hx => hlead x ?_)
    (fun x hx => hfib x (Or.inl hx.1)) (fun t v hv hv0 => ?_)
  · rw [supported_inter]
    refine ⟨hD x hx.1, ?_⟩
    rw [← sub_add_cancel (D (single x 1)) (D₀ (single x 1))]
    have s1 : {y | lt (u y) (u x)} ⊆ u ⁻¹' Z := fun y hy => hZ _ hx.2 _ hy
    have s2 : {y | u y = u x} ⊆ u ⁻¹' Z := fun y hy => by
      rw [Set.mem_preimage, show u y = u x from hy]
      exact hx.2
    exact Submodule.add_mem _ (supported_mono s1 (hlead x (Or.inr hx.1)))
      (supported_mono s2 (hfib x (Or.inr hx.1)))
  · rcases hx with h | h
    exacts [Or.inl h.1, Or.inr h.1]
  · by_cases ht : t ∈ Z
    · have s : V ∩ u ⁻¹' Z ∩ u ⁻¹' {t} ⊆ V ∩ u ⁻¹' {t} :=
        Set.inter_subset_inter_left _ Set.inter_subset_left
      obtain ⟨w, hw, hDw⟩ := hexact t v (supported_mono s hv) hv0
      have s' : V' ∩ u ⁻¹' {t} ⊆ V' ∩ u ⁻¹' Z ∩ u ⁻¹' {t} := fun x hx => by
        refine ⟨⟨hx.1, ?_⟩, hx.2⟩
        rw [Set.mem_preimage, Set.mem_singleton_iff.1 hx.2]
        exact ht
      exact ⟨w, supported_mono s' hw, hDw⟩
    · have hv' : v = 0 := by
        rw [← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
        intro x hx
        obtain ⟨⟨-, hxZ⟩, hxt⟩ := (mem_supported R v).1 hv hx
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hxt
        rw [Set.mem_preimage, hxt] at hxZ
        exact ht hxZ
      exact ⟨0, Submodule.zero_mem _, by rw [map_zero, hv']⟩

/-! ## Triangular families -/

/-- **A finite set has a maximal element** for a strict order, through any map. -/
lemma exists_max (irr : ∀ a, ¬ lt a a) (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    {ι : Type*} (f : ι → M) {s : Finset ι} (hs : s.Nonempty) :
    ∃ i ∈ s, ∀ j ∈ s, ¬ lt (f i) (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · refine ⟨a, Finset.mem_insert_self a ∅, fun j hj h => ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact irr _ h
      · exact absurd hj (Finset.notMem_empty _)
    · obtain ⟨i, hi, hmax⟩ := ih hs'
      by_cases hia : lt (f i) (f a)
      · refine ⟨a, Finset.mem_insert_self a s, fun j hj h => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact irr _ h
        · exact hmax j hj (trans hia h)
      · refine ⟨i, Finset.mem_insert_of_mem hi, fun j hj h => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hia h
        · exact hmax j hj h

/-- The coefficient of `x` in an element equal to `x` up to terms over elements strictly smaller
than `u x` is `1`. -/
lemma apply_self_of_triangular (irr : ∀ a, ¬ lt a a) {x : X} {f : X →₀ R}
    (hf : f - single x 1 ∈ supported R R {y | lt (u y) (u x)}) : f x = 1 := by
  have h : (f - single x 1 : X →₀ R) x = 0 := by
    by_contra h
    exact irr _ ((mem_supported R _).1 hf (Finsupp.mem_support_iff.2 h))
  rwa [Finsupp.sub_apply, Finsupp.single_eq_same, sub_eq_zero] at h

/-- **A triangular family is linearly independent**: a family of elements each equal to a basis
element `e i`, for an injective `e`, up to terms over elements strictly smaller than `u (e i)`. -/
theorem linearIndependent_of_triangular (irr : ∀ a, ¬ lt a a)
    (trans : ∀ {a b c}, lt a b → lt b c → lt a c) {ι : Type*} {e : ι → X}
    (he : Function.Injective e) {f : ι → X →₀ R}
    (hf : ∀ i, f i - single (e i) 1 ∈ supported R R {y | lt (u y) (u (e i))}) :
    LinearIndependent R f := by
  classical
  have hcoef : ∀ i j, i ≠ j → f j (e i) ≠ 0 → lt (u (e i)) (u (e j)) := by
    intro i j hij h
    have h1 : (f j - single (e j) 1 : X →₀ R) (e i) ≠ 0 := by
      rwa [Finsupp.sub_apply, Finsupp.single_eq_of_ne (he.ne hij), sub_zero]
    exact (mem_supported R _).1 (hf j) (Finsupp.mem_support_iff.2 h1)
  rw [linearIndependent_iff']
  intro s g hg i₀ hi₀
  by_contra hne
  obtain ⟨i, hi, hmax⟩ := exists_max lt irr trans (fun i => u (e i))
    (s := s.filter (g · ≠ 0)) ⟨i₀, Finset.mem_filter.2 ⟨hi₀, hne⟩⟩
  obtain ⟨his, hgi⟩ := Finset.mem_filter.1 hi
  have h := congrArg (fun v => v (e i)) hg
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i (fun j hj hji => ?_) (fun h => absurd his h),
    apply_self_of_triangular lt u irr (hf i), mul_one] at h
  · exact hgi h
  · by_contra hj'
    have hgj : g j ≠ 0 := left_ne_zero_of_mul hj'
    exact hmax j (Finset.mem_filter.2 ⟨hj, hgj⟩)
      (hcoef i j (Ne.symm hji) (right_ne_zero_of_mul hj'))

/-- **A triangular family spans**: if the maximal elements of the support of every element of a
submodule `S` are among the basis elements `e i`, and each `f i ∈ S` is equal to `e i` up to terms
over elements strictly smaller than `u (e i)`, the family `f` spans `S`. -/
theorem span_of_triangular (wf : WellFounded lt) (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    {ι : Type*} {e : ι → X} {f : ι → X →₀ R} {S : Submodule R (X →₀ R)} (hfS : ∀ i, f i ∈ S)
    (hf : ∀ i, f i - single (e i) 1 ∈ supported R R {y | lt (u y) (u (e i))})
    (hmax : ∀ v ∈ S, ∀ x ∈ v.support, (∀ y ∈ v.support, ¬ lt (u x) (u y)) → x ∈ Set.range e) :
    S ≤ Submodule.span R (Set.range f) := by
  classical
  have irr : ∀ a, ¬ lt a a := fun a => wf.irrefl.irrefl a
  letI : Preorder X :=
    { le := fun a b => a = b ∨ lt (u a) (u b)
      lt := fun a b => lt (u a) (u b)
      le_refl := fun _ => Or.inl rfl
      le_trans := by
        rintro a b c (rfl | hab) (rfl | hbc)
        · exact Or.inl rfl
        · exact Or.inr hbc
        · exact Or.inr hab
        · exact Or.inr (trans hab hbc)
      lt_iff_le_not_ge := fun a b => by
        refine ⟨fun h => ⟨Or.inr h, ?_⟩, ?_⟩
        · rintro (rfl | h')
          · exact irr _ h
          · exact irr _ (trans h h')
        · rintro ⟨rfl | h, h'⟩
          · exact absurd (Or.inl rfl) h'
          · exact h }
  haveI : WellFoundedLT X := ⟨InvImage.wf u wf⟩
  suffices key : ∀ U : Multiset X, ∀ v ∈ S, v.support.val = U →
      v ∈ Submodule.span R (Set.range f) from fun v hv => key _ v hv rfl
  intro U
  have hwf := Multiset.wellFounded_isDershowitzMannaLT (α := X)
  induction U using hwf.induction with
  | _ U ih =>
  intro v hv hU
  by_cases hv0 : v = 0
  · rw [hv0]
    exact Submodule.zero_mem _
  obtain ⟨x, hx, hxmax⟩ := exists_max lt irr trans u (Finsupp.support_nonempty_iff.2 hv0)
  obtain ⟨i, rfl⟩ := hmax v hv x hx hxmax
  have hdiag := apply_self_of_triangular lt u irr (hf i)
  set v' := v - v (e i) • f i with hv'
  have hv'S : v' ∈ S := S.sub_mem hv (S.smul_mem _ (hfS i))
  have hsupp : ∀ y ∈ v'.support, (y ∈ v.support ∧ y ≠ e i) ∨ lt (u y) (u (e i)) := by
    intro y hy
    rw [Finsupp.mem_support_iff, hv', Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] at hy
    have hyi : y ≠ e i := by
      rintro rfl
      rw [hdiag, mul_one, sub_self] at hy
      exact hy rfl
    by_cases hvy : v y = 0
    · right
      have h1 : (f i - single (e i) 1 : X →₀ R) y ≠ 0 := by
        rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hyi, sub_zero]
        intro h
        rw [hvy, h, mul_zero, sub_zero] at hy
        exact hy rfl
      exact (mem_supported R _).1 (hf i) (Finsupp.mem_support_iff.2 h1)
    · exact Or.inl ⟨Finsupp.mem_support_iff.2 hvy, hyi⟩
  have hDM : Multiset.IsDershowitzMannaLT v'.support.val U := by
    rw [← hU]
    exact isDershowitzMannaLT_of_subset (fun a b => lt (u a) (u b)) (fun _ _ => Iff.rfl) hx
      (irr _) hsupp
  have e1 : v = v' + v (e i) • f i := by rw [hv', sub_add_cancel]
  rw [e1]
  exact Submodule.add_mem _ (ih _ hDM v' hv'S rfl)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

end Hoffbeck

end Operad
