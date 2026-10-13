/-
# Syzygies of a quadratic Gröbner basis are generated in arity four

Let `R` be relators of arity three forming a quadratic Gröbner basis of a shuffle operad, and let
`D` be a linear map on the relators with values in the free operad, a cochain on the relators. The
*syzygies* of arity `n` are the combinations of relators placed at edges of monomials of arity
`n` which vanish in the free operad; `D` *kills* them when the same combination, with each relator
replaced by its image under `D`, lies in the ideal (`LTree.KillsSyz`). This is what is needed for
`D` to extend to the ideal compatibly with the operad structure: an extension `c` with `c(x) = D(x)`
on the relators placed at edges is then well defined.

* **Theorem** (`LTree.killsSyz_of_four`): if `D` kills the syzygies of arity four, it kills those
  of every arity; so it extends to the ideal in every arity (`LTree.exists_idealExt`), uniquely
  (`LTree.idealExt_unique`).

The proof is Schreyer's argument for Gröbner bases, in the form of a reduction of the syzygies to
the pairs of leading terms (`Operad.schreyer`). Every relator is a combination of the normalized
relators led by the leading monomials (`LTree.lrel`), and every placement of one of them is a
*leading placement*: its relator placed at a *leading position*, an edge whose window is leading
(`LTree.LPos`), with leading monomial that of the position. Two leading placements at the same
monomial `M` agree modulo placements with smaller leading monomials and the ideal
(`LTree.spair`): when the two edges share a vertex, they span a subtree of three vertices, a
context of arity four in which the difference reduces to placements of lower leading monomials
by the Gröbner basis of arity four, the hypothesis on `D` taking care of that syzygy of arity four
(`LTree.spair_ctx4`); otherwise the two substitutions commute (`LTree.spair_comm`), the Koszul
syzygies, which `D` kills in any case.
-/
import Operad.ShuffleContext

namespace Operad

/-! ## An abstract Schreyer argument -/

section Abstract

variable {K : Type*} [Field K] {X : Type*} [Fintype X] [DecidableEq X] {W : Type*}
  [AddCommGroup W] [Module K W] {ι : Type*}

omit [Fintype X] [DecidableEq X] in
open Submodule in
/-- **The vectors supported strictly below a level**: the first components of the span of
generators of lower levels, and of `Q`, vanish from that level on. -/
lemma fst_eq_zero_of_mem_span {β : Type*} [LinearOrder β] (key : X → β)
    (Q : Submodule K ((X → K) × W)) (hQ : ∀ v ∈ Q, v.1 = 0) (g : ι → (X → K) × W)
    (lvl : ι → X) (hlow : ∀ i y, (g i).1 y ≠ 0 → y ≠ lvl i → key y < key (lvl i)) (b : β)
    {v : (X → K) × W} (hv : v ∈ span K (g '' {k | key (lvl k) < b}) ⊔ Q) {y : X}
    (hy : b ≤ key y) : v.1 y = 0 := by
  obtain ⟨a, ha, c, hc, rfl⟩ := mem_sup.1 hv
  clear hv
  simp only [Prod.fst_add, Pi.add_apply, hQ c hc, Pi.zero_apply, add_zero]
  induction ha using span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    by_contra h
    by_cases hyk : y = lvl k
    · subst hyk
      exact absurd hk (not_lt.2 hy)
    · exact absurd ((hlow k y h hyk).trans hk) (not_lt.2 hy)
  | zero => rfl
  | add x z _ _ hx hz => simp [hx, hz]
  | smul r x _ hx => simp [hx]

open Submodule in
/-- **An abstract Schreyer argument.** Let `g i` be pairs of vectors on a finite set of monomials
and of elements of `W`, the first component of `g i` having the coefficient `1` at a monomial
`lvl i` and otherwise only monomials of smaller keys. Suppose that two generators at the same
monomial agree modulo generators at monomials of smaller keys and modulo a space `Q` of pairs with
vanishing first component. Then every combination of the generators and of `Q` with vanishing
first component lies in `Q`. -/
theorem schreyer {β : Type*} [LinearOrder β] (key : X → β) (Q : Submodule K ((X → K) × W))
    (hQ : ∀ v ∈ Q, v.1 = 0) (g : ι → (X → K) × W) (lvl : ι → X)
    (hone : ∀ i, (g i).1 (lvl i) = 1)
    (hlow : ∀ i y, (g i).1 y ≠ 0 → y ≠ lvl i → key y < key (lvl i))
    (hS : ∀ i j, lvl i = lvl j →
      g i - g j ∈ span K (g '' {k | key (lvl k) < key (lvl i)}) ⊔ Q) :
    ∀ v ∈ span K (Set.range g) ⊔ Q, v.1 = 0 → v ∈ Q := by
  classical
  -- the generators below a bound, in `WithTop β`
  let S : WithTop β → Submodule K ((X → K) × W) := fun b =>
    span K (g '' {k | (key (lvl k) : WithTop β) < b}) ⊔ Q
  have hcoe : ∀ b : β, S b = span K (g '' {k | key (lvl k) < b}) ⊔ Q := fun b => by
    simp only [S, WithTop.coe_lt_coe]
  suffices h : ∀ N : ℕ, ∀ b : WithTop β,
      (Finset.univ.filter fun x => (key x : WithTop β) < b).card ≤ N →
      ∀ v ∈ S b, v.1 = 0 → v ∈ Q by
    intro v hv h0
    refine h _ ⊤ le_rfl v ?_ h0
    simpa [S] using hv
  intro N
  induction N with
  | zero =>
    intro b hb v hv _
    have hempty : {k | (key (lvl k) : WithTop β) < b} = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hk
      have hmem : lvl k ∈ Finset.univ.filter fun x => (key x : WithTop β) < b := by simp [hk]
      have := Finset.card_pos.2 ⟨lvl k, hmem⟩
      omega
    simpa [S, hempty] using hv
  | succ N ih =>
    intro b hb v hv h0
    set F := Finset.univ.filter fun x => (key x : WithTop β) < b with hF
    by_cases hFe : F = ∅
    · have hempty : {k | (key (lvl k) : WithTop β) < b} = ∅ := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hk
        have : lvl k ∈ F := by simp [hF, hk]
        rw [hFe] at this
        simp at this
      simpa [S, hempty] using hv
    -- the largest key below `b`
    have hFne : (F.image key).Nonempty := (Finset.nonempty_iff_ne_empty.2 hFe).image key
    set κ := (F.image key).max' hFne with hκ
    obtain ⟨x₀, hx₀F, hx₀κ⟩ : ∃ x ∈ F, key x = κ :=
      Finset.mem_image.1 ((F.image key).max'_mem hFne)
    have hκb : (κ : WithTop β) < b := by
      rw [← hx₀κ]
      simpa [hF] using hx₀F
    have hle : ∀ x, (key x : WithTop β) < b → key x ≤ κ := fun x hx =>
      (F.image key).le_max' _ (Finset.mem_image.2 ⟨x, by simp [hF, hx], rfl⟩)
    -- below `κ` there are fewer monomials
    have hcard : (Finset.univ.filter fun x => (key x : WithTop β) < (κ : WithTop β)).card ≤ N := by
      have hsub : (Finset.univ.filter fun x => (key x : WithTop β) < (κ : WithTop β)) ⊂ F := by
        refine ⟨fun x hx => ?_, fun hsub => ?_⟩
        · have hx' : (key x : WithTop β) < κ := by simpa using hx
          simpa [hF] using hx'.trans hκb
        · have := hsub hx₀F
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx₀κ] at this
          exact lt_irrefl _ this
      have := Finset.card_lt_card hsub
      omega
    -- the monomials of key `κ` reached by generators, with a chosen generator each
    let T := {x : X // key x = κ ∧ ∃ i, lvl i = x}
    let c : T → ι := fun x => Classical.choose x.2.2
    have hc : ∀ x : T, lvl (c x) = x.1 := fun x => Classical.choose_spec x.2.2
    -- every generator below `b` is in `S κ` plus the span of the chosen ones
    have hstep : S b ≤ S κ ⊔ span K (Set.range (g ∘ c)) := by
      refine sup_le (span_le.2 ?_) (le_sup_of_le_left le_sup_right)
      rintro _ ⟨k, hk, rfl⟩
      rcases (hle _ hk).lt_or_eq with hlt | heq
      · exact mem_sup_left (mem_sup_left (subset_span ⟨k, by simpa using hlt, rfl⟩))
      · let x : T := ⟨lvl k, heq, k, rfl⟩
        have hd := hS k (c x) (hc x).symm
        rw [heq, ← hcoe] at hd
        have : g k = (g k - g (c x)) + g (c x) := by abel
        rw [this]
        exact add_mem (mem_sup_left hd) (mem_sup_right (subset_span ⟨x, rfl⟩))
    obtain ⟨s, hs, w, hw, rfl⟩ := mem_sup.1 (hstep hv)
    obtain ⟨a, rfl⟩ := (mem_span_range_iff_exists_fun K).1 hw
    -- the coefficients of the chosen generators vanish
    have hs0 : ∀ y : X, κ ≤ key y → s.1 y = 0 := fun y hy => by
      rw [hcoe] at hs
      exact fst_eq_zero_of_mem_span key Q hQ g lvl hlow κ hs hy
    have ha : ∀ x, a x = 0 := by
      intro x
      have hx := congrFun h0 x.1
      simp only [Prod.fst_add, Pi.add_apply, Pi.zero_apply, Prod.fst_sum, Finset.sum_apply,
        Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Function.comp] at hx
      rw [hs0 x.1 x.2.1.ge, zero_add, Finset.sum_eq_single x] at hx
      · rw [← hc x, hone, mul_one] at hx
        exact hx
      · intro x' _ hx'
        by_contra hne
        have hne' := right_ne_zero_of_mul hne
        have hxl : x.1 ≠ lvl (c x') := by
          rw [hc x']
          exact fun h => hx' (Subtype.ext h).symm
        have := hlow (c x') x.1 hne' hxl
        rw [hc x', x.2.1, x'.2.1] at this
        exact lt_irrefl _ this
      · simp
    simp only [ha, zero_smul, Finset.sum_const_zero, add_zero]
    exact ih κ hcard s hs (by simpa [ha] using h0)

open Submodule in
/-- **Standard representations**: if the first components of the generators lie in `I`, and every
leading monomial of a vector of `I` is the monomial of a generator, then every vector of `I`
whose monomials have keys below `b` is the first component of a combination of generators of
keys below `b`. -/
theorem exists_mem_span_fst [LinearOrder X] {β : Type*} [LinearOrder β] (key : X → β)
    (hkey : Monotone key) (I : Submodule K (X → K)) (g : ι → (X → K) × W) (lvl : ι → X)
    (hmem : ∀ i, (g i).1 ∈ I) (hone : ∀ i, (g i).1 (lvl i) = 1)
    (hlow : ∀ i y, (g i).1 y ≠ 0 → y ≠ lvl i → key y < key (lvl i))
    (hlead : ∀ v ∈ I, ∀ x, IsLeadingOf v x → ∃ i, lvl i = x) (b : β) :
    ∀ v ∈ I, (∀ y, v y ≠ 0 → key y < b) →
      ∃ γ ∈ span K (g '' {k | key (lvl k) < b}), γ.1 = v := by
  classical
  suffices h : ∀ (c : WithTop X) (v : X → K), v ∈ I → (∀ y, v y ≠ 0 → (y : WithTop X) < c) →
      (∀ y, v y ≠ 0 → key y < b) → ∃ γ ∈ span K (g '' {k | key (lvl k) < b}), γ.1 = v from
    fun v hv hb => h ⊤ v hv (fun _ _ => WithTop.coe_lt_top _) hb
  intro c
  induction c using WellFoundedLT.induction with
  | _ c ih =>
  intro v hv hc hb
  by_cases h0 : ∀ y, v y = 0
  · exact ⟨0, zero_mem _, by funext y; simp [h0 y]⟩
  push Not at h0
  set D := Finset.univ.filter fun y => v y ≠ 0 with hD
  have hDne : D.Nonempty := by
    obtain ⟨y, hy⟩ := h0
    exact ⟨y, by simp [hD, hy]⟩
  set x := D.max' hDne with hx
  have hxD : v x ≠ 0 := by simpa [hD] using D.max'_mem hDne
  have hxmax : ∀ y, x < y → v y = 0 := fun y hy => by
    by_contra h
    exact absurd (D.le_max' y (by simp [hD, h])) (not_le.2 hy)
  obtain ⟨i, hi⟩ := hlead v hv x ⟨hxD, hxmax⟩
  set v' := v - v x • (g i).1 with hv'
  have hgi : ∀ y, (g i).1 y ≠ 0 → y ≠ x → y < x := fun y hy hyx => by
    have := hlow i y hy (by rw [hi]; exact hyx)
    rw [hi] at this
    by_contra h
    exact absurd (hkey (not_lt.1 h)) (not_le.2 this)
  have hv'lt : ∀ y, v' y ≠ 0 → y < x := by
    intro y hy
    by_contra h
    rcases (not_lt.1 h).lt_or_eq with h | h
    · have h1 := hxmax y h
      have h2 : (g i).1 y = 0 := by
        by_contra h2
        exact absurd (hgi y h2 (ne_of_gt h)) (not_lt.2 h.le)
      exact hy (by simp [hv', h1, h2])
    · subst h
      exact hy (by simp [hv', ← hi, hone])
  have hv'b : ∀ y, v' y ≠ 0 → key y < b := by
    intro y hy
    have hxb : key x < b := hb x hxD
    by_cases hvy : v y = 0
    · have h2 : (g i).1 y ≠ 0 := fun h2 => hy (by simp [hv', hvy, h2])
      by_cases hyx : y = x
      · rw [hyx]
        exact hxb
      · have := hlow i y h2 (by rw [hi]; exact hyx)
        rw [hi] at this
        exact this.trans hxb
    · exact hb y hvy
  obtain ⟨γ', hγ', hγ'v⟩ := ih x (hc x hxD) v' (I.sub_mem hv (I.smul_mem _ (hmem i)))
    (fun y hy => WithTop.coe_lt_coe.2 (hv'lt y hy)) hv'b
  refine ⟨γ' + v x • g i, add_mem hγ' (smul_mem _ _ (subset_span ⟨i, ?_, rfl⟩)), ?_⟩
  · show key (lvl i) < b
    rw [hi]
    exact hb x hxD
  · simp [hγ'v, hv']

open Submodule in
/-- **Standard representations**, without a bound on the keys. -/
theorem exists_mem_span_fst_top [LinearOrder X] {β : Type*} [LinearOrder β] (key : X → β)
    (hkey : Monotone key) (I : Submodule K (X → K)) (g : ι → (X → K) × W) (lvl : ι → X)
    (hmem : ∀ i, (g i).1 ∈ I) (hone : ∀ i, (g i).1 (lvl i) = 1)
    (hlow : ∀ i y, (g i).1 y ≠ 0 → y ≠ lvl i → key y < key (lvl i))
    (hlead : ∀ v ∈ I, ∀ x, IsLeadingOf v x → ∃ i, lvl i = x) :
    ∀ v ∈ I, ∃ γ ∈ span K (Set.range g), γ.1 = v := by
  intro v hv
  obtain ⟨γ, hγ, hγv⟩ := exists_mem_span_fst (fun x => (key x : WithTop β))
    (fun x y h => WithTop.coe_le_coe.2 (hkey h)) I g lvl hmem hone
    (fun i y h h' => WithTop.coe_lt_coe.2 (hlow i y h h')) hlead ⊤ v hv
    (fun _ _ => WithTop.coe_lt_top _)
  exact ⟨γ, span_mono (Set.image_subset_range _ _) hγ, hγv⟩

end Abstract

/-! ## Placements of relators -/

namespace LTree

section Placements

variable (K : Type*) [Field K] {E : Type*} [Fintype E] [DecidableEq E]

/-- **Substitution of relators at an edge**, as a linear map. -/
noncomputable def substVecL (n : ℕ) (t : LTree E) (p : List Bool) (s : Bool) :
    (Mono E 3 → K) →ₗ[K] (Mono E n → K) where
  toFun := substVec K n t p s
  map_add' r r' := by simp [substVec, add_smul, Finset.sum_add_distrib]
  map_smul' c r := by simp [substVec, Finset.smul_sum, smul_smul]

@[simp] lemma substVecL_apply (n : ℕ) (t : LTree E) (p : List Bool) (s : Bool)
    (r : Mono E 3 → K) : substVecL K n t p s r = substVec K n t p s r := rfl

variable {K} {R : Submodule K (Mono E 3 → K)} (D : R →ₗ[K] (Mono E 3 → K))

/-- **A relator placed at an edge**, with its image under `D` placed there. -/
noncomputable def pairOf (n : ℕ) (t : LTree E) (p : List Bool) (s : Bool) (r : R) :
    (Mono E n → K) × (Mono E n → K) :=
  (substVec K n t p s r, substVec K n t p s (D r))

/-- The placement at an edge, as a linear map on the relators. -/
noncomputable def pairOfL (n : ℕ) (t : LTree E) (p : List Bool) (s : Bool) :
    R →ₗ[K] (Mono E n → K) × (Mono E n → K) :=
  (substVecL K n t p s ∘ₗ R.subtype).prod (substVecL K n t p s ∘ₗ D)

@[simp] lemma pairOfL_apply (n : ℕ) (t : LTree E) (p : List Bool) (s : Bool) (r : R) :
    pairOfL D n t p s r = pairOf D n t p s r := rfl

/-- **The placements of arity `n`**: the span of the relators placed at the edges of the
monomials, each with its image under `D` placed at the same edge. -/
noncomputable def syzSpan (n : ℕ) : Submodule K ((Mono E n → K) × (Mono E n → K)) :=
  Submodule.span K {x | ∃ (t : Mono E n) (p : List Bool) (s : Bool), t.1.IsEdge p s ∧
    ∃ r : R, x = pairOf D n t.1 p s r}

/-- **`D` kills the syzygies of arity `n`**: whenever a combination of relators placed at edges of
monomials of arity `n` vanishes, the same combination of their images under `D` lies in the
ideal. -/
def KillsSyz (n : ℕ) : Prop :=
  ∀ w : Mono E n → K, ((0 : Mono E n → K), w) ∈ syzSpan D n → w ∈ idealOf K R n

/-- The pairs with vanishing first component and second component in the ideal. -/
abbrev idealPairs (R : Submodule K (Mono E 3 → K)) (n : ℕ) :
    Submodule K ((Mono E n → K) × (Mono E n → K)) :=
  (⊥ : Submodule K (Mono E n → K)).prod (idealOf K R n)

lemma fst_eq_zero_of_mem_idealPairs {n : ℕ} {v : (Mono E n → K) × (Mono E n → K)}
    (hv : v ∈ idealPairs R n) : v.1 = 0 :=
  (Submodule.mem_bot K).1 (Submodule.mem_prod.1 hv).1

end Placements

/-! ## Leading placements -/

section Leading

variable {K : Type*} [Field K] {E : Type*} [Fintype E] [DecidableEq E] {rk : E → ℕ}
  {L : Set (LTree E)} {R : Submodule K (Mono E 3 → K)} (D : R →ₗ[K] (Mono E 3 → K))

open Classical in
/-- **The normalized relator led by** a leading monomial `ℓ`: its coefficient at `ℓ` is `1`, and
the other monomials of its support have smaller keys. -/
noncomputable def lrel (hG : IsGroebner K rk L R) (ℓ : LTree E) : R :=
  if h : ℓ ∈ L then
    ((Classical.choose (hG.lead ℓ h)) ⟨ℓ, hG.mem ℓ h⟩)⁻¹ •
      ⟨Classical.choose (hG.lead ℓ h), (Classical.choose_spec (hG.lead ℓ h)).1⟩
  else 0

variable (hG : IsGroebner K rk L R)

lemma lrel_self {ℓ : LTree E} (h : ℓ ∈ L) : (lrel hG ℓ : Mono E 3 → K) ⟨ℓ, hG.mem ℓ h⟩ = 1 := by
  have hs := Classical.choose_spec (hG.lead ℓ h)
  simp only [lrel, dif_pos h, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact inv_mul_cancel₀ hs.2.1

lemma lrel_lt {ℓ : LTree E} (h : ℓ ∈ L) {σ : Mono E 3} (hσ : σ.1 ≠ ℓ)
    (hr : (lrel hG ℓ : Mono E 3 → K) σ ≠ 0) : pathKey rk 3 σ.1 < pathKey rk 3 ℓ := by
  have hs := Classical.choose_spec (hG.lead ℓ h)
  simp only [lrel, dif_pos h, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at hr
  exact hs.2.2 σ hσ (right_ne_zero_of_mul hr)

/-- Substituting at a leading window another monomial of its relator lowers the key. -/
lemma pathKey_substAt_lrel {n : ℕ} {t : LTree E} (ht : t ∈ monomials n) {p : List Bool}
    {s : Bool} (he : t.IsEdge p s) (hl : t.windowAt p s ∈ L) {σ : Mono E 3}
    (hσ : σ.1 ≠ t.windowAt p s) (hr : (lrel hG (t.windowAt p s) : Mono E 3 → K) σ ≠ 0) :
    pathKey rk n (t.substAt p s σ.1) < pathKey rk n t := by
  have hm := (mem_monomials n t).1 ht
  have hself := substAt_windowAt he hm.1 (hm.2.nodup_iff.2 List.nodup_range)
  have := pathKey_substAt_lt' rk ht he σ.2 (hG.mem _ hl) (lrel_lt hG hl hσ hr)
  rwa [hself] at this

/-- **The relator led by a window, placed there**, has coefficient `1` at the monomial. -/
lemma substVec_lrel_self {n : ℕ} (t : Mono E n) {p : List Bool} {s : Bool} (he : t.1.IsEdge p s)
    (hl : t.1.windowAt p s ∈ L) : substVec K n t.1 p s (lrel hG (t.1.windowAt p s)) t = 1 := by
  classical
  have hm := (mem_monomials n t.1).1 t.2
  have hself := substAt_windowAt he hm.1 (hm.2.nodup_iff.2 List.nodup_range)
  simp only [substVec, Finset.sum_apply, Pi.smul_apply, vecOf, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_eq_single ⟨_, hG.mem _ hl⟩ (fun σ _ hσ => ?_) (by simp)]
  · rw [if_pos hself.symm]
    exact lrel_self hG hl
  · by_cases hr : (lrel hG (t.1.windowAt p s) : Mono E 3 → K) σ = 0
    · simp [hr]
    · rw [if_neg]
      intro h
      have := pathKey_substAt_lrel hG t.2 he hl (fun h' => hσ (Subtype.ext h')) hr
      rw [← h] at this
      exact lt_irrefl _ this

/-- **The other monomials of the placed relator have smaller keys.** -/
lemma substVec_lrel_low {n : ℕ} (t : Mono E n) {p : List Bool} {s : Bool} (he : t.1.IsEdge p s)
    (hl : t.1.windowAt p s ∈ L) {y : Mono E n}
    (hy : substVec K n t.1 p s (lrel hG (t.1.windowAt p s)) y ≠ 0) (hyt : y ≠ t) :
    pathKey rk n y.1 < pathKey rk n t.1 := by
  classical
  have hm := (mem_monomials n t.1).1 t.2
  have hself := substAt_windowAt he hm.1 (hm.2.nodup_iff.2 List.nodup_range)
  simp only [substVec, Finset.sum_apply, Pi.smul_apply, vecOf, smul_eq_mul, mul_ite, mul_one,
    mul_zero] at hy
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  split_ifs at hσ with h
  · have hσw : σ.1 ≠ t.1.windowAt p s := fun h' => hyt (Subtype.ext (by rw [h, h', hself]))
    rw [h]
    exact pathKey_substAt_lrel hG t.2 he hl hσw hσ
  · exact absurd rfl hσ

/-- **A leading position** in arity `n`: a monomial with an edge whose window is leading. -/
structure LPos (L : Set (LTree E)) (n : ℕ) where
  /-- The monomial. -/
  mono : Mono E n
  /-- The path to the upper vertex of the edge. -/
  path : List Bool
  /-- The slot of the lower vertex. -/
  side : Bool
  edge : mono.1.IsEdge path side
  lead : mono.1.windowAt path side ∈ L

/-- **The leading placement** at a leading position: the relator led by the window, placed
there, with its image under `D`. -/
noncomputable def lpair {n : ℕ} (i : LPos L n) : (Mono E n → K) × (Mono E n → K) :=
  pairOf D n i.mono.1 i.path i.side (lrel hG (i.mono.1.windowAt i.path i.side))

lemma lpair_fst_self {n : ℕ} (i : LPos L n) : (lpair D hG i).1 i.mono = 1 :=
  substVec_lrel_self hG i.mono i.edge i.lead

lemma lpair_fst_low {n : ℕ} (i : LPos L n) (y : Mono E n) (hy : (lpair D hG i).1 y ≠ 0)
    (hyi : y ≠ i.mono) : pathKey rk n y.1 < pathKey rk n i.mono.1 :=
  substVec_lrel_low hG i.mono i.edge i.lead hy hyi

lemma lpair_fst_mem {n : ℕ} (i : LPos L n) : (lpair D hG i).1 ∈ idealOf K R n :=
  substVec_mem_idealOf K R i.mono i.edge (lrel hG _).2

lemma lpair_mem_syzSpan {n : ℕ} (i : LPos L n) : lpair D hG i ∈ syzSpan D n :=
  Submodule.subset_span ⟨i.mono, i.path, i.side, i.edge, _, rfl⟩

include hG in
/-- **Every leading monomial of a vector of the ideal is the monomial of a leading position.** -/
lemma exists_lpos {n : ℕ} (v : Mono E n → K) (hv : v ∈ idealOf K R n) (x : Mono E n)
    (hx : letI := keyOrder rk n; IsLeadingOf v x) : ∃ i : LPos L n, i.mono = x := by
  letI := keyOrder rk n
  have hlead : IsLeading (idealOf K R n : Set (Mono E n → K)) x := ⟨v, hv, hx⟩
  rw [isLeading_iff_of_supportedOn _ _ (fun x hx => hG.isLeading x hx) (hG.indep n)] at hlead
  obtain ⟨p, s, he, hw⟩ := not_isNormal_iff.1 hlead
  exact ⟨⟨x, p, s, he, hw⟩, rfl⟩

/-- **The relators are combinations of the normalized leading relators.** -/
lemma mem_span_lrel (r : R) :
    r ∈ Submodule.span K (Set.range fun ℓ : L => lrel hG ℓ.1) := by
  classical
  letI := keyOrder rk 3
  -- generators: the leading relators, twice
  let g : LPos L 3 → (Mono E 3 → K) × R := fun i =>
    ((lrel hG (i.mono.1.windowAt i.path i.side) : Mono E 3 → K),
      lrel hG (i.mono.1.windowAt i.path i.side))
  have hwin : ∀ i : LPos L 3, i.mono.1.windowAt i.path i.side = i.mono.1 := fun i =>
    ShuffleBar.windowAt_three i.mono.2 i.edge
  have hmono : ∀ i : LPos L 3, (⟨i.mono.1.windowAt i.path i.side, hG.mem _ i.lead⟩ : Mono E 3) =
      i.mono := fun i => Subtype.ext (hwin i)
  obtain ⟨γ, hγ, hγr⟩ := exists_mem_span_fst_top (fun y : Mono E 3 => pathKey rk 3 y.1)
    (fun x y h => by
      by_contra h'
      exact absurd h (not_le.2 (keyOrder_lt (not_le.1 h'))))
    (idealOf K R 3) g LPos.mono
    (fun i => by rw [ShuffleBar.idealOf_three]; exact (lrel hG _).2)
    (fun i => by
      show (lrel hG _ : Mono E 3 → K) i.mono = 1
      have := lrel_self hG i.lead
      rwa [hmono i] at this)
    (fun i y hy hyi => by
      have := lrel_lt hG i.lead (σ := y) (fun h => hyi (by rw [← hmono i]; exact Subtype.ext h)) hy
      rwa [hwin i] at this)
    (fun v hv x hx => exists_lpos hG v hv x hx) r (by rw [ShuffleBar.idealOf_three]; exact r.2)
  -- the span of the generators is on the diagonal
  have hdiag : ∀ γ ∈ Submodule.span K (Set.range g), γ.1 = (γ.2 : Mono E 3 → K) ∧
      γ.2 ∈ Submodule.span K (Set.range fun ℓ : L => lrel hG ℓ.1) := by
    intro γ hγ
    induction hγ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨rfl, Submodule.subset_span ⟨⟨_, i.lead⟩, rfl⟩⟩
    | zero => exact ⟨rfl, zero_mem _⟩
    | add x y _ _ hx hy =>
      exact ⟨by simp [hx.1, hy.1], add_mem hx.2 hy.2⟩
    | smul c x _ hx => exact ⟨by simp [hx.1], Submodule.smul_mem _ _ hx.2⟩
  obtain ⟨h1, h2⟩ := hdiag γ hγ
  have : γ.2 = r := Subtype.ext (h1.symm.trans hγr)
  rwa [← this]

/-- **A placement of a normalized relator is a leading placement**, at the monomial obtained by
substituting its leading monomial. -/
lemma exists_lpos_pairOf {n : ℕ} (t : Mono E n) {p : List Bool} {s : Bool} (he : t.1.IsEdge p s)
    (ℓ : L) : ∃ i : LPos L n, pairOf D n t.1 p s (lrel hG ℓ.1) = lpair D hG i := by
  have hm := (mem_monomials n t.1).1 t.2
  have hnd := hm.2.nodup_iff.2 List.nodup_range
  have hc := isCtx_window he hm.1 hnd
  have hℓ := hG.mem _ ℓ.2
  have hℓm := (mem_monomials 3 ℓ.1).1 hℓ
  have hℓe : ℓ.1.IsEdge [] (side3 ℓ.1) := by
    obtain ⟨e, f, h | h | h⟩ := mono3_cases hℓm.1 hℓm.2 <;> rw [h] <;> trivial
  have hmono := hc.strictOn (lt_of_perm_range hℓm.2)
  have hedge := isEdge_ctx hc.valid ((t.1.subtreeAt p).winIns s) hℓe
  have hwin := windowAt_ctx hc.valid ((t.1.subtreeAt p).winIns s) hℓe hmono
  rw [ShuffleBar.windowAt_three hℓ hℓe, List.append_nil] at hwin
  rw [List.append_nil] at hedge
  refine ⟨⟨⟨_, substAt_mem_monomials t.2 he hℓ⟩, p, side3 ℓ.1, hedge, ?_⟩, ?_⟩
  · show (t.1.substAt p s ℓ.1).windowAt p (side3 ℓ.1) ∈ L
    unfold substAt
    rw [hwin]
    exact ℓ.2
  · have hsub : ∀ σ : Mono E 3, (t.1.substAt p s ℓ.1).substAt p (side3 ℓ.1) σ.1 =
        t.1.substAt p s σ.1 := fun σ => by
      have := substAt_ctx hc.valid ((t.1.subtreeAt p).winIns s) hℓe hmono σ.1
      rw [List.append_nil, ShuffleBar.substAt_of_mem_monomials_three hℓ hℓe
        ((mem_monomials 3 σ.1).1 σ.2).2] at this
      exact this
    have hw : (t.1.substAt p s ℓ.1).windowAt p (side3 ℓ.1) = ℓ.1 := by
      unfold substAt
      exact hwin
    simp only [lpair, pairOf, hw, substVec, hsub]

/-- **The placements are combinations of leading placements.** -/
lemma syzSpan_le {n : ℕ} : syzSpan D n ≤ Submodule.span K (Set.range (lpair D hG (n := n))) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨t, p, s, he, r, rfl⟩
  have h := Submodule.mem_map_of_mem (f := pairOfL D n t.1 p s) (mem_span_lrel hG r)
  rw [Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨ℓ, rfl⟩, rfl⟩
  obtain ⟨i, hi⟩ := exists_lpos_pairOf D hG t he ℓ
  exact ⟨i, by rw [pairOfL_apply, hi]⟩

/-- The path-lexicographic key is monotone for the order refining it. -/
lemma monotone_pathKey (rk : E → ℕ) (n : ℕ) :
    letI := keyOrder rk n; Monotone fun y : Mono E n => pathKey rk n y.1 := by
  letI := keyOrder rk n
  intro x y h
  by_contra h'
  exact absurd h (not_le.2 (keyOrder_lt (not_le.1 h')))

/-- **The leading placements at monomials of smaller keys**, with the pairs of the ideal. -/
noncomputable def lowSpan {n : ℕ} (M : Mono E n) : Submodule K ((Mono E n → K) × (Mono E n → K)) :=
  Submodule.span K (lpair D hG '' {k : LPos L n | pathKey rk n k.mono.1 < pathKey rk n M.1}) ⊔
    idealPairs R n

/-- **Two leading placements whose substitutions commute** agree modulo leading placements at
monomials of smaller keys and the ideal: the Koszul syzygies, which `D` kills. The position of the
second edge after substituting at the first is `pos`. -/
theorem spair_comm {n : ℕ} (M : Mono E n) {p₁ p₂ : List Bool} {s₁ s₂ : Bool}
    (h₁ : M.1.IsEdge p₁ s₁) (hl₁ : M.1.windowAt p₁ s₁ ∈ L) (h₂ : M.1.IsEdge p₂ s₂)
    (hl₂ : M.1.windowAt p₂ s₂ ∈ L) (pos : LTree E → List Bool × Bool)
    (hpos : ∀ σ : Mono E 3, (M.1.substAt p₁ s₁ σ.1).IsEdge (pos σ.1).1 (pos σ.1).2 ∧
      (M.1.substAt p₁ s₁ σ.1).windowAt (pos σ.1).1 (pos σ.1).2 = M.1.windowAt p₂ s₂)
    (hpos₀ : pos (M.1.windowAt p₁ s₁) = (p₂, s₂))
    (hback : ∀ τ : Mono E 3, (M.1.substAt p₂ s₂ τ.1).IsEdge p₁ s₁ ∧
      (M.1.substAt p₂ s₂ τ.1).windowAt p₁ s₁ = M.1.windowAt p₁ s₁)
    (hcomm : ∀ σ τ : Mono E 3, (M.1.substAt p₁ s₁ σ.1).substAt (pos σ.1).1 (pos σ.1).2 τ.1 =
      (M.1.substAt p₂ s₂ τ.1).substAt p₁ s₁ σ.1) :
    pairOf D n M.1 p₁ s₁ (lrel hG (M.1.windowAt p₁ s₁)) -
      pairOf D n M.1 p₂ s₂ (lrel hG (M.1.windowAt p₂ s₂)) ∈ lowSpan D hG M := by
  classical
  set ℓ₁ := M.1.windowAt p₁ s₁ with hℓ₁
  set ℓ₂ := M.1.windowAt p₂ s₂ with hℓ₂
  set ρ₁ := lrel hG ℓ₁ with hρ₁
  set ρ₂ := lrel hG ℓ₂ with hρ₂
  have hM := (mem_monomials n M.1).1 M.2
  have hnd := hM.2.nodup_iff.2 List.nodup_range
  set w₁ : Mono E 3 := ⟨ℓ₁, hG.mem ℓ₁ hl₁⟩ with hw₁
  set w₂ : Mono E 3 := ⟨ℓ₂, hG.mem ℓ₂ hl₂⟩ with hw₂
  have hself₁ : M.1.substAt p₁ s₁ ℓ₁ = M.1 := substAt_windowAt h₁ hM.1 hnd
  have hself₂ : M.1.substAt p₂ s₂ ℓ₂ = M.1 := substAt_windowAt h₂ hM.1 hnd
  -- the commutation identity
  have hAB : ∀ r r' : Mono E 3 → K,
      ∑ σ : Mono E 3, r σ • substVec K n (M.1.substAt p₁ s₁ σ.1) (pos σ.1).1 (pos σ.1).2 r' =
        ∑ τ : Mono E 3, r' τ • substVec K n (M.1.substAt p₂ s₂ τ.1) p₁ s₁ r := by
    intro r r'
    simp only [substVec, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [hcomm σ τ, mul_comm]
  have hI₁ : ∀ r : Mono E 3 → K,
      ∑ σ : Mono E 3, r σ • substVec K n (M.1.substAt p₁ s₁ σ.1) (pos σ.1).1 (pos σ.1).2 ρ₂ ∈
        idealOf K R n := fun r =>
    Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _
      (substVec_mem_idealOf K R ⟨_, substAt_mem_monomials M.2 h₁ σ.2⟩ (hpos σ).1 ρ₂.2)
  have hI₂ : ∀ r : Mono E 3 → K,
      ∑ τ : Mono E 3, r τ • substVec K n (M.1.substAt p₂ s₂ τ.1) p₁ s₁ ρ₁ ∈ idealOf K R n :=
    fun r => Submodule.sum_mem _ fun τ _ => Submodule.smul_mem _ _
      (substVec_mem_idealOf K R ⟨_, substAt_mem_monomials M.2 h₂ τ.2⟩ (hback τ).1 ρ₁.2)
  -- the placements after one substitution
  set P₁ := ∑ σ : Mono E 3,
    (ρ₁ : Mono E 3 → K) σ • pairOf D n (M.1.substAt p₁ s₁ σ.1) (pos σ.1).1 (pos σ.1).2 ρ₂ with hP₁
  set P₂ := ∑ τ : Mono E 3,
    (ρ₂ : Mono E 3 → K) τ • pairOf D n (M.1.substAt p₂ s₂ τ.1) p₁ s₁ ρ₁ with hP₂
  have hlow₁ : ∀ σ ∈ Finset.univ.erase w₁, (ρ₁ : Mono E 3 → K) σ •
      pairOf D n (M.1.substAt p₁ s₁ σ.1) (pos σ.1).1 (pos σ.1).2 ρ₂ ∈ lowSpan D hG M := by
    intro σ hσ
    have hσ' : σ ≠ w₁ := Finset.ne_of_mem_erase hσ
    by_cases hr : (ρ₁ : Mono E 3 → K) σ = 0
    · rw [hr, zero_smul]
      exact zero_mem _
    refine Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.subset_span
      ⟨⟨⟨_, substAt_mem_monomials M.2 h₁ σ.2⟩, (pos σ.1).1, (pos σ.1).2, (hpos σ).1,
        by rw [(hpos σ).2]; exact hl₂⟩, ?_, ?_⟩))
    · exact pathKey_substAt_lrel hG M.2 h₁ hl₁ (fun h => hσ' (Subtype.ext h)) hr
    · exact congrArg (fun ℓ => pairOf D n (M.1.substAt p₁ s₁ σ.1) (pos σ.1).1 (pos σ.1).2
        (lrel hG ℓ)) (hpos σ).2
  have hlow₂ : ∀ τ ∈ Finset.univ.erase w₂, (ρ₂ : Mono E 3 → K) τ •
      pairOf D n (M.1.substAt p₂ s₂ τ.1) p₁ s₁ ρ₁ ∈ lowSpan D hG M := by
    intro τ hτ
    have hτ' : τ ≠ w₂ := Finset.ne_of_mem_erase hτ
    by_cases hr : (ρ₂ : Mono E 3 → K) τ = 0
    · rw [hr, zero_smul]
      exact zero_mem _
    refine Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.subset_span
      ⟨⟨⟨_, substAt_mem_monomials M.2 h₂ τ.2⟩, p₁, s₁, (hback τ).1,
        by rw [(hback τ).2]; exact hl₁⟩, ?_, ?_⟩))
    · exact pathKey_substAt_lrel hG M.2 h₂ hl₂ (fun h => hτ' (Subtype.ext h)) hr
    · exact congrArg (fun ℓ => pairOf D n (M.1.substAt p₂ s₂ τ.1) p₁ s₁ (lrel hG ℓ)) (hback τ).2
  have hP₁b : P₁ - pairOf D n M.1 p₂ s₂ ρ₂ ∈ lowSpan D hG M := by
    rw [hP₁, ← Finset.add_sum_erase _ _ (Finset.mem_univ w₁)]
    have h0 : (ρ₁ : Mono E 3 → K) w₁ •
        pairOf D n (M.1.substAt p₁ s₁ w₁.1) (pos w₁.1).1 (pos w₁.1).2 ρ₂ =
          pairOf D n M.1 p₂ s₂ ρ₂ := by
      rw [lrel_self hG hl₁, one_smul]
      show pairOf D n (M.1.substAt p₁ s₁ ℓ₁) (pos ℓ₁).1 (pos ℓ₁).2 ρ₂ = _
      rw [hself₁, hpos₀]
    rw [h0, add_sub_cancel_left]
    exact Submodule.sum_mem _ hlow₁
  have hP₂b : P₂ - pairOf D n M.1 p₁ s₁ ρ₁ ∈ lowSpan D hG M := by
    rw [hP₂, ← Finset.add_sum_erase _ _ (Finset.mem_univ w₂)]
    have h0 : (ρ₂ : Mono E 3 → K) w₂ • pairOf D n (M.1.substAt p₂ s₂ w₂.1) p₁ s₁ ρ₁ =
        pairOf D n M.1 p₁ s₁ ρ₁ := by
      rw [lrel_self hG hl₂, one_smul]
      show pairOf D n (M.1.substAt p₂ s₂ ℓ₂) p₁ s₁ ρ₁ = _
      rw [hself₂]
    rw [h0, add_sub_cancel_left]
    exact Submodule.sum_mem _ hlow₂
  have hP : P₂ - P₁ ∈ idealPairs R n := by
    have e1 : P₁.1 = ∑ σ : Mono E 3, (ρ₁ : Mono E 3 → K) σ •
        substVec K n (M.1.substAt p₁ s₁ σ.1) (pos σ.1).1 (pos σ.1).2 ρ₂ := by
      simp [hP₁, pairOf, Prod.fst_sum]
    have e2 : P₂.1 = ∑ τ : Mono E 3, (ρ₂ : Mono E 3 → K) τ •
        substVec K n (M.1.substAt p₂ s₂ τ.1) p₁ s₁ ρ₁ := by
      simp [hP₂, pairOf, Prod.fst_sum]
    have e3 : P₁.2 = ∑ σ : Mono E 3, (ρ₁ : Mono E 3 → K) σ •
        substVec K n (M.1.substAt p₁ s₁ σ.1) (pos σ.1).1 (pos σ.1).2 (D ρ₂) := by
      simp [hP₁, pairOf, Prod.snd_sum]
    have e4 : P₂.2 = ∑ τ : Mono E 3, (ρ₂ : Mono E 3 → K) τ •
        substVec K n (M.1.substAt p₂ s₂ τ.1) p₁ s₁ (D ρ₁) := by
      simp [hP₂, pairOf, Prod.snd_sum]
    refine Submodule.mem_prod.2 ⟨?_, ?_⟩
    · rw [Prod.fst_sub, e1, e2, hAB, sub_self]
      exact zero_mem _
    · rw [Prod.snd_sub, e3, e4, ← hAB (D ρ₁) ρ₂, hAB (ρ₁ : Mono E 3 → K) (D ρ₂)]
      exact sub_mem (hI₁ _) (hI₂ _)
  have : pairOf D n M.1 p₁ s₁ ρ₁ - pairOf D n M.1 p₂ s₂ ρ₂ =
      (P₁ - pairOf D n M.1 p₂ s₂ ρ₂) - (P₂ - pairOf D n M.1 p₁ s₁ ρ₁) + (P₂ - P₁) := by
    abel
  rw [this]
  exact add_mem (sub_mem hP₁b hP₂b) (Submodule.mem_sup_right hP)

/-! ### Contexts of arity four -/

section Ctx4

variable (K) in
/-- **A context of arity four, on vectors**: each monomial `y` of arity four goes to the monomial
of the context with `y` in place. -/
noncomputable def ctxVec (n : ℕ) (M : LTree E) (q : List Bool) (ins : ℕ → LTree E) :
    (Mono E 4 → K) →ₗ[K] (Mono E n → K) :=
  ∑ y : Mono E 4, (LinearMap.proj y : (Mono E 4 → K) →ₗ[K] K).smulRight
    (vecOf K n (M.replaceAt q (y.1.plug ins)))

variable {n : ℕ} {M : LTree E} {q : List Bool} {ins : ℕ → LTree E}

lemma ctxVec_apply (v : Mono E 4 → K) :
    ctxVec K n M q ins v = ∑ y : Mono E 4, v y • vecOf K n (M.replaceAt q (y.1.plug ins)) := by
  simp [ctxVec]

lemma ctxVec_vecOf {t : LTree E} (ht : t ∈ monomials 4) :
    ctxVec K n M q ins (vecOf K 4 t) = vecOf K n (M.replaceAt q (t.plug ins)) := by
  classical
  rw [ctxVec_apply, Finset.sum_eq_single ⟨t, ht⟩]
  · simp [vecOf]
  · intro y _ hy
    simp [vecOf, show y.1 ≠ t from fun h => hy (Subtype.ext h)]
  · simp

lemma ctxVec_substVec (hc : IsCtx M q 4 ins) {t : LTree E} (ht : t ∈ monomials 4) {x : List Bool}
    {s : Bool} (he : t.IsEdge x s) (r : Mono E 3 → K) :
    ctxVec K n M q ins (substVec K 4 t x s r) =
      substVec K n (M.replaceAt q (t.plug ins)) (q ++ x) s r := by
  have hmono := hc.strictOn (lt_of_perm_range ((mem_monomials 4 t).1 ht).2)
  simp only [substVec, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [ctxVec_vecOf (substAt_mem_monomials ht he σ.2), substAt_ctx hc.valid ins he hmono]

lemma ctxVec_mem_idealOf (hc : IsCtx M q 4 ins) (hM : M ∈ monomials n) {v : Mono E 4 → K}
    (hv : v ∈ idealOf K R 4) : ctxVec K n M q ins v ∈ idealOf K R n := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, x, s, r, hr, he, rfl⟩ := hx
    rw [ctxVec_substVec hc t.2 he]
    exact substVec_mem_idealOf K R ⟨_, hc.ctx_mem_monomials hM t.2⟩ (isEdge_ctx hc.valid ins he) hr
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

end Ctx4

/-- **Two leading placements at edges of a subtree of arity four** agree modulo leading placements
at monomials of smaller keys and the ideal, if `D` kills the syzygies of arity four: the
difference reduces by the Gröbner basis of arity four, which is a syzygy of arity four. -/
theorem spair_ctx4 (h4 : KillsSyz D 4) {n : ℕ} (M : Mono E n) {q : List Bool}
    {ins : ℕ → LTree E} (hc : IsCtx M.1 q 4 ins) {Wt : LTree E} (hW4 : Wt ∈ monomials 4)
    (hW : Wt.plug ins = M.1.subtreeAt q) {x₁ x₂ : List Bool} {s₁ s₂ : Bool}
    (h₁ : Wt.IsEdge x₁ s₁) (h₂ : Wt.IsEdge x₂ s₂) (hl₁ : M.1.windowAt (q ++ x₁) s₁ ∈ L)
    (hl₂ : M.1.windowAt (q ++ x₂) s₂ ∈ L) :
    pairOf D n M.1 (q ++ x₁) s₁ (lrel hG (M.1.windowAt (q ++ x₁) s₁)) -
      pairOf D n M.1 (q ++ x₂) s₂ (lrel hG (M.1.windowAt (q ++ x₂) s₂)) ∈ lowSpan D hG M := by
  classical
  have hctx : M.1.replaceAt q (Wt.plug ins) = M.1 := by rw [hW, replaceAt_subtreeAt]
  have hMm := (mem_monomials n M.1).1 M.2
  have hmonoOf : ∀ {y : LTree E}, y ∈ monomials 4 → StrictOn (fun a => (ins a).minLabel) y :=
    fun hy => hc.strictOn (lt_of_perm_range ((mem_monomials 4 _).1 hy).2)
  have hwin : ∀ {x : List Bool} {s : Bool}, Wt.IsEdge x s →
      M.1.windowAt (q ++ x) s = Wt.windowAt x s := fun he => by
    have := windowAt_ctx hc.valid ins he (hmonoOf hW4)
    rwa [hctx] at this
  set W : Mono E 4 := ⟨Wt, hW4⟩ with hWdef
  let a : LPos L 4 := ⟨W, x₁, s₁, h₁, by rw [← hwin h₁]; exact hl₁⟩
  let b : LPos L 4 := ⟨W, x₂, s₂, h₂, by rw [← hwin h₂]; exact hl₂⟩
  -- the difference of the first components is in the ideal, below `W`
  set v := (lpair D hG a).1 - (lpair D hG b).1 with hv
  have hvI : v ∈ idealOf K R 4 := sub_mem (lpair_fst_mem D hG a) (lpair_fst_mem D hG b)
  have hvlow : ∀ y, v y ≠ 0 → pathKey rk 4 y.1 < pathKey rk 4 W.1 := by
    intro y hy
    by_cases hyW : y = W
    · exfalso
      apply hy
      rw [hyW, hv, Pi.sub_apply]
      rw [show (lpair D hG a).1 W = 1 from lpair_fst_self D hG a,
        show (lpair D hG b).1 W = 1 from lpair_fst_self D hG b, sub_self]
    · by_cases ha : (lpair D hG a).1 y = 0
      · have hb : (lpair D hG b).1 y ≠ 0 := fun hb => hy (by simp [hv, ha, hb])
        exact lpair_fst_low D hG b y hb hyW
      · exact lpair_fst_low D hG a y ha hyW
  -- a standard representation in arity four
  letI := keyOrder rk 4
  obtain ⟨γ, hγ, hγv⟩ := exists_mem_span_fst (fun y : Mono E 4 => pathKey rk 4 y.1)
    (monotone_pathKey rk 4) (idealOf K R 4) (lpair D hG) LPos.mono (lpair_fst_mem D hG)
    (lpair_fst_self D hG) (lpair_fst_low D hG) (fun v hv x hx => exists_lpos hG v hv x hx)
    (pathKey rk 4 W.1) v hvI hvlow
  -- the syzygy of arity four
  set δ := lpair D hG a - lpair D hG b - γ with hδ
  have hγS : γ ∈ syzSpan D 4 := by
    refine Submodule.span_le.2 ?_ hγ
    rintro _ ⟨k, -, rfl⟩
    exact lpair_mem_syzSpan D hG k
  have hδS : δ ∈ syzSpan D 4 :=
    sub_mem (sub_mem (lpair_mem_syzSpan D hG a) (lpair_mem_syzSpan D hG b)) hγS
  have hδ1 : δ.1 = 0 := by simp [hδ, hγv, hv]
  have hδ2 : δ.2 ∈ idealOf K R 4 :=
    h4 δ.2 (by rwa [show ((0 : Mono E 4 → K), δ.2) = δ from Prod.ext hδ1.symm rfl])
  -- the transport to the monomial of arity `n`
  set C := ctxVec K n M.1 q ins with hC
  set Φ := LinearMap.prodMap C C with hΦ
  have hΦpair : ∀ k : LPos L 4, ∃ k' : LPos L n, Φ (lpair D hG k) = lpair D hG k' ∧
      k'.mono.1 = M.1.replaceAt q (k.mono.1.plug ins) := by
    intro k
    have hwk := windowAt_ctx hc.valid ins k.edge (hmonoOf k.mono.2)
    refine ⟨⟨⟨_, hc.ctx_mem_monomials M.2 k.mono.2⟩, q ++ k.path, k.side,
      isEdge_ctx hc.valid ins k.edge, by rw [hwk]; exact k.lead⟩, ?_, rfl⟩
    simp only [hΦ, LinearMap.prodMap_apply, lpair, pairOf, hC,
      ctxVec_substVec hc k.mono.2 k.edge]
    rw [hwk]
  have hΦγ : Φ γ ∈ Submodule.span K
      (lpair D hG '' {k : LPos L n | pathKey rk n k.mono.1 < pathKey rk n M.1}) := by
    have := Submodule.mem_map_of_mem (f := Φ) hγ
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    obtain ⟨k', hk', hk'm⟩ := hΦpair k
    refine ⟨k', ?_, hk'.symm⟩
    show pathKey rk n k'.mono.1 < pathKey rk n M.1
    rw [hk'm]
    have := hc.pathKey_ctx_lt rk hMm.2 ((mem_monomials 4 _).1 k.mono.2).2
      ((mem_monomials 4 _).1 hW4).2 hk
    rwa [hctx] at this
  have hΦδ : Φ δ ∈ idealPairs R n := by
    refine Submodule.mem_prod.2 ⟨?_, ?_⟩
    · show C δ.1 ∈ ⊥
      rw [hδ1, map_zero]
      exact zero_mem _
    · exact ctxVec_mem_idealOf hc M.2 hδ2
  have hΦa : Φ (lpair D hG a) = pairOf D n M.1 (q ++ x₁) s₁
      (lrel hG (M.1.windowAt (q ++ x₁) s₁)) := by
    show Φ (pairOf D 4 Wt x₁ s₁ (lrel hG (Wt.windowAt x₁ s₁))) = _
    simp only [hΦ, LinearMap.prodMap_apply, pairOf, hC, ctxVec_substVec hc hW4 h₁, hctx]
    rw [hwin h₁]
  have hΦb : Φ (lpair D hG b) = pairOf D n M.1 (q ++ x₂) s₂
      (lrel hG (M.1.windowAt (q ++ x₂) s₂)) := by
    show Φ (pairOf D 4 Wt x₂ s₂ (lrel hG (Wt.windowAt x₂ s₂))) = _
    simp only [hΦ, LinearMap.prodMap_apply, pairOf, hC, ctxVec_substVec hc hW4 h₂, hctx]
    rw [hwin h₂]
  rw [← hΦa, ← hΦb, ← map_sub, show lpair D hG a - lpair D hG b = γ + δ by rw [hδ]; abel,
    map_add]
  exact add_mem (Submodule.mem_sup_left hΦγ) (Submodule.mem_sup_right hΦδ)

/-- **An edge inside an input of a window**: its substitutions commute with those at the window,
the input being moved by the substitution at the window. -/
theorem spair_nested {n : ℕ} (M : Mono E n) {p₁ : List Bool} {s₁ s₂ : Bool}
    (h₁ : M.1.IsEdge p₁ s₁) (hl₁ : M.1.windowAt p₁ s₁ ∈ L) {j : ℕ} (hj : j < 3) {d : List Bool}
    (hd : ((M.1.subtreeAt p₁).winIns s₁ j).IsEdge d s₂)
    (hl₂ : M.1.windowAt (p₁ ++ (leafPos j (M.1.windowAt p₁ s₁) ++ d)) s₂ ∈ L) :
    pairOf D n M.1 p₁ s₁ (lrel hG (M.1.windowAt p₁ s₁)) -
      pairOf D n M.1 (p₁ ++ (leafPos j (M.1.windowAt p₁ s₁) ++ d)) s₂
        (lrel hG (M.1.windowAt (p₁ ++ (leafPos j (M.1.windowAt p₁ s₁) ++ d)) s₂)) ∈
      lowSpan D hG M := by
  have hM := (mem_monomials n M.1).1 M.2
  have hnd := hM.2.nodup_iff.2 List.nodup_range
  set ins := (M.1.subtreeAt p₁).winIns s₁ with hins
  set W₁ := M.1.windowAt p₁ s₁ with hW₁
  have hc := isCtx_window h₁ hM.1 hnd
  have hW₁m : W₁ ∈ monomials 3 := ShuffleBar.windowAt_mem_three M.2 h₁
  have hW₁l := ((mem_monomials 3 W₁).1 hW₁m).2
  have hctx : M.1.replaceAt p₁ (W₁.plug ins) = M.1 := substAt_windowAt h₁ hM.1 hnd
  have hW₁e : W₁.IsEdge [] s₁ := isEdge_windowAt h₁
  have hjm : ∀ {σ : LTree E}, σ.labels.Perm (List.range 3) → j ∈ σ.labels := fun hσ =>
    hσ.symm.subset (List.mem_range.2 hj)
  have hσl : ∀ σ : Mono E 3, σ.1.labels.Perm (List.range 3) := fun σ =>
    ((mem_monomials 3 σ.1).1 σ.2).2
  -- the inputs after substituting at the inner edge
  set ins' : LTree E → ℕ → LTree E := fun τ =>
    Function.update ins j ((ins j).substAt d s₂ τ) with hins'
  have hmin' : ∀ τ : Mono E 3, ∀ a, (ins' τ.1 a).minLabel = (ins a).minLabel := by
    intro τ a
    by_cases ha : a = j
    · subst ha
      simp only [hins', Function.update_self]
      exact minLabel_eq_of_perm (perm_labels_substAt hd (hc.shuffle a hj) (hc.nodup_ins hnd a hj)
        (hσl τ))
    · simp only [hins', Function.update_of_ne ha]
  have hmono' : ∀ τ : Mono E 3, StrictOn (fun a => (ins' τ.1 a).minLabel) W₁ := fun τ => by
    simp only [hmin']
    exact hc.strictOn (lt_of_perm_range hW₁l)
  have hM₂ : ∀ τ : Mono E 3, M.1.substAt (p₁ ++ (leafPos j W₁ ++ d)) s₂ τ.1 =
      M.1.replaceAt p₁ (W₁.plug (ins' τ.1)) := fun τ => by
    conv_lhs => rw [← hctx]
    exact substAt_ctx_ins hc.valid ins (hW₁l.nodup_iff.2 List.nodup_range) (hjm hW₁l) d s₂ τ.1
  have hwin₂ : M.1.windowAt (p₁ ++ (leafPos j W₁ ++ d)) s₂ = (ins j).windowAt d s₂ := by
    conv_lhs => rw [← hctx]
    exact windowAt_ctx_ins hc.valid ins (hjm hW₁l) d s₂
  have h₂ : M.1.IsEdge (p₁ ++ (leafPos j W₁ ++ d)) s₂ := by
    rw [← hctx]
    exact isEdge_ctx_ins hc.valid ins (hjm hW₁l) hd
  refine spair_comm D hG M h₁ hl₁ h₂ hl₂ (fun σ => (p₁ ++ (leafPos j σ ++ d), s₂))
    (fun σ => ⟨isEdge_ctx_ins hc.valid ins (hjm (hσl σ)) hd, ?_⟩) rfl (fun τ => ⟨?_, ?_⟩)
    (fun σ τ => ?_)
  · rw [hwin₂]
    exact windowAt_ctx_ins hc.valid ins (hjm (hσl σ)) d s₂
  · rw [hM₂ τ]
    have := isEdge_ctx hc.valid (ins' τ.1) hW₁e
    rwa [List.append_nil] at this
  · rw [hM₂ τ]
    have := windowAt_ctx hc.valid (ins' τ.1) hW₁e (hmono' τ)
    rwa [List.append_nil, ShuffleBar.windowAt_three hW₁m hW₁e] at this
  · show (M.1.replaceAt p₁ (σ.1.plug ins)).substAt (p₁ ++ (leafPos j σ.1 ++ d)) s₂ τ.1 = _
    rw [substAt_ctx_ins hc.valid ins ((hσl σ).nodup_iff.2 List.nodup_range) (hjm (hσl σ)) d s₂ τ.1,
      hM₂ τ]
    have := substAt_ctx hc.valid (ins' τ.1) hW₁e (hmono' τ) σ.1
    rw [List.append_nil, ShuffleBar.substAt_of_mem_monomials_three hW₁m hW₁e (hσl σ)] at this
    exact this.symm

/-- **Two edges in disjoint subtrees**: their substitutions commute. -/
theorem spair_diverge {n : ℕ} (M : Mono E n) {c d₁ d₂ : List Bool} {b s₁ s₂ : Bool}
    (h₁ : M.1.IsEdge (c ++ b :: d₁) s₁) (hl₁ : M.1.windowAt (c ++ b :: d₁) s₁ ∈ L)
    (h₂ : M.1.IsEdge (c ++ (!b) :: d₂) s₂) (hl₂ : M.1.windowAt (c ++ (!b) :: d₂) s₂ ∈ L) :
    pairOf D n M.1 (c ++ b :: d₁) s₁ (lrel hG (M.1.windowAt (c ++ b :: d₁) s₁)) -
      pairOf D n M.1 (c ++ (!b) :: d₂) s₂ (lrel hG (M.1.windowAt (c ++ (!b) :: d₂) s₂)) ∈
      lowSpan D hG M := by
  have hsub₁ : ∀ τ : LTree E, (M.1.substAt (c ++ (!b) :: d₂) s₂ τ).subtreeAt (c ++ b :: d₁) =
      M.1.subtreeAt (c ++ b :: d₁) := fun τ => by
    have := subtreeAt_substAt_of_diverge M.1 c d₂ d₁ (!b) s₂ τ
    rwa [Bool.not_not] at this
  refine spair_comm D hG M h₁ hl₁ h₂ hl₂ (fun _ => (c ++ (!b) :: d₂, s₂)) (fun σ => ⟨?_, ?_⟩) rfl
    (fun τ => ⟨?_, ?_⟩) (fun σ τ => substAt_comm_of_diverge M.1 c d₁ d₂ b s₁ s₂ σ.1 τ.1)
  · unfold IsEdge
    rw [subtreeAt_substAt_of_diverge]
    exact h₂
  · unfold windowAt
    rw [subtreeAt_substAt_of_diverge]
  · unfold IsEdge
    rw [hsub₁]
    exact h₁
  · unfold windowAt
    rw [hsub₁]

/-- **Two edges, the second below the vertex of the first.** -/
theorem spair_extends (h4 : KillsSyz D 4) {n : ℕ} (M : Mono E n) {p₁ x : List Bool}
    {s₁ s₂ : Bool} (h₁ : M.1.IsEdge p₁ s₁) (hl₁ : M.1.windowAt p₁ s₁ ∈ L)
    (h₂ : M.1.IsEdge (p₁ ++ x) s₂) (hl₂ : M.1.windowAt (p₁ ++ x) s₂ ∈ L) :
    pairOf D n M.1 p₁ s₁ (lrel hG (M.1.windowAt p₁ s₁)) -
      pairOf D n M.1 (p₁ ++ x) s₂ (lrel hG (M.1.windowAt (p₁ ++ x) s₂)) ∈ lowSpan D hG M := by
  have hM := (mem_monomials n M.1).1 M.2
  have hnd := hM.2.nodup_iff.2 List.nodup_range
  rcases edge_below_cases h₁ hM.1 hnd h₂ with rfl | rfl | ⟨j, hj, d, rfl, hd⟩
  · -- the same vertex
    rw [List.append_nil] at h₂ hl₂ ⊢
    by_cases hs : s₂ = s₁
    · subst hs
      rw [sub_self]
      exact zero_mem _
    have hs' : s₂ = !s₁ := by cases s₁ <;> cases s₂ <;> simp_all
    subst hs'
    have hu₁ : (M.1.subtreeAt p₁).IsEdgeRoot s₁ := h₁
    have hu₂ : (M.1.subtreeAt p₁).IsEdgeRoot (!s₁) := h₂
    have hcov : Covers cherryShape (M.1.subtreeAt p₁) := by
      cases s₁
      · exact covers_cherry hu₁ hu₂
      · exact covers_cherry hu₂ hu₁
    obtain ⟨Wt, ins, hc, hW, hWs, hWl, hWe⟩ :=
      exists_ctx4 hM.1 hnd h₁.exists_node hcov arity_cherryShape
    have := spair_ctx4 D hG h4 M hc ((mem_monomials 4 Wt).2 ⟨hWs, hWl⟩) hW
      (hWe [] s₁ (isEdge_cherryShape s₁)) (hWe [] (!s₁) (isEdge_cherryShape _))
      (by rwa [List.append_nil]) (by rwa [List.append_nil])
    simpa only [List.append_nil] using this
  · -- the lower vertex of the window
    have hu₁ : (M.1.subtreeAt p₁).IsEdgeRoot s₁ := h₁
    have hu₂ : ((M.1.subtreeAt p₁).subtreeAt [s₁]).IsEdgeRoot s₂ := by
      have := h₂
      unfold IsEdge at this
      rwa [subtreeAt_append] at this
    obtain ⟨Wt, ins, hc, hW, hWs, hWl, hWe⟩ :=
      exists_ctx4 hM.1 hnd h₁.exists_node (covers_chain hu₁ hu₂) (arity_chainShape s₁ s₂)
    have := spair_ctx4 D hG h4 M hc ((mem_monomials 4 Wt).2 ⟨hWs, hWl⟩) hW
      (hWe [] s₁ (isEdge_chainShape s₁ s₂).1) (hWe [s₁] s₂ (isEdge_chainShape s₁ s₂).2)
      (by rwa [List.append_nil]) hl₂
    simpa only [List.append_nil] using this
  · -- inside an input of the window
    exact spair_nested D hG M h₁ hl₁ hj hd hl₂

/-- **Two leading placements at the same monomial** agree modulo leading placements at monomials
of smaller keys and the ideal, if `D` kills the syzygies of arity four. -/
theorem spair (h4 : KillsSyz D 4) {n : ℕ} (M : Mono E n) {p₁ p₂ : List Bool} {s₁ s₂ : Bool}
    (h₁ : M.1.IsEdge p₁ s₁) (hl₁ : M.1.windowAt p₁ s₁ ∈ L) (h₂ : M.1.IsEdge p₂ s₂)
    (hl₂ : M.1.windowAt p₂ s₂ ∈ L) :
    pairOf D n M.1 p₁ s₁ (lrel hG (M.1.windowAt p₁ s₁)) -
      pairOf D n M.1 p₂ s₂ (lrel hG (M.1.windowAt p₂ s₂)) ∈ lowSpan D hG M := by
  rcases path_cases p₁ p₂ with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨c, d₁, d₂, b, rfl, rfl⟩
  · exact spair_extends D hG h4 M h₁ hl₁ h₂ hl₂
  · rw [← neg_sub]
    exact neg_mem (spair_extends D hG h4 M h₂ hl₂ h₁ hl₁)
  · exact spair_diverge D hG M h₁ hl₁ h₂ hl₂

/-! ## Syzygies in every arity -/

include hG in
/-- **If `D` kills the syzygies of arity four, it kills those of every arity**, for a quadratic
Gröbner basis. -/
theorem killsSyz_of_four (h4 : KillsSyz D 4) (n : ℕ) : KillsSyz D n := by
  classical
  have hsch := schreyer (fun y : Mono E n => pathKey rk n y.1) (idealPairs R n)
    (fun v hv => fst_eq_zero_of_mem_idealPairs hv) (lpair D hG) LPos.mono
    (lpair_fst_self D hG) (lpair_fst_low D hG) fun i j hij => by
      obtain ⟨M, p₁, s₁, h₁, hl₁⟩ := i
      obtain ⟨M', p₂, s₂, h₂, hl₂⟩ := j
      obtain rfl : M = M' := hij
      exact spair D hG h4 M h₁ hl₁ h₂ hl₂
  intro w hw
  exact (Submodule.mem_prod.1 (hsch _ (Submodule.mem_sup_left (syzSpan_le D hG hw)) rfl)).2

end Leading

/-! ## The extension to the ideal -/

section Extension

variable {K : Type*} [Field K] {E : Type*} [Fintype E] [DecidableEq E]
  {R : Submodule K (Mono E 3 → K)} (D : R →ₗ[K] (Mono E 3 → K))

lemma fst_mem_of_mem_syzSpan {n : ℕ} {x : (Mono E n → K) × (Mono E n → K)}
    (hx : x ∈ syzSpan D n) : x.1 ∈ idealOf K R n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, p, s, he, r, rfl⟩ := hx
    exact substVec_mem_idealOf K R t he r.2
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ _ hx

lemma exists_mem_syzSpan {n : ℕ} {v : Mono E n → K} (hv : v ∈ idealOf K R n) :
    ∃ x ∈ syzSpan D n, x.1 = v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, p, s, r, hr, he, rfl⟩ := hv
    exact ⟨_, Submodule.subset_span ⟨t, p, s, he, ⟨r, hr⟩, rfl⟩, rfl⟩
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add v w _ _ hv hw =>
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨y, hy, rfl⟩ := hw
    exact ⟨x + y, add_mem hx hy, rfl⟩
  | smul c v _ hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨c • x, Submodule.smul_mem _ _ hx, rfl⟩

/-- **`D` kills the syzygies of arity `n` exactly when it extends to the ideal**: there is a linear
map `c` on the ideal, with values in the quotient, taking each relator `r` placed at an edge to
`D(r)` placed at the same edge. -/
theorem killsSyz_iff_exists_ext {n : ℕ} : KillsSyz D n ↔
    ∃ c : idealOf K R n →ₗ[K] (Mono E n → K) ⧸ idealOf K R n,
      ∀ (t : Mono E n) (p : List Bool) (s : Bool) (he : t.1.IsEdge p s) (r : R),
        c ⟨substVec K n t.1 p s r, substVec_mem_idealOf K R t he r.2⟩ =
          Submodule.Quotient.mk (substVec K n t.1 p s (D r)) := by
  set Γ := syzSpan D n with hΓ
  let g : Γ →ₗ[K] idealOf K R n :=
    (LinearMap.fst K _ _ ∘ₗ Γ.subtype).codRestrict (idealOf K R n) fun x =>
      fst_mem_of_mem_syzSpan D x.2
  let f : Γ →ₗ[K] (Mono E n → K) ⧸ idealOf K R n :=
    (idealOf K R n).mkQ ∘ₗ LinearMap.snd K _ _ ∘ₗ Γ.subtype
  have hg : Function.Surjective g := by
    rintro ⟨v, hv⟩
    obtain ⟨x, hx, rfl⟩ := exists_mem_syzSpan D hv
    exact ⟨⟨x, hx⟩, rfl⟩
  constructor
  · intro h
    have hker : LinearMap.ker g ≤ LinearMap.ker f := by
      rintro ⟨x, hx⟩ hgx
      have h1 : x.1 = 0 := congrArg Subtype.val hgx
      have h2 : x.2 ∈ idealOf K R n :=
        h x.2 (by rwa [show ((0 : Mono E n → K), x.2) = x from Prod.ext h1.symm rfl])
      simpa [f] using (Submodule.Quotient.mk_eq_zero _).2 h2
    refine ⟨(LinearMap.ker g).liftQ f hker ∘ₗ (g.quotKerEquivOfSurjective hg).symm.toLinearMap,
      fun t p s he r => ?_⟩
    have hx : pairOf D n t.1 p s r ∈ Γ := Submodule.subset_span ⟨t, p, s, he, r, rfl⟩
    have : (⟨substVec K n t.1 p s r, substVec_mem_idealOf K R t he r.2⟩ : idealOf K R n) =
        g ⟨_, hx⟩ := rfl
    rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  · rintro ⟨c, hc⟩ w hw
    have key : ∀ x (hx : x ∈ Γ), c ⟨x.1, fst_mem_of_mem_syzSpan D hx⟩ =
        Submodule.Quotient.mk x.2 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨t, p, s, he, r, rfl⟩ := hx
        exact hc t p s he r
      | zero => exact map_zero c
      | add x y hx' hy' hx hy =>
        have := congrArg₂ (· + ·) hx hy
        simp only [← map_add] at this
        convert this using 1
      | smul a x hx' hx =>
        have := congrArg (a • ·) hx
        simp only [← map_smul] at this
        convert this using 1
    have h0 : c ⟨((0 : Mono E n → K), w).1, fst_mem_of_mem_syzSpan D hw⟩ = 0 := map_zero c
    rw [key _ hw] at h0
    exact (Submodule.Quotient.mk_eq_zero _).1 h0

variable {rk : E → ℕ} {L : Set (LTree E)}

/-- **A cochain on the relators killing the syzygies of arity four extends to the ideal**, in every
arity, for a quadratic Gröbner basis: there is a linear map on the ideal, with values in the
quotient, taking each relator `r` placed at an edge to `D(r)` placed at the same edge. -/
theorem exists_idealExt (hG : IsGroebner K rk L R) (h4 : KillsSyz D 4) (n : ℕ) :
    ∃ c : idealOf K R n →ₗ[K] (Mono E n → K) ⧸ idealOf K R n,
      ∀ (t : Mono E n) (p : List Bool) (s : Bool) (he : t.1.IsEdge p s) (r : R),
        c ⟨substVec K n t.1 p s r, substVec_mem_idealOf K R t he r.2⟩ =
          Submodule.Quotient.mk (substVec K n t.1 p s (D r)) :=
  (killsSyz_iff_exists_ext D).1 (killsSyz_of_four D hG h4 n)

/-- **The extension is unique**: the ideal is spanned by the relators placed at edges. -/
theorem idealExt_unique {n : ℕ} {c c' : idealOf K R n →ₗ[K] (Mono E n → K) ⧸ idealOf K R n}
    (hc : ∀ (t : Mono E n) (p : List Bool) (s : Bool) (he : t.1.IsEdge p s) (r : R),
      c ⟨substVec K n t.1 p s r, substVec_mem_idealOf K R t he r.2⟩ =
        Submodule.Quotient.mk (substVec K n t.1 p s (D r)))
    (hc' : ∀ (t : Mono E n) (p : List Bool) (s : Bool) (he : t.1.IsEdge p s) (r : R),
      c' ⟨substVec K n t.1 p s r, substVec_mem_idealOf K R t he r.2⟩ =
        Submodule.Quotient.mk (substVec K n t.1 p s (D r))) : c = c' := by
  ext ⟨v, hv⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, p, s, r, hr, he, rfl⟩ := hv
    exact (hc t p s he ⟨r, hr⟩).trans (hc' t p s he ⟨r, hr⟩).symm
  | zero => exact (map_zero c).trans (map_zero c').symm
  | add x y hx' hy' hx hy =>
    have e : (⟨x + y, add_mem hx' hy'⟩ : idealOf K R n) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
    rw [e, map_add, map_add, hx, hy]
  | smul a x hx' hx =>
    have e : (⟨a • x, Submodule.smul_mem _ a hx'⟩ : idealOf K R n) = a • ⟨x, hx'⟩ := rfl
    rw [e, map_smul, map_smul, hx]

end Extension

end LTree

end Operad
