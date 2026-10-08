/-
# Quasi-isomorphisms of modules with differentials, by filtrations and retractions

For linear maps `D : M → M`, `D' : M' → M'` and `F : M → M'`, and submodules `S`, `S'`, the
predicates `QIso.Surj` and `QIso.Inj` say that `F` is surjective, resp. injective, on the
homology of `D` restricted to `S` and of `D'` restricted to `S'`: every cycle of `S'` is the image
of a cycle of `S` up to a boundary of `S'`, and a cycle of `S` whose image is a boundary of `S'`
is a boundary of `S`.

* **Extensions** (`QIso.surj_sup`, `QIso.inj_sup`): let `D = D₀ + D₁` with `D` squaring to zero,
  `U` and `W` independent submodules, `D₀` preserving `U`, `D₁` sending `U` into `W`, and `D`
  preserving `W`. If `F` commutes with `D₀` and `D₁` and is a quasi-isomorphism on `(U, D₀)` and
  on `(W, D)`, it is one on `(U ⊔ W, D)`: the five lemma for the split extension
  `0 → W → U ⊔ W → U → 0`.
* **The two out of three property** (`QIso.surj_of_sup`, `QIso.inj_of_sup`): if `F` is a
  quasi-isomorphism on `(W, D)` and on `(U ⊔ W, D)`, it is one on `(U, D₀)`.
* **Finite filtrations** (`QIso.surj_filt`, `QIso.inj_filt`): for a decreasing filtration
  `S p = X p ⊔ S (p + 1)`, vanishing from some point on, with `D₀` preserving the graded pieces
  `X p` and `D₁` raising the filtration, a quasi-isomorphism on the graded pieces is one on the
  filtered module.
* **Retractions** (`QIso.surj_of_retract`, `QIso.inj_of_retract`): if `r` and `r'` are idempotent
  maps killing the differentials and killed by them, whose kernels are acyclic, and `r' F r` is
  identified with a map `G` invertible on the images, then `F` is a quasi-isomorphism.
-/
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

universe u

namespace Operad

namespace QIso

variable {R : Type u} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

/-- **Surjectivity on homology** of `F`, restricted to `S` and `S'`. -/
def Surj (S : Submodule R M) (S' : Submodule R M') (D : M →ₗ[R] M) (D' : M' →ₗ[R] M')
    (F : M →ₗ[R] M') : Prop :=
  ∀ y' ∈ S', D' y' = 0 → ∃ x ∈ S, D x = 0 ∧ ∃ z' ∈ S', F x - y' = D' z'

/-- **Injectivity on homology** of `F`, restricted to `S` and `S'`. -/
def Inj (S : Submodule R M) (S' : Submodule R M') (D : M →ₗ[R] M) (D' : M' →ₗ[R] M')
    (F : M →ₗ[R] M') : Prop :=
  ∀ x ∈ S, D x = 0 → ∀ z' ∈ S', F x = D' z' → ∃ z ∈ S, D z = x

lemma surj_bot (D : M →ₗ[R] M) (D' : M' →ₗ[R] M') (F : M →ₗ[R] M') :
    Surj ⊥ ⊥ D D' F := fun y' hy' _ => by
  rw [Submodule.mem_bot] at hy'
  exact ⟨0, zero_mem _, map_zero D, 0, zero_mem _, by rw [hy', map_zero, map_zero, sub_zero]⟩

lemma inj_bot (D : M →ₗ[R] M) (D' : M' →ₗ[R] M') (F : M →ₗ[R] M') :
    Inj ⊥ ⊥ D D' F := fun x hx _ _ _ _ => by
  rw [Submodule.mem_bot] at hx
  exact ⟨0, zero_mem _, by rw [hx, map_zero]⟩

/-- Components in independent submodules of a vanishing sum vanish. -/
lemma eq_zero_of_add {U W : Submodule R M} (h : Disjoint U W) {u w : M} (hu : u ∈ U)
    (hw : w ∈ W) (hs : u + w = 0) : u = 0 ∧ w = 0 := by
  have hu' : u = -w := eq_neg_of_add_eq_zero_left hs
  have h0 : u = 0 := Submodule.disjoint_def.1 h u hu (hu' ▸ W.neg_mem hw)
  exact ⟨h0, by rw [h0, zero_add] at hs; exact hs⟩

/-! ## Split extensions -/

section Extension

variable {D₀ D₁ : M →ₗ[R] M} {D₀' D₁' : M' →ₗ[R] M'} {F : M →ₗ[R] M'}
  {U W : Submodule R M} {U' W' : Submodule R M'}

/-- The data of a split extension `0 → W → U ⊔ W → U → 0` of modules with differentials. -/
structure Split (D₀ D₁ : M →ₗ[R] M) (U W : Submodule R M) : Prop where
  disj : Disjoint U W
  dd : ∀ x, (D₀ + D₁) ((D₀ + D₁) x) = 0
  mem₀ : ∀ u ∈ U, D₀ u ∈ U
  mem₁ : ∀ u ∈ U, D₁ u ∈ W
  memW : ∀ w ∈ W, (D₀ + D₁) w ∈ W

/-- A morphism of split extensions. -/
structure SplitHom (F : M →ₗ[R] M') (D₀ D₁ : M →ₗ[R] M) (D₀' D₁' : M' →ₗ[R] M')
    (U W : Submodule R M) (U' W' : Submodule R M') : Prop where
  memU : ∀ u ∈ U, F u ∈ U'
  memW : ∀ w ∈ W, F w ∈ W'
  comm₀ : ∀ x, F (D₀ x) = D₀' (F x)
  comm₁ : ∀ x, F (D₁ x) = D₁' (F x)

namespace Split

variable (hs : Split D₀ D₁ U W)
include hs

lemma memW' {w : M} (hw : w ∈ W) : D₀ w + D₁ w ∈ W := by
  have := hs.memW w hw
  rwa [LinearMap.add_apply] at this

lemma dd' (x : M) : D₀ (D₀ x) + D₁ (D₀ x) + (D₀ (D₁ x) + D₁ (D₁ x)) = 0 := by
  have h := hs.dd x
  simpa only [LinearMap.add_apply, map_add] using h

lemma d₀_d₀ {u : M} (hu : u ∈ U) : D₀ (D₀ u) = 0 :=
  (eq_zero_of_add hs.disj (hs.mem₀ _ (hs.mem₀ u hu))
    (W.add_mem (hs.mem₁ _ (hs.mem₀ u hu)) (hs.memW' (hs.mem₁ u hu)))
    (by linear_combination (norm := module) hs.dd' u)).1

/-- `D (D₁ u) = -D₁ (D₀ u)`. -/
lemma d_d₁ {u : M} (hu : u ∈ U) : D₀ (D₁ u) + D₁ (D₁ u) = -D₁ (D₀ u) := by
  have := (eq_zero_of_add hs.disj (hs.mem₀ _ (hs.mem₀ u hu))
    (W.add_mem (hs.mem₁ _ (hs.mem₀ u hu)) (hs.memW' (hs.mem₁ u hu)))
    (by linear_combination (norm := module) hs.dd' u)).2
  linear_combination (norm := module) this

lemma comps {u w : M} (hu : u ∈ U) (hw : w ∈ W) (h : (D₀ + D₁) (u + w) = 0) :
    D₀ u = 0 ∧ D₁ u + (D₀ w + D₁ w) = 0 :=
  eq_zero_of_add hs.disj (hs.mem₀ u hu) (W.add_mem (hs.mem₁ u hu) (hs.memW' hw)) (by
    simp only [LinearMap.add_apply, map_add] at h
    linear_combination (norm := module) h)

end Split

variable (hs : Split D₀ D₁ U W) (hs' : Split D₀' D₁' U' W')
  (hF : SplitHom F D₀ D₁ D₀' D₁' U W U' W')
include hs hs' hF

/-- **Extensions, surjectivity**: a quasi-isomorphism on the quotient and on the subcomplex is
surjective on the homology of the extension. -/
theorem surj_sup (hUs : Surj U U' D₀ D₀' F) (hWs : Surj W W' (D₀ + D₁) (D₀' + D₁') F)
    (hWi : Inj W W' (D₀ + D₁) (D₀' + D₁') F) :
    Surj (U ⊔ W) (U' ⊔ W') (D₀ + D₁) (D₀' + D₁') F := by
  intro y' hy' hdy
  obtain ⟨u', hu', w', hw', rfl⟩ := Submodule.mem_sup.1 hy'
  obtain ⟨h0', h1'⟩ := hs'.comps hu' hw' hdy
  obtain ⟨u, hu, hdu, a', ha', hua⟩ := hUs u' hu' h0'
  have ea := hs'.d_d₁ ha'
  have ec := hF.comm₁ u
  have eh := congrArg D₁' hua
  rw [map_sub] at eh
  have hFd : F (D₁ u) = (D₀' + D₁') (-w' - D₁' a') := by
    simp only [LinearMap.add_apply, map_sub, map_neg]
    linear_combination (norm := module) ec + eh + h1' + ea
  have hdd : (D₀ + D₁) (D₁ u) = 0 := by
    rw [LinearMap.add_apply, hs.d_d₁ hu, hdu, map_zero, neg_zero]
  obtain ⟨z, hz, hdz⟩ := hWi _ (hs.mem₁ u hu) hdd _
    (W'.sub_mem (W'.neg_mem hw') (hs'.mem₁ a' ha')) hFd
  rw [LinearMap.add_apply] at hdz
  have hc'm : F (-z) - w' - D₁' a' ∈ W' := W'.sub_mem (W'.sub_mem (hF.memW _ (W.neg_mem hz)) hw')
    (hs'.mem₁ a' ha')
  have hdc : (D₀' + D₁') (F (-z) - w' - D₁' a') = 0 := by
    have eFz := congrArg F hdz
    rw [map_add] at eFz
    have ec0 := hF.comm₀ z
    have ec1 := hF.comm₁ z
    simp only [LinearMap.add_apply, map_sub, map_neg] at hFd ⊢
    linear_combination (norm := module) ec0 + ec1 - eFz - hFd
  obtain ⟨w₁, hw₁, hdw₁, b', hb', hwb⟩ := hWs _ hc'm hdc
  refine ⟨u + (-z - w₁), Submodule.mem_sup.2 ⟨u, hu, _, W.sub_mem (W.neg_mem hz) hw₁, rfl⟩, ?_,
    a' - b', Submodule.sub_mem _ (Submodule.mem_sup_left ha') (Submodule.mem_sup_right hb'), ?_⟩
  · simp only [LinearMap.add_apply, map_add, map_sub, map_neg] at hdw₁ ⊢
    linear_combination (norm := module) hdu - hdz - hdw₁
  · simp only [LinearMap.add_apply, map_add, map_sub, map_neg] at hwb ⊢
    linear_combination (norm := module) hua - hwb

/-- **Extensions, injectivity**. -/
theorem inj_sup (hUs : Surj U U' D₀ D₀' F) (hUi : Inj U U' D₀ D₀' F)
    (hWi : Inj W W' (D₀ + D₁) (D₀' + D₁') F) :
    Inj (U ⊔ W) (U' ⊔ W') (D₀ + D₁) (D₀' + D₁') F := by
  intro x hx hdx z' hz' hFx
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 hz'
  obtain ⟨h0, h1⟩ := hs.comps hu hw hdx
  simp only [LinearMap.add_apply, map_add] at hFx
  obtain ⟨e1, e2⟩ := eq_zero_of_add hs'.disj (U'.sub_mem (hF.memU u hu) (hs'.mem₀ a' ha'))
    (W'.sub_mem (hF.memW w hw) (W'.add_mem (hs'.mem₁ a' ha') (hs'.memW' hb')))
    (by linear_combination (norm := module) hFx)
  rw [sub_eq_zero] at e1 e2
  obtain ⟨a, ha, hda⟩ := hUi u hu h0 a' ha' e1
  have hcy : D₀' (a' - F a) = 0 := by
    have ec := hF.comm₀ a
    have eFa := congrArg F hda
    rw [map_sub]
    linear_combination (norm := module) -e1 - eFa + ec
  obtain ⟨a₁, ha₁, hda₁, c', hc', hac⟩ := hUs _ (U'.sub_mem ha' (hF.memU a ha)) hcy
  have hw₂ : w - D₁ a - D₁ a₁ ∈ W := W.sub_mem (W.sub_mem hw (hs.mem₁ a ha)) (hs.mem₁ a₁ ha₁)
  have hdw₂ : (D₀ + D₁) (w - D₁ a - D₁ a₁) = 0 := by
    have ea := hs.d_d₁ ha
    have ea₁ := hs.d_d₁ ha₁
    have ed := congrArg D₁ hda
    have ed₁ : D₁ (D₀ a₁) = 0 := by rw [hda₁, map_zero]
    simp only [LinearMap.add_apply, map_sub]
    linear_combination (norm := module) h1 - ea - ea₁ + ed + ed₁
  have hFw₂ : F (w - D₁ a - D₁ a₁) = (D₀' + D₁') (D₁' c' + b') := by
    have c1 := hF.comm₁ a
    have c2 := hF.comm₁ a₁
    have h := congrArg D₁' hac
    have ec' := hs'.d_d₁ hc'
    simp only [map_sub] at h
    simp only [LinearMap.add_apply, map_sub, map_add]
    linear_combination (norm := module) e2 - c1 - c2 - h - ec'
  obtain ⟨e, he, hde⟩ := hWi _ hw₂ hdw₂ _ (W'.add_mem (hs'.mem₁ c' hc') hb') hFw₂
  refine ⟨a + a₁ + e, Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left ha)
    (Submodule.mem_sup_left ha₁)) (Submodule.mem_sup_right he), ?_⟩
  simp only [LinearMap.add_apply, map_add] at hde ⊢
  linear_combination (norm := module) hda + hda₁ + hde

/-- **Two out of three, surjectivity**: a quasi-isomorphism on the subcomplex and on the
extension is surjective on the homology of the quotient. -/
theorem surj_of_sup (hWs : Surj W W' (D₀ + D₁) (D₀' + D₁') F)
    (hs_ : Surj (U ⊔ W) (U' ⊔ W') (D₀ + D₁) (D₀' + D₁') F)
    (hi_ : Inj (U ⊔ W) (U' ⊔ W') (D₀ + D₁) (D₀' + D₁') F) : Surj U U' D₀ D₀' F := by
  intro u' hu' h0'
  have hcy : (D₀' + D₁') (D₁' u') = 0 := by
    rw [LinearMap.add_apply, hs'.d_d₁ hu', h0', map_zero, neg_zero]
  obtain ⟨w₀, hw₀, hdw₀, b', hb', hwb⟩ := hWs _ (hs'.mem₁ u' hu') hcy
  simp only [LinearMap.add_apply] at hwb
  have hFw₀ : F w₀ = (D₀' + D₁') (u' + b') := by
    simp only [LinearMap.add_apply, map_add]
    linear_combination (norm := module) hwb - h0'
  obtain ⟨z, hz, hdz⟩ := hi_ w₀ (Submodule.mem_sup_right hw₀) hdw₀ _
    (Submodule.add_mem _ (Submodule.mem_sup_left hu') (Submodule.mem_sup_right hb')) hFw₀
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hz
  simp only [LinearMap.add_apply, map_add] at hdz
  obtain ⟨hda, hdac⟩ := eq_zero_of_add hs.disj (hs.mem₀ a ha)
    (W.sub_mem (W.add_mem (hs.mem₁ a ha) (hs.memW' hc)) hw₀)
    (by linear_combination (norm := module) hdz)
  have ht : (D₀' + D₁') (F a - u' + (F c - b')) = 0 := by
    have c0a := hF.comm₀ a
    have c1a := hF.comm₁ a
    have c0c := hF.comm₀ c
    have c1c := hF.comm₁ c
    have eF := congrArg F hdac
    have hda' : F (D₀ a) = 0 := by rw [hda, map_zero]
    simp only [map_sub, map_add, map_zero] at eF
    simp only [LinearMap.add_apply, map_sub, map_add]
    linear_combination (norm := module) -c0a + hda' - h0' - c1a - c0c - c1c + eF + hwb
  obtain ⟨x₂, hx₂, hdx₂, g', hg', hxg⟩ := hs_ _ (Submodule.add_mem _
    (Submodule.mem_sup_left (U'.sub_mem (hF.memU a ha) hu'))
    (Submodule.mem_sup_right (W'.sub_mem (hF.memW c hc) hb'))) ht
  obtain ⟨a₂, ha₂, c₂, hc₂, rfl⟩ := Submodule.mem_sup.1 hx₂
  obtain ⟨e', he', h', hh', rfl⟩ := Submodule.mem_sup.1 hg'
  have hda₂ := (hs.comps ha₂ hc₂ hdx₂).1
  simp only [LinearMap.add_apply, map_add] at hxg
  have hU : F a₂ - (F a - u') - D₀' e' = 0 := (eq_zero_of_add hs'.disj
    (U'.sub_mem (U'.sub_mem (hF.memU a₂ ha₂) (U'.sub_mem (hF.memU a ha) hu')) (hs'.mem₀ e' he'))
    (W'.sub_mem (W'.sub_mem (hF.memW c₂ hc₂) (W'.sub_mem (hF.memW c hc) hb'))
      (W'.add_mem (hs'.mem₁ e' he') (hs'.memW' hh')))
    (by linear_combination (norm := module) hxg)).1
  refine ⟨a - a₂, U.sub_mem ha ha₂, by rw [map_sub, hda, hda₂, sub_zero], -e', U'.neg_mem he', ?_⟩
  simp only [map_sub, map_neg]
  linear_combination (norm := module) -hU

/-- **Two out of three, injectivity**. -/
theorem inj_of_sup (hWs : Surj W W' (D₀ + D₁) (D₀' + D₁') F)
    (hWi : Inj W W' (D₀ + D₁) (D₀' + D₁') F)
    (hi_ : Inj (U ⊔ W) (U' ⊔ W') (D₀ + D₁) (D₀' + D₁') F) : Inj U U' D₀ D₀' F := by
  intro u hu h0 a' ha' hFu
  have hcy : (D₀ + D₁) (D₁ u) = 0 := by
    rw [LinearMap.add_apply, hs.d_d₁ hu, h0, map_zero, neg_zero]
  have hFd : F (D₁ u) = (D₀' + D₁') (-D₁' a') := by
    have c1 := hF.comm₁ u
    have eD := congrArg D₁' hFu
    have ea := hs'.d_d₁ ha'
    simp only [LinearMap.add_apply, map_neg]
    linear_combination (norm := module) c1 + eD + ea
  obtain ⟨w, hw, hdw⟩ := hWi _ (hs.mem₁ u hu) hcy _ (W'.neg_mem (hs'.mem₁ a' ha')) hFd
  rw [LinearMap.add_apply] at hdw
  have hdx : (D₀ + D₁) (u - w) = 0 := by
    simp only [LinearMap.add_apply, map_sub]
    linear_combination (norm := module) h0 - hdw
  have hc'm : F (u - w) - (D₀' + D₁') a' ∈ W' := by
    have : F (u - w) - (D₀' + D₁') a' = -(F w + D₁' a') := by
      simp only [LinearMap.add_apply, map_sub]
      linear_combination (norm := module) hFu
    rw [this]
    exact W'.neg_mem (W'.add_mem (hF.memW w hw) (hs'.mem₁ a' ha'))
  have hdc : (D₀' + D₁') (F (u - w) - (D₀' + D₁') a') = 0 := by
    have c0u := hF.comm₀ u
    have c1u := hF.comm₁ u
    have c0w := hF.comm₀ w
    have c1w := hF.comm₁ w
    have eFx := congrArg F hdx
    have edd := hs'.dd' a'
    simp only [LinearMap.add_apply, map_sub, map_add, map_zero] at eFx
    simp only [LinearMap.add_apply, map_sub, map_add]
    linear_combination (norm := module) -c0u - c1u + c0w + c1w + eFx - edd
  obtain ⟨w₁, hw₁, hdw₁, b', hb', hwb⟩ := hWs _ hc'm hdc
  have hFx₁ : F (u - w - w₁) = (D₀' + D₁') (a' - b') := by
    simp only [LinearMap.add_apply, map_sub] at hwb ⊢
    linear_combination (norm := module) -hwb
  obtain ⟨z, hz, hdz⟩ := hi_ _ (Submodule.sub_mem _ (Submodule.sub_mem _
    (Submodule.mem_sup_left hu) (Submodule.mem_sup_right hw)) (Submodule.mem_sup_right hw₁))
    (by rw [map_sub, hdx, hdw₁, sub_zero]) _
    (Submodule.sub_mem _ (Submodule.mem_sup_left ha') (Submodule.mem_sup_right hb')) hFx₁
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hz
  refine ⟨a, ha, ?_⟩
  simp only [LinearMap.add_apply, map_add] at hdz
  exact sub_eq_zero.1 (eq_zero_of_add hs.disj (U.sub_mem (hs.mem₀ a ha) hu)
    (W.add_mem (W.add_mem (W.add_mem (hs.mem₁ a ha) (hs.memW' hc)) hw) hw₁)
    (by linear_combination (norm := module) hdz)).1

/-- **Direct summands, surjectivity**: when `D₁` vanishes on `U`, a quasi-isomorphism on
`U ⊔ W` is surjective on the homology of `W`. -/
theorem surj_of_sup_right (hU : ∀ u ∈ U, D₁ u = 0) (hU' : ∀ u ∈ U', D₁' u = 0)
    (hs_ : Surj (U ⊔ W) (U' ⊔ W') (D₀ + D₁) (D₀' + D₁') F) :
    Surj W W' (D₀ + D₁) (D₀' + D₁') F := by
  intro y' hy' hdy
  obtain ⟨x, hx, hdx, z', hz', hxz⟩ := hs_ y' (Submodule.mem_sup_right hy') hdy
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 hz'
  obtain ⟨-, h1⟩ := hs.comps hu hw hdx
  rw [hU u hu, zero_add] at h1
  refine ⟨w, hw, by rw [LinearMap.add_apply]; exact h1, b', hb', ?_⟩
  simp only [LinearMap.add_apply, map_add] at hxz ⊢
  rw [hU' a' ha', add_zero] at hxz
  have := (eq_zero_of_add hs'.disj (U'.sub_mem (hF.memU u hu) (hs'.mem₀ a' ha'))
    (W'.sub_mem (W'.sub_mem (hF.memW w hw) hy') (hs'.memW' hb'))
    (by linear_combination (norm := module) hxz)).2
  linear_combination (norm := module) this

omit hs' hF in
/-- **Direct summands, injectivity**. -/
theorem inj_of_sup_right (hU : ∀ u ∈ U, D₁ u = 0)
    (hi_ : Inj (U ⊔ W) (U' ⊔ W') (D₀ + D₁) (D₀' + D₁') F) :
    Inj W W' (D₀ + D₁) (D₀' + D₁') F := by
  intro x hx hdx z' hz' hFx
  obtain ⟨z, hz, hdz⟩ := hi_ x (Submodule.mem_sup_right hx) hdx z' (Submodule.mem_sup_right hz') hFx
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hz
  refine ⟨c, hc, ?_⟩
  simp only [LinearMap.add_apply, map_add] at hdz ⊢
  rw [hU a ha, add_zero] at hdz
  have := (eq_zero_of_add hs.disj (hs.mem₀ a ha) (W.sub_mem (hs.memW' hc) hx)
    (by linear_combination (norm := module) hdz)).2
  linear_combination (norm := module) this

end Extension

/-! ## Finite filtrations -/

section Filtration

variable {D₀ D₁ : M →ₗ[R] M} {D₀' D₁' : M' →ₗ[R] M'} {F : M →ₗ[R] M'}
  (X S : ℕ → Submodule R M) (X' S' : ℕ → Submodule R M') (m : ℕ)

/-- **A filtered quasi-isomorphism**: a morphism of finite decreasing filtrations
`S p = X p ⊔ S (p + 1)`, split by the graded pieces, quasi-isomorphic on the graded pieces. -/
structure FiltData (D₀ D₁ : M →ₗ[R] M) (D₀' D₁' : M' →ₗ[R] M') (F : M →ₗ[R] M') : Prop where
  split : ∀ p, Split D₀ D₁ (X p) (S (p + 1))
  split' : ∀ p, Split D₀' D₁' (X' p) (S' (p + 1))
  hom : ∀ p, SplitHom F D₀ D₁ D₀' D₁' (X p) (S (p + 1)) (X' p) (S' (p + 1))
  sup : ∀ p, S p = X p ⊔ S (p + 1)
  sup' : ∀ p, S' p = X' p ⊔ S' (p + 1)
  top : S m = ⊥
  top' : S' m = ⊥

variable {X S X' S' m}

/-- **A quasi-isomorphism on the graded pieces of finite filtrations from `p₀` on is one on the
filtered modules from `p₀` on.** -/
theorem qiso_filt_ge (hd : FiltData X S X' S' m D₀ D₁ D₀' D₁' F) {p₀ : ℕ}
    (hs : ∀ p, p₀ ≤ p → Surj (X p) (X' p) D₀ D₀' F)
    (hi : ∀ p, p₀ ≤ p → Inj (X p) (X' p) D₀ D₀' F) (p : ℕ) (hp : p₀ ≤ p) :
    Surj (S p) (S' p) (D₀ + D₁) (D₀' + D₁') F ∧ Inj (S p) (S' p) (D₀ + D₁) (D₀' + D₁') F := by
  suffices h : ∀ j p, p₀ ≤ p → p + j = m →
      Surj (S p) (S' p) (D₀ + D₁) (D₀' + D₁') F ∧ Inj (S p) (S' p) (D₀ + D₁) (D₀' + D₁') F by
    rcases le_or_gt p m with hpm | hpm
    · exact h (m - p) p hp (by omega)
    · have hb : ∀ k, S (m + k) = ⊥ ∧ S' (m + k) = ⊥ := by
        intro k
        induction k with
        | zero => exact ⟨hd.top, hd.top'⟩
        | succ k ih =>
          refine ⟨eq_bot_iff.2 ?_, eq_bot_iff.2 ?_⟩
          · rw [← ih.1, hd.sup (m + k)]; exact le_sup_right
          · rw [← ih.2, hd.sup' (m + k)]; exact le_sup_right
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpm.le
      rw [(hb k).1, (hb k).2]
      exact ⟨surj_bot _ _ _, inj_bot _ _ _⟩
  intro j
  induction j with
  | zero =>
    intro p _ hp
    rw [add_zero] at hp
    subst hp
    rw [hd.top, hd.top']
    exact ⟨surj_bot _ _ _, inj_bot _ _ _⟩
  | succ j ih =>
    intro p hp₀ hp
    obtain ⟨h1, h2⟩ := ih (p + 1) (by omega) (by omega)
    rw [hd.sup p, hd.sup' p]
    exact ⟨surj_sup (hd.split p) (hd.split' p) (hd.hom p) (hs p hp₀) h1 h2,
      inj_sup (hd.split p) (hd.split' p) (hd.hom p) (hs p hp₀) (hi p hp₀) h2⟩

/-- **A quasi-isomorphism on the graded pieces of finite filtrations is one on the filtered
modules.** -/
theorem qiso_filt (hd : FiltData X S X' S' m D₀ D₁ D₀' D₁' F)
    (hs : ∀ p, Surj (X p) (X' p) D₀ D₀' F) (hi : ∀ p, Inj (X p) (X' p) D₀ D₀' F) (p : ℕ) :
    Surj (S p) (S' p) (D₀ + D₁) (D₀' + D₁') F ∧ Inj (S p) (S' p) (D₀ + D₁) (D₀' + D₁') F :=
  qiso_filt_ge hd (p₀ := 0) (fun p _ => hs p) (fun p _ => hi p) p (Nat.zero_le p)

end Filtration

/-! ## Retractions -/

section Retract

variable {D : M →ₗ[R] M} {D' : M' →ₗ[R] M'} {F : M →ₗ[R] M'} {S : Submodule R M}
  {S' : Submodule R M'} {r : M →ₗ[R] M} {r' : M' →ₗ[R] M'} {G : M →ₗ[R] M'} {K : M' →ₗ[R] M}

/-- **Retractions onto subcomplexes with the zero differential**: idempotents preserving the
submodules, killing the differential and killed by it, whose kernels are acyclic. -/
structure Retract (S : Submodule R M) (D r : M →ₗ[R] M) : Prop where
  mem : ∀ x ∈ S, r x ∈ S
  memD : ∀ x ∈ S, D x ∈ S
  rr : ∀ x, r (r x) = r x
  rD : ∀ x, r (D x) = 0
  Dr : ∀ x, D (r x) = 0
  acyc : ∀ x ∈ S, D x = 0 → r x = 0 → ∃ z ∈ S, D z = x

variable (hr : Retract S D r) (hr' : Retract S' D' r') (hFS : ∀ x ∈ S, F x ∈ S')
  (hFD : ∀ x, F (D x) = D' (F x)) (hG : ∀ x, r' (F (r x)) = G x)
include hr hr' hFS hFD hG

/-- **Comparison through retractions, surjectivity.** -/
theorem surj_of_retract (hKS : ∀ y ∈ S', K y ∈ S) (hGK : ∀ y ∈ S', G (K y) = r' y) :
    Surj S S' D D' F := by
  intro y' hy' hdy
  have hx : r (K (r' y')) ∈ S := hr.mem _ (hKS _ (hr'.mem _ hy'))
  have h1 : r' (F (r (K (r' y'))) - y') = 0 := by
    rw [map_sub, hG, hGK _ (hr'.mem _ hy'), hr'.rr, sub_self]
  have h2 : D' (F (r (K (r' y'))) - y') = 0 := by rw [map_sub, ← hFD, hr.Dr, map_zero, hdy,
    sub_self]
  obtain ⟨z', hz', hdz⟩ := hr'.acyc _ (S'.sub_mem (hFS _ hx) hy') h2 h1
  exact ⟨_, hx, hr.Dr _, z', hz', hdz.symm⟩

omit hFS in
/-- **Comparison through retractions, injectivity.** -/
theorem inj_of_retract (hKG : ∀ x ∈ S, K (G x) = r x) : Inj S S' D D' F := by
  intro x hx hdx z' hz' hFx
  obtain ⟨w, hw, hdw⟩ := hr.acyc (x - r x) (S.sub_mem hx (hr.mem x hx))
    (by rw [map_sub, hdx, hr.Dr, sub_self]) (by rw [map_sub, hr.rr, sub_self])
  have h0 : G (r x) = 0 := by
    rw [← hG, hr.rr]
    have : F (r x) = D' z' - D' (F w) := by rw [← hFD, hdw, map_sub, hFx]; abel
    rw [this, map_sub, hr'.rD, hr'.rD, sub_self]
  have h1 : r x = 0 := by rw [← hr.rr x, ← hKG _ (hr.mem x hx), h0, map_zero]
  exact ⟨w, hw, by rw [hdw, h1, sub_zero]⟩

omit hr hr' hFS hFD hG in
/-- A retraction for `D` is one for `-D`. -/
lemma Retract.neg (hr : Retract S D r) : Retract S (-D) r where
  mem := hr.mem
  memD x hx := by rw [LinearMap.neg_apply]; exact S.neg_mem (hr.memD x hx)
  rr := hr.rr
  rD x := by rw [LinearMap.neg_apply, map_neg, hr.rD, neg_zero]
  Dr x := by rw [LinearMap.neg_apply, hr.Dr, neg_zero]
  acyc x hx hdx hrx := by
    rw [LinearMap.neg_apply, neg_eq_zero] at hdx
    obtain ⟨z, hz, hdz⟩ := hr.acyc x hx hdx hrx
    exact ⟨-z, S.neg_mem hz, by rw [LinearMap.neg_apply, map_neg, neg_neg, hdz]⟩

end Retract

end QIso

end Operad
