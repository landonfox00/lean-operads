/-
# Homology, contractions and the homological perturbation lemma

The homological algebra underneath homotopy transfer, for modules with a square-zero
endomorphism. Gradings play no role: every statement is an identity between linear maps.

* `Homology d`: cycles modulo boundaries of `d` with `d ∘ d = 0`; a chain map induces a map on
  homology (`Homology.map`), functorially, and **homotopic chain maps induce the same map**
  (`Homology.map_eq_of_homotopy`).
* `Contraction dV dW`: a strong deformation retract `(ι, π, h)` of `(V, dV)` onto `(W, dW)`:
  chain maps with `π ι = 1`, `ι π = 1 + dV h + h dV`, and the side conditions `h ι = 0`,
  `π h = 0`, `h h = 0`. **`ι` and `π` induce mutually inverse isomorphisms on homology**
  (`Contraction.homologyEquiv`).
* **The homological perturbation lemma** (`Contraction.perturb`): if `dV + δ` is again a
  differential and `1 - δ h` is invertible, with inverse `κ`, then with `A = κ δ`,
  `ι' = ι + h A ι`, `π' = π + π A h`, `h' = h + h A h` is a contraction of `(V, dV + δ)` onto
  `(W, dW + π A ι)`. The key identity is `dV A + A dV + A ι π A = 0`
  (`Contraction.perturb_key`).
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

universe u v w x

namespace Operad

/-! ## Homology -/

section Homology

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {W : Type w} [AddCommGroup W] [Module R W] {U : Type x} [AddCommGroup U] [Module R U]

/-- The boundaries of `d`, as a submodule of its cycles. -/
def boundariesIn (d : V →ₗ[R] V) : Submodule R (LinearMap.ker d) :=
  (LinearMap.range d).comap (LinearMap.ker d).subtype

variable (R) in
/-- **The homology** of a module with an endomorphism `d`: the cycles modulo the boundaries
(meaningful when `d ∘ d = 0`). -/
abbrev Homology (d : V →ₗ[R] V) : Type v := LinearMap.ker d ⧸ boundariesIn d

namespace Homology

/-- The class of a cycle. -/
def mk (d : V →ₗ[R] V) : LinearMap.ker d →ₗ[R] Homology R d := (boundariesIn d).mkQ

lemma mk_eq_mk_iff {d : V →ₗ[R] V} (z z' : LinearMap.ker d) :
    mk d z = mk d z' ↔ ∃ v, d v = z.1 - z'.1 := by
  rw [mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simp [boundariesIn, Submodule.mem_comap, LinearMap.mem_range]

lemma mk_surjective (d : V →ₗ[R] V) : Function.Surjective (mk d) :=
  Submodule.mkQ_surjective _

lemma mk_boundary {d : V →ₗ[R] V} (hd : ∀ v, d (d v) = 0) (v : V) :
    mk d ⟨d v, hd v⟩ = 0 := by
  rw [mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨v, rfl⟩

/-- A chain map sends cycles to cycles. -/
def cycleMap {dV : V →ₗ[R] V} {dW : W →ₗ[R] W} (f : V →ₗ[R] W) (hf : ∀ v, f (dV v) = dW (f v)) :
    LinearMap.ker dV →ₗ[R] LinearMap.ker dW :=
  f.restrict fun v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← hf, hv, map_zero]

/-- **The map induced on homology by a chain map.** -/
def map {dV : V →ₗ[R] V} {dW : W →ₗ[R] W} (f : V →ₗ[R] W) (hf : ∀ v, f (dV v) = dW (f v)) :
    Homology R dV →ₗ[R] Homology R dW :=
  Submodule.mapQ _ _ (cycleMap f hf) fun z hz => by
    obtain ⟨v, hv⟩ := hz
    exact ⟨f v, by rw [← hf, hv]; rfl⟩

@[simp] lemma map_mk {dV : V →ₗ[R] V} {dW : W →ₗ[R] W} (f : V →ₗ[R] W)
    (hf : ∀ v, f (dV v) = dW (f v)) (z : LinearMap.ker dV) :
    map f hf (mk dV z) = mk dW (cycleMap f hf z) := rfl

lemma map_id (dV : V →ₗ[R] V) : map (dV := dV) LinearMap.id (fun _ => rfl) = LinearMap.id := by
  ext z
  rfl

lemma map_comp {dV : V →ₗ[R] V} {dW : W →ₗ[R] W} {dU : U →ₗ[R] U} (f : V →ₗ[R] W)
    (hf : ∀ v, f (dV v) = dW (f v)) (g : W →ₗ[R] U) (hg : ∀ w, g (dW w) = dU (g w)) :
    map (g ∘ₗ f) (fun v => by simp [hf, hg]) = map g hg ∘ₗ map f hf := by
  ext z
  rfl

/-- **Homotopic chain maps induce the same map on homology.** -/
theorem map_eq_of_homotopy {dV : V →ₗ[R] V} {dW : W →ₗ[R] W} (f g : V →ₗ[R] W)
    (hf : ∀ v, f (dV v) = dW (f v)) (hg : ∀ v, g (dV v) = dW (g v)) (s : V →ₗ[R] W)
    (hs : ∀ v, f v - g v = dW (s v) + s (dV v)) : map f hf = map g hg := by
  ext z
  show map f hf (mk dV z) = map g hg (mk dV z)
  rw [map_mk, map_mk, mk_eq_mk_iff]
  refine ⟨s z.1, ?_⟩
  have hz : dV z.1 = 0 := z.2
  rw [show (cycleMap f hf z).1 = f z.1 from rfl, show (cycleMap g hg z).1 = g z.1 from rfl, hs,
    hz, map_zero, add_zero]

end Homology

end Homology

/-! ## Contractions -/

/-- **A contraction** (strong deformation retract) of `(V, dV)` onto `(W, dW)`: chain maps
`ι : W → V` and `π : V → W` with `π ι = 1` and `ι π = 1 + dV h + h dV`, satisfying the side
conditions `h ι = 0`, `π h = 0` and `h h = 0`. -/
structure Contraction {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type w} [AddCommGroup W] [Module R W] (dV : V →ₗ[R] V) (dW : W →ₗ[R] W) where
  /-- The inclusion. -/
  ι : W →ₗ[R] V
  /-- The projection. -/
  π : V →ₗ[R] W
  /-- The homotopy. -/
  h : V →ₗ[R] V
  ι_comm : ∀ w, dV (ι w) = ι (dW w)
  π_comm : ∀ v, π (dV v) = dW (π v)
  π_ι : ∀ w, π (ι w) = w
  ι_π : ∀ v, ι (π v) = v + dV (h v) + h (dV v)
  h_ι : ∀ w, h (ι w) = 0
  π_h : ∀ v, π (h v) = 0
  h_h : ∀ v, h (h v) = 0

namespace Contraction

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {W : Type w} [AddCommGroup W] [Module R W] {dV : V →ₗ[R] V} {dW : W →ₗ[R] W}

/-- **A contraction induces an isomorphism on homology**, by `π`, with inverse induced by `ι`. -/
def homologyEquiv (c : Contraction dV dW) : Homology R dV ≃ₗ[R] Homology R dW :=
  LinearEquiv.ofLinear (Homology.map c.π c.π_comm) (Homology.map c.ι fun w => (c.ι_comm w).symm)
    (by
      rw [← Homology.map_comp, ← Homology.map_id dW]
      congr 1
      exact LinearMap.ext c.π_ι)
    (by
      rw [← Homology.map_comp, ← Homology.map_id dV]
      exact Homology.map_eq_of_homotopy _ _ _ _ c.h fun v => by
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply, c.ι_π]
        abel)

/-! ## The homological perturbation lemma -/

variable (c : Contraction dV dW) (δ κ : V →ₗ[R] V)

/-- The perturbation series `A = κ δ`, where `κ` inverts `1 - δ h`. -/
def pA : V →ₗ[R] V := κ ∘ₗ δ

variable {c δ κ}

section Key

variable (hκ₁ : ∀ v, κ (v - δ (c.h v)) = v) (hκ₂ : ∀ v, κ v - δ (c.h (κ v)) = v)
include hκ₁ hκ₂

omit hκ₁ in
/-- `A = δ + δ h A`. -/
lemma pA_eq_left (v : V) : pA δ κ v = δ v + δ (c.h (pA δ κ v)) :=
  sub_eq_iff_eq_add.mp (hκ₂ (δ v))

omit hκ₂ in
/-- `A = δ + A h δ`. -/
lemma pA_eq_right (v : V) : pA δ κ v = δ v + pA δ κ (c.h (δ v)) := by
  have := hκ₁ (δ v)
  rw [map_sub] at this
  exact sub_eq_iff_eq_add.mp this

variable (hdV : ∀ v, dV (dV v) = 0) (hδ : ∀ v, dV (dV v) + dV (δ v) + δ (dV v) + δ (δ v) = 0)
include hdV hδ

/-- **The key identity of the perturbation lemma**: `dV A + A dV + A ι π A = 0`. -/
theorem perturb_key (v : V) :
    dV (pA δ κ v) + pA δ κ (dV v) + pA δ κ (c.ι (c.π (pA δ κ v))) = 0 := by
  set A := pA δ κ with hAdef
  have hL : ∀ z, A z - δ (c.h (A z)) = δ z := fun z => by
    have := pA_eq_left (c := c) hκ₂ z
    linear_combination (norm := module) this
  set M : V → V := fun z => dV (A z) + A (dV z) + A (c.ι (c.π (A z))) with hMdef
  -- `1 - δ h` kills `M (1 - h δ)`
  have h1 : ∀ x, M (x - c.h (δ x)) - δ (c.h (M (x - c.h (δ x)))) = 0 := by
    intro x
    have hAy : A (x - c.h (δ x)) = δ x := by
      rw [map_sub, pA_eq_right (c := c) hκ₁ x]
      abel
    calc M (x - c.h (δ x)) - δ (c.h (M (x - c.h (δ x))))
        = dV (δ x) - δ (c.h (dV (δ x)))
          + (A (dV (x - c.h (δ x))) - δ (c.h (A (dV (x - c.h (δ x))))))
          + (A (c.ι (c.π (δ x))) - δ (c.h (A (c.ι (c.π (δ x)))))) := by
            simp only [hMdef, hAy, map_add]
            abel
      _ = dV (δ x) - δ (c.h (dV (δ x))) + δ (dV (x - c.h (δ x))) + δ (c.ι (c.π (δ x))) := by
            rw [hL, hL]
      _ = dV (δ x) + δ (dV x) + δ (δ x) := by
            rw [c.ι_π]
            simp only [map_add, map_sub]
            abel
      _ = 0 := by
            have := hδ x
            rw [hdV] at this
            linear_combination (norm := module) this
  -- and `1 - h δ` has a right inverse
  have hw : (v + c.h (κ (δ v))) - c.h (δ (v + c.h (κ (δ v)))) = v := by
    have e := congrArg c.h (hκ₂ (δ v))
    simp only [map_add, map_sub] at e ⊢
    linear_combination (norm := module) e
  have h2 := h1 (v + c.h (κ (δ v)))
  rw [hw] at h2
  have h3 := congrArg κ h2
  rw [hκ₁, map_zero] at h3
  exact h3

end Key

variable (hκ₁ : ∀ v, κ (v - δ (c.h v)) = v) (hκ₂ : ∀ v, κ v - δ (c.h (κ v)) = v)
  (hdV : ∀ v, dV (dV v) = 0) (hδ : ∀ v, dV (dV v) + dV (δ v) + δ (dV v) + δ (δ v) = 0)

include hκ₁ hκ₂ hdV hδ in
/-- **The perturbed differential on `W` squares to zero.** -/
theorem perturb_dW_dW (hdW : ∀ w, dW (dW w) = 0) (w : W) :
    (dW + c.π ∘ₗ pA δ κ ∘ₗ c.ι) ((dW + c.π ∘ₗ pA δ κ ∘ₗ c.ι) w) = 0 := by
  have key := congrArg c.π (perturb_key hκ₁ hκ₂ hdV hδ (c.ι w))
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, map_add, hdW,
    ← c.π_comm, ← c.ι_comm, map_zero] at key ⊢
  linear_combination (norm := module) key

/-- **The homological perturbation lemma.** If `dV + δ` is a differential and `κ` inverts
`1 - δ h`, then with `A = κ δ`, `(ι + h A ι, π + π A h, h + h A h)` is a contraction of
`(V, dV + δ)` onto `(W, dW + π A ι)`. -/
def perturb : Contraction (dV + δ) (dW + c.π ∘ₗ pA δ κ ∘ₗ c.ι) where
  ι := c.ι + c.h ∘ₗ pA δ κ ∘ₗ c.ι
  π := c.π + c.π ∘ₗ pA δ κ ∘ₗ c.h
  h := c.h + c.h ∘ₗ pA δ κ ∘ₗ c.h
  ι_comm w := by
    have key := congrArg c.h (perturb_key hκ₁ hκ₂ hdV hδ (c.ι w))
    have hL := pA_eq_left (c := c) hκ₂ (c.ι w)
    have f1 := c.ι_comm w
    have f2 := congrArg (fun t => c.h (pA δ κ t)) f1
    have e := c.ι_π (pA δ κ (c.ι w))
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, map_add,
      map_zero] at key f2 ⊢
    linear_combination (norm := module) f1 - e + f2 - hL - key
  π_comm v := by
    have key := congrArg c.π (perturb_key hκ₁ hκ₂ hdV hδ (c.h v))
    have hR := congrArg c.π (pA_eq_right (c := c) hκ₁ v)
    have g1 := c.π_comm v
    have g2 := c.π_comm (pA δ κ (c.h v))
    have e1 := congrArg (fun t => c.π (pA δ κ t)) (c.ι_π v)
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, map_add,
      map_zero] at key hR e1 ⊢
    linear_combination (norm := module) g1 + g2 - e1 - hR - key
  π_ι w := by
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, map_add, c.π_ι,
      c.π_h, c.h_ι, c.h_h, map_zero, add_zero]
  ι_π v := by
    have key := congrArg c.h (perturb_key hκ₁ hκ₂ hdV hδ (c.h v))
    have hL := pA_eq_left (c := c) hκ₂ (c.h v)
    have hR := congrArg c.h (pA_eq_right (c := c) hκ₁ v)
    have e1 := c.ι_π v
    have e2 := c.ι_π (pA δ κ (c.h v))
    have e3 := congrArg (fun t => c.h (pA δ κ t)) (c.ι_π v)
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, map_add,
      map_zero] at key hR e3 ⊢
    linear_combination (norm := module) e1 + e2 + e3 + hL + hR + key
  h_ι w := by
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, map_add, c.h_ι,
      c.h_h, map_zero, add_zero]
  π_h v := by
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, map_add, c.π_h,
      c.h_h, map_zero, add_zero]
  h_h v := by
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, map_add, c.h_h,
      map_zero, add_zero]

end Contraction

end Operad
