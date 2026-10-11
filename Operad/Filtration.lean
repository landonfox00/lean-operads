/-
# Suboperads and filtered symmetric operads

* `SymSuboperad`: a family of submodules stable under relabelling and composition and containing
  the unit; the image of a morphism is one (`SymOperadHom.range`).
* `SymOperadFiltration`: an increasing, exhaustive family of submodules `F p A ⊆ P A`, stable under
  relabelling, with the unit in degree zero and `F p ∘ᵢ F q ⊆ F (p + q)`. Its degree-zero part is
  a suboperad (`SymOperadFiltration.zero`).
* `weightFiltration`: a weight on a set operad which is invariant under relabelling, zero on the
  unit and subadditive under composition filters the linearization, `F p` being spanned by the
  operations of weight at most `p`.
* `SymOperadFiltration.map`: a filtration transports along a morphism with surjective components.
-/
import Operad.SetOperad
import Mathlib.LinearAlgebra.Finsupp.Supported

universe u v w

namespace Operad

open Sym

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

variable (R P) in
/-- **A suboperad of a symmetric operad.** -/
structure SymSuboperad where
  /-- The component at a finite input set. -/
  sub (A : Type) [Fintype A] [DecidableEq A] : Submodule R (P A)
  map_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    {x : P A} : x ∈ sub A → SymOperad.map (R := R) e x ∈ sub B
  one_mem : SymOperad.one R ∈ sub Unit
  comp_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    {x : P A} {y : P B} :
    x ∈ sub A → y ∈ sub B → SymOperad.comp (R := R) i x y ∈ sub (Without A i ⊕ B)

/-- **The image of a morphism is a suboperad.** -/
def SymOperadHom.range (f : SymOperadHom R P Q) : SymSuboperad R Q where
  sub A _ _ := LinearMap.range (f.app A)
  map_mem := by
    rintro A B _ _ _ _ e _ ⟨x, rfl⟩
    exact ⟨SymOperad.map (R := R) e x, f.app_map e x⟩
  one_mem := ⟨SymOperad.one R, f.app_one⟩
  comp_mem := by
    rintro A B _ _ _ _ i _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨SymOperad.comp (R := R) i x y, f.app_comp i x y⟩

variable (R P) in
/-- **A filtration of a symmetric operad**, increasing and exhaustive, with
`F p ∘ᵢ F q ⊆ F (p + q)`. -/
structure SymOperadFiltration where
  /-- The operations of filtration degree at most `p`. -/
  F (p : ℕ) (A : Type) [Fintype A] [DecidableEq A] : Submodule R (P A)
  mono {p q : ℕ} (h : p ≤ q) (A : Type) [Fintype A] [DecidableEq A] : F p A ≤ F q A
  map_mem {p : ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) {x : P A} : x ∈ F p A → SymOperad.map (R := R) e x ∈ F p B
  one_mem : SymOperad.one R ∈ F 0 Unit
  comp_mem {p q : ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) {x : P A} {y : P B} :
    x ∈ F p A → y ∈ F q B → SymOperad.comp (R := R) i x y ∈ F (p + q) (Without A i ⊕ B)
  exhaustive {A : Type} [Fintype A] [DecidableEq A] (x : P A) : ∃ p, x ∈ F p A

namespace SymOperadFiltration

/-- **The degree-zero part of a filtration is a suboperad.** -/
def zero (Φ : SymOperadFiltration R P) : SymSuboperad R P where
  sub A _ _ := Φ.F 0 A
  map_mem := by
    intro A B _ _ _ _ e x hx
    exact Φ.map_mem e hx
  one_mem := Φ.one_mem
  comp_mem := by
    intro A B _ _ _ _ i x y hx hy
    exact Φ.comp_mem i hx hy

/-- **A filtration transports along a morphism with surjective components**: the image of the
filtration is a filtration of the target. -/
def map (Φ : SymOperadFiltration R P) (f : SymOperadHom R P Q)
    (hf : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Surjective (f.app A)) :
    SymOperadFiltration R Q where
  F p A _ _ := (Φ.F p A).map (f.app A)
  mono h A _ _ := Submodule.map_mono (Φ.mono h A)
  map_mem := by
    rintro p A B _ _ _ _ e _ ⟨x, hx, rfl⟩
    exact ⟨SymOperad.map (R := R) e x, Φ.map_mem e hx, f.app_map e x⟩
  one_mem := ⟨SymOperad.one R, Φ.one_mem, f.app_one⟩
  comp_mem := by
    rintro p q A B _ _ _ _ i _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨SymOperad.comp (R := R) i x y, Φ.comp_mem i hx hy, f.app_comp i x y⟩
  exhaustive := by
    intro A _ _ y
    obtain ⟨x, rfl⟩ := hf A y
    obtain ⟨p, hp⟩ := Φ.exhaustive x
    exact ⟨p, x, hp, rfl⟩

lemma mem_map (Φ : SymOperadFiltration R P) (f : SymOperadHom R P Q)
    (hf : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Surjective (f.app A)) {p : ℕ}
    {A : Type} [Fintype A] [DecidableEq A] (x : P A) (hx : x ∈ Φ.F p A) :
    f.app A x ∈ (Φ.map f hf).F p A :=
  ⟨x, hx, rfl⟩

end SymOperadFiltration

/-! ## The filtration of a linearization by a weight -/

section Weight

variable (R) {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]

/-- **The filtration by a weight**: `F p` is spanned by the operations of weight at most `p`. For
a weight invariant under relabelling, zero on the unit and subadditive under composition, this is
a filtration of the linearization. -/
noncomputable def weightFiltration (w : ∀ (A : Type) [Fintype A] [DecidableEq A], S A → ℕ)
    (hmap : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (s : S A), w B (SetOperad.map e s) = w A s)
    (hone : w Unit SetOperad.one = 0)
    (hcomp : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (s : S A) (t : S B), w _ (SetOperad.comp i s t) ≤ w A s + w B t) :
    SymOperadFiltration R (Lin R S) where
  F p A _ _ := Finsupp.supported R R {s | w A s ≤ p}
  mono h A _ _ := Finsupp.supported_mono fun s (hs : _ ≤ _) => le_trans hs h
  map_mem := by
    classical
    intro p A B _ _ _ _ e x hx
    rw [Finsupp.mem_supported] at hx ⊢
    intro b hb
    show w B b ≤ p
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hb)
    rw [hmap]
    exact hx ha
  one_mem := by
    rw [Finsupp.mem_supported]
    intro s hs
    show w Unit s ≤ 0
    have : s = SetOperad.one := by
      by_contra h
      exact (Finsupp.mem_support_iff.1 hs) (Finsupp.single_eq_of_ne h)
    rw [this, hone]
  comp_mem := by
    intro p q A B _ _ _ _ i x y hx hy
    rw [Finsupp.supported_eq_span_single] at hx hy
    induction hx using Submodule.span_induction with
    | mem s hs =>
      induction hy using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨s, hs, rfl⟩ := hs
        obtain ⟨t, ht, rfl⟩ := ht
        show Lin.compL R i (Finsupp.single s 1) (Finsupp.single t 1) ∈ _
        rw [Lin.compL_single]
        exact Finsupp.single_mem_supported R _
          (le_trans (hcomp i s t) (Nat.add_le_add hs ht))
      | zero => simp
      | add y y' _ _ hy hy' => simpa only [map_add] using Submodule.add_mem _ hy hy'
      | smul r y _ hy => simpa only [map_smul] using Submodule.smul_mem _ r hy
    | zero => simp
    | add x x' _ _ hx hx' =>
      simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ hx hx'
    | smul r x _ hx =>
      simpa only [map_smul, LinearMap.smul_apply] using Submodule.smul_mem _ r hx
  exhaustive := by
    intro A _ _ x
    refine ⟨x.support.sup (w A), ?_⟩
    rw [Finsupp.mem_supported]
    intro s hs
    exact Finset.le_sup (f := w A) hs

end Weight

end Operad
