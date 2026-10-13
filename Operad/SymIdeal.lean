/-
# Ideals of symmetric operads, and kernels

An *ideal* of a symmetric operad `P` in `R`-modules is a family of submodules `I A ⊆ P A`, stable
under relabelling, such that a partial composite lies in `I` as soon as either factor does. The
kernel of a morphism of operads is an ideal (`SymOperadHom.ker`), and so the cochains with values
in an ideal are what the deformation theory of Part III restricts to: the kernel of the coordinate
sum `Σ : Perm → Com` is an ideal of `Perm` (`Sym.Perm.kerSum`), the ideal of standard
representations.
-/
import Operad.Sym

universe u v w

namespace Operad

open Sym

/-- **An ideal of a symmetric operad.** -/
structure SymOperadIdeal (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P] where
  /-- The component at a finite input set. -/
  sub (A : Type) [Fintype A] [DecidableEq A] : Submodule R (P A)
  map_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    {x : P A} : x ∈ sub A → SymOperad.map (R := R) e x ∈ sub B
  comp_mem_left {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    {x : P A} (y : P B) : x ∈ sub A → SymOperad.comp (R := R) i x y ∈ sub (Without A i ⊕ B)
  comp_mem_right {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : P A) {y : P B} : y ∈ sub B → SymOperad.comp (R := R) i x y ∈ sub (Without A i ⊕ B)

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **The kernel of a morphism of operads is an ideal.** -/
def SymOperadHom.ker (f : SymOperadHom R P Q) : SymOperadIdeal R P where
  sub A _ _ := LinearMap.ker (f.app A)
  map_mem := by
    intro A B _ _ _ _ e x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [f.app_map, hx, map_zero]
  comp_mem_left := by
    intro A B _ _ _ _ i x y hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [f.app_comp, hx, map_zero, LinearMap.zero_apply]
  comp_mem_right := by
    intro A B _ _ _ _ i x y hy
    rw [LinearMap.mem_ker] at hy ⊢
    rw [f.app_comp, hy, map_zero]

@[simp] lemma SymOperadHom.mem_ker (f : SymOperadHom R P Q) {A : Type} [Fintype A]
    [DecidableEq A] (x : P A) : x ∈ f.ker.sub A ↔ f.app A x = 0 :=
  LinearMap.mem_ker

/-- **The ideal of standard representations**: the sum-zero vectors, the kernel of
`Σ : Perm → Com`. -/
def Sym.Perm.kerSum (R : Type u) [CommRing R] : SymOperadIdeal R (Perm R) :=
  (Perm.sumHom R).ker

lemma Sym.Perm.mem_kerSum {A : Type} [Fintype A] [DecidableEq A] (x : Perm R A) :
    x ∈ (kerSum R).sub A ↔ ∑ a, x a = 0 :=
  SymOperadHom.mem_ker _ x

end Operad
