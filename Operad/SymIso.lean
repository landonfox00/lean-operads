/-
# Isomorphisms of symmetric operads

* The unit and associativity laws for composites of morphisms (`SymOperadHom.comp_id`,
  `SymOperadHom.id_comp`, `SymOperadHom.comp_assoc`).
* `SymOperadIso`: morphisms both ways, inverse to each other, with `symm`, `trans`, the
  componentwise linear equivalences, and `SymOperadIso.ofBijective`: a morphism with bijective
  components is an isomorphism.
-/
import Operad.Sym

universe u v w w'

namespace Operad

open Sym

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]
  {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type w'}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (S A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (S A)] [SymOperad R S]

namespace SymOperadHom

@[simp] lemma id_app (A : Type) [Fintype A] [DecidableEq A] (x : P A) :
    (SymOperadHom.id : SymOperadHom R P P).app A x = x := rfl

@[simp] lemma comp_id (φ : SymOperadHom R P Q) : φ.comp SymOperadHom.id = φ :=
  ext fun _ _ _ _ => rfl

@[simp] lemma id_comp (φ : SymOperadHom R P Q) : SymOperadHom.id.comp φ = φ :=
  ext fun _ _ _ _ => rfl

lemma comp_assoc {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (T A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (T A)] [SymOperad R T]
    (χ : SymOperadHom R S T) (ψ : SymOperadHom R Q S) (φ : SymOperadHom R P Q) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) :=
  ext fun _ _ _ _ => rfl

end SymOperadHom

variable (R P Q) in
/-- **An isomorphism of symmetric operads.** -/
structure SymOperadIso where
  /-- The forward morphism. -/
  hom : SymOperadHom R P Q
  /-- The inverse morphism. -/
  inv : SymOperadHom R Q P
  hom_inv_id : inv.comp hom = SymOperadHom.id
  inv_hom_id : hom.comp inv = SymOperadHom.id

namespace SymOperadIso

@[simp] lemma inv_hom_apply (e : SymOperadIso R P Q) (A : Type) [Fintype A] [DecidableEq A]
    (x : P A) : e.inv.app A (e.hom.app A x) = x :=
  congrArg (fun φ : SymOperadHom R P P => φ.app A x) e.hom_inv_id

@[simp] lemma hom_inv_apply (e : SymOperadIso R P Q) (A : Type) [Fintype A] [DecidableEq A]
    (y : Q A) : e.hom.app A (e.inv.app A y) = y :=
  congrArg (fun φ : SymOperadHom R Q Q => φ.app A y) e.inv_hom_id

/-- The identity isomorphism. -/
def refl : SymOperadIso R P P :=
  ⟨SymOperadHom.id, SymOperadHom.id, SymOperadHom.id_comp _, SymOperadHom.id_comp _⟩

/-- The inverse isomorphism. -/
def symm (e : SymOperadIso R P Q) : SymOperadIso R Q P :=
  ⟨e.inv, e.hom, e.inv_hom_id, e.hom_inv_id⟩

/-- The composite of two isomorphisms. -/
def trans (e : SymOperadIso R P Q) (f : SymOperadIso R Q S) : SymOperadIso R P S where
  hom := f.hom.comp e.hom
  inv := e.inv.comp f.inv
  hom_inv_id := SymOperadHom.ext fun A _ _ x => by simp
  inv_hom_id := SymOperadHom.ext fun A _ _ y => by simp

/-- The components of an isomorphism, as linear equivalences. -/
def linearEquiv (e : SymOperadIso R P Q) (A : Type) [Fintype A] [DecidableEq A] :
    P A ≃ₗ[R] Q A :=
  LinearEquiv.ofLinear (e.hom.app A) (e.inv.app A) (LinearMap.ext fun y => e.hom_inv_apply A y)
    (LinearMap.ext fun x => e.inv_hom_apply A x)

@[simp] lemma linearEquiv_apply (e : SymOperadIso R P Q) (A : Type) [Fintype A] [DecidableEq A]
    (x : P A) : e.linearEquiv A x = e.hom.app A x := rfl

/-- The components of an isomorphism are bijective. -/
lemma bijective (e : SymOperadIso R P Q) (A : Type) [Fintype A] [DecidableEq A] :
    Function.Bijective (e.hom.app A) :=
  (e.linearEquiv A).bijective

/-- **A morphism with bijective components is an isomorphism.** -/
noncomputable def ofBijective (φ : SymOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (φ.app A)) :
    SymOperadIso R P Q where
  hom := φ
  inv := φ.invOfBijective h
  hom_inv_id := SymOperadHom.ext fun A _ _ x => SymOperadHom.invOfBijective_app φ h A x
  inv_hom_id := SymOperadHom.ext fun A _ _ y => SymOperadHom.app_invOfBijective φ h A y

@[simp] lemma ofBijective_hom (φ : SymOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (φ.app A)) :
    (ofBijective φ h).hom = φ := rfl

end SymOperadIso

end Operad
