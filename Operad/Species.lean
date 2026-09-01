/-
# Linear species

A symmetric operad is an operad in species, so this file builds the spine: species themselves,
their symmetric-group actions, and the endomorphism species that any symmetric operad theory has
to reproduce.

A **linear species** is a functor from the groupoid of finite sets and bijections to `R`-modules.
Indexing by finite *sets* rather than by `ℕ` is what makes the symmetric-group actions automatic:
`Aut S` acts on `F.obj S` by functoriality, with the action axioms coming from `F.map_id` and
`F.map_comp` rather than being imposed. The alternative — an `ℕ`-indexed family carrying an
explicit `Σₙ`-action — has to state and then carry those axioms by hand.

Modules are bundled as `ModuleCat R` so that a species is literally a functor.
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Core
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic

universe u

namespace Operad

open CategoryTheory

/-- The groupoid of finite sets and bijections. -/
abbrev FinBij : Type (u + 1) := Core FintypeCat.{u}

/-- A finite set, as an object of the groupoid. -/
abbrev FinBij.mk (S : Type u) [Finite S] : FinBij.{u} := ⟨FintypeCat.of S⟩

/-- A bijection of finite sets, as a morphism of the groupoid. -/
def FinBij.hom {S T : FintypeCat.{u}} (e : S ≃ T) : (⟨S⟩ : FinBij.{u}) ⟶ ⟨T⟩ :=
  ⟨FintypeCat.equivEquivIso e⟩

@[simp] lemma FinBij.hom_refl {S : FintypeCat.{u}} :
    FinBij.hom (Equiv.refl S) = 𝟙 (⟨S⟩ : FinBij.{u}) :=
  Core.hom_ext rfl

lemma FinBij.hom_trans {S T U : FintypeCat.{u}} (e : S ≃ T) (e' : T ≃ U) :
    FinBij.hom (e.trans e') = FinBij.hom e ≫ FinBij.hom e' :=
  Core.hom_ext rfl

/-- A linear species: an `R`-module for each finite set, functorial in bijections. -/
abbrev Species (R : Type u) [Ring R] : Type (u + 1) := FinBij.{u} ⥤ ModuleCat.{u} R

namespace Species

variable {R : Type u} [Ring R]

/-- The component of a species at a finite set. -/
abbrev component (F : Species R) (S : Type u) [Finite S] : ModuleCat.{u} R :=
  F.obj (FinBij.mk S)

/-- The arity-`n` component: the value at the standard `n`-element set. -/
abbrev arity (F : Species R) (n : ℕ) : ModuleCat.{u} R := F.component (ULift (Fin n))

/-- A bijection acts on the components of a species. -/
def act (F : Species R) {S T : Type u} [Finite S] [Finite T] (e : S ≃ T) :
    F.component S ⟶ F.component T :=
  F.map (FinBij.hom (S := FintypeCat.of S) (T := FintypeCat.of T) e)

@[simp] lemma act_refl (F : Species R) {S : Type u} [Finite S] :
    F.act (Equiv.refl S) = 𝟙 _ := by
  rw [act, FinBij.hom_refl, F.map_id]

lemma act_trans (F : Species R) {S T U : Type u} [Finite S] [Finite T] [Finite U]
    (e : S ≃ T) (e' : T ≃ U) : F.act (e.trans e') = F.act e ≫ F.act e' := by
  rw [act, act, act, ← F.map_comp]
  exact congrArg F.map (FinBij.hom_trans (S := FintypeCat.of S) (T := FintypeCat.of T)
    (U := FintypeCat.of U) e e')

/-- The symmetric-group action on a component, as a monoid homomorphism into automorphisms. The
action axioms are `map_id` and `map_comp`, not extra hypotheses. -/
def perm (F : Species R) (S : Type u) [Finite S] : Equiv.Perm S →* End (F.component S) where
  toFun e := F.act e
  map_one' := F.act_refl
  map_mul' e e' := F.act_trans e' e

/-! ### The endomorphism species

The test of the definition: the endomorphism species must exist, and its value at the standard
`n`-element set must be the arity-`n` part of the endomorphism operad. Functoriality is
`MultilinearMap.domDomCongr`, and both functor laws are definitional — `domDomCongr_trans` is
`rfl`, which is exactly the coherence a species needs. -/

/-- The endomorphism species of a module: a finite set `S` indexes the inputs of an `S`-ary
multilinear map, and a bijection relabels them. -/
noncomputable def endSpecies (R : Type u) [CommRing R] (V : Type u) [AddCommGroup V]
    [Module R V] : Species R where
  obj S := ModuleCat.of R (MultilinearMap R (fun _ : S.of => V) V)
  map f := ModuleCat.ofHom
    (MultilinearMap.domDomCongrLinearEquiv (R := R) (S := R) (M₂ := V) (M₃ := V)
      (FintypeCat.equivEquivIso.symm f.iso)).toLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The species spine reproduces the endomorphism operad.** The arity-`n` component of the
endomorphism species is the arity-`n` part of `Operad.End`, up to the relabelling
`ULift (Fin n) ≃ Fin n`. -/
noncomputable def endSpeciesArity (R : Type u) [CommRing R] (V : Type u) [AddCommGroup V]
    [Module R V] (n : ℕ) :
    ((endSpecies R V).arity n : Type u) ≃ₗ[R] MultilinearMap R (fun _ : Fin n => V) V :=
  MultilinearMap.domDomCongrLinearEquiv (R := R) (S := R) (M₂ := V) (M₃ := V) Equiv.ulift

end Species

end Operad
