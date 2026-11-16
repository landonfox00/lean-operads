/-
# The free operad on a linearized set species

The library has two free constructions on a species: the free set operad `FreeSp X` on a set
species `X`, and the free operad in modules `FreeL R V` on a linear species `V`, a quotient of the
linearization of `FreeSp` of the underlying set species of `V` (`Operad/FreeSpecies.lean`). This
file compares them on the linearization of a set species.

* **The linearization of a set species** (`LinSp R X`): the free modules `X A →₀ R`, relabelled
  through `X`, with basis elements `LinSp.single R x`. A morphism of linear species out of it is a
  morphism of set species out of `X` into the underlying set species (`LinSp.homEquiv`).
* **The comparison** (`FreeL.linIso`): the free operad on the linearization of `X` is the
  linearization of the free set operad on `X`,

    `FreeL R (LinSp R X) ≅ Lin R (FreeSp X)`,

  an isomorphism of symmetric operads sending the generator of a basis element `x` to the basis
  element of the generator `x` (`FreeL.toLin_ι`, `FreeL.ofLin_single`). Both sides have the same
  universal property: `FreeL.homEquiv` and `LinSp.homEquiv` on the left, `linHomEquiv` and
  `FreeSp.homEquiv` on the right.
* **A basis** (`FreeL.linBasis`): the free operad on `LinSp R X` has in each arity a basis indexed
  by the free set operad on `X`, whose vectors at the generators of `X` are the generators
  (`FreeL.linBasis_ι`), and its rank is the number of operations of `FreeSp X` when these are
  finitely many (`FreeL.finrank_linSp`).
-/
import Operad.FreeSpecies
import Operad.SymIso
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

universe u v w

namespace Operad

open Sym

/-! ## The linearization of a set species -/

/-- **The linearization of a set species**: the free modules on its values. It is a definition
and not an abbreviation of `Lin`: on a set operad `Lin` carries the species structure of an
operad in modules, and the two would be found by different instance paths. -/
def LinSp (R : Type u) [CommRing R]
    (X : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type (max u v) :=
  fun A _ _ => X A →₀ R

section LinSp

variable (R : Type u) [CommRing R]
  (X : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (LinSp R X A) :=
  inferInstanceAs (AddCommGroup (X A →₀ R))

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : Module R (LinSp R X A) :=
  inferInstanceAs (Module R (X A →₀ R))

variable [SetSpecies X]

/-- **The linearization of a set species is a linear species**, relabelled through the
species. -/
noncomputable instance instSymSpeciesLinSp : SymSpecies R (LinSp R X) where
  map e := Finsupp.lmapDomain R R (SetSpecies.map e)
  map_refl x := by
    show Finsupp.mapDomain (SetSpecies.map (Equiv.refl _)) x = x
    rw [Finsupp.mapDomain_congr (g := id) (fun s _ => SetSpecies.map_refl s),
      Finsupp.mapDomain_id]
  map_trans e f x := by
    show Finsupp.mapDomain _ x = Finsupp.mapDomain _ (Finsupp.mapDomain _ x)
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun s _ => SetSpecies.map_trans e f s

namespace LinSp

variable {X} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **A basis element of the linearization.** -/
noncomputable def single (x : X A) : LinSp R X A := Finsupp.single x 1

variable {R}

/-- Relabelling a basis element relabels it in the species. -/
lemma map_single (e : A ≃ B) (x : X A) :
    SymSpecies.map (R := R) e (single R x) = single R (SetSpecies.map e x) :=
  Finsupp.mapDomain_single

omit [SetSpecies X] in
/-- Two linear maps out of the linearization agree when they agree on the basis elements. -/
lemma lhom_ext {M : Type*} [AddCommGroup M] [Module R M] {f g : LinSp R X A →ₗ[R] M}
    (h : ∀ x, f (single R x) = g (single R x)) : f = g :=
  Finsupp.lhom_ext' fun x => LinearMap.ext_ring (h x)

variable {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [SymSpecies R V]

omit [SetSpecies X] [SymSpecies R V] in
/-- The linear extension of a family of values, on a basis element. -/
lemma linearCombination_single (g : X A → V A) (x : X A) :
    Finsupp.linearCombination R g (single R x) = g x := by
  rw [single, Finsupp.linearCombination_single, one_smul]

/-- **The linearization adjunction for species**: a morphism of linear species out of the
linearization of `X` is a morphism of set species out of `X` into the underlying set species. -/
noncomputable def homEquiv : SymSpeciesHom R (LinSp R X) V ≃ SetSpeciesHom X (UndSp R V) where
  toFun φ := ⟨fun A _ _ x => UndSp.of R V (φ.app A (single R x)), fun e x => by
    show UndSp.of R V (φ.app _ (single R (SetSpecies.map e x)))
      = UndSp.of R V (SymSpecies.map (R := R) e (φ.app _ (single R x)))
    rw [← map_single, φ.app_map]⟩
  invFun f := ⟨fun A _ _ => Finsupp.linearCombination R fun x => (UndSp.of R V).symm (f.app A x),
    fun {A B} _ _ _ _ e x => LinearMap.congr_fun (lhom_ext
      (f := (Finsupp.linearCombination R fun x => (UndSp.of R V).symm (f.app B x)).comp
        (SymSpecies.map (R := R) e))
      (g := (SymSpecies.map (R := R) e).comp
        (Finsupp.linearCombination R fun x => (UndSp.of R V).symm (f.app A x)))
      fun s => by
        show Finsupp.linearCombination R _
            (Finsupp.mapDomain (SetSpecies.map e) (Finsupp.single s 1))
          = SymSpecies.map (R := R) e (Finsupp.linearCombination R _ (Finsupp.single s 1))
        rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single,
          Finsupp.linearCombination_single, one_smul, one_smul]
        exact congrArg (UndSp.of R V).symm (f.app_map e s)) x⟩
  left_inv φ := SymSpeciesHom.ext fun A _ _ x =>
    LinearMap.congr_fun (lhom_ext (g := φ.app A) fun s => linearCombination_single _ s) x
  right_inv f := SetSpeciesHom.ext fun A _ _ x =>
    congrArg (UndSp.of R V) (linearCombination_single _ x)

/-- The morphism of set species of a morphism of linear species is its restriction to the basis
elements. -/
lemma homEquiv_apply (φ : SymSpeciesHom R (LinSp R X) V) (x : X A) :
    (homEquiv φ).app A x = UndSp.of R V (φ.app A (single R x)) := rfl

/-- **The morphism of linear species extending a morphism of set species** takes its values on
the basis elements. -/
lemma homEquiv_symm_single (f : SetSpeciesHom X (UndSp R V)) (x : X A) :
    (homEquiv.symm f).app A (single R x) = (UndSp.of R V).symm (f.app A x) :=
  linearCombination_single _ x

end LinSp

end LinSp

/-! ## The comparison -/

section Compare

variable {R : Type u} [CommRing R]
  {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- The linear extension of a morphism of set operads, on a basis element. -/
lemma linHomEquiv_single (ψ : SetOperadHom S (Und R Q)) {A : Type} [Fintype A] [DecidableEq A]
    (s : S A) : (linHomEquiv R ψ).app A (Finsupp.single s 1) = (Und.of R Q).symm (ψ.app A s) := by
  show Finsupp.lift (Q _) R _ _ (Finsupp.single _ 1) = _
  simp

end Compare

namespace FreeL

variable (R : Type u) [CommRing R]
  (X : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) [SetSpecies X]

/-- The generators of `X`, as basis elements of the linearization of the free set operad: a
morphism of linear species. -/
noncomputable def linGenSp : SymSpeciesHom R (LinSp R X) (Lin R (FreeSp X)) :=
  LinSp.homEquiv.symm ⟨fun A _ _ x => UndSp.of R _ (Finsupp.single (FreeSp.ι.app A x) 1),
    fun e x => by
      show UndSp.of R (Lin R (FreeSp X)) (Finsupp.single (FreeSp.ι.app _ (SetSpecies.map e x)) 1)
        = UndSp.of R (Lin R (FreeSp X)) (Lin.mapL R e (Finsupp.single (FreeSp.ι.app _ x) 1))
      rw [Lin.mapL_single]
      exact congrArg (fun s => UndSp.of R (Lin R (FreeSp X)) (Finsupp.single s 1))
        (FreeSp.ι.app_map e x)⟩

/-- **The comparison morphism** from the free operad on the linearization of `X` to the
linearization of the free set operad on `X`, extending `linGenSp`. -/
noncomputable def toLin : SymOperadHom R (FreeL R (LinSp R X)) (Lin R (FreeSp X)) :=
  FreeL.homEquiv.symm (linGenSp R X)

variable {X} in
/-- The comparison morphism sends the generator of a basis element to the basis element of the
generator. -/
lemma toLin_ι {A : Type} [Fintype A] [DecidableEq A] (x : X A) :
    (toLin R X).app A ((FreeL.ι R (LinSp R X)).app A (LinSp.single R x))
      = Finsupp.single (FreeSp.ι.app A x) 1 := by
  rw [toLin, FreeL.homEquiv_symm_ι]
  exact LinSp.homEquiv_symm_single _ x

/-- The generators of the free operad on the linearization of `X`, at the basis elements: a
morphism of set species. -/
noncomputable def genSet : SetSpeciesHom X (Und R (FreeL R (LinSp R X))) :=
  ⟨fun A _ _ x => Und.of R _ ((FreeL.ι R (LinSp R X)).app A (LinSp.single R x)), fun e x => by
    show Und.of R (FreeL R (LinSp R X))
        ((FreeL.ι R (LinSp R X)).app _ (LinSp.single R (SetSpecies.map e x)))
      = Und.of R (FreeL R (LinSp R X)) (SymOperad.map (R := R) e
        ((FreeL.ι R (LinSp R X)).app _ (LinSp.single R x)))
    rw [← LinSp.map_single, (FreeL.ι R (LinSp R X)).app_map]
    rfl⟩

/-- **The inverse comparison morphism**, extending `genSet` by the universal properties of the
free set operad and of the linearization. -/
noncomputable def ofLin : SymOperadHom R (Lin R (FreeSp X)) (FreeL R (LinSp R X)) :=
  linHomEquiv R (FreeSp.homEquiv.symm (genSet R X))

variable {X} in
/-- The inverse comparison morphism sends the basis element of a generator to the generator of
the basis element. -/
lemma ofLin_single {A : Type} [Fintype A] [DecidableEq A] (x : X A) :
    (ofLin R X).app A (Finsupp.single (FreeSp.ι.app A x) 1)
      = (FreeL.ι R (LinSp R X)).app A (LinSp.single R x) := by
  rw [ofLin, linHomEquiv_single, FreeSp.homEquiv_symm_ι]
  rfl

/-- **The free operad on the linearization of a set species is the linearization of the free set
operad**: `FreeL R (LinSp R X) ≅ Lin R (FreeSp X)`, an isomorphism of symmetric operads. -/
noncomputable def linIso : SymOperadIso R (FreeL R (LinSp R X)) (Lin R (FreeSp X)) where
  hom := toLin R X
  inv := ofLin R X
  hom_inv_id := FreeL.hom_ext fun A _ _ v =>
    LinearMap.congr_fun (LinSp.lhom_ext
      (f := ((ofLin R X).app A).comp
        (((toLin R X).app A).comp ((FreeL.ι R (LinSp R X)).app A)))
      (g := (FreeL.ι R (LinSp R X)).app A) fun x => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, toLin_ι, ofLin_single]) v
  inv_hom_id := (linHomEquiv R).symm.injective (FreeSp.hom_ext fun A _ _ x => by
    show Und.of R (Lin R (FreeSp X)) ((toLin R X).app A
        ((ofLin R X).app A (Finsupp.single (FreeSp.ι.app A x) 1)))
      = Und.of R (Lin R (FreeSp X)) (Finsupp.single (FreeSp.ι.app A x) 1)
    rw [ofLin_single, toLin_ι])

/-- **A basis of the free operad on the linearization of a set species**, indexed by the free
set operad. -/
noncomputable def linBasis (A : Type) [Fintype A] [DecidableEq A] :
    Module.Basis (FreeSp X A) R (FreeL R (LinSp R X) A) :=
  Module.Basis.ofRepr ((linIso R X).linearEquiv A)

variable {X} in
/-- The basis vector at a generator of `X` is the generator of its basis element. -/
lemma linBasis_ι {A : Type} [Fintype A] [DecidableEq A] (x : X A) :
    linBasis R X A (FreeSp.ι.app A x) = (FreeL.ι R (LinSp R X)).app A (LinSp.single R x) := by
  rw [← ofLin_single, linBasis, Module.Basis.coe_ofRepr]
  rfl

/-- **The rank of the free operad on the linearization of a set species** is the number of
operations of the free set operad, when these are finitely many. -/
theorem finrank_linSp [Nontrivial R] (A : Type) [Fintype A] [DecidableEq A]
    [Fintype (FreeSp X A)] :
    Module.finrank R (FreeL R (LinSp R X) A) = Fintype.card (FreeSp X A) :=
  Module.finrank_eq_card_basis (linBasis R X A)

end FreeL

end Operad
