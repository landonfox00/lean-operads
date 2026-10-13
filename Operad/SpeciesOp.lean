/-
# Species in the operad style

A *species* (Joyal) assigns a set, or a module, to every finite set, functorially in bijections.
Indexed like the library's operads, by finite types and bijections, a **set species** is a family
`X A` with relabelling (`SetSpecies`) and a **linear species** a family of modules with linear
relabelling (`SymSpecies`): the data of a set operad, or of an operad in modules, without the
composition. Every operad has an underlying species (`SetOperad.toSetSpecies`,
`SymOperad.toSymSpecies`).

* **Morphisms of species** are the natural families of maps (`SetSpeciesHom`, `SymSpeciesHom`).
* **The skeleton** (`SetSpeciesHom.skeletonEquiv`): a morphism of species is determined by its
  components at the standard finite types `Fin n`, and any family of maps on them that commutes
  with the permutations of each `Fin n` extends to a morphism (`SetSpeciesHom.extend`), through a
  numbering of each finite type; the extension does not depend on the numbering
  (`SetSpeciesHom.extendApp_chart`). This is the comparison with the classical description of a
  species as a sequence of sets with actions of the symmetric groups.
* **The underlying set species of a linear species** (`UndSp`), and the linear morphisms as the
  morphisms of underlying set species whose components are linear (`SymSpeciesHom.undEquiv`).
-/
import Operad.SetOperad

universe u v w x

namespace Operad

/-! ## Set species -/

/-- **A set species**: a family of types indexed by finite types, functorial in bijections. -/
class SetSpecies (X : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) where
  /-- Relabelling along a bijection. -/
  map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    (A ≃ B) → X A → X B
  map_refl {A : Type} [Fintype A] [DecidableEq A] (x : X A) : map (Equiv.refl A) x = x
  map_trans {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (e : A ≃ B) (f : B ≃ C) (x : X A) :
    map (e.trans f) x = map f (map e x)

/-- **A morphism of set species**: a family of maps commuting with relabelling. -/
structure SetSpeciesHom (X : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (Y : (A : Type) → [Fintype A] → [DecidableEq A] → Type w) [SetSpecies X] [SetSpecies Y] :
    Type (max 1 v w) where
  /-- The component at a finite type. -/
  app (A : Type) [Fintype A] [DecidableEq A] : X A → Y A
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : X A) : app B (SetSpecies.map e x) = SetSpecies.map e (app A x)

/-- **The underlying species of a set operad.** -/
instance (priority := 100) SetOperad.toSetSpecies
    (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) [SetOperad S] :
    SetSpecies S where
  map := SetOperad.map
  map_refl := SetOperad.map_refl
  map_trans := SetOperad.map_trans

namespace SetSpecies

variable {X : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetSpecies X]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

@[simp] lemma map_symm_map (e : A ≃ B) (x : X A) : map e.symm (map e x) = x := by
  rw [← map_trans, Equiv.self_trans_symm, map_refl]

@[simp] lemma map_map_symm (e : A ≃ B) (y : X B) : map e (map e.symm y) = y := by
  rw [← map_trans, Equiv.symm_trans_self, map_refl]

end SetSpecies

namespace SetSpeciesHom

variable {X : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  {Y : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  {Z : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [SetSpecies X] [SetSpecies Y] [SetSpecies Z]

@[ext] lemma ext {φ ψ : SetSpeciesHom X Y}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : X A), φ.app A x = ψ.app A x) :
    φ = ψ := by
  obtain ⟨φa, _⟩ := φ
  obtain ⟨ψa, _⟩ := ψ
  have : @φa = @ψa := by
    funext A _ _ x
    exact h A x
  subst this
  rfl

/-- The identity morphism. -/
def id : SetSpeciesHom X X where
  app _ _ _ x := x
  app_map _ _ := rfl

/-- Composition of morphisms. -/
def comp (ψ : SetSpeciesHom Y Z) (φ : SetSpeciesHom X Y) : SetSpeciesHom X Z where
  app A _ _ x := ψ.app A (φ.app A x)
  app_map e x := by rw [φ.app_map, ψ.app_map]

/-! ### The skeleton -/

/-- A family of maps on the standard finite types **commuting with their permutations**. -/
def Equivariant (f : ∀ n : ℕ, X (Fin n) → Y (Fin n)) : Prop :=
  ∀ (n : ℕ) (σ : Fin n ≃ Fin n) (x : X (Fin n)),
    f n (SetSpecies.map σ x) = SetSpecies.map σ (f n x)

/-- The component at `A` of the morphism extending `f`, through a chosen numbering of `A`. -/
noncomputable def extendApp (f : ∀ n : ℕ, X (Fin n) → Y (Fin n)) (A : Type) [Fintype A]
    [DecidableEq A] (x : X A) : Y A :=
  SetSpecies.map (Fintype.equivFin A).symm (f _ (SetSpecies.map (Fintype.equivFin A) x))

/-- **The extension does not depend on the numbering.** -/
lemma extendApp_chart {f : ∀ n : ℕ, X (Fin n) → Y (Fin n)} (hf : Equivariant f) {A : Type}
    [Fintype A] [DecidableEq A] {n : ℕ} (φ : Fin n ≃ A) (x : X A) :
    extendApp f A x = SetSpecies.map φ (f n (SetSpecies.map φ.symm x)) := by
  have hn : n = Fintype.card A := by simpa using Fintype.card_congr φ
  subst hn
  set ψ := (Fintype.equivFin A).symm
  have hσ : SetSpecies.map ψ.symm x
      = SetSpecies.map (φ.trans ψ.symm) (SetSpecies.map φ.symm x) := by
    rw [← SetSpecies.map_trans, ← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]
  show SetSpecies.map ψ (f _ (SetSpecies.map ψ.symm x)) = _
  rw [hσ, hf, ← SetSpecies.map_trans, Equiv.trans_assoc, Equiv.symm_trans_self,
    Equiv.trans_refl]

/-- **The morphism of species extending an equivariant family** on the standard finite types. -/
noncomputable def extend (f : ∀ n : ℕ, X (Fin n) → Y (Fin n)) (hf : Equivariant f) :
    SetSpeciesHom X Y where
  app A _ _ := extendApp f A
  app_map {A B} _ _ _ _ e x := by
    have h1 : SetSpecies.map ((Fintype.equivFin A).symm.trans e).symm (SetSpecies.map e x)
        = SetSpecies.map (Fintype.equivFin A) x := by
      rw [← SetSpecies.map_trans]
      exact congrArg (fun g => SetSpecies.map g x) (Equiv.ext fun a => by simp)
    rw [extendApp_chart hf ((Fintype.equivFin A).symm.trans e), h1, SetSpecies.map_trans]
    rfl

@[simp] lemma extend_app_fin {f : ∀ n : ℕ, X (Fin n) → Y (Fin n)} (hf : Equivariant f)
    (n : ℕ) (x : X (Fin n)) : (extend f hf).app (Fin n) x = f n x := by
  show extendApp f (Fin n) x = f n x
  rw [extendApp_chart hf (Equiv.refl (Fin n)), Equiv.refl_symm, SetSpecies.map_refl,
    SetSpecies.map_refl]

/-- A morphism of species, computed through a numbering. -/
lemma app_eq_chart (φ : SetSpeciesHom X Y) {A : Type} [Fintype A] [DecidableEq A] {n : ℕ}
    (e : Fin n ≃ A) (x : X A) :
    φ.app A x = SetSpecies.map e (φ.app (Fin n) (SetSpecies.map e.symm x)) := by
  rw [← φ.app_map, SetSpecies.map_map_symm]

/-- **The skeleton**: morphisms of species are the families of maps on the standard finite
types commuting with their permutations. -/
noncomputable def skeletonEquiv :
    SetSpeciesHom X Y ≃ {f : ∀ n : ℕ, X (Fin n) → Y (Fin n) // Equivariant f} where
  toFun φ := ⟨fun n => φ.app (Fin n), fun _ σ x => φ.app_map σ x⟩
  invFun f := extend f.1 f.2
  left_inv φ := by
    ext A _ _ y
    show extendApp _ A y = _
    rw [extendApp_chart (fun _ σ x => φ.app_map σ x) (Fintype.equivFin A).symm,
      ← app_eq_chart]
  right_inv f := Subtype.ext (funext fun n => funext fun x => extend_app_fin f.2 n x)

end SetSpeciesHom

/-- The underlying morphism of species of a morphism of set operads. -/
def SetOperadHom.toSpeciesHom {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S] [SetOperad T]
    (φ : SetOperadHom S T) : SetSpeciesHom S T :=
  ⟨φ.app, φ.app_map⟩

/-! ## Linear species -/

/-- **A linear species**: a family of `R`-modules indexed by finite types, functorial in
bijections. -/
class SymSpecies (R : Type u) [CommRing R]
    (V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] where
  /-- Relabelling along a bijection. -/
  map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    (A ≃ B) → V A →ₗ[R] V B
  map_refl {A : Type} [Fintype A] [DecidableEq A] (x : V A) : map (Equiv.refl A) x = x
  map_trans {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (e : A ≃ B) (f : B ≃ C) (x : V A) :
    map (e.trans f) x = map f (map e x)

/-- **A morphism of linear species**: a family of linear maps commuting with relabelling. -/
structure SymSpeciesHom (R : Type u) [CommRing R]
    (V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)]
    [SymSpecies R V] [SymSpecies R W] where
  /-- The component at a finite type. -/
  app (A : Type) [Fintype A] [DecidableEq A] : V A →ₗ[R] W A
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : V A) : app B (SymSpecies.map (R := R) e x) = SymSpecies.map (R := R) e (app A x)

/-- **The underlying linear species of an operad in modules.** -/
instance (priority := 100) SymOperad.toSymSpecies (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P] :
    SymSpecies R P where
  map := SymOperad.map
  map_refl := SymOperad.map_refl
  map_trans := SymOperad.map_trans

/-- The underlying morphism of linear species of a morphism of operads in modules. -/
def SymOperadHom.toSpeciesHom {R : Type u} [CommRing R]
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R P] [SymOperad R Q]
    (φ : SymOperadHom R P Q) : SymSpeciesHom R P Q :=
  ⟨φ.app, φ.app_map⟩

namespace SymSpeciesHom

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)]
  [SymSpecies R V] [SymSpecies R W]

@[ext] lemma ext {φ ψ : SymSpeciesHom R V W}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), φ.app A x = ψ.app A x) :
    φ = ψ := by
  obtain ⟨φa, _⟩ := φ
  obtain ⟨ψa, _⟩ := ψ
  have : @φa = @ψa := by
    funext A _ _
    exact LinearMap.ext (h A)
  subst this
  rfl

end SymSpeciesHom

/-! ### The underlying set species -/

/-- **The underlying set species** of a linear species. A type synonym, recording the ring. -/
@[nolint unusedArguments]
def UndSp (R : Type u) [CommRing R]
    (V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type v :=
  fun A _ _ => V A

section UndSp

variable (R : Type u) [CommRing R]
  (V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [SymSpecies R V]

/-- An element of `V A`, seen in the underlying set species. -/
def UndSp.of {A : Type} [Fintype A] [DecidableEq A] : V A ≃ UndSp R V A := Equiv.refl _

instance instSetSpeciesUndSp : SetSpecies (UndSp R V) where
  map e x := UndSp.of R V (SymSpecies.map (R := R) e ((UndSp.of R V).symm x))
  map_refl x := SymSpecies.map_refl (R := R) (V := V) x
  map_trans e f x := SymSpecies.map_trans (R := R) (V := V) e f x

end UndSp

namespace SymSpeciesHom

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)]
  [SymSpecies R V] [SymSpecies R W]

/-- A morphism of set species between underlying set species is **linear** when its components
are. -/
def IsLinear (φ : SetSpeciesHom (UndSp R V) (UndSp R W)) : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A],
    (∀ x y : V A, φ.app A (UndSp.of R V (x + y))
      = UndSp.of R W ((UndSp.of R W).symm (φ.app A (UndSp.of R V x))
        + (UndSp.of R W).symm (φ.app A (UndSp.of R V y)))) ∧
    ∀ (c : R) (x : V A), φ.app A (UndSp.of R V (c • x))
      = UndSp.of R W (c • (UndSp.of R W).symm (φ.app A (UndSp.of R V x)))

/-- **Morphisms of linear species are the linear morphisms of the underlying set species.** -/
def undEquiv :
    SymSpeciesHom R V W ≃ {φ : SetSpeciesHom (UndSp R V) (UndSp R W) // IsLinear φ} where
  toFun φ := ⟨⟨fun A _ _ x => UndSp.of R W (φ.app A ((UndSp.of R V).symm x)),
      fun e _ => congrArg (UndSp.of R W) (φ.app_map e _)⟩,
    fun A _ _ => ⟨fun x y => congrArg (UndSp.of R W) ((φ.app A).map_add x y),
      fun c x => congrArg (UndSp.of R W) ((φ.app A).map_smul c x)⟩⟩
  invFun φ := ⟨fun A _ _ =>
      { toFun := fun x => (UndSp.of R W).symm (φ.1.app A (UndSp.of R V x))
        map_add' := fun x y => congrArg (UndSp.of R W).symm ((φ.2 A).1 x y)
        map_smul' := fun c x => congrArg (UndSp.of R W).symm ((φ.2 A).2 c x) },
    fun e x => congrArg (UndSp.of R W).symm (φ.1.app_map e (UndSp.of R V x))⟩
  left_inv _ := rfl
  right_inv _ := rfl

end SymSpeciesHom

end Operad
