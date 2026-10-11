/-
# Shuffle operads and the forgetful functor from symmetric operads

A **shuffle operad** (Dotsenko–Khoroshkin) has components indexed by finite *ordered* sets, with
relabelling only along order isomorphisms, and only those partial compositions which are
*shuffles*: inserting an operation with inputs `B` at the input `i` of one with inputs `A` gives
inputs `Without A i ⊕ B`, ordered in a way that keeps the orders of `Without A i` and of `B` and
puts the least input of `B` where `i` was (`Operad.IsShuffle`). The order of the composite is the
datum of the composition: a bijection `e : Without A i ⊕ B ≃ C` onto an ordered set `C`.

* `ShuffleOperad`: shuffle operads in `R`-modules, on ordered species. The axioms are those of a
  symmetric operad, for the shuffle bijections: equivariance under order isomorphisms, the unit
  laws, and sequential and parallel associativity whenever the two composites put every input at
  the same place.
* `ShuffleOperadHom`, `ShuffleOperadIdeal`, and the quotient by an ideal
  (`ShuffleOperadIdeal.Quot`).
* **The forgetful functor** (`SymOperad.toShuffle`): every symmetric operad is a shuffle operad,
  composing and then relabelling along the shuffle; the axioms hold for any bijections, not only
  shuffles. Morphisms (`SymOperadHom.toShuffle`) and ideals (`SymOperadIdeal.toShuffle`) are
  transported, and the quotient of the forgetful image by a transported ideal is the forgetful
  image of the quotient (`SymOperadIdeal.toShuffle_quot`).
-/
import Operad.SymQuot

universe u v w

namespace Operad

open Sym

/-! ## Shuffles -/

section Shuffles

variable {A B C : Type} [LinearOrder A] [LinearOrder B] [LinearOrder C]

/-- **A shuffle**: a bijection from `Without A i ⊕ B` onto an ordered set, increasing on both
parts, which puts the least input of `B` at the place of `i`. -/
structure IsShuffle (i : A) (e : Without A i ⊕ B ≃ C) : Prop where
  /-- The inputs of the outer operation keep their order. -/
  mono_left : StrictMono fun a : Without A i => e (Sum.inl a)
  /-- The inputs of the inner operation keep their order. -/
  mono_right : StrictMono fun b : B => e (Sum.inr b)
  /-- The least input of the inner operation takes the place of `i`. -/
  pointed : ∀ (a : Without A i) (b : B), (∀ b' : B, b ≤ b') →
    (a.1 < i ↔ e (Sum.inl a) < e (Sum.inr b))

end Shuffles

/-! ## Shuffle operads -/

/-- **A shuffle operad in `R`-modules**, on ordered species: relabellings along order
isomorphisms, a unit, and partial compositions along shuffles. -/
class ShuffleOperad (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [LinearOrder A] → Type v)
    [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (P A)] where
  /-- Relabelling along an order isomorphism. -/
  map {A B : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B] :
    (A ≃o B) → P A →ₗ[R] P B
  /-- Relabelling along the identity changes nothing. -/
  map_refl {A : Type} [Fintype A] [LinearOrder A] (x : P A) : map (OrderIso.refl A) x = x
  /-- Relabelling is functorial. -/
  map_trans {A B C : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B] [Fintype C]
    [LinearOrder C] (e : A ≃o B) (f : B ≃o C) (x : P A) : map (e.trans f) x = map f (map e x)
  /-- The identity operation. -/
  one : P Unit
  /-- **Shuffle composition**: insert an operation with inputs `B` at the input `i` of one with
  inputs `A`, the inputs of the composite ordered by the shuffle `e`. -/
  comp {A B C : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B] [Fintype C]
    [LinearOrder C] (i : A) (e : Without A i ⊕ B ≃ C) (he : IsShuffle i e) :
    P A →ₗ[R] P B →ₗ[R] P C
  /-- **Equivariance** under order isomorphisms of the three input sets. -/
  map_comp {A A' B B' C C' : Type} [Fintype A] [LinearOrder A] [Fintype A'] [LinearOrder A']
    [Fintype B] [LinearOrder B] [Fintype B'] [LinearOrder B'] [Fintype C] [LinearOrder C]
    [Fintype C'] [LinearOrder C'] (σ : A ≃o A') (τ : B ≃o B') (ρ : C ≃o C') (i : A)
    (e : Without A i ⊕ B ≃ C) (he : IsShuffle i e) (e' : Without A' (σ i) ⊕ B' ≃ C')
    (he' : IsShuffle (σ i) e')
    (h : ∀ c, ρ (e c) = e' (compEquiv σ.toEquiv τ.toEquiv i c)) (x : P A) (y : P B) :
    map ρ (comp i e he x y) = comp (σ i) e' he' (map σ x) (map τ y)
  /-- The right unit law. -/
  comp_one {A C : Type} [Fintype A] [LinearOrder A] [Fintype C] [LinearOrder C] (i : A)
    (e : Without A i ⊕ Unit ≃ C) (he : IsShuffle i e) (φ : A ≃o C)
    (hφ : ∀ a, φ a = e ((rightUnitEquiv i).symm a)) (x : P A) :
    comp i e he x one = map φ x
  /-- The left unit law. -/
  one_comp {B C : Type} [Fintype B] [LinearOrder B] [Fintype C] [LinearOrder C]
    (e : Without Unit () ⊕ B ≃ C) (he : IsShuffle () e) (φ : B ≃o C)
    (hφ : ∀ b, φ b = e (Sum.inr b)) (y : P B) :
    comp () e he one y = map φ y
  /-- **Sequential associativity**, whenever the two composites put every input at the same
  place. -/
  comp_assoc_seq {A B D C₁ C₃ C : Type} [Fintype A] [LinearOrder A] [Fintype B]
    [LinearOrder B] [Fintype D] [LinearOrder D] [Fintype C₁] [LinearOrder C₁] [Fintype C₃]
    [LinearOrder C₃] [Fintype C] [LinearOrder C] (i : A) (j : B) (e₁ : Without A i ⊕ B ≃ C₁)
    (he₁ : IsShuffle i e₁) (e₂ : Without C₁ (e₁ (Sum.inr j)) ⊕ D ≃ C)
    (he₂ : IsShuffle (e₁ (Sum.inr j)) e₂) (e₃ : Without B j ⊕ D ≃ C₃) (he₃ : IsShuffle j e₃)
    (e₄ : Without A i ⊕ C₃ ≃ C) (he₄ : IsShuffle i e₄)
    (h₁ : ∀ a : Without A i, e₂ (Sum.inl ⟨e₁ (Sum.inl a),
      fun h => Sum.inl_ne_inr (e₁.injective h)⟩) = e₄ (Sum.inl a))
    (h₂ : ∀ b : Without B j, e₂ (Sum.inl ⟨e₁ (Sum.inr b.1),
      fun h => b.2 (Sum.inr_injective (e₁.injective h))⟩) = e₄ (Sum.inr (e₃ (Sum.inl b))))
    (h₃ : ∀ d : D, e₂ (Sum.inr d) = e₄ (Sum.inr (e₃ (Sum.inr d)))) (x : P A) (y : P B)
    (z : P D) :
    comp (e₁ (Sum.inr j)) e₂ he₂ (comp i e₁ he₁ x y) z = comp i e₄ he₄ x (comp j e₃ he₃ y z)
  /-- **Parallel associativity**, whenever the two composites put every input at the same
  place. -/
  comp_assoc_par {A B D C₁ C₃ C : Type} [Fintype A] [LinearOrder A] [Fintype B]
    [LinearOrder B] [Fintype D] [LinearOrder D] [Fintype C₁] [LinearOrder C₁] [Fintype C₃]
    [LinearOrder C₃] [Fintype C] [LinearOrder C] {i k : A} (hik : i ≠ k)
    (e₁ : Without A i ⊕ B ≃ C₁) (he₁ : IsShuffle i e₁)
    (e₂ : Without C₁ (e₁ (Sum.inl ⟨k, Ne.symm hik⟩)) ⊕ D ≃ C)
    (he₂ : IsShuffle (e₁ (Sum.inl ⟨k, Ne.symm hik⟩)) e₂) (e₃ : Without A k ⊕ D ≃ C₃)
    (he₃ : IsShuffle k e₃) (e₄ : Without C₃ (e₃ (Sum.inl ⟨i, hik⟩)) ⊕ B ≃ C)
    (he₄ : IsShuffle (e₃ (Sum.inl ⟨i, hik⟩)) e₄)
    (h₁ : ∀ (a : A) (hai : a ≠ i) (hak : a ≠ k),
      e₂ (Sum.inl ⟨e₁ (Sum.inl ⟨a, hai⟩), fun h => hak (congrArg Subtype.val
        (Sum.inl_injective (e₁.injective h)))⟩)
        = e₄ (Sum.inl ⟨e₃ (Sum.inl ⟨a, hak⟩), fun h => hai (congrArg Subtype.val
          (Sum.inl_injective (e₃.injective h)))⟩))
    (h₂ : ∀ b : B, e₂ (Sum.inl ⟨e₁ (Sum.inr b), fun h => Sum.inr_ne_inl (e₁.injective h)⟩)
      = e₄ (Sum.inr b))
    (h₃ : ∀ d : D, e₂ (Sum.inr d)
      = e₄ (Sum.inl ⟨e₃ (Sum.inr d), fun h => Sum.inr_ne_inl (e₃.injective h)⟩))
    (x : P A) (y : P B) (z : P D) :
    comp (e₁ (Sum.inl ⟨k, Ne.symm hik⟩)) e₂ he₂ (comp i e₁ he₁ x y) z
      = comp (e₃ (Sum.inl ⟨i, hik⟩)) e₄ he₄ (comp k e₃ he₃ x z) y

/-- **A morphism of shuffle operads**: a family of linear maps commuting with relabelling,
preserving the unit and the shuffle compositions. -/
structure ShuffleOperadHom (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [LinearOrder A] → Type v)
    (Q : (A : Type) → [Fintype A] → [LinearOrder A] → Type w)
    [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (P A)]
    [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (Q A)]
    [ShuffleOperad R P] [ShuffleOperad R Q] where
  /-- The component at a finite ordered input set. -/
  app (A : Type) [Fintype A] [LinearOrder A] : P A →ₗ[R] Q A
  /-- Components commute with relabelling. -/
  app_map {A B : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B] (e : A ≃o B)
    (x : P A) : app B (ShuffleOperad.map (R := R) e x) = ShuffleOperad.map (R := R) e (app A x)
  /-- The unit goes to the unit. -/
  app_one : app Unit (ShuffleOperad.one R) = ShuffleOperad.one R
  /-- Shuffle compositions go to shuffle compositions. -/
  app_comp {A B C : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B] [Fintype C]
    [LinearOrder C] (i : A) (e : Without A i ⊕ B ≃ C) (he : IsShuffle i e) (x : P A) (y : P B) :
    app C (ShuffleOperad.comp (R := R) i e he x y)
      = ShuffleOperad.comp (R := R) i e he (app A x) (app B y)

/-- **An ideal of a shuffle operad**: submodules stable under relabelling and under shuffle
composition on either side. -/
structure ShuffleOperadIdeal (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [LinearOrder A] → Type v)
    [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (P A)] [ShuffleOperad R P] where
  /-- The component at a finite ordered input set. -/
  sub (A : Type) [Fintype A] [LinearOrder A] : Submodule R (P A)
  map_mem {A B : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B] (e : A ≃o B)
    {x : P A} : x ∈ sub A → ShuffleOperad.map (R := R) e x ∈ sub B
  comp_mem_left {A B C : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    [Fintype C] [LinearOrder C] (i : A) (e : Without A i ⊕ B ≃ C) (he : IsShuffle i e)
    {x : P A} (y : P B) : x ∈ sub A → ShuffleOperad.comp (R := R) i e he x y ∈ sub C
  comp_mem_right {A B C : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    [Fintype C] [LinearOrder C] (i : A) (e : Without A i ⊕ B ≃ C) (he : IsShuffle i e)
    (x : P A) {y : P B} : y ∈ sub B → ShuffleOperad.comp (R := R) i e he x y ∈ sub C

/-! ## Quotients of shuffle operads -/

namespace ShuffleOperadIdeal

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [LinearOrder A] → Type v}
  [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (P A)] [ShuffleOperad R P]
  (I : ShuffleOperadIdeal R P)

/-- **The quotient of a shuffle operad by an ideal**, input set by input set. -/
def Quot (A : Type) [Fintype A] [LinearOrder A] : Type v := P A ⧸ I.sub A

instance (A : Type) [Fintype A] [LinearOrder A] : AddCommGroup (I.Quot A) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (A : Type) [Fintype A] [LinearOrder A] : Module R (I.Quot A) :=
  inferInstanceAs (Module R (_ ⧸ _))

variable {A B C : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B] [Fintype C]
  [LinearOrder C]

/-- The quotient map. -/
def proj (A : Type) [Fintype A] [LinearOrder A] : P A →ₗ[R] I.Quot A := (I.sub A).mkQ

lemma proj_surjective (A : Type) [Fintype A] [LinearOrder A] : Function.Surjective (I.proj A) :=
  Submodule.mkQ_surjective _

/-- Relabelling, descended to the quotient. -/
def mapQ (e : A ≃o B) : I.Quot A →ₗ[R] I.Quot B :=
  Submodule.mapQ _ _ (ShuffleOperad.map (R := R) e) fun _ hx => I.map_mem e hx

lemma mapQ_proj (e : A ≃o B) (x : P A) :
    I.mapQ e (I.proj A x) = I.proj B (ShuffleOperad.map (R := R) e x) := rfl

/-- Composition with a fixed outer operation, descended to the quotient. -/
def compRight (i : A) (e : Without A i ⊕ B ≃ C) (he : IsShuffle i e) (x : P A) :
    I.Quot B →ₗ[R] I.Quot C :=
  Submodule.mapQ _ _ (ShuffleOperad.comp (R := R) i e he x) fun _ hy =>
    I.comp_mem_right i e he x hy

/-- Shuffle composition on the quotient. -/
def compQ (i : A) (e : Without A i ⊕ B ≃ C) (he : IsShuffle i e) :
    I.Quot A →ₗ[R] I.Quot B →ₗ[R] I.Quot C :=
  Submodule.liftQ _
    { toFun := fun x => I.compRight i e he x
      map_add' := fun x x' => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨y, rfl⟩ := I.proj_surjective B q
        simp only [compRight]
        exact congrArg (I.proj C) (by rw [map_add, LinearMap.add_apply])
      map_smul' := fun c x => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨y, rfl⟩ := I.proj_surjective B q
        simp only [compRight, RingHom.id_apply]
        exact congrArg (I.proj C) (by rw [map_smul, LinearMap.smul_apply]) }
    fun x hx => LinearMap.ext fun q => by
      obtain ⟨y, rfl⟩ := I.proj_surjective B q
      exact (Submodule.Quotient.mk_eq_zero _).2 (I.comp_mem_left i e he y hx)

lemma compQ_proj (i : A) (e : Without A i ⊕ B ≃ C) (he : IsShuffle i e) (x : P A) (y : P B) :
    I.compQ i e he (I.proj A x) (I.proj B y)
      = I.proj C (ShuffleOperad.comp (R := R) i e he x y) := rfl

/-- **The quotient of a shuffle operad by an ideal is a shuffle operad.** -/
instance instShuffleOperadQuot : ShuffleOperad R I.Quot where
  map e := I.mapQ e
  map_refl q := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ q
    exact congrArg (I.proj _) (ShuffleOperad.map_refl x)
  map_trans e f q := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ q
    exact congrArg (I.proj _) (ShuffleOperad.map_trans e f x)
  one := I.proj Unit (ShuffleOperad.one R)
  comp i e he := I.compQ i e he
  map_comp σ τ ρ i e he e' he' h p q := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ p
    obtain ⟨y, rfl⟩ := I.proj_surjective _ q
    exact congrArg (I.proj _) (ShuffleOperad.map_comp σ τ ρ i e he e' he' h x y)
  comp_one i e he φ hφ p := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ p
    exact congrArg (I.proj _) (ShuffleOperad.comp_one i e he φ hφ x)
  one_comp e he φ hφ q := by
    obtain ⟨y, rfl⟩ := I.proj_surjective _ q
    exact congrArg (I.proj _) (ShuffleOperad.one_comp e he φ hφ y)
  comp_assoc_seq i j e₁ he₁ e₂ he₂ e₃ he₃ e₄ he₄ h₁ h₂ h₃ p q r := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ p
    obtain ⟨y, rfl⟩ := I.proj_surjective _ q
    obtain ⟨z, rfl⟩ := I.proj_surjective _ r
    exact congrArg (I.proj _)
      (ShuffleOperad.comp_assoc_seq i j e₁ he₁ e₂ he₂ e₃ he₃ e₄ he₄ h₁ h₂ h₃ x y z)
  comp_assoc_par hik e₁ he₁ e₂ he₂ e₃ he₃ e₄ he₄ h₁ h₂ h₃ p q r := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ p
    obtain ⟨y, rfl⟩ := I.proj_surjective _ q
    obtain ⟨z, rfl⟩ := I.proj_surjective _ r
    exact congrArg (I.proj _)
      (ShuffleOperad.comp_assoc_par hik e₁ he₁ e₂ he₂ e₃ he₃ e₄ he₄ h₁ h₂ h₃ x y z)

/-- The quotient map is a morphism of shuffle operads. -/
def projHom : ShuffleOperadHom R P I.Quot where
  app A _ _ := I.proj A
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ _ _ := rfl

section Lift

variable {Q : (A : Type) → [Fintype A] → [LinearOrder A] → Type w}
  [∀ (A : Type) [Fintype A] [LinearOrder A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [LinearOrder A], Module R (Q A)] [ShuffleOperad R Q]

/-- **The universal property of the quotient**: a morphism of shuffle operads vanishing on an
ideal factors through the quotient. -/
def liftHom (ψ : ShuffleOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [LinearOrder A], ∀ x ∈ I.sub A, ψ.app A x = 0) :
    ShuffleOperadHom R I.Quot Q where
  app A _ _ := (I.sub A).liftQ (ψ.app A) fun x hx => h A x hx
  app_map e q := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ q
    exact ψ.app_map e x
  app_one := ψ.app_one
  app_comp i e he p q := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ p
    obtain ⟨y, rfl⟩ := I.proj_surjective _ q
    exact ψ.app_comp i e he x y

@[simp] lemma liftHom_proj (ψ : ShuffleOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [LinearOrder A], ∀ x ∈ I.sub A, ψ.app A x = 0)
    (A : Type) [Fintype A] [LinearOrder A] (x : P A) :
    (I.liftHom ψ h).app A (I.proj A x) = ψ.app A x := rfl

/-- **Morphisms out of a quotient** agreeing on the classes agree. -/
lemma hom_ext_proj {ψ₁ ψ₂ : ShuffleOperadHom R I.Quot Q}
    (h : ∀ (A : Type) [Fintype A] [LinearOrder A] (x : P A),
      ψ₁.app A (I.proj A x) = ψ₂.app A (I.proj A x))
    (A : Type) [Fintype A] [LinearOrder A] (q : I.Quot A) : ψ₁.app A q = ψ₂.app A q := by
  obtain ⟨x, rfl⟩ := I.proj_surjective A q
  exact h A x

end Lift

end ShuffleOperadIdeal

/-! ## The forgetful functor from symmetric operads -/

/-- **The ordered species underlying a species**: the same components, on ordered sets. -/
@[nolint unusedArguments]
def Shuf (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) :
    (A : Type) → [Fintype A] → [LinearOrder A] → Type v :=
  fun A _ _ => P A

instance Shuf.instAddCommGroup (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)] (A : Type) [Fintype A]
    [LinearOrder A] : AddCommGroup (Shuf P A) :=
  inferInstanceAs (AddCommGroup (P A))

instance Shuf.instModule (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] (A : Type) [Fintype A]
    [LinearOrder A] : Module R (Shuf P A) :=
  inferInstanceAs (Module R (P A))

namespace SymOperad

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-- A relabelling of the outer operation of a composite is a relabelling of the composite. -/
lemma comp_map_left' {A A' B : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] (σ : A ≃ A') (i : A) (x : P A) (y : P B) :
    comp (R := R) (σ i) (map (R := R) σ x) y
      = map (R := R) (compEquiv σ (Equiv.refl B) i) (comp (R := R) i x y) := by
  rw [map_comp, map_refl]

lemma map_congr' {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {e e' : A ≃ B} (h : ∀ a, e a = e' a) (x : P A) : map (R := R) e x = map (R := R) e' x := by
  rw [Equiv.ext h]

/-- A relabelling of the inner operation of a composite is a relabelling of the composite. -/
lemma comp_map_right' {A B B' : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B'] (τ : B ≃ B') (i : A) (x : P A) (y : P B) :
    comp (R := R) i x (map (R := R) τ y)
      = map (R := R) (Equiv.sumCongr (Equiv.refl (Without A i)) τ) (comp (R := R) i x y) := by
  have h := map_comp (R := R) (Equiv.refl A) τ i x y
  rw [map_refl] at h
  refine h.symm.trans ?_
  exact map_congr' (fun s => by rcases s with s | s <;> rfl) _

lemma map_map' {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (e : A ≃ B) (f : B ≃ C) (x : P A) :
    map (R := R) f (map (R := R) e x) = map (R := R) (e.trans f) x :=
  (map_trans e f x).symm

lemma eq_map_symm {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) {x : P A} {y : P B} (h : map (R := R) e x = y) : x = map (R := R) e.symm y := by
  rw [← h, map_map', Equiv.self_trans_symm, map_refl]

/-- **The forgetful functor**: a symmetric operad is a shuffle operad, composing and relabelling
along the shuffle. -/
noncomputable instance toShuffle : ShuffleOperad R (Shuf P) where
  map e := map (R := R) e.toEquiv
  map_refl x := map_refl (R := R) x
  map_trans e f x := map_trans (R := R) e.toEquiv f.toEquiv x
  one := one R
  comp i e _ := (comp (R := R) i).compr₂ (map (R := R) e)
  map_comp σ τ ρ i e he e' he' h x y := by
    show map (R := R) ρ.toEquiv (map (R := R) e (comp (R := R) i x y))
      = map (R := R) e' (comp (R := R) (σ.toEquiv i) (map (R := R) σ.toEquiv x)
          (map (R := R) τ.toEquiv y))
    rw [← map_comp, map_map', map_map']
    exact map_congr' (fun c => h c) _
  comp_one i e he φ hφ x := by
    show map (R := R) e (comp (R := R) i x (one R)) = map (R := R) φ.toEquiv x
    rw [eq_map_symm _ (comp_one (R := R) i x), map_map']
    exact map_congr' (fun a => (hφ a).symm) _
  one_comp e he φ hφ y := by
    show map (R := R) e (comp (R := R) () (one R) y) = map (R := R) φ.toEquiv y
    rw [eq_map_symm _ (one_comp (R := R) y), map_map']
    exact map_congr' (fun b => (hφ b).symm) _
  comp_assoc_seq i j e₁ he₁ e₂ he₂ e₃ he₃ e₄ he₄ h₁ h₂ h₃ x y z := by
    show map (R := R) e₂ (comp (R := R) (e₁ (Sum.inr j)) (map (R := R) e₁ (comp (R := R) i x y)) z)
      = map (R := R) e₄ (comp (R := R) i x (map (R := R) e₃ (comp (R := R) j y z)))
    rw [comp_map_left', comp_map_right', ← comp_assoc_seq (R := R) i j x y z, map_map', map_map',
      map_map']
    refine map_congr' (fun c => ?_) _
    rcases c with ⟨(a | b), hc⟩ | d
    · exact h₁ a
    · exact h₂ ⟨b, fun h => hc (congrArg Sum.inr h)⟩
    · exact h₃ d
  comp_assoc_par hik e₁ he₁ e₂ he₂ e₃ he₃ e₄ he₄ h₁ h₂ h₃ x y z := by
    show map (R := R) e₂ (comp (R := R) (e₁ (Sum.inl ⟨_, Ne.symm hik⟩))
        (map (R := R) e₁ (comp (R := R) _ x y)) z)
      = map (R := R) e₄ (comp (R := R) (e₃ (Sum.inl ⟨_, hik⟩))
        (map (R := R) e₃ (comp (R := R) _ x z)) y)
    rw [comp_map_left', comp_map_left', ← comp_assoc_par (R := R) hik x y z, map_map', map_map',
      map_map']
    refine map_congr' (fun c => ?_) _
    rcases c with ⟨(⟨a, hai⟩ | b), hc⟩ | d
    · exact h₁ a hai fun h => hc (by subst h; rfl)
    · exact h₂ b
    · exact h₃ d

lemma toShuffle_map {A B : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    (e : A ≃o B) (x : P A) :
    ShuffleOperad.map (R := R) (P := Shuf P) e x = map (R := R) e.toEquiv x :=
  rfl

lemma toShuffle_comp {A B C : Type} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    [Fintype C] [LinearOrder C] (i : A) (e : Without A i ⊕ B ≃ C) (he : IsShuffle i e) (x : P A)
    (y : P B) :
    ShuffleOperad.comp (R := R) (P := Shuf P) i e he x y = map (R := R) e (comp (R := R) i x y) :=
  rfl

end SymOperad

namespace SymOperadHom

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **The forgetful functor on morphisms.** -/
def toShuffle (f : SymOperadHom R P Q) : ShuffleOperadHom R (Shuf P) (Shuf Q) where
  app A _ _ := f.app A
  app_map e x := f.app_map e.toEquiv x
  app_one := f.app_one
  app_comp i e he x y := by
    show f.app _ (SymOperad.map (R := R) e (SymOperad.comp (R := R) i x y))
      = SymOperad.map (R := R) e (SymOperad.comp (R := R) i (f.app _ x) (f.app _ y))
    rw [f.app_map, f.app_comp]

end SymOperadHom

namespace SymOperadIdeal

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  (I : SymOperadIdeal R P)

/-- **An ideal of a symmetric operad is an ideal of its underlying shuffle operad.** -/
def toShuffle : ShuffleOperadIdeal R (Shuf P) where
  sub A _ _ := I.sub A
  map_mem e _ hx := I.map_mem e.toEquiv hx
  comp_mem_left i e _ _ y hx := I.map_mem e (I.comp_mem_left i y hx)
  comp_mem_right i e _ x _ hy := I.map_mem e (I.comp_mem_right i x hy)

/-- **Quotients are transported**: the underlying shuffle operad of the quotient is the quotient
of the underlying shuffle operad, by the identity maps of the components. -/
def toShuffleQuot : ShuffleOperadHom R (Shuf I.Quot) I.toShuffle.Quot where
  app _ _ _ := LinearMap.id
  app_map e q := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ q
    rfl
  app_one := rfl
  app_comp i e he p q := by
    obtain ⟨x, rfl⟩ := I.proj_surjective _ p
    obtain ⟨y, rfl⟩ := I.proj_surjective _ q
    rfl

lemma toShuffleQuot_bijective (A : Type) [Fintype A] [LinearOrder A] :
    Function.Bijective (I.toShuffleQuot.app A) :=
  Function.bijective_id

end SymOperadIdeal

end Operad
