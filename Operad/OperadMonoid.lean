/-
# Operads are the monoids for the composition product

A **monoid** for the composition product of linear species (`Operad.SymMonoid`) is a species `P`
with a multiplication `γ : P ∘ P → P` and a unit `η : I → P`, associative and unital through the
associator and the unitors of `Operad.Composite`:

`γ ∘ (γ ∘ 1) = γ ∘ (1 ∘ γ) ∘ α`, `γ ∘ (η ∘ 1) = λ`, `γ ∘ (1 ∘ η) = ρ`.

* `Operad.SymOperad.toSymMonoid`: **an operad is a monoid**, multiplying by total composition
  (`Operad.SymOperad.total`), with unit its identity operation.
* `Operad.SymMonoid.toSymOperad`: **a monoid is an operad**: its total composition satisfies May's
  axioms (`Operad.SymMonoid.toMaySetOperad`), and the partial compositions are those of May's
  definition (`Operad.MaySetOperad.toSetOperad`), linear in both operations.
* **The two constructions are inverse to each other** (`Operad.SymOperad.toSymMonoid_toSymOperad`,
  `Operad.SymMonoid.toSymOperad_toSymMonoid`).
-/
import Operad.CompositeAssoc
import Operad.MayClass

universe u v

namespace Operad

open Function Composite

/-! ## Identity morphisms of species -/

namespace SymSpeciesHom

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [SymSpecies R V]

variable (R V) in
/-- The identity morphism of a linear species. -/
def id : SymSpeciesHom R V V where
  app _ _ _ := LinearMap.id
  app_map _ _ := rfl

@[simp] lemma id_app {A : Type} [Fintype A] [DecidableEq A] (x : V A) : (id R V).app A x = x :=
  rfl

end SymSpeciesHom

/-! ## Monoids -/

variable (R : Type u) [CommRing R] (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]

/-- **A monoid for the composition product**: a multiplication `P ∘ P → P` and a unit `I → P`,
associative and unital through the associator and the unitors. -/
structure SymMonoid [SymSpecies R P] where
  /-- The multiplication. -/
  mul : SymSpeciesHom R (Composite R P P) P
  /-- The unit. -/
  unit : SymSpeciesHom R (UnitSp R) P
  /-- **Associativity**: `γ ∘ (γ ∘ 1) = γ ∘ (1 ∘ γ) ∘ α`. -/
  mul_assoc (S : Type) [Fintype S] [DecidableEq S] (z : Composite R (Composite R P P) P S) :
    mul.app S ((map₂ mul (SymSpeciesHom.id R P)).app S z)
      = mul.app S ((map₂ (SymSpeciesHom.id R P) mul).app S (assoc.app S z))
  /-- **The left unit law**: `γ ∘ (η ∘ 1) = λ`. -/
  one_mul (S : Type) [Fintype S] [DecidableEq S] (z : Composite R (UnitSp R) P S) :
    mul.app S ((map₂ unit (SymSpeciesHom.id R P)).app S z) = leftUnitor.app S z
  /-- **The right unit law**: `γ ∘ (1 ∘ η) = ρ`. -/
  mul_one (S : Type) [Fintype S] [DecidableEq S] (z : Composite R P (UnitSp R) S) :
    mul.app S ((map₂ (SymSpeciesHom.id R P) unit).app S z) = rightUnitor.app S z

/-! ## Operads are monoids -/

namespace SymOperad

variable {R P} [SymOperad R P] {S : Type} [Fintype S] [DecidableEq S]

/-- Total composition on a generator of `P ∘ P`, with its inputs named. -/
noncomputable def totalFun (g : CompGen P P S) : P S :=
  SymOperad.map (R := R) g.e (SymOperad.total R g.m g.y)

lemma sigmaCongr_refl_right {A A' : Type} {B : A' → Type} (σ : A ≃ A') :
    Equiv.sigmaCongr σ (fun a => Equiv.refl (B (σ a))) = Equiv.sigmaCongrLeft σ :=
  Equiv.ext fun _ => rfl

lemma totalFun_respects : CompGen.Respects R (totalFun (R := R) (P := P) (S := S)) where
  add_m g m' := by
    simp only [totalFun, SymOperad.total_add, map_add]
  smul_m g c := by
    simp only [totalFun, SymOperad.total_smul, map_smul]
  add_y g a z z' := by
    simp only [totalFun, SymOperad.total_update_add, map_add]
  smul_y g a c z := by
    simp only [totalFun, SymOperad.total_update_smul, map_smul]
  outer := @fun g A' _ _ σ m => by
    have h := SymOperad.total_map (R := R) σ (fun a => Equiv.refl (g.B (σ a))) m
      (fun a => g.y (σ a)) g.y (fun a => (SymOperad.map_refl _).symm)
    show SymOperad.map (R := R) g.e (SymOperad.total R (SymOperad.map (R := R) σ m) g.y)
      = SymOperad.map (R := R) ((Equiv.sigmaCongrLeft σ).trans g.e)
        (SymOperad.total R m fun a => g.y (σ a))
    rw [← h, ← SymOperad.map_trans, sigmaCongr_refl_right]
  inner := @fun g B' _ _ τ => by
    have h := SymOperad.total_map (R := R) (Equiv.refl g.A) τ g.m g.y
      (fun a => SymOperad.map (R := R) (τ a) (g.y a)) (fun a => rfl)
    rw [SymOperad.map_refl] at h
    show SymOperad.map (R := R) ((Equiv.sigmaCongrRight τ).symm.trans g.e)
        (SymOperad.total R g.m fun a => SymOperad.map (R := R) (τ a) (g.y a))
      = SymOperad.map (R := R) g.e (SymOperad.total R g.m g.y)
    rw [← h, ← SymOperad.map_trans]
    congr 2
    ext ⟨a, b⟩
    show g.e ((Equiv.sigmaCongrRight τ).symm ⟨a, τ a b⟩) = g.e ⟨a, b⟩
    congr 1
    rw [Equiv.symm_apply_eq]
    rfl

variable (S) in
/-- The components of the multiplication of an operad. -/
noncomputable def mulApp : Composite R P P S →ₗ[R] P S :=
  lift totalFun totalFun_respects

lemma mulApp_mk (g : CompGen P P S) :
    mulApp S (Composite.mk R g) = SymOperad.map (R := R) g.e (SymOperad.total R g.m g.y) :=
  lift_mk _ _ g

variable (R P) in
/-- **The multiplication of an operad**: total composition. -/
noncomputable def mulHom : SymSpeciesHom R (Composite R P P) P where
  app S _ _ := mulApp S
  app_map := @fun A B _ _ _ _ f x => by
    have h := hom_ext (φ := (mulApp (R := R) (P := P) B).comp (Composite.map f))
      (ψ := (SymOperad.map (R := R) f).comp (mulApp A)) fun g => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Composite.map_mk, mulApp_mk, mulApp_mk]
        exact SymOperad.map_trans _ _ _
    exact LinearMap.congr_fun h x

lemma mulHom_app_mk (g : CompGen P P S) :
    (mulHom R P).app S (Composite.mk R g)
      = SymOperad.map (R := R) g.e (SymOperad.total R g.m g.y) :=
  mulApp_mk g

variable (R P) in
/-- **The unit of an operad**: its identity operation. -/
noncomputable def unitHom : SymSpeciesHom R (UnitSp R) P where
  app S _ _ := Finsupp.lift (P S) R (Unit ≃ S) fun u => SymOperad.map (R := R) u (SymOperad.one R)
  app_map := @fun A B _ _ _ _ f x => by
    show Finsupp.lift _ R _ _ (Finsupp.mapDomain (fun u => u.trans f) x)
      = SymOperad.map (R := R) f (Finsupp.lift _ R _ _ x)
    rw [Finsupp.lift_mapDomain', Finsupp.linear_lift]
    exact Finsupp.lift_congr_fun (fun u => SymOperad.map_trans _ _ _) x

lemma unitHom_app (x : UnitSp R S) :
    (unitHom R P).app S x
      = Finsupp.lift (P S) R (Unit ≃ S) (fun u => SymOperad.map (R := R) u (SymOperad.one R)) x :=
  rfl

/-- Relabelling, total composition in the outer operation. -/
noncomputable def totalLeft {A : Type} [Fintype A] [DecidableEq A] {B : A → Type}
    [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (e : (Σ a, B a) ≃ S) (y : ∀ a, P (B a)) :
    P A →ₗ[R] P S where
  toFun x := SymOperad.map (R := R) e (SymOperad.total R x y)
  map_add' x x' := by rw [SymOperad.total_add, map_add]
  map_smul' c x := by rw [SymOperad.total_smul, map_smul]; rfl

/-- **Associativity of the multiplication of an operad.** -/
theorem mulHom_assoc (z : Composite R (Composite R P P) P S) :
    (mulHom R P).app S ((map₂ (mulHom R P) (SymSpeciesHom.id R P)).app S z)
      = (mulHom R P).app S ((map₂ (SymSpeciesHom.id R P) (mulHom R P)).app S (assoc.app S z)) := by
  have h : ((mulHom R P).app S).comp ((map₂ (mulHom R P) (SymSpeciesHom.id R P)).app S)
      = ((mulHom R P).app S).comp (((map₂ (SymSpeciesHom.id R P) (mulHom R P)).app S).comp
          (assoc.app S)) := hom_ext fun h => by
    simp only [LinearMap.comp_apply]
    rw [map₂_mk]
    show mulApp S (mkM (genMap₂ (mulHom R P) (SymSpeciesHom.id R P) h) (mulApp h.A h.m))
      = mulApp S ((map₂ (SymSpeciesHom.id R P) (mulHom R P)).app S
          (assocApp S (Composite.mk R h)))
    rw [assocApp_mk]
    induction h.m using induction_on with
    | h0 => simp only [map_zero, MultilinearMap.zero_apply]
    | hadd x y hx hy => simp only [map_add, MultilinearMap.add_apply, hx, hy]
    | hsmul c x hx => simp only [map_smul, MultilinearMap.smul_apply, hx]
    | hmk k =>
      simp only [assocLin_mk, map₂_mk, mkM_apply, mulApp_mk, mulHom_app_mk,
        SymSpeciesHom.id_app, SymOperad.map_refl]
      have h1 := SymOperad.total_map (R := R) k.e (fun p => Equiv.refl (h.B (k.e p)))
        (SymOperad.total R k.m k.y) (fun p => h.y (k.e p)) h.y
        (fun p => (SymOperad.map_refl _).symm)
      have h2 := SymOperad.total_assoc (R := R) k.m k.y fun a b => h.y (k.e ⟨a, b⟩)
      rw [← h1, ← h2, ← SymOperad.map_trans, ← SymOperad.map_trans, sigmaCongr_refl_right]
      congr 2
  exact LinearMap.congr_fun h z

/-- **The left unit law of an operad.** -/
theorem mulHom_one (z : Composite R (UnitSp R) P S) :
    (mulHom R P).app S ((map₂ (unitHom R P) (SymSpeciesHom.id R P)).app S z)
      = leftUnitor.app S z := by
  have h : ((mulHom R P).app S).comp ((map₂ (unitHom R P) (SymSpeciesHom.id R P)).app S)
      = leftUnitor.app S := hom_ext fun g => by
    rw [LinearMap.comp_apply, map₂_mk]
    show mulApp S (Composite.mk R (genMap₂ (unitHom R P) (SymSpeciesHom.id R P) g))
      = leftUnitorApp S (Composite.mk R g)
    rw [mulApp_mk, leftUnitorApp_mk, leftUnitorFun]
    show totalLeft g.e g.y (Finsupp.lift (P g.A) R _
      (fun u => SymOperad.map (R := R) u (SymOperad.one R)) g.m) = _
    rw [Finsupp.linear_lift]
    refine Finsupp.lift_congr_fun (fun u => ?_) g.m
    show SymOperad.map (R := R) g.e (SymOperad.total R (SymOperad.map (R := R) u
        (SymOperad.one R)) g.y)
      = SymOperad.map (R := R) ((unitSigma u g.B).trans g.e) (g.y (u ()))
    have h1 := SymOperad.total_map (R := R) u (fun x => Equiv.refl (g.B (u x))) (SymOperad.one R)
      (fun x => g.y (u x)) g.y (fun x => (SymOperad.map_refl _).symm)
    have h2 := SymOperad.total_one_left (R := R) (E := fun x => g.B (u x)) fun x => g.y (u x)
    have h3 : SymOperad.total R (SymOperad.one R) (fun x => g.y (u x))
        = SymOperad.map (R := R) (Equiv.uniqueSigma fun x => g.B (u x)).symm (g.y (u ())) := by
      rw [← h2, ← SymOperad.map_trans, Equiv.self_trans_symm, SymOperad.map_refl]
    rw [← h1, h3, ← SymOperad.map_trans, ← SymOperad.map_trans]
    congr 2
  exact LinearMap.congr_fun h z

/-- **The right unit law of an operad.** -/
theorem mulHom_unit (z : Composite R P (UnitSp R) S) :
    (mulHom R P).app S ((map₂ (SymSpeciesHom.id R P) (unitHom R P)).app S z)
      = rightUnitor.app S z := by
  have h : ((mulHom R P).app S).comp ((map₂ (SymSpeciesHom.id R P) (unitHom R P)).app S)
      = rightUnitor.app S := hom_ext fun g => by
    rw [LinearMap.comp_apply, map₂_mk]
    show mulApp S (Composite.mk R (genMap₂ (SymSpeciesHom.id R P) (unitHom R P) g))
      = rightUnitorApp S (Composite.mk R g)
    rw [mulApp_mk, rightUnitorApp_mk, rightUnitorFun]
    have hy : (fun a => (unitHom R P).app (g.B a) (g.y a)) = fun a =>
        ∑ v : Unit ≃ g.B a, g.y a v • SymOperad.map (R := R) v (SymOperad.one R) :=
      funext fun a => by
        rw [unitHom_app, Finsupp.lift_apply, Finsupp.sum_fintype]
        exact fun _ => zero_smul R _
    show SymOperad.map (R := R) g.e (SymOperad.totalML R g.m
      (fun a => (unitHom R P).app (g.B a) (g.y a))) = _
    rw [hy, MultilinearMap.map_sum, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [MultilinearMap.map_smul_univ, map_smul]
    congr 1
    have h1 := SymOperad.total_map (R := R) (Equiv.refl g.A) u g.m
      (fun _ => SymOperad.one R) (fun a => SymOperad.map (R := R) (u a) (SymOperad.one R))
      (fun a => rfl)
    rw [SymOperad.map_refl] at h1
    have h2 := SymOperad.total_one_right (R := R) g.m
    have h3 : SymOperad.total R g.m (fun _ => (SymOperad.one R : P Unit))
        = SymOperad.map (R := R) (Equiv.sigmaPUnit g.A).symm g.m := by
      conv_rhs => rw [← h2]
      rw [← SymOperad.map_trans, Equiv.self_trans_symm, SymOperad.map_refl]
    show SymOperad.map (R := R) g.e (SymOperad.total R g.m
      fun a => SymOperad.map (R := R) (u a) (SymOperad.one R)) = _
    rw [← h1, h3, ← SymOperad.map_trans, ← SymOperad.map_trans]
    congr 2
  exact LinearMap.congr_fun h z

variable (R P) in
/-- **An operad is a monoid** for the composition product. -/
noncomputable def toSymMonoid : SymMonoid R P where
  mul := mulHom R P
  unit := unitHom R P
  mul_assoc _ _ _ z := mulHom_assoc z
  one_mul _ _ _ z := mulHom_one z
  mul_one _ _ _ z := mulHom_unit z

end SymOperad

/-! ## Monoids are operads -/

namespace SymMonoid

variable {R P} [SymSpecies R P] (μ : SymMonoid R P) {S : Type} [Fintype S] [DecidableEq S]

/-- **Total composition** in a monoid: the multiplication of a generator. -/
noncomputable def total {A : Type} [Fintype A] [DecidableEq A] {B : A → Type}
    [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (x : P A) (y : ∀ a, P (B a)) : P (Σ a, B a) :=
  μ.mul.app _ (Composite.mk R ⟨A, B, x, y, Equiv.refl _⟩)

/-- The identity operation of a monoid: the unit of the identity of `Unit`. -/
noncomputable def one : P Unit :=
  μ.unit.app Unit (Finsupp.single (Equiv.refl Unit) 1)

lemma mk_eq_map (g : CompGen P P S) :
    Composite.mk R g = SymSpecies.map (R := R) (V := Composite R P P) g.e
      (Composite.mk R ⟨g.A, g.B, g.m, g.y, Equiv.refl _⟩) := by
  rw [symSpecies_map_mk]
  rfl

lemma mul_mk (g : CompGen P P S) :
    μ.mul.app S (Composite.mk R g) = SymSpecies.map (R := R) g.e (μ.total g.m g.y) := by
  rw [mk_eq_map, μ.mul.app_map]
  rfl

variable {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

/-- **Equivariance** of total composition in a monoid. -/
theorem total_map {A' : Type} [Fintype A'] [DecidableEq A'] {B' : A' → Type}
    [∀ a, Fintype (B' a)] [∀ a, DecidableEq (B' a)] (σ : A ≃ A') (τ : ∀ a, B a ≃ B' (σ a))
    (x : P A) (y : ∀ a, P (B a)) (y' : ∀ a, P (B' a))
    (hy : ∀ a, y' (σ a) = SymSpecies.map (R := R) (τ a) (y a)) :
    SymSpecies.map (R := R) (Equiv.sigmaCongr σ τ) (μ.total x y)
      = μ.total (SymSpecies.map (R := R) σ x) y' := by
  rw [total, ← μ.mul.app_map, symSpecies_map_mk, total]
  have h1 := mk_outer (R := R) (⟨A', B', SymSpecies.map (R := R) σ x, y', Equiv.refl _⟩ :
    CompGen P P _) σ x
  have h2 := mk_inner (R := R) (⟨A, B, x, y, Equiv.sigmaCongr σ τ⟩ : CompGen P P _)
    (B := fun a => B' (σ a)) τ
  rw [show (Equiv.sigmaCongrRight τ).symm.trans (Equiv.sigmaCongr σ τ)
      = (Equiv.sigmaCongrLeft σ).trans (Equiv.refl _) from Equiv.ext fun ⟨a, b'⟩ => by
        show (⟨σ a, τ a ((τ a).symm b')⟩ : Σ a', B' a') = ⟨σ a, b'⟩
        rw [Equiv.apply_symm_apply],
    ← funext hy] at h2
  exact congrArg (μ.mul.app _) (h2.symm.trans h1.symm)

/-- **The left unit law** of total composition in a monoid. -/
theorem total_one_left {E : Unit → Type} [∀ u, Fintype (E u)] [∀ u, DecidableEq (E u)]
    (y : (u : Unit) → P (E u)) :
    SymSpecies.map (R := R) (Equiv.uniqueSigma E) (μ.total μ.one y) = y () := by
  have h := μ.one_mul _ (Composite.mk R ⟨Unit, E, Finsupp.single (Equiv.refl Unit) 1, y,
    Equiv.refl _⟩)
  rw [map₂_mk] at h
  change μ.total μ.one y = leftUnitorApp _ _ at h
  rw [h, leftUnitorApp_mk, leftUnitorFun]
  show SymSpecies.map (R := R) _ (Finsupp.lift _ R (Unit ≃ Unit) _
    (Finsupp.single (Equiv.refl Unit) 1)) = _
  rw [Finsupp.lift_single', one_smul, ← SymSpecies.map_trans]
  exact (map_congr_equiv (fun _ => rfl) _).trans (SymSpecies.map_refl _)

/-- **The right unit law** of total composition in a monoid. -/
theorem total_one_right (x : P A) :
    SymSpecies.map (R := R) (Equiv.sigmaPUnit A) (μ.total x fun _ => μ.one) = x := by
  have h := μ.mul_one _ (Composite.mk R ⟨A, fun _ => Unit, x,
    fun _ => Finsupp.single (Equiv.refl Unit) 1, Equiv.refl _⟩)
  rw [map₂_mk] at h
  change μ.total x (fun _ => μ.one) = rightUnitorApp _ _ at h
  rw [h, rightUnitorApp_mk, rightUnitorFun]
  show SymSpecies.map (R := R) _ (∑ u : (A → Unit ≃ Unit),
    (∏ a, (Finsupp.single (Equiv.refl Unit) (1 : R)) (u a)) •
      SymSpecies.map (R := R) ((unitsEquiv u).trans (Equiv.refl _)) x) = x
  rw [Fintype.sum_eq_single (fun _ => Equiv.refl Unit) fun u hu =>
      absurd (funext fun _ => Subsingleton.elim _ _) hu]
  simp only [Finsupp.single_eq_same, Finset.prod_const_one, one_smul]
  rw [← SymSpecies.map_trans]
  exact (map_congr_equiv (fun _ => rfl) _).trans (SymSpecies.map_refl _)

/-- **Associativity** of total composition in a monoid. -/
theorem total_assoc {C : (a : A) → B a → Type} [∀ a b, Fintype (C a b)]
    [∀ a b, DecidableEq (C a b)] (x : P A) (y : (a : A) → P (B a))
    (z : (a : A) → (b : B a) → P (C a b)) :
    SymSpecies.map (R := R) (Equiv.sigmaAssoc C) (μ.total (μ.total x y) fun p => z p.1 p.2)
      = μ.total x fun a => μ.total (y a) (z a) := by
  have h := μ.mul_assoc _ (Composite.mk R (⟨Σ a, B a, fun p => C p.1 p.2,
    Composite.mk R (⟨A, B, x, y, Equiv.refl _⟩ : CompGen P P _), fun p => z p.1 p.2,
      Equiv.refl _⟩ : CompGen (Composite R P P) P _))
  simp only [map₂_mk, assoc_app, assocApp_mk, assocLin_mk, μ.mul_mk, SymSpeciesHom.id_app,
    SymSpecies.map_refl] at h
  rw [h, ← SymSpecies.map_trans]
  exact (map_congr_equiv (fun ⟨_, _, _⟩ => rfl) _).trans (SymSpecies.map_refl _)

/-- **Total composition is linear in the outer operation.** -/
lemma total_add (x x' : P A) (y : ∀ a, P (B a)) :
    μ.total (x + x') y = μ.total x y + μ.total x' y := by
  rw [total, total, total, ← map_add]
  exact congrArg _ (mk_add_m (R := R) (⟨A, B, x, y, Equiv.refl _⟩ : CompGen P P _) x')

lemma total_smul (c : R) (x : P A) (y : ∀ a, P (B a)) :
    μ.total (c • x) y = c • μ.total x y := by
  rw [total, total, ← map_smul]
  exact congrArg _ (mk_smul_m (R := R) (⟨A, B, x, y, Equiv.refl _⟩ : CompGen P P _) c)

/-- **Total composition is multilinear in the inserted operations.** -/
lemma total_update_add (x : P A) (y : ∀ a, P (B a)) (a : A) (v v' : P (B a)) :
    μ.total x (update y a (v + v'))
      = μ.total x (update y a v) + μ.total x (update y a v') := by
  rw [total, total, total, ← map_add]
  exact congrArg _ (mk_add_y (R := R) (⟨A, B, x, y, Equiv.refl _⟩ : CompGen P P _) a v v')

lemma total_update_smul (x : P A) (y : ∀ a, P (B a)) (a : A) (c : R) (v : P (B a)) :
    μ.total x (update y a (c • v)) = c • μ.total x (update y a v) := by
  rw [total, total, ← map_smul]
  exact congrArg _ (mk_smul_y (R := R) (⟨A, B, x, y, Equiv.refl _⟩ : CompGen P P _) a c v)

/-- **A monoid is an operad in May's sense**, with its total composition. -/
@[reducible] noncomputable def toMaySetOperad : MaySetOperad P where
  map e x := SymSpecies.map (R := R) e x
  map_refl := SymSpecies.map_refl (R := R)
  map_trans := SymSpecies.map_trans (R := R)
  one := μ.one
  total := μ.total
  total_map σ τ x y y' hy := μ.total_map σ τ x y y' hy
  total_one_left y := μ.total_one_left y
  total_one_right x := μ.total_one_right x
  total_assoc x y z := μ.total_assoc x y z

omit [Fintype A] in
lemma pad_eq_update {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [MaySetOperad T]
    {B' : Type} [Fintype B'] [DecidableEq B'] (i : A) (y y'' : T B') :
    MaySetOperad.pad i y'' = update (MaySetOperad.pad i y) i (MaySetOperad.pad i y'' i) := by
  funext a
  by_cases h : a = i
  · subst h
    rw [update_self]
  · rw [update_of_ne h, MaySetOperad.pad_of_ne h, MaySetOperad.pad_of_ne h]

/-- **A monoid is an operad**: partial composition inserts the unit at all inputs but one, and is
linear in both operations. -/
@[reducible] noncomputable def toSymOperad : SymOperad R P :=
  letI : MaySetOperad P := μ.toMaySetOperad
  letI : SetOperad P := MaySetOperad.toSetOperad
  { map := fun e => SymSpecies.map (R := R) e
    map_refl := SymSpecies.map_refl (R := R)
    map_trans := SymSpecies.map_trans (R := R)
    one := μ.one
    comp := fun {A B} _ _ _ _ i => LinearMap.mk₂ R (fun x y => SetOperad.comp i x y)
      (fun x x' y => by
        show SymSpecies.map (R := R) _ (μ.total (x + x') _) = SymSpecies.map (R := R) _
          (μ.total x _) + SymSpecies.map (R := R) _ (μ.total x' _)
        rw [μ.total_add, map_add])
      (fun c x y => by
        show SymSpecies.map (R := R) _ (μ.total (c • x) _) = c • SymSpecies.map (R := R) _
          (μ.total x _)
        rw [μ.total_smul, map_smul])
      (fun x y y' => by
        have hp : MaySetOperad.pad i (y + y') = update (MaySetOperad.pad i y) i
            (MaySetOperad.pad i y i + MaySetOperad.pad i y' i) := by
          rw [pad_eq_update i y (y + y')]
          congr 1
          rw [MaySetOperad.pad_of_eq rfl, MaySetOperad.pad_of_eq rfl, MaySetOperad.pad_of_eq rfl]
          exact map_add (SymSpecies.map (R := R) (V := P) (May.padIn (rfl : i = i))) y y'
        show SymSpecies.map (R := R) _ (μ.total x (MaySetOperad.pad i (y + y')))
          = SymSpecies.map (R := R) _ (μ.total x (MaySetOperad.pad i y))
            + SymSpecies.map (R := R) _ (μ.total x (MaySetOperad.pad i y'))
        rw [hp, μ.total_update_add, map_add, update_eq_self, ← pad_eq_update])
      (fun c x y => by
        have hp : MaySetOperad.pad i (c • y) = update (MaySetOperad.pad i y) i
            (c • MaySetOperad.pad i y i) := by
          rw [pad_eq_update i y (c • y)]
          congr 1
          rw [MaySetOperad.pad_of_eq rfl, MaySetOperad.pad_of_eq rfl]
          exact map_smul (SymSpecies.map (R := R) (V := P) (May.padIn (rfl : i = i))) c y
        show SymSpecies.map (R := R) _ (μ.total x (MaySetOperad.pad i (c • y)))
          = c • SymSpecies.map (R := R) _ (μ.total x (MaySetOperad.pad i y))
        rw [hp, μ.total_update_smul, map_smul, update_eq_self])
    map_comp := fun σ τ i x y => SetOperad.map_comp σ τ i x y
    comp_one := fun i x => SetOperad.comp_one i x
    one_comp := fun y => SetOperad.one_comp y
    comp_assoc_seq := fun i j x y z => SetOperad.comp_assoc_seq i j x y z
    comp_assoc_par := fun hik x y z => SetOperad.comp_assoc_par hik x y z }

omit [SymSpecies R P] in
@[ext] theorem ext [SymSpecies R P] {μ ν : SymMonoid R P} (hmul : μ.mul = ν.mul)
    (hunit : μ.unit = ν.unit) : μ = ν := by
  cases μ
  cases ν
  cases hmul
  cases hunit
  rfl

/-- **Total composition in the operad of a monoid** is that of the monoid. -/
theorem total_toSymOperad (x : P A) (y : ∀ a, P (B a)) :
    @SymOperad.total R _ P _ _ μ.toSymOperad A _ _ B _ _ x y = μ.total x y := by
  letI : SymOperad R P := μ.toSymOperad
  have hI : (instSetOperadUnd R P : SetOperad (Und R P))
      = (@MaySetOperad.toSetOperad P μ.toMaySetOperad : SetOperad (Und R P)) :=
    SetOperad.ext_of (fun _ _ => rfl) rfl (fun _ _ _ => rfl)
  show (Und.of R P).symm (@SetOperad.total (Und R P) (instSetOperadUnd R P) A _ _ B _ _
    (Und.of R P x) fun a => Und.of R P (y a)) = _
  rw [hI]
  exact @MaySetOperad.total_toSetOperad P μ.toMaySetOperad A _ _ B _ _ x y

/-- **From a monoid to an operad and back.** -/
theorem toSymOperad_toSymMonoid :
    @SymOperad.toSymMonoid R _ P _ _ μ.toSymOperad = μ := by
  letI : SymOperad R P := μ.toSymOperad
  ext S _ _ x
  · refine LinearMap.congr_fun (hom_ext (φ := (SymOperad.mulHom R P).app S) (ψ := μ.mul.app S)
      fun g => ?_) x
    rw [μ.mul_mk, SymOperad.mulHom_app_mk]
    exact congrArg _ (total_toSymOperad μ g.m g.y)
  · refine LinearMap.congr_fun (Finsupp.lhom_ext' fun u => LinearMap.ext_ring ?_) x
    show (SymOperad.unitHom R P).app S (Finsupp.single u 1) = μ.unit.app S (Finsupp.single u 1)
    rw [SymOperad.unitHom_app, Finsupp.lift_single', one_smul, UnitSp.single_eq_map,
      μ.unit.app_map]
    rfl

end SymMonoid

/-! ## Operads from their monoids -/

namespace SymOperad

variable {R P}

/-- **Two operad structures** with the same relabelling, unit and partial composition are
equal. -/
theorem ext_of {I J : SymOperad R P}
    (hmap : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (x : P A), @SymOperad.map R _ P _ _ I A B _ _ _ _ e x
        = @SymOperad.map R _ P _ _ J A B _ _ _ _ e x)
    (hone : @SymOperad.one R _ P _ _ I = @SymOperad.one R _ P _ _ J)
    (hcomp : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (x : P A) (y : P B), @SymOperad.comp R _ P _ _ I A B _ _ _ _ i x y
        = @SymOperad.comp R _ P _ _ J A B _ _ _ _ i x y) :
    I = J := by
  obtain ⟨mI, _, _, oI, cI, _, _, _, _, _⟩ := I
  obtain ⟨mJ, _, _, oJ, cJ, _, _, _, _, _⟩ := J
  have h1 : @mI = @mJ := by
    funext A B _ _ _ _ e
    exact LinearMap.ext (hmap e)
  have h2 : @cI = @cJ := by
    funext A B _ _ _ _ i
    exact LinearMap.ext₂ (hcomp i)
  subst h1 h2
  cases hone
  rfl

/-- **From an operad to a monoid and back.** -/
theorem toSymMonoid_toSymOperad [inst : SymOperad R P] :
    (SymOperad.toSymMonoid R P).toSymOperad = inst := by
  have hone : (SymOperad.toSymMonoid R P).one = SymOperad.one R := by
    show (unitHom R P).app Unit (Finsupp.single (Equiv.refl Unit) 1) = _
    rw [unitHom_app, Finsupp.lift_single', one_smul, SymOperad.map_refl]
  have htotal : ∀ {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
      [∀ a, DecidableEq (B a)] (x : P A) (y : ∀ a, P (B a)),
      (SymOperad.toSymMonoid R P).total x y = SymOperad.total R x y := by
    intro A _ _ B _ _ x y
    show mulApp _ (Composite.mk R ⟨A, B, x, y, Equiv.refl _⟩) = _
    rw [mulApp_mk, SymOperad.map_refl]
  have hM : (SymOperad.toSymMonoid R P).toMaySetOperad
      = (SetOperad.toMaySetOperad (Und R P) : MaySetOperad (Und R P)) :=
    MaySetOperad.ext_of (fun _ _ => rfl) hone fun x y => htotal x y
  refine ext_of (fun _ _ => rfl) hone fun i x y => ?_
  show @MaySetOperad.comp P (SymOperad.toSymMonoid R P).toMaySetOperad _ _ _ _ _ _ i x y = _
  rw [hM]
  exact MaySetOperad.comp_toMaySetOperad (S := Und R P) i x y

end SymOperad

end Operad
