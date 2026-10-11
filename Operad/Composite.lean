/-
# The composition product of linear species

For linear species `M` and `N`, the **composite** `M ∘ N` has, at a finite type `S`, the classes
`⟨m; y; e⟩` of an operation `m ∈ M A`, an operation `y a ∈ N (B a)` at every input `a` of `m`,
and a naming `e : (Σ a, B a) ≃ S` of the inputs; up to linearity in `m`, multilinearity in `y`,
and relabelling of the inputs of `m` and of each `y a` (`Operad.Composite`). This is the
classical `(M ∘ N)(S) = ⊕_π M(π) ⊗ ⊗_{b ∈ π} N(b)`, the sum over the partitions `π` of `S`,
presented without choosing representatives.

* `Operad.Composite.lift`, `Operad.Composite.hom_ext`: **linear maps out of a composite** are the
  functions on generators respecting the relations (`Operad.CompGen.Respects`), and agree when
  they agree on generators.
* Relabelling the inputs makes `M ∘ N` a linear species (`Operad.Composite.instSymSpecies`),
  functorial in both variables (`Operad.Composite.map₂`).
* **The unit** `I` (`Operad.UnitSp`): the combinations of bijections `Unit ≃ S`. **The unitors**
  `I ∘ M ≅ M ≅ M ∘ I` (`Operad.Composite.leftUnitorEquiv`, `Operad.Composite.rightUnitorEquiv`).
* **The associator** `(M ∘ N) ∘ L → M ∘ (N ∘ L)` (`Operad.Composite.assoc`), sending
  `⟨⟨m; n; f⟩; l; e⟩` to `⟨m; ⟨n a; l⟩_a; e'⟩`; it is an isomorphism
  (`Operad.Composite.assocEquiv`, in `Operad.CompositeAssoc`).
-/
import Operad.MultilinearQuot
import Operad.SpeciesOp
import Mathlib.Data.Fintype.Perm

universe u v w x

namespace Operad

open Function

/-! ## Generators and relations -/

/-- **A generator of the composite** `M ∘ N` at `S`: an operation `m` with inputs `A`, an operation
`y a` with inputs `B a` at every input `a` of `m`, and the naming `e` of the inputs. -/
structure CompGen (M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w) (S : Type) where
  /-- The inputs of the outer operation. -/
  A : Type
  [instFintypeA : Fintype A]
  [instDecEqA : DecidableEq A]
  /-- The inputs of the inner operations. -/
  B : A → Type
  [instFintypeB : ∀ a, Fintype (B a)]
  [instDecEqB : ∀ a, DecidableEq (B a)]
  /-- The outer operation. -/
  m : M A
  /-- The inner operations. -/
  y : ∀ a, N (B a)
  /-- The naming of the inputs. -/
  e : (Σ a, B a) ≃ S

attribute [instance] CompGen.instFintypeA CompGen.instDecEqA CompGen.instFintypeB
  CompGen.instDecEqB

/-- **Relabelling the inputs** of a generator. -/
def CompGen.relabel {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} {S S' : Type}
    (g : CompGen M N S) (f : S ≃ S') : CompGen M N S' :=
  { g with e := g.e.trans f }

variable {R : Type u} [CommRing R]
  {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [SymSpecies R N]

variable (R M N) in
/-- **The relations of the composite**: linearity in the outer operation, multilinearity in the
inner ones, and relabelling the inputs of the outer operation and of the inner ones. -/
inductive CompRel (S : Type) : (CompGen M N S →₀ R) → Prop
  | add_m (g : CompGen M N S) (m' : M g.A) :
      CompRel S (Finsupp.single { g with m := g.m + m' } 1 - Finsupp.single g 1
        - Finsupp.single { g with m := m' } 1)
  | smul_m (g : CompGen M N S) (c : R) :
      CompRel S (Finsupp.single { g with m := c • g.m } 1 - c • Finsupp.single g 1)
  | add_y (g : CompGen M N S) (a : g.A) (z z' : N (g.B a)) :
      CompRel S (Finsupp.single { g with y := update g.y a (z + z') } 1
        - Finsupp.single { g with y := update g.y a z } 1
        - Finsupp.single { g with y := update g.y a z' } 1)
  | smul_y (g : CompGen M N S) (a : g.A) (c : R) (z : N (g.B a)) :
      CompRel S (Finsupp.single { g with y := update g.y a (c • z) } 1
        - c • Finsupp.single { g with y := update g.y a z } 1)
  | outer (g : CompGen M N S) {A : Type} [Fintype A] [DecidableEq A] (σ : A ≃ g.A) (m : M A) :
      CompRel S (Finsupp.single { g with m := SymSpecies.map (R := R) σ m } 1
        - Finsupp.single ⟨A, fun a => g.B (σ a), m, fun a => g.y (σ a),
            (Equiv.sigmaCongrLeft σ).trans g.e⟩ 1)
  | inner (g : CompGen M N S) {B : g.A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
      (τ : ∀ a, g.B a ≃ B a) :
      CompRel S (Finsupp.single ⟨g.A, B, g.m, fun a => SymSpecies.map (R := R) (τ a) (g.y a),
          (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ 1 - Finsupp.single g 1)

variable (R M N) in
/-- **The composite** `M ∘ N` of linear species, at a finite type `S`. -/
@[nolint unusedArguments]
def Composite (S : Type) [Fintype S] [DecidableEq S] : Type (max 1 u v w) :=
  (CompGen M N S →₀ R) ⧸ Submodule.span R {x | CompRel R M N S x}

namespace Composite

variable {S : Type} [Fintype S] [DecidableEq S]

noncomputable instance instAddCommGroup : AddCommGroup (Composite R M N S) :=
  Submodule.Quotient.addCommGroup _

noncomputable instance instModule : Module R (Composite R M N S) :=
  Submodule.Quotient.module _

variable (R) in
/-- **The class of a generator.** -/
noncomputable def mk (g : CompGen M N S) : Composite R M N S :=
  (Submodule.Quotient.mk (Finsupp.single g 1) :
    (CompGen M N S →₀ R) ⧸ Submodule.span R {x | CompRel R M N S x})

omit [Fintype S] [DecidableEq S] in
lemma mk_rel {x : CompGen M N S →₀ R} (hx : CompRel R M N S x) :
    (Submodule.Quotient.mk x : (CompGen M N S →₀ R) ⧸ Submodule.span R {x | CompRel R M N S x})
      = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span hx)

lemma mk_add_m (g : CompGen M N S) (m' : M g.A) :
    mk R { g with m := g.m + m' } = mk R g + mk R { g with m := m' } := by
  have h := mk_rel (CompRel.add_m (R := R) g m')
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, sub_sub, sub_eq_zero] at h
  exact h

lemma mk_smul_m (g : CompGen M N S) (c : R) : mk R { g with m := c • g.m } = c • mk R g := by
  have h := mk_rel (CompRel.smul_m g c)
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero] at h
  exact h

lemma mk_add_y (g : CompGen M N S) (a : g.A) (z z' : N (g.B a)) :
    mk R { g with y := update g.y a (z + z') }
      = mk R { g with y := update g.y a z } + mk R { g with y := update g.y a z' } := by
  have h := mk_rel (CompRel.add_y (R := R) g a z z')
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, sub_sub, sub_eq_zero] at h
  exact h

lemma mk_smul_y (g : CompGen M N S) (a : g.A) (c : R) (z : N (g.B a)) :
    mk R { g with y := update g.y a (c • z) } = c • mk R { g with y := update g.y a z } := by
  have h := mk_rel (CompRel.smul_y g a c z)
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero] at h
  exact h

/-- **Relabelling the inputs of the outer operation.** -/
lemma mk_outer (g : CompGen M N S) {A : Type} [Fintype A] [DecidableEq A] (σ : A ≃ g.A)
    (m : M A) :
    mk R { g with m := SymSpecies.map (R := R) σ m }
      = mk R ⟨A, fun a => g.B (σ a), m, fun a => g.y (σ a),
          (Equiv.sigmaCongrLeft σ).trans g.e⟩ := by
  have h := mk_rel (CompRel.outer (R := R) g σ m)
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at h
  exact h

/-- **Relabelling the inputs of the inner operations.** -/
lemma mk_inner (g : CompGen M N S) {B : g.A → Type} [∀ a, Fintype (B a)]
    [∀ a, DecidableEq (B a)] (τ : ∀ a, g.B a ≃ B a) :
    mk R ⟨g.A, B, g.m, fun a => SymSpecies.map (R := R) (τ a) (g.y a),
        (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ = mk R g := by
  have h := mk_rel (CompRel.inner (R := R) g τ)
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at h
  exact h


/-- **A generator is linear in its outer operation.** -/
noncomputable def mkM (g : CompGen M N S) : M g.A →ₗ[R] Composite R M N S where
  toFun m := mk R { g with m := m }
  map_add' m m' := mk_add_m { g with m := m } m'
  map_smul' c m := mk_smul_m { g with m := m } c

lemma mkM_apply (g : CompGen M N S) (m : M g.A) : mkM g m = mk R { g with m := m } := rfl

/-- **A generator is multilinear in its inner operations.** -/
noncomputable def mkY (g : CompGen M N S) :
    MultilinearMap R (fun a => N (g.B a)) (Composite R M N S) where
  toFun y := mk R { g with y := y }
  map_update_add' := by
    intro d y a z z'
    obtain rfl : d = g.instDecEqA := Subsingleton.elim _ _
    exact mk_add_y { g with y := y } a z z'
  map_update_smul' := by
    intro d y a c z
    obtain rfl : d = g.instDecEqA := Subsingleton.elim _ _
    exact mk_smul_y { g with y := y } a c z

lemma mkY_apply (g : CompGen M N S) (y : ∀ a, N (g.B a)) : mkY g y = mk R { g with y := y } :=
  rfl

/-- **A generator only depends on its naming of the inputs as a bijection.** -/
lemma mk_congr_e (g : CompGen M N S) (e' : (Σ a, g.B a) ≃ S) (h : ∀ p, g.e p = e' p) :
    mk R g = mk R { g with e := e' } := by
  rw [show e' = g.e from (Equiv.ext h).symm]
end Composite

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [SymSpecies R N] in
lemma Finsupp.lift_single' {X W : Type*} [AddCommGroup W] [Module R W] (F : X → W) (x : X)
    (c : R) : Finsupp.lift W R X F (Finsupp.single x c) = c • F x := by
  rw [Finsupp.lift_apply, Finsupp.sum_single_index]
  rw [zero_smul]

variable (R) in
/-- **The functions on generators respecting the relations of the composite**: they define the
linear maps out of it. -/
structure CompGen.Respects {S : Type} {W : Type x} [AddCommGroup W] [Module R W]
    (F : CompGen M N S → W) : Prop where
  add_m (g : CompGen M N S) (m' : M g.A) : F { g with m := g.m + m' } = F g + F { g with m := m' }
  smul_m (g : CompGen M N S) (c : R) : F { g with m := c • g.m } = c • F g
  add_y (g : CompGen M N S) (a : g.A) (z z' : N (g.B a)) :
    F { g with y := update g.y a (z + z') }
      = F { g with y := update g.y a z } + F { g with y := update g.y a z' }
  smul_y (g : CompGen M N S) (a : g.A) (c : R) (z : N (g.B a)) :
    F { g with y := update g.y a (c • z) } = c • F { g with y := update g.y a z }
  outer (g : CompGen M N S) {A : Type} [Fintype A] [DecidableEq A] (σ : A ≃ g.A) (m : M A) :
    F { g with m := SymSpecies.map (R := R) σ m }
      = F ⟨A, fun a => g.B (σ a), m, fun a => g.y (σ a), (Equiv.sigmaCongrLeft σ).trans g.e⟩
  inner (g : CompGen M N S) {B : g.A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    (τ : ∀ a, g.B a ≃ B a) :
    F ⟨g.A, B, g.m, fun a => SymSpecies.map (R := R) (τ a) (g.y a),
        (Equiv.sigmaCongrRight τ).symm.trans g.e⟩ = F g

namespace Composite

variable {S : Type} [Fintype S] [DecidableEq S] {W : Type x} [AddCommGroup W] [Module R W]

/-- **The linear map out of a composite** with given values on generators. -/
noncomputable def lift (F : CompGen M N S → W) (hF : CompGen.Respects R F) :
    Composite R M N S →ₗ[R] W :=
  Submodule.liftQ (Submodule.span R {x | CompRel R M N S x}) (Finsupp.lift W R _ F) <|
    Submodule.span_le.2 fun x hx => by
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      cases hx with
      | add_m g m' =>
        simp only [map_sub, Finsupp.lift_single', one_smul, hF.add_m]
        abel
      | smul_m g c => simp only [map_sub, map_smul, Finsupp.lift_single', one_smul, hF.smul_m,
          sub_self]
      | add_y g a z z' =>
        simp only [map_sub, Finsupp.lift_single', one_smul, hF.add_y]
        abel
      | smul_y g a c z => simp only [map_sub, map_smul, Finsupp.lift_single', one_smul,
          hF.smul_y, sub_self]
      | outer g σ m => simp only [map_sub, Finsupp.lift_single', one_smul, hF.outer, sub_self]
      | inner g τ => simp only [map_sub, Finsupp.lift_single', one_smul, hF.inner, sub_self]

@[simp] lemma lift_mk (F : CompGen M N S → W) (hF : CompGen.Respects R F) (g : CompGen M N S) :
    lift F hF (mk R g) = F g := by
  show Submodule.liftQ _ _ _ (Submodule.Quotient.mk (Finsupp.single g 1)) = F g
  rw [Submodule.liftQ_apply, Finsupp.lift_single', one_smul]

/-- **Linear maps out of a composite agree when they agree on generators.** -/
theorem hom_ext {φ ψ : Composite R M N S →ₗ[R] W} (h : ∀ g, φ (mk R g) = ψ (mk R g)) : φ = ψ :=
  Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun g => LinearMap.ext_ring (h g))

omit [Fintype S] [DecidableEq S] in
/-- **Induction on a composite**: a property closed under linear combinations holds as soon as
it holds on generators. -/
@[elab_as_elim]
theorem induction_on [Fintype S] [DecidableEq S] {P : Composite R M N S → Prop}
    (z : Composite R M N S) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : R) x, P x → P (c • x)) (hmk : ∀ g, P (mk R g)) : P z := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (Submodule.span R {x | CompRel R M N S x}) z
  induction x using Finsupp.induction_linear with
  | zero => exact h0
  | add x y hx hy => exact hadd _ _ hx hy
  | single g c =>
    rw [← mul_one c, ← smul_eq_mul, ← Finsupp.smul_single, Submodule.Quotient.mk_smul]
    exact hsmul c _ (hmk g)

/-! ### Relabelling -/

/-- **Relabelling the inputs of a composite.** -/
noncomputable def map {S' : Type} [Fintype S'] [DecidableEq S'] (f : S ≃ S') :
    Composite R M N S →ₗ[R] Composite R M N S' :=
  lift (fun g => mk R (g.relabel f))
    { add_m := fun g m' => mk_add_m (g.relabel f) m'
      smul_m := fun g c => mk_smul_m (g.relabel f) c
      add_y := fun g a z z' => mk_add_y (g.relabel f) a z z'
      smul_y := fun g a c z => mk_smul_y (g.relabel f) a c z
      outer := @fun g _ _ _ σ m => mk_outer (g.relabel f) σ m
      inner := @fun g _ _ _ τ => mk_inner (g.relabel f) τ }

@[simp] lemma map_mk {S' : Type} [Fintype S'] [DecidableEq S'] (f : S ≃ S') (g : CompGen M N S) :
    map f (mk R g) = mk R (g.relabel f) :=
  lift_mk _ _ g

/-- **The composite is a linear species.** -/
noncomputable instance instSymSpecies : SymSpecies R (Composite R M N) where
  map f := map f
  map_refl := @fun A _ _ x => by
    have h : map (R := R) (M := M) (N := N) (Equiv.refl A) = LinearMap.id :=
      hom_ext fun g => by rw [map_mk]; rfl
    exact LinearMap.congr_fun h x
  map_trans := @fun A B C _ _ _ _ _ _ f f' x => by
    have h : map (R := R) (M := M) (N := N) (f.trans f') = (map f').comp (map f) :=
      hom_ext fun g => by rw [map_mk, LinearMap.comp_apply, map_mk, map_mk]; rfl
    exact LinearMap.congr_fun h x

lemma symSpecies_map_mk {S' : Type} [Fintype S'] [DecidableEq S'] (f : S ≃ S')
    (g : CompGen M N S) :
    SymSpecies.map (R := R) (V := Composite R M N) f (mk R g) = mk R (g.relabel f) :=
  map_mk f g

end Composite

/-! ## Functoriality -/

namespace Composite

variable {M' : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M' A)] [SymSpecies R M']
  {N' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N' A)] [SymSpecies R N']

/-- A generator, with its operations replaced by their images. -/
abbrev genMap₂ (φ : SymSpeciesHom R M M') (ψ : SymSpeciesHom R N N') {S : Type}
    (g : CompGen M N S) : CompGen M' N' S :=
  ⟨g.A, g.B, φ.app _ g.m, fun a => ψ.app _ (g.y a), g.e⟩

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M] in
lemma app_update (ψ : SymSpeciesHom R N N') {S : Type} (g : CompGen M N S) (a : g.A)
    (z : N (g.B a)) :
    (fun a' => ψ.app _ (update g.y a z a')) = update (fun a' => ψ.app _ (g.y a')) a (ψ.app _ z) :=
  funext fun a' => apply_update (fun a' => ⇑(ψ.app (g.B a'))) g.y a z a'

/-- The components of the composite of morphisms of species. -/
noncomputable def map₂App (φ : SymSpeciesHom R M M') (ψ : SymSpeciesHom R N N') (S : Type)
    [Fintype S] [DecidableEq S] : Composite R M N S →ₗ[R] Composite R M' N' S :=
  lift (fun g => mk R (genMap₂ φ ψ g))
    { add_m := fun g m' => by
        show mk R ⟨g.A, g.B, φ.app _ (g.m + m'), _, g.e⟩ = _
        rw [map_add]
        exact mk_add_m (genMap₂ φ ψ g) (φ.app _ m')
      smul_m := fun g c => by
        show mk R ⟨g.A, g.B, φ.app _ (c • g.m), _, g.e⟩ = _
        rw [map_smul]
        exact mk_smul_m (genMap₂ φ ψ g) c
      add_y := fun g a z z' => by
        show mk R ⟨g.A, g.B, φ.app _ g.m, fun a' => ψ.app _ (update g.y a (z + z') a'), g.e⟩
          = mk R ⟨g.A, g.B, φ.app _ g.m, fun a' => ψ.app _ (update g.y a z a'), g.e⟩
            + mk R ⟨g.A, g.B, φ.app _ g.m, fun a' => ψ.app _ (update g.y a z' a'), g.e⟩
        rw [app_update, app_update, app_update, map_add]
        exact mk_add_y (genMap₂ φ ψ g) a _ _
      smul_y := fun g a c z => by
        show mk R ⟨g.A, g.B, φ.app _ g.m, fun a' => ψ.app _ (update g.y a (c • z) a'), g.e⟩
          = c • mk R ⟨g.A, g.B, φ.app _ g.m, fun a' => ψ.app _ (update g.y a z a'), g.e⟩
        rw [app_update, app_update, map_smul]
        exact mk_smul_y (genMap₂ φ ψ g) a c _
      outer := @fun g _ _ _ σ m => by
        show mk R ⟨g.A, g.B, φ.app _ (SymSpecies.map (R := R) σ m), _, g.e⟩ = _
        rw [φ.app_map]
        exact mk_outer (genMap₂ φ ψ g) σ (φ.app _ m)
      inner := @fun g _ _ _ τ => by
        show mk R ⟨g.A, _, φ.app _ g.m, fun a => ψ.app _ (SymSpecies.map (R := R) (τ a) (g.y a)),
          _⟩ = _
        simp only [ψ.app_map]
        exact mk_inner (genMap₂ φ ψ g) τ }

lemma map₂App_mk (φ : SymSpeciesHom R M M') (ψ : SymSpeciesHom R N N') {S : Type}
    [Fintype S] [DecidableEq S] (g : CompGen M N S) :
    map₂App φ ψ S (mk R g) = mk R (genMap₂ φ ψ g) :=
  lift_mk _ _ g

/-- **The composite of morphisms of species.** -/
noncomputable def map₂ (φ : SymSpeciesHom R M M') (ψ : SymSpeciesHom R N N') :
    SymSpeciesHom R (Composite R M N) (Composite R M' N') where
  app S _ _ := map₂App φ ψ S
  app_map f x := by
    have h := hom_ext (φ := (map₂App φ ψ _).comp (map f)) (ψ := (map f).comp (map₂App φ ψ _))
      fun g => by
        simp only [LinearMap.comp_apply, map_mk, map₂App_mk]
        rfl
    exact LinearMap.congr_fun h x

@[simp] lemma map₂_mk (φ : SymSpeciesHom R M M') (ψ : SymSpeciesHom R N N') {S : Type}
    [Fintype S] [DecidableEq S] (g : CompGen M N S) :
    (map₂ φ ψ).app S (mk R g) = mk R (genMap₂ φ ψ g) :=
  map₂App_mk φ ψ g

end Composite

/-! ## The unit -/

variable (R) in
/-- **The unit species** `I`: the formal combinations of bijections `Unit ≃ S`, so `R` on the
one-element types and `0` elsewhere. -/
@[nolint unusedArguments]
abbrev UnitSp (S : Type) [Fintype S] [DecidableEq S] : Type u := (Unit ≃ S) →₀ R

/-- **The unit species is a linear species.** -/
noncomputable instance UnitSp.instSymSpecies : SymSpecies R (UnitSp R) where
  map f := Finsupp.lmapDomain R R fun u => u.trans f
  map_refl x := Finsupp.mapDomain_id
  map_trans f f' x := by
    show Finsupp.mapDomain _ x = Finsupp.mapDomain _ (Finsupp.mapDomain _ x)
    rw [← Finsupp.mapDomain_comp]
    rfl

lemma UnitSp.map_apply {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']
    (f : S ≃ S') (x : UnitSp R S) :
    SymSpecies.map (R := R) (V := UnitSp R) f x = Finsupp.mapDomain (fun u => u.trans f) x :=
  rfl

lemma UnitSp.single_eq_map {S : Type} [Fintype S] [DecidableEq S] (u : Unit ≃ S) (c : R) :
    (Finsupp.single u c : UnitSp R S)
      = SymSpecies.map (R := R) (V := UnitSp R) u (Finsupp.single (Equiv.refl Unit) c) := by
  rw [UnitSp.map_apply, Finsupp.mapDomain_single]
  rfl

/-- The inputs of the operation inserted at the only input of an operation. -/
def unitSigma {A : Type} (u : Unit ≃ A) (B : A → Type) : B (u ()) ≃ Σ a, B a :=
  (Equiv.uniqueSigma fun x : Unit => B (u x)).symm.trans (Equiv.sigmaCongrLeft u)

@[simp] lemma unitSigma_apply {A : Type} (u : Unit ≃ A) (B : A → Type) (b : B (u ())) :
    unitSigma u B b = ⟨u (), b⟩ :=
  rfl

lemma eq_unit_apply {A : Type} (u : Unit ≃ A) (a : A) : a = u () :=
  (u.apply_symm_apply a).symm.trans (congrArg u (Subsingleton.elim _ _))

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [SymSpecies R N] in
lemma Finsupp.lift_add_fun {X W : Type*} [AddCommGroup W] [Module R W] {f f₁ f₂ : X → W}
    (h : ∀ x, f x = f₁ x + f₂ x) (p : X →₀ R) :
    Finsupp.lift W R X f p = Finsupp.lift W R X f₁ p + Finsupp.lift W R X f₂ p := by
  rw [← LinearMap.add_apply, ← map_add, show f = f₁ + f₂ from funext h]

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [SymSpecies R N] in
lemma Finsupp.lift_smul_fun {X W : Type*} [AddCommGroup W] [Module R W] {f f₁ : X → W} (c : R)
    (h : ∀ x, f x = c • f₁ x) (p : X →₀ R) :
    Finsupp.lift W R X f p = c • Finsupp.lift W R X f₁ p := by
  rw [Finsupp.lift_apply, Finsupp.lift_apply, Finsupp.smul_sum]
  exact Finsupp.sum_congr fun x _ => by rw [h, smul_comm]

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [SymSpecies R N] in
lemma Finsupp.lift_mapDomain' {X Y W : Type*} [AddCommGroup W] [Module R W] (f : Y → W)
    (h : X → Y) (p : X →₀ R) :
    Finsupp.lift W R Y f (Finsupp.mapDomain h p) = Finsupp.lift W R X (fun x => f (h x)) p := by
  rw [Finsupp.lift_apply, Finsupp.lift_apply, Finsupp.sum_mapDomain_index]
  · exact fun _ => zero_smul R _
  · exact fun _ _ _ => add_smul _ _ _

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [SymSpecies R N] in
lemma Finsupp.linear_lift {X W W' : Type*} [AddCommGroup W] [Module R W] [AddCommGroup W']
    [Module R W'] (φ : W →ₗ[R] W') (f : X → W) (p : X →₀ R) :
    φ (Finsupp.lift W R X f p) = Finsupp.lift W' R X (fun x => φ (f x)) p := by
  rw [Finsupp.lift_apply, Finsupp.lift_apply, map_finsuppSum]
  simp only [map_smul]

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M]
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [SymSpecies R N] in
lemma Finsupp.lift_congr_fun {X W : Type*} [AddCommGroup W] [Module R W] {f f' : X → W}
    (h : ∀ x, f x = f' x) (p : X →₀ R) :
    Finsupp.lift W R X f p = Finsupp.lift W R X f' p := by
  rw [funext h]

lemma map_congr_equiv {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {e e' : A ≃ B} (h : ∀ a, e a = e' a) (x : M A) :
    SymSpecies.map (R := R) e x = SymSpecies.map (R := R) e' x := by
  rw [Equiv.ext h]

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M] in
lemma SymSpecies.map_symm_map' {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [SymSpecies R V]
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B) (x : V A) :
    SymSpecies.map (R := R) e.symm (SymSpecies.map (R := R) e x) = x := by
  rw [← SymSpecies.map_trans, Equiv.self_trans_symm, SymSpecies.map_refl]

namespace Composite

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The left unitor on generators: the inner operation at the only input, relabelled. -/
noncomputable def leftUnitorFun (g : CompGen (UnitSp R) M S) : M S :=
  Finsupp.lift (M S) R (Unit ≃ g.A)
    (fun u => SymSpecies.map (R := R) ((unitSigma u g.B).trans g.e) (g.y (u ()))) g.m

lemma leftUnitorFun_respects : CompGen.Respects R (leftUnitorFun (R := R) (M := M) (S := S)) where
  add_m g m' := map_add _ _ _
  smul_m g c := map_smul _ _ _
  add_y g a z z' := Finsupp.lift_add_fun (fun u => by
    obtain rfl := eq_unit_apply u a
    simp only [update_self, map_add]) g.m
  smul_y g a c z := Finsupp.lift_smul_fun c (fun u => by
    obtain rfl := eq_unit_apply u a
    simp only [update_self, map_smul]) g.m
  outer := @fun g _ _ _ σ m => by
    show Finsupp.lift (M S) R _ _ (Finsupp.mapDomain _ m) = Finsupp.lift (M S) R _ _ m
    rw [Finsupp.lift_mapDomain']
    refine Finsupp.lift_congr_fun (fun u => ?_) m
    apply map_congr_equiv
    intro b
    rfl
  inner := @fun g B _ _ τ => by
    show Finsupp.lift (M S) R _ _ g.m = Finsupp.lift (M S) R _ _ g.m
    refine Finsupp.lift_congr_fun (fun u => ?_) g.m
    rw [← SymSpecies.map_trans]
    apply map_congr_equiv
    intro b
    simp only [Equiv.trans_apply, unitSigma_apply]
    congr 1
    rw [Equiv.symm_apply_eq]
    rfl

/-- The components of the left unitor. -/
noncomputable def leftUnitorApp (S : Type) [Fintype S] [DecidableEq S] :
    Composite R (UnitSp R) M S →ₗ[R] M S :=
  lift leftUnitorFun leftUnitorFun_respects

lemma leftUnitorApp_mk (g : CompGen (UnitSp R) M S) :
    leftUnitorApp S (mk R g) = leftUnitorFun g :=
  lift_mk _ _ g

/-- **The left unitor** `I ∘ M → M`. -/
noncomputable def leftUnitor : SymSpeciesHom R (Composite R (UnitSp R) M) M where
  app S _ _ := leftUnitorApp S
  app_map := @fun A B _ _ _ _ f x => by
    have h := hom_ext (φ := (leftUnitorApp B).comp (map f))
      (ψ := (SymSpecies.map (R := R) f).comp (leftUnitorApp A)) fun g => by
        simp only [LinearMap.comp_apply, map_mk, leftUnitorApp_mk, leftUnitorFun,
          Finsupp.linear_lift]
        refine congrArg (fun F => Finsupp.lift (M B) R (Unit ≃ g.A) F g.m) (funext fun u => ?_)
        rw [← SymSpecies.map_trans]
        rfl
    exact LinearMap.congr_fun h x

/-- The generator with the unit as outer operation. -/
noncomputable def unitGen (x : M S) : CompGen (UnitSp R) M S :=
  ⟨Unit, fun _ => S, Finsupp.single (Equiv.refl Unit) 1, fun _ => x,
    Equiv.uniqueSigma fun _ : Unit => S⟩

/-- The components of the inverse of the left unitor. -/
noncomputable def leftUnitorInvApp (S : Type) [Fintype S] [DecidableEq S] :
    M S →ₗ[R] Composite R (UnitSp R) M S where
  toFun x := mk R (unitGen x)
  map_add' x x' := by
    have h := (mkY (R := R) (unitGen (R := R) (0 : M S))).map_update_add (fun _ => 0) () x x'
    simp only [mkY_apply] at h
    exact h
  map_smul' c x := by
    have h := (mkY (R := R) (unitGen (R := R) (0 : M S))).map_update_smul (fun _ => 0) () c x
    simp only [mkY_apply] at h
    exact h

lemma leftUnitorInvApp_apply (x : M S) : leftUnitorInvApp (R := R) S x = mk R (unitGen x) := rfl

theorem leftUnitorApp_inv (x : M S) : leftUnitorApp S (leftUnitorInvApp (R := R) S x) = x := by
  rw [leftUnitorInvApp_apply, leftUnitorApp_mk, leftUnitorFun]
  show Finsupp.lift (M S) R (Unit ≃ Unit) _ (Finsupp.single (Equiv.refl Unit) 1) = x
  rw [Finsupp.lift_single', one_smul]
  refine (map_congr_equiv ?_ x).trans (SymSpecies.map_refl (R := R) (V := M) x)
  intro b
  rfl

theorem leftUnitorInvApp_leftUnitorApp (z : Composite R (UnitSp R) M S) :
    leftUnitorInvApp S (leftUnitorApp S z) = z := by
  have h : (leftUnitorInvApp (R := R) S).comp (leftUnitorApp (M := M) S) = LinearMap.id :=
    hom_ext fun g => by
      rw [LinearMap.comp_apply, leftUnitorApp_mk g, LinearMap.id_apply, leftUnitorFun,
        Finsupp.linear_lift]
      suffices H : Finsupp.lift (Composite R (UnitSp R) M S) R (Unit ≃ g.A)
          (fun u => leftUnitorInvApp S
          (SymSpecies.map (R := R) ((unitSigma u g.B).trans g.e) (g.y (u ())))) = mkM g by
        rw [H]
        rfl
      refine Finsupp.lhom_ext' fun u => LinearMap.ext_ring ?_
      rw [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.lift_single', one_smul,
        LinearMap.comp_apply, Finsupp.lsingle_apply, mkM_apply]
      have hE : (Equiv.sigmaCongrRight fun _ : Unit => (unitSigma u g.B).trans g.e).symm.trans
          ((Equiv.sigmaCongrLeft u).trans g.e) = Equiv.uniqueSigma fun _ : Unit => S := by
        ext ⟨⟨⟩, s⟩
        show g.e ⟨u (), (unitSigma u g.B).symm (g.e.symm s)⟩ = s
        rw [show (⟨u (), (unitSigma u g.B).symm (g.e.symm s)⟩ : Σ a, g.B a)
          = unitSigma u g.B ((unitSigma u g.B).symm (g.e.symm s)) from rfl,
          Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      calc leftUnitorInvApp S (SymSpecies.map (R := R) ((unitSigma u g.B).trans g.e) (g.y (u ())))
          = mk R ⟨Unit, fun _ => S, Finsupp.single (Equiv.refl Unit) 1,
              fun x => SymSpecies.map (R := R) ((unitSigma u g.B).trans g.e) (g.y (u x)),
              (Equiv.sigmaCongrRight fun _ : Unit => (unitSigma u g.B).trans g.e).symm.trans
                ((Equiv.sigmaCongrLeft u).trans g.e)⟩ := by
            rw [leftUnitorInvApp_apply, hE]
            rfl
        _ = mk R ⟨Unit, fun x => g.B (u x), Finsupp.single (Equiv.refl Unit) 1,
              fun x => g.y (u x), (Equiv.sigmaCongrLeft u).trans g.e⟩ :=
            mk_inner (R := R) (M := UnitSp R) (N := M) (B := fun _ => S) ⟨Unit, fun x => g.B (u x),
              Finsupp.single (Equiv.refl Unit) (1 : R), fun x => g.y (u x),
              (Equiv.sigmaCongrLeft u).trans g.e⟩ fun _ => (unitSigma u g.B).trans g.e
        _ = mk R { g with m := Finsupp.single u (1 : R) } := by
            rw [UnitSp.single_eq_map u, mk_outer]
  exact LinearMap.congr_fun h z

/-- **The left unitor** `I ∘ M ≅ M`, as a linear equivalence in each arity. -/
noncomputable def leftUnitorEquiv (S : Type) [Fintype S] [DecidableEq S] :
    Composite R (UnitSp R) M S ≃ₗ[R] M S :=
  LinearEquiv.ofLinear (leftUnitorApp S) (leftUnitorInvApp S)
    (LinearMap.ext leftUnitorApp_inv) (LinearMap.ext leftUnitorInvApp_leftUnitorApp)

/-! ### The right unitor -/

/-- The bijection `A ≃ Σ a, B a` given by the only input of each `B a`. -/
def unitsEquiv {A : Type} {B : A → Type} (u : ∀ a, Unit ≃ B a) : A ≃ Σ a, B a :=
  ((Equiv.sigmaCongrRight fun a => (u a).symm).trans (Equiv.sigmaPUnit A)).symm

@[simp] lemma unitsEquiv_apply {A : Type} {B : A → Type} (u : ∀ a, Unit ≃ B a) (a : A) :
    unitsEquiv u a = ⟨a, u a ()⟩ :=
  rfl

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M] [Fintype S]
  [DecidableEq S] in
lemma prod_update_apply {A : Type} [Fintype A] [DecidableEq A] {B : A → Type}
    (y : ∀ a, (Unit ≃ B a) →₀ R) (u : ∀ a, Unit ≃ B a) (a : A) (v : (Unit ≃ B a) →₀ R) :
    ∏ a', (update y a v a') (u a') = v (u a) * ∏ a' ∈ Finset.univ.erase a, y a' (u a') := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), update_self]
  congr 1
  refine Finset.prod_congr rfl fun a' ha' => ?_
  rw [update_of_ne (Finset.ne_of_mem_erase ha')]

/-- The right unitor on generators: the outer operation, its inputs named by the only input of
each inner unit. -/
noncomputable def rightUnitorFun (g : CompGen M (UnitSp R) S) : M S :=
  ∑ u : (∀ a, Unit ≃ g.B a),
    (∏ a, g.y a (u a)) • SymSpecies.map (R := R) ((unitsEquiv u).trans g.e) g.m

lemma rightUnitorFun_respects :
    CompGen.Respects R (rightUnitorFun (R := R) (M := M) (S := S)) where
  add_m g m' := by
    simp only [rightUnitorFun, map_add, smul_add, Finset.sum_add_distrib]
  smul_m g c := by
    simp only [rightUnitorFun, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun u _ => smul_comm _ _ _
  add_y g a z z' := by
    simp only [rightUnitorFun, prod_update_apply, Finsupp.add_apply, add_mul, add_smul,
      Finset.sum_add_distrib]
  smul_y g a c z := by
    simp only [rightUnitorFun, prod_update_apply, Finsupp.smul_apply, smul_eq_mul, mul_assoc,
      mul_smul, Finset.smul_sum]
  outer := @fun g A _ _ σ m => by
    simp only [rightUnitorFun]
    rw [← (Equiv.piCongrLeft (fun a => Unit ≃ g.B a) σ).sum_comp]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Equiv.prod_comp σ, ← SymSpecies.map_trans]
    congr 1
    · exact Finset.prod_congr rfl fun a _ => by rw [Equiv.piCongrLeft_apply_apply]
    · apply map_congr_equiv
      intro a
      show g.e ⟨σ a, (Equiv.piCongrLeft (fun a => Unit ≃ g.B a) σ u) (σ a) ()⟩
        = g.e ⟨σ a, u a ()⟩
      rw [Equiv.piCongrLeft_apply_apply]
  inner := @fun g B _ _ τ => by
    simp only [rightUnitorFun]
    let T : (∀ a, Unit ≃ g.B a) ≃ ∀ a, Unit ≃ B a :=
      Equiv.piCongrRight fun a => (Equiv.refl Unit).equivCongr (τ a)
    rw [← T.sum_comp]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    · refine Finset.prod_congr rfl fun a _ => ?_
      show Finsupp.mapDomain (fun v => v.trans (τ a)) (g.y a) ((u a).trans (τ a)) = g.y a (u a)
      exact Finsupp.mapDomain_apply (fun v w h => Equiv.ext fun x =>
        (τ a).injective (Equiv.congr_fun h x)) _ _
    · apply map_congr_equiv
      intro a
      show g.e ((Equiv.sigmaCongrRight τ).symm ⟨a, τ a (u a ())⟩) = g.e ⟨a, u a ()⟩
      congr 1
      rw [Equiv.symm_apply_eq]
      rfl

/-- The components of the right unitor. -/
noncomputable def rightUnitorApp (S : Type) [Fintype S] [DecidableEq S] :
    Composite R M (UnitSp R) S →ₗ[R] M S :=
  lift rightUnitorFun rightUnitorFun_respects

lemma rightUnitorApp_mk (g : CompGen M (UnitSp R) S) :
    rightUnitorApp S (mk R g) = rightUnitorFun g :=
  lift_mk _ _ g

/-- **The right unitor** `M ∘ I → M`. -/
noncomputable def rightUnitor : SymSpeciesHom R (Composite R M (UnitSp R)) M where
  app S _ _ := rightUnitorApp S
  app_map := @fun A B _ _ _ _ f x => by
    have h := hom_ext (φ := (rightUnitorApp (M := M) B).comp (map f))
      (ψ := (SymSpecies.map (R := R) f).comp (rightUnitorApp A)) fun g => by
        simp only [LinearMap.comp_apply, map_mk, rightUnitorApp_mk, rightUnitorFun, map_sum,
          map_smul]
        apply Finset.sum_congr rfl
        intro u _
        rw [← SymSpecies.map_trans]
        rfl
    exact LinearMap.congr_fun h x

/-- The generator with units as inner operations. -/
noncomputable def unitsGen (x : M S) : CompGen M (UnitSp R) S :=
  ⟨S, fun _ => Unit, x, fun _ => Finsupp.single (Equiv.refl Unit) 1, Equiv.sigmaPUnit S⟩

/-- The components of the inverse of the right unitor. -/
noncomputable def rightUnitorInvApp (S : Type) [Fintype S] [DecidableEq S] :
    M S →ₗ[R] Composite R M (UnitSp R) S :=
  mkM (unitsGen (R := R) (0 : M S))

lemma rightUnitorInvApp_apply (x : M S) :
    rightUnitorInvApp (R := R) S x = mk R (unitsGen x) :=
  rfl

theorem rightUnitorApp_inv (x : M S) :
    rightUnitorApp S (rightUnitorInvApp (R := R) S x) = x := by
  rw [rightUnitorInvApp_apply, rightUnitorApp_mk, rightUnitorFun]
  show ∑ u : (S → Unit ≃ Unit), (∏ s, (Finsupp.single (Equiv.refl Unit) (1 : R)) (u s)) •
    SymSpecies.map (R := R) ((unitsEquiv u).trans (Equiv.sigmaPUnit S)) x = x
  rw [Fintype.sum_eq_single (fun _ => Equiv.refl Unit) fun u hu =>
      absurd (funext fun _ => Subsingleton.elim _ _) hu]
  simp only [Finsupp.single_eq_same, Finset.prod_const_one, one_smul]
  refine (map_congr_equiv ?_ x).trans (SymSpecies.map_refl (R := R) (V := M) x)
  intro b
  rfl

/-- **A generator is the combination of the generators with basis vectors as inner
operations.** -/
lemma mk_eq_sum_units (g : CompGen M (UnitSp R) S) :
    mk R g = ∑ u : (∀ a, Unit ≃ g.B a),
      (∏ a, g.y a (u a)) • mk R { g with y := fun a => Finsupp.single (u a) (1 : R) } := by
  have hy : g.y = fun a => ∑ v : Unit ≃ g.B a, g.y a v • Finsupp.single v (1 : R) := by
    funext a
    conv_lhs => rw [← Finsupp.univ_sum_single (g.y a)]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  have h := (mkY (R := R) g).map_sum fun a v => g.y a v • Finsupp.single v (1 : R)
  rw [← hy] at h
  rw [show mk R g = mkY (R := R) g g.y from rfl, h]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

theorem rightUnitorInvApp_rightUnitorApp (z : Composite R M (UnitSp R) S) :
    rightUnitorInvApp S (rightUnitorApp S z) = z := by
  have h : (rightUnitorInvApp (R := R) S).comp (rightUnitorApp (M := M) S) = LinearMap.id :=
    hom_ext fun g => by
      rw [LinearMap.comp_apply, rightUnitorApp_mk g, LinearMap.id_apply, rightUnitorFun, map_sum,
        mk_eq_sum_units g]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [map_smul]
      congr 1
      have hE : (Equiv.sigmaCongrRight u).symm.trans ((Equiv.sigmaCongrRight u).trans g.e) = g.e :=
        Equiv.ext fun p => by simp
      calc rightUnitorInvApp S (SymSpecies.map (R := R) ((unitsEquiv u).trans g.e) g.m)
          = mk R ⟨g.A, fun _ => Unit, g.m, fun _ => Finsupp.single (Equiv.refl Unit) (1 : R),
              (Equiv.sigmaCongrRight u).trans g.e⟩ := by
            rw [rightUnitorInvApp_apply]
            refine (mk_outer (unitsGen (R := R) (0 : M S)) ((unitsEquiv u).trans g.e) g.m).trans ?_
            exact congrArg (fun e => mk R (⟨g.A, fun _ => Unit, g.m,
              fun _ => Finsupp.single (Equiv.refl Unit) (1 : R), e⟩ : CompGen M (UnitSp R) S))
              (Equiv.ext fun p => rfl)
        _ = mk R ⟨g.A, g.B, g.m, fun a => SymSpecies.map (R := R) (V := UnitSp R) (u a)
              (Finsupp.single (Equiv.refl Unit) (1 : R)),
              (Equiv.sigmaCongrRight u).symm.trans ((Equiv.sigmaCongrRight u).trans g.e)⟩ :=
            (mk_inner (R := R) (M := M) (N := UnitSp R) (B := g.B) ⟨g.A, fun _ => Unit, g.m,
              fun _ => Finsupp.single (Equiv.refl Unit) (1 : R),
              (Equiv.sigmaCongrRight u).trans g.e⟩ u).symm
        _ = mk R { g with y := fun a => Finsupp.single (u a) (1 : R) } := by
            rw [hE]
            congr 2
            funext a
            rw [← UnitSp.single_eq_map]
  exact LinearMap.congr_fun h z

/-- **The right unitor** `M ∘ I ≅ M`, as a linear equivalence in each arity. -/
noncomputable def rightUnitorEquiv (S : Type) [Fintype S] [DecidableEq S] :
    Composite R M (UnitSp R) S ≃ₗ[R] M S :=
  LinearEquiv.ofLinear (rightUnitorApp S) (rightUnitorInvApp S)
    (LinearMap.ext rightUnitorApp_inv) (LinearMap.ext rightUnitorInvApp_rightUnitorApp)

end Composite

/-! ## The associator -/

lemma Equiv.symm_trans_eq_of {α β γ : Type*} (f : α ≃ β) (g : α ≃ γ) (h : β ≃ γ)
    (H : ∀ q, g q = h (f q)) : f.symm.trans g = h :=
  Equiv.ext fun x => by
    obtain ⟨q, rfl⟩ := f.surjective x
    rw [Equiv.trans_apply, Equiv.symm_apply_apply, H]

namespace Composite

variable {L : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (L A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (L A)] [SymSpecies R L]
  {S U : Type} [Fintype S] [DecidableEq S] [Fintype U] [DecidableEq U]

omit [SymSpecies R M] [SymSpecies R N] [Fintype S] [DecidableEq S] in
/-- **Relabelling along a transport is transport.** -/
lemma map_cast {T : Type} {D : T → Type} [∀ t, Fintype (D t)] [∀ t, DecidableEq (D t)]
    (l : ∀ t, L (D t)) {t t' : T} (h : t = t') :
    SymSpecies.map (R := R) (Equiv.cast (congrArg D h)) (l t) = l t' := by
  subst h
  rw [Equiv.cast_refl, SymSpecies.map_refl]

/-- The inner generators of the associator: the operation `k.y a` with the operations of `l`
plugged in. -/
abbrev assocInner (k : CompGen M N U) (D : U → Type) [∀ t, Fintype (D t)] [∀ t, DecidableEq (D t)]
    (l : ∀ t, L (D t)) (a : k.A) : CompGen N L (Σ b, D (k.e ⟨a, b⟩)) :=
  ⟨k.B a, fun b => D (k.e ⟨a, b⟩), k.y a, fun b => l (k.e ⟨a, b⟩), Equiv.refl _⟩

/-- The naming of the inputs in the associator. -/
def assocE (k : CompGen M N U) (D : U → Type) (e : (Σ t, D t) ≃ S) :
    (Σ a, Σ b, D (k.e ⟨a, b⟩)) ≃ S :=
  (Equiv.sigmaAssoc fun a b => D (k.e ⟨a, b⟩)).symm.trans ((Equiv.sigmaCongrLeft k.e).trans e)

variable (R) in
/-- The generator of `M ∘ (N ∘ L)` of the associator. -/
noncomputable abbrev assocGen (k : CompGen M N U) (D : U → Type) [∀ t, Fintype (D t)]
    [∀ t, DecidableEq (D t)] (l : ∀ t, L (D t)) (e : (Σ t, D t) ≃ S) :
    CompGen M (Composite R N L) S :=
  ⟨k.A, fun a => Σ b, D (k.e ⟨a, b⟩), k.m, fun a => mk R (assocInner k D l a), assocE k D e⟩

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M] [Fintype U] in
lemma assocInner_update (k : CompGen M N U) (D : U → Type) [∀ t, Fintype (D t)]
    [∀ t, DecidableEq (D t)] (l : ∀ t, L (D t)) (a : k.A) (b : k.B a)
    (w : L (D (k.e ⟨a, b⟩))) :
    (fun a' => mk R (assocInner k D (update l (k.e ⟨a, b⟩) w) a'))
      = update (fun a' => mk R (assocInner k D l a')) a
          (mkY (assocInner k D l a) (update (assocInner k D l a).y b w)) := by
  funext a'
  by_cases h : a' = a
  · subst h
    rw [update_self]
    have hinj : Function.Injective fun b' : k.B a' => k.e ⟨a', b'⟩ :=
      fun b₁ b₂ hb => sigma_mk_injective (k.e.injective hb)
    have := update_comp_eq_of_injective' l hinj b w
    simp only [assocInner] at this ⊢
    rw [this]
    rfl
  · rw [update_of_ne h]
    have : (fun b' => update l (k.e ⟨a, b⟩) w (k.e ⟨a', b'⟩)) = fun b' => l (k.e ⟨a', b'⟩) :=
      funext fun b' => update_of_ne (fun hb => h (congrArg Sigma.fst (k.e.injective hb))) _ _
    simp only [assocInner, this]

/-- **The associator is multilinear in the outer operations.** -/
noncomputable def assocML (k : CompGen M N U) (D : U → Type) [∀ t, Fintype (D t)]
    [∀ t, DecidableEq (D t)] (e : (Σ t, D t) ≃ S) :
    MultilinearMap R (fun t => L (D t)) (Composite R M (Composite R N L) S) :=
  MultilinearMap.mk' (fun l => mk R (assocGen R k D l e))
    (fun l t w w' => by
      obtain ⟨⟨a, b⟩, rfl⟩ := k.e.surjective t
      show mk R ⟨k.A, _, k.m,
          fun a' => mk R (assocInner k D (update l (k.e ⟨a, b⟩) (w + w')) a'), _⟩
        = mk R ⟨k.A, _, k.m, fun a' => mk R (assocInner k D (update l (k.e ⟨a, b⟩) w) a'), _⟩
          + mk R ⟨k.A, _, k.m, fun a' => mk R (assocInner k D (update l (k.e ⟨a, b⟩) w') a'), _⟩
      rw [assocInner_update, assocInner_update, assocInner_update]
      simp only [MultilinearMap.map_update_add]
      exact mk_add_y (assocGen R k D l e) a _ _)
    (fun l t c w => by
      obtain ⟨⟨a, b⟩, rfl⟩ := k.e.surjective t
      show mk R ⟨k.A, _, k.m,
          fun a' => mk R (assocInner k D (update l (k.e ⟨a, b⟩) (c • w)) a'), _⟩
        = c • mk R ⟨k.A, _, k.m,
          fun a' => mk R (assocInner k D (update l (k.e ⟨a, b⟩) w) a'), _⟩
      rw [assocInner_update, assocInner_update]
      simp only [MultilinearMap.map_update_smul]
      exact mk_smul_y (assocGen R k D l e) a c _)

omit [Fintype U] in
lemma assocML_apply (k : CompGen M N U) (D : U → Type) [∀ t, Fintype (D t)]
    [∀ t, DecidableEq (D t)] (e : (Σ t, D t) ≃ S) (l : ∀ t, L (D t)) :
    assocML k D e l = mk R (assocGen R k D l e) :=
  rfl

omit [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [SymSpecies R M] [Fintype U]
  [DecidableEq U] in
lemma assocInner_update_y (k : CompGen M N U) (D : U → Type) [∀ t, Fintype (D t)]
    [∀ t, DecidableEq (D t)] (l : ∀ t, L (D t)) (a : k.A) (z : N (k.B a)) :
    (fun a' => mk R (assocInner { k with y := update k.y a z } D l a'))
      = update (fun a' => mk R (assocInner k D l a')) a (mkM (assocInner k D l a) z) := by
  funext a'
  exact apply_update (fun a' (n : N (k.B a')) => mk R (⟨k.B a', fun b => D (k.e ⟨a', b⟩), n,
    fun b => l (k.e ⟨a', b⟩), Equiv.refl _⟩ : CompGen N L _)) k.y a z a'

/-- **The associator, linear in the outer operation.** -/
noncomputable def assocLin (D : U → Type) [∀ t, Fintype (D t)] [∀ t, DecidableEq (D t)]
    (e : (Σ t, D t) ≃ S) :
    Composite R M N U →ₗ[R]
      MultilinearMap R (fun t => L (D t)) (Composite R M (Composite R N L) S) :=
  lift (fun k => assocML k D e)
    { add_m := fun k m' => MultilinearMap.ext fun l => mk_add_m (assocGen R k D l e) m'
      smul_m := fun k c => MultilinearMap.ext fun l => mk_smul_m (assocGen R k D l e) c
      add_y := fun k a z z' => MultilinearMap.ext fun l => by
        show mk R ⟨k.A, _, k.m, fun a' => mk R (assocInner { k with y := update k.y a (z + z') }
          D l a'), _⟩ = mk R ⟨k.A, _, k.m, fun a' => mk R (assocInner { k with y := update k.y a z }
          D l a'), _⟩ + mk R ⟨k.A, _, k.m, fun a' => mk R (assocInner
            { k with y := update k.y a z' } D l a'), _⟩
        rw [assocInner_update_y, assocInner_update_y, assocInner_update_y, map_add]
        exact mk_add_y (assocGen R k D l e) a _ _
      smul_y := fun k a c z => MultilinearMap.ext fun l => by
        show mk R ⟨k.A, _, k.m, fun a' => mk R (assocInner { k with y := update k.y a (c • z) }
          D l a'), _⟩ = c • mk R ⟨k.A, _, k.m, fun a' => mk R (assocInner
            { k with y := update k.y a z } D l a'), _⟩
        rw [assocInner_update_y, assocInner_update_y, map_smul]
        exact mk_smul_y (assocGen R k D l e) a c _
      outer := @fun k A' _ _ σ m => MultilinearMap.ext fun l => by
        refine (mk_outer (assocGen R k D l e) σ m).trans ?_
        exact mk_congr_e _ _ fun p => rfl
      inner := @fun k B' _ _ τ => MultilinearMap.ext fun l => by
        let k'' : CompGen M N U := ⟨k.A, B', k.m, fun a => SymSpecies.map (R := R) (τ a) (k.y a),
          (Equiv.sigmaCongrRight τ).symm.trans k.e⟩
        let Ξ : ∀ a, (Σ b', D (k''.e ⟨a, b'⟩)) ≃ Σ b, D (k.e ⟨a, b⟩) := fun a =>
          Equiv.sigmaCongrLeft (β := fun b => D (k.e ⟨a, b⟩)) (τ a).symm
        have hC : ∀ a, mk R (assocInner k D l a) = SymSpecies.map (R := R)
            (V := Composite R N L) (Ξ a) (mk R (assocInner k'' D l a)) := by
          intro a
          rw [symSpecies_map_mk]
          have h1 := mk_outer (R := R) (M := N) (N := L) ⟨k.B a, fun b => D (k.e ⟨a, b⟩), k.y a,
            fun b => l (k.e ⟨a, b⟩), Equiv.refl _⟩ (τ a).symm
            (SymSpecies.map (R := R) (τ a) (k.y a))
          rw [SymSpecies.map_symm_map'] at h1
          exact h1
        have h3 := mk_inner (R := R) (assocGen R k'' D l e) (B := fun a => Σ b, D (k.e ⟨a, b⟩)) Ξ
        rw [Equiv.symm_trans_eq_of (Equiv.sigmaCongrRight Ξ) (assocE k'' D e) (assocE k D e)
          (fun ⟨_, _, _⟩ => rfl)] at h3
        refine h3.symm.trans ?_
        exact congrArg (fun y => mk R (⟨k.A, fun a => Σ b, D (k.e ⟨a, b⟩), k.m, y, assocE k D e⟩ :
          CompGen M (Composite R N L) S)) (funext hC).symm }

variable (R M N L) in
/-- The associator on generators. -/
noncomputable def assocFun (h : CompGen (Composite R M N) L S) :
    Composite R M (Composite R N L) S :=
  assocLin h.B h.e h.m h.y

lemma assocLin_mk (k : CompGen M N U) (D : U → Type) [∀ t, Fintype (D t)]
    [∀ t, DecidableEq (D t)] (e : (Σ t, D t) ≃ S) (l : ∀ t, L (D t)) :
    assocLin D e (mk R k) l = mk R (assocGen R k D l e) := by
  rw [assocLin, lift_mk]
  rfl

lemma assocFun_respects : CompGen.Respects R (assocFun R M N L (S := S)) where
  add_m h x' := by
    show assocLin h.B h.e (h.m + x') h.y = assocLin h.B h.e h.m h.y + assocLin h.B h.e x' h.y
    rw [map_add]
    rfl
  smul_m h c := by
    show assocLin h.B h.e (c • h.m) h.y = c • assocLin h.B h.e h.m h.y
    rw [map_smul]
    rfl
  add_y h t v v' := (assocLin h.B h.e h.m).map_update_add h.y t v v'
  smul_y h t c v := (assocLin h.B h.e h.m).map_update_smul h.y t c v
  outer := @fun h U' _ _ σ x => by
    show assocLin h.B h.e (SymSpecies.map (R := R) σ x) h.y
      = assocLin (fun t => h.B (σ t)) ((Equiv.sigmaCongrLeft σ).trans h.e) x fun t => h.y (σ t)
    induction x using induction_on with
    | h0 => simp only [map_zero, MultilinearMap.zero_apply]
    | hadd x y hx hy => simp only [map_add, MultilinearMap.add_apply, hx, hy]
    | hsmul c x hx => simp only [map_smul, MultilinearMap.smul_apply, hx]
    | hmk k =>
      rw [symSpecies_map_mk, assocLin_mk, assocLin_mk]
      exact mk_congr_e _ _ fun ⟨_, _, _⟩ => rfl
  inner := @fun h D' _ _ τ => by
    show assocLin D' ((Equiv.sigmaCongrRight τ).symm.trans h.e) h.m
      (fun t => SymSpecies.map (R := R) (τ t) (h.y t)) = assocLin h.B h.e h.m h.y
    induction h.m using induction_on with
    | h0 => simp only [map_zero, MultilinearMap.zero_apply]
    | hadd x y hx hy => simp only [map_add, MultilinearMap.add_apply, hx, hy]
    | hsmul c x hx => simp only [map_smul, MultilinearMap.smul_apply, hx]
    | hmk k =>
      rw [assocLin_mk, assocLin_mk]
      let Ξ : ∀ a, (Σ b, h.B (k.e ⟨a, b⟩)) ≃ Σ b, D' (k.e ⟨a, b⟩) := fun a =>
        Equiv.sigmaCongrRight fun b => τ (k.e ⟨a, b⟩)
      have hC : ∀ a, mk R (assocInner k D' (fun t => SymSpecies.map (R := R) (τ t) (h.y t)) a)
          = SymSpecies.map (R := R) (V := Composite R N L) (Ξ a)
            (mk R (assocInner k h.B h.y a)) := by
        intro a
        rw [symSpecies_map_mk]
        have h1 := mk_inner (R := R) (M := N) (N := L) ⟨k.B a, fun b => h.B (k.e ⟨a, b⟩), k.y a,
          fun b => h.y (k.e ⟨a, b⟩), Ξ a⟩ (B := fun b => D' (k.e ⟨a, b⟩))
          fun b => τ (k.e ⟨a, b⟩)
        rw [Equiv.symm_trans_self] at h1
        exact h1
      have h3 := mk_inner (R := R) (assocGen R k h.B h.y h.e)
        (B := fun a => Σ b, D' (k.e ⟨a, b⟩)) Ξ
      rw [Equiv.symm_trans_eq_of (Equiv.sigmaCongrRight Ξ) (assocE k h.B h.e)
        (assocE k D' ((Equiv.sigmaCongrRight τ).symm.trans h.e))
        (fun ⟨a, b, d⟩ => by
          show h.e ⟨k.e ⟨a, b⟩, d⟩
            = h.e ⟨k.e ⟨a, b⟩, (τ (k.e ⟨a, b⟩)).symm (τ (k.e ⟨a, b⟩) d)⟩
          rw [Equiv.symm_apply_apply])] at h3
      refine Eq.trans ?_ h3
      exact congrArg (fun y => mk R (⟨k.A, fun a => Σ b, D' (k.e ⟨a, b⟩), k.m, y,
        assocE k D' ((Equiv.sigmaCongrRight τ).symm.trans h.e)⟩ :
          CompGen M (Composite R N L) S)) (funext hC)

/-- The components of the associator. -/
noncomputable def assocApp (S : Type) [Fintype S] [DecidableEq S] :
    Composite R (Composite R M N) L S →ₗ[R] Composite R M (Composite R N L) S :=
  lift (assocFun R M N L) assocFun_respects

lemma assocApp_mk (h : CompGen (Composite R M N) L S) :
    assocApp S (mk R h) = assocLin h.B h.e h.m h.y :=
  lift_mk _ _ h

/-- **The associator** `(M ∘ N) ∘ L → M ∘ (N ∘ L)`. -/
noncomputable def assoc :
    SymSpeciesHom R (Composite R (Composite R M N) L) (Composite R M (Composite R N L)) where
  app S _ _ := assocApp S
  app_map := @fun A B _ _ _ _ f x => by
    have h := hom_ext (φ := (assocApp (M := M) (N := N) (L := L) B).comp (map f))
      (ψ := (SymSpecies.map (R := R) f).comp (assocApp A)) fun h => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, map_mk, assocApp_mk, assocApp_mk]
        show assocLin h.B (h.e.trans f) h.m h.y
          = SymSpecies.map (R := R) f (assocLin h.B h.e h.m h.y)
        induction h.m using induction_on with
        | h0 => simp only [map_zero, MultilinearMap.zero_apply]
        | hadd x y hx hy => simp only [map_add, MultilinearMap.add_apply, hx, hy]
        | hsmul c x hx => simp only [map_smul, MultilinearMap.smul_apply, hx]
        | hmk k =>
          rw [assocLin_mk, assocLin_mk, symSpecies_map_mk]
          rfl
    exact LinearMap.congr_fun h x

@[simp] lemma assoc_app (z : Composite R (Composite R M N) L S) :
    (assoc (M := M) (N := N) (L := L)).app S z = assocApp S z :=
  rfl

end Composite

end Operad
