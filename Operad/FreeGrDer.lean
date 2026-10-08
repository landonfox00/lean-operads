/-
# Derivations of free graded operads induced by maps of generators

* **The graded commutator of derivations** `[D, D'] = D D' - (-1)^{e e'} D' D` is a derivation of
  parity `e + e'` (`GrDer.gcomm`).
* **Endomorphisms of parity `e` of a graded linear species** (`GrSpEnd`), with their composites,
  sums and graded commutators. Each extends to **a derivation of the free graded operad**
  (`FreeGrL.derSp`), and the graded commutator of the extensions is the extension of the graded
  commutator (`FreeGrL.derSp_gcomm`). A morphism of graded linear species extends to **a morphism
  of free graded operads** (`FreeGrL.mapSp`), functorially, and it intertwines the derivations
  extending intertwined endomorphisms (`FreeGrL.derSp_mapSp`).
* **Induction on the free graded operad** (`FreeGrL.submodule_eq_top`): a family of submodules
  containing the relabelled units and the generators, stable under relabelling and composition,
  is everything.
-/
import Operad.CobarWeight

universe u v w

namespace Operad

open Sym GerBV TreeOfArity FreeGr

/-! ## Graded commutators of derivations -/

namespace GrOperad

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {A : Type} [Fintype A] [DecidableEq A]

/-- **The sign twists compose by adding the parities.** -/
lemma tw_tw' (e e' : Bool) (x : P A) :
    tw (R := R) e (tw (R := R) e' x) = tw (R := R) (xor e e') x := by
  cases e <;> cases e' <;> simp

end GrOperad

namespace GrDer

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P] {e e' : Bool}

/-- **The graded commutator of two derivations** `D D' - (-1)^{e e'} D' D`, a derivation of the
sum of their parities. -/
def gcomm (D : GrDer (GrOperadHom.id R P) e) (D' : GrDer (GrOperadHom.id R P) e') :
    GrDer (GrOperadHom.id R P) (xor e e') where
  app A _ _ := D.app A ∘ₗ D'.app A - σ R (e && e') • (D'.app A ∘ₗ D.app A)
  app_par c x := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, D.app_par,
      D'.app_par, map_sub, map_smul]
    cases c <;> cases e <;> cases e' <;> rfl
  app_map σ' x := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, D.app_map,
      D'.app_map, map_sub, map_smul]
  app_one := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, D.app_one,
      D'.app_one, map_zero, smul_zero, sub_zero]
  app_comp i x y := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, D.app_comp,
      D'.app_comp, GrOperadHom.id_app, map_add, map_sub, map_smul, D.app_tw, D'.app_tw,
      GrOperad.tw_tw']
    cases e <;> cases e' <;> simp <;> abel

@[simp] lemma gcomm_app (D : GrDer (GrOperadHom.id R P) e) (D' : GrDer (GrOperadHom.id R P) e')
    {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    (D.gcomm D').app A x = D.app A (D'.app A x) - σ R (e && e') • D'.app A (D.app A x) := rfl

end GrDer

/-! ## Endomorphisms of graded linear species -/

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]

variable (R V) in
/-- **An endomorphism of parity `e` of a graded linear species**: linear maps commuting with the
relabellings and shifting the parities by `e`. -/
structure GrSpEnd (e : Bool) where
  /-- The component at a finite type. -/
  app (A : Type) [Fintype A] [DecidableEq A] : V A →ₗ[R] V A
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (σ' : A ≃ B)
    (x : V A) : app B (SymSpecies.map (R := R) σ' x) = SymSpecies.map (R := R) σ' (app A x)
  app_par {A : Type} [Fintype A] [DecidableEq A] (c : Bool) (x : V A) :
    app A (GrSpecies.par (R := R) c x) = GrSpecies.par (R := R) (xor c e) (app A x)

namespace GrSpEnd

variable {e e' : Bool}

@[ext] lemma ext {φ ψ : GrSpEnd R V e}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), φ.app A x = ψ.app A x) :
    φ = ψ := by
  obtain ⟨φa, _, _⟩ := φ
  obtain ⟨ψa, _, _⟩ := ψ
  have : @φa = @ψa := by
    funext A _ _
    exact LinearMap.ext (h A)
  subst this
  rfl

variable (R V) in
/-- The identity. -/
def id : GrSpEnd R V false where
  app _ _ _ := LinearMap.id
  app_map _ _ := rfl
  app_par c x := by rw [Bool.xor_false]; rfl

variable (R V e) in
/-- The zero endomorphism. -/
def zero : GrSpEnd R V e where
  app _ _ _ := 0
  app_map _ _ := by simp only [LinearMap.zero_apply, map_zero]
  app_par _ _ := by simp only [LinearMap.zero_apply, map_zero]

/-- The composite. -/
def comp (φ : GrSpEnd R V e) (ψ : GrSpEnd R V e') : GrSpEnd R V (xor e e') where
  app A _ _ := φ.app A ∘ₗ ψ.app A
  app_map σ' x := by simp only [LinearMap.comp_apply, ψ.app_map, φ.app_map]
  app_par c x := by
    simp only [LinearMap.comp_apply, ψ.app_par, φ.app_par, Bool.xor_assoc, Bool.xor_comm e']

/-- The difference. -/
def sub (φ ψ : GrSpEnd R V e) : GrSpEnd R V e where
  app A _ _ := φ.app A - ψ.app A
  app_map σ' x := by simp only [LinearMap.sub_apply, φ.app_map, ψ.app_map, map_sub]
  app_par c x := by simp only [LinearMap.sub_apply, φ.app_par, ψ.app_par, map_sub]

/-- The sum. -/
def add (φ ψ : GrSpEnd R V e) : GrSpEnd R V e where
  app A _ _ := φ.app A + ψ.app A
  app_map σ' x := by simp only [LinearMap.add_apply, φ.app_map, ψ.app_map, map_add]
  app_par c x := by simp only [LinearMap.add_apply, φ.app_par, ψ.app_par, map_add]

/-- The scalar multiple. -/
def smul (a : R) (φ : GrSpEnd R V e) : GrSpEnd R V e where
  app A _ _ := a • φ.app A
  app_map σ' x := by simp only [LinearMap.smul_apply, φ.app_map, map_smul]
  app_par c x := by simp only [LinearMap.smul_apply, φ.app_par, map_smul]

/-- **The graded commutator** `φ ψ - (-1)^{e e'} ψ φ`. -/
def gcomm (φ : GrSpEnd R V e) (ψ : GrSpEnd R V e') : GrSpEnd R V (xor e e') where
  app A _ _ := φ.app A ∘ₗ ψ.app A - σ R (e && e') • (ψ.app A ∘ₗ φ.app A)
  app_map σ' x := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, ψ.app_map,
      φ.app_map, map_sub, map_smul]
  app_par c x := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, ψ.app_par,
      φ.app_par, map_sub, map_smul]
    cases c <;> cases e <;> cases e' <;> rfl

@[simp] lemma id_app {A : Type} [Fintype A] [DecidableEq A] (x : V A) :
    (id R V).app A x = x := rfl
@[simp] lemma zero_app {A : Type} [Fintype A] [DecidableEq A] (x : V A) :
    (zero R V e).app A x = 0 := rfl
@[simp] lemma comp_app (φ : GrSpEnd R V e) (ψ : GrSpEnd R V e') {A : Type} [Fintype A]
    [DecidableEq A] (x : V A) : (φ.comp ψ).app A x = φ.app A (ψ.app A x) := rfl
@[simp] lemma sub_app (φ ψ : GrSpEnd R V e) {A : Type} [Fintype A] [DecidableEq A] (x : V A) :
    (φ.sub ψ).app A x = φ.app A x - ψ.app A x := rfl
@[simp] lemma add_app (φ ψ : GrSpEnd R V e) {A : Type} [Fintype A] [DecidableEq A] (x : V A) :
    (φ.add ψ).app A x = φ.app A x + ψ.app A x := rfl
@[simp] lemma smul_app (a : R) (φ : GrSpEnd R V e) {A : Type} [Fintype A] [DecidableEq A]
    (x : V A) : (φ.smul a).app A x = a • φ.app A x := rfl
@[simp] lemma gcomm_app (φ : GrSpEnd R V e) (ψ : GrSpEnd R V e') {A : Type} [Fintype A]
    [DecidableEq A] (x : V A) :
    (φ.gcomm ψ).app A x = φ.app A (ψ.app A x) - σ R (e && e') • ψ.app A (φ.app A x) := rfl

/-- An even endomorphism, as a morphism of graded linear species. -/
def toHom (φ : GrSpEnd R V false) : GrSpeciesHom R V V where
  app := φ.app
  app_map := φ.app_map
  app_par c x := by rw [φ.app_par, Bool.xor_false]

@[simp] lemma toHom_app (φ : GrSpEnd R V false) {A : Type} [Fintype A] [DecidableEq A]
    (x : V A) : φ.toHom.app A x = φ.app A x := rfl

end GrSpEnd

/-- The composite of morphisms of graded linear species. -/
def GrSpeciesHom.comp {U : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (U A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (U A)] [GrSpecies R U]
    (ψ : GrSpeciesHom R W U) (φ : GrSpeciesHom R V W) : GrSpeciesHom R V U where
  app A _ _ := ψ.app A ∘ₗ φ.app A
  app_map σ' x := by simp only [LinearMap.comp_apply, φ.app_map, ψ.app_map]
  app_par c x := by simp only [LinearMap.comp_apply, φ.app_par, ψ.app_par]

@[simp] lemma GrSpeciesHom.comp_app {U : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (U A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (U A)] [GrSpecies R U]
    (ψ : GrSpeciesHom R W U) (φ : GrSpeciesHom R V W) {A : Type} [Fintype A] [DecidableEq A]
    (x : V A) : (ψ.comp φ).app A x = ψ.app A (φ.app A x) := rfl

/-! ## Derivations and morphisms of free graded operads extending maps of generators -/

namespace FreeGrL

variable {e e' : Bool}

/-- The values `v ↦ ι (φ v)` on the generators. -/
noncomputable def genSp (φ : GrSpEnd R V e) : SymSpeciesHom R V (FreeGrL R V) where
  app A _ _ := (ι R V).app A ∘ₗ φ.app A
  app_map σ' x := by
    simp only [LinearMap.comp_apply, φ.app_map]
    exact (ι R V).app_map σ' _

lemma isShift_genSp (φ : GrSpEnd R V e) : IsShift (genSp φ) e := by
  intro A _ _ c v
  show (ι R V).app A (φ.app A (GrSpecies.par (R := R) c v)) = _
  rw [φ.app_par]
  exact (ι R V).app_par _ _

/-- **The derivation of the free graded operad extending an endomorphism of the generators.** -/
noncomputable def derSp (φ : GrSpEnd R V e) : GrDer (GrOperadHom.id R (FreeGrL R V)) e :=
  derOf (GrOperadHom.id R (FreeGrL R V)) (genSp φ) (isShift_genSp φ)

@[simp] lemma derSp_ι (φ : GrSpEnd R V e) {A : Type} [Fintype A] [DecidableEq A] (v : V A) :
    (derSp φ).app A ((ι R V).app A v) = (ι R V).app A (φ.app A v) :=
  derOf_ι _ _ _ v

/-- **The graded commutator of extended derivations extends the graded commutator.** -/
theorem derSp_gcomm (φ : GrSpEnd R V e) (ψ : GrSpEnd R V e') :
    (derSp φ).gcomm (derSp ψ) = derSp (φ.gcomm ψ) :=
  der_ext fun A _ _ v => by
    rw [GrDer.gcomm_app, derSp_ι, derSp_ι, derSp_ι, derSp_ι, derSp_ι, GrSpEnd.gcomm_app,
      map_sub, map_smul]

lemma derSp_gcomm_app (φ : GrSpEnd R V e) (ψ : GrSpEnd R V e') {A : Type} [Fintype A]
    [DecidableEq A] (x : FreeGrL R V A) :
    (derSp φ).app A ((derSp ψ).app A x) - σ R (e && e') • (derSp ψ).app A ((derSp φ).app A x)
      = (derSp (φ.gcomm ψ)).app A x := by
  rw [← derSp_gcomm]
  rfl

/-- The derivation extending zero vanishes. -/
lemma derSp_zero_app {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (derSp (GrSpEnd.zero R V e)).app A x = 0 := by
  have : derSp (GrSpEnd.zero R V e) = GrDer.zero _ e :=
    der_eq_zero fun A _ _ v => by rw [derSp_ι, GrSpEnd.zero_app, map_zero]
  rw [this]
  rfl

/-- Derivations extending equal endomorphisms are equal. -/
lemma derSp_congr {φ ψ : GrSpEnd R V e}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), φ.app A x = ψ.app A x)
    {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (derSp φ).app A x = (derSp ψ).app A x := by
  rw [GrSpEnd.ext h]

/-- **The morphism of free graded operads extending a morphism of the generators.** -/
noncomputable def mapSp (φ : GrSpeciesHom R V W) : GrOperadHom R (FreeGrL R V) (FreeGrL R W) :=
  homEquiv.symm ((ι R W).comp φ)

@[simp] lemma mapSp_ι (φ : GrSpeciesHom R V W) {A : Type} [Fintype A] [DecidableEq A] (v : V A) :
    (mapSp φ).app A ((ι R V).app A v) = (ι R W).app A (φ.app A v) :=
  homEquiv_symm_ι _ v

/-- **Functoriality.** -/
lemma mapSp_comp {U : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (U A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (U A)] [GrSpecies R U]
    (ψ : GrSpeciesHom R W U) (φ : GrSpeciesHom R V W) {A : Type} [Fintype A] [DecidableEq A]
    (x : FreeGrL R V A) : (mapSp ψ).app A ((mapSp φ).app A x) = (mapSp (ψ.comp φ)).app A x := by
  have : (mapSp ψ).comp (mapSp φ) = mapSp (ψ.comp φ) := hom_ext fun A _ _ v => by
    rw [GrOperadHom.comp_app, mapSp_ι, mapSp_ι, mapSp_ι, GrSpeciesHom.comp_app]
  exact congrArg (fun g : GrOperadHom R (FreeGrL R V) (FreeGrL R U) => g.app A x) this

/-- Morphisms extending equal morphisms of generators are equal. -/
lemma mapSp_congr {φ ψ : GrSpeciesHom R V W}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), φ.app A x = ψ.app A x)
    {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (mapSp φ).app A x = (mapSp ψ).app A x := by
  rw [GrSpeciesHom.ext h]

/-- The identity of the generators extends to the identity. -/
lemma mapSp_id {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (mapSp (GrSpEnd.id R V).toHom).app A x = x := by
  have : mapSp (GrSpEnd.id R V).toHom = GrOperadHom.id R (FreeGrL R V) := hom_ext fun A _ _ v => by
    rw [mapSp_ι]
    rfl
  rw [this]
  rfl

/-- **Intertwining**: if `b φ = φ a` on the generators, the extended morphism intertwines the
extended derivations. -/
theorem derSp_mapSp {a : GrSpEnd R V e} {b : GrSpEnd R W e} {φ : GrSpeciesHom R V W}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A),
      b.app A (φ.app A v) = φ.app A (a.app A v))
    {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (derSp b).app A ((mapSp φ).app A x) = (mapSp φ).app A ((derSp a).app A x) := by
  have : (derSp b).compHom (mapSp φ) = GrDer.homComp (mapSp φ) (derSp a) :=
    der_ext fun A _ _ v => by
      rw [GrDer.compHom_app, GrDer.homComp_app, mapSp_ι, derSp_ι, derSp_ι, mapSp_ι, h]
  exact congrArg (fun D : GrDer (mapSp φ) e => D.app A x) this

/-! ## Induction on the free graded operad -/

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R V)
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R V)) R

omit [GrSpecies R W] in
private lemma mem_of_single' {α : Type*} {M : Type*} [AddCommGroup M] [Module R M]
    {S : Submodule R M} (f : (α →₀ R) →ₗ[R] M) (h : ∀ a, f (Finsupp.single a 1) ∈ S)
    (x : α →₀ R) : f x ∈ S := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact S.zero_mem
  | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
  | single a b =>
    rw [← Finsupp.smul_single_one, map_smul]
    exact S.smul_mem b (h a)

/-- **Induction on the free graded operad**: a family of submodules containing the relabelled
units and the generators, stable under relabelling and composition, is everything. -/
theorem submodule_eq_top (S : ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (FreeGrL R V A))
    (hunit : ∀ (A : Type) [Fintype A] [DecidableEq A] (e : Unit ≃ A),
      GrOperad.map (R := R) e (GrOperad.one (R := R) (P := FreeGrL R V)) ∈ S A)
    (hgen : ∀ (n : ℕ) (v : V (Fin n)), (ι R V).app (Fin n) v ∈ S (Fin n))
    (hmap : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (x : FreeGrL R V A), x ∈ S A → GrOperad.map (R := R) e x ∈ S B)
    (hcomp : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (x : FreeGrL R V A) (y : FreeGrL R V B), x ∈ S A → y ∈ S B →
        GrOperad.comp (R := R) i x y ∈ S (Without A i ⊕ B))
    (A : Type) [Fintype A] [DecidableEq A] : S A = ⊤ := by
  have hbas : ∀ (X : Type) [Fintype X] [DecidableEq X] (x : Reg (TreeOfArity (GrGen R V)) X),
      (𝒥).proj X (𝔟 x) ∈ S X :=
    tree_induction (motive := fun X _ _ x => (𝒥).proj X (𝔟 x) ∈ S X)
      (fun X _ _ x hl => by
        beta_reduce
        obtain ⟨e, he⟩ := proj_bas_leaf hl
        rw [he]
        exact hunit X e)
      (fun X _ _ k g e => by
        beta_reduce
        rw [proj_bas_map, proj_bas_corolla]
        exact hmap _ _ e _ (hgen k _))
      (fun X A B _ _ _ _ _ _ r p q e _ _ hp hq => by
        beta_reduce at hp hq ⊢
        rw [proj_bas_map, proj_bas_comp]
        exact hmap _ _ e _ (Submodule.smul_mem _ _ (hcomp _ _ r _ _ hp hq)))
  refine eq_top_iff.2 fun Y _ => ?_
  have h := Function.surjInv_eq ((𝒥).proj_surjective A) Y
  rw [← h]
  exact mem_of_single' ((𝒥).proj A) (fun x => hbas A x) _


/-! ## Eigenspace decompositions -/

section Eigen

variable (a : GrSpEnd R V false)

variable (R V) in
omit [GrSpecies R V] in
/-- **Over a `ℚ`-algebra, an endomorphism whose eigenspaces for the natural numbers span has no
eigenvector for a negative integer.** -/
lemma _root_.Operad.eq_zero_of_eigen_neg [Algebra ℚ R] {M : Type*} [AddCommGroup M] [Module R M]
    (E : M →ₗ[R] M) (htop : ⨆ j : ℕ, Module.End.eigenspace E (j : R) = ⊤) {m : ℕ} (hm : m ≠ 0)
    {x : M} (hx : E x = -(m : R) • x) : x = 0 := by
  set E' : M →ₗ[R] M := E + (m : R) • LinearMap.id
  have h0 : x ∈ Module.End.eigenspace E' ((0 : ℕ) : R) := by
    rw [Module.End.mem_eigenspace_iff, Nat.cast_zero, zero_smul]
    show E x + (m : R) • x = 0
    rw [hx, neg_smul, neg_add_cancel]
  have h1 : x ∈ ⨆ (j : ℕ) (_ : j ≠ 0), Module.End.eigenspace E' (j : R) := by
    have hle : (⨆ j : ℕ, Module.End.eigenspace E (j : R))
        ≤ ⨆ (j : ℕ) (_ : j ≠ 0), Module.End.eigenspace E' (j : R) := iSup_le fun j => by
      intro y hy
      have hy' : y ∈ Module.End.eigenspace E' ((j + m : ℕ) : R) := by
        rw [Module.End.mem_eigenspace_iff] at hy ⊢
        show E y + (m : R) • y = _
        rw [hy, Nat.cast_add, add_smul]
      exact Submodule.mem_iSup_of_mem (j + m) (Submodule.mem_iSup_of_mem (by omega) hy')
    exact hle (htop ▸ Submodule.mem_top)
  exact Submodule.disjoint_def.1 (iSupIndep_eigenspace_nat E' 0) x h0 h1

variable (R V) in
/-- **The eigenspace for `j`** of the derivation extending an even endomorphism. -/
noncomputable abbrev eig (j : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    Submodule R (FreeGrL R V A) :=
  Module.End.eigenspace ((derSp a).app A) (j : R)

variable {a}

lemma mem_eig {j : ℕ} {A : Type} [Fintype A] [DecidableEq A] {x : FreeGrL R V A} :
    x ∈ eig R V a j A ↔ (derSp a).app A x = (j : R) • x :=
  Module.End.mem_eigenspace_iff

lemma unit_mem_eig {A : Type} [Fintype A] [DecidableEq A] (e : Unit ≃ A) :
    GrOperad.map (R := R) e (GrOperad.one (R := R) (P := FreeGrL R V)) ∈ eig R V a 0 A := by
  rw [mem_eig, Nat.cast_zero, zero_smul]
  exact ((derSp a).app_map e _).trans ((congrArg _ (derSp a).app_one).trans (map_zero _))

lemma map_mem_eig {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) {j : ℕ} {x : FreeGrL R V A} (hx : x ∈ eig R V a j A) :
    GrOperad.map (R := R) e x ∈ eig R V a j B :=
  mem_eig.2 (((derSp a).app_map e x).trans ((congrArg _ (mem_eig.1 hx)).trans (map_smul _ _ _)))

/-- **The eigenvalues add under composition.** -/
lemma comp_mem_eig {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (r : A)
    {i j : ℕ} {x : FreeGrL R V A} {y : FreeGrL R V B} (hx : x ∈ eig R V a i A)
    (hy : y ∈ eig R V a j B) : GrOperad.comp (R := R) r x y ∈ eig R V a (i + j) _ := by
  refine mem_eig.2 (((derSp a).app_comp r x y).trans ?_)
  rw [GrOperadHom.id_app, GrOperadHom.id_app, GrOperad.tw_false, mem_eig.1 hx, mem_eig.1 hy,
    LinearMap.map_smul₂, map_smul, ← add_smul, Nat.cast_add]

/-- Composites of elements of sums of submodules, by bilinearity. -/
lemma comp_mem_of_iSup {ι κ : Type*} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (r : A) {p : ι → Submodule R (FreeGrL R V A)}
    {q : κ → Submodule R (FreeGrL R V B)} {T : Submodule R (FreeGrL R V (Without A r ⊕ B))}
    (h : ∀ i k, ∀ x ∈ p i, ∀ y ∈ q k, GrOperad.comp (R := R) r x y ∈ T) {x : FreeGrL R V A}
    {y : FreeGrL R V B} (hx : x ∈ ⨆ i, p i) (hy : y ∈ ⨆ k, q k) :
    GrOperad.comp (R := R) r x y ∈ T := by
  refine Submodule.iSup_induction p (motive := fun x => GrOperad.comp (R := R) r x y ∈ T) hx
    (fun i x hx => ?_) (by beta_reduce; rw [LinearMap.map_zero₂]; exact T.zero_mem)
    (fun x x' hx hx' => by beta_reduce at hx hx' ⊢; rw [LinearMap.map_add₂]; exact T.add_mem hx hx')
  exact Submodule.iSup_induction q (motive := fun y => GrOperad.comp (R := R) r x y ∈ T) hy
    (fun k y hy => h i k x hx y hy) (by beta_reduce; rw [map_zero]; exact T.zero_mem)
    (fun y y' hy hy' => by beta_reduce at hy hy' ⊢; rw [map_add]; exact T.add_mem hy hy')

lemma map_mem_iSup {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (f : ℕ → ℕ) {x : FreeGrL R V A} (hx : x ∈ ⨆ j, eig R V a (f j) A) :
    GrOperad.map (R := R) e x ∈ ⨆ j, eig R V a (f j) B :=
  Submodule.iSup_induction _ (motive := fun x => GrOperad.map (R := R) e x ∈ _) hx
    (fun j x hx => Submodule.mem_iSup_of_mem j (map_mem_eig e hx))
    (by beta_reduce; rw [map_zero]; exact zero_mem _)
    (fun x x' hx hx' => by beta_reduce at hx hx' ⊢; rw [map_add]; exact add_mem hx hx')

/-- A generator decomposing into eigenvectors of the endomorphism decomposes into eigenvectors of
the derivation. -/
lemma ι_mem_iSup_eig {A : Type} [Fintype A] [DecidableEq A] {v : V A}
    (hv : v ∈ ⨆ j : ℕ, Module.End.eigenspace (a.app A) (j : R)) :
    (ι R V).app A v ∈ ⨆ j : ℕ, eig R V a j A :=
  Submodule.iSup_induction _ (motive := fun v => (ι R V).app A v ∈ _) hv
    (fun j v hv => Submodule.mem_iSup_of_mem j (mem_eig.2 (by
      rw [derSp_ι, Module.End.mem_eigenspace_iff.1 hv, map_smul])))
    (by beta_reduce; rw [map_zero]; exact zero_mem _)
    (fun x x' hx hx' => by beta_reduce at hx hx' ⊢; rw [map_add]; exact add_mem hx hx')

/-- **The free graded operad is the sum of the eigenspaces** of the derivation extending an
endomorphism whose eigenspaces for the natural numbers span the generators. -/
theorem iSup_eig_eq_top
    (hgen : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A),
      v ∈ ⨆ j : ℕ, Module.End.eigenspace (a.app A) (j : R))
    (A : Type) [Fintype A] [DecidableEq A] : ⨆ j : ℕ, eig R V a j A = ⊤ :=
  submodule_eq_top (fun A _ _ => ⨆ j : ℕ, eig R V a j A)
    (fun _ _ _ e => Submodule.mem_iSup_of_mem 0 (unit_mem_eig e))
    (fun _ v => ι_mem_iSup_eig (hgen _ v))
    (fun _ _ _ _ _ _ e _ hx => map_mem_iSup e id hx)
    (fun _ _ _ _ _ _ r _ _ hx hy => comp_mem_of_iSup r
      (fun i k _ hx _ hy => Submodule.mem_iSup_of_mem (i + k) (comp_mem_eig r hx hy)) hx hy) A

/-- **The free graded operad is the direct sum of the eigenspaces**, over a `ℚ`-algebra. -/
theorem isInternal_eig [Algebra ℚ R]
    (hgen : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A),
      v ∈ ⨆ j : ℕ, Module.End.eigenspace (a.app A) (j : R))
    (A : Type) [Fintype A] [DecidableEq A] : DirectSum.IsInternal fun j : ℕ => eig R V a j A :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_eigenspace_nat ((derSp a).app A)) (iSup_eig_eq_top hgen A)

end Eigen


/-! ## Idempotent endomorphisms of the generators -/

section Idem

variable (π : GrSpEnd R V false)
  (hπ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : V A), π.app A (π.app A x) = π.app A x)

variable (R V) in
/-- The complementary idempotent `1 - π`. -/
def GrSpEnd.compl : GrSpEnd R V false := (GrSpEnd.id R V).sub π

@[simp] lemma GrSpEnd.compl_app {A : Type} [Fintype A] [DecidableEq A] (x : V A) :
    (GrSpEnd.compl R V π).app A x = x - π.app A x := rfl

include hπ

/-- The generators decompose into the eigenvectors `π v` and `v - π v` of `1 - π`. -/
lemma mem_iSup_compl {A : Type} [Fintype A] [DecidableEq A] (v : V A) :
    v ∈ ⨆ j : ℕ, Module.End.eigenspace ((GrSpEnd.compl R V π).app A) (j : R) := by
  have h0 : π.app A v ∈ Module.End.eigenspace ((GrSpEnd.compl R V π).app A) ((0 : ℕ) : R) := by
    rw [Module.End.mem_eigenspace_iff, GrSpEnd.compl_app, hπ, sub_self, Nat.cast_zero, zero_smul]
  have h1 : v - π.app A v
      ∈ Module.End.eigenspace ((GrSpEnd.compl R V π).app A) ((1 : ℕ) : R) := by
    rw [Module.End.mem_eigenspace_iff, GrSpEnd.compl_app, map_sub, hπ, sub_self, sub_zero,
      Nat.cast_one, one_smul]
  have : v = π.app A v + (v - π.app A v) := by abel
  rw [this]
  exact add_mem (Submodule.mem_iSup_of_mem 0 h0) (Submodule.mem_iSup_of_mem 1 h1)

/-- **The projection kills the counting derivation**: `N ∘ T(π) = 0`. -/
lemma derSp_compl_mapSp {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (derSp (GrSpEnd.compl R V π)).app A ((mapSp π.toHom).app A x) = 0 := by
  rw [derSp_mapSp (a := GrSpEnd.zero R V false) (fun A _ _ v => by
    rw [GrSpEnd.compl_app, GrSpEnd.toHom_app, hπ, sub_self, GrSpEnd.zero_app, map_zero]),
    derSp_zero_app, map_zero]

/-- **The counting derivation is killed by the projection**: `T(π) ∘ N = 0`. -/
lemma mapSp_derSp_compl {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    (mapSp π.toHom).app A ((derSp (GrSpEnd.compl R V π)).app A x) = 0 := by
  rw [← derSp_mapSp (b := GrSpEnd.zero R V false) (fun A _ _ v => by
    simp only [GrSpEnd.compl_app, GrSpEnd.toHom_app, map_sub, hπ, sub_self, GrSpEnd.zero_app]),
    derSp_zero_app]

/-- **An element differs from its projection by an element of positive eigenvalues.** -/
lemma sub_mapSp_mem {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    x - (mapSp π.toHom).app A x ∈ ⨆ j : ℕ, eig R V (GrSpEnd.compl R V π) (j + 1) A := by
  set T := mapSp (R := R) (V := V) π.toHom
  have htop := iSup_eig_eq_top (a := GrSpEnd.compl R V π) (fun A _ _ v => mem_iSup_compl π hπ v)
  have hT0 : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : FreeGrL R V A),
      T.app A x ∈ eig R V (GrSpEnd.compl R V π) 0 A := fun A _ _ x =>
    mem_eig.2 (by rw [derSp_compl_mapSp π hπ, Nat.cast_zero, zero_smul])
  have h := submodule_eq_top (R := R) (V := V)
    (fun A _ _ => (⨆ j : ℕ, eig R V (GrSpEnd.compl R V π) (j + 1) A).comap
      (LinearMap.id - T.app A))
    (fun A _ _ e => by
      rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, T.app_map, T.app_one,
        sub_self]
      exact zero_mem _)
    (fun n v => by
      rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, mapSp_ι,
        GrSpEnd.toHom_app, ← map_sub]
      refine Submodule.mem_iSup_of_mem 0 (mem_eig.2 ?_)
      rw [derSp_ι]
      simp only [GrSpEnd.compl_app, map_sub, hπ, sub_self, sub_zero, zero_add, Nat.cast_one,
        one_smul])
    (fun A B _ _ _ _ e x hx => by
      rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, T.app_map, ← map_sub]
      exact map_mem_iSup e (· + 1) hx)
    (fun A B _ _ _ _ r x y hx hy => by
      rw [Submodule.mem_comap] at hx hy ⊢
      rw [LinearMap.sub_apply, LinearMap.id_apply, T.app_comp]
      have e : GrOperad.comp (R := R) r x y - GrOperad.comp (R := R) r (T.app A x) (T.app B y)
          = GrOperad.comp (R := R) r (x - T.app A x) y
            + GrOperad.comp (R := R) r (T.app A x) (y - T.app B y) := by
        rw [LinearMap.map_sub₂, map_sub]
        abel
      rw [e]
      refine add_mem (comp_mem_of_iSup r (fun i k x hx y hy => ?_) hx
        (htop B ▸ Submodule.mem_top : y ∈ ⨆ j : ℕ, eig R V (GrSpEnd.compl R V π) j B))
        (comp_mem_of_iSup (p := fun _ : Unit => eig R V (GrSpEnd.compl R V π) 0 A) r
          (fun _ k x hx y hy => ?_) (Submodule.mem_iSup_of_mem () (hT0 A x)) hy)
      · exact Submodule.mem_iSup_of_mem (i + k) (by
          rw [show i + k + 1 = i + 1 + k by omega]; exact comp_mem_eig r hx hy)
      · exact Submodule.mem_iSup_of_mem k (by
          rw [show k + 1 = 0 + (k + 1) by omega]; exact comp_mem_eig r hx hy)) A
  have hx : x ∈ (⊤ : Submodule R (FreeGrL R V A)) := Submodule.mem_top
  rw [← h] at hx
  exact hx

/-- **The projection fixes the eigenspace for zero**, over a `ℚ`-algebra. -/
theorem mapSp_eq_self [Algebra ℚ R] {A : Type} [Fintype A] [DecidableEq A] {x : FreeGrL R V A}
    (hx : x ∈ eig R V (GrSpEnd.compl R V π) 0 A) : (mapSp π.toHom).app A x = x := by
  have h0 : x - (mapSp π.toHom).app A x ∈ eig R V (GrSpEnd.compl R V π) 0 A :=
    sub_mem hx (mem_eig.2 (by rw [derSp_compl_mapSp π hπ, Nat.cast_zero, zero_smul]))
  have h1 : x - (mapSp π.toHom).app A x
      ∈ ⨆ (j : ℕ) (_ : j ≠ 0), eig R V (GrSpEnd.compl R V π) j A :=
    (iSup_le fun j => le_iSup₂_of_le (f := fun (k : ℕ) (_ : k ≠ 0) =>
      eig R V (GrSpEnd.compl R V π) k A) (j + 1) (by omega) le_rfl) (sub_mapSp_mem π hπ x)
  have := Submodule.disjoint_def.1 (iSupIndep_eigenspace_nat _ 0) _ h0 h1
  exact (sub_eq_zero.1 this).symm

/-- **The projection kills the eigenspaces for the positive integers**, over a `ℚ`-algebra. -/
theorem mapSp_eq_zero [Algebra ℚ R] {A : Type} [Fintype A] [DecidableEq A] {j : ℕ} (hj : j ≠ 0)
    {x : FreeGrL R V A} (hx : x ∈ eig R V (GrSpEnd.compl R V π) j A) :
    (mapSp π.toHom).app A x = 0 := by
  have h := mapSp_derSp_compl π hπ x
  rw [mem_eig.1 hx, map_smul] at h
  exact (isUnit_natCast_of_ne_zero hj).smul_left_cancel.1 (h.trans (smul_zero _).symm)

end Idem

end FreeGrL

end Operad
