/-
# Symmetric cooperads

The dual of `Operad.SymOperad`, in the same species convention. Where an operad has partial
composition `comp i : P A → P B → P (Without A i ⊕ B)`, a cooperad has **infinitesimal
decomposition**

`decomp i : C (Without A i ⊕ B) →ₗ C A ⊗ C B`,

splitting a cooperation with inputs `Without A i ⊕ B` into an outer cooperation with inputs `A`
and an inner one with inputs `B`, plugged at `i`. Every axiom is the corresponding operad axiom
with the arrows reversed; as for `Operad.NSCooperad`, they are equalities of linear maps, since a
tensor product has no description by elements.

* `SymCooperad`, `SymCooperadHom`: symmetric cooperads in `R`-modules and their morphisms.
* `SymCooperad.Dual`: **the linear dual of a cooperad is an operad**, with composition
  `(f ∘ᵢ g)(c) = (f ⊗ g)(Δᵢ c)` and unit the counit (`SymCooperad.instSymOperadDual`); a morphism
  of cooperads dualizes to a morphism of operads (`SymCooperadHom.dual`).
* `ComC`: **the commutative cooperad**, `R` in every arity with decomposition `1 ↦ 1 ⊗ 1`; its
  dual is the commutative operad (`ComC.dualHom`, `ComC.dualHom_bijective`).
-/
import Operad.Sym
import Operad.Cooperad
import Mathlib.LinearAlgebra.Dual.Defs

universe u v w

namespace Operad

open scoped TensorProduct

open Sym

/-- **A symmetric cooperad in `R`-modules**: relabellings, a counit and infinitesimal
decompositions, with the axioms of an operad reversed. -/
class SymCooperad (R : Type u) [CommRing R]
    (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] where
  /-- Relabelling the inputs along a bijection. -/
  map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    (A ≃ B) → C A →ₗ[R] C B
  /-- Relabelling along the identity changes nothing. -/
  map_refl {A : Type} [Fintype A] [DecidableEq A] (x : C A) : map (Equiv.refl A) x = x
  /-- Relabelling is functorial. -/
  map_trans {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (e : A ≃ B) (f : B ≃ D) (x : C A) :
    map (e.trans f) x = map f (map e x)
  /-- The counit, dual to the unit of an operad. -/
  counit : C Unit →ₗ[R] R
  /-- **Infinitesimal decomposition**: split off an inner cooperation with inputs `B`, plugged
  at the input `i` of an outer one with inputs `A`. -/
  decomp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) :
    C (Without A i ⊕ B) →ₗ[R] C A ⊗[R] C B
  /-- **Equivariance**: decomposition is natural in bijections of both input sets. -/
  decomp_map {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (σ : A ≃ A') (τ : B ≃ B') (i : A) :
    decomp (σ i) ∘ₗ map (compEquiv σ τ i) = TensorProduct.map (map σ) (map τ) ∘ₗ decomp i
  /-- The right counit law, dual to `SymOperad.comp_one`. -/
  counit_right {A : Type} [Fintype A] [DecidableEq A] (i : A) :
    (TensorProduct.rid R (C A)).toLinearMap ∘ₗ LinearMap.lTensor (C A) counit ∘ₗ decomp i ∘ₗ
      map (rightUnitEquiv i).symm = LinearMap.id
  /-- The left counit law, dual to `SymOperad.one_comp`. -/
  counit_left {B : Type} [Fintype B] [DecidableEq B] :
    (TensorProduct.lid R (C B)).toLinearMap ∘ₗ LinearMap.rTensor (C B) counit ∘ₗ
      decomp () ∘ₗ map (leftUnitEquiv B).symm = LinearMap.id
  /-- Sequential coassociativity, dual to `SymOperad.comp_assoc_seq`. -/
  decomp_assoc_seq {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) :
    LinearMap.lTensor (C A) (decomp (B := D) j) ∘ₗ decomp i
      = (TensorProduct.assoc R (C A) (C B) (C D)).toLinearMap ∘ₗ
          LinearMap.rTensor (C D) (decomp i) ∘ₗ decomp (Sum.inr j) ∘ₗ map (seqEquiv i j D).symm
  /-- Parallel coassociativity, dual to `SymOperad.comp_assoc_par`. -/
  decomp_assoc_par {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) :
    LinearMap.rTensor (C B) (decomp (B := D) k) ∘ₗ decomp (Sum.inl ⟨i, hik⟩)
      = (swapLast R (C A) (C B) (C D)).toLinearMap ∘ₗ
          LinearMap.rTensor (C D) (decomp i) ∘ₗ decomp (Sum.inl ⟨k, Ne.symm hik⟩) ∘ₗ
            map (parEquiv hik B D).symm

/-- **A morphism of symmetric cooperads**: a family of linear maps commuting with relabelling,
the counits and the decompositions. -/
structure SymCooperadHom (R : Type u) [CommRing R]
    (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (D : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (D A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (D A)]
    [SymCooperad R C] [SymCooperad R D] where
  /-- The component at a finite input set. -/
  app (A : Type) [Fintype A] [DecidableEq A] : C A →ₗ[R] D A
  /-- Components commute with relabelling. -/
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B) :
    app B ∘ₗ SymCooperad.map (R := R) e = SymCooperad.map (R := R) e ∘ₗ app A
  /-- The counit is preserved. -/
  counit_app : SymCooperad.counit (R := R) (C := D) ∘ₗ app Unit = SymCooperad.counit
  /-- Decompositions are preserved. -/
  decomp_app {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) :
    SymCooperad.decomp (R := R) (C := D) (B := B) i ∘ₗ app (Without A i ⊕ B)
      = TensorProduct.map (app A) (app B) ∘ₗ SymCooperad.decomp i

namespace SymCooperad

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [SymCooperad R C]

/-! ## The dual operad -/

variable (R C) in
/-- **The linear dual of a cooperad**, which is an operad. -/
@[nolint unusedArguments]
abbrev Dual (A : Type) [Fintype A] [DecidableEq A] : Type (max u v) := Module.Dual R (C A)

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Pairing a tensor product with a pair of functionals. -/
noncomputable def pair {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] : Module.Dual R X →ₗ[R] Module.Dual R Y →ₗ[R] Module.Dual R (X ⊗[R] Y) :=
  LinearMap.mk₂ R (fun f g => (TensorProduct.lid R R).toLinearMap ∘ₗ TensorProduct.map f g)
    (fun f f' g => TensorProduct.ext' fun x y => by simp [add_mul])
    (fun c f g => TensorProduct.ext' fun x y => by simp [mul_assoc])
    (fun f g g' => TensorProduct.ext' fun x y => by simp [mul_add])
    (fun c f g => TensorProduct.ext' fun x y => by simp [mul_left_comm])

@[simp] lemma pair_tmul {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (f : Module.Dual R X) (g : Module.Dual R Y) (x : X) (y : Y) :
    pair f g (x ⊗ₜ[R] y) = f x * g y := by
  simp [pair]

/-- Composition in the dual: `(f ∘ᵢ g)(c) = (f ⊗ g)(Δᵢ c)`. -/
noncomputable def dualComp (i : A) :
    Dual R C A →ₗ[R] Dual R C B →ₗ[R] Dual R C (Without A i ⊕ B) :=
  pair.compr₂ (LinearMap.lcomp R R (decomp (R := R) (C := C) (B := B) i))

@[simp] lemma dualComp_apply (i : A) (f : Dual R C A) (g : Dual R C B)
    (c : C (Without A i ⊕ B)) : dualComp i f g c = pair f g (decomp (R := R) i c) :=
  rfl

/-- Relabelling in the dual: precompose with the inverse relabelling. -/
noncomputable def dualMap {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) : Dual R C A →ₗ[R] Dual R C B :=
  LinearMap.lcomp R R (map (R := R) (C := C) e.symm)

@[simp] lemma dualMap_apply {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (f : Dual R C A) (c : C B) : dualMap e f c = f (map (R := R) e.symm c) :=
  rfl

lemma pair_map {X Y X' Y' : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup X'] [Module R X'] [AddCommGroup Y'] [Module R Y'] (f : Module.Dual R X')
    (g : Module.Dual R Y') (φ : X →ₗ[R] X') (ψ : Y →ₗ[R] Y') :
    pair f g ∘ₗ TensorProduct.map φ ψ = pair (f ∘ₗ φ) (g ∘ₗ ψ) :=
  TensorProduct.ext' fun x y => by simp

lemma map_symm_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (x : C A) : map (R := R) e.symm (map (R := R) e x) = x := by
  rw [← map_trans, Equiv.self_trans_symm, map_refl]

lemma map_map_symm {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (x : C B) : map (R := R) e (map (R := R) e.symm x) = x := by
  rw [← map_trans, Equiv.symm_trans_self, map_refl]

lemma pair_counit_right {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : Module.Dual R X) (ε : Module.Dual R Y) :
    pair f ε = f ∘ₗ (TensorProduct.rid R X).toLinearMap ∘ₗ LinearMap.lTensor X ε :=
  TensorProduct.ext' fun x y => by simp [mul_comm]

lemma pair_counit_left {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (ε : Module.Dual R X) (g : Module.Dual R Y) :
    pair ε g = g ∘ₗ (TensorProduct.lid R Y).toLinearMap ∘ₗ LinearMap.rTensor Y ε :=
  TensorProduct.ext' fun x y => by simp

lemma pair_assoc {X Y Z : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] (f : Module.Dual R X) (g : Module.Dual R Y)
    (h : Module.Dual R Z) :
    pair f (pair g h) ∘ₗ (TensorProduct.assoc R X Y Z).toLinearMap = pair (pair f g) h :=
  TensorProduct.ext_threefold fun x y z => by simp [mul_assoc]

lemma pair_swapLast {X Y Z : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] (f : Module.Dual R X) (g : Module.Dual R Y)
    (h : Module.Dual R Z) :
    pair (pair f h) g ∘ₗ (swapLast R X Y Z).toLinearMap = pair (pair f g) h :=
  TensorProduct.ext_threefold fun x y z => by simp [swapLast, mul_right_comm]

lemma pair_comp_decomp (i : A) (f : Dual R C A) (g : Dual R C B) :
    dualComp i f g = pair f g ∘ₗ decomp (R := R) i :=
  rfl

lemma pair_comp_left {X X' Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup X']
    [Module R X'] [AddCommGroup Y] [Module R Y] (F : Module.Dual R X') (φ : X →ₗ[R] X')
    (G : Module.Dual R Y) : pair (F ∘ₗ φ) G = pair F G ∘ₗ LinearMap.rTensor Y φ := by
  rw [LinearMap.rTensor, pair_map, LinearMap.comp_id]

lemma pair_comp_right {X Y Y' : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] [AddCommGroup Y'] [Module R Y'] (F : Module.Dual R X) (G : Module.Dual R Y')
    (ψ : Y →ₗ[R] Y') : pair F (G ∘ₗ ψ) = pair F G ∘ₗ LinearMap.lTensor X ψ := by
  rw [LinearMap.lTensor, pair_map, LinearMap.comp_id]

/-- **The linear dual of a cooperad is an operad.** -/
noncomputable instance instSymOperadDual : SymOperad R (Dual R C) where
  map e := dualMap e
  map_refl f := LinearMap.ext fun c => by
    rw [dualMap_apply, Equiv.refl_symm, map_refl]
  map_trans e e' f := LinearMap.ext fun c => by
    show f (map (R := R) (e'.symm.trans e.symm) c)
      = f (map (R := R) e.symm (map (R := R) e'.symm c))
    rw [map_trans]
  one := counit
  comp i := dualComp i
  map_comp σ τ i f g := LinearMap.ext fun c => by
    obtain ⟨c', rfl⟩ : ∃ c', c = map (R := R) (compEquiv σ τ i) c' :=
      ⟨map (R := R) (compEquiv σ τ i).symm c, (map_map_symm _ _).symm⟩
    have h1 := LinearMap.congr_fun (decomp_map (R := R) (C := C) σ τ i) c'
    have h2 := LinearMap.congr_fun
      (pair_map (dualMap σ f) (dualMap τ g) (map (R := R) σ) (map (R := R) τ))
      (decomp (R := R) i c')
    have hf : dualMap σ f ∘ₗ map (R := R) σ = f := LinearMap.ext fun x => by
      simp [map_symm_map]
    have hg : dualMap τ g ∘ₗ map (R := R) τ = g := LinearMap.ext fun x => by
      simp [map_symm_map]
    simp only [LinearMap.comp_apply] at h1 h2
    rw [hf, hg] at h2
    show dualComp i f g (map (R := R) (compEquiv σ τ i).symm
        (map (R := R) (compEquiv σ τ i) c'))
      = dualComp (σ i) (dualMap σ f) (dualMap τ g) (map (R := R) (compEquiv σ τ i) c')
    rw [map_symm_map, dualComp_apply, dualComp_apply, h1, h2]
  comp_one i f := LinearMap.ext fun c => by
    rw [dualMap_apply, dualComp_apply, pair_counit_right]
    exact congrArg f (LinearMap.congr_fun (counit_right (R := R) (C := C) i) c)
  one_comp g := LinearMap.ext fun c => by
    rw [dualMap_apply, dualComp_apply, pair_counit_left]
    exact congrArg g (LinearMap.congr_fun (counit_left (R := R) (C := C)) c)
  comp_assoc_seq i j f g h := LinearMap.ext fun c => by
    have hseq := LinearMap.congr_fun (decomp_assoc_seq (R := R) (C := C) i j) c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hseq
    show pair (pair f g ∘ₗ decomp (R := R) i) h
        (decomp (R := R) (Sum.inr j) (map (R := R) (seqEquiv i j _).symm c))
      = pair f (pair g h ∘ₗ decomp (R := R) j) (decomp (R := R) i c)
    rw [pair_comp_left, pair_comp_right, LinearMap.comp_apply, LinearMap.comp_apply, hseq,
      ← pair_assoc]
    rfl
  comp_assoc_par hik f g h := LinearMap.ext fun c => by
    have hpar := LinearMap.congr_fun (decomp_assoc_par (R := R) (C := C) (B := _) (D := _) hik) c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hpar
    show pair (pair f g ∘ₗ decomp (R := R) _) h
        (decomp (R := R) (Sum.inl ⟨_, Ne.symm hik⟩) (map (R := R) (parEquiv hik _ _).symm c))
      = pair (pair f h ∘ₗ decomp (R := R) _) g (decomp (R := R) (Sum.inl ⟨_, hik⟩) c)
    rw [pair_comp_left, pair_comp_left, LinearMap.comp_apply, LinearMap.comp_apply, hpar,
      ← pair_swapLast]
    rfl

@[simp] lemma dual_map_apply {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (e : A ≃ B) (f : Dual R C A) (c : C B) :
    SymOperad.map (R := R) (P := Dual R C) e f c = f (map (R := R) e.symm c) :=
  rfl

@[simp] lemma dual_comp_apply (i : A) (f : Dual R C A) (g : Dual R C B)
    (c : C (Without A i ⊕ B)) :
    SymOperad.comp (R := R) (P := Dual R C) i f g c = pair f g (decomp (R := R) i c) :=
  rfl

lemma dual_one : SymOperad.one R (P := Dual R C) = counit :=
  rfl

end SymCooperad

namespace SymCooperadHom

open SymCooperad

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [SymCooperad R C]
  {D : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (D A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (D A)] [SymCooperad R D]

/-- **A morphism of cooperads dualizes to a morphism of operads**, in the other direction. -/
noncomputable def dual (φ : SymCooperadHom R C D) : SymOperadHom R (Dual R D) (Dual R C) where
  app A _ _ := LinearMap.lcomp R R (φ.app A)
  app_map e f := LinearMap.ext fun c => by
    show f (map (R := R) e.symm (φ.app _ c)) = f (φ.app _ (map (R := R) e.symm c))
    rw [← LinearMap.comp_apply (φ.app _), φ.app_map]
    rfl
  app_one := φ.counit_app
  app_comp i f g := LinearMap.ext fun c => by
    show pair f g (decomp (R := R) i (φ.app _ c)) = pair (f ∘ₗ φ.app _) (g ∘ₗ φ.app _)
      (decomp (R := R) i c)
    rw [← LinearMap.comp_apply (decomp (R := R) i), φ.decomp_app, ← pair_map]
    rfl

end SymCooperadHom

/-! ## The commutative cooperad -/

/-- `ComC R A = R`, the commutative cooperad. -/
@[nolint unusedArguments]
abbrev ComC (R : Type u) [CommRing R] : (A : Type) → [Fintype A] → [DecidableEq A] → Type u :=
  fun _ _ _ => R

/-- **The commutative cooperad**: `R` in every arity, every decomposition `1 ↦ 1 ⊗ 1`. -/
noncomputable instance instSymCooperadComC (R : Type u) [CommRing R] : SymCooperad R (ComC R)
    where
  map _ := LinearMap.id
  map_refl _ := rfl
  map_trans _ _ _ := rfl
  counit := LinearMap.id
  decomp _ := (TensorProduct.lid R R).symm.toLinearMap
  decomp_map _ _ _ := LinearMap.ext_ring (by simp)
  counit_right _ := LinearMap.ext_ring (by simp)
  counit_left := LinearMap.ext_ring (by simp)
  decomp_assoc_seq _ _ := LinearMap.ext_ring (by simp)
  decomp_assoc_par _ := LinearMap.ext_ring (by simp [swapLast])

namespace ComC

variable (R : Type u) [CommRing R]

@[simp] lemma map_eq {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) : SymCooperad.map (R := R) (C := ComC R) e = LinearMap.id :=
  rfl

@[simp] lemma counit_eq : SymCooperad.counit (R := R) (C := ComC R) = LinearMap.id :=
  rfl

@[simp] lemma decomp_eq {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) : SymCooperad.decomp (R := R) (C := ComC R) (B := B) i
      = (TensorProduct.lid R R).symm.toLinearMap :=
  rfl

/-- **The dual of the commutative cooperad is the commutative operad**: the morphism. -/
noncomputable def dualHom : SymOperadHom R (Com R) (SymCooperad.Dual R (ComC R)) where
  app _ _ _ := LinearMap.ringLmapEquivSelf R R R |>.symm.toLinearMap
  app_map _ _ := LinearMap.ext_ring (by simp)
  app_one := LinearMap.ext_ring (by simp [SymCooperad.dual_one])
  app_comp _ _ _ := LinearMap.ext_ring (by simp [SymCooperad.dual_comp_apply])

/-- Its components are bijective. -/
theorem dualHom_bijective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Bijective ((dualHom R).app A) :=
  (LinearMap.ringLmapEquivSelf R R R).symm.bijective

end ComC

end Operad
