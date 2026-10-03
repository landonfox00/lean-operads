/-
# The decomposition cooperad of a set operad

A set operad `S` in which every operation has finitely many factorizations `x = p ∘ᵢ q` at each
input (`SetOperad.FiniteFact`) carries a cooperad structure on its linearization `Lin R S`, the
**decomposition cooperad**: an operation decomposes as the sum of its factorizations,

  `Δᵢ x = ∑_{p ∘ᵢ q = x} p ⊗ q`,

and the counit takes the coefficient of the identity (`Lin.instSymCooperad`). Under
`R[X] ⊗ R[Y] ≅ R[X × Y]` the decomposition is the pullback of finitely supported functions along
the composition (`finComap`), so that the coefficient of `p ⊗ q` in `Δᵢ x` is the coefficient of
`p ∘ᵢ q` in `x` (`Lin.decompL_apply`), and every axiom of a cooperad is the corresponding axiom of
`S`, read on coefficients.

**Cooperad morphisms into a decomposition cooperad are transposed operad morphisms**
(`Lin.coHomEquiv`): a family of linear maps `Φ : C → R[S]` is a morphism of cooperads exactly
when its transpose `p ↦ (c ↦ Φ c p)` is a morphism of set operads from `S` to the dual operad of
`C` (`SymCooperad.instSymOperadDual`), and the transposes so obtained are the *locally finite*
ones, those with which each cooperation pairs nontrivially only finitely often.
-/
import Operad.SymCooperad
import Operad.SetOperad
import Mathlib.LinearAlgebra.DirectSum.Finsupp

universe u v w

namespace Operad

open scoped TensorProduct

open Sym

/-! ## Pulling back finitely supported functions -/

section FinComap

variable {R : Type u} [CommRing R]

/-- **The pullback of a finitely supported function along a map with finite fibers.** -/
noncomputable def finComap {X Y : Type*} (c : X → Y) (hc : ∀ y, (c ⁻¹' {y}).Finite) :
    (Y →₀ R) →ₗ[R] (X →₀ R) where
  toFun x := Finsupp.ofSupportFinite (x ∘ c) (by
    refine (x.support.finite_toSet.biUnion fun y _ => hc y).subset fun a ha => ?_
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]
    exact ⟨c a, Finsupp.mem_support_iff.2 ha, rfl⟩)
  map_add' x y := by
    ext a
    simp [Finsupp.ofSupportFinite_coe]
  map_smul' r x := by
    ext a
    simp [Finsupp.ofSupportFinite_coe]

@[simp] lemma finComap_apply {X Y : Type*} (c : X → Y) (hc : ∀ y, (c ⁻¹' {y}).Finite)
    (x : Y →₀ R) (a : X) : finComap c hc x a = x (c a) :=
  rfl

/-- An injective map has finite fibers. -/
lemma finite_preimage_of_injective {X Y : Type*} {c : X → Y} (hc : Function.Injective c) (y : Y) :
    (c ⁻¹' {y}).Finite :=
  Set.Subsingleton.finite fun _ ha _ hb => hc (ha.trans hb.symm)

variable (R) in
/-- `R[X] ⊗ R[Y] ≅ R[X × Y]`. -/
noncomputable abbrev tens (X Y : Type*) : (X →₀ R) ⊗[R] (Y →₀ R) ≃ₗ[R] (X × Y →₀ R) :=
  finsuppTensorFinsupp' R X Y

lemma tens_tmul_apply {X Y : Type*} (x : X →₀ R) (y : Y →₀ R) (a : X) (b : Y) :
    tens R X Y (x ⊗ₜ y) (a, b) = x a * y b :=
  finsuppTensorFinsupp'_apply_apply R X Y x y a b

/-- A coefficient of a tensor of finitely supported functions, as a pairing. -/
lemma tens_apply_eq_pair {X Y : Type*} (t : (X →₀ R) ⊗[R] (Y →₀ R)) (a : X) (b : Y) :
    tens R X Y t (a, b) = SymCooperad.pair (Finsupp.lapply a) (Finsupp.lapply b) t := by
  have : (Finsupp.lapply (a, b)) ∘ₗ (tens R X Y).toLinearMap
      = SymCooperad.pair (Finsupp.lapply a) (Finsupp.lapply b) :=
    TensorProduct.ext' fun x y => by simp
  exact LinearMap.congr_fun this t

variable (R) in
/-- `R[X] ⊗ (R[Y] ⊗ R[Z]) ≅ R[X × (Y × Z)]`. -/
noncomputable def tens3 (X Y Z : Type*) :
    (X →₀ R) ⊗[R] ((Y →₀ R) ⊗[R] (Z →₀ R)) ≃ₗ[R] (X × (Y × Z) →₀ R) :=
  (TensorProduct.congr (LinearEquiv.refl R _) (tens R Y Z)).trans (tens R X (Y × Z))

variable (R) in
/-- `(R[X] ⊗ R[Y]) ⊗ R[Z] ≅ R[(X × Y) × Z]`. -/
noncomputable def tens3' (X Y Z : Type*) :
    ((X →₀ R) ⊗[R] (Y →₀ R)) ⊗[R] (Z →₀ R) ≃ₗ[R] ((X × Y) × Z →₀ R) :=
  (TensorProduct.congr (tens R X Y) (LinearEquiv.refl R _)).trans (tens R (X × Y) Z)

@[simp] lemma tens3_tmul_apply {X Y Z : Type*} (x : X →₀ R) (y : Y →₀ R) (z : Z →₀ R) (a : X)
    (b : Y) (d : Z) : tens3 R X Y Z (x ⊗ₜ (y ⊗ₜ z)) (a, (b, d)) = x a * (y b * z d) := by
  simp [tens3]

@[simp] lemma tens3'_tmul_apply {X Y Z : Type*} (x : X →₀ R) (y : Y →₀ R) (z : Z →₀ R) (a : X)
    (b : Y) (d : Z) : tens3' R X Y Z ((x ⊗ₜ y) ⊗ₜ z) ((a, b), d) = x a * y b * z d := by
  simp [tens3']

/-- Decomposing the second factor, on coefficients. -/
lemma tens3_lTensor {X Y Y₁ Y₂ : Type*} (g : (Y →₀ R) →ₗ[R] (Y₁ →₀ R) ⊗[R] (Y₂ →₀ R))
    (c : Y₁ × Y₂ → Y) (hg : ∀ y p, tens R Y₁ Y₂ (g y) p = y (c p))
    (t : (X →₀ R) ⊗[R] (Y →₀ R)) (a : X) (p : Y₁ × Y₂) :
    tens3 R X Y₁ Y₂ (LinearMap.lTensor (X →₀ R) g t) (a, p) = tens R X Y t (a, c p) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    obtain ⟨b, d⟩ := p
    simp only [LinearMap.lTensor_tmul, tens_tmul_apply, ← hg y (b, d)]
    simp [tens3]
  | add t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht']

/-- Decomposing the first factor, on coefficients. -/
lemma tens3'_rTensor {X X₁ X₂ Z : Type*} (g : (X →₀ R) →ₗ[R] (X₁ →₀ R) ⊗[R] (X₂ →₀ R))
    (c : X₁ × X₂ → X) (hg : ∀ x p, tens R X₁ X₂ (g x) p = x (c p))
    (t : (X →₀ R) ⊗[R] (Z →₀ R)) (p : X₁ × X₂) (d : Z) :
    tens3' R X₁ X₂ Z (LinearMap.rTensor (Z →₀ R) g t) (p, d) = tens R X Z t (c p, d) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x z =>
    obtain ⟨a, b⟩ := p
    simp only [LinearMap.rTensor_tmul, tens_tmul_apply, ← hg x (a, b)]
    simp [tens3']
  | add t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht']

/-- The associator, on coefficients. -/
lemma tens3_assoc {X Y Z : Type*} (t : ((X →₀ R) ⊗[R] (Y →₀ R)) ⊗[R] (Z →₀ R)) (a : X) (b : Y)
    (d : Z) :
    tens3 R X Y Z (TensorProduct.assoc R _ _ _ t) (a, (b, d)) = tens3' R X Y Z t ((a, b), d) := by
  have : (Finsupp.lapply (a, (b, d))) ∘ₗ (tens3 R X Y Z).toLinearMap ∘ₗ
        (TensorProduct.assoc R (X →₀ R) (Y →₀ R) (Z →₀ R)).toLinearMap
      = (Finsupp.lapply ((a, b), d)) ∘ₗ (tens3' R X Y Z).toLinearMap :=
    TensorProduct.ext_threefold fun x y z => by simp [mul_assoc]
  exact LinearMap.congr_fun this t

/-- The exchange of the last two factors, on coefficients. -/
lemma tens3'_swapLast {X Y Z : Type w} (t : ((X →₀ R) ⊗[R] (Y →₀ R)) ⊗[R] (Z →₀ R)) (a : X)
    (b : Y) (d : Z) :
    tens3' R X Z Y (swapLast R _ _ _ t) ((a, d), b) = tens3' R X Y Z t ((a, b), d) := by
  have : (Finsupp.lapply ((a, d), b)) ∘ₗ (tens3' R X Z Y).toLinearMap ∘ₗ
        (swapLast R (X →₀ R) (Y →₀ R) (Z →₀ R)).toLinearMap
      = (Finsupp.lapply ((a, b), d)) ∘ₗ (tens3' R X Y Z).toLinearMap :=
    TensorProduct.ext_threefold fun x y z => by simp [swapLast, mul_right_comm]
  exact LinearMap.congr_fun this t

/-- Two maps of tensor products, on coefficients. -/
lemma tens_map {X X' Y Y' : Type*} (f : (X →₀ R) →ₗ[R] (X' →₀ R)) (g : (Y →₀ R) →ₗ[R] (Y' →₀ R))
    (cf : X' → X) (cg : Y' → Y) (hf : ∀ x a, f x a = x (cf a)) (hg : ∀ y b, g y b = y (cg b))
    (t : (X →₀ R) ⊗[R] (Y →₀ R)) (a : X') (b : Y') :
    tens R X' Y' (TensorProduct.map f g t) (a, b) = tens R X Y t (cf a, cg b) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [hf, hg]
  | add t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht']

/-- The counit `x ↦ x u` on the right, on coefficients. -/
lemma rid_lTensor_lapply {X U : Type*} (u : U) (t : (X →₀ R) ⊗[R] (U →₀ R)) (a : X) :
    TensorProduct.rid R (X →₀ R) (LinearMap.lTensor (X →₀ R) (Finsupp.lapply u) t) a
      = tens R X U t (a, u) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [mul_comm]
  | add t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht']

/-- The counit `x ↦ x u` on the left, on coefficients. -/
lemma lid_rTensor_lapply {Y U : Type*} (u : U) (t : (U →₀ R) ⊗[R] (Y →₀ R)) (b : Y) :
    TensorProduct.lid R (Y →₀ R) (LinearMap.rTensor (Y →₀ R) (Finsupp.lapply u) t) b
      = tens R U Y t (u, b) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht']

end FinComap

/-! ## Finite factorizations -/

/-- **A set operad with finite factorizations**: at every input, every operation is a composite
in finitely many ways. -/
class SetOperad.FiniteFact (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [SetOperad S] : Prop where
  /-- The factorizations of an operation at an input are finite in number. -/
  finite {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : S (Without A i ⊕ B)) :
    ((fun pq : S A × S B => SetOperad.comp i pq.1 pq.2) ⁻¹' {x}).Finite

namespace Lin

variable (R : Type u) [CommRing R]
  {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
variable {A A' B B' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D]

variable {R} in
/-- Relabelling, on coefficients. -/
lemma mapL_apply (e : A ≃ B) (x : S A →₀ R) (y : S B) :
    mapL R e x y = x (SetOperad.map e.symm y) := by
  conv_lhs => rw [← SetOperad.map_map_symm e y]
  exact Finsupp.mapDomain_apply (SetOperad.map_injective e) x _

variable [SetOperad.FiniteFact S]

/-- **The decomposition**: `Δᵢ x = ∑_{p ∘ᵢ q = x} p ⊗ q`. -/
noncomputable def decompL (i : A) :
    (S (Without A i ⊕ B) →₀ R) →ₗ[R] (S A →₀ R) ⊗[R] (S B →₀ R) :=
  (tens R (S A) (S B)).symm.toLinearMap ∘ₗ
    finComap (fun pq : S A × S B => SetOperad.comp i pq.1 pq.2) (SetOperad.FiniteFact.finite i)

variable {R}

/-- **The coefficients of a decomposition**: the coefficient of `p ⊗ q` in `Δᵢ x` is the
coefficient of `p ∘ᵢ q` in `x`. -/
lemma decompL_apply (i : A) (x : S (Without A i ⊕ B) →₀ R) (pq : S A × S B) :
    tens R (S A) (S B) (decompL R i x) pq = x (SetOperad.comp i pq.1 pq.2) := by
  simp [decompL]

lemma decompL_map (σ : A ≃ A') (τ : B ≃ B') (i : A) :
    decompL R (σ i) ∘ₗ mapL R (compEquiv σ τ i)
      = TensorProduct.map (mapL R σ) (mapL R τ) ∘ₗ decompL (S := S) R i :=
  LinearMap.ext fun x => (tens R (S A') (S B')).injective (Finsupp.ext fun ⟨p, q⟩ => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, decompL_apply, mapL_apply,
      tens_map _ _ _ _ (mapL_apply σ) (mapL_apply τ), decompL_apply]
    congr 1
    rw [← SetOperad.map_symm_map (compEquiv σ τ i) (SetOperad.comp i _ _),
      SetOperad.map_comp, SetOperad.map_map_symm, SetOperad.map_map_symm])

lemma decompL_counit_right (i : A) :
    (TensorProduct.rid R (S A →₀ R)).toLinearMap ∘ₗ
        LinearMap.lTensor (S A →₀ R) (Finsupp.lapply SetOperad.one) ∘ₗ decompL (B := Unit) R i ∘ₗ
          mapL R (rightUnitEquiv i).symm
      = LinearMap.id :=
  LinearMap.ext fun x => Finsupp.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, rid_lTensor_lapply, decompL_apply,
      mapL_apply, Equiv.symm_symm, SetOperad.comp_one, LinearMap.id_apply]

lemma decompL_counit_left :
    (TensorProduct.lid R (S B →₀ R)).toLinearMap ∘ₗ
        LinearMap.rTensor (S B →₀ R) (Finsupp.lapply SetOperad.one) ∘ₗ decompL R () ∘ₗ
          mapL R (leftUnitEquiv B).symm
      = LinearMap.id :=
  LinearMap.ext fun x => Finsupp.ext fun b => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, lid_rTensor_lapply, decompL_apply,
      mapL_apply, Equiv.symm_symm, SetOperad.one_comp, LinearMap.id_apply]

lemma decompL_assoc_seq (i : A) (j : B) :
    LinearMap.lTensor (S A →₀ R) (decompL (B := D) R j) ∘ₗ decompL R i
      = (TensorProduct.assoc R (S A →₀ R) (S B →₀ R) (S D →₀ R)).toLinearMap ∘ₗ
          LinearMap.rTensor (S D →₀ R) (decompL R i) ∘ₗ decompL R (Sum.inr j) ∘ₗ
            mapL R (seqEquiv i j D).symm :=
  LinearMap.ext fun x => (tens3 R (S A) (S B) (S D)).injective (Finsupp.ext fun ⟨a, b, d⟩ => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [tens3_lTensor _ _ (decompL_apply j), decompL_apply, tens3_assoc,
      tens3'_rTensor _ _ (decompL_apply i), decompL_apply, mapL_apply, Equiv.symm_symm]
    exact congrArg x (SetOperad.comp_assoc_seq i j a b d).symm)

lemma decompL_assoc_par {i k : A} (hik : i ≠ k) :
    LinearMap.rTensor (S B →₀ R) (decompL (B := D) R k) ∘ₗ decompL R (Sum.inl ⟨i, hik⟩)
      = (swapLast R (S A →₀ R) (S B →₀ R) (S D →₀ R)).toLinearMap ∘ₗ
          LinearMap.rTensor (S D →₀ R) (decompL R i) ∘ₗ decompL R (Sum.inl ⟨k, Ne.symm hik⟩) ∘ₗ
            mapL R (parEquiv hik B D).symm :=
  LinearMap.ext fun x => (tens3' R (S A) (S D) (S B)).injective (Finsupp.ext fun ⟨⟨a, d⟩, b⟩ => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [tens3'_rTensor _ _ (decompL_apply k), decompL_apply, tens3'_swapLast,
      tens3'_rTensor _ _ (decompL_apply i), decompL_apply, mapL_apply, Equiv.symm_symm]
    exact congrArg x (SetOperad.comp_assoc_par hik a b d).symm)

end Lin

open Lin in
/-- **The decomposition cooperad of a set operad with finite factorizations.** -/
noncomputable instance Lin.instSymCooperad (R : Type u) [CommRing R]
    (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) [SetOperad S]
    [SetOperad.FiniteFact S] : SymCooperad R (Lin R S) where
  map e := mapL R e
  map_refl x := SymOperad.map_refl (R := R) (P := Lin R S) x
  map_trans e f x := SymOperad.map_trans (R := R) (P := Lin R S) e f x
  counit := Finsupp.lapply SetOperad.one
  decomp i := decompL R i
  decomp_map σ τ i := decompL_map σ τ i
  counit_right i := decompL_counit_right i
  counit_left := decompL_counit_left
  decomp_assoc_seq i j := decompL_assoc_seq i j
  decomp_assoc_par hik := decompL_assoc_par hik

namespace SymCooperadHom

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [SymCooperad R C]
  {D : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (D A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (D A)] [SymCooperad R D]

/-- Morphisms of cooperads are determined by their components. -/
@[ext] lemma ext {φ ψ : SymCooperadHom R C D}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : C A), φ.app A c = ψ.app A c) :
    φ = ψ := by
  obtain ⟨φa, _, _, _⟩ := φ
  obtain ⟨ψa, _, _, _⟩ := ψ
  have : @φa = @ψa := by
    funext A _ _
    exact LinearMap.ext (h A)
  subst this
  rfl

end SymCooperadHom

/-! ## Morphisms into a decomposition cooperad -/

namespace Lin

variable {R : Type u} [CommRing R]
  {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  [SetOperad.FiniteFact S]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [SymCooperad R C]

/-- The functional on cooperations given by an operation, under a morphism into the dual operad. -/
abbrev dualVal (Ψ : SetOperadHom S (Und R (SymCooperad.Dual R C))) {A : Type} [Fintype A]
    [DecidableEq A] (p : S A) : Module.Dual R (C A) :=
  (Und.of R (SymCooperad.Dual R C)).symm (Ψ.app A p)

omit [SetOperad.FiniteFact S] in
lemma dualVal_map (Ψ : SetOperadHom S (Und R (SymCooperad.Dual R C))) {A B : Type} [Fintype A]
    [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B) (p : S A) (c : C B) :
    dualVal Ψ (SetOperad.map e p) c = dualVal Ψ p (SymCooperad.map (R := R) e.symm c) := by
  rw [dualVal, Ψ.app_map]
  rfl

omit [SetOperad.FiniteFact S] in
lemma dualVal_one (Ψ : SetOperadHom S (Und R (SymCooperad.Dual R C))) (c : C Unit) :
    dualVal Ψ SetOperad.one c = SymCooperad.counit (R := R) c := by
  rw [dualVal, Ψ.app_one]
  rfl

omit [SetOperad.FiniteFact S] in
lemma dualVal_comp (Ψ : SetOperadHom S (Und R (SymCooperad.Dual R C))) {A B : Type} [Fintype A]
    [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) (p : S A) (q : S B)
    (c : C (Without A i ⊕ B)) :
    dualVal Ψ (SetOperad.comp i p q) c
      = SymCooperad.pair (dualVal Ψ p) (dualVal Ψ q) (SymCooperad.decomp (R := R) i c) := by
  rw [dualVal, Ψ.app_comp]
  rfl

/-- A morphism of set operads into the dual operad is **locally finite** when each cooperation
pairs nontrivially with finitely many operations. -/
def LocallyFinite (Ψ : SetOperadHom S (Und R (SymCooperad.Dual R C))) : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (c : C A),
    (Function.support fun p : S A => dualVal Ψ p c).Finite

/-- **The transpose** of a morphism into a decomposition cooperad: an operation `p` gives the
functional `c ↦ Φ c p`. -/
noncomputable def transpose (Φ : SymCooperadHom R C (Lin R S)) :
    SetOperadHom S (Und R (SymCooperad.Dual R C)) where
  app A _ _ p := Und.of R _ (Finsupp.lapply p ∘ₗ Φ.app A)
  app_map {A B} _ _ _ _ e p := by
    rw [Und.map_eq]
    congr 1
    refine LinearMap.ext fun c => ?_
    rw [SymCooperad.dual_map_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      Finsupp.lapply_apply, Finsupp.lapply_apply]
    conv_lhs => rw [← SymCooperad.map_map_symm (R := R) e c]
    rw [← LinearMap.comp_apply (Φ.app B), Φ.app_map]
    exact (mapL_apply e _ _).trans (by rw [SetOperad.map_symm_map])
  app_one := by
    rw [Und.one_eq, SymCooperad.dual_one]
    exact congrArg _ Φ.counit_app
  app_comp {A B} _ _ _ _ i p q := by
    rw [Und.comp_eq]
    congr 1
    refine LinearMap.ext fun c => ?_
    have h := LinearMap.congr_fun (Φ.decomp_app i) c
    simp only [LinearMap.comp_apply] at h
    rw [SymCooperad.dual_comp_apply, ← SymCooperad.pair_map, LinearMap.comp_apply,
      LinearMap.comp_apply, ← h, ← tens_apply_eq_pair]
    exact (decompL_apply i _ (p, q)).symm

@[simp] lemma dualVal_transpose (Φ : SymCooperadHom R C (Lin R S)) {A : Type} [Fintype A]
    [DecidableEq A] (p : S A) (c : C A) : dualVal (transpose Φ) p c = Φ.app A c p :=
  rfl

lemma transpose_locallyFinite (Φ : SymCooperadHom R C (Lin R S)) :
    LocallyFinite (transpose Φ) :=
  fun A _ _ c => by
    rw [show (fun p => dualVal (transpose Φ) p c) = ⇑(Φ.app A c) from rfl, Finsupp.fun_support_eq]
    exact (Φ.app A c).support.finite_toSet

/-- The morphism of cooperads with a given locally finite transpose. -/
noncomputable def ofTranspose (Ψ : SetOperadHom S (Und R (SymCooperad.Dual R C)))
    (hΨ : LocallyFinite Ψ) : SymCooperadHom R C (Lin R S) where
  app A _ _ :=
    { toFun := fun c => Finsupp.ofSupportFinite (fun p => dualVal Ψ p c) (hΨ A c)
      map_add' := fun c c' => Finsupp.ext fun p => by
        simp [Finsupp.ofSupportFinite_coe]
      map_smul' := fun r c => Finsupp.ext fun p => by
        simp [Finsupp.ofSupportFinite_coe] }
  app_map {A B} _ _ _ _ e := LinearMap.ext fun c => Finsupp.ext fun p => by
    show dualVal Ψ p (SymCooperad.map (R := R) e c)
      = mapL R e (Finsupp.ofSupportFinite (fun p => dualVal Ψ p c) (hΨ A c)) p
    rw [mapL_apply, Finsupp.ofSupportFinite_coe]
    conv_lhs => rw [← SetOperad.map_map_symm e p]
    rw [dualVal, Ψ.app_map]
    show dualVal Ψ (SetOperad.map e.symm p)
      (SymCooperad.map (R := R) e.symm (SymCooperad.map (R := R) e c)) = _
    rw [SymCooperad.map_symm_map]
  counit_app := LinearMap.ext fun c => by
    show dualVal Ψ SetOperad.one c = SymCooperad.counit c
    rw [dualVal, Ψ.app_one, Und.one_eq, Equiv.symm_apply_apply, SymCooperad.dual_one]
  decomp_app {A B} _ _ _ _ i := LinearMap.ext fun c => (tens R (S A) (S B)).injective
    (Finsupp.ext fun ⟨p, q⟩ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      show tens R (S A) (S B) (decompL R i _) (p, q) = _
      rw [decompL_apply, tens_apply_eq_pair, ← LinearMap.comp_apply (SymCooperad.pair _ _),
        SymCooperad.pair_map]
      show dualVal Ψ (SetOperad.comp i p q) c = _
      rw [dualVal, Ψ.app_comp]
      rfl)

@[simp] lemma ofTranspose_apply (Ψ : SetOperadHom S (Und R (SymCooperad.Dual R C)))
    (hΨ : LocallyFinite Ψ) {A : Type} [Fintype A] [DecidableEq A] (c : C A) (p : S A) :
    (ofTranspose Ψ hΨ).app A c p = dualVal Ψ p c :=
  rfl

/-- **Cooperad morphisms into a decomposition cooperad are transposed operad morphisms**: a
morphism `Φ : C → R[S]` is the same as a locally finite morphism of set operads from `S` to the
dual operad of `C`, by `p ↦ (c ↦ Φ c p)`. -/
noncomputable def coHomEquiv :
    SymCooperadHom R C (Lin R S) ≃
      {Ψ : SetOperadHom S (Und R (SymCooperad.Dual R C)) // LocallyFinite Ψ} where
  toFun Φ := ⟨transpose Φ, transpose_locallyFinite Φ⟩
  invFun Ψ := ofTranspose Ψ.1 Ψ.2
  left_inv _ := SymCooperadHom.ext fun _ _ _ _ => Finsupp.ext fun _ => rfl
  right_inv _ := Subtype.ext (SetOperadHom.ext fun _ _ _ _ => rfl)

@[simp] lemma coHomEquiv_apply_apply (Φ : SymCooperadHom R C (Lin R S)) {A : Type} [Fintype A]
    [DecidableEq A] (p : S A) (c : C A) : dualVal (coHomEquiv Φ).1 p c = Φ.app A c p :=
  rfl

end Lin

end Operad
