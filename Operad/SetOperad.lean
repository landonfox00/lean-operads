/-
# Set operads, and linearization

A *set operad* is a symmetric operad in sets: the same data and axioms as `Operad.SymOperad`, with
functions in place of linear maps. Many operads met in practice are linearizations of set operads —
`Com`, `Ass`, `Perm`, and the operads whose elements are subsets, bracketings or trees — and their
relations are identifications of monomials. For those, presentations and normal forms are statements
about sets, provable by induction on trees, and the linear statements follow by linearizing.

This file has the class, morphisms, the linearization `Lin R S A = S A →₀ R` as a symmetric operad
in `R`-modules, the underlying set operad of a linear one, and the adjunction between the two:
a morphism of linear operads out of `Lin R S` is exactly a morphism of set operads out of `S`
(`linHomEquiv`).
-/
import Operad.Sym
import Mathlib.LinearAlgebra.Finsupp.LSum

universe u v w

namespace Operad

open Sym

/-- **A symmetric set operad**, by partial composition over finite types. The axioms are those of
`SymOperad`, for functions. -/
class SetOperad (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) where
  /-- Relabelling the inputs along a bijection. -/
  map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] : (A ≃ B) → S A → S B
  map_refl {A : Type} [Fintype A] [DecidableEq A] (x : S A) : map (Equiv.refl A) x = x
  map_trans {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (e : A ≃ B) (f : B ≃ C) (x : S A) :
    map (e.trans f) x = map f (map e x)
  /-- The identity operation. -/
  one : S Unit
  /-- Partial composition at the input `i`. -/
  comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) :
    S A → S B → S (Without A i ⊕ B)
  map_comp {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (σ : A ≃ A') (τ : B ≃ B') (i : A)
    (x : S A) (y : S B) :
    map (compEquiv σ τ i) (comp i x y) = comp (σ i) (map σ x) (map τ y)
  comp_one {A : Type} [Fintype A] [DecidableEq A] (i : A) (x : S A) :
    map (rightUnitEquiv i) (comp i x one) = x
  one_comp {B : Type} [Fintype B] [DecidableEq B] (y : S B) :
    map (leftUnitEquiv B) (comp () one y) = y
  comp_assoc_seq {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) (x : S A) (y : S B) (z : S D) :
    map (seqEquiv i j D) (comp (Sum.inr j) (comp i x y) z) = comp i x (comp j y z)
  comp_assoc_par {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (x : S A) (y : S B) (z : S D) :
    map (parEquiv hik B D) (comp (Sum.inl ⟨k, Ne.symm hik⟩) (comp i x y) z)
      = comp (Sum.inl ⟨i, hik⟩) (comp k x z) y

/-- **A morphism of set operads.** -/
structure SetOperadHom (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w) [SetOperad S] [SetOperad T] where
  /-- The component at a finite input set. -/
  app (A : Type) [Fintype A] [DecidableEq A] : S A → T A
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : S A) : app B (SetOperad.map e x) = SetOperad.map e (app A x)
  app_one : app Unit SetOperad.one = SetOperad.one
  app_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : S A) (y : S B) :
    app (Without A i ⊕ B) (SetOperad.comp i x y) = SetOperad.comp i (app A x) (app B y)

namespace SetOperadHom

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S] [SetOperad T]

@[ext] lemma ext {φ ψ : SetOperadHom S T}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : S A), φ.app A x = ψ.app A x) :
    φ = ψ := by
  obtain ⟨φa, _, _, _⟩ := φ
  obtain ⟨ψa, _, _, _⟩ := ψ
  have : @φa = @ψa := by
    funext A _ _ x
    exact h A x
  subst this
  rfl

/-- The identity morphism. -/
def id : SetOperadHom S S where
  app _ _ _ := fun x => x
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

variable {U : (A : Type) → [Fintype A] → [DecidableEq A] → Type*} [SetOperad U]

/-- The composite of two morphisms. -/
def comp (ψ : SetOperadHom T U) (φ : SetOperadHom S T) : SetOperadHom S U where
  app A _ _ := fun x => ψ.app A (φ.app A x)
  app_map e x := by simp only [φ.app_map, ψ.app_map]
  app_one := by simp only [φ.app_one, ψ.app_one]
  app_comp i x y := by simp only [φ.app_comp, ψ.app_comp]

end SetOperadHom

/-- **An isomorphism of set operads**: morphisms both ways, inverse to each other. -/
structure SetOperadIso (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w) [SetOperad S] [SetOperad T] where
  /-- The forward morphism. -/
  hom : SetOperadHom S T
  /-- The inverse morphism. -/
  inv : SetOperadHom T S
  hom_inv_id : inv.comp hom = SetOperadHom.id
  inv_hom_id : hom.comp inv = SetOperadHom.id

namespace SetOperadIso

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  {T : (A : Type) → [Fintype A] → [DecidableEq A] → Type w} [SetOperad S] [SetOperad T]

/-- The components of an isomorphism are bijections. -/
def equiv (φ : SetOperadIso S T) (A : Type) [Fintype A] [DecidableEq A] : S A ≃ T A where
  toFun := φ.hom.app A
  invFun := φ.inv.app A
  left_inv x := congrArg (fun ψ : SetOperadHom S S => ψ.app A x) φ.hom_inv_id
  right_inv y := congrArg (fun ψ : SetOperadHom T T => ψ.app A y) φ.inv_hom_id

end SetOperadIso

namespace SetOperad

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
@[simp] lemma map_symm_map (e : A ≃ B) (x : S A) : map e.symm (map e x) = x := by
  rw [← map_trans, Equiv.self_trans_symm, map_refl]

omit [Fintype C] [DecidableEq C] in
@[simp] lemma map_map_symm (e : A ≃ B) (y : S B) : map e (map e.symm y) = y := by
  rw [← map_trans, Equiv.symm_trans_self, map_refl]

omit [Fintype C] [DecidableEq C] in
lemma map_injective (e : A ≃ B) : Function.Injective (map (S := S) e) :=
  fun x y h => by simpa using congrArg (map e.symm) h

end SetOperad

/-! ## Linearization -/

/-- **The linearization of a set operad**: the free `R`-module on each component. -/
abbrev Lin (R : Type u) [CommRing R] (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type (max u v) :=
  fun A _ _ => S A →₀ R

namespace Lin

variable (R : Type u) [CommRing R]
  {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
variable {A A' B B' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D]

/-- Relabelling, extended linearly. -/
noncomputable def mapL (e : A ≃ B) : (S A →₀ R) →ₗ[R] (S B →₀ R) :=
  Finsupp.lmapDomain R R (SetOperad.map e)

/-- Composition, extended bilinearly. -/
noncomputable def compL (i : A) : (S A →₀ R) →ₗ[R] (S B →₀ R) →ₗ[R] (S (Without A i ⊕ B) →₀ R) :=
  Finsupp.lift ((S B →₀ R) →ₗ[R] (S (Without A i ⊕ B) →₀ R)) R (S A)
    (fun s => Finsupp.lmapDomain R R (SetOperad.comp i s))

variable {R}

@[simp] lemma mapL_single (e : A ≃ B) (s : S A) (r : R) :
    mapL R e (Finsupp.single s r) = Finsupp.single (SetOperad.map e s) r := by
  simp [mapL]

@[simp] lemma compL_single (i : A) (s : S A) (t : S B) (r r' : R) :
    compL R i (Finsupp.single s r) (Finsupp.single t r')
      = Finsupp.single (SetOperad.comp i s t) (r * r') := by
  simp [compL, Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul]

omit [SetOperad S] in
/-- Two linear maps out of a free module agree when they agree on the basis. -/
lemma induction₁ {M : Type*} [AddCommGroup M] [Module R M] (f g : (S A →₀ R) →ₗ[R] M)
    (h : ∀ s, f (Finsupp.single s 1) = g (Finsupp.single s 1)) (x : S A →₀ R) : f x = g x := by
  have : f = g := Finsupp.lhom_ext' fun s => LinearMap.ext_ring (h s)
  rw [this]

end Lin

/-- **The linearization of a set operad is a symmetric operad in `R`-modules.** -/
noncomputable instance instSymOperadLin (R : Type u) [CommRing R]
    (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) [SetOperad S] :
    SymOperad R (Lin R S) where
  map e := Lin.mapL R e
  map_refl x := by
    show Finsupp.mapDomain (SetOperad.map (Equiv.refl _)) x = x
    rw [Finsupp.mapDomain_congr (g := id) (fun s _ => SetOperad.map_refl s),
      Finsupp.mapDomain_id]
  map_trans e f x := by
    show Finsupp.mapDomain _ x = Finsupp.mapDomain _ (Finsupp.mapDomain _ x)
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext s
    exact SetOperad.map_trans e f s
  one := Finsupp.single SetOperad.one 1
  comp i := Lin.compL R i
  map_comp σ τ i x y := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | single t r' =>
        simp only [Lin.compL_single, Lin.mapL_single, SetOperad.map_comp]
  comp_one i x := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r => simp only [Lin.compL_single, Lin.mapL_single, SetOperad.comp_one, mul_one]
  one_comp y := by
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single t r => simp only [Lin.compL_single, Lin.mapL_single, SetOperad.one_comp, one_mul]
  comp_assoc_seq i j x y z := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | single t r' =>
        induction z using Finsupp.induction_linear with
        | zero => simp
        | add z z' hz hz' => simp only [map_add, hz, hz']
        | single w r'' =>
          simp only [Lin.compL_single, Lin.mapL_single, SetOperad.comp_assoc_seq, mul_assoc]
  comp_assoc_par hik x y z := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | single t r' =>
        induction z using Finsupp.induction_linear with
        | zero => simp
        | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
        | single w r'' =>
          simp only [Lin.compL_single, Lin.mapL_single, SetOperad.comp_assoc_par]
          congr 1
          ring

/-! ## The underlying set operad of a linear operad, and the adjunction -/

/-- **The underlying set operad** of a symmetric operad in `R`-modules: the same components and
operations, forgetting linearity. A type synonym, so that the ring is recorded. -/
def Und (R : Type u) [CommRing R] (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w) :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type w :=
  fun A _ _ => Q A

section Und

variable (R : Type u) [CommRing R] (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- An element of `Q A`, seen in the underlying set operad. -/
def Und.of {A : Type} [Fintype A] [DecidableEq A] : Q A ≃ Und R Q A := Equiv.refl _

instance instSetOperadUnd : SetOperad (Und R Q) where
  map e x := (Und.of R Q) (SymOperad.map (R := R) e ((Und.of R Q).symm x))
  map_refl x := SymOperad.map_refl (R := R) (P := Q) x
  map_trans e f x := SymOperad.map_trans (R := R) (P := Q) e f x
  one := Und.of R Q (SymOperad.one R)
  comp i x y := (Und.of R Q)
    (SymOperad.comp (R := R) i ((Und.of R Q).symm x) ((Und.of R Q).symm y))
  map_comp σ τ i x y := SymOperad.map_comp (R := R) (P := Q) σ τ i x y
  comp_one i x := SymOperad.comp_one (R := R) (P := Q) i x
  one_comp y := SymOperad.one_comp (R := R) (P := Q) y
  comp_assoc_seq i j x y z := SymOperad.comp_assoc_seq (R := R) (P := Q) i j x y z
  comp_assoc_par hik x y z := SymOperad.comp_assoc_par (R := R) (P := Q) hik x y z

variable {R Q} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma Und.map_eq (e : A ≃ B) (x : Q A) :
    SetOperad.map e (Und.of R Q x) = Und.of R Q (SymOperad.map (R := R) e x) := rfl

lemma Und.one_eq : (SetOperad.one : Und R Q Unit) = Und.of R Q (SymOperad.one R) := rfl

lemma Und.comp_eq (i : A) (x : Q A) (y : Q B) :
    SetOperad.comp i (Und.of R Q x) (Und.of R Q y)
      = Und.of R Q (SymOperad.comp (R := R) i x y) := rfl

end Und

section Adjunction

variable (R : Type u) [CommRing R]
  {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- Extend a morphism of set operads into the underlying set operad of `Q` linearly. -/
noncomputable def SetOperadHom.linExtend (φ : SetOperadHom S (Und R Q)) :
    SymOperadHom R (Lin R S) Q where
  app A _ _ := Finsupp.lift (Q A) R (S A) (fun s => (Und.of R Q).symm (φ.app A s))
  app_map e x := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, hx, hx']
    | single s r =>
      show Finsupp.lift (Q _) R (S _) _ (Lin.mapL R e (Finsupp.single s r)) = _
      rw [Lin.mapL_single]
      simp only [Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul, map_smul]
      rw [φ.app_map e s]
      rfl
  app_one := by
    show Finsupp.lift (Q _) R (S _) _ (Finsupp.single SetOperad.one 1) = _
    simp only [Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul, one_smul]
    rw [φ.app_one]
    rfl
  app_comp i x y := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | single t r' =>
        show Finsupp.lift (Q _) R (S _) _
            (Lin.compL R i (Finsupp.single s r) (Finsupp.single t r')) = _
        rw [Lin.compL_single]
        simp only [Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul, map_smul,
          LinearMap.smul_apply, mul_smul]
        rw [φ.app_comp i s t, smul_comm]
        rfl

/-- Restrict a morphism out of the linearization to the basis. -/
noncomputable def SymOperadHom.restrictBasis (Φ : SymOperadHom R (Lin R S) Q) :
    SetOperadHom S (Und R Q) where
  app A _ _ := fun s => Und.of R Q (Φ.app A (Finsupp.single s 1))
  app_map e s := by
    show Und.of R Q (Φ.app _ (Finsupp.single (SetOperad.map e s) 1))
      = Und.of R Q (SymOperad.map (R := R) e (Φ.app _ (Finsupp.single s 1)))
    rw [← Φ.app_map]
    exact congrArg _ (congrArg _ (Lin.mapL_single (R := R) e s 1).symm)
  app_one := congrArg (Und.of R Q) Φ.app_one
  app_comp i s t := by
    show Und.of R Q (Φ.app _ (Finsupp.single (SetOperad.comp i s t) 1))
      = Und.of R Q (SymOperad.comp (R := R) i (Φ.app _ (Finsupp.single s 1))
          (Φ.app _ (Finsupp.single t 1)))
    rw [← Φ.app_comp]
    refine congrArg _ (congrArg _ ?_)
    rw [show (Finsupp.single (SetOperad.comp i s t) (1 : R))
        = Finsupp.single (SetOperad.comp i s t) (1 * 1) by rw [mul_one]]
    exact (Lin.compL_single (R := R) i s t 1 1).symm

/-- **The linearization adjunction**: a morphism of linear operads out of `Lin R S` is the same as a
morphism of set operads out of `S` into the underlying set operad. -/
noncomputable def linHomEquiv : SetOperadHom S (Und R Q) ≃ SymOperadHom R (Lin R S) Q where
  toFun φ := SetOperadHom.linExtend R φ
  invFun Φ := SymOperadHom.restrictBasis R Φ
  left_inv φ := by
    ext A _ _ s
    show Und.of R Q (Finsupp.lift (Q A) R (S A) _ (Finsupp.single s 1)) = φ.app A s
    simp
  right_inv Φ := by
    ext A _ _ x
    exact Lin.induction₁ (R := R) _ (Φ.app A) (fun s => by
      show Finsupp.lift (Q A) R (S A) _ (Finsupp.single s 1) = _
      simp
      rfl) x

end Adjunction

end Operad
