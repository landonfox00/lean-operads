/-
# Graded cooperads

The dual of `Operad.GrOperad`, in the conventions of `Operad.SymCooperad`: a **graded cooperad**
(`GrCooperad`) is a graded linear species with a counit and infinitesimal decompositions

  `decomp i : C (Without A i ⊕ B) →ₗ C A ⊗ C B`

preserving parities (`GrCooperad.decomp_par`), satisfying the axioms of a cooperad, with parallel
coassociativity up to the Koszul sign of exchanging the two inner cooperations: the super swap
`(x ⊗ y) ⊗ z ↦ σ(|y| |z|) (x ⊗ z) ⊗ y` (`sswapLast`).

* **Coaugmentations** (`GrCooperad.Coaug`): an even cooperation `1` of arity one, of counit one,
  whose relabellings span a subcooperad.
* **The reduced part** `C̄ = C / R·1` (`GrCooperad.Red`), the quotient by the span of the
  relabellings of `1`, a graded linear species, and **the parity shift** of a graded linear species
  (`GrSpecies.Shift`): the generators `s⁻¹ C̄` of the cobar construction.
* The sign twist of a graded linear species (`GrSpecies.tw`) and its compatibility with the
  decompositions (`GrCooperad.decomp_tw`).
-/
import Operad.InvPreLie
import Operad.Cooperad

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Parities on tensor products -/

section Tensor

variable {R : Type u} [CommRing R] {X Y Z : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y]
  [Module R Y] [AddCommGroup Z] [Module R Z]

variable (R) in
/-- The parity projections of a tensor product of super modules: `x ⊗ y` has parity
`|x| + |y|`. -/
noncomputable def tpar (pX : Bool → X →ₗ[R] X) (pY : Bool → Y →ₗ[R] Y) (b : Bool) :
    X ⊗[R] Y →ₗ[R] X ⊗[R] Y :=
  TensorProduct.map (pX false) (pY b) + TensorProduct.map (pX true) (pY (!b))

lemma tpar_tmul (pX : Bool → X →ₗ[R] X) (pY : Bool → Y →ₗ[R] Y) (b : Bool) (x : X) (y : Y) :
    tpar R pX pY b (x ⊗ₜ y) = pX false x ⊗ₜ pY b y + pX true x ⊗ₜ pY (!b) y := rfl

variable (R) in
/-- **The super swap of the last two factors**: `(x ⊗ y) ⊗ z ↦ σ(|y| |z|) (x ⊗ z) ⊗ y`. -/
noncomputable def sswapLast (pY : Bool → Y →ₗ[R] Y) (pZ : Bool → Z →ₗ[R] Z) :
    (X ⊗[R] Y) ⊗[R] Z →ₗ[R] (X ⊗[R] Z) ⊗[R] Y :=
  ∑ q : Bool, ∑ r : Bool, σ R (q && r) •
    ((swapLast R X Y Z).toLinearMap ∘ₗ TensorProduct.map (LinearMap.lTensor X (pY q)) (pZ r))

lemma sswapLast_tmul (pY : Bool → Y →ₗ[R] Y) (pZ : Bool → Z →ₗ[R] Z) (x : X) (y : Y) (z : Z) :
    sswapLast R pY pZ ((x ⊗ₜ y) ⊗ₜ z)
      = ∑ q : Bool, ∑ r : Bool, σ R (q && r) • ((x ⊗ₜ pZ r z) ⊗ₜ pY q y) := by
  simp only [sswapLast, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearEquiv.coe_coe]
  rfl

end Tensor

namespace SymSpecies

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [SymSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

@[simp] lemma map_symm_map (e : A ≃ B) (x : V A) :
    map (R := R) e.symm (map (R := R) e x) = x := by
  rw [← map_trans, Equiv.self_trans_symm, map_refl]

@[simp] lemma map_map_symm (e : A ≃ B) (y : V B) :
    map (R := R) e (map (R := R) e.symm y) = y := by
  rw [← map_trans, Equiv.symm_trans_self, map_refl]

end SymSpecies

/-! ## The sign twist of a graded linear species -/

namespace GrSpecies

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The sign twist of parity `e`**: `x ↦ σ(e |x|) x` on homogeneous elements. -/
def tw (e : Bool) : V A →ₗ[R] V A := par false + σ R e • par true

lemma tw_apply (e : Bool) (x : V A) :
    tw (R := R) e x = par (R := R) false x + σ R e • par (R := R) true x := rfl

lemma tw_hom (e : Bool) {c : Bool} {x : V A} (h : par (R := R) c x = x) :
    tw (R := R) e x = σ R (e && c) • x := by
  rw [tw_apply, ← h, par_par, par_par]
  cases c <;> cases e <;> simp

lemma par_tw (e c : Bool) (x : V A) :
    par (R := R) c (tw (R := R) e x) = tw (R := R) e (par (R := R) c x) := by
  simp only [tw_apply, map_add, map_smul, par_par]
  cases c <;> simp

lemma map_tw (e : Bool) (σ' : A ≃ B) (x : V A) :
    SymSpecies.map (R := R) σ' (tw (R := R) e x) = tw (R := R) e (SymSpecies.map (R := R) σ' x)
    := by
  simp only [tw_apply, map_add, map_smul, map_par]

@[simp] lemma tw_false (x : V A) : tw (R := R) false x = x := by
  rw [tw_apply, σ_false, one_smul, par_add]

lemma tw_false_eq_id : tw (R := R) (V := V) (A := A) false = LinearMap.id :=
  LinearMap.ext tw_false

/-- The sign twists compose: `tw e ∘ tw e' = tw (e + e')`. -/
lemma tw_tw (e e' : Bool) (x : V A) :
    tw (R := R) e (tw (R := R) e' x) = tw (R := R) (xor e e') x := by
  simp only [tw_apply, map_add, map_smul, par_par]
  cases e <;> cases e' <;> simp

/-! ### The parity shift -/

variable (V) in
/-- **The parity shift** of a graded linear species: the same modules and relabellings, with the
parities exchanged. -/
@[nolint unusedArguments]
def Shift (_R : Type u) [CommRing _R] (A : Type) [Fintype A] [DecidableEq A] : Type v := V A

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (Shift V R A) :=
  inferInstanceAs (AddCommGroup (V A))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (Shift V R A) :=
  inferInstanceAs (Module R (V A))

/-- **The parity shift is a graded linear species.** -/
instance instGrSpeciesShift : GrSpecies R (Shift V R) where
  map e := SymSpecies.map (R := R) (V := V) e
  map_refl := SymSpecies.map_refl (R := R) (V := V)
  map_trans := SymSpecies.map_trans (R := R) (V := V)
  par b := par (R := R) (V := V) (!b)
  par_add x := (add_comm _ _).trans (par_add (R := R) (V := V) x)
  par_par b b' x := by
    show par (R := R) (V := V) (!b) (par (R := R) (V := V) (!b') x) = _
    rw [par_par]
    simp only [Bool.not_inj_iff]
    rfl
  map_par e b x := map_par (R := R) (V := V) e (!b) x

/-- An element, in the parity shift. -/
def Shift.of (A : Type) [Fintype A] [DecidableEq A] : V A ≃ₗ[R] Shift V R A := LinearEquiv.refl R _

@[simp] lemma Shift.par_of (b : Bool) (x : V A) :
    par (R := R) (V := Shift V R) b (Shift.of A x) = Shift.of A (par (R := R) (!b) x) := rfl

@[simp] lemma Shift.map_of (e : A ≃ B) (x : V A) :
    SymSpecies.map (R := R) (V := Shift V R) e (Shift.of A x)
      = Shift.of B (SymSpecies.map (R := R) e x) := rfl

end GrSpecies

/-! ## Graded cooperads -/

/-- **A graded cooperad**: a graded linear species with a counit and infinitesimal decompositions
preserving parities, satisfying the axioms of a cooperad, parallel coassociativity holding up to
the Koszul sign of exchanging the two inner cooperations. -/
class GrCooperad (R : Type u) [CommRing R]
    (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] extends GrSpecies R C where
  /-- The counit. -/
  counit : C Unit →ₗ[R] R
  /-- The counit is even. -/
  counit_par : counit ∘ₗ par true = 0
  /-- **Infinitesimal decomposition**: split off an inner cooperation with inputs `B`, plugged
  at the input `i` of an outer one with inputs `A`. -/
  decomp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) :
    C (Without A i ⊕ B) →ₗ[R] C A ⊗[R] C B
  /-- Decomposition preserves parities. -/
  decomp_par {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (b : Bool) :
    decomp (B := B) i ∘ₗ par b = tpar R (fun c => par c) (fun c => par c) b ∘ₗ decomp i
  /-- Decomposition is natural in bijections of both input sets. -/
  decomp_map {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (σ' : A ≃ A') (τ : B ≃ B')
    (i : A) :
    decomp (σ' i) ∘ₗ map (compEquiv σ' τ i) = TensorProduct.map (map σ') (map τ) ∘ₗ decomp i
  /-- The right counit law. -/
  counit_right {A : Type} [Fintype A] [DecidableEq A] (i : A) :
    (TensorProduct.rid R (C A)).toLinearMap ∘ₗ LinearMap.lTensor (C A) counit ∘ₗ decomp i ∘ₗ
      map (rightUnitEquiv i).symm = LinearMap.id
  /-- The left counit law. -/
  counit_left {B : Type} [Fintype B] [DecidableEq B] :
    (TensorProduct.lid R (C B)).toLinearMap ∘ₗ LinearMap.rTensor (C B) counit ∘ₗ
      decomp () ∘ₗ map (leftUnitEquiv B).symm = LinearMap.id
  /-- Sequential coassociativity. -/
  decomp_assoc_seq {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) :
    LinearMap.lTensor (C A) (decomp (B := D) j) ∘ₗ decomp i
      = (TensorProduct.assoc R (C A) (C B) (C D)).toLinearMap ∘ₗ
          LinearMap.rTensor (C D) (decomp i) ∘ₗ decomp (Sum.inr j) ∘ₗ map (seqEquiv i j D).symm
  /-- **Parallel coassociativity, up to the Koszul sign** of exchanging the inner
  cooperations. -/
  decomp_assoc_par {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) :
    LinearMap.rTensor (C B) (decomp (B := D) k) ∘ₗ decomp (Sum.inl ⟨i, hik⟩)
      = sswapLast R (fun c => par c) (fun c => par c) ∘ₗ
          LinearMap.rTensor (C D) (decomp i) ∘ₗ decomp (Sum.inl ⟨k, Ne.symm hik⟩) ∘ₗ
            map (parEquiv hik B D).symm

namespace GrCooperad

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **Decomposition commutes with the sign twists.** -/
lemma decomp_tw (e : Bool) (i : A) :
    decomp (R := R) (C := C) (B := B) i ∘ₗ GrSpecies.tw (R := R) e
      = TensorProduct.map (GrSpecies.tw (R := R) e) (GrSpecies.tw (R := R) e) ∘ₗ
          decomp (R := R) i := by
  have h0 := decomp_par (R := R) (C := C) (B := B) i false
  have h1 := decomp_par (R := R) (C := C) (B := B) i true
  apply LinearMap.ext
  intro x
  have e0 := LinearMap.congr_fun h0 x
  have e1 := LinearMap.congr_fun h1 x
  simp only [LinearMap.comp_apply] at e0 e1
  rw [LinearMap.comp_apply, GrSpecies.tw_apply, map_add, map_smul, e0, e1, LinearMap.comp_apply]
  induction decomp (R := R) i x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [tpar_tmul, TensorProduct.map_tmul, GrSpecies.tw_apply, Bool.not_false,
      Bool.not_true, TensorProduct.tmul_add, TensorProduct.add_tmul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', smul_add, smul_smul]
    cases e <;> simp only [σ_false, σ_true, one_smul, mul_one, mul_neg, neg_neg, neg_smul] <;>
      abel
  | add a b ha hb =>
    rw [map_add, map_add, map_add, smul_add, ← ha, ← hb]
    abel

/-! ## Coaugmentations and the reduced part -/

variable (R C) in
/-- The span of the relabellings of a cooperation of arity one. -/
def unitSpanOf (one : C Unit) (A : Type) [Fintype A] [DecidableEq A] : Submodule R (C A) :=
  Submodule.span R (Set.range fun e : Unit ≃ A => SymSpecies.map (R := R) e one)

variable (R C) in
/-- **A coaugmentation** of a graded cooperad: an even cooperation `1` of arity one, of counit
one, whose relabellings span a subcooperad. -/
class Coaug where
  /-- The coaugmentation, the cooperation `1` of arity one. -/
  one : C Unit
  par_one : GrSpecies.par (R := R) false one = one
  counit_one : counit (R := R) (C := C) one = 1
  /-- The decompositions of the relabellings of `1` are tensors of relabellings of `1`. -/
  decomp_mem {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (e : Unit ≃ Without A i ⊕ B) :
    decomp (R := R) (C := C) i (SymSpecies.map (R := R) e one)
      ∈ Submodule.map₂ (TensorProduct.mk R (C A) (C B)) (unitSpanOf R C one A)
          (unitSpanOf R C one B)

variable [Coaug R C]

variable (R C) in
/-- The span `R·1` of the relabellings of the coaugmentation. -/
abbrev unitSpan (A : Type) [Fintype A] [DecidableEq A] : Submodule R (C A) :=
  unitSpanOf R C (Coaug.one (R := R)) A

lemma map_one_mem (e : Unit ≃ A) :
    SymSpecies.map (R := R) e (Coaug.one (R := R) (C := C)) ∈ unitSpan R C A :=
  Submodule.subset_span ⟨e, rfl⟩

lemma unitSpan_le_comap_map (σ' : A ≃ B) :
    unitSpan R C A ≤ (unitSpan R C B).comap (SymSpecies.map (R := R) σ') := by
  rw [unitSpan, unitSpanOf, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  show SymSpecies.map (R := R) σ' (SymSpecies.map (R := R) e _) ∈ unitSpan R C B
  rw [← SymSpecies.map_trans]
  exact map_one_mem _

lemma unitSpan_le_comap_par (b : Bool) :
    unitSpan R C A ≤ (unitSpan R C A).comap (GrSpecies.par (R := R) b) := by
  rw [unitSpan, unitSpanOf, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  show GrSpecies.par (R := R) b (SymSpecies.map (R := R) e _) ∈ unitSpan R C A
  rw [← GrSpecies.map_par, ← Coaug.par_one (R := R) (C := C), GrSpecies.par_par]
  cases b
  · rw [if_pos rfl, Coaug.par_one]
    exact map_one_mem _
  · rw [if_neg (by decide), map_zero]
    exact Submodule.zero_mem _

variable (R C) in
/-- **The reduced part** `C̄ = C / R·1` of a coaugmented graded cooperad. -/
def Red (A : Type) [Fintype A] [DecidableEq A] : Type v := C A ⧸ unitSpan R C A

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (Red R C A) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (Red R C A) :=
  inferInstanceAs (Module R (_ ⧸ _))

variable (R C) in
/-- The projection onto the reduced part. -/
def Red.proj (A : Type) [Fintype A] [DecidableEq A] : C A →ₗ[R] Red R C A := (unitSpan R C A).mkQ

lemma Red.proj_surjective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Surjective (Red.proj R C A) :=
  Submodule.mkQ_surjective _

lemma Red.proj_map_one (e : Unit ≃ A) :
    Red.proj R C A (SymSpecies.map (R := R) e (Coaug.one (R := R) (C := C))) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (map_one_mem e)

/-- **The reduced part is a graded linear species.** -/
instance Red.instGrSpecies : GrSpecies R (Red R C) where
  map σ' := Submodule.mapQ _ _ (SymSpecies.map (R := R) σ') (unitSpan_le_comap_map σ')
  map_refl X := by
    obtain ⟨x, rfl⟩ := Red.proj_surjective _ X
    exact congrArg (Red.proj R C _) (SymSpecies.map_refl (R := R) x)
  map_trans σ' τ X := by
    obtain ⟨x, rfl⟩ := Red.proj_surjective _ X
    exact congrArg (Red.proj R C _) (SymSpecies.map_trans (R := R) σ' τ x)
  par b := Submodule.mapQ _ _ (GrSpecies.par (R := R) b) (unitSpan_le_comap_par b)
  par_add X := by
    obtain ⟨x, rfl⟩ := Red.proj_surjective _ X
    exact (map_add (Red.proj R C _) _ _).symm.trans
      (congrArg (Red.proj R C _) (GrSpecies.par_add (R := R) x))
  par_par b b' X := by
    obtain ⟨x, rfl⟩ := Red.proj_surjective _ X
    show Red.proj R C _ (GrSpecies.par (R := R) b (GrSpecies.par (R := R) b' x)) = _
    rw [GrSpecies.par_par]
    split_ifs
    · rfl
    · exact map_zero _
  map_par σ' b X := by
    obtain ⟨x, rfl⟩ := Red.proj_surjective _ X
    exact congrArg (Red.proj R C _) (GrSpecies.map_par (R := R) σ' b x)

@[simp] lemma Red.map_proj (σ' : A ≃ B) (x : C A) :
    SymSpecies.map (R := R) σ' (Red.proj R C A x)
      = Red.proj R C B (SymSpecies.map (R := R) σ' x) := rfl

@[simp] lemma Red.par_proj (b : Bool) (x : C A) :
    GrSpecies.par (R := R) b (Red.proj R C A x)
      = Red.proj R C A (GrSpecies.par (R := R) b x) := rfl

end GrCooperad

end Operad
