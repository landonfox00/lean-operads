/-
# The convolution operad of a graded cooperad and a graded operad

For a graded cooperad `C` and a graded operad `P`, the linear maps `C A → P A` form a graded
operad (`ConvOp R C P`, `ConvOp.instGrOperad`), **the convolution operad**: a map of parity `p`
raises parities by `p`, relabellings act on both sides, the unit is the counit followed by the
unit, and the composite of `f` and `g` decomposes, applies `f ⊗ g` with the Koszul sign, and
composes,

  `(f ∘ᵢ g) = μᵢ ∘ (f ⊗ g) ∘ Δᵢ`,   `(f ⊗ g)(x ⊗ y) = σ(|g| |x|) f x ⊗ g y`.

Every axiom of a graded operad for `ConvOp R C P` is the corresponding axiom of `P` combined with
that of `C`, the Koszul signs of the parallel axioms matching. Its invariant families
(`GrOperad.Inv`) are the equivariant maps `C → P`, and their product is the convolution product.

* Composing with a morphism of graded operads is a morphism of convolution operads
  (`ConvOp.postHom`), and composing with a derivation of `P` is a derivation of the convolution
  operad (`ConvOp.postDer`).
-/
import Operad.GrCooperad

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace GrOperad

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
/-- A homogeneous operation has a single nonzero parity part. -/
lemma par_of_hom {c d : Bool} {z : P A} (h : par (R := R) d z = z) :
    par (R := R) c z = if c = d then z else 0 := by
  rw [← h, par_par, h]

/-- **The parity parts of a composite with a homogeneous left factor.** -/
lemma par_comp_par_left (i : A) (c p : Bool) (x : P A) (y : P B) :
    par (R := R) c (comp (R := R) i (par (R := R) p x) y)
      = comp (R := R) i (par (R := R) p x) (par (R := R) (xor c p) y) := by
  conv_lhs => rw [← par_add (R := R) y]
  rw [map_add, map_add, par_of_hom (comp_par i p false x y), par_of_hom (comp_par i p true x y)]
  cases c <;> cases p <;> simp

end GrOperad

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]

variable (R C P) in
/-- **The convolution operad**: the linear maps `C A → P A`. -/
@[nolint unusedArguments]
def ConvOp (A : Type) [Fintype A] [DecidableEq A] : Type (max v w) := C A →ₗ[R] P A

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (ConvOp R C P A) :=
  inferInstanceAs (AddCommGroup (C A →ₗ[R] P A))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (ConvOp R C P A) :=
  inferInstanceAs (Module R (C A →ₗ[R] P A))

namespace ConvOp

variable {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
  [DecidableEq D]

/-- A linear map, as an element of the convolution operad. -/
def of (f : C A →ₗ[R] P A) : ConvOp R C P A := f

/-- The underlying linear map. -/
def toLin (f : ConvOp R C P A) : C A →ₗ[R] P A := f

@[simp] lemma toLin_of (f : C A →ₗ[R] P A) : toLin (of f) = f := rfl

@[simp] lemma of_toLin (f : ConvOp R C P A) : of (toLin f) = f := rfl

@[simp] lemma toLin_add (f g : ConvOp R C P A) : toLin (f + g) = toLin f + toLin g := rfl

@[simp] lemma toLin_smul (a : R) (f : ConvOp R C P A) : toLin (a • f) = a • toLin f := rfl

@[simp] lemma toLin_zero : toLin (0 : ConvOp R C P A) = 0 := rfl

@[simp] lemma toLin_sub (f g : ConvOp R C P A) : toLin (f - g) = toLin f - toLin g := rfl

@[simp] lemma toLin_neg (f : ConvOp R C P A) : toLin (-f) = -toLin f := rfl

@[simp] lemma toLin_sum {I : Type} (s : Finset I) (f : I → ConvOp R C P A) :
    toLin (∑ i ∈ s, f i) = ∑ i ∈ s, toLin (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => simp only [Finset.sum_insert ha, toLin_add, ih]

@[ext] lemma ext {f g : ConvOp R C P A} (h : ∀ x, toLin f x = toLin g x) : f = g :=
  LinearMap.ext h

variable [GrCooperad R C] [GrOperad R P]

/-! ### Parities -/

/-- The parity projections: the part of a linear map raising parities by `b`. -/
def parC (b : Bool) : ConvOp R C P A →ₗ[R] ConvOp R C P A where
  toFun f := of (∑ c : Bool,
    GrOperad.par (R := R) (xor c b) ∘ₗ toLin f ∘ₗ GrSpecies.par (R := R) (V := C) c)
  map_add' f g := by
    simp only [toLin_add, LinearMap.add_comp, LinearMap.comp_add]
    exact Finset.sum_add_distrib
  map_smul' a f := by
    simp only [toLin_smul, LinearMap.smul_comp, LinearMap.comp_smul]
    exact Finset.smul_sum.symm

lemma parC_apply (b : Bool) (f : ConvOp R C P A) (x : C A) :
    toLin (parC b f) x = ∑ c : Bool,
      GrOperad.par (R := R) (xor c b) (toLin f (GrSpecies.par (R := R) c x)) := by
  simp only [parC, LinearMap.coe_mk, AddHom.coe_mk, toLin_of, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.comp_apply]

/-- A linear map **raising parities by `p`**. -/
def IsParC (p : Bool) (f : ConvOp R C P A) : Prop :=
  ∀ (c : Bool) (x : C A), toLin f (GrSpecies.par (R := R) c x)
    = GrOperad.par (R := R) (xor c p) (toLin f x)

lemma parC_eq_self_iff {p : Bool} {f : ConvOp R C P A} : parC p f = f ↔ IsParC p f := by
  constructor
  · intro h c x
    have key : ∀ y, toLin f y
        = ∑ d : Bool, GrOperad.par (R := R) (xor d p) (toLin f (GrSpecies.par (R := R) d y)) :=
      fun y => by
        conv_lhs => rw [← h]
        exact parC_apply p f y
    rw [key (GrSpecies.par (R := R) c x), key x, map_sum]
    cases c <;> cases p <;> simp [GrSpecies.par_par, GrOperad.par_par]
  · intro h
    ext x
    have h' : ∀ c, toLin f (GrSpecies.par (R := R) c x)
        = GrOperad.par (R := R) (xor c p) (toLin f x) := fun c => h c x
    rw [parC_apply]
    simp only [h', GrOperad.par_par, if_true, Fintype.sum_bool]
    cases p
    · rw [Bool.true_xor, Bool.false_xor, Bool.not_false, add_comm]
      exact GrOperad.par_add _
    · rw [Bool.true_xor, Bool.false_xor, Bool.not_true]
      exact GrOperad.par_add _

lemma isParC_parC (p : Bool) (f : ConvOp R C P A) : IsParC p (parC p f) := by
  intro c x
  rw [parC_apply, parC_apply, map_sum]
  cases c <;> cases p <;> simp [GrSpecies.par_par, GrOperad.par_par]

lemma parC_add (f : ConvOp R C P A) : parC false f + parC true f = f := by
  ext x
  rw [toLin_add, LinearMap.add_apply, parC_apply, parC_apply, ← Finset.sum_add_distrib]
  have : ∀ c : Bool, GrOperad.par (R := R) (xor c false) (toLin f (GrSpecies.par (R := R) c x))
      + GrOperad.par (R := R) (xor c true) (toLin f (GrSpecies.par (R := R) c x))
      = toLin f (GrSpecies.par (R := R) c x) := fun c => by
    cases c
    · exact GrOperad.par_add _
    · exact (add_comm _ _).trans (GrOperad.par_add _)
  rw [Finset.sum_congr rfl (fun c _ => this c), ← map_sum, Fintype.sum_bool, add_comm,
    GrSpecies.par_add]

/-! ### The sign twist -/

lemma toLin_comp_tw {p : Bool} {f : ConvOp R C P A} (hf : IsParC p f) (e : Bool) :
    toLin f ∘ₗ GrSpecies.tw (R := R) e = σ R (e && p) • (GrOperad.tw (R := R) e ∘ₗ toLin f) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, GrSpecies.tw_apply, GrOperad.tw_apply,
    map_add, map_smul]
  rw [hf false x, hf true x]
  cases e <;> cases p <;> simp <;> abel

lemma parC_parC (b b' : Bool) (f : ConvOp R C P A) :
    parC b (parC b' f) = if b = b' then parC b' f else 0 := by
  ext x
  by_cases h : b = b'
  · subst h
    rw [if_pos rfl]
    simp only [parC_apply, map_sum, GrSpecies.par_par, GrOperad.par_par]
    cases b <;> simp
  · rw [if_neg h, toLin_zero, LinearMap.zero_apply]
    simp only [parC_apply, map_sum, GrSpecies.par_par, GrOperad.par_par]
    cases b <;> cases b' <;> simp_all

lemma parC_of_isParC {p : Bool} {f : ConvOp R C P A} (hf : IsParC p f) (b : Bool) :
    parC b f = if b = p then f else 0 := by
  rw [← parC_eq_self_iff.2 hf, parC_parC]

/-! ### Relabellings, unit and compositions -/

/-- The relabellings: `f ↦ map σ ∘ f ∘ map σ⁻¹`. -/
def mapC (σ' : A ≃ B) : ConvOp R C P A →ₗ[R] ConvOp R C P B where
  toFun f := of (GrOperad.map (R := R) σ' ∘ₗ toLin f ∘ₗ SymSpecies.map (R := R) (V := C) σ'.symm)
  map_add' f g := by
    simp only [toLin_add, LinearMap.add_comp, LinearMap.comp_add]
    rfl
  map_smul' a f := by
    simp only [toLin_smul, LinearMap.smul_comp, LinearMap.comp_smul]
    rfl

lemma mapC_apply (σ' : A ≃ B) (f : ConvOp R C P A) (x : C B) :
    toLin (mapC σ' f) x
      = GrOperad.map (R := R) σ' (toLin f (SymSpecies.map (R := R) σ'.symm x)) := rfl

variable (R C P) in
/-- The unit: the counit followed by the unit of `P`. -/
def oneC : ConvOp R C P Unit :=
  of ((GrCooperad.counit (R := R) (C := C)).smulRight (GrOperad.one (R := R) (P := P)))

lemma oneC_apply (x : C Unit) :
    toLin (oneC R C P) x = GrCooperad.counit (R := R) x • GrOperad.one (R := R) (P := P) := rfl

/-- The composition of `P`, on tensors. -/
noncomputable def mu (i : A) : P A ⊗[R] P B →ₗ[R] P (Without A i ⊕ B) :=
  TensorProduct.lift (GrOperad.comp (R := R) i)

@[simp] lemma mu_tmul (i : A) (x : P A) (y : P B) :
    mu (R := R) i (x ⊗ₜ y) = GrOperad.comp (R := R) i x y :=
  TensorProduct.lift.tmul _ _

/-- The tensor product of two linear maps with the Koszul sign: `x ⊗ y ↦ σ(|g| |x|) f x ⊗ g y`. -/
noncomputable def kap (f : ConvOp R C P A) (g : ConvOp R C P B) : C A ⊗[R] C B →ₗ[R] P A ⊗[R] P B :=
  ∑ q : Bool, TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) q) (toLin (parC q g))

lemma kap_hom {q : Bool} (f : ConvOp R C P A) {g : ConvOp R C P B} (hg : IsParC q g) :
    kap f g = TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) q) (toLin g) := by
  simp only [kap, Fintype.sum_bool, parC_of_isParC hg]
  cases q <;> simp

lemma kap_tmul {q : Bool} (f : ConvOp R C P A) {g : ConvOp R C P B} (hg : IsParC q g) (x : C A)
    (y : C B) : kap f g (x ⊗ₜ y) = toLin f (GrSpecies.tw (R := R) q x) ⊗ₜ toLin g y := by
  rw [kap_hom f hg]
  rfl

lemma kap_add_left (f f' : ConvOp R C P A) (g : ConvOp R C P B) :
    kap (f + f') g = kap f g + kap f' g := by
  simp only [kap, toLin_add, LinearMap.add_comp, TensorProduct.map_add_left,
    Finset.sum_add_distrib]

lemma kap_smul_left (a : R) (f : ConvOp R C P A) (g : ConvOp R C P B) :
    kap (a • f) g = a • kap f g := by
  simp only [kap, toLin_smul, LinearMap.smul_comp, TensorProduct.map_smul_left, Finset.smul_sum]

lemma kap_add_right (f : ConvOp R C P A) (g g' : ConvOp R C P B) :
    kap f (g + g') = kap f g + kap f g' := by
  simp only [kap, map_add, toLin_add, TensorProduct.map_add_right, Finset.sum_add_distrib]

lemma kap_smul_right (a : R) (f : ConvOp R C P A) (g : ConvOp R C P B) :
    kap f (a • g) = a • kap f g := by
  simp only [kap, map_smul, toLin_smul, TensorProduct.map_smul_right, Finset.smul_sum]

/-- **The compositions**: `f ∘ᵢ g = μᵢ ∘ (f ⊗ g) ∘ Δᵢ`, with the Koszul sign. -/
noncomputable def compC (i : A) :
    ConvOp R C P A →ₗ[R] ConvOp R C P B →ₗ[R] ConvOp R C P (Without A i ⊕ B) :=
  LinearMap.mk₂ R (fun f g => of (mu i ∘ₗ kap f g ∘ₗ GrCooperad.decomp (R := R) (C := C) i))
    (fun f f' g => by
      simp only [kap_add_left, LinearMap.add_comp, LinearMap.comp_add]
      rfl)
    (fun a f g => by
      simp only [kap_smul_left, LinearMap.smul_comp, LinearMap.comp_smul]
      rfl)
    (fun f g g' => by
      simp only [kap_add_right, LinearMap.add_comp, LinearMap.comp_add]
      rfl)
    (fun a f g => by
      simp only [kap_smul_right, LinearMap.smul_comp, LinearMap.comp_smul]
      rfl)

lemma toLin_compC (i : A) (f : ConvOp R C P A) (g : ConvOp R C P B) :
    toLin (compC i f g) = mu i ∘ₗ kap f g ∘ₗ GrCooperad.decomp (R := R) (C := C) i := rfl

/-! ### The axioms -/

lemma mapC_refl (f : ConvOp R C P A) : mapC (Equiv.refl A) f = f := by
  ext x
  rw [mapC_apply, Equiv.refl_symm, SymSpecies.map_refl, GrOperad.map_refl]

lemma mapC_trans (σ' : A ≃ B) (τ : B ≃ D) (f : ConvOp R C P A) :
    mapC (σ'.trans τ) f = mapC τ (mapC σ' f) := by
  ext x
  rw [mapC_apply, mapC_apply, mapC_apply,
    show (σ'.trans τ).symm = τ.symm.trans σ'.symm from rfl, SymSpecies.map_trans,
    GrOperad.map_trans]

lemma mapC_parC (σ' : A ≃ B) (b : Bool) (f : ConvOp R C P A) :
    mapC σ' (parC b f) = parC b (mapC σ' f) := by
  ext x
  simp only [mapC_apply, parC_apply, map_sum, GrOperad.map_par, GrSpecies.map_par]

lemma counit_par_false (x : C Unit) :
    GrCooperad.counit (R := R) (GrSpecies.par (R := R) false x) = GrCooperad.counit (R := R) x := by
  have h := LinearMap.congr_fun (GrCooperad.counit_par (R := R) (C := C)) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  conv_rhs => rw [← GrSpecies.par_add (R := R) x, map_add, h, add_zero]

lemma isParC_oneC : IsParC false (oneC R C P) := by
  intro c x
  simp only [oneC_apply, map_smul, Bool.xor_false]
  have h := LinearMap.congr_fun (GrCooperad.counit_par (R := R) (C := C)) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  cases c
  · rw [counit_par_false, GrOperad.par_one]
  · rw [h, zero_smul, ← GrOperad.par_one (R := R) (P := P), GrOperad.par_par, if_neg (by decide),
      smul_zero]

lemma parC_oneC : parC false (oneC R C P) = oneC R C P :=
  parC_eq_self_iff.2 isParC_oneC

lemma tw_par (e d : Bool) (x : C A) :
    GrSpecies.tw (R := R) e (GrSpecies.par (R := R) d x)
      = σ R (e && d) • GrSpecies.par (R := R) d x :=
  GrSpecies.tw_hom e (GrSpecies.par_par_self d x)

/-- **A composite of homogeneous maps has the sum of their parities.** -/
lemma isParC_compC {p q : Bool} (i : A) {f : ConvOp R C P A} {g : ConvOp R C P B} (hf : IsParC p f)
    (hg : IsParC q g) : IsParC (xor p q) (compC i f g) := by
  intro c x
  have hd := LinearMap.congr_fun (GrCooperad.decomp_par (R := R) (C := C) (B := B) i c) x
  simp only [LinearMap.comp_apply] at hd
  rw [toLin_compC, LinearMap.comp_apply, LinearMap.comp_apply, hd, LinearMap.comp_apply,
    LinearMap.comp_apply]
  induction GrCooperad.decomp (R := R) (C := C) i x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have hf' : ∀ (c : Bool) (y : C A), toLin f (GrSpecies.par (R := R) c y)
        = GrOperad.par (R := R) (xor c p) (toLin f y) := hf
    have hg' : ∀ (c : Bool) (y : C B), toLin g (GrSpecies.par (R := R) c y)
        = GrOperad.par (R := R) (xor c q) (toLin g y) := hg
    rw [tpar_tmul, map_add, map_add, kap_tmul f hg, kap_tmul f hg, kap_tmul f hg, mu_tmul,
      mu_tmul, mu_tmul]
    conv_rhs => rw [← GrSpecies.par_add (R := R) a]
    simp only [map_add, LinearMap.add_apply, tw_par, map_smul, LinearMap.smul_apply, hf', hg',
      GrOperad.par_comp_par_left]
    cases c <;> cases p <;> cases q <;> simp
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb, map_add, map_add, map_add]

lemma parC_compC (i : A) (p q : Bool) (f : ConvOp R C P A) (g : ConvOp R C P B) :
    parC (xor p q) (compC i (parC p f) (parC q g)) = compC i (parC p f) (parC q g) :=
  parC_eq_self_iff.2 (isParC_compC i (isParC_parC p f) (isParC_parC q g))

lemma mapC_compC {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (σ' : A ≃ A') (τ : B ≃ B') (i : A) (f : ConvOp R C P A) (g : ConvOp R C P B) :
    mapC (compEquiv σ' τ i) (compC i f g) = compC (σ' i) (mapC σ' f) (mapC τ g) := by
  ext x
  obtain ⟨y, rfl⟩ : ∃ y, x = SymSpecies.map (R := R) (compEquiv σ' τ i) y :=
    ⟨SymSpecies.map (R := R) (compEquiv σ' τ i).symm x, by rw [SymSpecies.map_map_symm]⟩
  have hd := LinearMap.congr_fun (GrCooperad.decomp_map (R := R) (C := C) σ' τ i) y
  simp only [LinearMap.comp_apply] at hd
  rw [mapC_apply, SymSpecies.map_symm_map, toLin_compC, toLin_compC, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hd]
  induction GrCooperad.decomp (R := R) (C := C) i y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul, kap, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.comp_apply, map_sum, mu_tmul, ← mapC_parC, mapC_apply, GrSpecies.map_tw,
      SymSpecies.map_symm_map]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← GrOperad.map_comp]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb, map_add, map_add, map_add]

/-- The unit absorbs the twist: the counit is even. -/
lemma oneC_comp_tw (e : Bool) :
    toLin (oneC R C P) ∘ₗ GrSpecies.tw (R := R) e = toLin (oneC R C P) := by
  rw [toLin_comp_tw isParC_oneC e, Bool.and_false, σ_false, one_smul]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, oneC_apply, map_smul]
  rw [GrOperad.tw_hom e GrOperad.par_one, Bool.and_false, σ_false, one_smul]

lemma compC_oneC (i : A) (f : ConvOp R C P A) :
    mapC (rightUnitEquiv i) (compC i f (oneC R C P)) = f := by
  ext x
  have hc := LinearMap.congr_fun (GrCooperad.counit_right (R := R) (C := C) i) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at hc
  rw [mapC_apply, toLin_compC, kap_hom f isParC_oneC, GrSpecies.tw_false_eq_id,
    LinearMap.comp_id]
  have key : ∀ t, GrOperad.map (R := R) (rightUnitEquiv i)
      (mu i (TensorProduct.map (toLin f) (toLin (oneC R C P)) t))
      = toLin f ((TensorProduct.rid R (C A)) (LinearMap.lTensor (C A)
          (GrCooperad.counit (R := R) (C := C)) t)) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
      simp only [TensorProduct.map_tmul, oneC_apply, mu_tmul, map_smul, GrOperad.comp_one,
        LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add, map_add, map_add]
  conv_rhs => rw [← hc]
  exact key _

lemma oneC_compC (g : ConvOp R C P B) :
    mapC (leftUnitEquiv B) (compC () (oneC R C P) g) = g := by
  ext x
  have hc := LinearMap.congr_fun (GrCooperad.counit_left (R := R) (C := C) (B := B)) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at hc
  have hk : kap (oneC R C P) g = TensorProduct.map (toLin (oneC R C P)) (toLin g) := by
    simp only [kap, oneC_comp_tw, Fintype.sum_bool, ← TensorProduct.map_add_right, ← toLin_add,
      add_comm (parC true g), parC_add]
  rw [mapC_apply, toLin_compC, hk]
  have key : ∀ t, GrOperad.map (R := R) (leftUnitEquiv B)
      (mu () (TensorProduct.map (toLin (oneC R C P)) (toLin g) t))
      = toLin g ((TensorProduct.lid R (C B)) (LinearMap.rTensor (C B)
          (GrCooperad.counit (R := R) (C := C)) t)) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul u b =>
      simp only [TensorProduct.map_tmul, oneC_apply, mu_tmul, map_smul, LinearMap.smul_apply,
        GrOperad.one_comp, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add, map_add, map_add]
  conv_rhs => rw [← hc]
  exact key _

/-! ### Associativity -/

lemma decomp_tw_apply (e : Bool) (i : A) (u : C (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := C) i (GrSpecies.tw (R := R) e u)
      = TensorProduct.map (GrSpecies.tw (R := R) e) (GrSpecies.tw (R := R) e)
          (GrCooperad.decomp (R := R) (C := C) i u) :=
  LinearMap.congr_fun (GrCooperad.decomp_tw e i) u

/-- Sequential associativity, for homogeneous inner maps. -/
lemma compC_assoc_seq_hom (i : A) (j : B) (f : ConvOp R C P A) {q r : Bool} {g : ConvOp R C P B}
    {h : ConvOp R C P D} (hg : IsParC q g) (hh : IsParC r h) :
    mapC (seqEquiv i j D) (compC (Sum.inr j) (compC i f g) h) = compC i f (compC j g h) := by
  have hgh := isParC_compC j hg hh
  ext x
  set w := SymSpecies.map (R := R) (V := C) (seqEquiv i j D).symm x
  have hco := LinearMap.congr_fun (GrCooperad.decomp_assoc_seq (R := R) (C := C) (D := D) i j) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hco
  have hL : toLin (mapC (seqEquiv i j D) (compC (Sum.inr j) (compC i f g) h)) x
      = GrOperad.map (R := R) (seqEquiv i j D) (mu (Sum.inr j)
          (TensorProduct.map (mu i ∘ₗ TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) q)
            (toLin g) ∘ₗ TensorProduct.map (GrSpecies.tw (R := R) r) (GrSpecies.tw (R := R) r))
            (toLin h)
            (LinearMap.rTensor (C D) (GrCooperad.decomp (R := R) (C := C) i)
              (GrCooperad.decomp (R := R) (C := C) (Sum.inr j) w)))) := by
    rw [mapC_apply, toLin_compC, kap_hom _ hh, toLin_compC, kap_hom f hg]
    simp only [LinearMap.comp_apply]
    congr 2
    induction GrCooperad.decomp (R := R) (C := C) (Sum.inr j) w using TensorProduct.induction_on
      with
    | zero => simp
    | tmul u z =>
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.rTensor_tmul,
        decomp_tw_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hR : toLin (compC i f (compC j g h)) x
      = mu i (TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) (xor q r))
          (mu j ∘ₗ TensorProduct.map (toLin g ∘ₗ GrSpecies.tw (R := R) r) (toLin h))
          (TensorProduct.assoc R (C A) (C B) (C D)
            (LinearMap.rTensor (C D) (GrCooperad.decomp (R := R) (C := C) i)
              (GrCooperad.decomp (R := R) (C := C) (Sum.inr j) w)))) := by
    rw [toLin_compC, kap_hom f hgh, toLin_compC, kap_hom g hh]
    simp only [LinearMap.comp_apply]
    rw [← hco]
    congr 1
    induction GrCooperad.decomp (R := R) (C := C) i x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.comp_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [hL, hR]
  induction LinearMap.rTensor (C D) (GrCooperad.decomp (R := R) (C := C) i)
      (GrCooperad.decomp (R := R) (C := C) (Sum.inr j) w) using TensorProduct.induction_on with
  | zero => simp
  | tmul t z =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, mu_tmul,
        TensorProduct.assoc_tmul, GrOperad.comp_assoc_seq, GrSpecies.tw_tw]
    | add a b ha hb => simp only [map_add, TensorProduct.add_tmul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **Sequential associativity** of the convolution operad. -/
lemma compC_assoc_seq (i : A) (j : B) (f : ConvOp R C P A) (g : ConvOp R C P B)
    (h : ConvOp R C P D) :
    mapC (seqEquiv i j D) (compC (Sum.inr j) (compC i f g) h) = compC i f (compC j g h) := by
  rw [← parC_add g, ← parC_add h]
  simp only [map_add, LinearMap.add_apply]
  rw [compC_assoc_seq_hom i j f (isParC_parC false g) (isParC_parC false h),
    compC_assoc_seq_hom i j f (isParC_parC false g) (isParC_parC true h),
    compC_assoc_seq_hom i j f (isParC_parC true g) (isParC_parC false h),
    compC_assoc_seq_hom i j f (isParC_parC true g) (isParC_parC true h)]

omit [GrOperad R P] in
lemma par_of_hom_C {c d : Bool} {z : C A} (h : GrSpecies.par (R := R) d z = z) :
    GrSpecies.par (R := R) c z = if c = d then z else 0 := by
  rw [← h, GrSpecies.par_par, h]

omit [GrOperad R P] in
/-- The super swap of homogeneous tensors. -/
lemma sswapLast_hom (x : C A) {y : C B} {z : C D} {sy sz : Bool}
    (hy : GrSpecies.par (R := R) sy y = y) (hz : GrSpecies.par (R := R) sz z = z) :
    sswapLast R (fun c => GrSpecies.par (R := R) (V := C) (A := B) c)
        (fun c => GrSpecies.par (R := R) (V := C) (A := D) c) ((x ⊗ₜ y) ⊗ₜ z)
      = σ R (sy && sz) • ((x ⊗ₜ z) ⊗ₜ y) := by
  rw [sswapLast_tmul]
  simp only [Fintype.sum_bool, par_of_hom_C hy, par_of_hom_C hz]
  cases sy <;> cases sz <;> simp

/-- **Parallel associativity** of the convolution operad, up to the Koszul sign. -/
lemma compC_assoc_par {i k : A} (hik : i ≠ k) (f : ConvOp R C P A) {q r : Bool}
    {g : ConvOp R C P B} {h : ConvOp R C P D} (hg : parC q g = g) (hh : parC r h = h) :
    mapC (parEquiv hik B D) (compC (Sum.inl ⟨k, Ne.symm hik⟩) (compC i f g) h)
      = σ R (q && r) • compC (Sum.inl ⟨i, hik⟩) (compC k f h) g := by
  have hg' := parC_eq_self_iff.1 hg
  have hh' := parC_eq_self_iff.1 hh
  ext x
  set w := SymSpecies.map (R := R) (V := C) (parEquiv hik B D).symm x
  have hco := LinearMap.congr_fun
    (GrCooperad.decomp_assoc_par (R := R) (C := C) (B := B) (D := D) hik) x
  simp only [LinearMap.comp_apply] at hco
  have hL : toLin (mapC (parEquiv hik B D) (compC (Sum.inl ⟨k, Ne.symm hik⟩) (compC i f g) h)) x
      = GrOperad.map (R := R) (parEquiv hik B D) (mu (Sum.inl ⟨k, Ne.symm hik⟩)
          (TensorProduct.map (mu i ∘ₗ TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) q)
            (toLin g) ∘ₗ TensorProduct.map (GrSpecies.tw (R := R) r) (GrSpecies.tw (R := R) r))
            (toLin h)
            (LinearMap.rTensor (C D) (GrCooperad.decomp (R := R) (C := C) i)
              (GrCooperad.decomp (R := R) (C := C)
              (Sum.inl ⟨k, Ne.symm hik⟩ : Without A i ⊕ B) w)))) := by
    rw [mapC_apply, toLin_compC, kap_hom _ hh', toLin_compC, kap_hom f hg']
    simp only [LinearMap.comp_apply]
    congr 2
    induction GrCooperad.decomp (R := R) (C := C)
              (Sum.inl ⟨k, Ne.symm hik⟩ : Without A i ⊕ B) w
      using TensorProduct.induction_on with
    | zero => simp
    | tmul u z =>
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.rTensor_tmul,
        decomp_tw_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hR : toLin (σ R (q && r) • compC (Sum.inl ⟨i, hik⟩) (compC k f h) g) x
      = σ R (q && r) • mu (Sum.inl ⟨i, hik⟩)
          (TensorProduct.map (mu k ∘ₗ TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) r)
            (toLin h) ∘ₗ TensorProduct.map (GrSpecies.tw (R := R) q) (GrSpecies.tw (R := R) q))
            (toLin g)
            (LinearMap.rTensor (C B) (GrCooperad.decomp (R := R) (C := C) k)
              (GrCooperad.decomp (R := R) (C := C)
              (Sum.inl ⟨i, hik⟩ : Without A k ⊕ D) x))) := by
    rw [toLin_smul, LinearMap.smul_apply, toLin_compC, kap_hom _ hg', toLin_compC,
      kap_hom f hh']
    simp only [LinearMap.comp_apply]
    congr 2
    induction GrCooperad.decomp (R := R) (C := C)
              (Sum.inl ⟨i, hik⟩ : Without A k ⊕ D) x
      using TensorProduct.induction_on with
    | zero => simp
    | tmul u z =>
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.rTensor_tmul,
        decomp_tw_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [hL, hR, hco]
  have H : GrOperad.map (R := R) (parEquiv hik B D) ∘ₗ
      mu (Sum.inl ⟨k, Ne.symm hik⟩ : Without A i ⊕ B) ∘ₗ
      TensorProduct.map (mu i ∘ₗ TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) q)
        (toLin g) ∘ₗ TensorProduct.map (GrSpecies.tw (R := R) r) (GrSpecies.tw (R := R) r))
        (toLin h)
      = σ R (q && r) • (mu (Sum.inl ⟨i, hik⟩ : Without A k ⊕ D) ∘ₗ
          TensorProduct.map (mu k ∘ₗ TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) r)
            (toLin h) ∘ₗ TensorProduct.map (GrSpecies.tw (R := R) q) (GrSpecies.tw (R := R) q))
            (toLin g) ∘ₗ sswapLast R (fun c => GrSpecies.par (R := R) (V := C) (A := B) c)
              (fun c => GrSpecies.par (R := R) (V := C) (A := D) c)) := by
    apply TensorProduct.ext_threefold
    intro a b d
    have key : ∀ (b' : C B) (d' : C D) (sb sd : Bool), GrSpecies.par (R := R) sb b' = b' →
        GrSpecies.par (R := R) sd d' = d' →
        (GrOperad.map (R := R) (parEquiv hik B D) ∘ₗ
          mu (Sum.inl ⟨k, Ne.symm hik⟩ : Without A i ⊕ B) ∘ₗ
          TensorProduct.map (mu i ∘ₗ TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) q)
            (toLin g) ∘ₗ TensorProduct.map (GrSpecies.tw (R := R) r)
              (GrSpecies.tw (R := R) r)) (toLin h)) ((a ⊗ₜ b') ⊗ₜ d')
        = (σ R (q && r) • (mu (Sum.inl ⟨i, hik⟩ : Without A k ⊕ D) ∘ₗ
            TensorProduct.map (mu k ∘ₗ TensorProduct.map (toLin f ∘ₗ GrSpecies.tw (R := R) r)
              (toLin h) ∘ₗ TensorProduct.map (GrSpecies.tw (R := R) q)
                (GrSpecies.tw (R := R) q)) (toLin g) ∘ₗ
              sswapLast R (fun c => GrSpecies.par (R := R) (V := C) (A := B) c)
                (fun c => GrSpecies.par (R := R) (V := C) (A := D) c))) ((a ⊗ₜ b') ⊗ₜ d') := by
      intro b' d' sb sd hb hd
      have hgb : GrOperad.par (R := R) (xor sb q) (toLin g b') = toLin g b' := by
        rw [← hg' sb b', hb]
      have hhd : GrOperad.par (R := R) (xor sd r) (toLin h d') = toLin h d' := by
        rw [← hh' sd d', hd]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, TensorProduct.map_tmul, mu_tmul,
        sswapLast_hom a hb hd, map_smul, GrSpecies.tw_hom r hb, GrSpecies.tw_hom q hd,
        LinearMap.smul_apply, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
      rw [GrOperad.comp_assoc_par hik _ hgb hhd, GrSpecies.tw_tw, GrSpecies.tw_tw,
        Bool.xor_comm r q, smul_smul, smul_smul, smul_smul]
      congr 1
      cases sb <;> cases sd <;> cases q <;> cases r <;> simp
    rw [← GrSpecies.par_add (R := R) b, ← GrSpecies.par_add (R := R) d]
    simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add]
    rw [key _ _ _ _ (GrSpecies.par_par_self _ _) (GrSpecies.par_par_self _ _),
      key _ _ _ _ (GrSpecies.par_par_self _ _) (GrSpecies.par_par_self _ _),
      key _ _ _ _ (GrSpecies.par_par_self _ _) (GrSpecies.par_par_self _ _),
      key _ _ _ _ (GrSpecies.par_par_self _ _) (GrSpecies.par_par_self _ _)]
  exact LinearMap.congr_fun H _

/-! ### The convolution operad -/

/-- **The convolution operad is a graded operad.** -/
noncomputable instance instGrOperad : GrOperad R (ConvOp R C P) where
  par b := parC b
  par_add := parC_add
  par_par := parC_parC
  map σ' := mapC σ'
  map_refl := mapC_refl
  map_trans := mapC_trans
  map_par := mapC_parC
  one := oneC R C P
  par_one := parC_oneC
  comp i := compC i
  comp_par := parC_compC
  map_comp := mapC_compC
  comp_one := compC_oneC
  one_comp := oneC_compC
  comp_assoc_seq := compC_assoc_seq
  comp_assoc_par hik f _ _ _ _ hy hz := compC_assoc_par hik f hy hz

lemma par_def (b : Bool) (f : ConvOp R C P A) : GrOperad.par (R := R) b f = parC b f := rfl

lemma map_def (σ' : A ≃ B) (f : ConvOp R C P A) : GrOperad.map (R := R) σ' f = mapC σ' f := rfl

lemma comp_def (i : A) (f : ConvOp R C P A) (g : ConvOp R C P B) :
    GrOperad.comp (R := R) i f g = compC i f g := rfl

lemma one_def : (GrOperad.one (R := R) : ConvOp R C P Unit) = oneC R C P := rfl

/-- The sign twist of the convolution operad: `(tw e f)(x) = tw e (f (tw e x))`. -/
lemma tw_apply (e : Bool) (f : ConvOp R C P A) (y : C A) :
    toLin (GrOperad.tw (R := R) e f) y
      = GrOperad.tw (R := R) e (toLin f (GrSpecies.tw (R := R) e y)) := by
  rw [GrOperad.tw_apply, par_def, par_def, toLin_add, toLin_smul, LinearMap.add_apply,
    LinearMap.smul_apply, parC_apply, parC_apply, GrSpecies.tw_apply, map_add, map_smul]
  simp only [Fintype.sum_bool, GrOperad.tw_apply, map_add, map_smul]
  cases e <;> simp <;> abel

/-! ### Composing with morphisms and derivations -/

variable {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [GrOperad R P']

/-- Composing with a linear map `P A → P' A`. -/
def postL (φ : P A →ₗ[R] P' A) : ConvOp R C P A →ₗ[R] ConvOp R C P' A where
  toFun f := of (φ ∘ₗ toLin f)
  map_add' f g := by
    simp only [toLin_add, LinearMap.comp_add]
    rfl
  map_smul' a f := by
    simp only [toLin_smul, LinearMap.comp_smul]
    rfl

omit [GrCooperad R C] [GrOperad R P] [GrOperad R P'] in
@[simp] lemma toLin_postL (φ : P A →ₗ[R] P' A) (f : ConvOp R C P A) :
    toLin (postL φ f) = φ ∘ₗ toLin f := rfl

/-- **Composing with a morphism of graded operads is a morphism of convolution operads.** -/
noncomputable def postHom (φ : GrOperadHom R P P') :
    GrOperadHom R (ConvOp R C P) (ConvOp R C P') where
  app A _ _ := postL (φ.app A)
  app_par b f := by
    ext x
    simp only [par_def, toLin_postL, LinearMap.comp_apply, parC_apply, map_sum, φ.app_par]
  app_map σ' f := by
    ext x
    simp only [map_def, toLin_postL, LinearMap.comp_apply, mapC_apply, φ.app_map]
  app_one := by
    ext x
    simp only [one_def, toLin_postL, LinearMap.comp_apply, oneC_apply, map_smul, φ.app_one]
  app_comp i f g := by
    ext x
    simp only [comp_def, toLin_postL, LinearMap.comp_apply, toLin_compC]
    induction GrCooperad.decomp (R := R) (C := C) i x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [kap, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
        LinearMap.comp_apply, mu_tmul, φ.app_comp]
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      simp only [parC_apply, toLin_postL, LinearMap.comp_apply, map_sum, φ.app_par]
    | add a b ha hb => simp only [map_add, ha, hb]

@[simp] lemma postHom_app (φ : GrOperadHom R P P') (f : ConvOp R C P A) :
    toLin ((postHom φ).app A f) = φ.app A ∘ₗ toLin f := rfl

/-- **Composing with a derivation of `P` is a derivation of the convolution operad.** -/
noncomputable def postDer {e : Bool} (D : GrDer (GrOperadHom.id R P) e) :
    GrDer (GrOperadHom.id R (ConvOp R C P)) e where
  app A _ _ := postL (D.app A)
  app_par c f := by
    ext x
    simp only [par_def, toLin_postL, LinearMap.comp_apply, parC_apply, map_sum, D.app_par]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Bool.xor_assoc, Bool.xor_comm c e, ← Bool.xor_assoc]
  app_map σ' f := by
    ext x
    simp only [map_def, toLin_postL, LinearMap.comp_apply, mapC_apply, D.app_map]
  app_one := by
    ext x
    simp only [one_def, toLin_postL, LinearMap.comp_apply, oneC_apply, map_smul, D.app_one,
      smul_zero, toLin_zero, LinearMap.zero_apply]
  app_comp {A₁ B₁} _ _ _ _ i f g := by
    ext x
    simp only [comp_def, toLin_postL, LinearMap.comp_apply, toLin_compC, toLin_add,
      LinearMap.add_apply, GrOperadHom.id_app]
    induction GrCooperad.decomp (R := R) (C := C) i x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hp : ∀ q : Bool, parC (C := C) q (postL (D.app B₁) g)
          = postL (C := C) (D.app B₁) (parC (xor q e) g) :=
        fun q => by
          ext y
          simp only [toLin_postL, LinearMap.comp_apply, parC_apply, map_sum, D.app_par]
          refine Finset.sum_congr rfl fun d _ => ?_
          congr 1
          cases d <;> cases q <;> cases e <;> rfl
      simp only [kap, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
        LinearMap.comp_apply, mu_tmul, D.app_comp, GrOperadHom.id_app, Finset.sum_add_distrib,
        hp, toLin_postL, tw_apply, GrSpecies.tw_tw]
      congr 1
      simp only [Fintype.sum_bool]
      cases e <;> simp [add_comm]
    | add a b ha hb =>
      simp only [map_add, ha, hb]
      abel

@[simp] lemma postDer_app {e : Bool} (D : GrDer (GrOperadHom.id R P) e) (f : ConvOp R C P A) :
    toLin ((postDer (C := C) D).app A f) = D.app A ∘ₗ toLin f := rfl

lemma appDer_postDer_apply {e : Bool} (D : GrDer (GrOperadHom.id R P) e)
    (q : GrOperad.Inv R (ConvOp R C P)) (x : C A) :
    toLin ((GrOperad.Inv.appDer (postDer (C := C) D) q).1 A) x = D.app A (toLin (q.1 A) x) :=
  rfl

lemma appHom_postHom_apply (φ : GrOperadHom R P P') (q : GrOperad.Inv R (ConvOp R C P))
    (x : C A) :
    toLin ((GrOperad.Inv.appHom (postHom (C := C) φ) q).1 A) x = φ.app A (toLin (q.1 A) x) :=
  rfl

end ConvOp

end Operad
