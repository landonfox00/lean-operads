/-
# Polynomials with coefficients in an operad

For a symmetric operad `P` over `R`, the polynomials `∑ xₚ ħᵖ` with coefficients in `P` form a
symmetric operad `PolyOp R P` over `R[X]`, with `(x ħᵖ) ∘ᵢ (y ħ^q) = (x ∘ᵢ y) ħ^(p + q)`.

* `PolynomialModule.map_smul_of_X`: an `R`-linear map of polynomial modules commuting with `X`
  commutes with every polynomial.
* `PolynomialModule.conv`: the convolution of a bilinear map, and
  `PolynomialModule.convX`, the same as a map bilinear over `R[X]`.
* `PolyOp R P`, its operad structure (`PolyOp.instSymOperad`), and the formulas on monomials
  (`PolyOp.map_single`, `PolyOp.comp_single`).
* **The Rees operad** of a filtered operad (`SymOperadFiltration.rees`,
  `SymOperadFiltration.Rees`): the suboperad of the polynomials `∑ xₚ ħᵖ` with `xₚ` of filtration
  degree at most `p`, an operad over `R[X]`. It is a submodule over `R[X]` because the filtration
  increases, and a suboperad because `F p ∘ᵢ F q ⊆ F (p + q)`.

`Operad.ReesFiber` computes its fibers at `ħ = 1` and `ħ = 0`; `Operad.BaseChange` identifies
`PolyOp R P` with the base change `R[X] ⊗[R] P`.
-/
import Operad.SymSuboperad
import Operad.SymIso
import Mathlib.Algebra.Polynomial.Module.Basic

universe u v w

namespace PolynomialModule

open Polynomial

variable {R : Type u} [CommRing R] {M : Type*} {N : Type*} {L : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]

/-- **An `R`-linear map commuting with `X` commutes with every polynomial.** -/
lemma map_smul_of_X (φ : PolynomialModule R M →ₗ[R] PolynomialModule R N)
    (h : ∀ f, φ ((X : R[X]) • f) = (X : R[X]) • φ f) (p : R[X]) (f : PolynomialModule R M) :
    φ (p • f) = p • φ f := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_smul, map_add, hp, hq, add_smul]
  | monomial n a =>
    induction n generalizing f with
    | zero =>
      rw [Polynomial.monomial_zero_left, Polynomial.C_eq_algebraMap, algebraMap_smul,
        algebraMap_smul]
      exact φ.map_smul a f
    | succ n ih => rw [← Polynomial.monomial_mul_X, mul_smul, ih, h, mul_smul]

/-- **An `R`-linear map commuting with `X`**, as a map linear over `R[X]`. -/
noncomputable def ofCommX (φ : PolynomialModule R M →ₗ[R] PolynomialModule R N)
    (h : ∀ f, φ ((X : R[X]) • f) = (X : R[X]) • φ f) :
    PolynomialModule R M →ₗ[R[X]] PolynomialModule R N where
  toFun := φ
  map_add' := φ.map_add
  map_smul' p f := map_smul_of_X φ h p f

@[simp] lemma ofCommX_apply (φ : PolynomialModule R M →ₗ[R] PolynomialModule R N)
    (h : ∀ f, φ ((X : R[X]) • f) = (X : R[X]) • φ f) (f : PolynomialModule R M) :
    ofCommX φ h f = φ f := rfl

lemma X_smul_single (p : ℕ) (m : M) :
    (X : R[X]) • single R p m = single R (p + 1) m := by
  rw [← Polynomial.monomial_one_one_eq_X, monomial_smul_single, one_smul, add_comm]

/-- **The coefficientwise map** of an `R`-linear map, linear over `R[X]`. -/
noncomputable def lmap (f : M →ₗ[R] N) : PolynomialModule R M →ₗ[R[X]] PolynomialModule R N :=
  ofCommX (map R f) fun g => by
    induction g using induction_linear with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add g g' hg hg' => rw [smul_add, map_add, hg, hg', map_add, smul_add]
    | single p m => rw [X_smul_single, map_single, map_single, X_smul_single]

@[simp] lemma lmap_single (f : M →ₗ[R] N) (p : ℕ) (m : M) :
    lmap f (single R p m) = single R p (f m) :=
  map_single R f p m

/-- **The convolution of a bilinear map**: `(x ħᵖ, y ħ^q) ↦ β x y ħ^(p + q)`. -/
noncomputable def conv (β : M →ₗ[R] N →ₗ[R] L) :
    PolynomialModule R M →ₗ[R] PolynomialModule R N →ₗ[R] PolynomialModule R L :=
  Finsupp.lsum R fun p : ℕ =>
    (Finsupp.lsum R (M := N) (N := PolynomialModule R L) (α := ℕ)).toLinearMap ∘ₗ
      LinearMap.pi fun q : ℕ => β.compr₂ (lsingle R (p + q))

@[simp] lemma conv_single (β : M →ₗ[R] N →ₗ[R] L) (p q : ℕ) (m : M) (n : N) :
    conv β (single R p m) (single R q n) = single R (p + q) (β m n) := by
  unfold conv
  rw [show single R p m = Finsupp.single p m from rfl,
    show single R q n = Finsupp.single q n from rfl]
  erw [Finsupp.lsum_single (S := R)]
  exact Finsupp.lsum_single (S := R) _ q n

lemma conv_X_smul_left (β : M →ₗ[R] N →ₗ[R] L) (f : PolynomialModule R M)
    (g : PolynomialModule R N) : conv β ((X : R[X]) • f) g = (X : R[X]) • conv β f g := by
  induction f using induction_linear with
  | zero => rw [smul_zero, map_zero, LinearMap.zero_apply, smul_zero]
  | add f f' hf hf' => rw [smul_add, map_add, LinearMap.add_apply, hf, hf', map_add,
      LinearMap.add_apply, smul_add]
  | single p m =>
    induction g using induction_linear with
    | zero => rw [map_zero, map_zero, smul_zero]
    | add g g' hg hg' => rw [map_add, hg, hg', map_add, smul_add]
    | single q n =>
      rw [X_smul_single, conv_single, conv_single, X_smul_single, add_right_comm]

lemma conv_X_smul_right (β : M →ₗ[R] N →ₗ[R] L) (f : PolynomialModule R M)
    (g : PolynomialModule R N) : conv β f ((X : R[X]) • g) = (X : R[X]) • conv β f g := by
  induction f using induction_linear with
  | zero => rw [map_zero, LinearMap.zero_apply, LinearMap.zero_apply, smul_zero]
  | add f f' hf hf' => rw [map_add, LinearMap.add_apply, hf, hf', LinearMap.add_apply, smul_add]
  | single p m =>
    induction g using induction_linear with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add g g' hg hg' => rw [smul_add, map_add, hg, hg', map_add, smul_add]
    | single q n =>
      rw [X_smul_single, conv_single, conv_single, X_smul_single, add_assoc]

/-- **The convolution of a bilinear map**, bilinear over `R[X]`. -/
noncomputable def convX (β : M →ₗ[R] N →ₗ[R] L) :
    PolynomialModule R M →ₗ[R[X]] PolynomialModule R N →ₗ[R[X]] PolynomialModule R L :=
  LinearMap.mk₂ R[X] (fun f g => conv β f g)
    (fun f f' g => by simp only [map_add, LinearMap.add_apply])
    (fun p f g => map_smul_of_X ((conv β).flip g) (fun f => conv_X_smul_left β f g) p f)
    (fun f g g' => map_add _ g g')
    (fun p f g => map_smul_of_X (conv β f) (fun g => conv_X_smul_right β f g) p g)

@[simp] lemma convX_apply (β : M →ₗ[R] N →ₗ[R] L) (f : PolynomialModule R M)
    (g : PolynomialModule R N) : convX β f g = conv β f g := rfl

lemma convX_single (β : M →ₗ[R] N →ₗ[R] L) (p q : ℕ) (m : M) (n : N) :
    convX β (single R p m) (single R q n) = single R (p + q) (β m n) :=
  conv_single β p q m n

end PolynomialModule

namespace Operad

open Polynomial

variable (R : Type u) [CommRing R]
  (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]

/-- **Polynomials with coefficients in `P`**: `PolyOp R P A` is the module of polynomials
`∑ xₚ ħᵖ` with `xₚ` in `P A`, a module over `R[X]`. -/
@[nolint unusedArguments]
def PolyOp : (A : Type) → [Fintype A] → [DecidableEq A] → Type v :=
  fun A _ _ => PolynomialModule R (P A)

namespace PolyOp

variable {R P}

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (PolyOp R P A) :=
  inferInstanceAs (AddCommGroup (PolynomialModule R (P A)))

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : Module R[X] (PolyOp R P A) :=
  inferInstanceAs (Module R[X] (PolynomialModule R (P A)))

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : Module R (PolyOp R P A) :=
  inferInstanceAs (Module R (PolynomialModule R (P A)))

instance (A : Type) [Fintype A] [DecidableEq A] : IsScalarTower R R[X] (PolyOp R P A) :=
  inferInstanceAs (IsScalarTower R R[X] (PolynomialModule R (P A)))

/-- **The monomial `x ħᵖ`.** -/
noncomputable def single {A : Type} [Fintype A] [DecidableEq A] (p : ℕ) (x : P A) :
    PolyOp R P A :=
  PolynomialModule.single R p x

/-- **Induction on monomials.** -/
theorem induction {A : Type} [Fintype A] [DecidableEq A] {motive : PolyOp R P A → Prop}
    (f : PolyOp R P A) (zero : motive 0) (add : ∀ f g, motive f → motive g → motive (f + g))
    (single : ∀ p x, motive (single p x)) : motive f :=
  PolynomialModule.induction_linear (R := R) f zero add single

variable [SymOperad R P]

/-- **The operad of polynomials with coefficients in `P`**, over `R[X]`: relabelling
coefficientwise, composition by convolution. -/
noncomputable instance instSymOperad : SymOperad R[X] (PolyOp R P) where
  map e := PolynomialModule.lmap (SymOperad.map (R := R) e)
  map_refl x := by
    induction x using induction with
    | zero => rw [map_zero]
    | add f g hf hg => rw [map_add, hf, hg]
    | single p x =>
      exact (PolynomialModule.lmap_single _ p x).trans (by rw [SymOperad.map_refl]; rfl)
  map_trans e f x := by
    induction x using induction with
    | zero => rw [map_zero, map_zero, map_zero]
    | add f g hf hg => rw [map_add, hf, hg, map_add, map_add]
    | single p x =>
      refine (PolynomialModule.lmap_single _ p x).trans ?_
      rw [SymOperad.map_trans]
      exact ((congrArg _ (PolynomialModule.lmap_single _ p x)).trans
        (PolynomialModule.lmap_single _ p _)).symm
  one := single 0 (SymOperad.one R)
  comp i := PolynomialModule.convX (SymOperad.comp (R := R) i)
  map_comp σ τ i x y := by
    induction x using induction with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
    | single p a =>
      induction y using induction with
      | zero => simp only [map_zero]
      | add f g hf hg => simp only [map_add, hf, hg]
      | single q b =>
        refine (congrArg _ (PolynomialModule.convX_single _ p q a b)).trans ?_
        refine (PolynomialModule.lmap_single _ _ _).trans ?_
        rw [SymOperad.map_comp]
        exact ((congrArg₂ (fun u v => PolynomialModule.convX (SymOperad.comp (R := R) (σ i)) u v)
          (PolynomialModule.lmap_single _ p a) (PolynomialModule.lmap_single _ q b)).trans
          (PolynomialModule.convX_single _ p q _ _)).symm
  comp_one i x := by
    induction x using induction with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
    | single p a =>
      refine (congrArg _ (PolynomialModule.convX_single _ p 0 a _)).trans ?_
      refine (PolynomialModule.lmap_single _ _ _).trans ?_
      rw [SymOperad.comp_one, add_zero]
      rfl
  one_comp y := by
    induction y using induction with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg]
    | single q b =>
      refine (congrArg _ (PolynomialModule.convX_single _ 0 q _ b)).trans ?_
      refine (PolynomialModule.lmap_single _ _ _).trans ?_
      rw [SymOperad.one_comp, zero_add]
      rfl
  comp_assoc_seq i j x y z := by
    induction x using induction with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
    | single p a =>
      induction y using induction with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
      | single q b =>
        induction z using induction with
        | zero => simp only [map_zero]
        | add f g hf hg => simp only [map_add, hf, hg]
        | single r c =>
          refine (congrArg _ ((congrArg (fun u => PolynomialModule.convX
            (SymOperad.comp (R := R) (Sum.inr j)) u (single r c))
            (PolynomialModule.convX_single _ p q a b)).trans
            (PolynomialModule.convX_single _ (p + q) r _ c))).trans ?_
          refine (PolynomialModule.lmap_single _ _ _).trans ?_
          rw [SymOperad.comp_assoc_seq, add_assoc]
          exact ((congrArg (fun v => PolynomialModule.convX (SymOperad.comp (R := R) i)
            (single p a) v) (PolynomialModule.convX_single _ q r b c)).trans
            (PolynomialModule.convX_single _ p (q + r) a _)).symm
  comp_assoc_par hik x y z := by
    induction x using induction with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
    | single p a =>
      induction y using induction with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
      | single q b =>
        induction z using induction with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
        | single r c =>
          refine (congrArg _ ((congrArg (fun u => PolynomialModule.convX _ u (single r c))
            (PolynomialModule.convX_single _ p q a b)).trans
            (PolynomialModule.convX_single _ (p + q) r _ c))).trans ?_
          refine (PolynomialModule.lmap_single _ _ _).trans ?_
          rw [SymOperad.comp_assoc_par hik, add_right_comm]
          exact ((congrArg (fun u => PolynomialModule.convX _ u (single q b))
            (PolynomialModule.convX_single _ p r a c)).trans
            (PolynomialModule.convX_single _ (p + r) q _ b)).symm

end PolyOp

/-! ## The Rees operad of a filtration -/

namespace PolyOp

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]

/-- **The coefficient of `ħᵖ`.** -/
def coeff {A : Type} [Fintype A] [DecidableEq A] (f : PolyOp R P A) (p : ℕ) : P A :=
  (show ℕ →₀ P A from f) p

@[simp] lemma coeff_zero {A : Type} [Fintype A] [DecidableEq A] (p : ℕ) :
    coeff (0 : PolyOp R P A) p = 0 := rfl

@[simp] lemma coeff_add {A : Type} [Fintype A] [DecidableEq A] (f g : PolyOp R P A) (p : ℕ) :
    coeff (f + g) p = coeff f p + coeff g p := rfl

lemma coeff_single {A : Type} [Fintype A] [DecidableEq A] (p : ℕ) (x : P A) (n : ℕ) :
    coeff (single (R := R) p x) n = if p = n then x else 0 :=
  PolynomialModule.single_apply R p x n

lemma coeff_monomial_smul {A : Type} [Fintype A] [DecidableEq A] (k : ℕ) (a : R)
    (f : PolyOp R P A) (n : ℕ) :
    coeff (Polynomial.monomial k a • f) n = if k ≤ n then a • coeff f (n - k) else 0 :=
  PolynomialModule.monomial_smul_apply k a f n

@[ext] lemma ext {A : Type} [Fintype A] [DecidableEq A] {f g : PolyOp R P A}
    (h : ∀ p, coeff f p = coeff g p) : f = g :=
  Finsupp.ext h

/-- **A polynomial is the sum of its monomials.** -/
lemma sum_single {A : Type} [Fintype A] [DecidableEq A] (f : PolyOp R P A) :
    ∃ s : Finset ℕ, f = ∑ p ∈ s, single p (coeff f p) :=
  ⟨(show ℕ →₀ P A from f).support, (Finsupp.sum_single (show ℕ →₀ P A from f)).symm⟩

variable [SymOperad R P]

lemma map_single {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (p : ℕ) (x : P A) :
    SymOperad.map (R := R[X]) e (single (R := R) p x) = single p (SymOperad.map (R := R) e x) :=
  PolynomialModule.lmap_single _ p x

lemma comp_single {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) (p q : ℕ) (x : P A) (y : P B) :
    SymOperad.comp (R := R[X]) i (single (R := R) p x) (single q y) =
      single (p + q) (SymOperad.comp (R := R) i x y) :=
  PolynomialModule.convX_single _ p q x y

lemma one_def : (SymOperad.one R[X] : PolyOp R P Unit) = single 0 (SymOperad.one R) := rfl

lemma coeff_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (f : PolyOp R P A) (p : ℕ) :
    coeff (SymOperad.map (R := R[X]) e f) p = SymOperad.map (R := R) e (coeff f p) :=
  Finsupp.mapRange_apply (hf := (SymOperad.map (R := R) e).map_zero)

end PolyOp

namespace SymOperadFiltration

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  (Φ : SymOperadFiltration R P)

/-- **The Rees module** of a filtration on a set of inputs: the polynomials `∑ xₚ ħᵖ` with `xₚ`
of filtration degree at most `p`. -/
def reesSub (A : Type) [Fintype A] [DecidableEq A] : Submodule R[X] (PolyOp R P A) where
  carrier := {f | ∀ p, PolyOp.coeff f p ∈ Φ.F p A}
  add_mem' hf hg p := (Φ.F p A).add_mem (hf p) (hg p)
  zero_mem' p := (Φ.F p A).zero_mem
  smul_mem' c f hf := by
    induction c using Polynomial.induction_on' with
    | add c d hc hd =>
      intro p
      rw [add_smul]
      exact (Φ.F p A).add_mem (hc p) (hd p)
    | monomial k a =>
      intro p
      rw [PolyOp.coeff_monomial_smul]
      split_ifs with h
      · exact (Φ.F p A).smul_mem a (Φ.mono (Nat.sub_le p k) A (hf (p - k)))
      · exact (Φ.F p A).zero_mem

lemma mem_reesSub {A : Type} [Fintype A] [DecidableEq A] {f : PolyOp R P A} :
    f ∈ Φ.reesSub A ↔ ∀ p, PolyOp.coeff f p ∈ Φ.F p A := Iff.rfl

lemma single_mem_reesSub {A : Type} [Fintype A] [DecidableEq A] {p : ℕ} {x : P A}
    (hx : x ∈ Φ.F p A) : PolyOp.single (R := R) p x ∈ Φ.reesSub A := fun n => by
  rw [PolyOp.coeff_single]
  split_ifs with h
  · exact h ▸ hx
  · exact (Φ.F n A).zero_mem

/-- **The Rees operad of a filtration**, as a suboperad of the polynomials with coefficients in
`P`, over `R[X]`. -/
def rees : SymSuboperad R[X] (PolyOp R P) where
  sub A _ _ := Φ.reesSub A
  map_mem e f hf p := by
    rw [PolyOp.coeff_map]
    exact Φ.map_mem e (hf p)
  one_mem := Φ.single_mem_reesSub Φ.one_mem
  comp_mem := by
    intro A B _ _ _ _ i f g hf hg
    obtain ⟨s, hs⟩ := PolyOp.sum_single f
    obtain ⟨t, ht⟩ := PolyOp.sum_single g
    rw [hs, ht]
    simp only [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun _ _ => Submodule.sum_mem _ fun _ _ => ?_
    rw [PolyOp.comp_single]
    exact Φ.single_mem_reesSub (Φ.comp_mem i (hf _) (hg _))

/-- **The Rees operad** `⊕ₚ Fₚ ħᵖ` of a filtered operad, an operad over `R[X]`. -/
abbrev Rees := Φ.rees.Op

end SymOperadFiltration

end Operad
