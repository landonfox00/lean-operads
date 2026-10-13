/-
# Weighted set operads: the associated graded and the Rees family

A **weight** on a set operad `S` (`SetOperadWeight`) is invariant under relabelling, zero on the
unit and subadditive under composition; it filters the linearization (`weightFiltration`). The
**defect** of a composite is the weight it drops, `w s + w t - w (s ∘ᵢ t)`, and it is additive
along both kinds of iterated composite (`defect_assoc_seq`, `defect_assoc_par`).

For every `h : R` this gives the **twisted linearization** `TwLin R W h`: the free modules
`S A →₀ R`, with composition

  `s ∘ᵢ t = h ^ (w s + w t - w (s ∘ᵢ t)) • (s ∘ᵢ t)`.

It is filtered by the same weight (`TwLin.filtration`), and its three instances are

* `h = 1`: the linearization (`TwLin.isoLin : TwLin R W 1 ≅ Lin R S`);
* `h = 0`: **the associated graded** `Gr R W` of the weight filtration, in which the composites that
  drop weight vanish and the others are the composites of `S` (`Gr.comp_single`);
* `h = X` over `R[X]`: **the Rees family**. In the basis `s ↦ Xʷ⁽ˢ⁾ s` of the classical Rees
  module `⊕ₚ Fₚ Xᵖ` the composition is exactly this one. Its specialization at `X = c`
  (`TwLin.specialize`) is a morphism of the underlying set operads onto `TwLin R W c`,
  semilinear along `Polynomial.eval c`, whose kernel is `(X - c)` times the family
  (`TwLin.specialize_eq_zero_iff`): the fiber at `c = 1` is the linearization and the fiber at
  `c = 0` is the associated graded.

Morphisms out of a twisted linearization are built from their values on the basis
(`TwLin.liftHom`). On the associated graded, `s ↦ (-1)^{w s} s` is an involutive automorphism
(`Gr.sign`), and the weight-zero coefficient is a morphism to `Com` (`Gr.evZero`).
-/
import Operad.Filtration
import Operad.SymIso
import Operad.SetBinary
import Mathlib.Algebra.Polynomial.Div

universe u v w

namespace Operad

open Sym

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]

variable (S) in
/-- **A weight on a set operad**: invariant under relabelling, zero on the unit, subadditive under
composition. -/
structure SetOperadWeight where
  /-- The weight of an operation. -/
  w : ∀ (A : Type) [Fintype A] [DecidableEq A], S A → ℕ
  w_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (s : S A) : w B (SetOperad.map e s) = w A s
  w_one : w Unit SetOperad.one = 0
  w_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) (s : S A)
    (t : S B) : w _ (SetOperad.comp i s t) ≤ w A s + w B t

namespace SetOperadWeight

variable (W : SetOperadWeight S)
  {A A' B B' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D]

/-- **The filtration by the weight** of the linearization. -/
noncomputable def filtration (R : Type u) [CommRing R] : SymOperadFiltration R (Lin R S) :=
  weightFiltration R W.w W.w_map W.w_one W.w_comp

/-- **The defect of a composite**: the weight it drops. -/
def defect (i : A) (s : S A) (t : S B) : ℕ := W.w A s + W.w B t - W.w _ (SetOperad.comp i s t)

lemma w_comp_add_defect (i : A) (s : S A) (t : S B) :
    W.w _ (SetOperad.comp i s t) + W.defect i s t = W.w A s + W.w B t := by
  have := W.w_comp i s t
  unfold defect
  omega

lemma defect_eq_zero_iff (i : A) (s : S A) (t : S B) :
    W.defect i s t = 0 ↔ W.w _ (SetOperad.comp i s t) = W.w A s + W.w B t := by
  have := W.w_comp i s t
  unfold defect
  omega

omit [Fintype D] [DecidableEq D] in
lemma defect_map (σ : A ≃ A') (τ : B ≃ B') (i : A) (s : S A) (t : S B) :
    W.defect (σ i) (SetOperad.map σ s) (SetOperad.map τ t) = W.defect i s t := by
  unfold defect
  rw [← SetOperad.map_comp, W.w_map, W.w_map, W.w_map]

omit [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D] in
lemma defect_one_right (i : A) (s : S A) : W.defect i s SetOperad.one = 0 := by
  have h := congrArg (W.w A) (SetOperad.comp_one (S := S) i s)
  rw [W.w_map] at h
  unfold defect
  rw [h, W.w_one]
  omega

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
lemma defect_one_left (t : S B) : W.defect () SetOperad.one t = 0 := by
  have h := congrArg (W.w B) (SetOperad.one_comp (S := S) t)
  rw [W.w_map] at h
  unfold defect
  rw [h, W.w_one]
  omega

/-- **The defect is additive along sequential composites.** -/
lemma defect_assoc_seq (i : A) (j : B) (s : S A) (t : S B) (u : S D) :
    W.defect i s t + W.defect (Sum.inr j) (SetOperad.comp i s t) u
      = W.defect j t u + W.defect i s (SetOperad.comp j t u) := by
  have h := congrArg (W.w _) (SetOperad.comp_assoc_seq (S := S) i j s t u)
  rw [W.w_map] at h
  have h1 := W.w_comp i s t
  have h2 := W.w_comp (Sum.inr j) (SetOperad.comp i s t) u
  have h3 := W.w_comp j t u
  have h4 := W.w_comp i s (SetOperad.comp j t u)
  unfold defect
  omega

/-- **The defect is additive along parallel composites.** -/
lemma defect_assoc_par {i k : A} (hik : i ≠ k) (s : S A) (t : S B) (u : S D) :
    W.defect i s t + W.defect (Sum.inl ⟨k, Ne.symm hik⟩) (SetOperad.comp i s t) u
      = W.defect k s u + W.defect (Sum.inl ⟨i, hik⟩) (SetOperad.comp k s u) t := by
  have h := congrArg (W.w _) (SetOperad.comp_assoc_par (S := S) hik s t u)
  rw [W.w_map] at h
  have h1 := W.w_comp i s t
  have h2 := W.w_comp (Sum.inl ⟨k, Ne.symm hik⟩) (SetOperad.comp i s t) u
  have h3 := W.w_comp k s u
  have h4 := W.w_comp (Sum.inl ⟨i, hik⟩) (SetOperad.comp k s u) t
  unfold defect
  omega

end SetOperadWeight

/-! ## The twisted linearization -/

variable (R : Type u) [CommRing R]

/-- **The twisted linearization** of a weighted set operad: the free modules `S A →₀ R`, with the
composite of two operations scaled by `h` to the power of the weight it drops. -/
@[nolint unusedArguments]
def TwLin (_W : SetOperadWeight S) (_h : R) :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type (max u v) :=
  fun A _ _ => S A →₀ R

namespace TwLin

variable {R} (W : SetOperadWeight S) (h : R)
  {A A' B B' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D]

noncomputable instance instAddCommGroup : AddCommGroup (TwLin R W h A) :=
  inferInstanceAs (AddCommGroup (S A →₀ R))

noncomputable instance instModule : Module R (TwLin R W h A) :=
  inferInstanceAs (Module R (S A →₀ R))

/-- The basis element of an operation, with a coefficient. -/
noncomputable def single (s : S A) (r : R) : TwLin R W h A := Finsupp.single s r

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype D] [DecidableEq D] in
@[simp] lemma single_zero (s : S A) : single W h s 0 = 0 := Finsupp.single_zero s

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype D] [DecidableEq D] in
lemma single_add (s : S A) (r r' : R) :
    single W h s (r + r') = single W h s r + single W h s r' := Finsupp.single_add s r r'

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype D] [DecidableEq D] in
@[simp] lemma smul_single (a : R) (s : S A) (r : R) :
    a • single W h s r = single W h s (a * r) := Finsupp.smul_single a s r

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype D] [DecidableEq D] in
/-- Induction on the basis. -/
@[elab_as_elim]
lemma induction {motive : TwLin R W h A → Prop} (x : TwLin R W h A) (h0 : motive 0)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsingle : ∀ s r, motive (single W h s r)) : motive x :=
  Finsupp.induction_linear (motive := motive) x h0 hadd hsingle

/-- Relabelling, extended linearly. -/
noncomputable def mapL (e : A ≃ B) : TwLin R W h A →ₗ[R] TwLin R W h B := Lin.mapL R e

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D] in
@[simp] lemma mapL_single (e : A ≃ B) (s : S A) (r : R) :
    mapL W h e (single W h s r) = single W h (SetOperad.map e s) r :=
  Lin.mapL_single e s r

/-- Composition on the free modules, twisted by the defect. -/
noncomputable def compF (i : A) :
    (S A →₀ R) →ₗ[R] (S B →₀ R) →ₗ[R] (S (Without A i ⊕ B) →₀ R) :=
  Finsupp.lift ((S B →₀ R) →ₗ[R] (S (Without A i ⊕ B) →₀ R)) R (S A) fun s =>
    Finsupp.lift (S (Without A i ⊕ B) →₀ R) R (S B) fun t =>
      Finsupp.single (SetOperad.comp i s t) (h ^ W.defect i s t)

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D] in
lemma compF_single (i : A) (s : S A) (t : S B) (r r' : R) :
    compF W h i (Finsupp.single s r) (Finsupp.single t r')
      = Finsupp.single (SetOperad.comp i s t) (h ^ W.defect i s t * (r * r')) := by
  simp only [compF, Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul,
    LinearMap.smul_apply, Finsupp.smul_single, smul_eq_mul, zero_mul, Finsupp.single_zero]
  congr 1
  ring

/-- Composition, extended bilinearly and twisted by the defect. -/
noncomputable def compL (i : A) :
    TwLin R W h A →ₗ[R] TwLin R W h B →ₗ[R] TwLin R W h (Without A i ⊕ B) :=
  compF W h i

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D] in
@[simp] lemma compL_single (i : A) (s : S A) (t : S B) (r r' : R) :
    compL W h i (single W h s r) (single W h t r')
      = single W h (SetOperad.comp i s t) (h ^ W.defect i s t * (r * r')) :=
  compF_single W h i s t r r'

/-- The linear map out of a twisted linearization with given values on the basis. -/
noncomputable def lift {M : Type*} [AddCommGroup M] [Module R M] (f : S A → M) :
    TwLin R W h A →ₗ[R] M :=
  Finsupp.lift M R (S A) f

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype D] [DecidableEq D] in
@[simp] lemma lift_single {M : Type*} [AddCommGroup M] [Module R M] (f : S A → M) (s : S A)
    (r : R) : lift W h f (single W h s r) = r • f s := by
  show Finsupp.lift M R (S A) f (Finsupp.single s r) = r • f s
  simp

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype D] [DecidableEq D] in
/-- Two linear maps out of a twisted linearization agree when they agree on the basis. -/
lemma linearMap_ext {M : Type*} [AddCommGroup M] [Module R M] {f g : TwLin R W h A →ₗ[R] M}
    (hfg : ∀ s, f (single W h s 1) = g (single W h s 1)) : f = g :=
  Finsupp.lhom_ext' fun s => LinearMap.ext_ring (hfg s)

end TwLin

open TwLin in
/-- **The twisted linearization is a symmetric operad.** -/
noncomputable instance instSymOperadTwLin (W : SetOperadWeight S) (h : R) :
    SymOperad R (TwLin R W h) where
  map e := mapL W h e
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
  one := single W h SetOperad.one 1
  comp i := compL W h i
  map_comp σ τ i x y := by
    induction x using TwLin.induction with
    | h0 => simp
    | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | hsingle s r =>
      induction y using TwLin.induction with
      | h0 => simp
      | hadd y y' hy hy' => simp only [map_add, hy, hy']
      | hsingle t r' =>
        simp only [compL_single, mapL_single, SetOperad.map_comp, W.defect_map]
  comp_one i x := by
    induction x using TwLin.induction with
    | h0 => simp
    | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | hsingle s r =>
      simp only [compL_single, mapL_single, SetOperad.comp_one, W.defect_one_right, pow_zero,
        one_mul, mul_one]
  one_comp y := by
    induction y using TwLin.induction with
    | h0 => simp
    | hadd y y' hy hy' => simp only [map_add, hy, hy']
    | hsingle t r =>
      simp only [compL_single, mapL_single, SetOperad.one_comp, W.defect_one_left, pow_zero,
        one_mul]
  comp_assoc_seq i j x y z := by
    induction x using TwLin.induction with
    | h0 => simp
    | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | hsingle s r =>
      induction y using TwLin.induction with
      | h0 => simp
      | hadd y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | hsingle t r' =>
        induction z using TwLin.induction with
        | h0 => simp
        | hadd z z' hz hz' => simp only [map_add, hz, hz']
        | hsingle u r'' =>
          simp only [compL_single, mapL_single, SetOperad.comp_assoc_seq]
          congr 1
          have hd := W.defect_assoc_seq i j s t u
          calc h ^ W.defect (Sum.inr j) (SetOperad.comp i s t) u
                * (h ^ W.defect i s t * (r * r') * r'')
              = h ^ (W.defect i s t + W.defect (Sum.inr j) (SetOperad.comp i s t) u)
                * (r * r' * r'') := by ring
            _ = h ^ (W.defect j t u + W.defect i s (SetOperad.comp j t u)) * (r * r' * r'') := by
                rw [hd]
            _ = _ := by ring
  comp_assoc_par hik x y z := by
    induction x using TwLin.induction with
    | h0 => simp
    | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | hsingle s r =>
      induction y using TwLin.induction with
      | h0 => simp
      | hadd y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | hsingle t r' =>
        induction z using TwLin.induction with
        | h0 => simp
        | hadd z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
        | hsingle u r'' =>
          simp only [compL_single, mapL_single, SetOperad.comp_assoc_par]
          congr 1
          have hd := W.defect_assoc_par hik s t u
          calc h ^ W.defect _ (SetOperad.comp _ s t) u * (h ^ W.defect _ s t * (r * r') * r'')
              = h ^ (W.defect _ s t + W.defect (Sum.inl ⟨_, Ne.symm hik⟩) (SetOperad.comp _ s t) u)
                * (r * r' * r'') := by ring
            _ = h ^ (W.defect _ s u + W.defect (Sum.inl ⟨_, hik⟩) (SetOperad.comp _ s u) t)
                * (r * r' * r'') := by rw [hd]
            _ = _ := by ring

namespace TwLin

variable {R} (W : SetOperadWeight S) (h : R)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

@[simp] lemma map_single (e : A ≃ B) (s : S A) (r : R) :
    SymOperad.map (R := R) (P := TwLin R W h) e (single W h s r)
      = single W h (SetOperad.map e s) r :=
  mapL_single W h e s r

lemma one_eq : SymOperad.one R (P := TwLin R W h) = single W h SetOperad.one 1 := rfl

@[simp] lemma comp_single (i : A) (s : S A) (t : S B) (r r' : R) :
    SymOperad.comp (R := R) (P := TwLin R W h) i (single W h s r) (single W h t r')
      = single W h (SetOperad.comp i s t) (h ^ W.defect i s t * (r * r')) :=
  compL_single W h i s t r r'

/-! ### The filtration -/

/-- **The weight filtration of a twisted linearization**: `F p` is spanned by the operations of
weight at most `p`. -/
noncomputable def filtration : SymOperadFiltration R (TwLin R W h) where
  F p A _ _ := Finsupp.supported R R {s | W.w A s ≤ p}
  mono hpq A _ _ := Finsupp.supported_mono fun s (hs : _ ≤ _) => le_trans hs hpq
  map_mem := (W.filtration R).map_mem
  one_mem := (W.filtration R).one_mem
  comp_mem := by
    intro p q A B _ _ _ _ i x y hx hy
    rw [Finsupp.supported_eq_span_single] at hx hy
    induction hx using Submodule.span_induction with
    | mem s hs =>
      induction hy using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨s, hs, rfl⟩ := hs
        obtain ⟨t, ht, rfl⟩ := ht
        show compL W h i (single W h s 1) (single W h t 1) ∈ _
        rw [compL_single]
        exact Finsupp.single_mem_supported R _
          (le_trans (W.w_comp i s t) (Nat.add_le_add hs ht))
      | zero => simp
      | add y y' _ _ hy hy' => simpa only [map_add] using Submodule.add_mem _ hy hy'
      | smul r y _ hy => simpa only [map_smul] using Submodule.smul_mem _ r hy
    | zero => simp
    | add x x' _ _ hx hx' =>
      simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ hx hx'
    | smul r x _ hx =>
      simpa only [map_smul, LinearMap.smul_apply] using Submodule.smul_mem _ r hx
  exhaustive := (W.filtration R).exhaustive

/-! ### Morphisms out of a twisted linearization -/

variable {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **A morphism out of a twisted linearization, from its values on the basis**: a family of
functions commuting with relabelling and the unit, and with composition up to the twist. -/
noncomputable def liftHom (f : ∀ (A : Type) [Fintype A] [DecidableEq A], S A → Q A)
    (hmap : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (s : S A), f B (SetOperad.map e s) = SymOperad.map (R := R) e (f A s))
    (hone : f Unit SetOperad.one = SymOperad.one R)
    (hcomp : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (s : S A) (t : S B),
      h ^ W.defect i s t • f _ (SetOperad.comp i s t) = SymOperad.comp (R := R) i (f A s) (f B t)) :
    SymOperadHom R (TwLin R W h) Q where
  app A _ _ := lift W h (f A)
  app_map e x := by
    induction x using TwLin.induction with
    | h0 => simp
    | hadd x x' hx hx' => simp only [map_add, hx, hx']
    | hsingle s r => rw [map_single, lift_single, lift_single, map_smul, hmap]
  app_one := by rw [one_eq, lift_single, one_smul, hone]
  app_comp i x y := by
    induction x using TwLin.induction with
    | h0 => simp
    | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | hsingle s r =>
      induction y using TwLin.induction with
      | h0 => simp
      | hadd y y' hy hy' => simp only [map_add, hy, hy']
      | hsingle t r' =>
        rw [comp_single, lift_single, lift_single, lift_single]
        simp only [map_smul, LinearMap.smul_apply]
        rw [← hcomp, smul_smul, smul_smul]
        congr 1
        ring

omit [Fintype B] [DecidableEq B] in
@[simp] lemma liftHom_single (f : ∀ (A : Type) [Fintype A] [DecidableEq A], S A → Q A) (hmap)
    (hone) (hcomp) (s : S A) (r : R) :
    (liftHom W h f hmap hone hcomp).app A (single W h s r) = r • f A s :=
  lift_single W h (f A) s r

/-! ### The fiber at `h = 1`: the linearization -/

variable (R) in
/-- The identity on bases, `TwLin R W 1 → Lin R S`. -/
noncomputable def toLin : SymOperadHom R (TwLin R W 1) (Lin R S) :=
  liftHom W 1 (fun _ _ _ s => Finsupp.single s 1) (fun e s => (Lin.mapL_single e s 1).symm) rfl
    (fun i s t => by
      rw [one_pow, one_smul]
      show Finsupp.single (SetOperad.comp i s t) 1
        = Lin.compL R i (Finsupp.single s (1 : R)) (Finsupp.single t 1)
      rw [Lin.compL_single, mul_one])

omit [Fintype B] [DecidableEq B] in
lemma toLin_app (x : TwLin R W 1 A) : (toLin R W).app A x = x := by
  induction x using TwLin.induction with
  | h0 => rw [map_zero]; rfl
  | hadd x y hx hy => rw [map_add, hx, hy]; rfl
  | hsingle s r =>
    rw [toLin, liftHom_single]
    exact (Finsupp.smul_single r s (1 : R)).trans (by rw [smul_eq_mul, mul_one]; rfl)

variable (R) in
/-- **The fiber at `h = 1` is the linearization.** -/
noncomputable def isoLin : SymOperadIso R (TwLin R W 1) (Lin R S) :=
  SymOperadIso.ofBijective (toLin R W) fun A _ _ => by
    have : ⇑((toLin R W).app A) = fun x => x := funext (toLin_app W)
    rw [this]
    exact Function.bijective_id

end TwLin

/-! ## The associated graded -/

/-- **The associated graded of the weight filtration**: the twisted linearization at `h = 0`, in
which the composites that drop weight vanish. -/
abbrev Gr (W : SetOperadWeight S) : (A : Type) → [Fintype A] → [DecidableEq A] → Type (max u v) :=
  TwLin R W (0 : R)

namespace Gr

variable {R} (W : SetOperadWeight S)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **Composition in the associated graded**: the composite in `S` when no weight is dropped,
and zero otherwise. -/
lemma comp_single (i : A) (s : S A) (t : S B) (r r' : R) :
    SymOperad.comp (R := R) (P := Gr R W) i (TwLin.single W 0 s r) (TwLin.single W 0 t r')
      = if W.defect i s t = 0 then TwLin.single W 0 (SetOperad.comp i s t) (r * r') else 0 := by
  rw [TwLin.comp_single]
  split_ifs with hd
  · rw [hd, pow_zero, one_mul]
  · rw [zero_pow hd, zero_mul, TwLin.single_zero]

/-- **The sign automorphism** of the associated graded, `s ↦ (-1)^{w s} s`. -/
noncomputable def sign : SymOperadHom R (Gr R W) (Gr R W) :=
  TwLin.liftHom W 0 (fun A _ _ s => TwLin.single W 0 s ((-1) ^ W.w A s))
    (fun e s => by dsimp only; rw [TwLin.map_single, W.w_map])
    (by dsimp only; rw [W.w_one, pow_zero]; rfl)
    (fun i s t => by
      dsimp only
      rw [comp_single]
      split_ifs with hd
      · have hw := (W.defect_eq_zero_iff i s t).1 hd
        rw [hd, pow_zero, one_smul, hw, pow_add]
      · rw [zero_pow hd, zero_smul])

@[simp] lemma sign_single (s : S A) (r : R) :
    (sign W).app A (TwLin.single W 0 s r) = TwLin.single W 0 s ((-1) ^ W.w A s * r) := by
  rw [sign, TwLin.liftHom_single, TwLin.smul_single, mul_comm]

/-- **The sign automorphism is an involution.** -/
theorem sign_comp_sign : (sign W).comp (sign W) = SymOperadHom.id (R := R) := by
  refine SymOperadHom.ext fun A _ _ x => ?_
  induction x using TwLin.induction with
  | h0 => simp
  | hadd x x' hx hx' => simp only [map_add, hx, hx']
  | hsingle s r =>
    rw [SymOperadHom.comp_app, sign_single, sign_single, ← mul_assoc, ← pow_add, ← two_mul,
      pow_mul, neg_one_sq, one_pow, one_mul]
    rfl

/-- **The weight-zero coefficient**, `Gr R W → Com R`: an operation counts `1` when it has weight
zero and `0` otherwise. -/
noncomputable def evZero : SymOperadHom R (Gr R W) (Com R) :=
  TwLin.liftHom W 0 (fun A _ _ s => if W.w A s = 0 then (1 : R) else 0)
    (fun e s => by dsimp only; rw [W.w_map]; rfl)
    (by dsimp only; rw [if_pos W.w_one]; rfl)
    (fun i s t => by
      show (0 : R) ^ W.defect i s t • (if W.w _ (SetOperad.comp i s t) = 0 then (1 : R) else 0)
        = (if W.w _ s = 0 then (1 : R) else 0) * (if W.w _ t = 0 then (1 : R) else 0)
      have hc := W.w_comp_add_defect i s t
      by_cases hd : W.defect i s t = 0
      · rw [hd, pow_zero, one_smul]
        by_cases hs : W.w _ s = 0
        · by_cases ht : W.w _ t = 0
          · rw [if_pos hs, if_pos ht, if_pos (by omega), mul_one]
          · rw [if_pos hs, if_neg ht, if_neg (by omega), mul_zero]
        · rw [if_neg hs, if_neg (by omega), zero_mul]
      · rw [zero_pow hd, zero_smul]
        by_cases hs : W.w _ s = 0
        · by_cases ht : W.w _ t = 0
          · exact absurd (by omega : W.defect i s t = 0) hd
          · rw [if_neg ht, mul_zero]
        · rw [if_neg hs, zero_mul])

@[simp] lemma evZero_single (s : S A) (r : R) :
    (evZero (R := R) W).app A (TwLin.single W 0 s r) = if W.w A s = 0 then r else 0 := by
  rw [evZero, TwLin.liftHom_single]
  split_ifs
  · exact mul_one r
  · exact mul_zero r

end Gr

/-! ## The Rees family -/

namespace TwLin

open Polynomial

variable {R} (W : SetOperadWeight S) (c : R)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **Specialization of the Rees family at `X = c`**, on each component. -/
noncomputable def specializeL (A : Type) [Fintype A] [DecidableEq A] :
    TwLin R[X] W X A →+ TwLin R W c A :=
  Finsupp.mapRange.addMonoidHom (Polynomial.evalRingHom c).toAddMonoidHom

omit [Fintype B] [DecidableEq B] in
@[simp] lemma specializeL_single (s : S A) (p : R[X]) :
    specializeL W c A (single W X s p) = single W c s (p.eval c) :=
  Finsupp.mapRange_single (hf := (Polynomial.evalRingHom c).toAddMonoidHom.map_zero)

omit [Fintype B] [DecidableEq B] in
lemma specializeL_smul (p : R[X]) (x : TwLin R[X] W X A) :
    specializeL W c A (p • x) = p.eval c • specializeL W c A x := by
  induction x using TwLin.induction with
  | h0 => rw [smul_zero, map_zero, smul_zero]
  | hadd x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
  | hsingle s q =>
    rw [smul_single, specializeL_single, specializeL_single, eval_mul, smul_single]

/-- **Specialization of the Rees family at `X = c`**: a morphism of the underlying set operads
onto the twisted linearization at `c`. -/
noncomputable def specialize :
    SetOperadHom (Und R[X] (TwLin R[X] W X)) (Und R (TwLin R W c)) where
  app A _ _ x := Und.of R (TwLin R W c) (specializeL W c A ((Und.of R[X] (TwLin R[X] W X)).symm x))
  app_map e x := by
    show specializeL W c _ (SymOperad.map (R := R[X]) (P := TwLin R[X] W X) e x)
      = SymOperad.map (R := R) (P := TwLin R W c) e (specializeL W c _ x)
    induction x using TwLin.induction with
    | h0 => simp only [map_zero]
    | hadd x x' hx hx' => simp only [map_add, hx, hx']
    | hsingle s p => rw [map_single, specializeL_single, specializeL_single, map_single]
  app_one := by
    show specializeL W c _ (single W X SetOperad.one 1) = single W c SetOperad.one 1
    rw [specializeL_single, eval_one]
  app_comp i x y := by
    show specializeL W c _ (SymOperad.comp (R := R[X]) (P := TwLin R[X] W X) i x y)
      = SymOperad.comp (R := R) (P := TwLin R W c) i (specializeL W c _ x) (specializeL W c _ y)
    induction x using TwLin.induction with
    | h0 => simp only [map_zero, LinearMap.zero_apply]
    | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | hsingle s p =>
      induction y using TwLin.induction with
      | h0 => simp only [map_zero]
      | hadd y y' hy hy' => simp only [map_add, hy, hy']
      | hsingle t q =>
        rw [comp_single, specializeL_single, specializeL_single, specializeL_single, comp_single,
          eval_mul, eval_pow, eval_X, eval_mul]

omit [SetOperad S] [Fintype B] [DecidableEq B] in
private lemma mapRange_eval_C (x : S A →₀ R) :
    Finsupp.mapRange.addMonoidHom (Polynomial.evalRingHom c).toAddMonoidHom
      (Finsupp.mapRange Polynomial.C Polynomial.C_0 x) = x := by
  ext s
  simp

omit [Fintype B] [DecidableEq B] in
/-- **Specialization is surjective**: constant coefficients lift. -/
lemma specializeL_surjective : Function.Surjective (specializeL W c A) := fun x =>
  ⟨Finsupp.mapRange Polynomial.C Polynomial.C_0 (show S A →₀ R from x),
    mapRange_eval_C c (show S A →₀ R from x)⟩

omit [SetOperad S] [Fintype B] [DecidableEq B] in
private lemma mapRange_eval_eq_zero_iff (x : S A →₀ R[X]) :
    Finsupp.mapRange.addMonoidHom (Polynomial.evalRingHom c).toAddMonoidHom x = 0
      ↔ ∃ y : S A →₀ R[X], x = (X - C c) • y := by
  constructor
  · intro hx
    refine ⟨Finsupp.mapRange (fun p => p /ₘ (X - C c)) (by simp) x, ?_⟩
    refine Finsupp.ext fun s => ?_
    have hs : (x s).IsRoot c := by
      have := DFunLike.congr_fun hx s
      simpa using this
    rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact ((mul_divByMonic_eq_iff_isRoot).2 hs).symm
  · rintro ⟨y, rfl⟩
    refine Finsupp.ext fun s => ?_
    simp

omit [Fintype B] [DecidableEq B] in
/-- **The kernel of specialization at `X = c` is `(X - c)` times the Rees family.** -/
theorem specializeL_eq_zero_iff (x : TwLin R[X] W X A) :
    specializeL W c A x = 0 ↔ ∃ y : TwLin R[X] W X A, x = (X - C c) • y :=
  mapRange_eval_eq_zero_iff c (show S A →₀ R[X] from x)

end TwLin

/-! ## Binary composites in a twisted linearization -/

section TwLinBin

open SetOperad

variable {R : Type u} [CommRing R] (W : SetOperadWeight S) {A B : Type} [Fintype A]
  [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **A binary composite of basis elements** in a twisted linearization: the composite in `S`,
scaled by `h` to the weight lost. -/
lemma twLin_bin_single (h : R) (g : S (Fin 2)) (x : S A) (y : S B) (a b c : R) :
    bin (Und.of R (TwLin R W h) (TwLin.single W h g a))
        (Und.of R (TwLin R W h) (TwLin.single W h x b))
        (Und.of R (TwLin R W h) (TwLin.single W h y c))
      = Und.of R (TwLin R W h) (TwLin.single W h (bin g x y)
          (h ^ W.defect (Sum.inl slotOne) (comp 0 g x) y
            * (h ^ W.defect 0 g x * (a * b) * c))) := by
  show SymOperad.map (R := R) (P := TwLin R W h) (binEquiv A B)
      (SymOperad.comp (R := R) (P := TwLin R W h) (Sum.inl slotOne)
        (SymOperad.comp (R := R) (P := TwLin R W h) (0 : Fin 2) (TwLin.single W h g a)
          (TwLin.single W h x b)) (TwLin.single W h y c)) = _
  rw [TwLin.comp_single, TwLin.comp_single, TwLin.map_single]
  rfl

/-- **A binary composite of basis elements in the associated graded**: the composite in `S` when
no weight is lost, and zero otherwise. -/
lemma gr_bin_single (g : S (Fin 2)) (x : S A) (y : S B) :
    bin (Und.of R (Gr R W) (TwLin.single W 0 g 1)) (Und.of R (Gr R W) (TwLin.single W 0 x 1))
        (Und.of R (Gr R W) (TwLin.single W 0 y 1))
      = Und.of R (Gr R W) (TwLin.single W 0 (bin g x y)
          (if W.w _ (bin g x y) = W.w _ g + W.w _ x + W.w _ y then 1 else 0)) := by
  rw [twLin_bin_single]
  have h1 := W.w_comp_add_defect 0 g x
  have h2 := W.w_comp_add_defect (Sum.inl slotOne) (comp 0 g x) y
  have h3 : W.w _ (bin g x y) = W.w _ (comp (Sum.inl slotOne) (comp 0 g x) y) := W.w_map _ _
  congr 2
  split_ifs with hw
  · have hd1 : W.defect 0 g x = 0 := by omega
    have hd2 : W.defect (Sum.inl slotOne) (comp 0 g x) y = 0 := by omega
    rw [hd1, hd2]
    ring
  · by_cases hd1 : W.defect 0 g x = 0
    · have hd2 : W.defect (Sum.inl slotOne) (comp 0 g x) y ≠ 0 := by omega
      rw [zero_pow hd2, zero_mul]
    · rw [zero_pow hd1]
      ring

end TwLinBin

end Operad
