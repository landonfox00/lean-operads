/-
# Infinitesimal deformations of a symmetric operad

**The deformed operad.** Let `P` be a symmetric operad over a commutative ring `R`, and `ω` a
family of bilinear maps `ωᵢ : P A → P B → P (A ∖ i ⊔ B)` of the shape of partial composition
(a *two-cochain*, `SymCochain`). On the pairs `(x, x')`, read as `x + εx'` with
`ε² = 0`, put

  `(x, x') ∘ᵢ (y, y') = (x ∘ᵢ y, x' ∘ᵢ y + x ∘ᵢ y' + ωᵢ(x, y))`,

with the action of `P` on both components and the unit `(1, 0)` (`Deformed`, `Deformed.comp`).

* **This is a symmetric operad exactly when `ω` is a cocycle** (`SymCochain.IsCocycle`: five
  identities, equivariance, the two unit laws, sequential and parallel associativity):
  `Deformed.instSymOperad`, and conversely `Deformed.isCocycle_of_symOperad`. These are the
  `𝔖`-two-cocycles of Bao, Wang, Xu, Ye, Zhang, and Zhao, the infinitesimal deformations with
  the action and the unit fixed. The trivial deformation `P[ε]` is `ω = 0`
  (`SymCochain.isCocycle_zero`), and the cocycles are closed under linear combinations
  (`SymCochain.IsCocycle.add_smul`). The first component is a morphism `P_ω → P`
  (`Deformed.fstHom`), and `εP` is a square-zero ideal (`Deformed.comp_mk_zero_left`, …).
* **Coboundaries.** An equivariant family `φ` of linear maps (`SymEndo`) has the coboundary
  `(δφ)ᵢ(x, y) = φ(x ∘ᵢ y) - φ(x) ∘ᵢ y - x ∘ᵢ φ(y)` (`SymEndo.coboundary`), a cocycle when
  `φ(1) = 0` (`SymEndo.isCocycle_coboundary`). **A cocycle is a coboundary exactly when there is
  a morphism `P → P_ω` with first component the identity** (`isCoboundary_iff_exists_lift`); the
  morphism is `x ↦ (x, φ x)`.
* **Derivations** (`SymDerivation`): equivariant families with the Leibniz rule, closed under
  sums and scalar multiples (`SymDerivation.add_app`, `SymDerivation.smul_app`). They kill the
  unit (`SymDerivation.app_one`), and **they are the morphisms `P → P[ε]` lifting the identity**
  (`SymDerivation.liftEquiv`; `SymDerivation.eq_of_lift_eq`). The Euler derivation multiplies
  `P(A)` by `|A| - 1` (`SymDerivation.euler`); the inner derivation of `θ ∈ P(1)` is
  `ad_θ(x) = θ ∘ x - Σₐ x ∘ₐ θ` (`SymDerivation.ad`), and `ad_1 = -euler` (`ad_one`), so the
  multiples of the Euler derivation are inner (`smul_euler_eq_ad`).
* **Transport along isomorphisms** (`SymCochain.comap`): if every cocycle of `P` is a coboundary,
  so is every cocycle of an isomorphic operad (`SymOperadIso.forall_isCoboundary`); derivations
  transport likewise (`SymDerivation.transport`), and with them the statement that every
  derivation is a multiple of the Euler derivation (`SymOperadIso.forall_eq_smul_euler`).
-/
import Operad.SymIso
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

universe u v w

namespace Operad

open Sym

/-! ## Two-cochains and the deformed pairs -/

section Pairs

variable (R : Type u) [CommRing R]
  (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]

/-- **A two-cochain**: a family of bilinear maps of the shape of partial composition. -/
abbrev SymCochain :=
  ∀ ⦃A B : Type⦄ [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A),
    P A →ₗ[R] P B →ₗ[R] P (Without A i ⊕ B)

variable {R P}

/-- The zero cochain. -/
protected def SymCochain.zero : SymCochain R P := fun _ => 0

@[simp] lemma SymCochain.zero_apply {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (i : A) (x : P A) (y : P B) :
    SymCochain.zero (R := R) (P := P) i x y = 0 := rfl

/-- **The deformed operad** `P_ω`, as a family of modules: pairs `(x, x') = x + εx'`. -/
@[nolint unusedArguments]
def Deformed (_ω : SymCochain R P) : (A : Type) → [Fintype A] → [DecidableEq A] → Type v :=
  fun A _ _ => P A × P A

namespace Deformed

variable (ω : SymCochain R P)

instance instAddCommGroup (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (Deformed ω A) :=
  inferInstanceAs (AddCommGroup (P A × P A))

instance instModule (A : Type) [Fintype A] [DecidableEq A] : Module R (Deformed ω A) :=
  inferInstanceAs (Module R (P A × P A))

variable {ω} {A : Type} [Fintype A] [DecidableEq A]

/-- An element `x + εx'`. -/
def mk (x x' : P A) : Deformed ω A := (x, x')

/-- The component `x` of `x + εx'`. -/
def fst (z : Deformed ω A) : P A := Prod.fst (α := P A) (β := P A) z

/-- The component `x'` of `x + εx'`. -/
def snd (z : Deformed ω A) : P A := Prod.snd (α := P A) (β := P A) z

@[simp] lemma fst_mk (x x' : P A) : fst (mk (ω := ω) x x') = x := rfl

@[simp] lemma snd_mk (x x' : P A) : snd (mk (ω := ω) x x') = x' := rfl

@[ext] lemma ext {z z' : Deformed ω A} (h1 : fst z = fst z') (h2 : snd z = snd z') : z = z' :=
  Prod.ext h1 h2

@[simp] lemma mk_fst_snd (z : Deformed ω A) : mk (fst z) (snd z) = z := rfl

@[simp] lemma fst_add (z z' : Deformed ω A) : fst (z + z') = fst z + fst z' := rfl

@[simp] lemma snd_add (z z' : Deformed ω A) : snd (z + z') = snd z + snd z' := rfl

@[simp] lemma fst_sub (z z' : Deformed ω A) : fst (z - z') = fst z - fst z' := rfl

@[simp] lemma snd_sub (z z' : Deformed ω A) : snd (z - z') = snd z - snd z' := rfl

@[simp] lemma fst_neg (z : Deformed ω A) : fst (-z) = -fst z := rfl

@[simp] lemma snd_neg (z : Deformed ω A) : snd (-z) = -snd z := rfl

@[simp] lemma fst_zero : fst (0 : Deformed ω A) = 0 := rfl

@[simp] lemma snd_zero : snd (0 : Deformed ω A) = 0 := rfl

@[simp] lemma fst_smul (c : R) (z : Deformed ω A) : fst (c • z) = c • fst z := rfl

@[simp] lemma snd_smul (c : R) (z : Deformed ω A) : snd (c • z) = c • snd z := rfl

lemma mk_add (x x' y y' : P A) : mk (ω := ω) x x' + mk y y' = mk (x + y) (x' + y') := rfl

lemma mk_sub (x x' y y' : P A) : mk (ω := ω) x x' - mk y y' = mk (x - y) (x' - y') := rfl

@[simp] lemma mk_zero_zero : mk (ω := ω) (0 : P A) 0 = 0 := rfl

/-- `x + εx' = x + ε·x'`, split into its two parts. -/
lemma mk_eq_add (x x' : P A) : mk (ω := ω) x x' = mk x 0 + mk 0 x' := by
  rw [mk_add, add_zero, zero_add]

variable (ω) in
/-- The first component, as a linear map. -/
def fstL (A : Type) [Fintype A] [DecidableEq A] : Deformed ω A →ₗ[R] P A where
  toFun := fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (ω) in
/-- The second component, as a linear map. -/
def sndL (A : Type) [Fintype A] [DecidableEq A] : Deformed ω A →ₗ[R] P A where
  toFun := snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma fstL_apply (z : Deformed ω A) : fstL ω A z = fst z := rfl

@[simp] lemma sndL_apply (z : Deformed ω A) : sndL ω A z = snd z := rfl

end Deformed

end Pairs

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-- Moving a relabelling to the other side. -/
lemma SymOperad.eq_map_symm_of_map_eq' {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] {e : A ≃ B} {x : P A} {y : P B} (h : SymOperad.map (R := R) e x = y) :
    x = SymOperad.map (R := R) e.symm y := by
  rw [← h, SymOperad.map_symm_map]

/-! ## The cocycle conditions -/

namespace SymCochain

/-- **The cocycle conditions** on a two-cochain: the identities making the deformed composition an
operad with the same action and unit, written out (equivariance, the two unit laws, sequential and
parallel associativity). -/
structure IsCocycle (ω : SymCochain R P) : Prop where
  map_comp : ∀ {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (σ : A ≃ A') (τ : B ≃ B') (i : A)
    (x : P A) (y : P B),
    SymOperad.map (R := R) (compEquiv σ τ i) (ω i x y)
      = ω (σ i) (SymOperad.map (R := R) σ x) (SymOperad.map (R := R) τ y)
  comp_one : ∀ {A : Type} [Fintype A] [DecidableEq A] (i : A) (x : P A),
    ω i x (SymOperad.one R) = 0
  one_comp : ∀ {B : Type} [Fintype B] [DecidableEq B] (y : P B), ω () (SymOperad.one R) y = 0
  assoc_seq : ∀ {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) (x : P A) (y : P B) (z : P D),
    SymOperad.map (R := R) (seqEquiv i j D)
        (SymOperad.comp (R := R) (Sum.inr j) (ω i x y) z
          + ω (Sum.inr j) (SymOperad.comp (R := R) i x y) z)
      = SymOperad.comp (R := R) i x (ω j y z) + ω i x (SymOperad.comp (R := R) j y z)
  assoc_par : ∀ {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (x : P A) (y : P B) (z : P D),
    SymOperad.map (R := R) (parEquiv hik B D)
        (SymOperad.comp (R := R) (Sum.inl ⟨k, Ne.symm hik⟩) (ω i x y) z
          + ω (Sum.inl ⟨k, Ne.symm hik⟩) (SymOperad.comp (R := R) i x y) z)
      = SymOperad.comp (R := R) (Sum.inl ⟨i, hik⟩) (ω k x z) y
        + ω (Sum.inl ⟨i, hik⟩) (SymOperad.comp (R := R) k x z) y

/-- **The zero cochain is a cocycle**: the trivial deformation `P[ε]`. -/
theorem isCocycle_zero : (SymCochain.zero : SymCochain R P).IsCocycle where
  map_comp _ _ _ _ _ := by simp
  comp_one _ _ := rfl
  one_comp _ := rfl
  assoc_seq _ _ _ _ _ := by simp
  assoc_par _ _ _ _ := by simp

instance instFactIsCocycleZero : Fact (SymCochain.zero : SymCochain R P).IsCocycle :=
  ⟨isCocycle_zero⟩

/-- **The cocycles form a submodule**: a linear combination of cocycles is a cocycle. -/
theorem IsCocycle.add_smul {ω ω' : SymCochain R P} (h : ω.IsCocycle) (h' : ω'.IsCocycle)
    (c c' : R) : (c • ω + c' • ω').IsCocycle where
  map_comp σ τ i x y := by
    simp only [Pi.add_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add,
      map_smul, h.map_comp, h'.map_comp]
  comp_one i x := by
    simp only [Pi.add_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      h.comp_one, h'.comp_one, smul_zero, add_zero]
  one_comp y := by
    simp only [Pi.add_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      h.one_comp, h'.one_comp, smul_zero, add_zero]
  assoc_seq i j x y z := by
    have e := h.assoc_seq i j x y z
    have e' := h'.assoc_seq i j x y z
    simp only [Pi.add_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add,
      map_smul] at e e' ⊢
    linear_combination (norm := module) c • e + c' • e'
  assoc_par hik x y z := by
    have e := h.assoc_par hik x y z
    have e' := h'.assoc_par hik x y z
    simp only [Pi.add_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add,
      map_smul] at e e' ⊢
    linear_combination (norm := module) c • e + c' • e'

end SymCochain

/-! ## The deformed operad -/

namespace Deformed

variable {ω : SymCochain R P} {A B C D : Type} [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable (ω) in
/-- Relabelling, componentwise. -/
def map (e : A ≃ B) : Deformed ω A →ₗ[R] Deformed ω B where
  toFun z := mk (SymOperad.map (R := R) e (fst z)) (SymOperad.map (R := R) e (snd z))
  map_add' z z' := by ext <;> simp
  map_smul' c z := by ext <;> simp

@[simp] lemma fst_map (e : A ≃ B) (z : Deformed ω A) :
    fst (map ω e z) = SymOperad.map (R := R) e (fst z) := rfl

@[simp] lemma snd_map (e : A ≃ B) (z : Deformed ω A) :
    snd (map ω e z) = SymOperad.map (R := R) e (snd z) := rfl

variable (ω) in
/-- **The deformed composition** `(x, x') ∘ᵢ (y, y') = (x ∘ᵢ y, x' ∘ᵢ y + x ∘ᵢ y' + ωᵢ(x, y))`. -/
def comp (i : A) : Deformed ω A →ₗ[R] Deformed ω B →ₗ[R] Deformed ω (Without A i ⊕ B) :=
  LinearMap.mk₂ R
    (fun z z' => mk (SymOperad.comp (R := R) i (fst z) (fst z'))
      (SymOperad.comp (R := R) i (snd z) (fst z') + SymOperad.comp (R := R) i (fst z) (snd z')
        + ω i (fst z) (fst z')))
    (fun z₁ z₂ z' => by
      ext
      · simp
      · simp only [snd_mk, fst_add, snd_add, map_add, LinearMap.add_apply]
        abel)
    (fun c z z' => by ext <;> simp [smul_add])
    (fun z z₁ z₂ => by
      ext
      · simp
      · simp only [snd_mk, fst_add, snd_add, map_add]
        abel)
    (fun c z z' => by ext <;> simp [smul_add])

@[simp] lemma fst_comp (i : A) (z : Deformed ω A) (z' : Deformed ω B) :
    fst (comp ω i z z') = SymOperad.comp (R := R) i (fst z) (fst z') := rfl

@[simp] lemma snd_comp (i : A) (z : Deformed ω A) (z' : Deformed ω B) :
    snd (comp ω i z z') = SymOperad.comp (R := R) i (snd z) (fst z')
      + SymOperad.comp (R := R) i (fst z) (snd z') + ω i (fst z) (fst z') := rfl

/-- **The deformed operad is a symmetric operad when `ω` is a cocycle.** -/
instance instSymOperad [hω : Fact ω.IsCocycle] : SymOperad R (Deformed ω) where
  map e := map ω e
  map_refl z := ext (SymOperad.map_refl (R := R) _) (SymOperad.map_refl (R := R) _)
  map_trans e f z := ext (SymOperad.map_trans (R := R) _ _ _) (SymOperad.map_trans (R := R) _ _ _)
  one := mk (SymOperad.one R) 0
  comp i := comp ω i
  map_comp σ τ i z z' := by
    ext
    · exact SymOperad.map_comp (R := R) σ τ i _ _
    · simp only [snd_map, snd_comp, fst_map, map_add, SymOperad.map_comp (R := R),
        hω.out.map_comp]
  comp_one i z := by
    ext
    · exact SymOperad.comp_one (R := R) i (fst z)
    · simp only [snd_map, snd_comp, fst_mk, snd_mk, map_zero, hω.out.comp_one, add_zero,
        SymOperad.comp_one (R := R)]
  one_comp z := by
    ext
    · exact SymOperad.one_comp (R := R) (fst z)
    · simp only [snd_map, snd_comp, fst_mk, snd_mk, map_zero, LinearMap.zero_apply,
        hω.out.one_comp, zero_add, add_zero, SymOperad.one_comp (R := R)]
  comp_assoc_seq i j x y z := by
    ext
    · exact SymOperad.comp_assoc_seq (R := R) i j (fst x) (fst y) (fst z)
    · have h := hω.out.assoc_seq i j (fst x) (fst y) (fst z)
      rw [map_add] at h
      simp only [snd_map, snd_comp, fst_comp, map_add, LinearMap.add_apply,
        SymOperad.comp_assoc_seq (R := R)]
      linear_combination (norm := module) h
  comp_assoc_par hik x y z := by
    ext
    · exact SymOperad.comp_assoc_par (R := R) hik (fst x) (fst y) (fst z)
    · have h := hω.out.assoc_par hik (fst x) (fst y) (fst z)
      rw [map_add] at h
      simp only [snd_map, snd_comp, fst_comp, map_add, LinearMap.add_apply,
        SymOperad.comp_assoc_par (R := R)]
      linear_combination (norm := module) h

section Operations

variable [Fact ω.IsCocycle]

@[simp] lemma fst_symMap (e : A ≃ B) (z : Deformed ω A) :
    fst (SymOperad.map (R := R) e z) = SymOperad.map (R := R) e (fst z) := rfl

@[simp] lemma snd_symMap (e : A ≃ B) (z : Deformed ω A) :
    snd (SymOperad.map (R := R) e z) = SymOperad.map (R := R) e (snd z) := rfl

@[simp] lemma fst_symComp (i : A) (z : Deformed ω A) (z' : Deformed ω B) :
    fst (SymOperad.comp (R := R) i z z') = SymOperad.comp (R := R) i (fst z) (fst z') := rfl

@[simp] lemma snd_symComp (i : A) (z : Deformed ω A) (z' : Deformed ω B) :
    snd (SymOperad.comp (R := R) i z z') = SymOperad.comp (R := R) i (snd z) (fst z')
      + SymOperad.comp (R := R) i (fst z) (snd z') + ω i (fst z) (fst z') := rfl

@[simp] lemma fst_one : fst (SymOperad.one R : Deformed ω Unit) = SymOperad.one R := rfl

@[simp] lemma snd_one : snd (SymOperad.one R : Deformed ω Unit) = 0 := rfl

lemma symMap_mk (e : A ≃ B) (x x' : P A) :
    SymOperad.map (R := R) e (mk (ω := ω) x x')
      = mk (SymOperad.map (R := R) e x) (SymOperad.map (R := R) e x') := rfl

/-- **`εP` is a square-zero ideal**, on the left. -/
lemma comp_mk_zero_left (i : A) (ξ : P A) (z : Deformed ω B) :
    SymOperad.comp (R := R) i (mk (ω := ω) 0 ξ) z
      = mk 0 (SymOperad.comp (R := R) i ξ (fst z)) := by
  ext <;> simp

/-- **`εP` is a square-zero ideal**, on the right. -/
lemma comp_mk_zero_right (i : A) (z : Deformed ω A) (ξ : P B) :
    SymOperad.comp (R := R) i z (mk (ω := ω) 0 ξ)
      = mk 0 (SymOperad.comp (R := R) i (fst z) ξ) := by
  ext <;> simp

variable (ω) in
/-- **The first component is a morphism** `P_ω → P`. -/
def fstHom : SymOperadHom R (Deformed ω) P where
  app A _ _ := fstL ω A
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

@[simp] lemma fstHom_app (z : Deformed ω A) : (fstHom ω).app A z = fst z := rfl

end Operations

/-- **Conversely, a composition of the deformed shape making the pairs an operad, with the action
and the unit of `P`, comes from a cocycle.** -/
theorem isCocycle_of_symOperad (S : SymOperad R (Deformed ω))
    (hmap : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B),
      @SymOperad.map R _ (Deformed ω) _ _ S A B _ _ _ _ e = map ω e)
    (hone : @SymOperad.one R _ (Deformed ω) _ _ S = mk (SymOperad.one R) 0)
    (hcomp : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A),
      @SymOperad.comp R _ (Deformed ω) _ _ S A B _ _ _ _ i = comp ω i) :
    ω.IsCocycle where
  map_comp σ τ i x y := by
    have h := congrArg snd (@SymOperad.map_comp R _ (Deformed ω) _ _ S _ _ _ _ _ _ _ _ _ _ _ _
      σ τ i (mk x 0) (mk y 0))
    simpa [hmap, hcomp] using h
  comp_one i x := by
    have h := congrArg snd (@SymOperad.comp_one R _ (Deformed ω) _ _ S _ _ _ i (mk x 0))
    simp only [hmap, hcomp, hone, snd_map, snd_comp, fst_mk, snd_mk, map_zero,
      LinearMap.zero_apply, zero_add] at h
    exact SymOperad.map_injective (R := R) _ (h.trans (map_zero _).symm)
  one_comp y := by
    have h := congrArg snd (@SymOperad.one_comp R _ (Deformed ω) _ _ S _ _ _ (mk y 0))
    simp only [hmap, hcomp, hone, snd_map, snd_comp, fst_mk, snd_mk, map_zero,
      LinearMap.zero_apply, zero_add] at h
    exact SymOperad.map_injective (R := R) _ (h.trans (map_zero _).symm)
  assoc_seq i j x y z := by
    have h := congrArg snd (@SymOperad.comp_assoc_seq R _ (Deformed ω) _ _ S _ _ _ _ _ _ _ _ _
      i j (mk x 0) (mk y 0) (mk z 0))
    simpa [hmap, hcomp] using h
  assoc_par hik x y z := by
    have h := congrArg snd (@SymOperad.comp_assoc_par R _ (Deformed ω) _ _ S _ _ _ _ _ _ _ _ _
      _ _ hik (mk x 0) (mk y 0) (mk z 0))
    simpa [hmap, hcomp] using h

end Deformed

/-! ## Coboundaries -/

variable (R P) in
/-- **An equivariant family of linear maps**, a one-cochain. -/
structure SymEndo where
  /-- The component at a finite input set. -/
  app (A : Type) [Fintype A] [DecidableEq A] : P A →ₗ[R] P A
  /-- The components commute with relabelling. -/
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : P A) : app B (SymOperad.map (R := R) e x) = SymOperad.map (R := R) e (app A x)

namespace SymEndo

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The coboundary** `(δφ)ᵢ(x, y) = φ(x ∘ᵢ y) - φ(x) ∘ᵢ y - x ∘ᵢ φ(y)`. -/
def coboundary (φ : SymEndo R P) : SymCochain R P := fun _ _ _ _ _ _ i =>
  (SymOperad.comp (R := R) i).compr₂ (φ.app _) - (SymOperad.comp (R := R) i).comp (φ.app _)
    - (SymOperad.comp (R := R) i).compl₂ (φ.app _)

@[simp] lemma coboundary_apply (φ : SymEndo R P) (i : A) (x : P A) (y : P B) :
    φ.coboundary i x y = φ.app _ (SymOperad.comp (R := R) i x y)
      - SymOperad.comp (R := R) i (φ.app A x) y - SymOperad.comp (R := R) i x (φ.app B y) :=
  rfl

/-- **The coboundary of an equivariant family vanishing on the unit is a cocycle.** -/
theorem isCocycle_coboundary (φ : SymEndo R P) (h : φ.app Unit (SymOperad.one R) = 0) :
    φ.coboundary.IsCocycle where
  map_comp σ τ i x y := by
    simp only [coboundary_apply, map_sub, ← φ.app_map, SymOperad.map_comp (R := R)]
  comp_one i x := by
    simp only [coboundary_apply, h, map_zero, SymOperad.comp_one' (R := R), φ.app_map, sub_self]
  one_comp y := by
    simp only [coboundary_apply, h, map_zero, LinearMap.zero_apply, SymOperad.one_comp' (R := R),
      φ.app_map, sub_zero, sub_self]
  assoc_seq i j x y z := by
    simp only [coboundary_apply, map_sub, LinearMap.sub_apply, map_add, ← φ.app_map,
      SymOperad.comp_assoc_seq (R := R)]
    abel
  assoc_par hik x y z := by
    simp only [coboundary_apply, map_sub, LinearMap.sub_apply, map_add, ← φ.app_map,
      SymOperad.comp_assoc_par (R := R)]
    abel

end SymEndo

namespace SymCochain

/-- **A coboundary**: `ω = δφ` for an equivariant family `φ` of linear maps. -/
def IsCoboundary (ω : SymCochain R P) : Prop :=
  ∃ φ : SymEndo R P, ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (i : A) (x : P A) (y : P B), ω i x y = φ.coboundary i x y

/-- A family whose coboundary is a cocycle vanishes on the unit. -/
lemma app_one_eq_zero {ω : SymCochain R P} (hω : ω.IsCocycle) (φ : SymEndo R P)
    (hφ : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
      (i : A) (x : P A) (y : P B), ω i x y = φ.coboundary i x y) :
    φ.app Unit (SymOperad.one R) = 0 := by
  have h := (hφ () (SymOperad.one R) (SymOperad.one R)).symm.trans (hω.comp_one () _)
  rw [SymEndo.coboundary_apply, SymOperad.comp_one' (R := R), SymOperad.comp_one' (R := R),
    SymOperad.one_comp' (R := R), φ.app_map, sub_self, zero_sub, neg_eq_zero] at h
  exact SymOperad.map_injective (R := R) _ (h.trans (map_zero _).symm)

end SymCochain

section Lift

variable {ω : SymCochain R P} [hω : Fact ω.IsCocycle]

/-- The morphism `x ↦ (x, φ x)` of a family whose coboundary is `ω`. -/
def SymEndo.lift (φ : SymEndo R P)
    (hφ : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
      (i : A) (x : P A) (y : P B), ω i x y = φ.coboundary i x y) :
    SymOperadHom R P (Deformed ω) where
  app A _ _ :=
    { toFun := fun x => Deformed.mk x (φ.app A x)
      map_add' := fun x y => by rw [map_add, Deformed.mk_add]
      map_smul' := fun c x => by
        ext <;> simp only [Deformed.fst_mk, Deformed.snd_mk, Deformed.fst_smul,
          Deformed.snd_smul, map_smul, RingHom.id_apply] }
  app_map e x := by
    ext
    · rfl
    · exact φ.app_map e x
  app_one := by
    ext
    · rfl
    · exact SymCochain.app_one_eq_zero hω.out φ hφ
  app_comp i x y := by
    ext
    · rfl
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, Deformed.snd_mk, Deformed.snd_symComp,
        Deformed.fst_mk, hφ, SymEndo.coboundary_apply]
      abel

/-- **A cocycle is a coboundary exactly when `P → P_ω` has a lift of the identity**: a morphism
of operads with first component the identity (Bao, Wang, Xu, Ye, Zhang, and Zhao, Thm. 2.10(2)).
The lift is `x ↦ (x, φ x)`, for `ω = δφ`. -/
theorem isCoboundary_iff_exists_lift :
    ω.IsCoboundary ↔ ∃ F : SymOperadHom R P (Deformed ω),
      ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), Deformed.fst (F.app A x) = x := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ.lift hφ, fun _ _ _ _ => rfl⟩
  · rintro ⟨F, hF⟩
    refine ⟨⟨fun A _ _ => (Deformed.sndL ω A).comp (F.app A), fun e x => ?_⟩, ?_⟩
    · simp only [LinearMap.coe_comp, Function.comp_apply, Deformed.sndL_apply, F.app_map]
      rfl
    · intro A B _ _ _ _ i x y
      have h := congrArg Deformed.snd (F.app_comp i x y)
      simp only [Deformed.snd_symComp, hF] at h
      simp only [SymEndo.coboundary_apply, LinearMap.coe_comp, Function.comp_apply,
        Deformed.sndL_apply, h]
      abel

end Lift

/-! ## Derivations -/

variable (R P) in
/-- **A derivation**: an equivariant family of linear maps with the Leibniz rule
`D(x ∘ᵢ y) = D x ∘ᵢ y + x ∘ᵢ D y`. -/
structure SymDerivation extends SymEndo R P where
  /-- The Leibniz rule. -/
  app_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : P A) (y : P B) :
    app _ (SymOperad.comp (R := R) i x y)
      = SymOperad.comp (R := R) i (app A x) y + SymOperad.comp (R := R) i x (app B y)

namespace SymDerivation

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

@[ext] lemma ext {D D' : SymDerivation R P}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), D.app A x = D'.app A x) :
    D = D' := by
  obtain ⟨⟨Da, _⟩, _⟩ := D
  obtain ⟨⟨D'a, _⟩, _⟩ := D'
  have : @Da = @D'a := by
    funext A _ _
    exact LinearMap.ext (h A)
  subst this
  rfl

/-- **A derivation kills the unit.** -/
theorem app_one (D : SymDerivation R P) : D.app Unit (SymOperad.one R) = 0 := by
  have h := D.app_comp () (SymOperad.one R) (SymOperad.one R)
  rw [SymOperad.comp_one' (R := R), SymOperad.comp_one' (R := R), SymOperad.one_comp' (R := R),
    D.app_map] at h
  have h2 : SymOperad.map (R := R) (leftUnitEquiv Unit).symm (D.app Unit (SymOperad.one R)) = 0 :=
    by linear_combination (norm := module) (-1 : R) • h
  exact SymOperad.map_injective (R := R) _ (h2.trans (map_zero _).symm)

/-- The morphism `x ↦ (x, D x)` into `P[ε]`. -/
def lift (D : SymDerivation R P) : SymOperadHom R P (Deformed (SymCochain.zero : SymCochain R P)) :=
  D.toSymEndo.lift (ω := SymCochain.zero) fun i x y => by
    rw [SymEndo.coboundary_apply, SymCochain.zero_apply, D.app_comp]
    abel

@[simp] lemma fst_lift (D : SymDerivation R P) (x : P A) : Deformed.fst (D.lift.app A x) = x :=
  rfl

@[simp] lemma snd_lift (D : SymDerivation R P) (x : P A) :
    Deformed.snd (D.lift.app A x) = D.app A x := rfl

/-- **Derivations are the morphisms `P → P[ε]` lifting the identity** (`ω = 0`). -/
def liftEquiv : SymDerivation R P ≃
    {F : SymOperadHom R P (Deformed (SymCochain.zero : SymCochain R P)) //
      ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), Deformed.fst (F.app A x) = x} where
  toFun D := ⟨D.lift, fun _ _ _ _ => rfl⟩
  invFun F :=
    { app := fun A _ _ => (Deformed.sndL _ A).comp (F.1.app A)
      app_map := fun e x => by
        simp only [LinearMap.coe_comp, Function.comp_apply, Deformed.sndL_apply, F.1.app_map]
        rfl
      app_comp := fun i x y => by
        have h := congrArg Deformed.snd (F.1.app_comp i x y)
        simp only [Deformed.snd_symComp, F.2, SymCochain.zero_apply, add_zero] at h
        simp only [LinearMap.coe_comp, Function.comp_apply, Deformed.sndL_apply, h] }
  left_inv D := by ext; rfl
  right_inv F := by
    apply Subtype.ext
    ext A _ _ x
    · exact (F.2 A x).symm
    · rfl

/-! ### Linear combinations of derivations -/

instance : Zero (SymDerivation R P) :=
  ⟨{ app := fun _ _ _ => 0
     app_map := fun _ _ => by simp
     app_comp := fun _ _ _ => by simp }⟩

instance : Add (SymDerivation R P) :=
  ⟨fun D D' =>
    { app := fun A _ _ => D.app A + D'.app A
      app_map := fun e x => by simp only [LinearMap.add_apply, map_add, D.app_map, D'.app_map]
      app_comp := fun i x y => by
        simp only [LinearMap.add_apply, D.app_comp, D'.app_comp, map_add, LinearMap.add_apply]
        abel }⟩

instance : SMul R (SymDerivation R P) :=
  ⟨fun c D =>
    { app := fun A _ _ => c • D.app A
      app_map := fun e x => by simp only [LinearMap.smul_apply, map_smul, D.app_map]
      app_comp := fun i x y => by
        simp only [LinearMap.smul_apply, D.app_comp, map_smul, LinearMap.smul_apply, smul_add] }⟩

@[simp] lemma zero_app (x : P A) : (0 : SymDerivation R P).app A x = 0 := rfl

@[simp] lemma add_app (D D' : SymDerivation R P) (x : P A) :
    (D + D').app A x = D.app A x + D'.app A x := rfl

@[simp] lemma smul_app (c : R) (D : SymDerivation R P) (x : P A) :
    (c • D).app A x = c • D.app A x := rfl

/-- **Derivations are determined by their lifts**: two derivations with the same lift
`P → P[ε]` are equal. -/
lemma eq_of_lift_eq {D D' : SymDerivation R P} (h : D.lift = D'.lift) : D = D' :=
  liftEquiv.injective (Subtype.ext h)

/-! ### The Euler derivation and the inner derivations -/

lemma card_without (i : A) : Fintype.card (Without A i) + 1 = Fintype.card A := by
  rw [← Fintype.card_option, Fintype.card_congr (Equiv.optionSubtypeNe i)]

/-- **The Euler derivation**, multiplying `P(A)` by `|A| - 1`. -/
def euler : SymDerivation R P where
  app A _ _ := ((Fintype.card A : R) - 1) • LinearMap.id
  app_map e x := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Fintype.card_congr e]
  app_comp i x y := by
    have h := card_without i
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearMap.smul_apply,
      Fintype.card_sum, ← add_smul]
    congr 1
    rw [← h]
    push_cast
    ring

@[simp] lemma euler_app (x : P A) :
    (euler : SymDerivation R P).app A x = ((Fintype.card A : R) - 1) • x := rfl

/-- The `θ ∘ x` term of an inner derivation. -/
def adLeft (θ : P Unit) (A : Type) [Fintype A] [DecidableEq A] : P A →ₗ[R] P A :=
  (SymOperad.map (R := R) (leftUnitEquiv A)).comp (SymOperad.comp (R := R) () θ)

/-- The `x ∘ₐ θ` term of an inner derivation. -/
def adRight (θ : P Unit) (A : Type) [Fintype A] [DecidableEq A] (a : A) : P A →ₗ[R] P A :=
  (SymOperad.map (R := R) (rightUnitEquiv a)).comp ((SymOperad.comp (R := R) a).flip θ)

@[simp] lemma adLeft_apply (θ : P Unit) (x : P A) :
    adLeft (R := R) θ A x
      = SymOperad.map (R := R) (leftUnitEquiv A) (SymOperad.comp (R := R) () θ x) := rfl

@[simp] lemma adRight_apply (θ : P Unit) (a : A) (x : P A) :
    adRight (R := R) θ A a x
      = SymOperad.map (R := R) (rightUnitEquiv a) (SymOperad.comp (R := R) a x θ) := rfl

lemma map_congr_equiv {e f : A ≃ B} (h : ∀ a, e a = f a) (x : P A) :
    SymOperad.map (R := R) e x = SymOperad.map (R := R) f x := by
  rw [Equiv.ext h]

lemma adLeft_map (θ : P Unit) (e : A ≃ B) (x : P A) :
    adLeft (R := R) θ B (SymOperad.map (R := R) e x)
      = SymOperad.map (R := R) e (adLeft (R := R) θ A x) := by
  have h := SymOperad.map_comp (R := R) (Equiv.refl Unit) e () θ x
  rw [SymOperad.map_refl (R := R)] at h
  rw [adLeft_apply, adLeft_apply, ← h, SymOperad.map_map, SymOperad.map_map]
  refine map_congr_equiv (fun c => ?_) _
  rcases c with ⟨u, hu⟩ | a
  · exact absurd (Subsingleton.elim u ()) hu
  · rfl

lemma adRight_map (θ : P Unit) (e : A ≃ B) (a : A) (x : P A) :
    adRight (R := R) θ B (e a) (SymOperad.map (R := R) e x)
      = SymOperad.map (R := R) e (adRight (R := R) θ A a x) := by
  have h := SymOperad.map_comp (R := R) e (Equiv.refl Unit) a x θ
  rw [SymOperad.map_refl (R := R)] at h
  rw [adRight_apply, adRight_apply, ← h, SymOperad.map_map, SymOperad.map_map]
  refine map_congr_equiv (fun c => ?_) _
  rcases c with ⟨c, hc⟩ | u
  · rfl
  · rfl

lemma adLeft_comp (θ : P Unit) (i : A) (x : P A) (y : P B) :
    adLeft (R := R) θ _ (SymOperad.comp (R := R) i x y)
      = SymOperad.comp (R := R) i (adLeft (R := R) θ A x) y := by
  have h1 := SymOperad.comp_assoc_seq (R := R) () i θ x y
  have h2 := SymOperad.map_comp (R := R) (leftUnitEquiv A) (Equiv.refl B) (Sum.inr i)
    (SymOperad.comp (R := R) () θ x) y
  rw [SymOperad.map_refl (R := R)] at h2
  rw [adLeft_apply, adLeft_apply, ← h1, SymOperad.map_map]
  refine Eq.trans ?_ h2
  refine map_congr_equiv (fun c => ?_) _
  rcases c with ⟨⟨u, hu⟩ | a, h⟩ | b
  · exact absurd (Subsingleton.elim u ()) hu
  · rfl
  · rfl

lemma adRight_comp_inl (θ : P Unit) (i : A) (a : Without A i) (x : P A) (y : P B) :
    adRight (R := R) θ _ (Sum.inl a) (SymOperad.comp (R := R) i x y)
      = SymOperad.comp (R := R) i (adRight (R := R) θ A a.1 x) y := by
  obtain ⟨a, ha⟩ := a
  have h1 := SymOperad.comp_assoc_par (R := R) (Ne.symm ha) x y θ
  have h2 := SymOperad.map_comp (R := R) (rightUnitEquiv a) (Equiv.refl B)
    (Sum.inl ⟨i, Ne.symm ha⟩) (SymOperad.comp (R := R) a x θ) y
  rw [SymOperad.map_refl (R := R)] at h2
  rw [adRight_apply, adRight_apply, SymOperad.eq_map_symm_of_map_eq' h1, SymOperad.map_map]
  refine Eq.trans ?_ h2
  refine map_congr_equiv (fun c => ?_) _
  rcases c with ⟨⟨c, hc⟩ | b, h⟩ | u
  · rfl
  · rfl
  · rfl

lemma adRight_comp_inr (θ : P Unit) (i : A) (b : B) (x : P A) (y : P B) :
    adRight (R := R) θ _ (Sum.inr b) (SymOperad.comp (R := R) i x y)
      = SymOperad.comp (R := R) i x (adRight (R := R) θ B b y) := by
  have h1 := SymOperad.comp_assoc_seq (R := R) i b x y θ
  have h2 := SymOperad.map_comp (R := R) (Equiv.refl A) (rightUnitEquiv b) i x
    (SymOperad.comp (R := R) b y θ)
  rw [SymOperad.map_refl (R := R), ← h1, SymOperad.map_map] at h2
  rw [adRight_apply, adRight_apply]
  refine Eq.trans ?_ h2
  refine map_congr_equiv (fun c => ?_) _
  rcases c with ⟨a | b', h⟩ | u
  · rfl
  · rfl
  · rfl

lemma adRight_self_comp (θ : P Unit) (i : A) (x : P A) (y : P B) :
    SymOperad.comp (R := R) i (adRight (R := R) θ A i x) y
      = SymOperad.comp (R := R) i x (adLeft (R := R) θ B y) := by
  have h1 := SymOperad.comp_assoc_seq (R := R) i () x θ y
  have h2 := SymOperad.map_comp (R := R) (rightUnitEquiv i) (Equiv.refl B) (Sum.inr ())
    (SymOperad.comp (R := R) i x θ) y
  have h3 := SymOperad.map_comp (R := R) (Equiv.refl A) (leftUnitEquiv B) i x
    (SymOperad.comp (R := R) () θ y)
  rw [SymOperad.map_refl (R := R)] at h2 h3
  rw [← h1, SymOperad.map_map] at h3
  rw [adRight_apply, adLeft_apply]
  refine h2.symm.trans (Eq.trans ?_ h3)
  refine map_congr_equiv (fun c => ?_) _
  rcases c with ⟨a | u, h⟩ | b
  · rfl
  · exact absurd rfl h
  · rfl

/-- The inner derivation of `θ`, as a family of linear maps. -/
def adApp (θ : P Unit) (A : Type) [Fintype A] [DecidableEq A] : P A →ₗ[R] P A :=
  adLeft θ A - ∑ a : A, adRight θ A a

lemma adApp_apply (θ : P Unit) (x : P A) :
    adApp (R := R) θ A x = adLeft (R := R) θ A x - ∑ a : A, adRight (R := R) θ A a x := by
  simp [adApp, LinearMap.coe_sum]

/-- **The inner derivation** `ad_θ(x) = θ ∘ x - Σₐ x ∘ₐ θ` of `θ ∈ P(1)`. -/
def ad (θ : P Unit) : SymDerivation R P where
  app A _ _ := adApp θ A
  app_map e x := by
    rw [adApp_apply, adApp_apply, map_sub, map_sum, adLeft_map, ← Equiv.sum_comp e]
    congr 1
    exact Finset.sum_congr rfl fun a _ => adRight_map θ e a x
  app_comp i x y := by
    rw [adApp_apply, adApp_apply, adApp_apply, adLeft_comp, Fintype.sum_sum_type,
      Fintype.sum_eq_add_sum_subtype_ne _ i]
    simp only [adRight_comp_inl, adRight_comp_inr, map_sub, map_add, map_sum,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
      adRight_self_comp]
    abel

@[simp] lemma ad_app (θ : P Unit) (x : P A) :
    (ad (R := R) θ).app A x = adLeft (R := R) θ A x - ∑ a : A, adRight (R := R) θ A a x :=
  adApp_apply θ x

/-- **The inner derivation of the unit is minus the Euler derivation**: `ad_1` multiplies `P(A)`
by `1 - |A|`. -/
theorem ad_one (x : P A) :
    (ad (R := R) (SymOperad.one R)).app A x = -(euler : SymDerivation R P).app A x := by
  simp only [ad_app, adLeft_apply, SymOperad.one_comp (R := R), adRight_apply,
    SymOperad.comp_one (R := R), Finset.sum_const, Finset.card_univ, euler_app, sub_smul,
    one_smul, neg_sub, ← Nat.cast_smul_eq_nsmul R]

/-- The inner derivation is linear in `θ`. -/
theorem ad_smul (c : R) (θ : P Unit) (x : P A) :
    (ad (R := R) (c • θ)).app A x = c • (ad (R := R) θ).app A x := by
  simp only [ad_app, adLeft_apply, adRight_apply, map_smul, LinearMap.smul_apply, smul_sub,
    Finset.smul_sum]

/-- **The multiples of the Euler derivation are inner**: `c · euler = ad_{-c·1}`. -/
theorem smul_euler_eq_ad (c : R) :
    c • (euler : SymDerivation R P) = ad (-c • SymOperad.one R) := by
  ext A _ _ x
  rw [smul_app, ad_smul, ad_one, smul_neg, neg_smul, neg_neg]

end SymDerivation

/-! ## Transport along isomorphisms -/

section Transport

variable {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [SymOperad R P']
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The pullback of a two-cochain along an isomorphism**:
`(e^* ω')ᵢ(x, y) = e⁻¹ ω'ᵢ(e x, e y)`. -/
def SymCochain.comap (e : SymOperadIso R P P') (ω' : SymCochain R P') : SymCochain R P :=
  fun _ _ _ _ _ _ i => ((ω' i).compl₁₂ (e.hom.app _) (e.hom.app _)).compr₂ (e.inv.app _)

@[simp] lemma SymCochain.comap_apply (e : SymOperadIso R P P') (ω' : SymCochain R P') (i : A)
    (x : P A) (y : P B) :
    SymCochain.comap e ω' i x y = e.inv.app _ (ω' i (e.hom.app A x) (e.hom.app B y)) := rfl

/-- **The pullback of a cocycle is a cocycle.** -/
theorem SymCochain.isCocycle_comap (e : SymOperadIso R P P') {ω' : SymCochain R P'}
    (h : ω'.IsCocycle) : (SymCochain.comap e ω').IsCocycle where
  map_comp σ τ i x y := by
    apply (e.bijective _).1
    simp only [comap_apply, e.hom.app_map, SymOperadIso.hom_inv_apply, h.map_comp]
  comp_one i x := by
    simp only [comap_apply, e.hom.app_one, h.comp_one, map_zero]
  one_comp y := by
    simp only [comap_apply, e.hom.app_one, h.one_comp, map_zero]
  assoc_seq i j x y z := by
    apply (e.bijective _).1
    have h' := h.assoc_seq i j (e.hom.app _ x) (e.hom.app _ y) (e.hom.app _ z)
    rw [map_add] at h'
    simp only [comap_apply, map_add, e.hom.app_map, e.hom.app_comp,
      SymOperadIso.hom_inv_apply]
    linear_combination (norm := module) h'
  assoc_par hik x y z := by
    apply (e.bijective _).1
    have h' := h.assoc_par hik (e.hom.app _ x) (e.hom.app _ y) (e.hom.app _ z)
    rw [map_add] at h'
    simp only [comap_apply, map_add, e.hom.app_map, e.hom.app_comp,
      SymOperadIso.hom_inv_apply]
    linear_combination (norm := module) h'

/-- **Vanishing second cohomology transports along isomorphisms**: if every cocycle of `P` is a
coboundary, so is every cocycle of an operad isomorphic to `P`. -/
theorem SymOperadIso.forall_isCoboundary (e : SymOperadIso R P P')
    (h : ∀ ω : SymCochain R P, ω.IsCocycle → ω.IsCoboundary) (ω' : SymCochain R P')
    (hω' : ω'.IsCocycle) : ω'.IsCoboundary := by
  obtain ⟨φ, hφ⟩ := h _ (SymCochain.isCocycle_comap e hω')
  refine ⟨⟨fun A _ _ => (e.hom.app A).comp ((φ.app A).comp (e.inv.app A)), fun f x => ?_⟩,
    fun i x y => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, e.inv.app_map, φ.app_map, e.hom.app_map]
  · have h1 := congrArg (e.hom.app _) (hφ i (e.inv.app _ x) (e.inv.app _ y))
    simp only [SymCochain.comap_apply, SymOperadIso.hom_inv_apply, SymEndo.coboundary_apply,
      map_sub, e.hom.app_comp] at h1
    simp only [SymEndo.coboundary_apply, LinearMap.coe_comp, Function.comp_apply, h1,
      e.inv.app_comp]

/-- **A derivation transported along an isomorphism**: `e ∘ D ∘ e⁻¹`. -/
def SymDerivation.transport (e : SymOperadIso R P P') (D : SymDerivation R P) :
    SymDerivation R P' where
  app A _ _ := (e.hom.app A).comp ((D.app A).comp (e.inv.app A))
  app_map f x := by
    simp only [LinearMap.coe_comp, Function.comp_apply, e.inv.app_map, D.app_map, e.hom.app_map]
  app_comp i x y := by
    simp only [LinearMap.coe_comp, Function.comp_apply, e.inv.app_comp, D.app_comp, map_add,
      e.hom.app_comp, SymOperadIso.hom_inv_apply]

@[simp] lemma SymDerivation.transport_app (e : SymOperadIso R P P') (D : SymDerivation R P)
    (x : P' A) : (D.transport e).app A x = e.hom.app A (D.app A (e.inv.app A x)) := rfl

/-- **If every derivation of `P` is a multiple of the Euler derivation, so is every derivation of
an operad isomorphic to `P`.** -/
theorem SymOperadIso.forall_eq_smul_euler (e : SymOperadIso R P P')
    (h : ∀ D : SymDerivation R P, ∃ c : R, D = c • SymDerivation.euler)
    (D' : SymDerivation R P') : ∃ c : R, D' = c • SymDerivation.euler := by
  obtain ⟨c, hc⟩ := h (D'.transport e.symm)
  refine ⟨c, SymDerivation.ext fun A _ _ x => ?_⟩
  have h1 := congrArg (fun D : SymDerivation R P => D.app A (e.inv.app A x)) hc
  simp only [SymDerivation.transport_app, SymDerivation.smul_app, SymDerivation.euler_app] at h1
  have h2 := congrArg (e.hom.app A) h1
  simp only [SymOperadIso.symm, SymOperadIso.hom_inv_apply, map_smul] at h2
  rw [SymDerivation.smul_app, SymDerivation.euler_app]
  exact h2

end Transport

end Operad
