/-
# Square-zero extensions and derivations of graded operads

* **The sign twist** of parity `e` of a graded operad (`GrOperad.tw`), multiplying the operations
  of parity `p` by `σ(e p)`: an involution commuting with the parity projections, the relabellings
  and the compositions (`GrOperad.tw_comp`), which morphisms preserve.
* **The square-zero extension** of a graded operad `Q` by a parameter `ε` of parity `e`
  (`DualExt R Q e`): the pairs `(x, x')` standing for `x + ε x'`, with `ε² = 0`, composed by
  `(x + ε x') ∘ᵢ (y + ε y') = x ∘ᵢ y + ε (x' ∘ᵢ y + σ(e |x|) x ∘ᵢ y')`, the sign coming from moving
  `ε` across `x`. It is a graded operad (`DualExt.instGrOperad`), projecting onto `Q`
  (`DualExt.fstHom`).
* **Derivations of parity `e` along a morphism** `f : P → Q` (`GrDer f e`): linear maps shifting
  the parities by `e`, commuting with the relabellings, vanishing on the unit, with the Leibniz
  rule `D (x ∘ᵢ y) = D x ∘ᵢ f y + σ(e |x|) f x ∘ᵢ D y`. **They are the morphisms into the
  square-zero extension lifting `f`** (`GrDer.equiv`). The differential of a dg operad is an odd
  derivation (`DGOperad.toDer`), derivations along the identity compose with morphisms on either
  side (`GrDer.compHom`, `GrDer.homComp`), and **the square of an odd derivation is an even
  derivation** (`GrDer.sq`).
* **Derivations out of a free graded operad on a graded linear species** are determined by their
  values on the generators (`FreeGrL.der_ext`), and any family of values commuting with the
  relabellings and shifting the parities extends to one (`FreeGrL.derOf`, `FreeGrL.derOf_ι`). So
  **an odd derivation of `FreeGrL R V` squares to zero as soon as its square vanishes on the
  generators** (`FreeGrL.sq_eq_zero`).
-/
import Operad.FreeGrSpecies

universe u v w

namespace Operad

open Sym GerBV

/-! ## The sign twist -/

namespace GrOperad

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma par_par_self (c : Bool) (x : P A) : par (R := R) c (par (R := R) c x) = par (R := R) c x :=
  by rw [par_par, if_pos rfl]

/-- **The sign twist of parity `e`**: `x ↦ σ(e |x|) x` on homogeneous operations. -/
def tw (e : Bool) : P A →ₗ[R] P A := par false + σ R e • par true

lemma tw_apply (e : Bool) (x : P A) :
    tw (R := R) e x = par (R := R) false x + σ R e • par (R := R) true x := rfl

/-- The sign twist of a homogeneous operation. -/
lemma tw_hom (e : Bool) {c : Bool} {x : P A} (h : par (R := R) c x = x) :
    tw (R := R) e x = σ R (e && c) • x := by
  rw [tw_apply, ← h, par_par, par_par]
  cases c <;> cases e <;> simp

@[simp] lemma tw_false (x : P A) : tw (R := R) false x = x := by
  rw [tw_apply, σ_false, one_smul, par_add]

lemma tw_true (x : P A) : tw (R := R) true x = par (R := R) false x - par (R := R) true x := by
  rw [tw_apply, σ_true, neg_one_smul, sub_eq_add_neg]

lemma par_tw (e c : Bool) (x : P A) :
    par (R := R) c (tw (R := R) e x) = tw (R := R) e (par (R := R) c x) := by
  simp only [tw_apply, map_add, map_smul, par_par]
  cases c <;> simp

@[simp] lemma tw_tw (e : Bool) (x : P A) : tw (R := R) e (tw (R := R) e x) = x := by
  cases e
  · rw [tw_false, tw_false]
  · simp only [tw_true, map_sub, par_par]
    simp only [if_true, Bool.false_eq_true, if_false, Bool.true_eq_false, sub_zero, zero_sub,
      sub_neg_eq_add]
    exact par_add x

lemma map_tw (e : Bool) (σ' : A ≃ B) (x : P A) :
    map (R := R) σ' (tw (R := R) e x) = tw (R := R) e (map (R := R) σ' x) := by
  simp only [tw_apply, map_add, map_smul, map_par]

@[simp] lemma tw_one (e : Bool) : tw (R := R) e (one (R := R) (P := P)) = one (R := R) := by
  rw [tw_hom e par_one, Bool.and_false, σ_false, one_smul]

/-- A composite of homogeneous operations has the sum of their parities. -/
lemma par_comp_hom (i : A) {p q c : Bool} (hc : xor p q = c) {x : P A} {y : P B}
    (hx : par (R := R) p x = x) (hy : par (R := R) q y = y) :
    par (R := R) c (comp (R := R) i x y) = comp (R := R) i x y := by
  subst hc
  rw [← hx, ← hy]
  exact comp_par i p q x y

/-- **The sign twist is multiplicative.** -/
lemma tw_comp (e : Bool) (i : A) (x : P A) (y : P B) :
    tw (R := R) e (comp (R := R) i x y)
      = comp (R := R) i (tw (R := R) e x) (tw (R := R) e y) := by
  have key : ∀ p q : Bool,
      tw (R := R) e (comp (R := R) i (par (R := R) p x) (par (R := R) q y))
        = σ R (e && p) • σ R (e && q) • comp (R := R) i (par (R := R) p x) (par (R := R) q y) := by
    intro p q
    rw [tw_hom e (comp_par i p q x y), Bool.and_xor_distrib_left, σ_xor, mul_smul]
  have hx : tw (R := R) e x
      = σ R (e && false) • par (R := R) false x + σ R (e && true) • par (R := R) true x := by
    rw [tw_apply, Bool.and_false, Bool.and_true, σ_false, one_smul]
  have hy : tw (R := R) e y
      = σ R (e && false) • par (R := R) false y + σ R (e && true) • par (R := R) true y := by
    rw [tw_apply, Bool.and_false, Bool.and_true, σ_false, one_smul]
  conv_lhs => rw [← par_add (R := R) x, ← par_add (R := R) y]
  rw [hx, hy]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, key, smul_add,
    Bool.and_false, Bool.and_true, σ_false, one_smul]

end GrOperad

namespace GrOperadHom

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

@[simp] lemma id_app {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    (GrOperadHom.id R P).app A x = x := rfl

/-- **Morphisms preserve the sign twists.** -/
lemma app_tw (g : GrOperadHom R P Q) (e : Bool) {A : Type} [Fintype A] [DecidableEq A]
    (x : P A) : g.app A (GrOperad.tw (R := R) e x) = GrOperad.tw (R := R) e (g.app A x) := by
  simp only [GrOperad.tw_apply, map_add, map_smul, g.app_par]

end GrOperadHom

/-! ## Square-zero extensions -/

section DualExt

variable (R : Type u) [CommRing R] (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)]

set_option linter.unusedVariables false in
/-- **The square-zero extension by a parameter of parity `e`**: the pairs `(x, x')`, standing for
`x + ε x'` with `ε` of parity `e` and `ε² = 0`. -/
@[nolint unusedArguments]
def DualExt (R : Type u) [CommRing R] (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (e : Bool) (A : Type) [Fintype A] [DecidableEq A] : Type v := Q A × Q A

instance (e : Bool) (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (DualExt R Q e A) :=
  inferInstanceAs (AddCommGroup (Q A × Q A))

instance (e : Bool) (A : Type) [Fintype A] [DecidableEq A] : Module R (DualExt R Q e A) :=
  inferInstanceAs (Module R (Q A × Q A))

namespace DualExt

variable {R Q} {e : Bool} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The element `x + ε x'`. -/
def mk (x x' : Q A) : DualExt R Q e A := (x, x')

/-- The constant part. -/
def fst : DualExt R Q e A →ₗ[R] Q A := LinearMap.fst R (Q A) (Q A)

/-- The coefficient of `ε`. -/
def snd : DualExt R Q e A →ₗ[R] Q A := LinearMap.snd R (Q A) (Q A)

@[simp] lemma fst_mk (x x' : Q A) : fst (mk (R := R) (e := e) x x') = x := rfl

@[simp] lemma snd_mk (x x' : Q A) : snd (mk (R := R) (e := e) x x') = x' := rfl

@[ext] lemma ext {X Y : DualExt R Q e A} (h1 : fst X = fst Y) (h2 : snd X = snd Y) : X = Y :=
  Prod.ext h1 h2

variable [GrOperad R Q]

/-- The parity projections: `ε x'` has the parity of `x'` plus `e`. -/
def parE (c : Bool) : DualExt R Q e A →ₗ[R] DualExt R Q e A :=
  LinearMap.prodMap (GrOperad.par (R := R) c) (GrOperad.par (R := R) (xor c e))

/-- The relabellings. -/
def mapE (σ' : A ≃ B) : DualExt R Q e A →ₗ[R] DualExt R Q e B :=
  LinearMap.prodMap (GrOperad.map (R := R) σ') (GrOperad.map (R := R) σ')

/-- The compositions: `(x + ε x') ∘ᵢ (y + ε y') = x ∘ᵢ y + ε (x' ∘ᵢ y + σ(e |x|) x ∘ᵢ y')`. -/
def compE (i : A) :
    DualExt R Q e A →ₗ[R] DualExt R Q e B →ₗ[R] DualExt R Q e (Without A i ⊕ B) :=
  LinearMap.mk₂ R (fun X Y => mk (GrOperad.comp (R := R) i (fst X) (fst Y))
      (GrOperad.comp (R := R) i (snd X) (fst Y)
        + GrOperad.comp (R := R) i (GrOperad.tw (R := R) e (fst X)) (snd Y)))
    (fun X X' Y => by
      ext
      · simp only [fst_mk, map_add, LinearMap.add_apply]
      · simp only [snd_mk, map_add, LinearMap.add_apply]
        abel)
    (fun c X Y => by
      ext <;> simp only [fst_mk, snd_mk, map_smul, LinearMap.smul_apply, smul_add])
    (fun X Y Y' => by
      ext
      · simp only [fst_mk, map_add]
      · simp only [snd_mk, map_add]
        abel)
    (fun c X Y => by
      ext <;> simp only [fst_mk, snd_mk, map_smul, smul_add])

@[simp] lemma fst_parE (c : Bool) (X : DualExt R Q e A) :
    fst (parE c X) = GrOperad.par (R := R) c (fst X) := rfl

@[simp] lemma snd_parE (c : Bool) (X : DualExt R Q e A) :
    snd (parE c X) = GrOperad.par (R := R) (xor c e) (snd X) := rfl

@[simp] lemma fst_mapE (σ' : A ≃ B) (X : DualExt R Q e A) :
    fst (mapE σ' X) = GrOperad.map (R := R) σ' (fst X) := rfl

@[simp] lemma snd_mapE (σ' : A ≃ B) (X : DualExt R Q e A) :
    snd (mapE σ' X) = GrOperad.map (R := R) σ' (snd X) := rfl

@[simp] lemma fst_compE (i : A) (X : DualExt R Q e A) (Y : DualExt R Q e B) :
    fst (compE i X Y) = GrOperad.comp (R := R) i (fst X) (fst Y) := rfl

@[simp] lemma snd_compE (i : A) (X : DualExt R Q e A) (Y : DualExt R Q e B) :
    snd (compE i X Y) = GrOperad.comp (R := R) i (snd X) (fst Y)
      + GrOperad.comp (R := R) i (GrOperad.tw (R := R) e (fst X)) (snd Y) := rfl

/-- The unit, `1 + ε 0`. -/
def oneE : DualExt R Q e Unit := mk (GrOperad.one (R := R)) 0

@[simp] lemma fst_oneE : fst (oneE (R := R) (Q := Q) (e := e)) = GrOperad.one (R := R) := rfl

@[simp] lemma snd_oneE : snd (oneE (R := R) (Q := Q) (e := e)) = 0 := rfl

lemma parE_add (X : DualExt R Q e A) : parE false X + parE true X = X := by
  ext
  · simp only [map_add, fst_parE, GrOperad.par_add]
  · simp only [map_add, snd_parE]
    cases e
    · exact GrOperad.par_add _
    · exact (add_comm _ _).trans (GrOperad.par_add _)

lemma parE_parE (c c' : Bool) (X : DualExt R Q e A) :
    parE c (parE c' X) = if c = c' then parE c' X else 0 := by
  by_cases h : c = c'
  · subst h
    rw [if_pos rfl]
    ext
    · simp only [fst_parE, GrOperad.par_par_self]
    · simp only [snd_parE, GrOperad.par_par_self]
  · rw [if_neg h]
    ext
    · simp only [fst_parE, GrOperad.par_par, if_neg h, map_zero]
    · simp only [snd_parE, GrOperad.par_par, Bool.xor_left_inj, if_neg h, map_zero]

lemma compE_par (i : A) (p q : Bool) (X : DualExt R Q e A) (Y : DualExt R Q e B) :
    parE (xor p q) (compE i (parE p X) (parE q Y)) = compE i (parE p X) (parE q Y) := by
  ext
  · exact GrOperad.comp_par i p q _ _
  · simp only [snd_compE, fst_parE, snd_parE, map_add]
    congr 1
    · exact GrOperad.par_comp_hom i (by cases p <;> cases q <;> cases e <;> rfl)
        (GrOperad.par_par_self _ _) (GrOperad.par_par_self _ _)
    · rw [GrOperad.tw_hom e (GrOperad.par_par_self p _), map_smul, LinearMap.smul_apply,
        map_smul]
      congr 1
      exact GrOperad.par_comp_hom i (by cases p <;> cases q <;> cases e <;> rfl)
        (GrOperad.par_par_self _ _) (GrOperad.par_par_self _ _)

lemma mapE_compE {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (σ' : A ≃ A') (τ : B ≃ B') (i : A) (X : DualExt R Q e A) (Y : DualExt R Q e B) :
    mapE (compEquiv σ' τ i) (compE i X Y) = compE (σ' i) (mapE σ' X) (mapE τ Y) := by
  ext
  · exact GrOperad.map_comp σ' τ i _ _
  · simp only [snd_mapE, snd_compE, fst_mapE, map_add, GrOperad.map_comp, GrOperad.map_tw]

lemma compE_one (i : A) (X : DualExt R Q e A) :
    mapE (rightUnitEquiv i) (compE i X oneE) = X := by
  ext
  · exact GrOperad.comp_one i _
  · simp only [snd_mapE, snd_compE, fst_oneE, snd_oneE, map_zero, add_zero, GrOperad.comp_one]

lemma one_compE (Y : DualExt R Q e B) : mapE (leftUnitEquiv B) (compE () oneE Y) = Y := by
  ext
  · exact GrOperad.one_comp _
  · simp only [snd_mapE, snd_compE, fst_oneE, snd_oneE, map_zero, LinearMap.zero_apply,
      zero_add, GrOperad.tw_one, GrOperad.one_comp]

lemma compE_assoc_seq {D : Type} [Fintype D] [DecidableEq D] (i : A) (j : B)
    (X : DualExt R Q e A) (Y : DualExt R Q e B) (Z : DualExt R Q e D) :
    mapE (seqEquiv i j D) (compE (Sum.inr j) (compE i X Y) Z) = compE i X (compE j Y Z) := by
  ext
  · exact GrOperad.comp_assoc_seq i j _ _ _
  · simp only [snd_mapE, snd_compE, fst_compE, map_add, LinearMap.add_apply,
      GrOperad.comp_assoc_seq, GrOperad.tw_comp]
    abel

lemma compE_assoc_par {D : Type} [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k)
    (X : DualExt R Q e A) {q r : Bool} {Y : DualExt R Q e B} {Z : DualExt R Q e D}
    (hy : parE q Y = Y) (hz : parE r Z = Z) :
    mapE (parEquiv hik B D) (compE (Sum.inl ⟨k, Ne.symm hik⟩) (compE i X Y) Z)
      = σ R (q && r) • compE (Sum.inl ⟨i, hik⟩) (compE k X Z) Y := by
  have hy1 : GrOperad.par (R := R) q (fst Y) = fst Y := congrArg fst hy
  have hy2 : GrOperad.par (R := R) (xor q e) (snd Y) = snd Y := congrArg snd hy
  have hz1 : GrOperad.par (R := R) r (fst Z) = fst Z := congrArg fst hz
  have hz2 : GrOperad.par (R := R) (xor r e) (snd Z) = snd Z := congrArg snd hz
  ext
  · exact GrOperad.comp_assoc_par hik _ hy1 hz1
  · have t1 : GrOperad.tw (R := R) e (GrOperad.comp (R := R) i (fst X) (fst Y))
        = σ R (e && q) • GrOperad.comp (R := R) i (GrOperad.tw (R := R) e (fst X)) (fst Y) := by
      rw [GrOperad.tw_comp, GrOperad.tw_hom e hy1, map_smul]
    have t2 : GrOperad.tw (R := R) e (GrOperad.comp (R := R) k (fst X) (fst Z))
        = σ R (e && r) • GrOperad.comp (R := R) k (GrOperad.tw (R := R) e (fst X)) (fst Z) := by
      rw [GrOperad.tw_comp, GrOperad.tw_hom e hz1, map_smul]
    have h1 : σ R (e && q) * σ R (q && xor r e) = σ R (q && r) := by
      cases q <;> cases r <;> cases e <;> simp
    have h2 : σ R (xor q e && r) = σ R (q && r) * σ R (e && r) := by
      cases q <;> cases r <;> cases e <;> simp
    simp only [snd_mapE, snd_compE, fst_compE, map_smul, map_add, LinearMap.add_apply,
      LinearMap.smul_apply, t1, t2, GrOperad.comp_assoc_par hik _ hy1 hz1,
      GrOperad.comp_assoc_par hik _ hy2 hz1, GrOperad.comp_assoc_par hik _ hy1 hz2, smul_add,
      smul_smul, h1, h2]
    abel

/-- **The square-zero extension is a graded operad.** -/
noncomputable instance instGrOperad : GrOperad R (DualExt R Q e) where
  par c := parE c
  par_add := parE_add
  par_par := parE_parE
  map σ' := mapE σ'
  map_refl X := by
    ext
    · exact GrOperad.map_refl _
    · exact GrOperad.map_refl _
  map_trans σ' τ X := by
    ext
    · exact GrOperad.map_trans σ' τ _
    · exact GrOperad.map_trans σ' τ _
  map_par σ' c X := by
    ext
    · exact GrOperad.map_par σ' c _
    · exact GrOperad.map_par σ' _ _
  one := oneE
  par_one := by
    ext
    · exact GrOperad.par_one
    · simp only [snd_parE, snd_oneE, map_zero]
  comp i := compE i
  comp_par := compE_par
  map_comp := mapE_compE
  comp_one := compE_one
  one_comp := one_compE
  comp_assoc_seq := compE_assoc_seq
  comp_assoc_par := compE_assoc_par

lemma par_def (c : Bool) (X : DualExt R Q e A) : GrOperad.par (R := R) c X = parE c X := rfl

lemma map_def (σ' : A ≃ B) (X : DualExt R Q e A) : GrOperad.map (R := R) σ' X = mapE σ' X :=
  rfl

lemma one_def : (GrOperad.one (R := R) : DualExt R Q e Unit) = oneE := rfl

lemma comp_def (i : A) (X : DualExt R Q e A) (Y : DualExt R Q e B) :
    GrOperad.comp (R := R) i X Y = compE i X Y := rfl

variable (R Q e) in
/-- **The projection of the square-zero extension onto its constant part**, a morphism of graded
operads. -/
def fstHom : GrOperadHom R (DualExt R Q e) Q where
  app _ _ _ := fst
  app_par _ _ := rfl
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

@[simp] lemma fstHom_app (X : DualExt R Q e A) : (fstHom R Q e).app A X = fst X := rfl

end DualExt

end DualExt

/-! ## Derivations -/

section Der

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **A derivation of parity `e` along a morphism `f`**: linear maps shifting the parities by
`e`, commuting with the relabellings, vanishing on the unit, with the Leibniz rule
`D (x ∘ᵢ y) = D x ∘ᵢ f y + σ(e |x|) f x ∘ᵢ D y`. -/
structure GrDer (f : GrOperadHom R P Q) (e : Bool) where
  /-- The component at a finite input set. -/
  app (A : Type) [Fintype A] [DecidableEq A] : P A →ₗ[R] Q A
  app_par {A : Type} [Fintype A] [DecidableEq A] (c : Bool) (x : P A) :
    app A (GrOperad.par (R := R) c x) = GrOperad.par (R := R) (xor c e) (app A x)
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (σ' : A ≃ B)
    (x : P A) : app B (GrOperad.map (R := R) σ' x) = GrOperad.map (R := R) σ' (app A x)
  app_one : app Unit (GrOperad.one (R := R) (P := P)) = 0
  app_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : P A) (y : P B) :
    app (Without A i ⊕ B) (GrOperad.comp (R := R) i x y)
      = GrOperad.comp (R := R) i (app A x) (f.app B y)
        + GrOperad.comp (R := R) i (GrOperad.tw (R := R) e (f.app A x)) (app B y)

namespace GrDer

variable {f : GrOperadHom R P Q} {e : Bool}

@[ext] lemma ext {D D' : GrDer f e}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), D.app A x = D'.app A x) :
    D = D' := by
  obtain ⟨Da, _, _, _, _⟩ := D
  obtain ⟨Da', _, _, _, _⟩ := D'
  have : @Da = @Da' := by
    funext A _ _
    exact LinearMap.ext (h A)
  subst this
  rfl

variable (f e) in
/-- The zero derivation. -/
def zero : GrDer f e where
  app _ _ _ := 0
  app_par _ _ := by simp only [LinearMap.zero_apply, map_zero]
  app_map _ _ := by simp only [LinearMap.zero_apply, map_zero]
  app_one := rfl
  app_comp _ _ _ := by
    simp only [LinearMap.zero_apply, map_zero, LinearMap.zero_apply, add_zero]

/-- **A derivation shifts the sign twists**: `D (σ(e' |x|) x) = σ(e' e) σ(e' |D x|) D x`. -/
lemma app_tw (D : GrDer f e) (e' : Bool) {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    D.app A (GrOperad.tw (R := R) e' x) = σ R (e' && e) • GrOperad.tw (R := R) e' (D.app A x) := by
  simp only [GrOperad.tw_apply, map_add, map_smul, D.app_par, smul_add, smul_smul]
  cases e <;> cases e' <;> simp [add_comm]

/-- The morphism into the square-zero extension of a derivation: `x ↦ f x + ε D x`. -/
def toHom (D : GrDer f e) : GrOperadHom R P (DualExt R Q e) where
  app A _ _ := LinearMap.prod (f.app A) (D.app A)
  app_par c x := DualExt.ext (f.app_par c x) (D.app_par c x)
  app_map σ' x := DualExt.ext (f.app_map σ' x) (D.app_map σ' x)
  app_one := DualExt.ext f.app_one D.app_one
  app_comp i x y := DualExt.ext (f.app_comp i x y) (D.app_comp i x y)

@[simp] lemma fst_toHom (D : GrDer f e) {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    DualExt.fst (D.toHom.app A x) = f.app A x := rfl

@[simp] lemma snd_toHom (D : GrDer f e) {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    DualExt.snd (D.toHom.app A x) = D.app A x := rfl

/-- The derivation of a morphism into the square-zero extension lifting `f`: the coefficient of
`ε`. -/
def ofHom (φ : GrOperadHom R P (DualExt R Q e))
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A),
      DualExt.fst (φ.app A x) = f.app A x) : GrDer f e where
  app A _ _ := DualExt.snd ∘ₗ φ.app A
  app_par c x := by
    show DualExt.snd (φ.app _ (GrOperad.par (R := R) c x)) = _
    rw [φ.app_par]
    rfl
  app_map σ' x := by
    show DualExt.snd (φ.app _ (GrOperad.map (R := R) σ' x)) = _
    rw [φ.app_map]
    rfl
  app_one := by
    show DualExt.snd (φ.app _ (GrOperad.one (R := R) (P := P))) = 0
    rw [φ.app_one]
    rfl
  app_comp i x y := by
    show DualExt.snd (φ.app _ (GrOperad.comp (R := R) i x y)) = _
    rw [φ.app_comp, DualExt.comp_def, DualExt.snd_compE, hφ, hφ]
    rfl

/-- **Derivations along `f` are the morphisms into the square-zero extension lifting `f`.** -/
def equiv : GrDer f e ≃ {φ : GrOperadHom R P (DualExt R Q e) //
    ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), DualExt.fst (φ.app A x) = f.app A x} where
  toFun D := ⟨D.toHom, fun _ _ _ _ => rfl⟩
  invFun φ := ofHom φ.1 φ.2
  left_inv _ := rfl
  right_inv φ := Subtype.ext (GrOperadHom.ext fun A _ _ x =>
    DualExt.ext (φ.2 A x).symm rfl)

/-- **A derivation along the identity, after a morphism**, is a derivation along it. -/
def compHom {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [GrOperad R P']
    (D : GrDer (GrOperadHom.id R P) e) (g : GrOperadHom R P' P) : GrDer g e where
  app A _ _ := D.app A ∘ₗ g.app A
  app_par c x := by
    simp only [LinearMap.comp_apply, g.app_par, D.app_par]
  app_map σ' x := by
    simp only [LinearMap.comp_apply, g.app_map, D.app_map]
  app_one := by
    simp only [LinearMap.comp_apply, g.app_one, D.app_one]
  app_comp i x y := by
    simp only [LinearMap.comp_apply, g.app_comp, D.app_comp]
    rfl

@[simp] lemma compHom_app {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [GrOperad R P']
    (D : GrDer (GrOperadHom.id R P) e) (g : GrOperadHom R P' P) {A : Type} [Fintype A]
    [DecidableEq A] (x : P' A) : (D.compHom g).app A x = D.app A (g.app A x) := rfl

/-- **A morphism after a derivation along the identity** is a derivation along it. -/
def homComp (g : GrOperadHom R P Q) (D : GrDer (GrOperadHom.id R P) e) : GrDer g e where
  app A _ _ := g.app A ∘ₗ D.app A
  app_par c x := by
    simp only [LinearMap.comp_apply, D.app_par, g.app_par]
  app_map σ' x := by
    simp only [LinearMap.comp_apply, D.app_map, g.app_map]
  app_one := by
    simp only [LinearMap.comp_apply, D.app_one, map_zero]
  app_comp i x y := by
    simp only [LinearMap.comp_apply, D.app_comp, map_add, g.app_comp, g.app_tw]
    rfl

@[simp] lemma homComp_app (g : GrOperadHom R P Q) (D : GrDer (GrOperadHom.id R P) e)
    {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    (homComp g D).app A x = g.app A (D.app A x) := rfl

/-- **The square of an odd derivation is an even derivation.** -/
def sq (D : GrDer (GrOperadHom.id R P) true) : GrDer (GrOperadHom.id R P) false where
  app A _ _ := D.app A ∘ₗ D.app A
  app_par c x := by
    simp only [LinearMap.comp_apply, D.app_par]
    cases c <;> rfl
  app_map σ' x := by
    simp only [LinearMap.comp_apply, D.app_map]
  app_one := by
    simp only [LinearMap.comp_apply, D.app_one, map_zero]
  app_comp i x y := by
    simp only [LinearMap.comp_apply, D.app_comp, map_add, D.app_tw]
    simp only [GrOperadHom.id, LinearMap.id_apply, GrOperad.tw_false, GrOperad.tw_tw,
      Bool.and_self, σ_true, neg_one_smul, map_neg, LinearMap.neg_apply]
    abel

@[simp] lemma sq_app (D : GrDer (GrOperadHom.id R P) true) {A : Type} [Fintype A]
    [DecidableEq A] (x : P A) : D.sq.app A x = D.app A (D.app A x) := rfl

end GrDer

end Der

/-- **The differential of a dg operad is an odd derivation.** -/
def DGOperad.toDer {R : Type u} [CommRing R]
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P] :
    GrDer (GrOperadHom.id R P) true where
  app _ _ _ := DGOperad.d
  app_par c x := by
    rw [DGOperad.d_par, Bool.xor_true]
  app_map σ' x := (DGOperad.map_d σ' x).symm
  app_one := DGOperad.d_one
  app_comp i x y := by
    rw [DGOperad.d_comp, GrOperad.tw_true]
    rfl

/-! ## Derivations out of a free graded operad -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {f : GrOperadHom R (FreeGrL R V) Q} {e : Bool}

/-- **Derivations out of the free graded operad on a graded linear species are determined by
their values on the generators.** -/
theorem der_ext {D D' : GrDer f e}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A),
      D.app A ((ι R V).app A v) = D'.app A ((ι R V).app A v)) : D = D' :=
  GrDer.equiv.injective (Subtype.ext (hom_ext fun A _ _ v => DualExt.ext rfl (h A v)))

/-- **A derivation vanishing on the generators vanishes.** -/
theorem der_eq_zero {D : GrDer f e}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A), D.app A ((ι R V).app A v) = 0) :
    D = GrDer.zero f e :=
  der_ext h

/-- **An odd derivation of a free graded operad squares to zero as soon as its square vanishes on
the generators.** -/
theorem sq_eq_zero {D : GrDer (GrOperadHom.id R (FreeGrL R V)) true}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A),
      D.app A (D.app A ((ι R V).app A v)) = 0)
    {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) : D.app A (D.app A x) = 0 := by
  have := der_eq_zero (D := D.sq) h
  exact congrArg (fun D' : GrDer _ false => D'.app A x) this

/-- A morphism of linear species **of parity `e`**: it shifts the parities by `e`. -/
def IsShift (F : SymSpeciesHom R V Q) (e : Bool) : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (c : Bool) (v : V A),
    F.app A (GrSpecies.par (R := R) c v) = GrOperad.par (R := R) (xor c e) (F.app A v)

/-- The morphism of graded linear species `v ↦ f v + ε F v` into the square-zero extension. -/
noncomputable def liftSp (f : GrOperadHom R (FreeGrL R V) Q) (F : SymSpeciesHom R V Q)
    (hF : IsShift F e) : GrSpeciesHom R V (DualExt R Q e) where
  app A _ _ := LinearMap.prod (f.app A ∘ₗ (ι R V).app A) (F.app A)
  app_map σ' v := DualExt.ext
    (by
      show f.app _ ((ι R V).app _ (SymSpecies.map (R := R) σ' v)) = _
      rw [(ι R V).app_map, GrOperad.toGrSpecies_map, f.app_map]
      rfl)
    (F.app_map σ' v)
  app_par c v := DualExt.ext
    (by
      show f.app _ ((ι R V).app _ (GrSpecies.par (R := R) c v)) = _
      rw [(ι R V).app_par, GrOperad.toGrSpecies_par, f.app_par]
      rfl)
    (hF _ c v)

/-- The morphism into the square-zero extension of the derivation extending `F`. -/
noncomputable def derHom (f : GrOperadHom R (FreeGrL R V) Q) (F : SymSpeciesHom R V Q)
    (hF : IsShift F e) : GrOperadHom R (FreeGrL R V) (DualExt R Q e) :=
  homEquiv.symm (liftSp f F hF)

lemma fst_derHom (f : GrOperadHom R (FreeGrL R V) Q) (F : SymSpeciesHom R V Q)
    (hF : IsShift F e) {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R V A) :
    DualExt.fst ((derHom f F hF).app A x) = f.app A x := by
  have : (DualExt.fstHom R Q e).comp (derHom f F hF) = f := hom_ext fun A _ _ v => by
    rw [GrOperadHom.comp_app, derHom, homEquiv_symm_ι]
    rfl
  exact congrArg (fun g : GrOperadHom R (FreeGrL R V) Q => g.app A x) this

/-- **The derivation along `f` extending values on the generators** commuting with the
relabellings and shifting the parities by `e`. -/
noncomputable def derOf (f : GrOperadHom R (FreeGrL R V) Q) (F : SymSpeciesHom R V Q)
    (hF : IsShift F e) : GrDer f e :=
  GrDer.ofHom (derHom f F hF) fun _ _ _ x => fst_derHom f F hF x

@[simp] lemma derOf_ι (f : GrOperadHom R (FreeGrL R V) Q) (F : SymSpeciesHom R V Q)
    (hF : IsShift F e) {A : Type} [Fintype A] [DecidableEq A] (v : V A) :
    (derOf f F hF).app A ((ι R V).app A v) = F.app A v := by
  show DualExt.snd ((derHom f F hF).app A ((ι R V).app A v)) = _
  rw [derHom, homEquiv_symm_ι]
  rfl

end FreeGrL

end Operad
