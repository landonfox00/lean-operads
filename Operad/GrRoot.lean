/-
# The square-zero extension of an augmented graded operad by `V ∘ C`

Let `C` be a graded operad with an augmentation `ε` (`GrAug`): coefficients `C A → R`, invariant
under relabelling, vanishing on odd operations and outside the arities of one element,
multiplicative, with `ε 1 = 1`. The graded composite `V ∘ C` is a `C`-bimodule: `C` acts on the
right by composing at the inputs (`GrComposite.act`), and on the left through `ε`
(`GrComposite.lact`). **The square-zero extension** `C ⋉ (V ∘ C)` (`GrComposite.SqExt`) is the
graded operad of the pairs `(x, ω)` composed by

  `(x, ω) ∘ᵢ (y, ν) = (x ∘ᵢ y, ω ◁ᵢ y + ε(x) ν)`

(`GrComposite.SqExt.instGrOperad`).
-/
import Operad.GrCompAct

universe u v w

namespace Operad

open Function Sym GerBV

/-! ## Augmentations -/

/-- **An augmentation of a graded operad**: coefficients of the unit, a morphism to the unit
operad. -/
structure GrAug (R : Type u) [CommRing R]
    (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrOperad R C] where
  /-- The coefficient of the unit. -/
  u (A : Type) [Fintype A] [DecidableEq A] : C A →ₗ[R] R
  u_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (σ : A ≃ B)
    (x : C A) : u B (GrOperad.map (R := R) σ x) = u A x
  u_par {A : Type} [Fintype A] [DecidableEq A] (x : C A) : u A (GrOperad.par (R := R) true x) = 0
  u_one : u Unit (GrOperad.one (R := R)) = 1
  u_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) (x : C A)
    (y : C B) : u _ (GrOperad.comp (R := R) i x y) = u A x * u B y
  u_eq_zero {A : Type} [Fintype A] [DecidableEq A] (h : IsEmpty (Unit ≃ A)) (x : C A) : u A x = 0

/-- The inputs of a composite into an operation with a single input are those of the inserted
operation. -/
def unitEquiv {A : Type} [DecidableEq A] (e : Unit ≃ A) (i : A) (B : Type) :
    Without A i ⊕ B ≃ B where
  toFun x := match x with
    | Sum.inl a => absurd (e.symm.injective (Subsingleton.elim _ _)) a.2
    | Sum.inr b => b
  invFun b := Sum.inr b
  left_inv := by
    rintro (⟨a, ha⟩ | b)
    · exact absurd (e.symm.injective (Subsingleton.elim _ _)) ha
    · rfl
  right_inv _ := rfl

@[simp] lemma unitEquiv_symm_apply {A : Type} [DecidableEq A] (e : Unit ≃ A) (i : A) {B : Type}
    (b : B) : (unitEquiv e i B).symm b = Sum.inr b := rfl

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrOperad R C]

namespace GrComposite

/-! ## Relabelling and parities -/

section Basic

variable {S S' S'' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']
  [Fintype S''] [DecidableEq S'']

lemma map_refl (x : GrComposite R V C S) : map (Equiv.refl S) x = x :=
  SymSpecies.map_refl (R := R) (V := GrComposite R V C) x

lemma map_trans (e : S ≃ S') (f : S' ≃ S'') (x : GrComposite R V C S) :
    map (e.trans f) x = map f (map e x) :=
  SymSpecies.map_trans (R := R) (V := GrComposite R V C) e f x

lemma map_congr {e e' : S ≃ S'} (h : ∀ s, e s = e' s) (x : GrComposite R V C S) :
    map e x = map e' x := by
  rw [Equiv.ext h]

lemma map_comp_congr (e : S ≃ S') (f : S' ≃ S'') (g : S ≃ S'') (h : ∀ s, f (e s) = g s)
    (x : GrComposite R V C S) : map f (map e x) = map g x := by
  rw [← map_trans]
  exact map_congr h x

lemma map_par' (e : S ≃ S') (b : Bool) (x : GrComposite R V C S) :
    map e (par R V C b x) = par R V C b (map e x) :=
  GrSpecies.map_par (R := R) (V := GrComposite R V C) e b x

lemma par_add' (x : GrComposite R V C S) : par R V C false x + par R V C true x = x :=
  GrSpecies.par_add (R := R) (V := GrComposite R V C) x

lemma par_par' (b b' : Bool) (x : GrComposite R V C S) :
    par R V C b (par R V C b' x) = if b = b' then par R V C b' x else 0 :=
  GrSpecies.par_par (R := R) (V := GrComposite R V C) b b' x

lemma par_par_self' (b : Bool) (x : GrComposite R V C S) :
    par R V C b (par R V C b x) = par R V C b x := by
  rw [par_par', if_pos rfl]

end Basic

/-! ## The left action through the augmentation -/

section LAct

variable (ε : GrAug R C) {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable (R V) in
/-- **The left action of `C` on `V ∘ C` through the augmentation**: an operation with a single
input acts by its unit coefficient, the others by zero. -/
noncomputable def lact (i : A) (x : C A) :
    GrComposite R V C B →ₗ[R] GrComposite R V C (Without A i ⊕ B) :=
  ∑ e : Unit ≃ A, ε.u A x • map (unitEquiv e i B).symm

lemma lact_eq (i : A) (x : C A) (e : Unit ≃ A) (ν : GrComposite R V C B) :
    lact R V ε i x ν = ε.u A x • map (unitEquiv e i B).symm ν := by
  haveI : Subsingleton (Unit ≃ A) := ⟨fun e₁ e₂ => Equiv.ext fun _ => by
    rw [← e.apply_symm_apply (e₁ _), ← e.apply_symm_apply (e₂ _)]⟩
  rw [lact, Fintype.sum_subsingleton _ e]
  rfl

lemma lact_of_isEmpty (h : IsEmpty (Unit ≃ A)) (i : A) (x : C A) :
    lact R V ε i x = (0 : GrComposite R V C B →ₗ[R] GrComposite R V C (Without A i ⊕ B)) := by
  rw [lact, Finset.univ_eq_empty, Finset.sum_empty]

lemma lact_of_u (i : A) {x : C A} (hx : ε.u A x = 0) :
    lact R V ε i x = (0 : GrComposite R V C B →ₗ[R] GrComposite R V C (Without A i ⊕ B)) := by
  simp only [lact, hx, zero_smul, Finset.sum_const_zero]

lemma u_of_ne {i k : A} (hik : i ≠ k) (x : C A) : ε.u A x = 0 :=
  ε.u_eq_zero ⟨fun e => hik (by rw [← e.apply_symm_apply i, ← e.apply_symm_apply k])⟩ x

lemma lact_par_true (i : A) (x : C A) :
    lact R V ε i (GrOperad.par (R := R) true x)
      = (0 : GrComposite R V C B →ₗ[R] GrComposite R V C (Without A i ⊕ B)) :=
  lact_of_u ε i (ε.u_par x)

lemma par_lact (b : Bool) (i : A) (x : C A) (ν : GrComposite R V C B) :
    par R V C b (lact R V ε i x ν) = lact R V ε i x (par R V C b ν) := by
  simp only [lact, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    map_par']

lemma map_lact {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (σ : A ≃ A') (τ : B ≃ B') (i : A) (x : C A) (ν : GrComposite R V C B) :
    map (compEquiv σ τ i) (lact R V ε i x ν)
      = lact R V ε (σ i) (GrOperad.map (R := R) σ x) (map τ ν) := by
  by_cases h : Nonempty (Unit ≃ A)
  · obtain ⟨e⟩ := h
    rw [lact_eq ε i x e, lact_eq ε (σ i) _ (e.trans σ), ε.u_map, map_smul, ← map_trans,
      ← map_trans]
    refine congrArg _ (map_congr ?_ ν)
    intro b
    rfl
  · have h' : IsEmpty (Unit ≃ A') := ⟨fun e => h ⟨e.trans σ.symm⟩⟩
    rw [lact_of_isEmpty ε (not_nonempty_iff.1 h), lact_of_isEmpty ε h', LinearMap.zero_apply,
      LinearMap.zero_apply, map_zero]

variable (R V) in
/-- The left action, bilinear. -/
noncomputable def lactL (i : A) :
    C A →ₗ[R] GrComposite R V C B →ₗ[R] GrComposite R V C (Without A i ⊕ B) where
  toFun x := lact R V ε i x
  map_add' x x' := by
    simp only [lact, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [lact, map_smul, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] lemma lactL_apply (i : A) (x : C A) : lactL R V ε (B := B) i x = lact R V ε i x := rfl

end LAct

/-! ## The square-zero extension -/

set_option linter.unusedVariables false in
variable (R V C) in
/-- **The square-zero extension** `C ⋉ (V ∘ C)` of an augmented graded operad. -/
@[nolint unusedArguments]
def SqExt (ε : GrAug R C) (A : Type) [Fintype A] [DecidableEq A] : Type (max 1 u v w) :=
  C A × GrComposite R V C A

namespace SqExt

variable {ε : GrAug R C}

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (SqExt R V C ε A) :=
  inferInstanceAs (AddCommGroup (C A × GrComposite R V C A))

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : Module R (SqExt R V C ε A) :=
  inferInstanceAs (Module R (C A × GrComposite R V C A))

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The pair `(x, ω)`. -/
noncomputable def mk (x : C A) (ω : GrComposite R V C A) : SqExt R V C ε A := (x, ω)

/-- The operation. -/
noncomputable def fst : SqExt R V C ε A →ₗ[R] C A := LinearMap.fst R (C A) (GrComposite R V C A)

/-- The element of `V ∘ C`. -/
noncomputable def snd : SqExt R V C ε A →ₗ[R] GrComposite R V C A :=
  LinearMap.snd R (C A) (GrComposite R V C A)

@[simp] lemma fst_mk (x : C A) (ω : GrComposite R V C A) : fst (mk (ε := ε) x ω) = x := rfl

@[simp] lemma snd_mk (x : C A) (ω : GrComposite R V C A) : snd (mk (ε := ε) x ω) = ω := rfl

@[ext] lemma ext {X Y : SqExt R V C ε A} (h1 : fst X = fst Y) (h2 : snd X = snd Y) : X = Y :=
  Prod.ext h1 h2

/-- The parity projections. -/
noncomputable def parE (c : Bool) : SqExt R V C ε A →ₗ[R] SqExt R V C ε A :=
  LinearMap.prodMap (GrOperad.par (R := R) c) (par R V C c)

/-- The relabellings. -/
noncomputable def mapE (σ' : A ≃ B) : SqExt R V C ε A →ₗ[R] SqExt R V C ε B :=
  LinearMap.prodMap (GrOperad.map (R := R) σ') (map σ')

/-- The compositions: `(x, ω) ∘ᵢ (y, ν) = (x ∘ᵢ y, ω ◁ᵢ y + ε(x) ν)`. -/
noncomputable def compE (i : A) :
    SqExt R V C ε A →ₗ[R] SqExt R V C ε B →ₗ[R] SqExt R V C ε (Without A i ⊕ B) :=
  LinearMap.mk₂ R (fun X Y => mk (GrOperad.comp (R := R) i (fst X) (fst Y))
      (act R V i (fst Y) (snd X) + lact R V ε i (fst X) (snd Y)))
    (fun X X' Y => by
      ext
      · simp only [fst_mk, map_add, LinearMap.add_apply]
      · simp only [snd_mk, map_add, lact, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
        abel)
    (fun c X Y => by
      ext
      · simp only [fst_mk, map_smul, LinearMap.smul_apply]
      · simp only [snd_mk, map_smul, lact, smul_add, LinearMap.coe_sum, Finset.sum_apply,
          LinearMap.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum])
    (fun X Y Y' => by
      ext
      · simp only [fst_mk, map_add]
      · simp only [snd_mk, map_add, ← actL_apply, LinearMap.add_apply]
        abel)
    (fun c X Y => by
      ext
      · simp only [fst_mk, map_smul]
      · simp only [snd_mk, map_smul, ← actL_apply, LinearMap.smul_apply, smul_add])

@[simp] lemma fst_parE (c : Bool) (X : SqExt R V C ε A) :
    fst (parE c X) = GrOperad.par (R := R) c (fst X) := rfl

@[simp] lemma snd_parE (c : Bool) (X : SqExt R V C ε A) :
    snd (parE c X) = par R V C c (snd X) := rfl

@[simp] lemma fst_mapE (σ' : A ≃ B) (X : SqExt R V C ε A) :
    fst (mapE σ' X) = GrOperad.map (R := R) σ' (fst X) := rfl

@[simp] lemma snd_mapE (σ' : A ≃ B) (X : SqExt R V C ε A) :
    snd (mapE σ' X) = map σ' (snd X) := rfl

@[simp] lemma fst_compE (i : A) (X : SqExt R V C ε A) (Y : SqExt R V C ε B) :
    fst (compE i X Y) = GrOperad.comp (R := R) i (fst X) (fst Y) := rfl

@[simp] lemma snd_compE (i : A) (X : SqExt R V C ε A) (Y : SqExt R V C ε B) :
    snd (compE i X Y) = act R V i (fst Y) (snd X) + lact R V ε i (fst X) (snd Y) := rfl

/-- The unit, `(1, 0)`. -/
noncomputable def oneE : SqExt R V C ε Unit := mk (GrOperad.one (R := R)) 0

@[simp] lemma fst_oneE : fst (oneE (R := R) (V := V) (ε := ε)) = GrOperad.one (R := R) := rfl

@[simp] lemma snd_oneE : snd (oneE (R := R) (V := V) (ε := ε)) = 0 := rfl

lemma parE_add (X : SqExt R V C ε A) : parE false X + parE true X = X := by
  ext
  · simp only [map_add, fst_parE, GrOperad.par_add]
  · simp only [map_add, snd_parE, par_add']

lemma parE_parE (c c' : Bool) (X : SqExt R V C ε A) :
    parE c (parE c' X) = if c = c' then parE c' X else 0 := by
  by_cases h : c = c'
  · subst h
    rw [if_pos rfl]
    ext
    · simp only [fst_parE, GrOperad.par_par_self]
    · simp only [snd_parE, par_par_self']
  · rw [if_neg h]
    ext
    · simp only [fst_parE, GrOperad.par_par, if_neg h]
      rfl
    · simp only [snd_parE, par_par', if_neg h]
      rfl

lemma compE_par (i : A) (p q : Bool) (X : SqExt R V C ε A) (Y : SqExt R V C ε B) :
    parE (xor p q) (compE i (parE p X) (parE q Y)) = compE i (parE p X) (parE q Y) := by
  ext
  · exact GrOperad.comp_par i p q _ _
  · simp only [snd_compE, fst_parE, snd_parE, map_add]
    congr 1
    · rw [par_act _ i _ (GrOperad.par_par_self (R := R) q _), Bool.xor_assoc, Bool.xor_self,
        Bool.xor_false, par_par_self']
    · cases p
      · rw [par_lact, Bool.false_xor, par_par_self']
      · rw [lact_par_true, LinearMap.zero_apply, map_zero]

lemma mapE_compE {A' B' : Type} [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (σ' : A ≃ A') (τ : B ≃ B') (i : A) (X : SqExt R V C ε A) (Y : SqExt R V C ε B) :
    mapE (compEquiv σ' τ i) (compE i X Y) = compE (σ' i) (mapE σ' X) (mapE τ Y) := by
  ext
  · exact GrOperad.map_comp σ' τ i _ _
  · simp only [snd_mapE, snd_compE, fst_mapE, map_add, map_act, map_lact]

lemma compE_one (i : A) (X : SqExt R V C ε A) :
    mapE (rightUnitEquiv i) (compE i X oneE) = X := by
  ext
  · exact GrOperad.comp_one i _
  · simp only [snd_mapE, snd_compE, fst_oneE, snd_oneE, map_zero, add_zero, map_act_one]

lemma one_compE (Y : SqExt R V C ε B) : mapE (leftUnitEquiv B) (compE () oneE Y) = Y := by
  ext
  · exact GrOperad.one_comp _
  · simp only [snd_mapE, snd_compE, fst_oneE, snd_oneE, map_zero, zero_add]
    rw [lact_eq ε () _ (Equiv.refl Unit), ε.u_one, one_smul, map_comp_congr _ _ (Equiv.refl B),
      map_refl]
    intro b
    rfl

lemma compE_assoc_seq {D : Type} [Fintype D] [DecidableEq D] (i : A) (j : B)
    (X : SqExt R V C ε A) (Y : SqExt R V C ε B) (Z : SqExt R V C ε D) :
    mapE (seqEquiv i j D) (compE (Sum.inr j) (compE i X Y) Z) = compE i X (compE j Y Z) := by
  ext
  · exact GrOperad.comp_assoc_seq i j _ _ _
  · simp only [snd_mapE, snd_compE, fst_compE, map_add]
    rw [map_act_seq, add_assoc]
    congr 1
    have h2 : map (seqEquiv i j D) (act R V (Sum.inr j) (fst Z) (lact R V ε i (fst X) (snd Y)))
        = lact R V ε i (fst X) (act R V j (fst Z) (snd Y)) := by
      by_cases hA : Nonempty (Unit ≃ A)
      · obtain ⟨e⟩ := hA
        rw [lact_eq ε i _ e, lact_eq ε i _ e, ← actL_apply, map_smul, map_smul, actL_apply]
        congr 1
        have h := map_act (R := R) (V := V) (unitEquiv e i B).symm (Equiv.refl D) j (fst Z)
          (snd Y)
        rw [GrOperad.map_refl] at h
        have h' : act R V (Sum.inr j : Without A i ⊕ B) (fst Z)
            (map (unitEquiv e i B).symm (snd Y))
            = map (compEquiv (unitEquiv e i B).symm (Equiv.refl D) j)
              (act R V j (fst Z) (snd Y)) := h.symm
        rw [h']
        refine map_comp_congr _ _ _ ?_ _
        rintro (⟨b, hb⟩ | d) <;> rfl
      · simp only [lact_of_isEmpty ε (not_nonempty_iff.1 hA), LinearMap.zero_apply, map_zero]
    have h3 : map (seqEquiv i j D) (lact R V ε (Sum.inr j : Without A i ⊕ B)
          (GrOperad.comp (R := R) i (fst X) (fst Y)) (snd Z))
        = lact R V ε i (fst X) (lact R V ε j (fst Y) (snd Z)) := by
      by_cases hA : Nonempty (Unit ≃ A)
      · obtain ⟨e⟩ := hA
        by_cases hB : Nonempty (Unit ≃ B)
        · obtain ⟨e'⟩ := hB
          rw [lact_eq ε j _ e', map_smul (lact R V ε i (fst X)), lact_eq ε i _ e,
            lact_eq ε (Sum.inr j : Without A i ⊕ B) _ (e'.trans (unitEquiv e i B).symm),
            ε.u_comp, map_smul, smul_smul, mul_comm (ε.u B _), ← map_trans, ← map_trans]
          refine congrArg _ (map_congr ?_ _)
          intro d
          rfl
        · have hy : ε.u B (fst Y) = 0 := ε.u_eq_zero (not_nonempty_iff.1 hB) _
          rw [lact_of_u ε _ (show ε.u _ (GrOperad.comp (R := R) i (fst X) (fst Y)) = 0 by
            rw [ε.u_comp, hy, mul_zero]), lact_of_u ε j hy]
          simp only [LinearMap.zero_apply, map_zero]
      · have hx : ε.u A (fst X) = 0 := ε.u_eq_zero (not_nonempty_iff.1 hA) _
        rw [lact_of_u ε i hx, lact_of_u ε _ (show ε.u _ (GrOperad.comp (R := R) i (fst X)
          (fst Y)) = 0 by rw [ε.u_comp, hx, zero_mul])]
        simp only [LinearMap.zero_apply, map_zero]
    rw [h2, h3]

lemma compE_assoc_par {D : Type} [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k)
    (X : SqExt R V C ε A) {q r : Bool} {Y : SqExt R V C ε B} {Z : SqExt R V C ε D}
    (hy : parE q Y = Y) (hz : parE r Z = Z) :
    mapE (parEquiv hik B D) (compE (Sum.inl ⟨k, Ne.symm hik⟩) (compE i X Y) Z)
      = σ R (q && r) • compE (Sum.inl ⟨i, hik⟩) (compE k X Z) Y := by
  have hy1 : GrOperad.par (R := R) q (fst Y) = fst Y := congrArg fst hy
  have hz1 : GrOperad.par (R := R) r (fst Z) = fst Z := congrArg fst hz
  have hx : ε.u A (fst X) = 0 := u_of_ne ε hik _
  ext
  · exact GrOperad.comp_assoc_par hik _ hy1 hz1
  · have h1 : ε.u _ (GrOperad.comp (R := R) i (fst X) (fst Y)) = 0 := by
      rw [ε.u_comp, hx, zero_mul]
    have h2 : ε.u _ (GrOperad.comp (R := R) k (fst X) (fst Z)) = 0 := by
      rw [ε.u_comp, hx, zero_mul]
    simp only [snd_mapE, snd_compE, fst_compE, map_smul, lact_of_u ε _ hx, lact_of_u ε _ h1,
      lact_of_u ε _ h2, LinearMap.zero_apply, add_zero]
    exact map_act_par hik hy1 hz1 _

/-- **The square-zero extension is a graded operad.** -/
noncomputable instance instGrOperad : GrOperad R (SqExt R V C ε) where
  par c := parE c
  par_add := parE_add
  par_par := parE_parE
  map σ' := mapE σ'
  map_refl X := by
    ext
    · exact GrOperad.map_refl _
    · exact map_refl _
  map_trans σ' τ X := by
    ext
    · exact GrOperad.map_trans σ' τ _
    · exact map_trans σ' τ _
  map_par σ' c X := by
    ext
    · exact GrOperad.map_par σ' c _
    · exact map_par' σ' c _
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

lemma par_def (c : Bool) (X : SqExt R V C ε A) : GrOperad.par (R := R) c X = parE c X := rfl

lemma map_def (σ' : A ≃ B) (X : SqExt R V C ε A) : GrOperad.map (R := R) σ' X = mapE σ' X :=
  rfl

lemma one_def : (GrOperad.one (R := R) : SqExt R V C ε Unit) = oneE := rfl

lemma comp_def (i : A) (X : SqExt R V C ε A) (Y : SqExt R V C ε B) :
    GrOperad.comp (R := R) i X Y = compE i X Y := rfl

variable (R V C ε) in
/-- **The projection onto the operations**, a morphism of graded operads. -/
noncomputable def fstHom : GrOperadHom R (SqExt R V C ε) C where
  app _ _ _ := fst
  app_par _ _ := rfl
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

@[simp] lemma fstHom_app (X : SqExt R V C ε A) : (fstHom R V C ε).app A X = fst X := rfl

end SqExt

end GrComposite

end Operad
