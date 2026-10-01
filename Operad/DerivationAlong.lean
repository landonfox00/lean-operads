/-
# Derivations along a morphism, and lifts to the deformed operads

Let `f : F → P` be a morphism of symmetric operads in `R`-modules. A **derivation along `f`**
(`SymDerivationAlong f`) is an equivariant family of linear maps `D : F(A) → P(A)` with the Leibniz
rule `D(x ∘ᵢ y) = D x ∘ᵢ f y + f x ∘ᵢ D y`. It kills the unit (`SymDerivationAlong.app_one`), the
derivations along `f` are closed under sums, negatives and scalar multiples, and a derivation `D` of
`P` gives the derivation `D ∘ f` along `f` (`SymDerivation.compHom`).

For a two-cocycle `ω` of `P` (`Operad.Deformation`), a **lift of `f`** to the deformed operad `P_ω`
is a morphism `F → P_ω` with first component `f`.

* **The lifts of `f` form a torsor under the derivations along `f`**: the difference of the second
  components of two lifts is a derivation along `f` (`SymDerivationAlong.ofLifts`), and adding a
  derivation along `f` to the second component of a lift gives a lift (`Deformed.liftAdd`).
* **The derivations along `f` are the lifts of `f` to the trivial deformation `P[ε]`**
  (`SymDerivationAlong.liftEquiv`), as the derivations of `P` are the lifts of the identity
  (`SymDerivation.liftEquiv`).
* **Out of a free operad** `Lin R (FreeSet T)` a morphism is a choice of generator values
  (`FreeSet.linHom`, `Pres.lin_hom_ext`), and so is a derivation along `f`
  (`SymDerivationAlong.freeEquiv`; Merkulov and Vallette, *Deformation theory of representations
  of prop(erad)s I*, Lemma 14); and `f` has a lift to every `P_ω`, sending each generator `g` to
  `(f g, 0)` (`Deformed.freeLift`).
-/
import Operad.Deformation
import Operad.SymPresentation

universe u v w w'

namespace Operad

open Sym SetOperad

variable {R : Type u} [CommRing R]
  {F : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (F A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (F A)] [SymOperad R F]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-! ## Derivations along a morphism -/

/-- **A derivation along a morphism** `f : F → P`: an equivariant family of linear maps
`D : F(A) → P(A)` with the Leibniz rule `D(x ∘ᵢ y) = D x ∘ᵢ f y + f x ∘ᵢ D y`. -/
structure SymDerivationAlong (f : SymOperadHom R F P) where
  /-- The component at a finite input set. -/
  app (A : Type) [Fintype A] [DecidableEq A] : F A →ₗ[R] P A
  /-- The components commute with relabelling. -/
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : F A) : app B (SymOperad.map (R := R) e x) = SymOperad.map (R := R) e (app A x)
  /-- The Leibniz rule along `f`. -/
  app_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : F A) (y : F B) :
    app _ (SymOperad.comp (R := R) i x y)
      = SymOperad.comp (R := R) i (app A x) (f.app B y)
        + SymOperad.comp (R := R) i (f.app A x) (app B y)

namespace SymDerivationAlong

variable {f : SymOperadHom R F P} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B]

@[ext] lemma ext {D D' : SymDerivationAlong f}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : F A), D.app A x = D'.app A x) :
    D = D' := by
  obtain ⟨Da, _, _⟩ := D
  obtain ⟨D'a, _, _⟩ := D'
  have : @Da = @D'a := by
    funext A _ _
    exact LinearMap.ext (h A)
  subst this
  rfl

/-- **A derivation along a morphism kills the unit.** -/
theorem app_one (D : SymDerivationAlong f) : D.app Unit (SymOperad.one R) = 0 := by
  have h := D.app_comp () (SymOperad.one R) (SymOperad.one R)
  rw [f.app_one, SymOperad.comp_one' (R := R), SymOperad.comp_one' (R := R),
    SymOperad.one_comp' (R := R), D.app_map] at h
  have h2 : SymOperad.map (R := R) (leftUnitEquiv Unit).symm (D.app Unit (SymOperad.one R)) = 0 :=
    by linear_combination (norm := module) (-1 : R) • h
  exact SymOperad.map_injective (R := R) _ (h2.trans (map_zero _).symm)

/-! ### Linear combinations -/

instance : Zero (SymDerivationAlong f) :=
  ⟨{ app := fun _ _ _ => 0
     app_map := fun _ _ => by simp
     app_comp := fun _ _ _ => by simp }⟩

instance : Add (SymDerivationAlong f) :=
  ⟨fun D D' =>
    { app := fun A _ _ => D.app A + D'.app A
      app_map := fun e x => by simp only [LinearMap.add_apply, map_add, D.app_map, D'.app_map]
      app_comp := fun i x y => by
        simp only [LinearMap.add_apply, D.app_comp, D'.app_comp, map_add, LinearMap.add_apply]
        abel }⟩

instance : Neg (SymDerivationAlong f) :=
  ⟨fun D =>
    { app := fun A _ _ => -D.app A
      app_map := fun e x => by simp only [LinearMap.neg_apply, map_neg, D.app_map]
      app_comp := fun i x y => by
        simp only [LinearMap.neg_apply, D.app_comp, map_neg, LinearMap.neg_apply, neg_add] }⟩

instance : Sub (SymDerivationAlong f) :=
  ⟨fun D D' =>
    { app := fun A _ _ => D.app A - D'.app A
      app_map := fun e x => by simp only [LinearMap.sub_apply, map_sub, D.app_map, D'.app_map]
      app_comp := fun i x y => by
        simp only [LinearMap.sub_apply, D.app_comp, D'.app_comp, map_sub, LinearMap.sub_apply]
        abel }⟩

instance : SMul R (SymDerivationAlong f) :=
  ⟨fun c D =>
    { app := fun A _ _ => c • D.app A
      app_map := fun e x => by simp only [LinearMap.smul_apply, map_smul, D.app_map]
      app_comp := fun i x y => by
        simp only [LinearMap.smul_apply, D.app_comp, map_smul, LinearMap.smul_apply, smul_add] }⟩

@[simp] lemma zero_app (x : F A) : (0 : SymDerivationAlong f).app A x = 0 := rfl

@[simp] lemma add_app (D D' : SymDerivationAlong f) (x : F A) :
    (D + D').app A x = D.app A x + D'.app A x := rfl

@[simp] lemma neg_app (D : SymDerivationAlong f) (x : F A) : (-D).app A x = -D.app A x := rfl

@[simp] lemma sub_app (D D' : SymDerivationAlong f) (x : F A) :
    (D - D').app A x = D.app A x - D'.app A x := rfl

@[simp] lemma smul_app (c : R) (D : SymDerivationAlong f) (x : F A) :
    (c • D).app A x = c • D.app A x := rfl

end SymDerivationAlong

/-- **A derivation of `P` composed with a morphism `f : F → P`** is a derivation along `f`. -/
def SymDerivation.compHom (D : SymDerivation R P) (f : SymOperadHom R F P) :
    SymDerivationAlong f where
  app A _ _ := D.app A ∘ₗ f.app A
  app_map e x := by simp only [LinearMap.comp_apply, f.app_map, D.app_map]
  app_comp i x y := by simp only [LinearMap.comp_apply, f.app_comp, D.app_comp]

@[simp] lemma SymDerivation.compHom_app (D : SymDerivation R P) (f : SymOperadHom R F P)
    {A : Type} [Fintype A] [DecidableEq A] (x : F A) :
    (D.compHom f).app A x = D.app A (f.app A x) := rfl

/-! ## Lifts to the deformed operads -/

section Lifts

variable {ω : SymCochain R P} [Fact ω.IsCocycle] {f : SymOperadHom R F P}
  {A : Type} [Fintype A] [DecidableEq A]

/-- **The difference of two lifts is a derivation**: if `Φ, Ψ : F → P_ω` both have first
component `f`, then `x ↦ Φ₂ x - Ψ₂ x` is a derivation along `f`. -/
def SymDerivationAlong.ofLifts (Φ Ψ : SymOperadHom R F (Deformed ω))
    (hΦ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : F A), Deformed.fst (Φ.app A x) = f.app A x)
    (hΨ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : F A),
      Deformed.fst (Ψ.app A x) = f.app A x) :
    SymDerivationAlong f where
  app A _ _ := (Deformed.sndL ω A).comp (Φ.app A) - (Deformed.sndL ω A).comp (Ψ.app A)
  app_map e x := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, Deformed.sndL_apply, Φ.app_map,
      Ψ.app_map, Deformed.snd_symMap, map_sub]
  app_comp i x y := by
    have h := congrArg Deformed.snd (Φ.app_comp i x y)
    have h' := congrArg Deformed.snd (Ψ.app_comp i x y)
    simp only [Deformed.snd_symComp, hΦ, hΨ] at h h'
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, Deformed.sndL_apply, h, h', map_sub,
      LinearMap.sub_apply]
    abel

@[simp] lemma SymDerivationAlong.ofLifts_app (Φ Ψ : SymOperadHom R F (Deformed ω))
    (hΦ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : F A), Deformed.fst (Φ.app A x) = f.app A x)
    (hΨ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : F A), Deformed.fst (Ψ.app A x) = f.app A x)
    (x : F A) :
    (SymDerivationAlong.ofLifts Φ Ψ hΦ hΨ).app A x
      = Deformed.snd (Φ.app A x) - Deformed.snd (Ψ.app A x) := rfl

/-- **A lift plus a derivation is a lift**: if `Φ : F → P_ω` has first component `f` and `D` is a
derivation along `f`, then `x ↦ (f x, Φ₂ x + D x)` is a morphism `F → P_ω`. -/
def Deformed.liftAdd (Φ : SymOperadHom R F (Deformed ω))
    (hΦ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : F A), Deformed.fst (Φ.app A x) = f.app A x)
    (D : SymDerivationAlong f) : SymOperadHom R F (Deformed ω) where
  app A _ _ :=
    { toFun := fun x => Deformed.mk (f.app A x) (Deformed.snd (Φ.app A x) + D.app A x)
      map_add' := fun x y => by
        ext
        · simp
        · simp only [map_add, Deformed.snd_mk, Deformed.snd_add]
          abel
      map_smul' := fun c x => by ext <;> simp [smul_add] }
  app_map e x := by
    ext
    · exact f.app_map e x
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, Deformed.snd_mk, Deformed.snd_symMap,
        Φ.app_map, D.app_map, map_add]
  app_one := by
    ext
    · exact f.app_one
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, Deformed.snd_mk, Φ.app_one, Deformed.snd_one,
        D.app_one, add_zero]
  app_comp i x y := by
    have h := congrArg Deformed.snd (Φ.app_comp i x y)
    simp only [Deformed.snd_symComp, hΦ] at h
    ext
    · exact f.app_comp i x y
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, Deformed.snd_mk, Deformed.snd_symComp,
        Deformed.fst_mk, h, D.app_comp, map_add, LinearMap.add_apply]
      abel

@[simp] lemma Deformed.fst_liftAdd (Φ : SymOperadHom R F (Deformed ω))
    (hΦ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : F A), Deformed.fst (Φ.app A x) = f.app A x)
    (D : SymDerivationAlong f) (x : F A) :
    Deformed.fst ((Deformed.liftAdd Φ hΦ D).app A x) = f.app A x := rfl

@[simp] lemma Deformed.snd_liftAdd (Φ : SymOperadHom R F (Deformed ω))
    (hΦ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : F A), Deformed.fst (Φ.app A x) = f.app A x)
    (D : SymDerivationAlong f) (x : F A) :
    Deformed.snd ((Deformed.liftAdd Φ hΦ D).app A x) = Deformed.snd (Φ.app A x) + D.app A x :=
  rfl

end Lifts

/-! ## Derivations along `f` are the lifts of `f` to `P[ε]` -/

namespace SymDerivationAlong

variable {f : SymOperadHom R F P} {A : Type} [Fintype A] [DecidableEq A]

/-- The morphism `x ↦ (f x, D x)` into `P[ε]`. -/
def lift (D : SymDerivationAlong f) :
    SymOperadHom R F (Deformed (SymCochain.zero : SymCochain R P)) where
  app A _ _ :=
    { toFun := fun x => Deformed.mk (f.app A x) (D.app A x)
      map_add' := fun x y => by rw [map_add, map_add, Deformed.mk_add]
      map_smul' := fun c x => by ext <;> simp }
  app_map e x := by
    ext
    · exact f.app_map e x
    · exact D.app_map e x
  app_one := by
    ext
    · exact f.app_one
    · exact D.app_one
  app_comp i x y := by
    ext
    · exact f.app_comp i x y
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, Deformed.snd_mk, Deformed.snd_symComp,
        Deformed.fst_mk, SymCochain.zero_apply, add_zero, D.app_comp]

@[simp] lemma fst_lift (D : SymDerivationAlong f) (x : F A) :
    Deformed.fst (D.lift.app A x) = f.app A x := rfl

@[simp] lemma snd_lift (D : SymDerivationAlong f) (x : F A) :
    Deformed.snd (D.lift.app A x) = D.app A x := rfl

/-- **The derivations along `f` are the morphisms `F → P[ε]` lifting `f`.** -/
def liftEquiv : SymDerivationAlong f ≃
    {Φ : SymOperadHom R F (Deformed (SymCochain.zero : SymCochain R P)) //
      ∀ (A : Type) [Fintype A] [DecidableEq A] (x : F A), Deformed.fst (Φ.app A x) = f.app A x}
    where
  toFun D := ⟨D.lift, fun _ _ _ _ => rfl⟩
  invFun Φ :=
    { app := fun A _ _ => (Deformed.sndL _ A).comp (Φ.1.app A)
      app_map := fun e x => by
        simp only [LinearMap.coe_comp, Function.comp_apply, Deformed.sndL_apply, Φ.1.app_map]
        rfl
      app_comp := fun i x y => by
        have h := congrArg Deformed.snd (Φ.1.app_comp i x y)
        simp only [Deformed.snd_symComp, Φ.2, SymCochain.zero_apply, add_zero] at h
        simp only [LinearMap.coe_comp, Function.comp_apply, Deformed.sndL_apply, h] }
  left_inv D := by ext; rfl
  right_inv Φ := by
    apply Subtype.ext
    ext A _ _ x
    · exact (Φ.2 A x).symm
    · rfl

end SymDerivationAlong

/-! ## Out of a free operad -/

section Free

variable {T : ℕ → Type w'}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

variable (R) in
/-- **The morphism out of the free operad given by generator values.** -/
noncomputable def FreeSet.linHom (v : ∀ n, T n → Q (Fin n)) :
    SymOperadHom R (Lin R (FreeSet T)) Q :=
  Operad.linHomEquiv R (FreeSet.homEquiv.symm fun n g => Und.of R Q (v n g))

@[simp] lemma FreeSet.linHom_gen (v : ∀ n, T n → Q (Fin n)) {n : ℕ} (g : T n) :
    (FreeSet.linHom R v).app (Fin n) (Finsupp.single (Pres.gen g) 1) = v n g := by
  show Finsupp.lift (Q _) R (FreeSet T _) _ (Finsupp.single (Pres.gen g) 1) = _
  simp
  rfl

/-- **A derivation along a morphism out of a free operad is its values on the generators**
(Merkulov and Vallette, Lemma 14). -/
noncomputable def SymDerivationAlong.freeEquiv (f : SymOperadHom R (Lin R (FreeSet T)) P) :
    SymDerivationAlong f ≃ (∀ n, T n → P (Fin n)) where
  toFun D n g := D.app _ (Finsupp.single (Pres.gen g) 1)
  invFun v := SymDerivationAlong.liftEquiv.symm
    ⟨FreeSet.linHom R fun n g =>
        Deformed.mk (ω := SymCochain.zero) (f.app _ (Finsupp.single (Pres.gen g) 1)) (v n g),
      fun A _ _ x => by
        have h : (Deformed.fstHom SymCochain.zero).comp (FreeSet.linHom R fun n g =>
            Deformed.mk (ω := SymCochain.zero) (f.app _ (Finsupp.single (Pres.gen g) 1)) (v n g))
              = f :=
          Pres.lin_hom_ext fun n g => by
            simp only [SymOperadHom.comp_app, FreeSet.linHom_gen, Deformed.fstHom_app,
              Deformed.fst_mk]
        exact congrArg (fun φ : SymOperadHom R _ P => φ.app A x) h⟩
  left_inv D := by
    apply SymDerivationAlong.liftEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    apply Pres.lin_hom_ext
    intro n g
    rw [FreeSet.linHom_gen]
    rfl
  right_inv v := by
    funext n g
    show Deformed.snd ((FreeSet.linHom R _).app _ _) = _
    rw [FreeSet.linHom_gen, Deformed.snd_mk]

@[simp] lemma SymDerivationAlong.freeEquiv_apply (f : SymOperadHom R (Lin R (FreeSet T)) P)
    (D : SymDerivationAlong f) (n : ℕ) (g : T n) :
    SymDerivationAlong.freeEquiv f D n g = D.app _ (Finsupp.single (Pres.gen g) 1) := rfl

@[simp] lemma SymDerivationAlong.freeEquiv_symm_gen (f : SymOperadHom R (Lin R (FreeSet T)) P)
    (v : ∀ n, T n → P (Fin n)) {n : ℕ} (g : T n) :
    ((SymDerivationAlong.freeEquiv f).symm v).app _ (Finsupp.single (Pres.gen g) 1) = v n g :=
  congrFun (congrFun ((SymDerivationAlong.freeEquiv f).apply_symm_apply v) n) g

/-- **Derivations along a morphism out of a free operad agree when they agree on the
generators.** -/
lemma SymDerivationAlong.free_ext {f : SymOperadHom R (Lin R (FreeSet T)) P}
    {D D' : SymDerivationAlong f}
    (h : ∀ (n : ℕ) (g : T n),
      D.app _ (Finsupp.single (Pres.gen g) 1) = D'.app _ (Finsupp.single (Pres.gen g) 1)) :
    D = D' :=
  (SymDerivationAlong.freeEquiv f).injective (funext fun n => funext fun g => h n g)

variable (ω : SymCochain R P) [Fact ω.IsCocycle]

/-- **The lift of a morphism out of a free operad to a deformed operad** `P_ω`, sending each
generator `g` to `(f g, 0)`. -/
noncomputable def Deformed.freeLift (f : SymOperadHom R (Lin R (FreeSet T)) P) :
    SymOperadHom R (Lin R (FreeSet T)) (Deformed ω) :=
  FreeSet.linHom R fun _ g => Deformed.mk (f.app _ (Finsupp.single (Pres.gen g) 1)) 0

@[simp] lemma Deformed.fst_freeLift (f : SymOperadHom R (Lin R (FreeSet T)) P)
    {A : Type} [Fintype A] [DecidableEq A] (x : Lin R (FreeSet T) A) :
    Deformed.fst ((Deformed.freeLift ω f).app A x) = f.app A x := by
  have h : (Deformed.fstHom ω).comp (Deformed.freeLift ω f) = f :=
    Pres.lin_hom_ext fun n g => by
      simp only [Deformed.freeLift, SymOperadHom.comp_app, FreeSet.linHom_gen,
        Deformed.fstHom_app, Deformed.fst_mk]
  exact congrArg (fun φ : SymOperadHom R _ P => φ.app A x) h

@[simp] lemma Deformed.snd_freeLift_gen (f : SymOperadHom R (Lin R (FreeSet T)) P) {n : ℕ}
    (g : T n) :
    Deformed.snd ((Deformed.freeLift ω f).app _ (Finsupp.single (Pres.gen g) 1)) = 0 := by
  rw [Deformed.freeLift, FreeSet.linHom_gen, Deformed.snd_mk]

end Free

end Operad
