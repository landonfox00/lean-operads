/-
# Twisting morphisms out of dg cooperads

For a dg cooperad `C` and a graded operad `P`, **precomposing with the differential of `C`, with
the Koszul sign**, `f ↦ (-1)^{|f|} f ∘ d`, is an odd derivation of the convolution operad
(`ConvOp.preDer`): `(f ∘ᵢ g) ∘ d = (-1)^{|g|} (f ∘ d) ∘ᵢ g + f ∘ᵢ (g ∘ d)` by the coderivation
rule (`ConvOp.preL_d_compC`). It anticommutes with postcomposing with an odd derivation of `P`
and squares to zero (`ConvOp.appDer_post_pre`, `ConvOp.appDer_pre_pre`).

* **Twisting morphisms** out of a coaugmented dg cooperad into a dg operad (`TwistingDG`): odd
  equivariant maps `α` vanishing on the coaugmentation with `d ∘ α + α ∘ d + α ⋆ α = 0`.
* **The cobar construction of a dg cooperad** whose differential kills the coaugmentation
  (`DGCooperad.DOne`): the free graded operad on `s⁻¹ C̄` with the odd derivation extending
  `s⁻¹ c̄ ↦ -(ι ⋆ ι)(c) - s⁻¹ (d c)‾` (`CobarDG.d`). **It squares to zero** (`CobarDG.d_d`): on the
  generators its square is a combination of `(ι ⋆ ι) ⋆ ι - ι ⋆ (ι ⋆ ι)`, which vanishes, and of the
  terms of the Leibniz rule of the two derivations on `ι ⋆ ι`, which cancel. It is a dg operad
  (`CobarDG.instDGOperad`).
* **The cobar adjunction** (`CobarDG.homEquiv`): the morphisms of graded operads out of it
  commuting with the differentials are the twisting morphisms.
-/
import Operad.Twisting
import Operad.DGCooperad
import Operad.GrSubCooperad

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace ConvOp

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [DGCooperad R C] [GrOperad R P]

/-- **The differential shifts the sign twists**: `d (tw e x) = (-1)^e tw e (d x)`. -/
lemma d_tw (e : Bool) (x : C A) :
    DGCooperad.d (R := R) (GrSpecies.tw (R := R) e x)
      = σ R e • GrSpecies.tw (R := R) e (DGCooperad.d (R := R) x) := by
  rw [GrSpecies.tw_apply, GrSpecies.tw_apply, map_add, map_smul, DGCooperad.d_par,
    DGCooperad.d_par, Bool.not_false, Bool.not_true, smul_add, smul_smul, σ_mul_self, one_smul,
    add_comm]

lemma tw_d (e : Bool) (x : C A) :
    GrSpecies.tw (R := R) e (DGCooperad.d (R := R) x)
      = σ R e • DGCooperad.d (R := R) (GrSpecies.tw (R := R) e x) := by
  rw [d_tw, smul_smul, σ_mul_self, one_smul]

/-- **Precomposing with the differential shifts parities by one.** -/
lemma parC_preL_d (b : Bool) (f : ConvOp R C P A) :
    parC b (preL (DGCooperad.d (R := R) (C := C)) f)
      = preL (DGCooperad.d (R := R) (C := C)) (parC (!b) f) := by
  ext x
  simp only [parC_apply, toLin_preL, LinearMap.comp_apply, DGCooperad.d_par, Fintype.sum_bool]
  cases b <;> simp [add_comm]

lemma isParC_preL_d {q : Bool} {g : ConvOp R C P A} (hg : IsParC q g) :
    IsParC (!q) (preL (DGCooperad.d (R := R) (C := C)) g) := by
  rw [← parC_eq_self_iff, parC_preL_d, Bool.not_not, parC_eq_self_iff.2 hg]

lemma mapC_preL_d (σ' : A ≃ B) (f : ConvOp R C P A) :
    mapC σ' (preL (DGCooperad.d (R := R) (C := C)) f)
      = preL (DGCooperad.d (R := R) (C := C)) (mapC σ' f) := by
  ext x
  simp only [mapC_apply, toLin_preL, LinearMap.comp_apply]
  rw [← DGCooperad.map_d]

/-- **Precomposing a composite with the differential**, the differential of `C` being a
coderivation: `(f ∘ᵢ g) ∘ d = (-1)^{|g|} (f ∘ d) ∘ᵢ g + f ∘ᵢ (g ∘ d)`. -/
lemma preL_d_compC (i : A) (f : ConvOp R C P A) {q : Bool} {g : ConvOp R C P B}
    (hg : IsParC q g) :
    preL (DGCooperad.d (R := R) (C := C)) (compC i f g)
      = σ R q • compC i (preL (DGCooperad.d (R := R) (C := C)) f) g
        + compC i f (preL (DGCooperad.d (R := R) (C := C)) g) := by
  ext x
  simp only [toLin_preL, LinearMap.comp_apply, toLin_compC, toLin_add, toLin_smul,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [DGCooperad.decomp_d_tw]
  generalize GrCooperad.decomp (R := R) (C := C) i x = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [map_add, TensorProduct.map_tmul, TensorProduct.map_tmul, map_add, kap_tmul f hg,
      kap_tmul f hg, kap_tmul _ hg, kap_tmul f (isParC_preL_d hg)]
    simp only [mu_tmul, LinearMap.id_apply, toLin_preL, LinearMap.comp_apply]
    rw [tw_d, GrSpecies.tw_tw, Bool.xor_true, map_smul, LinearMap.map_smul₂]
  | add a b ha hb =>
    simp only [map_add, smul_add] at ha hb ⊢
    rw [add_add_add_comm, ha, hb, add_add_add_comm, add_add_add_comm (σ R q • _)]

/-- **Precomposing with the differential of a dg cooperad, with the Koszul sign, is an odd
derivation of the convolution operad**: `f ↦ (-1)^{|f|} f ∘ d`. -/
noncomputable def preDer : GrDer (GrOperadHom.id R (ConvOp R C P)) true where
  app A _ _ := preL (DGCooperad.d (R := R) (C := C)) ∘ₗ GrOperad.tw (R := R) true
  app_par c f := by
    show preL _ (GrOperad.tw (R := R) true (GrOperad.par (R := R) c f))
      = GrOperad.par (R := R) (xor c true) (preL _ (GrOperad.tw (R := R) true f))
    rw [par_def (xor c true), parC_preL_d, Bool.xor_true, Bool.not_not, ← par_def,
      GrOperad.par_tw]
  app_map σ' f := by
    show preL _ (GrOperad.tw (R := R) true (GrOperad.map (R := R) σ' f))
      = GrOperad.map (R := R) σ' (preL _ (GrOperad.tw (R := R) true f))
    rw [← GrOperad.map_tw, map_def, map_def, mapC_preL_d]
  app_one := by
    show preL _ (GrOperad.tw (R := R) true (GrOperad.one (R := R))) = 0
    rw [GrOperad.tw_one]
    ext x
    rw [toLin_preL, LinearMap.comp_apply, one_def, oneC_apply, DGCooperad.counit_d, zero_smul,
      toLin_zero, LinearMap.zero_apply]
  app_comp {A₁ B₁} _ _ _ _ i f g := by
    show preL _ (GrOperad.tw (R := R) true (GrOperad.comp (R := R) i f g))
      = GrOperad.comp (R := R) i (preL _ (GrOperad.tw (R := R) true f)) g
        + GrOperad.comp (R := R) i (GrOperad.tw (R := R) true f)
            (preL _ (GrOperad.tw (R := R) true g))
    have key : ∀ (q : Bool) (g' : ConvOp R C P B₁), IsParC q g' →
        preL (DGCooperad.d (R := R) (C := C))
            (GrOperad.tw (R := R) true (GrOperad.comp (R := R) i f g'))
          = GrOperad.comp (R := R) i
              (preL (DGCooperad.d (R := R) (C := C)) (GrOperad.tw (R := R) true f)) g'
            + GrOperad.comp (R := R) i (GrOperad.tw (R := R) true f)
                (preL (DGCooperad.d (R := R) (C := C)) (GrOperad.tw (R := R) true g')) := by
      intro q g' hg
      have hg' : GrOperad.par (R := R) q g' = g' := parC_eq_self_iff.2 hg
      have htw : GrOperad.tw (R := R) true g' = σ R q • g' := by
        rw [GrOperad.tw_hom true hg', Bool.true_and]
      rw [GrOperad.tw_comp, htw]
      simp only [map_smul, comp_def]
      rw [preL_d_compC i _ hg, smul_add, smul_smul, σ_mul_self, one_smul]
    have e0 := key false (parC false g) (isParC_parC false g)
    have e1 := key true (parC true g) (isParC_parC true g)
    rw [← parC_add g]
    simp only [map_add]
    rw [e0, e1]
    abel

@[simp] lemma toLin_preDer (f : ConvOp R C P A) :
    toLin ((preDer (R := R) (C := C) (P := P)).app A f)
      = toLin (GrOperad.tw (R := R) true f) ∘ₗ DGCooperad.d (R := R) (C := C) := rfl

end ConvOp

/-! ## Precomposition and postcomposition -/

namespace ConvOp

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **Postcomposing with an odd derivation anticommutes with precomposing with the
differential.** -/
lemma appDer_post_pre (δ : GrDer (GrOperadHom.id R Q) true) (f : GrOperad.Inv R (ConvOp R C Q)) :
    GrOperad.Inv.appDer (postDer (C := C) δ) (GrOperad.Inv.appDer (preDer (C := C) (P := Q)) f)
      = -GrOperad.Inv.appDer (preDer (C := C) (P := Q))
          (GrOperad.Inv.appDer (postDer (C := C) δ) f) := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ?_)
  show (postDer (C := C) δ).app A (preL (DGCooperad.d (R := R) (C := C))
      (GrOperad.tw (R := R) true (f.1 A)))
    = -preL (DGCooperad.d (R := R) (C := C))
        (GrOperad.tw (R := R) true ((postDer (C := C) δ).app A (f.1 A)))
  have h := (postDer (C := C) δ).app_tw true (f.1 A)
  rw [Bool.and_self, σ_true, neg_one_smul] at h
  rw [← map_neg, ← h]
  rfl

/-- **Precomposing twice with the differential vanishes.** -/
lemma appDer_pre_pre (f : GrOperad.Inv R (ConvOp R C Q)) :
    GrOperad.Inv.appDer (preDer (C := C) (P := Q))
      (GrOperad.Inv.appDer (preDer (C := C) (P := Q)) f) = 0 := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ?_)
  ext x
  show toLin (GrOperad.tw (R := R) true (preL (DGCooperad.d (R := R) (C := C))
      (GrOperad.tw (R := R) true (f.1 A)))) (DGCooperad.d (R := R) x) = 0
  rw [tw_apply, toLin_preL, LinearMap.comp_apply, d_tw, DGCooperad.d_d, map_zero, smul_zero,
    map_zero, map_zero]

end ConvOp

/-! ## Twisting morphisms out of dg cooperads -/

section TwistingDG

variable (R : Type u) [CommRing R] (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C]
  (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]

/-- **Twisting morphisms** out of a dg cooperad: the odd equivariant maps `α : C → P` vanishing
on the coaugmentation and satisfying the Maurer–Cartan equation `d ∘ α + α ∘ d + α ⋆ α = 0`;
precomposing with the differential of `C` with the Koszul sign is `-(α ∘ d)`. -/
def TwistingDG : Type _ :=
  {α : GrOperad.Inv R (ConvOp R C P) // GrOperad.Inv.IsPar true α ∧ KillsUnit R C P α ∧
    GrOperad.Inv.appDer (ConvOp.postDer (C := C) (DGOperad.toDer (R := R) (P := P))) α
      - GrOperad.Inv.appDer (ConvOp.preDer (C := C) (P := P)) α
      + GrOperad.Inv.star R _ α α = 0}

end TwistingDG

/-! ## The cobar construction of a dg cooperad -/

namespace CobarDG

variable (R : Type u) [CommRing R] (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C] [DGCooperad.DOne R C]

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The internal part of the generator values: `s⁻¹ c̄ ↦ s⁻¹ (d c)‾`. -/
noncomputable def genI (A : Type) [Fintype A] [DecidableEq A] :
    CobarGen R C A →ₗ[R] CobarGr R C A :=
  Submodule.liftQ (GrCooperad.unitSpan R C A)
    (Cobar.ιL R C A ∘ₗ DGCooperad.d (R := R) (C := C)) fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, DGCooperad.d_unitSpan hx, map_zero]

lemma genI_proj (x : C A) :
    genI R C A (GrCooperad.Red.proj R C A x) = Cobar.ιL R C A (DGCooperad.d (R := R) x) :=
  rfl

/-- The generator values of the cobar differential of a dg cooperad:
`s⁻¹ c̄ ↦ -(ι ⋆ ι)(c) - s⁻¹ (d c)‾`. -/
noncomputable def genD (A : Type) [Fintype A] [DecidableEq A] :
    CobarGen R C A →ₗ[R] CobarGr R C A :=
  Cobar.genD R C A - genI R C A

lemma genD_proj (x : C A) :
    genD R C A (GrCooperad.Red.proj R C A x)
      = -ConvOp.toLin ((Cobar.ιι R C).1 A) x - Cobar.ιL R C A (DGCooperad.d (R := R) x) := by
  rw [genD, LinearMap.sub_apply, Cobar.genD_proj, genI_proj]

/-- The generator values, as a morphism of linear species. -/
noncomputable def genDSp : SymSpeciesHom R (CobarGen R C) (CobarGr R C) where
  app A _ _ := genD R C A
  app_map {A B} _ _ _ _ e v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    show genD R C B (GrCooperad.Red.proj R C B (SymSpecies.map (R := R) e x))
      = GrOperad.map (R := R) e (genD R C A (GrCooperad.Red.proj R C A x))
    rw [genD_proj, genD_proj, Cobar.ιι_map, map_sub, map_neg, ← Cobar.ιL_map,
      DGCooperad.map_d]

/-- **The generator values shift parities by one.** -/
lemma isShift_genD : FreeGrL.IsShift (genDSp R C) true := by
  intro A _ _ c v
  obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
  show genD R C A (GrCooperad.Red.proj R C A (GrSpecies.par (R := R) (!c) x))
    = GrOperad.par (R := R) (xor c true) (genD R C A (GrCooperad.Red.proj R C A x))
  have hev := ConvOp.parC_eq_self_iff.1 (Cobar.isPar_ιι R C A)
  rw [genD_proj, genD_proj, hev, DGCooperad.d_par, Cobar.ιL_par, map_sub, map_neg]
  simp only [Bool.not_not, Bool.xor_false, Bool.xor_true]

/-- **The cobar differential of a dg cooperad**: the odd derivation of the free graded operad on
`s⁻¹ C̄` extending `s⁻¹ c̄ ↦ -(ι ⋆ ι)(c) - s⁻¹ (d c)‾`. -/
noncomputable def d : GrDer (GrOperadHom.id R (CobarGr R C)) true :=
  FreeGrL.derOf (GrOperadHom.id R (CobarGr R C)) (genDSp R C) (isShift_genD R C)

lemma d_ιL (x : C A) :
    (d R C).app A (Cobar.ιL R C A x)
      = -ConvOp.toLin ((Cobar.ιι R C).1 A) x - Cobar.ιL R C A (DGCooperad.d (R := R) x) := by
  rw [Cobar.ιL_apply, d, FreeGrL.derOf_ι]
  exact genD_proj R C x

/-- **`d ∘ ι = -(ι ⋆ ι) - ι ∘ d`**, the last term being precomposition with the differential of
`C` with the Koszul sign of the odd `ι`. -/
theorem d_ι :
    GrOperad.Inv.appDer (ConvOp.postDer (C := C) (d R C)) (Cobar.ι R C)
      = -Cobar.ιι R C
        + GrOperad.Inv.appDer (ConvOp.preDer (C := C) (P := CobarGr R C)) (Cobar.ι R C) := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ?_)
  ext x
  have hι : GrOperad.tw (R := R) true ((Cobar.ι R C).1 A) = -(Cobar.ι R C).1 A := by
    rw [GrOperad.tw_hom true (Cobar.isPar_ι R C A), Bool.and_self, σ_true, neg_one_smul]
  show (d R C).app A (Cobar.ιL R C A x)
    = -ConvOp.toLin ((Cobar.ιι R C).1 A) x
      + ConvOp.toLin (GrOperad.tw (R := R) true ((Cobar.ι R C).1 A)) (DGCooperad.d (R := R) x)
  rw [hι, d_ιL, ConvOp.toLin_neg, LinearMap.neg_apply, sub_eq_add_neg]
  rfl

omit [DGCooperad R C] [GrCooperad.Coaug R C] [DGCooperad.DOne R C] in
/-- The algebra of `d² = 0` on the universal twisting morphism. -/
lemma sq_aux {M : Type*} [AddCommGroup M] [Module R M] (Dpost Dpre : M →ₗ[R] M)
    (st : M →ₗ[R] M →ₗ[R] M) (ι : M) {s : R} (hs : s = -1) (h1 : Dpost ι = -st ι ι + Dpre ι)
    (h2 : Dpost (st ι ι) = st (Dpost ι) ι + s • st ι (Dpost ι))
    (h3 : Dpre (st ι ι) = st (Dpre ι) ι + s • st ι (Dpre ι))
    (h4 : Dpost (Dpre ι) = -Dpre (Dpost ι)) (h5 : Dpre (Dpre ι) = 0)
    (hassoc : st (st ι ι) ι = st ι (st ι ι)) : Dpost (Dpost ι) = 0 := by
  subst hs
  rw [h1, map_add, map_neg, h4, h1, map_add, map_neg, h5, add_zero, neg_neg, h2, h3, h1]
  simp only [map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply, hassoc, neg_one_smul]
  abel

/-- **The cobar differential of a dg cooperad squares to zero.** -/
theorem d_d (y : CobarGr R C A) : (d R C).app A ((d R C).app A y) = 0 := by
  refine FreeGrL.sq_eq_zero (fun A _ _ v => ?_) y
  obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
  have hι := Cobar.isPar_ι R C
  have h2 := GrOperad.Inv.appDer_star (ConvOp.postDer (C := C) (d R C)) hι (Cobar.ι R C)
  have h3 := GrOperad.Inv.appDer_star (ConvOp.preDer (C := C) (P := CobarGr R C)) hι
    (Cobar.ι R C)
  have key := sq_aux R _ _ _ _ (rfl : σ R (true && true) = -1) (d_ι R C) h2 h3
    (ConvOp.appDer_post_pre (C := C) (d R C) (Cobar.ι R C))
    (ConvOp.appDer_pre_pre (C := C) (Q := CobarGr R C) (Cobar.ι R C))
    (GrOperad.Inv.assoc_odd (Cobar.ι R C) (Cobar.ι R C) hι)
  have e : ConvOp.toLin ((GrOperad.Inv.appDer (ConvOp.postDer (C := C) (d R C))
      (GrOperad.Inv.appDer (ConvOp.postDer (C := C) (d R C)) (Cobar.ι R C))).1 A) x = 0 := by
    rw [key]
    rfl
  rw [ConvOp.appDer_postDer_apply, ConvOp.appDer_postDer_apply] at e
  exact e

end CobarDG

/-! ## The cobar construction of a dg cooperad as a dg operad -/

section CobarDGOp

variable (R : Type u) [CommRing R] (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C] [DGCooperad.DOne R C]

/-- **The cobar construction of a coaugmented dg cooperad**, a dg operad. -/
def CobarDGOp (A : Type) [Fintype A] [DecidableEq A] : Type (max u v) := CobarGr R C A

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (CobarDGOp R C A) :=
  inferInstanceAs (AddCommGroup (CobarGr R C A))

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : Module R (CobarDGOp R C A) :=
  inferInstanceAs (Module R (CobarGr R C A))

namespace CobarDG

/-- **The cobar construction of a coaugmented dg cooperad is a dg operad.** -/
noncomputable instance instDGOperad : DGOperad R (CobarDGOp R C) :=
  { (inferInstance : GrOperad R (CobarGr R C)) with
    d := fun {A} _ _ => (d R C).app A
    d_d := fun {A} _ _ y => d_d R C (A := A) y
    d_par := fun {A} _ _ b y => by
      have h := (d R C).app_par b y
      rw [Bool.xor_true] at h
      exact h
    map_d := fun {A B} _ _ _ _ e y => ((d R C).app_map e y).symm
    d_one := (d R C).app_one
    d_comp := fun {A B} _ _ _ _ i y z => by
      have h := (d R C).app_comp i y z
      rw [GrOperadHom.id_app, GrOperadHom.id_app, GrOperad.tw_true] at h
      exact h }

end CobarDG

end CobarDGOp

/-! ## The cobar adjunction for dg cooperads -/

section AdjDG

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C] [DGCooperad.DOne R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]

variable (R C P) in
/-- **Morphisms of graded operads out of the cobar construction of a dg cooperad commuting with
the differentials.** -/
def CobarDGHom : Type _ :=
  {φ : GrOperadHom R (CobarGr R C) P // ∀ (A : Type) [Fintype A] [DecidableEq A]
    (y : CobarGr R C A), φ.app A ((CobarDG.d R C).app A y) = DGOperad.d (R := R) (φ.app A y)}

namespace CobarDG

/-- **The Maurer–Cartan equation of `φ ∘ ι` is `d ∘ φ = φ ∘ d` on the generators.** -/
lemma mc_iff (φ : GrOperadHom R (CobarGr R C) P) :
    GrOperad.Inv.appDer (ConvOp.postDer (C := C) (DGOperad.toDer (R := R) (P := P)))
        (Cobar.twOf φ)
      - GrOperad.Inv.appDer (ConvOp.preDer (C := C) (P := P)) (Cobar.twOf φ)
      + GrOperad.Inv.star R _ (Cobar.twOf φ) (Cobar.twOf φ) = 0
      ↔ ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        DGOperad.d (R := R) (φ.app A (Cobar.ιL R C A x))
          = φ.app A ((d R C).app A (Cobar.ιL R C A x)) := by
  have hst : GrOperad.Inv.star R _ (Cobar.twOf φ) (Cobar.twOf φ)
      = GrOperad.Inv.appHom (ConvOp.postHom (C := C) φ) (Cobar.ιι R C) :=
    (GrOperad.Inv.appHom_star _ _ _).symm
  have hpre : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      ConvOp.toLin ((GrOperad.Inv.appDer (ConvOp.preDer (C := C) (P := P))
          (Cobar.twOf φ)).1 A) x
        = -φ.app A (Cobar.ιL R C A (DGCooperad.d (R := R) x)) := by
    intro A _ _ x
    have htw : GrOperad.tw (R := R) true ((Cobar.twOf φ).1 A) = -(Cobar.twOf φ).1 A := by
      rw [GrOperad.tw_hom true (Cobar.isPar_twOf φ A), Bool.and_self, σ_true, neg_one_smul]
    show ConvOp.toLin (GrOperad.tw (R := R) true ((Cobar.twOf φ).1 A))
      (DGCooperad.d (R := R) x) = _
    rw [htw, ConvOp.toLin_neg, LinearMap.neg_apply]
    rfl
  rw [hst]
  constructor
  · intro h A _ _ x
    have h1 : DGOperad.d (R := R) (φ.app A (Cobar.ιL R C A x))
        - ConvOp.toLin ((GrOperad.Inv.appDer (ConvOp.preDer (C := C) (P := P))
            (Cobar.twOf φ)).1 A) x
        + φ.app A (ConvOp.toLin ((Cobar.ιι R C).1 A) x) = 0 :=
      congrArg (fun q : GrOperad.Inv R (ConvOp R C P) => ConvOp.toLin (q.1 A) x) h
    rw [hpre] at h1
    rw [d_ιL, map_sub, map_neg, ← sub_eq_zero, ← h1]
    abel
  · intro h
    refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun x => ?_)
    show DGOperad.d (R := R) (φ.app A (Cobar.ιL R C A x))
        - ConvOp.toLin ((GrOperad.Inv.appDer (ConvOp.preDer (C := C) (P := P))
            (Cobar.twOf φ)).1 A) x
        + φ.app A (ConvOp.toLin ((Cobar.ιι R C).1 A) x) = 0
    rw [hpre, h, d_ιL, map_sub, map_neg]
    abel

/-- **The morphism of a twisting morphism out of a dg cooperad commutes with the
differentials.** -/
lemma homOf_comm (α : GrOperad.Inv R (ConvOp R C P)) (hpar : GrOperad.Inv.IsPar true α)
    (hα : KillsUnit R C P α)
    (hmc : GrOperad.Inv.appDer (ConvOp.postDer (C := C) (DGOperad.toDer (R := R) (P := P))) α
      - GrOperad.Inv.appDer (ConvOp.preDer (C := C) (P := P)) α
      + GrOperad.Inv.star R _ α α = 0) {A : Type} [Fintype A] [DecidableEq A]
    (y : CobarGr R C A) :
    (Cobar.homOf α hpar hα).app A ((d R C).app A y)
      = DGOperad.d (R := R) ((Cobar.homOf α hpar hα).app A y) := by
  have hmc' := (mc_iff (Cobar.homOf α hpar hα)).1 (by rw [Cobar.twOf_homOf]; exact hmc)
  have hder : GrDer.homComp (Cobar.homOf α hpar hα) (d R C)
      = GrDer.compHom (DGOperad.toDer (R := R) (P := P)) (Cobar.homOf α hpar hα) :=
    FreeGrL.der_ext fun A _ _ v => by
      obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
      exact (hmc' A x).symm
  exact congrArg (fun D : GrDer _ true => D.app A y) hder

/-- **The cobar adjunction for dg cooperads**: morphisms of graded operads out of the cobar
construction of a coaugmented dg cooperad commuting with the differentials are the twisting
morphisms, by composition with the universal twisting morphism. -/
noncomputable def homEquiv : CobarDGHom R C P ≃ TwistingDG R C P where
  toFun φ := ⟨Cobar.twOf φ.1, Cobar.isPar_twOf φ.1, Cobar.killsUnit_twOf φ.1,
    (mc_iff φ.1).2 fun A _ _ _ => (φ.2 A _).symm⟩
  invFun α := ⟨Cobar.homOf α.1 α.2.1 α.2.2.1,
    fun _ _ _ y => homOf_comm α.1 α.2.1 α.2.2.1 α.2.2.2 y⟩
  left_inv φ := Subtype.ext (Cobar.homOf_twOf φ.1)
  right_inv α := Subtype.ext (Cobar.twOf_homOf α.1 α.2.1 α.2.2.1)

/-- The twisting morphism of a morphism out of the cobar construction is its composite with the
universal twisting morphism. -/
lemma homEquiv_apply (φ : CobarDGHom R C P) {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    ConvOp.toLin ((homEquiv φ).1.1 A) x = φ.1.app A (Cobar.ιL R C A x) := rfl

end CobarDG

end AdjDG

end Operad
