/-
# Cobar constructions of quasi-isomorphic dg cooperads

For a coaugmented dg cooperad `C` whose differential kills the coaugmentation, the differential of
the cobar construction `ΩC` is `-δ + d_Ω` (`CobarDG.d_app_eq_totD`): `δ` the derivation extending
the differential `d̄` of the generators `s⁻¹ C̄` (`CobarDG.redD`), and `d_Ω` the cobar
differential of the underlying graded cooperad, which **raises the number of vertices by one**
(`CobarMap.d_mem_vx`): on the generators it is `-(ι ⋆ ι)`, of two vertices. A morphism of
coaugmented dg cooperads `f` induces a morphism `f̄` of the generators (`CobarMap.redMap`) and the
morphism of free graded operads `Ωf = T(f̄)` (`CobarMap.map`), commuting with both parts of the
differentials (`CobarMap.d_map`).

Over a field of characteristic zero, for **reduced** cooperads (spanned by the coaugmentation in
the arities at most one), the comparison of the filtrations by the number of vertices
(`FreeGrL.CompareData`) gives:

* **`Ωf` is a quasi-isomorphism iff `f` is one in the arities at least two**
  (`CobarDG.map_bijective_iff`), quasi-isomorphisms being the bijections on homology
  (`QIso.bijective_iff`).
-/
import Operad.FreeGrCompare
import Operad.BarCobarQIso

universe u v w

namespace Operad

open Sym GerBV

/-! ## Quasi-isomorphisms and homology -/

namespace QIso

variable {R : Type u} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {D : M →ₗ[R] M} {D' : M' →ₗ[R] M'}

/-- **A chain map is a quasi-isomorphism iff it is surjective and injective on homology.** -/
theorem bijective_iff (F : M →ₗ[R] M') (hF : ∀ v, F (D v) = D' (F v)) :
    Function.Bijective (Homology.map F hF) ↔ Surj ⊤ ⊤ D D' F ∧ Inj ⊤ ⊤ D D' F := by
  constructor
  · rintro ⟨hi, hs⟩
    refine ⟨fun y _ hy => ?_, fun x _ hx z _ hz => ?_⟩
    · obtain ⟨c, hc⟩ := hs (Homology.mk D' ⟨y, hy⟩)
      obtain ⟨x, rfl⟩ := Homology.mk_surjective D c
      rw [Homology.map_mk, Homology.mk_eq_mk_iff] at hc
      obtain ⟨v, hv⟩ := hc
      exact ⟨x.1, Submodule.mem_top, x.2, v, Submodule.mem_top, hv.symm⟩
    · have h0 : Homology.map F hF (Homology.mk D ⟨x, hx⟩)
          = Homology.map F hF (Homology.mk D 0) := by
        rw [Homology.map_mk, Homology.map_mk, Homology.mk_eq_mk_iff]
        refine ⟨z, ?_⟩
        show D' z = F x - F 0
        rw [map_zero, sub_zero, hz]
      obtain ⟨v, hv⟩ := (Homology.mk_eq_mk_iff (d := D) ⟨x, hx⟩ 0).1 (hi h0)
      exact ⟨v, Submodule.mem_top, by simpa using hv⟩
  · rintro ⟨hs, hi⟩
    refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => ?_, fun c => ?_⟩
    · obtain ⟨x, rfl⟩ := Homology.mk_surjective D c
      rw [Homology.map_mk] at hc
      obtain ⟨v, hv⟩ := (Homology.mk_eq_mk_iff (d := D') _ 0).1 (hc.trans (map_zero _).symm)
      obtain ⟨z, _, hz⟩ := hi x.1 Submodule.mem_top x.2 v Submodule.mem_top
        (by simpa using hv.symm)
      rw [← map_zero (Homology.mk D), Homology.mk_eq_mk_iff]
      exact ⟨z, by simpa using hz⟩
    · obtain ⟨y, rfl⟩ := Homology.mk_surjective D' c
      obtain ⟨x, _, hx, z, _, hz⟩ := hs y.1 Submodule.mem_top y.2
      refine ⟨Homology.mk D ⟨x, hx⟩, ?_⟩
      rw [Homology.map_mk, Homology.mk_eq_mk_iff]
      exact ⟨z, hz.symm⟩

end QIso

/-! ## Derivations raising the number of vertices -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {X : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (X A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (X A)] [GrSpecies R X]

/-- **An odd derivation with values of two vertices on the generators raises the number of
vertices by one**: it satisfies `[N, D] = D`, `N` the vertex count. -/
theorem der_mem_vx {D : GrDer (GrOperadHom.id R (FreeGrL R X)) true}
    (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : X A),
      D.app A ((ι R X).app A v) ∈ vx R X 2 A)
    {A : Type} [Fintype A] [DecidableEq A] {k : ℕ} {x : FreeGrL R X A} (hx : x ∈ vx R X k A) :
    D.app A x ∈ vx R X (k + 1) A := by
  have h : (derSp (GrSpEnd.id R X)).gcomm D = D := der_ext fun A _ _ v => by
    rw [GrDer.gcomm_app, mem_eig.1 (hD A v), derSp_ι, GrSpEnd.id_app, Bool.false_and, σ_false,
      one_smul, Nat.cast_two, two_smul, add_sub_cancel_right]
  have e := congrArg (fun D' : GrDer (GrOperadHom.id R (FreeGrL R X)) true => D'.app A x) h
  simp only [GrDer.gcomm_app, Bool.false_and, σ_false, one_smul] at e
  rw [mem_eig.1 hx, map_smul] at e
  refine mem_eig.2 ?_
  rw [Nat.cast_add, Nat.cast_one]
  linear_combination (norm := module) e

/-- `-δ + D₁` for the zero endomorphism is `D₁`. -/
lemma totD_zero_app (D₁ : GrDer (GrOperadHom.id R (FreeGrL R X)) true) {A : Type} [Fintype A]
    [DecidableEq A] (y : FreeGrL R X A) : totD (GrSpEnd.zero R X true) D₁ A y = D₁.app A y := by
  rw [totD, LinearMap.add_apply, LinearMap.neg_apply, derSp_zero_app, neg_zero, zero_add]

end FreeGrL

/-! ## The cobar construction of a morphism of graded cooperads -/

namespace CobarMap

open FreeGrL

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [GrCooperad R C']
  [GrCooperad.Coaug R C']
  {A : Type} [Fintype A] [DecidableEq A]

variable (R C) in
/-- The projection onto the generators `s⁻¹ C̄`. -/
noncomputable def gen (A : Type) [Fintype A] [DecidableEq A] : C A →ₗ[R] CobarGen R C A :=
  GrCooperad.Red.proj R C A

lemma gen_surjective (A : Type) [Fintype A] [DecidableEq A] : Function.Surjective (gen R C A) :=
  GrCooperad.Red.proj_surjective A

/-- **`ι ⋆ ι` has two vertices.** -/
lemma ιι_mem_vx (x : C A) :
    ConvOp.toLin ((Cobar.ιι R C).1 A) x ∈ vx R (CobarGen R C) 2 A := by
  have hN : GrOperad.Inv.appDer (ConvOp.postDer (C := C)
      (derSp (GrSpEnd.id R (CobarGen R C)))) (Cobar.ι R C) = Cobar.ι R C :=
    Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun x => by
      rw [ConvOp.appDer_postDer_apply]
      show (derSp (GrSpEnd.id R (CobarGen R C))).app A (Cobar.ιL R C A x) = Cobar.ιL R C A x
      rw [Cobar.ιL_apply, derSp_ι, GrSpEnd.id_app])
  have h := GrOperad.Inv.appDer_star (ConvOp.postDer (C := C)
    (derSp (GrSpEnd.id R (CobarGen R C)))) (Cobar.isPar_ι R C) (Cobar.ι R C)
  have e := congrArg (fun q : GrOperad.Inv R (ConvOp R C (CobarGr R C)) =>
    ConvOp.toLin (q.1 A) x) h
  simp only [ConvOp.appDer_postDer_apply, hN] at e
  refine mem_eig.2 (e.trans ?_)
  show ConvOp.toLin ((Cobar.ιι R C).1 A + σ R false • (Cobar.ιι R C).1 A) x = _
  rw [σ_false, one_smul, ConvOp.toLin_add, LinearMap.add_apply, Nat.cast_two, two_smul]

variable (R C) in
/-- **The cobar differential raises the number of vertices by one.** -/
theorem d_mem_vx (k : ℕ) {y : CobarGr R C A} (hy : y ∈ vx R (CobarGen R C) k A) :
    (Cobar.d R C).app A y ∈ vx R (CobarGen R C) (k + 1) A :=
  der_mem_vx (fun A _ _ v => by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    show (Cobar.d R C).app A (Cobar.ιL R C A x) ∈ _
    rw [Cobar.d_ιL]
    exact neg_mem (ιι_mem_vx x)) hy

/-! ### Morphisms -/

section Map

variable (f : GrCooperadHom R C C')
  (hf : f.app Unit (GrCooperad.Coaug.one (R := R) (C := C))
    = GrCooperad.Coaug.one (R := R) (C := C'))
include hf

lemma unitSpan_le (A : Type) [Fintype A] [DecidableEq A] :
    GrCooperad.unitSpan R C A ≤ (GrCooperad.unitSpan R C' A).comap (f.app A) := by
  rw [GrCooperad.unitSpan, GrCooperad.unitSpanOf, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  show f.app A (SymSpecies.map (R := R) e _) ∈ GrCooperad.unitSpan R C' A
  rw [f.app_map, hf]
  exact GrCooperad.map_one_mem e

/-- **The morphism of the generators** `s⁻¹ C̄ → s⁻¹ C̄'`. -/
noncomputable def redMap : GrSpeciesHom R (CobarGen R C) (CobarGen R C') where
  app A _ _ := Submodule.mapQ _ _ (f.app A) (unitSpan_le f hf A)
  app_map {A B} _ _ _ _ σ' v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    exact congrArg (GrCooperad.Red.proj R C' B) (f.app_map σ' x)
  app_par {A} _ _ b v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    exact congrArg (GrCooperad.Red.proj R C' A) (f.app_par (!b) x)

lemma redMap_gen (x : C A) :
    (redMap f hf).app A (gen R C A x) = gen R C' A (f.app A x) := rfl

/-- **The morphism of cobar constructions** `Ωf = T(f̄)`. -/
noncomputable def map : GrOperadHom R (CobarGr R C) (CobarGr R C') := mapSp (redMap f hf)

lemma map_ιL (x : C A) : (map f hf).app A (Cobar.ιL R C A x) = Cobar.ιL R C' A (f.app A x) := by
  rw [Cobar.ιL_apply, map, mapSp_ι]
  rfl

/-- `(ι' ⋆ ι') ∘ f = Ωf ∘ (ι ⋆ ι)`. -/
lemma ιι_map (x : C A) :
    ConvOp.toLin ((Cobar.ιι R C').1 A) (f.app A x)
      = (map f hf).app A (ConvOp.toLin ((Cobar.ιι R C).1 A) x) := by
  have e1 := GrOperad.Inv.appHom_star
    (ConvOp.preHom (P := CobarGr R C') f) (Cobar.ι R C') (Cobar.ι R C')
  have e2 := GrOperad.Inv.appHom_star
    (ConvOp.postHom (C := C) (map f hf)) (Cobar.ι R C) (Cobar.ι R C)
  have e3 : GrOperad.Inv.appHom (ConvOp.preHom (P := CobarGr R C') f)
      (Cobar.ι R C') = GrOperad.Inv.appHom (ConvOp.postHom (C := C) (map f hf)) (Cobar.ι R C) :=
    Subtype.ext (funext fun A => funext fun _ => funext fun _ => by
      rw [GrOperad.Inv.appHom_apply, GrOperad.Inv.appHom_apply, Cobar.ι_apply, Cobar.ι_apply]
      ext x
      rw [ConvOp.preHom_app, ConvOp.postHom_app, LinearMap.comp_apply, LinearMap.comp_apply,
        ConvOp.toLin_of, ConvOp.toLin_of, map_ιL])
  have e := congrArg (fun q : GrOperad.Inv R (ConvOp R C (CobarGr R C')) =>
    ConvOp.toLin (q.1 A) x) (e1.trans ((congrArg₂ (fun a b =>
      GrOperad.Inv.star R (ConvOp R C (CobarGr R C')) a b) e3 e3).trans e2.symm))
  simp only [GrOperad.Inv.appHom_apply, ConvOp.preHom_app, ConvOp.postHom_app,
    LinearMap.comp_apply] at e
  exact e

/-- **`Ωf` commutes with the cobar differentials.** -/
theorem d_map (y : CobarGr R C A) :
    (Cobar.d R C').app A ((map f hf).app A y) = (map f hf).app A ((Cobar.d R C).app A y) := by
  have h : (Cobar.d R C').compHom (map f hf) = GrDer.homComp (map f hf) (Cobar.d R C) :=
    der_ext fun A _ _ v => by
      obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
      rw [GrDer.compHom_app, GrDer.homComp_app]
      show (Cobar.d R C').app A ((map f hf).app A (Cobar.ιL R C A x))
        = (map f hf).app A ((Cobar.d R C).app A (Cobar.ιL R C A x))
      rw [map_ιL, Cobar.d_ιL, Cobar.d_ιL, map_neg, ιι_map]
  exact congrArg (fun D : GrDer (map f hf) true => D.app A y) h

end Map

lemma unitSpan_eq_bot (hB : Fintype.card A ≠ 1) : GrCooperad.unitSpan R C A = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨e, rfl⟩
  exact absurd (Fintype.card_congr e).symm (by rw [Fintype.card_unit]; exact hB)

lemma gen_eq_zero (hB : Fintype.card A ≠ 1) {x : C A} : gen R C A x = 0 ↔ x = 0 := by
  refine (Submodule.Quotient.mk_eq_zero _).trans ?_
  rw [unitSpan_eq_bot hB, Submodule.mem_bot]

end CobarMap

/-! ## The cobar construction of a dg cooperad -/

namespace CobarDG

open FreeGrL
open CobarMap (gen gen_surjective redMap_gen gen_eq_zero)

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C] [DGCooperad.DOne R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [DGCooperad R C']
  [GrCooperad.Coaug R C'] [DGCooperad.DOne R C']
  {A : Type} [Fintype A] [DecidableEq A]

variable (R C) in
/-- **The differential of the generators** `s⁻¹ C̄`, induced by the differential of `C`. -/
noncomputable def redD : GrSpEnd R (CobarGen R C) true where
  app A _ _ := Submodule.mapQ (GrCooperad.unitSpan R C A) (GrCooperad.unitSpan R C A)
    (DGCooperad.d (R := R) (C := C)) fun x hx => by
      rw [Submodule.mem_comap, DGCooperad.d_unitSpan hx]
      exact zero_mem _
  app_map {A B} _ _ _ _ σ' v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    show GrCooperad.Red.proj R C B (DGCooperad.d (R := R) (SymSpecies.map (R := R) σ' x))
      = GrCooperad.Red.proj R C B (SymSpecies.map (R := R) σ' (DGCooperad.d (R := R) x))
    rw [DGCooperad.map_d]
  app_par {A} _ _ b v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    show GrCooperad.Red.proj R C A (DGCooperad.d (R := R) (GrSpecies.par (R := R) (!b) x))
      = GrCooperad.Red.proj R C A (GrSpecies.par (R := R) (!(xor b true))
          (DGCooperad.d (R := R) x))
    rw [DGCooperad.d_par]
    cases b <;> rfl

lemma redD_gen (x : C A) :
    (redD R C).app A (gen R C A x) = gen R C A (DGCooperad.d (R := R) x) := rfl

variable (R C) in
/-- **The differential of `ΩC` is the cobar differential minus the derivation extending the
differential of the generators.** -/
theorem d_eq_sub : d R C = (Cobar.d R C).sub (derSp (redD R C)) :=
  der_ext fun A _ _ v => by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    show (d R C).app A (Cobar.ιL R C A x)
      = (Cobar.d R C).app A (Cobar.ιL R C A x) - (derSp (redD R C)).app A (Cobar.ιL R C A x)
    rw [d_ιL, Cobar.d_ιL, Cobar.ιL_apply R C x, derSp_ι]
    rfl

variable (R C) in
lemma d_app_eq_totD (A : Type) [Fintype A] [DecidableEq A] (y : CobarGr R C A) :
    (d R C).app A y = totD (redD R C) (Cobar.d R C) A y := by
  rw [d_eq_sub, GrDer.sub_app, totD, LinearMap.add_apply, LinearMap.neg_apply]
  abel

/-! ### Morphisms -/

section Map

variable (f : DGCooperadHom R C C')
  (hf : f.app Unit (GrCooperad.Coaug.one (R := R) (C := C))
    = GrCooperad.Coaug.one (R := R) (C := C'))
include hf

/-- **The morphism of cobar constructions** `Ωf = T(f̄)`. -/
noncomputable def map : GrOperadHom R (CobarGr R C) (CobarGr R C') :=
  CobarMap.map f.toGrCooperadHom hf

/-- **`Ωf` commutes with the differentials.** -/
theorem map_d (y : CobarGr R C A) :
    (map f hf).app A ((d R C).app A y) = (d R C').app A ((map f hf).app A y) := by
  rw [map, d_app_eq_totD, d_app_eq_totD, totD, totD, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.neg_apply, map_add, map_neg, CobarMap.d_map, CobarMap.map,
    derSp_mapSp (a := redD R C) (fun A _ _ v => by
      obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
      show GrCooperad.Red.proj R C' A (DGCooperad.d (R := R) (f.app A x))
        = GrCooperad.Red.proj R C' A (f.app A (DGCooperad.d (R := R) x))
      rw [f.app_d])]

/-! ### Comparison -/

/-- **The comparison data** of `Ωf` for reduced cooperads. -/
theorem compareData
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ x : C B, x ∈ GrCooperad.unitSpan R C B)
    (hred' : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ x : C' B, x ∈ GrCooperad.unitSpan R C' B) :
    CompareData (redD R C) (redD R C') (Cobar.d R C) (Cobar.d R C')
      (CobarMap.redMap f.toGrCooperadHom hf) where
  redV B _ _ hB v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) B v
    exact (Submodule.Quotient.mk_eq_zero _).2 (hred B hB x)
  redW B _ _ hB v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C') B v
    exact (Submodule.Quotient.mk_eq_zero _).2 (hred' B hB x)
  ddV A _ _ v := by
    obtain ⟨x, rfl⟩ := gen_surjective (R := R) (C := C) A v
    rw [redD_gen, redD_gen, DGCooperad.d_d, map_zero]
  ddW A _ _ v := by
    obtain ⟨x, rfl⟩ := gen_surjective (R := R) (C := C') A v
    rw [redD_gen, redD_gen, DGCooperad.d_d, map_zero]
  dd A _ _ y := by
    rw [← d_app_eq_totD, ← d_app_eq_totD]
    exact d_d R C y
  dd' A _ _ y := by
    rw [← d_app_eq_totD, ← d_app_eq_totD]
    exact d_d R C' y
  raise A _ _ k _ hy := CobarMap.d_mem_vx R C k hy
  raise' A _ _ k _ hy := CobarMap.d_mem_vx R C' k hy
  comm A _ _ v := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective (R := R) (C := C) A v
    show GrCooperad.Red.proj R C' A (DGCooperad.d (R := R) (f.app A x))
      = GrCooperad.Red.proj R C' A (f.app A (DGCooperad.d (R := R) x))
    rw [f.app_d]
  commD A _ _ y := CobarMap.d_map f.toGrCooperadHom hf y

/-- **Away from arity one, `f̄` is surjective on homology iff `f` is.** -/
lemma surjAt_iff (hA : Fintype.card A ≠ 1) :
    SurjAt R (redD R C) (redD R C') (CobarMap.redMap f.toGrCooperadHom hf) A
      ↔ QIso.Surj ⊤ ⊤ (DGCooperad.d (R := R) (C := C) (A := A))
        (DGCooperad.d (R := R) (C := C') (A := A)) (f.app A) := by
  constructor
  · intro h y _ hy
    obtain ⟨x, hx, w, hw⟩ := h (gen R C' A y)
      (by rw [redD_gen, hy, map_zero])
    obtain ⟨x, rfl⟩ := gen_surjective (R := R) (C := C) A x
    obtain ⟨w, rfl⟩ := gen_surjective (R := R) (C := C') A w
    rw [redD_gen, gen_eq_zero hA] at hx
    rw [redMap_gen, redD_gen, ← map_sub, ← sub_eq_zero, ← map_sub, gen_eq_zero hA,
      sub_eq_zero] at hw
    exact ⟨x, Submodule.mem_top, hx, w, Submodule.mem_top, hw⟩
  · intro h v hv
    obtain ⟨y, rfl⟩ := gen_surjective (R := R) (C := C') A v
    rw [redD_gen, gen_eq_zero hA] at hv
    obtain ⟨x, _, hx, w, _, hw⟩ := h y Submodule.mem_top hv
    refine ⟨gen R C A x, by rw [redD_gen, hx, map_zero],
      gen R C' A w, ?_⟩
    rw [redMap_gen, redD_gen, ← map_sub, hw]

/-- **Away from arity one, `f̄` is injective on homology iff `f` is.** -/
lemma injAt_iff (hA : Fintype.card A ≠ 1) :
    InjAt R (redD R C) (redD R C') (CobarMap.redMap f.toGrCooperadHom hf) A
      ↔ QIso.Inj ⊤ ⊤ (DGCooperad.d (R := R) (C := C) (A := A))
        (DGCooperad.d (R := R) (C := C') (A := A)) (f.app A) := by
  constructor
  · intro h x _ hx w _ hw
    obtain ⟨z, hz⟩ := h (gen R C A x) (by rw [redD_gen, hx, map_zero])
      (gen R C' A w) (by rw [redMap_gen, redD_gen, hw])
    obtain ⟨z, rfl⟩ := gen_surjective (R := R) (C := C) A z
    rw [redD_gen, ← sub_eq_zero, ← map_sub, gen_eq_zero hA, sub_eq_zero] at hz
    exact ⟨z, Submodule.mem_top, hz⟩
  · intro h v hv w' hw
    obtain ⟨x, rfl⟩ := gen_surjective (R := R) (C := C) A v
    obtain ⟨w, rfl⟩ := gen_surjective (R := R) (C := C') A w'
    rw [redD_gen, gen_eq_zero hA] at hv
    rw [redMap_gen, redD_gen, ← sub_eq_zero, ← map_sub, gen_eq_zero hA, sub_eq_zero] at hw
    obtain ⟨z, _, hz⟩ := h x Submodule.mem_top hv w Submodule.mem_top hw
    exact ⟨gen R C A z, by rw [redD_gen, hz]⟩

end Map

section Field

variable {R : Type u} [Field R] [CharZero R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]
  [GrCooperad.Coaug R C] [DGCooperad.DOne R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [DGCooperad R C']
  [GrCooperad.Coaug R C'] [DGCooperad.DOne R C'] (f : DGCooperadHom R C C')
  (hf : f.app Unit (GrCooperad.Coaug.one (R := R) (C := C))
    = GrCooperad.Coaug.one (R := R) (C := C'))

/-- **Ω preserves and reflects quasi-isomorphisms.** Over a field of characteristic zero, for
reduced coaugmented dg cooperads, **`Ωf` is a quasi-isomorphism iff `f` is one in the arities at
least two.** -/
theorem map_bijective_iff
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ x : C B, x ∈ GrCooperad.unitSpan R C B)
    (hred' : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ x : C' B, x ∈ GrCooperad.unitSpan R C' B) :
    (∀ (B : Type) [Fintype B] [DecidableEq B], 2 ≤ Fintype.card B →
      Function.Bijective (Homology.map (dV := DGCooperad.d (R := R) (C := C) (A := B))
        (dW := DGCooperad.d (R := R) (C := C') (A := B)) (f.app B) fun x => f.app_d x)) ↔
    ∀ (A : Type) [Fintype A] [DecidableEq A],
      Function.Bijective (Homology.map (dV := (d R C).app A) (dW := (d R C').app A)
        ((map f hf).app A) fun y => map_d f hf y) := by
  have hc := compareData f hf hred hred'
  have hD : ∀ (A : Type) [Fintype A] [DecidableEq A],
      (d R C).app A = totD (redD R C) (Cobar.d R C) A := fun A _ _ =>
    LinearMap.ext (d_app_eq_totD R C A)
  have hD' : ∀ (A : Type) [Fintype A] [DecidableEq A],
      (d R C').app A = totD (redD R C') (Cobar.d R C') A := fun A _ _ =>
    LinearMap.ext (d_app_eq_totD R C' A)
  constructor
  · intro h A _ _
    rw [QIso.bijective_iff, hD, hD']
    refine hc.qiso_of_qiso A (fun B _ _ => ?_) (fun B _ _ => ?_)
    · rcases le_or_gt (Fintype.card B) 1 with hB | hB
      · intro y _
        exact ⟨0, map_zero _, 0, by rw [hc.redW B hB y, map_zero, map_zero, sub_zero]⟩
      · exact (surjAt_iff f hf (by omega)).2 ((QIso.bijective_iff _ _).1 (h B hB)).1
    · rcases le_or_gt (Fintype.card B) 1 with hB | hB
      · intro x _ _ _
        exact ⟨0, by rw [map_zero, hc.redV B hB x]⟩
      · exact (injAt_iff f hf (by omega)).2 ((QIso.bijective_iff _ _).1 (h B hB)).2
  · intro h B _ _ hB
    have hq := hc.qiso_of_qiso_free B
      (fun A _ _ => by
        have := ((QIso.bijective_iff _ _).1 (h A)).1
        rwa [hD, hD'] at this)
      (fun A _ _ => by
        have := ((QIso.bijective_iff _ _).1 (h A)).2
        rwa [hD, hD'] at this)
    rw [QIso.bijective_iff]
    exact ⟨(surjAt_iff f hf (by omega)).1 hq.1, (injAt_iff f hf (by omega)).1 hq.2⟩

end Field

end CobarDG

/-! ## Morphisms out of a cooperad with the zero differential -/

namespace CobarZero

open FreeGrL
open CobarMap (gen gen_surjective redMap_gen gen_eq_zero)

section General

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [DGCooperad R C']
  [GrCooperad.Coaug R C'] [DGCooperad.DOne R C'] (f : GrCooperadHom R C C')
  (hf : f.app Unit (GrCooperad.Coaug.one (R := R) (C := C))
    = GrCooperad.Coaug.one (R := R) (C := C'))
  (hfd : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), DGCooperad.d (R := R) (f.app A x) = 0)
  {A : Type} [Fintype A] [DecidableEq A]
include hf

include hfd in
/-- The differential of the generators of `ΩC'` kills the image of `C`. -/
lemma redD_redMap (v : CobarGen R C A) :
    (CobarDG.redD R C').app A ((CobarMap.redMap f hf).app A v) = 0 := by
  obtain ⟨x, rfl⟩ := gen_surjective (R := R) (C := C) A v
  show gen R C' A (DGCooperad.d (R := R) (f.app A x)) = 0
  rw [hfd, map_zero]

include hfd in
/-- **`Ωf` commutes with the differentials**, `C` having the zero differential. -/
theorem map_d (y : CobarGr R C A) :
    (CobarMap.map f hf).app A ((Cobar.d R C).app A y)
      = (CobarDG.d R C').app A ((CobarMap.map f hf).app A y) := by
  rw [CobarDG.d_app_eq_totD, totD, LinearMap.add_apply, LinearMap.neg_apply, CobarMap.d_map,
    CobarMap.map, derSp_mapSp (a := GrSpEnd.zero R _ true) (fun A _ _ v => by
      rw [GrSpEnd.zero_app, map_zero]
      exact redD_redMap f hf hfd v), derSp_zero_app, map_zero, neg_zero, zero_add]

include hfd in
/-- **The comparison data** of `Ωf`, `C` having the zero differential. -/
theorem compareData
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ x : C B, x ∈ GrCooperad.unitSpan R C B)
    (hred' : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ x : C' B, x ∈ GrCooperad.unitSpan R C' B) :
    CompareData (GrSpEnd.zero R (CobarGen R C) true) (CobarDG.redD R C') (Cobar.d R C)
      (Cobar.d R C') (CobarMap.redMap f hf) where
  redV B _ _ hB v := by
    obtain ⟨x, rfl⟩ := gen_surjective (R := R) (C := C) B v
    exact (Submodule.Quotient.mk_eq_zero _).2 (hred B hB x)
  redW B _ _ hB v := by
    obtain ⟨x, rfl⟩ := gen_surjective (R := R) (C := C') B v
    exact (Submodule.Quotient.mk_eq_zero _).2 (hred' B hB x)
  ddV A _ _ v := GrSpEnd.zero_app _
  ddW A _ _ v := by
    obtain ⟨x, rfl⟩ := gen_surjective (R := R) (C := C') A v
    rw [CobarDG.redD_gen, CobarDG.redD_gen, DGCooperad.d_d, map_zero]
  dd A _ _ y := by
    rw [totD_zero_app, totD_zero_app]
    exact Cobar.d_d R C y
  dd' A _ _ y := by
    rw [← CobarDG.d_app_eq_totD, ← CobarDG.d_app_eq_totD]
    exact CobarDG.d_d R C' y
  raise A _ _ k _ hy := CobarMap.d_mem_vx R C k hy
  raise' A _ _ k _ hy := CobarMap.d_mem_vx R C' k hy
  comm A _ _ v := by
    rw [GrSpEnd.zero_app, map_zero]
    exact redD_redMap f hf hfd v
  commD A _ _ y := CobarMap.d_map f hf y

/-- **Away from arity one, `f̄` is surjective on homology iff `f` is.** -/
lemma surjAt_iff (hA : Fintype.card A ≠ 1) :
    SurjAt R (GrSpEnd.zero R (CobarGen R C) true) (CobarDG.redD R C') (CobarMap.redMap f hf) A
      ↔ QIso.Surj ⊤ ⊤ (0 : C A →ₗ[R] C A) (DGCooperad.d (R := R) (C := C') (A := A))
        (f.app A) := by
  constructor
  · intro h y _ hy
    obtain ⟨x, -, w, hw⟩ := h (gen R C' A y) (by rw [CobarDG.redD_gen, hy, map_zero])
    obtain ⟨x, rfl⟩ := gen_surjective (R := R) (C := C) A x
    obtain ⟨w, rfl⟩ := gen_surjective (R := R) (C := C') A w
    rw [redMap_gen, CobarDG.redD_gen, ← map_sub, ← sub_eq_zero, ← map_sub, gen_eq_zero hA,
      sub_eq_zero] at hw
    exact ⟨x, Submodule.mem_top, LinearMap.zero_apply x, w, Submodule.mem_top, hw⟩
  · intro h v hv
    obtain ⟨y, rfl⟩ := gen_surjective (R := R) (C := C') A v
    rw [CobarDG.redD_gen, gen_eq_zero hA] at hv
    obtain ⟨x, _, -, w, _, hw⟩ := h y Submodule.mem_top hv
    exact ⟨gen R C A x, GrSpEnd.zero_app _, gen R C' A w,
      by rw [redMap_gen, CobarDG.redD_gen, ← map_sub, hw]⟩

/-- **Away from arity one, `f̄` is injective on homology iff `f` is.** -/
lemma injAt_iff (hA : Fintype.card A ≠ 1) :
    InjAt R (GrSpEnd.zero R (CobarGen R C) true) (CobarDG.redD R C') (CobarMap.redMap f hf) A
      ↔ QIso.Inj ⊤ ⊤ (0 : C A →ₗ[R] C A) (DGCooperad.d (R := R) (C := C') (A := A))
        (f.app A) := by
  constructor
  · intro h x _ _ w _ hw
    obtain ⟨z, hz⟩ := h (gen R C A x) (GrSpEnd.zero_app _) (gen R C' A w)
      (by rw [redMap_gen, CobarDG.redD_gen, hw])
    rw [GrSpEnd.zero_app, eq_comm, gen_eq_zero hA] at hz
    exact ⟨0, Submodule.mem_top, by rw [LinearMap.zero_apply, hz]⟩
  · intro h v _ w' hw
    obtain ⟨x, rfl⟩ := gen_surjective (R := R) (C := C) A v
    obtain ⟨w, rfl⟩ := gen_surjective (R := R) (C := C') A w'
    rw [redMap_gen, CobarDG.redD_gen, ← sub_eq_zero, ← map_sub, gen_eq_zero hA, sub_eq_zero] at hw
    obtain ⟨z, _, hz⟩ := h x Submodule.mem_top (LinearMap.zero_apply x) w Submodule.mem_top hw
    refine ⟨0, ?_⟩
    rw [GrSpEnd.zero_app, ← hz, LinearMap.zero_apply, map_zero]

end General

section Field

variable {R : Type u} [Field R] [CharZero R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [DGCooperad R C']
  [GrCooperad.Coaug R C'] [DGCooperad.DOne R C'] (f : GrCooperadHom R C C')
  (hf : f.app Unit (GrCooperad.Coaug.one (R := R) (C := C))
    = GrCooperad.Coaug.one (R := R) (C := C'))
  (hfd : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), DGCooperad.d (R := R) (f.app A x) = 0)

/-- **Ω preserves and reflects quasi-isomorphisms out of a cooperad with the zero
differential.** Over a field of characteristic zero, for reduced coaugmented cooperads, `C` with
the zero differential and `d' ∘ f = 0`, **`Ωf` is a quasi-isomorphism iff `f` is one in the
arities at least two.** -/
theorem map_bijective_iff
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ x : C B, x ∈ GrCooperad.unitSpan R C B)
    (hred' : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ x : C' B, x ∈ GrCooperad.unitSpan R C' B) :
    (∀ (B : Type) [Fintype B] [DecidableEq B], 2 ≤ Fintype.card B →
      Function.Bijective (Homology.map (dV := (0 : C B →ₗ[R] C B))
        (dW := DGCooperad.d (R := R) (C := C') (A := B)) (f.app B)
          fun x => by rw [LinearMap.zero_apply, map_zero, hfd])) ↔
    ∀ (A : Type) [Fintype A] [DecidableEq A],
      Function.Bijective (Homology.map (dV := (Cobar.d R C).app A) (dW := (CobarDG.d R C').app A)
        ((CobarMap.map f hf).app A) fun y => map_d f hf hfd y) := by
  have hc := compareData f hf hfd hred hred'
  have hD : ∀ (A : Type) [Fintype A] [DecidableEq A],
      (Cobar.d R C).app A = totD (GrSpEnd.zero R (CobarGen R C) true) (Cobar.d R C) A :=
    fun A _ _ => LinearMap.ext fun y => (totD_zero_app _ y).symm
  have hD' : ∀ (A : Type) [Fintype A] [DecidableEq A],
      (CobarDG.d R C').app A = totD (CobarDG.redD R C') (Cobar.d R C') A := fun A _ _ =>
    LinearMap.ext (CobarDG.d_app_eq_totD R C' A)
  constructor
  · intro h A _ _
    rw [QIso.bijective_iff, hD, hD']
    refine hc.qiso_of_qiso A (fun B _ _ => ?_) (fun B _ _ => ?_)
    · rcases le_or_gt (Fintype.card B) 1 with hB | hB
      · intro y _
        exact ⟨0, map_zero _, 0, by rw [hc.redW B hB y, map_zero, map_zero, sub_zero]⟩
      · exact (surjAt_iff f hf (by omega)).2 ((QIso.bijective_iff _ _).1 (h B hB)).1
    · rcases le_or_gt (Fintype.card B) 1 with hB | hB
      · intro x _ _ _
        exact ⟨0, by rw [map_zero, hc.redV B hB x]⟩
      · exact (injAt_iff f hf (by omega)).2 ((QIso.bijective_iff _ _).1 (h B hB)).2
  · intro h B _ _ hB
    have hq := hc.qiso_of_qiso_free B
      (fun A _ _ => by
        have := ((QIso.bijective_iff _ _).1 (h A)).1
        rwa [hD, hD'] at this)
      (fun A _ _ => by
        have := ((QIso.bijective_iff _ _).1 (h A)).2
        rwa [hD, hD'] at this)
    rw [QIso.bijective_iff]
    exact ⟨(surjAt_iff f hf (by omega)).1 hq.1, (injAt_iff f hf (by omega)).1 hq.2⟩

end Field

end CobarZero

end Operad
