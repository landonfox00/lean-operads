/-
# The Koszul dual dg cooperad of quadratic-linear data

Let `P = T(E)/(r)` be a presented graded operad over a field of characteristic zero, and `q` a
family of quadratic elements, the quadratic parts of the relators: `qP = T(E)/(q)`, with Koszul
dual cooperad `qP^¡` (`Koszul.Dual R E q`). **Quadratic-linear data** (`Koszul.IsQL`) are such
`q` with an ideal `I` of `P` without operations with at most one input, such that

* every element of `q` is congruent to a generator modulo `(r)`: the relators are `X - φ(X)`;
* the generators embed into `P`: `(r) ∩ E = 0`;
* the elements with two vertices of `(r)` lie in `(q)`: `(r) ∩ T(E)^{(2)} ⊆ (q)`.

The last two are the Poincaré–Birkhoff–Witt property of `P` in weights one and two. They are
stated on the ideal `(r)`, and imply the conditions `(ql₁)` and `(ql₂)` of Loday and Vallette,
which are stated on `R` and on `R ∘ E + E ∘ R`.

* **The differential.** `qP^¡` has a differential `d_φ` (`Koszul.dQL`), an odd coderivation
  (`Koszul.decomp_dQL`) with `d_φ² = 0` (`Koszul.dQL_dQL`): **the Koszul dual dg cooperad
  `(qP^¡, d_φ)`** (`Koszul.DualQL`, `Koszul.DualQL.instDGCooperad`). Its cogenerator part is
  minus the convolution square, `κ ∘ d_φ = -(κ ⋆ κ)` in `P` (`Koszul.proj_kapL_dQL`): the
  element `(κ_T ⋆ κ_T)(c)` of the quadratic part, read as a generator. For `r = q` it vanishes
  (`Koszul.dQL_eq_zero`).
* **The construction.** `d_φ` is the bar differential of `B(P, I)` on the image of `qP^¡` under
  the comparison morphism `i : qP^¡ → T^c(sE) → B(P, I)` (`Koszul.toBarQ`): `i ∘ d_φ = d_B ∘ i`
  (`Koszul.toBarQ_dQL`), and `i` is injective, so `d_φ` is determined (`Koszul.dQL_unique`).
  The suspended generators `sE → sI` have a retraction (`Koszul.retr`), by
  `GrSpeciesHom.exists_retraction`. The subcooperad `i(qP^¡) + d_B i(qP^¡)` of the bar
  construction (`GrSubCooperad.addD`) lies in the image of `T^c(sE)`
  (`Koszul.mapSp_mapSp_retr`): `π` takes it into the generators (`Koszul.piL_mem_genRange`),
  by `π ∘ d_B = -(π ⋆ π)` (`Bar.piL_d`), and two morphisms into a cut cooperad with the same
  coefficient of the generators are equal (`FreeGrL.app_eq_of_genCoef₀`). Its retraction lies
  in `qP^¡` (`Koszul.imRetr_le`): `κ_T ⋆ κ_T` takes the retraction of a boundary to an element
  with two vertices of `(r)`, since `π ⋆ π` vanishes on the boundaries (`Bar.star_pi_d`).
* **The comparison morphism** `i : (qP^¡, d_φ) → B(P, I)` is a morphism of dg cooperads
  (`Koszul.toBarDG`).
* **The morphism `Ω(qP^¡, d_φ) → P`** (`Koszul.cobarMorQL`) is the counit `ΩB(P, I) → P` after
  `Ωi`. It desuspends the cogenerators (`Koszul.cobarMorQL_ιL`) and commutes with the
  differentials (`Koszul.cobarMorQL_d`), so `κ : (qP^¡, d_φ) → P` is a twisting morphism
  (`Koszul.twistingQL`).
* **The Koszul criterion for quadratic-linear data** (`Koszul.cobarMorQL_bijective_iff`):
  `Ω(qP^¡, d_φ) → P` is a quasi-isomorphism iff `i` is one in the arities at least two, the
  counit being a quasi-isomorphism (`Bar.counit_bijective`) and `Ω` preserving and reflecting
  the quasi-isomorphisms of reduced dg cooperads (`CobarDG.map_bijective_iff`).

Also here: the coefficient of the generators is natural in the morphisms of the generators
(`FreeGrL.genCoef_mapSp`), and the image of a subcooperad under a morphism is a subcooperad
(`GrSubCooperad.map`).

That `i` is a quasi-isomorphism when `qP` is Koszul and `P` has the Poincaré–Birkhoff–Witt
property in every weight is in `Operad.KoszulInhomQIso`.
-/
import Operad.KoszulBar
import Operad.KoszulCorel
import Operad.BarAdjunction
import Operad.SpRetraction
import Operad.DeformationComplex
import Operad.KoszulCriterion
import Operad.BarCobarQIso

universe u v w

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

/-! ## The coefficient of the generators and morphisms of the generators -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {A : Type} [Fintype A] [DecidableEq A]

/-- The coefficient of the generators vanishes on the trees whose number of vertices is not
one. -/
lemma genCoef_eq_zero_of_mem_wtEqL {n : ℕ} (hn : n ≠ 1) {x : FreeGrL R V A}
    (hx : x ∈ wtEqL R V n A) : genCoef R V A x = 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [genCoef_proj]
  have hle : FreeGr.wtEq R (grGenPar R V) n A ≤ LinearMap.ker (genCoefF R V A) := by
    rw [FreeGr.wtEq, Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    have hw : (treeOf t).weight ≠ 1 := by
      rw [← Tree.cnt_one]
      exact fun h => hn (ht.symm.trans h)
    rw [SetLike.mem_coe, LinearMap.mem_ker, genCoefF_bas, coefReg_of_weight_ne hw]
  exact LinearMap.mem_ker.1 (hle hy)

/-- **The coefficient of the generators is natural** in the morphisms of the generators, over a
`ℚ`-algebra. -/
theorem genCoef_mapSp [Algebra ℚ R] (φ : GrSpeciesHom R V W) (x : FreeGrL R V A) :
    genCoef R W A ((mapSp φ).app A x) = φ.app A (genCoef R V A x) := by
  have hle : ∀ n : ℕ, wtEqL R V n A
      ≤ LinearMap.eqLocus (genCoef R W A ∘ₗ (mapSp φ).app A) (φ.app A ∘ₗ genCoef R V A) := by
    intro n y hy
    rw [LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.comp_apply]
    by_cases hn : n = 1
    · subst hn
      rw [eq_ι_genCoef (wtEqL_le_vx 1 hy), mapSp_ι, genCoef_ι, genCoef_ι]
    · have h1 : (mapSp φ).app A y ∈ wtEqL R W n A := by
        rw [wtEqL_eq_vx]
        exact mapSp_mem_vx (wtEqL_le_vx n hy)
      rw [genCoef_eq_zero_of_mem_wtEqL hn h1, genCoef_eq_zero_of_mem_wtEqL hn hy, map_zero]
  have hx : x ∈ ⨆ n, wtEqL R V n A := (iSup_wtEqL (R := R) (V := V) A).symm ▸ Submodule.mem_top
  exact LinearMap.mem_eqLocus.1 ((iSup_le hle) hx)

/-- **A retraction of the generators induces a retraction of the free graded operads.** -/
lemma mapSp_retraction {f : GrSpeciesHom R V W} {g : GrSpeciesHom R W V}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A), g.app A (f.app A v) = v)
    (x : FreeGrL R V A) : (mapSp g).app A ((mapSp f).app A x) = x := by
  rw [mapSp_comp]
  exact (mapSp_congr (φ := g.comp f) (ψ := (GrSpEnd.id R V).toHom) (fun A _ _ v => h A v) x).trans
    (mapSp_id x)

/-- A morphism of the generators with a retraction induces an injective morphism. -/
lemma mapSp_injective_of_retraction {f : GrSpeciesHom R V W} {g : GrSpeciesHom R W V}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A), g.app A (f.app A v) = v) :
    Function.Injective ((mapSp f).app A) :=
  Function.LeftInverse.injective (g := (mapSp g).app A) fun x => mapSp_retraction h x

end FreeGrL

/-! ## Images of subcooperads, and the subcooperad `K + d K` -/

namespace GrSubCooperad

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)]

section Map

variable [GrCooperad R C] [GrCooperad R C']

/-- **The image of a subcooperad under a morphism of graded cooperads.** -/
def map (f : GrCooperadHom R C C') (K : GrSubCooperad R C) : GrSubCooperad R C' where
  sub A _ _ := (K.sub A).map (f.app A)
  par_mem := by
    rintro A _ _ b _ ⟨x, hx, rfl⟩
    exact ⟨GrSpecies.par (R := R) b x, K.par_mem b hx, f.app_par b x⟩
  map_mem := by
    rintro A B _ _ _ _ e _ ⟨x, hx, rfl⟩
    exact ⟨SymSpecies.map (R := R) e x, K.map_mem e hx, f.app_map e x⟩
  decomp_mem := by
    rintro A B _ _ _ _ i _ ⟨x, hx, rfl⟩
    have h := LinearMap.congr_fun (f.decomp_app (B := B) i) x
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    rw [h]
    exact map_range_map_subtype_le (f.app A) (f.app B) (K.sub A) (K.sub B)
      (Submodule.mem_map_of_mem (K.decomp_mem i hx))

lemma mem_map {f : GrCooperadHom R C C'} {K : GrSubCooperad R C} {A : Type} [Fintype A]
    [DecidableEq A] {y : C' A} : y ∈ (K.map f).sub A ↔ ∃ x ∈ K.sub A, f.app A x = y :=
  Iff.rfl

end Map

section AddD

variable [DGCooperad R C] (K : GrSubCooperad R C)

/-- **The subcooperad `K + d K`** of a dg cooperad. -/
def addD : GrSubCooperad R C where
  sub A _ _ := K.sub A ⊔ (K.sub A).map (DGCooperad.d (R := R) (C := C))
  par_mem := by
    intro A _ _ b x hx
    obtain ⟨a, ha, _, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    refine Submodule.add_mem_sup (K.par_mem b ha) ⟨GrSpecies.par (R := R) (!b) c,
      K.par_mem (!b) hc, ?_⟩
    rw [DGCooperad.d_par, Bool.not_not]
  map_mem := by
    intro A B _ _ _ _ e x hx
    obtain ⟨a, ha, _, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (K.map_mem e ha) ⟨SymSpecies.map (R := R) e c, K.map_mem e hc,
      (DGCooperad.map_d (R := R) e c).symm⟩
  decomp_mem := by
    intro A B _ _ _ _ i x hx
    obtain ⟨a, ha, _, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    have hK : ∀ (A : Type) [Fintype A] [DecidableEq A],
        K.sub A ≤ K.sub A ⊔ (K.sub A).map (DGCooperad.d (R := R) (C := C)) :=
      fun A _ _ => le_sup_left
    have hd : ∀ (A : Type) [Fintype A] [DecidableEq A],
        (K.sub A).map (DGCooperad.d (R := R) (C := C))
          ≤ K.sub A ⊔ (K.sub A).map (DGCooperad.d (R := R) (C := C)) :=
      fun A _ _ => le_sup_right
    have hτ : (K.sub A).map (GrSpecies.par (R := R) (V := C) false
        - GrSpecies.par (R := R) (V := C) true) ≤ K.sub A := by
      rintro _ ⟨y, hy, rfl⟩
      exact sub_mem (K.par_mem false hy) (K.par_mem true hy)
    rw [map_add]
    refine add_mem (range_map_subtype_mono (hK A) (hK B) (K.decomp_mem i ha)) ?_
    rw [DGCooperad.decomp_d]
    refine add_mem ?_ ?_
    · have h1 := map_range_map_subtype_le (DGCooperad.d (R := R) (C := C)) LinearMap.id
        (K.sub A) (K.sub B) (Submodule.mem_map_of_mem (K.decomp_mem i hc))
      rw [Submodule.map_id] at h1
      exact range_map_subtype_mono (hd A) (hK B) h1
    · have h1 := map_range_map_subtype_le (GrSpecies.par (R := R) (V := C) false
          - GrSpecies.par (R := R) (V := C) true) (DGCooperad.d (R := R) (C := C))
        (K.sub A) (K.sub B) (Submodule.mem_map_of_mem (K.decomp_mem i hc))
      exact range_map_subtype_mono (hτ.trans (hK A)) (hd B) h1

lemma le_addD : K ≤ K.addD := fun _ _ _ => le_sup_left

lemma d_mem_addD {A : Type} [Fintype A] [DecidableEq A] {x : C A} (hx : x ∈ K.sub A) :
    DGCooperad.d (R := R) x ∈ K.addD.sub A :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

lemma mem_addD {A : Type} [Fintype A] [DecidableEq A] {x : C A} :
    x ∈ K.addD.sub A ↔ ∃ a ∈ K.sub A, ∃ c ∈ K.sub A, a + DGCooperad.d (R := R) c = x := by
  constructor
  · intro hx
    obtain ⟨a, ha, _, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨a, ha, c, hc, rfl⟩
  · rintro ⟨a, ha, c, hc, rfl⟩
    exact Submodule.add_mem_sup ha ⟨c, hc, rfl⟩

end AddD

end GrSubCooperad

/-! ## The universal twisting morphism and the differential -/

namespace Bar

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P}

/-- **`π ∘ d_B = -(π ⋆ π)`**, the Maurer–Cartan equation of the universal twisting morphism. -/
lemma piL_d (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) {A : Type} [Fintype A] [DecidableEq A]
    (x : BarCoop I A) :
    piL I A (DGCooperad.d (R := R) (C := BarCoop I) x)
      = -ConvOp.toLin ((GrOperad.Inv.star R _ (pi I) (pi I)).1 A) x := by
  have hmc := congrArg (fun q : GrOperad.Inv R (ConvOp R (BarCoop I) (ZeroDG R P)) =>
    ConvOp.toLin (q.1 A) x) (mc_pi I hI0)
  have hpi : GrOperad.tw (R := R) true ((pi I).1 A) = -(pi I).1 A := by
    rw [GrOperad.tw_hom true (isPar_pi A), Bool.and_self, σ_true, neg_one_smul]
  have key : (0 : ZeroDG R P A) - ConvOp.toLin (GrOperad.tw (R := R) true ((pi I).1 A))
      (DGCooperad.d (R := R) (C := BarCoop I) x)
      + ConvOp.toLin ((GrOperad.Inv.star R _ (pi I) (pi I)).1 A) x = 0 := hmc
  rw [hpi, ConvOp.toLin_neg, LinearMap.neg_apply, zero_sub, neg_neg] at key
  exact eq_neg_of_add_eq_zero_left key

/-- **`π ⋆ π` vanishes on the boundaries**, since `π ⋆ π = -π ∘ d_B` and `d_B² = 0`. -/
lemma star_pi_d (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) {A : Type} [Fintype A] [DecidableEq A]
    (x : BarCoop I A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (pi I) (pi I)).1 A)
      (DGCooperad.d (R := R) (C := BarCoop I) x) = 0 := by
  have h1 := piL_d hI0 (DGCooperad.d (R := R) (C := BarCoop I) x)
  have h2 : piL I A (DGCooperad.d (R := R) (C := BarCoop I)
      (DGCooperad.d (R := R) (C := BarCoop I) x)) = 0 :=
    (congrArg (piL I A) (DGCooperad.d_d (R := R) (C := BarCoop I) x)).trans (map_zero _)
  exact neg_eq_zero.1 (h1.symm.trans h2)

end Bar

/-! ## Quadratic-linear data and the bar differential on the Koszul dual cooperad -/

namespace Koszul

open FreeGrL

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} (I : GrOperadIdeal R (Pres R E r))
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)
  (q : ∀ n : ℕ, Set (FreeGrL R E (Fin n)))

local notation "𝒥" => GrOperadIdeal.span R r

/-- **Quadratic-linear data**: quadratic elements `q`, the quadratic parts of the relators of
`P = T(E)/(r)`, and an ideal `I` of `P` without operations with at most one input, such that
every element of `q` is congruent to a generator modulo `(r)`, the generators embed into `P`, and
the elements with two vertices of `(r)` lie in `(q)`. -/
structure IsQL : Prop where
  quad : IsQuadratic R E q
  red : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 → ∀ y ∈ I.sub B, y = 0
  lin : ∀ (n : ℕ), ∀ X ∈ q n, ∃ ℓ : E (Fin n),
    (𝒥).proj (Fin n) X = (𝒥).proj (Fin n) ((FreeGrL.ι R E).app (Fin n) ℓ)
  inj : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (𝒥).proj A ((FreeGrL.ι R E).app A v) = 0 → v = 0
  quad_mem : ∀ (A : Type) [Fintype A] [DecidableEq A] (z : FreeGrL R E A), z ∈ vx R E 2 A →
    (𝒥).proj A z = 0 → z ∈ (GrOperadIdeal.span R q).sub A

variable {I q} {A : Type} [Fintype A] [DecidableEq A]

variable (r) in
/-- The image of the generators in `P`. -/
noncomputable def genRange (A : Type) [Fintype A] [DecidableEq A] :
    Submodule R (Pres R E r A) :=
  LinearMap.range ((𝒥).proj A ∘ₗ (FreeGrL.ι R E).app A)

omit [CharZero R] in
/-- **The relations of the quadratic part are congruent to generators.** -/
lemma proj_relSp_mem (h : IsQL I q) {z : FreeGrL R E A} (hz : z ∈ relSp R E q A) :
    (𝒥).proj A z ∈ genRange r A := by
  have key : ∀ {n : ℕ} (e : Fin n ≃ A) (b : Bool) (y : FreeGrL R E (Fin n)),
      (𝒥).proj A (GrOperad.par (R := R) b (GrOperad.map (R := R) e y))
        = GrOperad.par (R := R) b (GrOperad.map (R := R) e ((𝒥).proj (Fin n) y)) :=
    fun e b y => ((𝒥).projHom.app_par b _).trans
      (congrArg (GrOperad.par (R := R) b) ((𝒥).projHom.app_map e y))
  have hle : relSp R E q A ≤ (genRange r A).comap ((𝒥).proj A) := by
    rw [relSp, Submodule.span_le]
    rintro _ ⟨n, x, hx, e, b, rfl⟩
    obtain ⟨ℓ, hℓ⟩ := h.lin n x hx
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine ⟨GrSpecies.par (R := R) b (SymSpecies.map (R := R) e ℓ), ?_⟩
    have e1 : (FreeGrL.ι R E).app A (GrSpecies.par (R := R) b (SymSpecies.map (R := R) e ℓ))
        = GrOperad.par (R := R) b (GrOperad.map (R := R) e ((FreeGrL.ι R E).app (Fin n) ℓ)) := by
      rw [(FreeGrL.ι R E).app_par, (FreeGrL.ι R E).app_map]
      rfl
    exact (congrArg ((𝒥).proj A) e1).trans ((key e b _).trans
      ((congrArg (fun y => GrOperad.par (R := R) b (GrOperad.map (R := R) e y)) hℓ.symm).trans
        (key e b x).symm))
  exact hle hz

include hE in
omit [CharZero R] in
/-- The suspended generators embed into the generators of the bar construction. -/
lemma barGen_injective (h : IsQL I q) (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective ((barGen I hE).app A) :=
  (injective_iff_map_eq_zero _).2 fun w hw =>
    h.inj A w (congrArg (IdealSp.val I) hw)

/-- **A retraction of the suspended generators** `sI → sE`, over a field of characteristic
zero. -/
noncomputable def retr (h : IsQL I q) : GrSpeciesHom R (BarGen I) (GrSpecies.Shift E R) :=
  Classical.choose (GrSpeciesHom.exists_retraction (barGen I hE)
    (fun A _ _ => barGen_injective hE h A))

lemma retr_barGen (h : IsQL I q) (w : GrSpecies.Shift E R A) :
    (retr hE h).app A ((barGen I hE).app A w) = w :=
  Classical.choose_spec (GrSpeciesHom.exists_retraction (barGen I hE)
    (fun A _ _ => barGen_injective hE h A)) A w

/-- The retraction, on the cut cooperads. -/
lemma mapSp_retr (h : IsQL I q) (y : Cut R E A) :
    (FreeGrL.mapSp (retr hE h)).app A ((FreeGrL.mapSp (barGen I hE)).app A y) = y :=
  FreeGrL.mapSp_retraction (fun _ _ _ w => retr_barGen hE h w) y

variable (q) in
/-- **The comparison morphism `qP^¡ → B(P, I)`** from the Koszul dual cooperad of the quadratic
part. -/
noncomputable def toBarQ : GrCooperadHom R (Dual R E q) (BarCoop I) :=
  (FreeGrL.mapCoop (barGen I hE)).comp (dualSub R E q).inclHom

omit [CharZero R] in
lemma toBarQ_app (x : Dual R E q A) :
    (toBarQ hE q).app A x
      = (FreeGrL.mapSp (barGen I hE)).app A ((dualSub R E q).incl A x) := rfl

omit [CharZero R] in
/-- **`(π ⋆ π) ∘ T^c(sE → sI) = proj ∘ (κ_T ⋆ κ_T)`.** -/
lemma toLin_star_pi_mapSp (y : Cut R E A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (Bar.pi I) (Bar.pi I)).1 A)
        ((FreeGrL.mapSp (barGen I hE)).app A y)
      = (𝒥).proj A (ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A) y) := by
  have h1 : GrOperad.Inv.appHom (ConvOp.preHom (P := ZeroDG R (Pres R E r))
        (FreeGrL.mapCoop (barGen I hE))) (Bar.pi I)
      = GrOperad.Inv.appHom (ConvOp.postHom (C := Cut R E)
        (GrOperadHom.toZeroDG (𝒥).projHom)) (kapT R E) :=
    Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun y =>
      piL_mapSp I hE y)
  have e1 := congrArg
    (fun X : GrOperad.Inv R (ConvOp R (Cut R E) (ZeroDG R (Pres R E r))) =>
      ConvOp.toLin (X.1 A) y)
    (GrOperad.Inv.appHom_star (ConvOp.preHom (P := ZeroDG R (Pres R E r))
      (FreeGrL.mapCoop (barGen I hE))) (Bar.pi I) (Bar.pi I))
  have e2 := congrArg
    (fun X : GrOperad.Inv R (ConvOp R (Cut R E) (ZeroDG R (Pres R E r))) =>
      ConvOp.toLin ((GrOperad.Inv.star R _ X X).1 A) y) h1
  have e3 := congrArg
    (fun X : GrOperad.Inv R (ConvOp R (Cut R E) (ZeroDG R (Pres R E r))) =>
      ConvOp.toLin (X.1 A) y)
    (GrOperad.Inv.appHom_star (ConvOp.postHom (C := Cut R E)
      (GrOperadHom.toZeroDG (𝒥).projHom)) (kapT R E) (kapT R E))
  exact e1.trans (e2.trans e3.symm)

variable (q) in
/-- The image of the Koszul dual cooperad of the quadratic part in the bar construction. -/
noncomputable def imDual : GrSubCooperad R (BarCoop I) :=
  (dualSub R E q).map (FreeGrL.mapCoop (barGen I hE))

variable (q) in
/-- The image of `qP^¡`, with its differentials. -/
noncomputable def imDualD : GrSubCooperad R (BarCoop I) := (imDual hE q).addD

/-- **The universal twisting morphism takes `qP^¡ + d_B qP^¡` into the generators.** -/
lemma piL_mem_genRange (h : IsQL I q) {x : BarCoop I A} (hx : x ∈ (imDualD hE q).sub A) :
    Bar.piL I A x ∈ genRange r A := by
  have hI0 : ∀ y ∈ I.sub (Fin 0), y = 0 := h.red (Fin 0) (by simp)
  obtain ⟨a, ⟨ya, hya, rfl⟩, c, ⟨yc, hyc, rfl⟩, rfl⟩ := (GrSubCooperad.mem_addD _).1 hx
  have h1 : Bar.piL I A ((FreeGrL.mapSp (barGen I hE)).app A ya) ∈ genRange r A := by
    rw [piL_mapSp I hE ya]
    exact ⟨FreeGrL.genCoef R E A (kapL R E A ya),
      (congrArg ((𝒥).proj A) (FreeGrL.eq_ι_genCoef (kapL_mem_vx ya))).symm⟩
  have hrel : ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A) yc
      ∈ relSp R E q A := by
    rw [← ideal_inf_vx_two h.quad]
    exact ⟨GrSubCooperad.cogen_le (admissible R E q) A hyc, star_mem_vx yc⟩
  have h2 : Bar.piL I A (DGCooperad.d (R := R) (C := BarCoop I)
      ((FreeGrL.mapSp (barGen I hE)).app A yc)) ∈ genRange r A := by
    rw [Bar.piL_d hI0, toLin_star_pi_mapSp hE yc]
    exact neg_mem (proj_relSp_mem h hrel)
  exact (map_add (Bar.piL I A) _ _).symm ▸ add_mem h1 h2

/-- The coefficient of the generators is not changed by the retraction, when the universal
twisting morphism takes its value in the generators. -/
lemma genCoef_mapSp_retr (h : IsQL I q) {x : BarCoop I A} (hx : Bar.piL I A x ∈ genRange r A) :
    FreeGrL.genCoef R (BarGen I) A ((FreeGrL.mapSp (barGen I hE)).app A
        ((FreeGrL.mapSp (retr hE h)).app A x))
      = FreeGrL.genCoef R (BarGen I) A x := by
  obtain ⟨ℓ, hℓ⟩ := hx
  have hg : FreeGrL.genCoef R (BarGen I) A x = (barGen I hE).app A ℓ :=
    IdealSp.ext I ((Bar.piL_eq_val_genCoef x).symm.trans hℓ.symm)
  rw [FreeGrL.genCoef_mapSp, FreeGrL.genCoef_mapSp, hg, retr_barGen]

/-- **`qP^¡ + d_B qP^¡` lies in the image of `T^c(sE)`**: the morphism `T^c(sE) → B(P, I)` after
the retraction is the identity on it, two morphisms of graded cooperads into the cut cooperad
with the same coefficient of the generators being equal. -/
theorem mapSp_mapSp_retr (h : IsQL I q) {x : BarCoop I A} (hx : x ∈ (imDualD hE q).sub A) :
    (FreeGrL.mapSp (barGen I hE)).app A ((FreeGrL.mapSp (retr hE h)).app A x) = x := by
  have hV0 : ∀ v : BarGen I (Fin 0), v = 0 := fun v =>
    IdealSp.ext I (h.red (Fin 0) (by simp) _ (IdealSp.mem I v))
  exact FreeGrL.app_eq_of_genCoef₀ hV0
    (f := (FreeGrL.mapCoop (barGen I hE)).comp
      ((FreeGrL.mapCoop (retr hE h)).comp (imDualD hE q).inclHom))
    (f' := (imDualD hE q).inclHom)
    (fun A _ _ x => genCoef_mapSp_retr hE h (piL_mem_genRange hE h x.2)) A ⟨x, hx⟩

end Koszul

/-! ## The differential of the Koszul dual cooperad -/

namespace Koszul

open FreeGrL

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {I : GrOperadIdeal R (Pres R E r)}
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)
  {q : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {A B : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R r

/-- The morphism `T^c(sE) → B(P, I)` of the suspended generators, as a linear map into the bar
construction. -/
noncomputable def cutBarL (A : Type) [Fintype A] [DecidableEq A] : Cut R E A →ₗ[R] BarCoop I A :=
  (FreeGrL.mapSp (barGen I hE)).app A

omit [CharZero R] in
lemma cutBarL_apply (y : Cut R E A) :
    cutBarL hE A y = (FreeGrL.mapSp (barGen I hE)).app A y := rfl

variable (q) in
/-- The image of `qP^¡ + d_B qP^¡` under the retraction, a subcooperad of `T^c(sE)`. -/
noncomputable def imRetr (h : IsQL I q) : GrSubCooperad R (Cut R E) :=
  (imDualD hE q).map (FreeGrL.mapCoop (retr hE h))

/-- `κ_T ⋆ κ_T` takes the retraction of a boundary of the image of `qP^¡` into `(q)`: its value
has two vertices and lies in `(r)`, since `π ⋆ π` vanishes on the boundaries. -/
lemma star_retr_d_mem (h : IsQL I q) {yc : Cut R E A} (hyc : yc ∈ (dualSub R E q).sub A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A)
      ((FreeGrL.mapSp (retr hE h)).app A (DGCooperad.d (R := R) (C := BarCoop I)
        ((FreeGrL.mapSp (barGen I hE)).app A yc))) ∈ (GrOperadIdeal.span R q).sub A := by
  have hI0 : ∀ y ∈ I.sub (Fin 0), y = 0 := h.red (Fin 0) (by simp)
  have hw : DGCooperad.d (R := R) (C := BarCoop I) ((FreeGrL.mapSp (barGen I hE)).app A yc)
      ∈ (imDualD hE q).sub A := GrSubCooperad.d_mem_addD (imDual hE q) ⟨yc, hyc, rfl⟩
  have e1 := toLin_star_pi_mapSp hE ((FreeGrL.mapSp (retr hE h)).app A
    (DGCooperad.d (R := R) (C := BarCoop I) ((FreeGrL.mapSp (barGen I hE)).app A yc)))
  have e2 := congrArg (fun z : BarCoop I A =>
    ConvOp.toLin ((GrOperad.Inv.star R _ (Bar.pi I) (Bar.pi I)).1 A) z)
    (mapSp_mapSp_retr hE h hw)
  have e3 := Bar.star_pi_d hI0 ((FreeGrL.mapSp (barGen I hE)).app A yc)
  exact h.quad_mem A _ (star_mem_vx _) (e1.symm.trans (e2.trans e3))

/-- `κ_T ⋆ κ_T` takes the retraction of `i a + d_B (i c)` into `(q)`, for `a` and `c` in
`qP^¡`. -/
lemma star_retr_mem (h : IsQL I q) {ya yc : Cut R E A} (hya : ya ∈ (dualSub R E q).sub A)
    (hyc : yc ∈ (dualSub R E q).sub A) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A)
      ((FreeGrL.mapSp (retr hE h)).app A (cutBarL hE A ya
        + DGCooperad.d (R := R) (C := BarCoop I) (cutBarL hE A yc)))
      ∈ (GrOperadIdeal.span R q).sub A := by
  have h3 : ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A) ya
      ∈ (GrOperadIdeal.span R q).sub A := GrSubCooperad.cogen_le (admissible R E q) A hya
  have e : (FreeGrL.mapSp (retr hE h)).app A (cutBarL hE A ya
        + DGCooperad.d (R := R) (C := BarCoop I) (cutBarL hE A yc))
      = ya + (FreeGrL.mapSp (retr hE h)).app A (DGCooperad.d (R := R) (C := BarCoop I)
        ((FreeGrL.mapSp (barGen I hE)).app A yc)) :=
    (map_add ((FreeGrL.mapSp (retr hE h)).app A) _ _).trans
      (congrArg (· + _) (mapSp_retr hE h ya))
  have e' := (congrArg (fun z : Cut R E A =>
    ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A) z) e).trans
      (map_add (ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A)) ya _)
  exact (congrArg (fun z => z ∈ (GrOperadIdeal.span R q).sub A) e').mpr
    (add_mem h3 (star_retr_d_mem hE h hyc))

/-- **The retraction of `qP^¡ + d_B qP^¡` lies in `qP^¡`**: `κ_T ⋆ κ_T` takes it into `(q)`. -/
theorem imRetr_le (h : IsQL I q) : imRetr hE q h ≤ dualSub R E q := by
  refine le_dualSub q fun A _ _ y hy => ?_
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨a, ha, c, hc, hac⟩ := (GrSubCooperad.mem_addD (imDual hE q)).1 hx
  obtain ⟨ya, hya, hya'⟩ := ha
  obtain ⟨yc, hyc, hyc'⟩ := hc
  have hx' : x = cutBarL hE A ya
      + DGCooperad.d (R := R) (C := BarCoop I) (cutBarL hE A yc) :=
    hac.symm.trans (congrArg₂ (fun u v : BarCoop I A =>
      u + DGCooperad.d (R := R) (C := BarCoop I) v) hya'.symm hyc'.symm)
  have hy' : y = (FreeGrL.mapSp (retr hE h)).app A (cutBarL hE A ya
      + DGCooperad.d (R := R) (C := BarCoop I) (cutBarL hE A yc)) :=
    hxy.symm.trans (congrArg ((FreeGrL.mapSp (retr hE h)).app A) hx')
  exact (congrArg (fun z : Cut R E A =>
    ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A) z
      ∈ (GrOperadIdeal.span R q).sub A) hy').mpr (star_retr_mem hE h hya hyc)

/-- The bar differential, as a linear map of the bar construction. -/
noncomputable abbrev dBar (I : GrOperadIdeal R (Pres R E r)) (A : Type) [Fintype A]
    [DecidableEq A] : BarCoop I A →ₗ[R] BarCoop I A :=
  DGCooperad.d (R := R) (C := BarCoop I)

/-- **The differential `d_φ` of the Koszul dual cooperad of the quadratic part**: the bar
differential of `B(P, I)` on the image of `qP^¡`, brought back by the retraction. -/
noncomputable def dQL (h : IsQL I q) (A : Type) [Fintype A] [DecidableEq A] :
    Dual R E q A →ₗ[R] Dual R E q A :=
  LinearMap.codRestrict ((dualSub R E q).sub A)
    ((FreeGrL.mapSp (retr hE h)).app A ∘ₗ dBar I A ∘ₗ (toBarQ hE q).app A)
    (fun c => imRetr_le hE h A
      ⟨_, GrSubCooperad.d_mem_addD (imDual hE q) ⟨_, c.2, rfl⟩, rfl⟩)

/-- **The comparison morphism `qP^¡ → B(P, I)` commutes with the differentials**:
`i ∘ d_φ = d_B ∘ i`. -/
theorem toBarQ_dQL (h : IsQL I q) (c : Dual R E q A) :
    (toBarQ hE q).app A (dQL hE h A c)
      = DGCooperad.d (R := R) (C := BarCoop I) ((toBarQ hE q).app A c) :=
  mapSp_mapSp_retr hE h (GrSubCooperad.d_mem_addD (imDual hE q) ⟨_, c.2, rfl⟩)

/-- The comparison morphism `qP^¡ → B(P, I)` is injective. -/
lemma toBarQ_injective (h : IsQL I q) : Function.Injective ((toBarQ hE q).app A) :=
  (FreeGrL.mapSp_injective_of_retraction (fun _ _ _ w => retr_barGen hE h w)).comp
    ((dualSub R E q).incl_injective A)

/-- **`d_φ² = 0`.** -/
theorem dQL_dQL (h : IsQL I q) (c : Dual R E q A) : dQL hE h A (dQL hE h A c) = 0 := by
  apply toBarQ_injective hE h
  rw [toBarQ_dQL, toBarQ_dQL, DGCooperad.d_d, map_zero]

/-- `d_φ` is odd. -/
lemma dQL_par (h : IsQL I q) (b : Bool) (c : Dual R E q A) :
    dQL hE h A (GrSpecies.par (R := R) b c) = GrSpecies.par (R := R) (!b) (dQL hE h A c) := by
  apply toBarQ_injective hE h
  rw [toBarQ_dQL, (toBarQ hE q).app_par, (toBarQ hE q).app_par, toBarQ_dQL,
    DGCooperad.d_par]

/-- `d_φ` commutes with the relabellings. -/
lemma map_dQL (h : IsQL I q) (e : A ≃ B) (c : Dual R E q A) :
    SymSpecies.map (R := R) e (dQL hE h A c) = dQL hE h B (SymSpecies.map (R := R) e c) := by
  apply toBarQ_injective hE h
  rw [toBarQ_dQL, (toBarQ hE q).app_map, (toBarQ hE q).app_map, toBarQ_dQL,
    DGCooperad.map_d]

/-- The counit kills `d_φ`. -/
lemma counit_dQL (h : IsQL I q) (c : Dual R E q Unit) :
    GrCooperad.counit (R := R) (C := Dual R E q) (dQL hE h Unit c) = 0 := by
  have h1 := LinearMap.congr_fun (toBarQ hE q).counit_app (dQL hE h Unit c)
  rw [LinearMap.comp_apply, toBarQ_dQL, DGCooperad.counit_d] at h1
  exact h1.symm

/-- The comparison morphism is injective on tensors. -/
lemma toBarQ_map_injective (h : IsQL I q) :
    Function.Injective
      (TensorProduct.map ((toBarQ hE q).app A) ((toBarQ hE q).app B)) := by
  have e : ∀ (A : Type) [Fintype A] [DecidableEq A],
      (FreeGrL.mapSp (retr hE h)).app A ∘ₗ (FreeGrL.mapSp (barGen I hE)).app A
        = LinearMap.id := fun A _ _ => LinearMap.ext fun y => mapSp_retr hE h y
  have hJ : Function.Injective (TensorProduct.map ((FreeGrL.mapSp (barGen I hE)).app A)
      ((FreeGrL.mapSp (barGen I hE)).app B)) :=
    Function.LeftInverse.injective
      (g := TensorProduct.map ((FreeGrL.mapSp (retr hE h)).app A)
        ((FreeGrL.mapSp (retr hE h)).app B)) fun t => by
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, e A, e B, TensorProduct.map_id]
      rfl
  have hc : TensorProduct.map ((toBarQ hE q).app A) ((toBarQ hE q).app B)
      = TensorProduct.map ((FreeGrL.mapSp (barGen I hE)).app A)
          ((FreeGrL.mapSp (barGen I hE)).app B) ∘ₗ
        TensorProduct.map ((dualSub R E q).incl A) ((dualSub R E q).incl B) := by
    rw [← TensorProduct.map_comp]
    rfl
  rw [hc]
  exact hJ.comp (dualSub R E q).map_incl_injective

/-- **`d_φ` is a coderivation.** -/
theorem decomp_dQL (h : IsQL I q) (i : A) (c : Dual R E q (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := Dual R E q) i (dQL hE h _ c)
      = TensorProduct.map (dQL hE h A) LinearMap.id
          (GrCooperad.decomp (R := R) (C := Dual R E q) i c)
        + TensorProduct.map (GrSpecies.par (R := R) (V := Dual R E q) false
            - GrSpecies.par (R := R) (V := Dual R E q) true) (dQL hE h B)
          (GrCooperad.decomp (R := R) (C := Dual R E q) i c) := by
  apply toBarQ_map_injective hE h
  have hd : ∀ (A : Type) [Fintype A] [DecidableEq A],
      dBar I A ∘ₗ (toBarQ hE q).app A = (toBarQ hE q).app A ∘ₗ dQL hE h A :=
    fun A _ _ => LinearMap.ext fun x => (toBarQ_dQL hE h x).symm
  have hτ : (GrSpecies.par (R := R) (V := BarCoop I) false
        - GrSpecies.par (R := R) (V := BarCoop I) true) ∘ₗ (toBarQ hE q).app A
      = (toBarQ hE q).app A ∘ₗ (GrSpecies.par (R := R) (V := Dual R E q) false
        - GrSpecies.par (R := R) (V := Dual R E q) true) :=
    LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub, (toBarQ hE q).app_par]
  have E1 : TensorProduct.map (dBar I A) (LinearMap.id (R := R) (M := BarCoop I B)) ∘ₗ
        TensorProduct.map ((toBarQ hE q).app A) ((toBarQ hE q).app B)
      = TensorProduct.map ((toBarQ hE q).app A) ((toBarQ hE q).app B) ∘ₗ
        TensorProduct.map (dQL hE h A) LinearMap.id := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hd A, LinearMap.id_comp,
      LinearMap.comp_id]
  have E2 : TensorProduct.map (GrSpecies.par (R := R) (V := BarCoop I) false
          - GrSpecies.par (R := R) (V := BarCoop I) true) (dBar I B) ∘ₗ
        TensorProduct.map ((toBarQ hE q).app A) ((toBarQ hE q).app B)
      = TensorProduct.map ((toBarQ hE q).app A) ((toBarQ hE q).app B) ∘ₗ
        TensorProduct.map (GrSpecies.par (R := R) (V := Dual R E q) false
          - GrSpecies.par (R := R) (V := Dual R E q) true) (dQL hE h B) := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hτ, hd B]
  have hdc := LinearMap.congr_fun ((toBarQ hE q).decomp_app (B := B) i)
  have s1 := (hdc (dQL hE h _ c)).symm
  have s2 := congrArg (GrCooperad.decomp (R := R) (C := BarCoop I) (B := B) i)
    (toBarQ_dQL hE h c)
  have s3 := DGCooperad.decomp_d (R := R) (C := BarCoop I) (B := B) i ((toBarQ hE q).app _ c)
  have s4 := hdc c
  have s5 := LinearMap.congr_fun E1 (GrCooperad.decomp (R := R) (C := Dual R E q) i c)
  have s6 := LinearMap.congr_fun E2 (GrCooperad.decomp (R := R) (C := Dual R E q) i c)
  rw [map_add]
  exact s1.trans (s2.trans (s3.trans ((congrArg (fun z =>
    TensorProduct.map (dBar I A) (LinearMap.id (R := R) (M := BarCoop I B)) z
      + TensorProduct.map (GrSpecies.par (R := R) (V := BarCoop I) false
        - GrSpecies.par (R := R) (V := BarCoop I) true) (dBar I B) z) s4).trans
    (congrArg₂ (· + ·) s5 s6))))

/-- **The Koszul dual cooperad of the quadratic part**, to carry the differential `d_φ`: the
Koszul dual dg cooperad `(qP^¡, d_φ)` of quadratic-linear data. -/
@[nolint unusedArguments]
def DualQL (_hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
      (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)
    (_h : IsQL I q) (A : Type) [Fintype A] [DecidableEq A] : Type u := Dual R E q A

noncomputable instance (h : IsQL I q) (A : Type) [Fintype A] [DecidableEq A] :
    AddCommGroup (DualQL hE h A) :=
  inferInstanceAs (AddCommGroup (Dual R E q A))

noncomputable instance (h : IsQL I q) (A : Type) [Fintype A] [DecidableEq A] :
    Module R (DualQL hE h A) :=
  inferInstanceAs (Module R (Dual R E q A))

/-- **The Koszul dual dg cooperad** `(qP^¡, d_φ)`. -/
noncomputable instance DualQL.instDGCooperad (h : IsQL I q) : DGCooperad R (DualQL hE h) :=
  { (inferInstance : GrCooperad R (Dual R E q)) with
    d := fun {A} _ _ => dQL hE h A
    d_d := fun {_} _ _ c => dQL_dQL hE h c
    d_par := fun {_} _ _ b c => dQL_par hE h b c
    map_d := fun {_ _} _ _ _ _ e c => map_dQL hE h e c
    counit_d := fun c => counit_dQL hE h c
    decomp_d := fun {_ _} _ _ _ _ i c => decomp_dQL hE h i c }

/-- The Koszul dual dg cooperad is coaugmented. -/
noncomputable instance DualQL.instCoaug (h : IsQL I q) : GrCooperad.Coaug R (DualQL hE h) :=
  inferInstanceAs (GrCooperad.Coaug R (Dual R E q))

lemma DualQL.d_apply (h : IsQL I q) (c : DualQL hE h A) :
    DGCooperad.d (R := R) (C := DualQL hE h) c = dQL hE h A c := rfl

/-- **The comparison morphism `(qP^¡, d_φ) → B(P, I)`**, a morphism of dg cooperads. -/
noncomputable def toBarDG (h : IsQL I q) : DGCooperadHom R (DualQL hE h) (BarCoop I) :=
  { toGrCooperadHom := toBarQ hE q
    app_d := fun c => toBarQ_dQL hE h c }

end Koszul

/-! ## The morphism `Ω(qP^¡, d_φ) → P` and the Koszul criterion -/

namespace Koszul

open FreeGrL

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {I : GrOperadIdeal R (Pres R E r)}
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)
  {q : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {A : Type} [Fintype A] [DecidableEq A]

local notation "𝒥" => GrOperadIdeal.span R r

omit [CharZero R] in
/-- The ideal of quadratic-linear data has no operations without inputs. -/
lemma IsQL.zero (h : IsQL I q) : ∀ y ∈ I.sub (Fin 0), y = 0 := h.red (Fin 0) (by simp)

include hE in
omit [CharZero R] in
/-- Quadratic-linear data have no generators with at most one input. -/
lemma IsQL.gen_eq_zero (h : IsQL I q) (B : Type) [Fintype B] [DecidableEq B]
    (hB : Fintype.card B ≤ 1) (v : E B) : v = 0 :=
  h.inj B v (h.red B hB _ (hE B v))

omit [CharZero R] in
/-- The comparison morphism preserves the coaugmentations. -/
lemma toBarQ_one : (toBarQ hE q).app Unit (GrCooperad.Coaug.one (R := R) (C := Dual R E q))
    = GrCooperad.Coaug.one (R := R) (C := BarCoop I) :=
  (FreeGrL.mapSp (barGen I hE)).app_one

/-- **`d_φ` kills the coaugmentation.** -/
instance DualQL.instDOne (h : IsQL I q) : DGCooperad.DOne R (DualQL hE h) :=
  ⟨toBarQ_injective hE h ((toBarQ_dQL hE h _).trans
    ((congrArg (DGCooperad.d (R := R) (C := BarCoop I)) (toBarQ_one hE)).trans
      (Bar.d_one.trans (map_zero ((toBarQ hE q).app Unit)).symm)))⟩

lemma toBarDG_one (h : IsQL I q) :
    (toBarDG hE h).app Unit (GrCooperad.Coaug.one (R := R) (C := DualQL hE h))
      = GrCooperad.Coaug.one (R := R) (C := BarCoop I) :=
  toBarQ_one hE

/-- **The morphism `Ω(qP^¡, d_φ) → P`**: the counit `ΩB(P, I) → P` of the bar–cobar adjunction
after `Ωi`. -/
noncomputable def cobarMorQL (h : IsQL I q) :
    GrOperadHom R (CobarGr R (DualQL hE h)) (ZeroDG R (Pres R E r)) :=
  (Bar.counit I h.zero).1.comp (CobarDG.map (toBarDG hE h) (toBarDG_one hE h))

/-- **The morphism `Ω(qP^¡, d_φ) → P` desuspends the cogenerators**: on `s⁻¹ c̄` it is `κ c`. -/
lemma cobarMorQL_ιL (h : IsQL I q) (c : DualQL hE h A) :
    (cobarMorQL hE h).app A (Cobar.ιL R (DualQL hE h) A c)
      = (𝒥).proj A (kapL R E A ((dualSub R E q).incl A c)) := by
  have e1 : (CobarDG.map (toBarDG hE h) (toBarDG_one hE h)).app A
      (Cobar.ιL R (DualQL hE h) A c)
      = Cobar.ιL R (BarCoop I) A ((toBarDG hE h).app A c) :=
    CobarMap.map_ιL (toBarDG hE h).toGrCooperadHom (toBarDG_one hE h) c
  exact (congrArg ((Bar.counit I h.zero).1.app A) e1).trans
    ((Bar.counit_ιL h.zero _).trans (piL_mapSp I hE _))

/-- **The morphism `Ω(qP^¡, d_φ) → P` commutes with the differentials**, `P` having the zero
differential. -/
lemma cobarMorQL_d (h : IsQL I q) (y : CobarGr R (DualQL hE h) A) :
    (cobarMorQL hE h).app A ((CobarDG.d R (DualQL hE h)).app A y)
      = DGOperad.d (R := R) (P := ZeroDG R (Pres R E r)) ((cobarMorQL hE h).app A y) :=
  (congrArg ((Bar.counit I h.zero).1.app A)
    (CobarDG.map_d (toBarDG hE h) (toBarDG_one hE h) y)).trans ((Bar.counit I h.zero).2 A _)

/-- **The Koszul criterion for quadratic-linear data.** Over a field of characteristic zero,
for an ideal `I` of `P` complementing the units, with a free unit: **the morphism
`Ω(qP^¡, d_φ) → P` is a quasi-isomorphism iff the comparison morphism
`(qP^¡, d_φ) → B(P, I)` is one in the arities at least two.** -/
theorem cobarMorQL_bijective_iff (h : IsQL I q)
    (hcompl : ∀ (A : Type) [Fintype A] [DecidableEq A],
      IsCompl (Bar.unitsP (Pres R E r) A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := Pres R E r) = 0 → a = 0) :
    (∀ (A : Type) [Fintype A] [DecidableEq A],
      Function.Bijective (Homology.map (dV := (CobarDG.d R (DualQL hE h)).app A)
        (dW := DGOperad.d (R := R) (P := ZeroDG R (Pres R E r)) (A := A))
        ((cobarMorQL hE h).app A) fun y => cobarMorQL_d hE h y)) ↔
    ∀ (B : Type) [Fintype B] [DecidableEq B], 2 ≤ Fintype.card B →
      Function.Bijective (Homology.map (dV := DGCooperad.d (R := R) (C := DualQL hE h) (A := B))
        (dW := DGCooperad.d (R := R) (C := BarCoop I) (A := B)) ((toBarDG hE h).app B)
          fun x => (toBarDG hE h).app_d x) := by
  refine Iff.trans ?_ (CobarDG.map_bijective_iff (toBarDG hE h) (toBarDG_one hE h)
    (fun B _ _ hB x => dual_mem_unitSpan (r := q) (h.gen_eq_zero hE) hB x)
    (fun B _ _ hB x => bar_mem_unitSpan I h.red hB x)).symm
  refine forall_congr' fun A => forall_congr' fun _ => forall_congr' fun _ => ?_
  exact Homology.bijective_comp_iff rfl _ ((Bar.counit I h.zero).2 A) _
    (Bar.counit_bijective (I := I) (A := A) h.zero (hcompl A) hone)

end Koszul

/-! ## The twisting morphism, the cogenerator part of `d_φ`, and the homogeneous case -/

namespace Koszul

open FreeGrL

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {I : GrOperadIdeal R (Pres R E r)}
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)
  {q : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {A : Type} [Fintype A] [DecidableEq A]

local notation "𝒥" => GrOperadIdeal.span R r

/-- **The Koszul twisting morphism of quadratic-linear data** `κ : (qP^¡, d_φ) → P`: the
twisting morphism of the morphism `Ω(qP^¡, d_φ) → P`, by the cobar adjunction. -/
noncomputable def twistingQL (h : IsQL I q) :
    TwistingDG R (DualQL hE h) (ZeroDG R (Pres R E r)) :=
  CobarDG.homEquiv ⟨cobarMorQL hE h, fun _ _ _ y => cobarMorQL_d hE h y⟩

/-- The Koszul twisting morphism is the desuspension map, restricted to `qP^¡` and projected
onto `P`. -/
lemma twistingQL_apply (h : IsQL I q) (c : DualQL hE h A) :
    ConvOp.toLin ((twistingQL hE h).1.1 A) c
      = (𝒥).proj A (kapL R E A ((dualSub R E q).incl A c)) :=
  cobarMorQL_ιL hE h c

/-- **The cogenerator part of `d_φ`**: `κ ∘ d_φ = -(κ ⋆ κ)`, the desuspension of `d_φ c` is, in
`P`, minus the convolution square `(κ_T ⋆ κ_T)(c)`, an element of the quadratic part `qR`. -/
theorem proj_kapL_dQL (h : IsQL I q) (c : Dual R E q A) :
    (𝒥).proj A (kapL R E A ((dualSub R E q).incl A (dQL hE h A c)))
      = -(𝒥).proj A (ConvOp.toLin ((GrOperad.Inv.star R _ (kapT R E) (kapT R E)).1 A)
          ((dualSub R E q).incl A c)) :=
  (piL_mapSp I hE _).symm.trans ((congrArg (Bar.piL I A) (toBarQ_dQL hE h c)).trans
    ((Bar.piL_d h.zero _).trans (congrArg Neg.neg (toLin_star_pi_mapSp hE _))))

/-- **`d_φ` is the only map intertwined with the bar differential** by the comparison
morphism: it does not depend on the retraction. -/
theorem dQL_unique (h : IsQL I q) {d' : Dual R E q A →ₗ[R] Dual R E q A}
    (hd : ∀ c, (toBarQ hE q).app A (d' c)
      = DGCooperad.d (R := R) (C := BarCoop I) ((toBarQ hE q).app A c)) :
    d' = dQL hE h A :=
  LinearMap.ext fun c => toBarQ_injective hE h ((hd c).trans (toBarQ_dQL hE h c).symm)

end Koszul

namespace Koszul

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {q : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {I : GrOperadIdeal R (Pres R E q)}
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R q).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)
  {A : Type} [Fintype A] [DecidableEq A]

/-- **The homogeneous case**: when the relators are the quadratic elements themselves,
`d_φ = 0`. -/
theorem dQL_eq_zero (h : IsQL I q) (c : Dual R E q A) : dQL hE h A c = 0 :=
  toBarQ_injective hE h ((toBarQ_dQL hE h c).trans
    ((d_toBar I hE h.red c).trans (map_zero ((toBarQ hE q).app A)).symm))

end Koszul

end Operad
