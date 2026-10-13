/-
# Weights in the bar construction

For a graded operad `P` and an ideal `I` without operations with at most one input, the bar
differential `d` of `B(P, I) = T^c(sI)` **raises nothing and lowers the number of vertices by
one** (`Bar.wtD_d`): it kills the trees with at most one vertex (`Bar.d_vx_zero`,
`Bar.d_vx_one`), so **its values have at least one vertex** (`Bar.d_mem_vxGe_one`). The
universal twisting morphism `π` only sees the trees with one vertex (`Bar.piL_vx`), on which it
is injective, so a value of `d` killed by `π` has at least two vertices (`Bar.mem_vxGe_two`).

**A morphism of graded cooperads `f : C → B(P, I)` with `π ∘ d ∘ f = 0` satisfies `d ∘ f = 0`**
(`Bar.d_app_eq_zero`), over a `ℚ`-algebra: if all the values of `d ∘ f` have at least `k ≥ 2`
vertices, the coderivation rule `(ι ⋆ ι) ∘ d ∘ f = ±(ι d f) ⋆ (ι f) ± (ι f) ⋆ (ι d f)` gives their
convolution squares weight at least `k + 1` (`Bar.ιι_d_mem`), so they have at least `k + 1`
vertices (`Cobar.mem_vxGe_succ`), and the trees in arity `A` have fewer than `|A|` vertices.
-/
import Operad.ConvFilt
import Operad.BarCobar
import Operad.BarCobarQIso

universe u v w

namespace Operad

open Sym GerBV FreeGrL FreeGr
open scoped TensorProduct

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

/-- **Every tree has a number of vertices.** -/
lemma iSup_vx (A : Type) [Fintype A] [DecidableEq A] : ⨆ j : ℕ, vx R V j A = ⊤ :=
  iSup_eig_eq_top (a := GrSpEnd.id R V) (fun A _ _ v =>
    Submodule.mem_iSup_of_mem 1 (by
      rw [Module.End.mem_eigenspace_iff, Nat.cast_one, one_smul]
      rfl)) A

/-- The trees with at least `p` vertices have at least `q ≤ p` vertices. -/
lemma vxGe_anti {A : Type} [Fintype A] [DecidableEq A] {p q : ℕ} (h : q ≤ p) :
    vxGe R V p A ≤ vxGe R V q A :=
  iSup_le fun j => le_iSup_of_le (⟨j.1, le_trans h j.2⟩ : {j : ℕ // q ≤ j}) le_rfl

end FreeGrL

namespace Cobar

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A : Type} [Fintype A] [DecidableEq A]

local notation "𝒞" => FreeGrL R V

/-- **The weights at least `k`**. -/
noncomputable abbrev wtGe (k : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    Submodule R (CobarGr R 𝒞 A) :=
  ⨆ j : {j : ℕ // k ≤ j}, wt R V j.1 A

lemma par_mem_wt (b : Bool) {j : ℕ} {Y : CobarGr R 𝒞 A} (hY : Y ∈ wt R V j A) :
    GrOperad.par (R := R) b Y ∈ wt R V j A :=
  mem_wt.2 (((wtΩ R V).app_par b Y).trans (by
    rw [Bool.xor_false, mem_wt.1 hY, map_smul]))

lemma wtGe_par (k : ℕ) (b : Bool) {Y : CobarGr R 𝒞 A} (hY : Y ∈ wtGe k A) :
    GrOperad.par (R := R) b Y ∈ wtGe (V := V) k A :=
  (iSup_le (fun j _ hz => Submodule.mem_iSup_of_mem j (par_mem_wt b hz)) :
    wtGe (V := V) k A ≤ (wtGe k A).comap (GrOperad.par (R := R) b)) hY

lemma wtGe_map {B : Type} [Fintype B] [DecidableEq B] (k : ℕ) (e : A ≃ B)
    {Y : CobarGr R 𝒞 A} (hY : Y ∈ wtGe k A) :
    GrOperad.map (R := R) e Y ∈ wtGe (V := V) k B :=
  (iSup_le (fun j _ hz => Submodule.mem_iSup_of_mem j (map_mem_wt e hz)) :
    wtGe (V := V) k A ≤ (wtGe k B).comap (GrOperad.map (R := R) e)) hY

lemma wtGe_comp {B : Type} [Fintype B] [DecidableEq B] (a b : ℕ) (r : A)
    {Y : CobarGr R 𝒞 A} {Z : CobarGr R 𝒞 B} (hY : Y ∈ wtGe a A) (hZ : Z ∈ wtGe b B) :
    GrOperad.comp (R := R) r Y Z ∈ wtGe (V := V) (a + b) _ := by
  refine (iSup_le (fun i y hy => ?_) : wtGe (V := V) a A ≤ (wtGe (a + b) _).comap
    ((GrOperad.comp (R := R) r).flip Z)) hY
  refine (iSup_le (fun j z hz => ?_) : wtGe (V := V) b B ≤ (wtGe (a + b) _).comap
    (GrOperad.comp (R := R) r y)) hZ
  exact Submodule.mem_iSup_of_mem (⟨i.1 + j.1, by have := i.2; have := j.2; omega⟩ :
    {j : ℕ // a + b ≤ j}) (comp_mem_wt r hy hz)

lemma wtGe_par_all (k : ℕ) : ∀ (A : Type) [Fintype A] [DecidableEq A] (b : Bool)
    (Y : CobarGr R 𝒞 A), Y ∈ wtGe (V := V) k A → GrOperad.par (R := R) b Y ∈ wtGe (V := V) k A :=
  fun _ _ _ b _ hY => wtGe_par k b hY

lemma wtGe_map_all (k : ℕ) : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (e : A ≃ B) (Y : CobarGr R 𝒞 A), Y ∈ wtGe (V := V) k A →
    GrOperad.map (R := R) e Y ∈ wtGe (V := V) k B :=
  fun _ _ _ _ _ _ e _ hY => wtGe_map k e hY

lemma wtGe_comp_all (a b c : ℕ) (h : c ≤ a + b) : ∀ (A B : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (r : A) (Y : CobarGr R 𝒞 A) (Z : CobarGr R 𝒞 B),
    Y ∈ wtGe (V := V) a A → Z ∈ wtGe (V := V) b B →
    GrOperad.comp (R := R) r Y Z ∈ wtGe (V := V) c _ :=
  fun _ _ _ _ _ _ r _ _ hY hZ =>
    (iSup_le fun j => le_iSup_of_le (⟨j.1, le_trans h j.2⟩ : {j : ℕ // c ≤ j}) le_rfl :
      wtGe (V := V) (a + b) _ ≤ wtGe c _) (wtGe_comp a b r hY hZ)

/-- The generators of the trees with at least `k` vertices have weight at least `k`. -/
lemma ιL_mem_wtGe {k : ℕ} {y : 𝒞 A} (hy : y ∈ vxGe R V k A) : ιL R 𝒞 A y ∈ wtGe (V := V) k A :=
  (iSup_le (fun j _ hz => Submodule.mem_iSup_of_mem j (ιL_mem_wt hz)) :
    vxGe R V k A ≤ (wtGe (V := V) k A).comap (ιL R 𝒞 A)) hy

/-- **The generators of the trees without vertices vanish**, over a `ℚ`-algebra. -/
lemma ιL_vx_zero [Algebra ℚ R] {y : 𝒞 A} (hy : y ∈ vx R V 0 A) : ιL R 𝒞 A y = 0 := by
  have h := mem_unitsΩ_of_mem_wt (ιL_mem_wt hy)
  rw [← FreeGrL.secC_of_unitCoeff (unitCoeffL_ιL y)]
  refine Submodule.span_induction (p := fun Y _ => FreeGrL.secC R (CobarGen R 𝒞) A Y = 0)
    ?_ (map_zero _) (fun Y Z _ _ hY hZ => by beta_reduce at hY hZ ⊢; rw [map_add, hY, hZ, add_zero])
    (fun c Y _ hY => by beta_reduce at hY ⊢; rw [map_smul, hY, smul_zero]) h
  rintro _ ⟨e, rfl⟩
  exact FreeGrL.secC_unit e

/-- **The generators have weight at least one**, over a `ℚ`-algebra. -/
lemma ιL_mem_wtGe_one [Algebra ℚ R] (y : 𝒞 A) : ιL R 𝒞 A y ∈ wtGe (V := V) 1 A := by
  have hy : y ∈ ⨆ j : ℕ, vx R V j A := (iSup_vx (R := R) (V := V) A).symm ▸ Submodule.mem_top
  refine (iSup_le (fun j z hz => ?_) : (⨆ j : ℕ, vx R V j A) ≤ (wtGe (V := V) 1 A).comap
    (ιL R 𝒞 A)) hy
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [Submodule.mem_comap, ιL_vx_zero hz]
    exact zero_mem _
  · exact Submodule.mem_iSup_of_mem (⟨j, h⟩ : {j : ℕ // 1 ≤ j}) (ιL_mem_wt hz)

end Cobar

namespace ConvOp

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [D : DGCooperad R C']
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  (f : GrCooperadHom R C C') {ι' : GrOperad.Inv R (ConvOp R C' Q)}
  (hι : GrOperad.Inv.IsPar true ι')
include hι

/-- An odd family precomposed with the differential, then with a morphism. -/
lemma toLin_appHom_preDer {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    toLin ((GrOperad.Inv.appHom (preHom (P := Q) f)
      (GrOperad.Inv.appDer (preDer (C := C') (P := Q)) ι')).1 A) x
      = -toLin (ι'.1 A) (DGCooperad.d (R := R) (f.app A x)) := by
  show toLin (GrOperad.tw (R := R) true (ι'.1 A)) (DGCooperad.d (R := R) (f.app A x)) = _
  rw [GrOperad.tw_hom true (hι A), Bool.and_self, σ_true, neg_one_smul, toLin_neg,
    LinearMap.neg_apply]

/-- **The coderivation rule for the square of an odd family**: `(ι ⋆ ι) ∘ d ∘ f =
(ι d f) ⋆ (ι f) - (ι f) ⋆ (ι d f)`, with `ι d` carrying the Koszul sign. -/
lemma toLin_star_d {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    toLin ((GrOperad.Inv.star R _ ι' ι').1 A) (DGCooperad.d (R := R) (f.app A x))
      = toLin ((GrOperad.Inv.star R _
          (GrOperad.Inv.appHom (preHom (P := Q) f)
            (GrOperad.Inv.appDer (preDer (C := C') (P := Q)) ι'))
          (GrOperad.Inv.appHom (preHom (P := Q) f) ι')).1 A) x
        - toLin ((GrOperad.Inv.star R _ (GrOperad.Inv.appHom (preHom (P := Q) f) ι')
          (GrOperad.Inv.appHom (preHom (P := Q) f)
            (GrOperad.Inv.appDer (preDer (C := C') (P := Q)) ι'))).1 A) x := by
  have h := GrOperad.Inv.appDer_star (preDer (C := C') (P := Q)) hι ι'
  have h2 := congrArg (GrOperad.Inv.appHom (preHom (P := Q) f)) h
  rw [map_add, map_smul, GrOperad.Inv.appHom_star, GrOperad.Inv.appHom_star] at h2
  have e := congrArg (fun q : GrOperad.Inv R (ConvOp R C Q) => toLin (q.1 A) x) h2
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.neg_apply, Bool.and_self,
    σ_true, neg_one_smul, ← sub_eq_add_neg] at e
  have hιι : GrOperad.Inv.IsPar false (GrOperad.Inv.star R _ ι' ι') := by
    have := GrOperad.Inv.isPar_star hι hι
    rwa [Bool.xor_self] at this
  refine Eq.trans ?_ e
  show _ = toLin (GrOperad.tw (R := R) true ((GrOperad.Inv.star R _ ι' ι').1 A))
    (DGCooperad.d (R := R) (f.app A x))
  rw [GrOperad.tw_hom true (hιι A), Bool.true_and, σ_false, one_smul]

/-- **The coderivation rule, filtered**: if `ι ∘ d ∘ f` and `ι ∘ f` take values in `F` and `G`,
with `F ∘ G` and `G ∘ F` in `H`, then `(ι ⋆ ι) ∘ d ∘ f` takes values in `H`. -/
theorem toLin_star_d_mem {F G H : ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (Q A)}
    (hF : ∀ (A : Type) [Fintype A] [DecidableEq A] (b : Bool) (y : Q A), y ∈ F A →
      GrOperad.par (R := R) b y ∈ F A)
    (hG : ∀ (A : Type) [Fintype A] [DecidableEq A] (b : Bool) (y : Q A), y ∈ G A →
      GrOperad.par (R := R) b y ∈ G A)
    (hH : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
      (y : Q A), y ∈ H A → GrOperad.map (R := R) e y ∈ H B)
    (hFG : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (y : Q A) (z : Q B), y ∈ F A → z ∈ G B → GrOperad.comp (R := R) i y z ∈ H _)
    (hGF : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (y : Q A) (z : Q B), y ∈ G A → z ∈ F B → GrOperad.comp (R := R) i y z ∈ H _)
    (hα : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      toLin (ι'.1 A) (DGCooperad.d (R := R) (f.app A x)) ∈ F A)
    (hβ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), toLin (ι'.1 A) (f.app A x) ∈ G A)
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) :
    toLin ((GrOperad.Inv.star R _ ι' ι').1 A) (DGCooperad.d (R := R) (f.app A x)) ∈ H A := by
  have hα' : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      toLin ((GrOperad.Inv.appHom (preHom (P := Q) f)
        (GrOperad.Inv.appDer (preDer (C := C') (P := Q)) ι')).1 A) x ∈ F A := fun A _ _ x => by
    rw [toLin_appHom_preDer f hι]
    exact neg_mem (hα A x)
  rw [toLin_star_d f hι x]
  exact sub_mem (toLin_star_mem hG hH hFG hα' hβ A x) (toLin_star_mem hF hH hGF hβ hα' A x)

end ConvOp

namespace Bar

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R (BarGen I))
local notation "𝒞" => FreeGrL R (BarGen I)

lemma d_map (e : A ≃ B) (X : 𝒞 A) :
    d I B (GrOperad.map (R := R) e X) = GrOperad.map (R := R) e (d I A X) := by
  obtain ⟨x, rfl⟩ := (𝒥).proj_surjective A X
  show (𝒥).proj B (barD (barMerge I) (grGenPar R (BarGen I)) R B (GrOperad.map (R := R) e x))
    = (𝒥).proj B (GrOperad.map (R := R) e (barD (barMerge I) (grGenPar R (BarGen I)) R A x))
  rw [map_barD]

/-- **The bar differential kills the generators.** -/
lemma d_ι (w : BarGen I A) : d I A ((FreeGrL.ι R (BarGen I)).app A w) = 0 := by
  rw [GrSpeciesHom.app_eq_chart (FreeGrL.ι R (BarGen I)) (Fintype.equivFin A).symm,
    FreeGrL.ι_app_fin]
  show d I A (GrOperad.map (R := R) (Fintype.equivFin A).symm
    ((𝒥).proj _ (FreeGr.gen _) + (𝒥).proj _ (FreeGr.gen _))) = 0
  rw [d_map, map_add, d_proj, d_proj, barD_gen, barD_gen, map_zero, add_zero, map_zero]

/-- **The bar differential lowers the number of vertices by one.** -/
lemma d_vx_succ {j : ℕ} {z : 𝒞 A} (hz : z ∈ vx R (BarGen I) (j + 1) A) :
    d I A z ∈ vx R (BarGen I) j A :=
  mem_eig.2 (by
    rw [← Cobar.wtD_eq_derSp, wtD_d, Cobar.wtD_eq_derSp, mem_eig.1 hz, map_smul, Nat.cast_succ,
      add_smul, one_smul, add_sub_cancel_right])

/-- **The bar differential kills the trees without vertices.** -/
lemma d_vx_zero [Algebra ℚ R] {z : 𝒞 A} (hz : z ∈ vx R (BarGen I) 0 A) : d I A z = 0 := by
  refine eq_zero_of_eigen_neg R ((derSp (GrSpEnd.id R (BarGen I))).app A)
    (iSup_vx (R := R) (V := BarGen I) A) (m := 1) one_ne_zero ?_
  rw [← Cobar.wtD_eq_derSp, wtD_d, Cobar.wtD_eq_derSp, mem_eig.1 hz, Nat.cast_zero, zero_smul,
    map_zero, zero_sub, Nat.cast_one, neg_one_smul]

/-- **The bar differential kills the trees with one vertex.** -/
lemma d_vx_one [Algebra ℚ R] {z : 𝒞 A} (hz : z ∈ vx R (BarGen I) 1 A) : d I A z = 0 := by
  rw [FreeGrL.eq_ι_genCoef hz, d_ι]

/-- **The values of the bar differential have at least one vertex.** -/
lemma d_mem_vxGe_one [Algebra ℚ R] (y : 𝒞 A) : d I A y ∈ vxGe R (BarGen I) 1 A := by
  have hy : y ∈ ⨆ j : ℕ, vx R (BarGen I) j A :=
    (iSup_vx (R := R) (V := BarGen I) A).symm ▸ Submodule.mem_top
  refine (iSup_le (fun j z hz => ?_) : (⨆ j : ℕ, vx R (BarGen I) j A)
    ≤ (vxGe R (BarGen I) 1 A).comap (d I A)) hy
  rw [Submodule.mem_comap]
  match j, hz with
  | 0, hz => rw [d_vx_zero hz]; exact zero_mem _
  | 1, hz => rw [d_vx_one hz]; exact zero_mem _
  | j + 2, hz => exact mem_vxGe (by omega) (d_vx_succ hz)

/-- **The universal twisting morphism only sees the trees with one vertex.** -/
lemma piL_vx [Algebra ℚ R] {j : ℕ} (hj : j ≠ 1) {z : 𝒞 A} (hz : z ∈ vx R (BarGen I) j A) :
    piL I A z = 0 :=
  FreeGrL.snd_eq_zero_of_vx (epsHom I) (fun A _ _ w => by rw [epsHom_ι]; rfl) hj hz

/-- **A value of `π` vanishing with at least one vertex has at least two.** -/
lemma mem_vxGe_two [Algebra ℚ R] {y : 𝒞 A} (hy : y ∈ vxGe R (BarGen I) 1 A)
    (hπ : piL I A y = 0) : y ∈ vxGe R (BarGen I) 2 A := by
  rw [vxGe_eq 1] at hy
  obtain ⟨z, hz, y', hy', rfl⟩ := Submodule.mem_sup.1 hy
  have h2 : piL I A y' = 0 :=
    (iSup_le (fun j w hw => by
      rw [LinearMap.mem_ker, piL_vx (by have := j.2; omega) hw]) :
      vxGe R (BarGen I) 2 A ≤ LinearMap.ker (piL I A)) hy'
  rw [map_add, h2, add_zero, FreeGrL.eq_ι_genCoef hz, piL_ι] at hπ
  have hg : FreeGrL.genCoef R (BarGen I) A z = 0 := IdealSp.ext I hπ
  rw [FreeGrL.eq_ι_genCoef hz, hg, map_zero, zero_add]
  exact hy'

variable (I) in
/-- The bar differential, as a dg cooperad structure on the cut cooperad. -/
@[reducible] noncomputable def dgFree : DGCooperad R (FreeGrL R (BarGen I)) where
  toGrCooperad := FreeGrL.instGrCooperad R (BarGen I)
  d := fun {A} _ _ => d I A
  d_d := (instDGCooperad I).d_d
  d_par := (instDGCooperad I).d_par
  map_d := (instDGCooperad I).map_d
  counit_d := (instDGCooperad I).counit_d
  decomp_d := (instDGCooperad I).decomp_d

/-- **The coderivation rule**: when all the values of `d ∘ f` have at least `k` vertices, their
convolution squares have weight at least `k + 1`. -/
lemma ιι_d_mem [Algebra ℚ R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
    (f : GrCooperadHom R C 𝒞) {k : ℕ}
    (hk : ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      d I A' (f.app A' x') ∈ vxGe R (BarGen I) k A')
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) :
    ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) (d I A (f.app A x))
      ∈ Cobar.wtGe (V := BarGen I) (k + 1) A := by
  exact ConvOp.toLin_star_d_mem (D := dgFree I) f (Cobar.isPar_ι R 𝒞)
    (Cobar.wtGe_par_all k) (Cobar.wtGe_par_all 1) (Cobar.wtGe_map_all (k + 1))
    (Cobar.wtGe_comp_all k 1 (k + 1) le_rfl) (Cobar.wtGe_comp_all 1 k (k + 1) (by omega))
    (fun A' _ _ x' => Cobar.ιL_mem_wtGe (hk A' x')) (fun A' _ _ x' => Cobar.ιL_mem_wtGe_one _) A x

/-- **A morphism of graded cooperads into the bar construction whose composite with `π ∘ d`
vanishes commutes with the differentials**: `π ∘ d ∘ f = 0` implies `d ∘ f = 0`, over a
`ℚ`-algebra, for an ideal without operations with at most one input. -/
theorem d_app_eq_zero [Algebra ℚ R]
    (hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ v : BarGen I B, v = 0)
    {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
    (f : GrCooperadHom R C 𝒞)
    (hπ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), piL I A (d I A (f.app A x)) = 0)
    (A : Type) [Fintype A] [DecidableEq A] (x : C A) : d I A (f.app A x) = 0 := by
  have hV0 : ∀ v : BarGen I (Fin 0), v = 0 := hred (Fin 0) (by simp)
  have key : ∀ k, 2 ≤ k → ∀ (A' : Type) [Fintype A'] [DecidableEq A'] (x' : C A'),
      d I A' (f.app A' x') ∈ vxGe R (BarGen I) k A' := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact fun A' _ _ x' => mem_vxGe_two (d_mem_vxGe_one _) (hπ A' x')
    | succ k hk ih =>
      exact fun A' _ _ x' => Cobar.mem_vxGe_succ hV0 hk (ih A' x') (ιι_d_mem f ih A' x')
  have h := key (max 2 (Fintype.card A)) (le_max_left _ _) A x
  have hle := vxGe_anti (R := R) (V := BarGen I) (A := A) (le_max_right 2 (Fintype.card A))
  rw [vxGe_card hred] at hle
  exact (Submodule.mem_bot R).1 (hle h)

end Bar

end Operad
