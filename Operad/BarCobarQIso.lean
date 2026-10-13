/-
# The bar–cobar resolution

For a graded operad `P` and an ideal `I`, the cobar construction `ΩB(P, I)` of the bar
construction is the cobar construction `ΩC` of the cut cooperad `C = FreeGrL R (s I)`, with the
differential `D = d - δ`: `d` the cobar differential of the cut cooperad, cutting the trees
decorating the generators, and `δ` the derivation extending `s⁻¹ c̄ ↦ s⁻¹ (d_B c)‾`, contracting
their edges (`Bar.δI`). Contracting an edge removes a vertex (`Bar.wtD_d`), so `δ` lowers the
weight by one, `E` counting the vertices of the trees decorating the generators.

**Theorem A: the bar–cobar resolution** (`Bar.counit_bijective`, `Bar.homologyEquiv`). Over a
`ℚ`-algebra, for a graded operad `P = R 1 ⊕ I` augmented by an ideal without operations without
inputs, with a free unit, **the counit `ΩB(P, I) → P` is a quasi-isomorphism**: it induces a
bijection on homology (`Homology.map`), as it maps the cycles onto `P`
(`Bar.exists_cycle_counit_eq`), and a cycle mapped to zero is a boundary
(`Bar.exists_d_eq_of_counit_eq_zero`). By the contraction identity `d h + h d = E - (1 - ε)`, the
cobar differential is acyclic in each weight `n ≥ 2`, the weights at most one are the units and the
generators of the corollas, on which the counit is injective, and the inner differential lowers
the weight (`Cobar.exists_sub_eq`).
-/
import Operad.CobarWeight
import Operad.BarCobar

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr

section Helpers

variable {R : Type u} [CommRing R] {M N Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]

omit [Module R M] in
private lemma alg_δι (a b : M) : -a - (-a - b) = b := by abel

private lemma alg_wtd (E d : M →ₗ[R] M) (x : M) {ι : Type*} (S : Finset ι) (s : ι → R)
    (z : ι → M) (w : R) (hdx : d x = ∑ k ∈ S, s k • z k)
    (hz : ∀ k ∈ S, E (z k) = (w - 1) • z k) (hx : E x = w • x) :
    E (d x) = d (E x) - d x := by
  have e : ∀ k ∈ S, E (s k • z k) = (w - 1) • (s k • z k) := fun k hk => by
    rw [map_smul, hz k hk, smul_comm]
  rw [hx, map_smul, hdx, map_sum, Finset.sum_congr rfl e, ← Finset.smul_sum, sub_smul, one_smul]

private lemma lin_eq_of_single' {α : Type*} (F G : M →ₗ[R] N) (f : (α →₀ R) →ₗ[R] M)
    (h : ∀ a, F (f (Finsupp.single a 1)) = G (f (Finsupp.single a 1))) (x : α →₀ R) :
    F (f x) = G (f x) :=
  LinearMap.congr_fun (Finsupp.lhom_ext' fun a => LinearMap.ext_ring (h a) :
    F.comp f = G.comp f) x

end Helpers

/-! ## Differences of derivations -/

section GrDerSub

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {f : GrOperadHom R P Q} {e : Bool}

/-- **The difference of two derivations** along the same morphism, of the same parity. -/
def GrDer.sub (D D' : GrDer f e) : GrDer f e where
  app A _ _ := D.app A - D'.app A
  app_par c x := by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, D.app_par, D'.app_par, map_sub]
  app_map σ' x := by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, D.app_map, D'.app_map, map_sub]
  app_one := by rw [LinearMap.sub_apply, D.app_one, D'.app_one, sub_zero]
  app_comp i x y := by
    simp only [LinearMap.sub_apply, D.app_comp, D'.app_comp, map_sub]
    abel

lemma GrDer.sub_app (D D' : GrDer f e) {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    (D.sub D').app A x = D.app A x - D'.app A x := rfl

end GrDerSub

section Internal

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {I : GrOperadIdeal R P} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒞" => FreeGrL R (BarGen I)
local notation "𝒥" => GrOperadIdeal.span R (grLinRel R (BarGen I))
local notation "𝒥Ω" => GrOperadIdeal.span R (grLinRel R (CobarGen R 𝒞))
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R (BarGen I))) R
local notation "𝔅" => SgnLin.bas (treeSgn (grGenPar R (CobarGen R 𝒞))) R

namespace Bar

/-! ## Contracting an edge removes a vertex -/

private lemma wtD_d_bas (t : Reg (TreeOfArity (BarT I)) A) :
    (FreeGrL.wtD R (BarGen I)).app A (Bar.d I A ((𝒥).proj A (𝔟 t)))
      = Bar.d I A ((FreeGrL.wtD R (BarGen I)).app A ((𝒥).proj A (𝔟 t)))
        - Bar.d I A ((𝒥).proj A (𝔟 t)) := by
  refine alg_wtd ((FreeGrL.wtD R (BarGen I)).app A) (Bar.d I A) ((𝒥).proj A (𝔟 t))
    (Finset.Ico 1 (treeOf t).weight)
    (fun k => σ R (Tree.contrSgn (grGenPar R (BarGen I)) (treeOf t) k))
    (fun k => (𝒥).proj A (𝔟 (contrR (barMerge I) t k))) ((treeOf t).weight : R) ?_ ?_
    (FreeGrL.wtD_proj_bas t)
  · exact (Bar.d_proj _).trans ((congrArg _
      (barD_bas (barMerge I) (grGenPar R (BarGen I)) R t)).trans ((map_sum _ _ _).trans
        (Finset.sum_congr rfl fun k _ => map_smul _ _ _)))
  · intro k hk
    rw [Finset.mem_Ico] at hk
    have hw := Tree.weight_contr (barMerge I) hk.1 hk.2
    rw [FreeGrL.wtD_proj_bas, treeOf_contrR, ← hw, Nat.cast_succ, add_sub_cancel_right]

/-- **The bar differential lowers the number of vertices by one**: `E d = d E - d` on the bar
construction, `E` counting the vertices of the trees. -/
theorem wtD_d (c : 𝒞 A) :
    (FreeGrL.wtD R (BarGen I)).app A (Bar.d I A c)
      = Bar.d I A ((FreeGrL.wtD R (BarGen I)).app A c) - Bar.d I A c := by
  have h := Function.surjInv_eq ((𝒥).proj_surjective A) c
  rw [← h]
  exact lin_eq_of_single' ((FreeGrL.wtD R (BarGen I)).app A ∘ₗ Bar.d I A)
    (Bar.d I A ∘ₗ (FreeGrL.wtD R (BarGen I)).app A - Bar.d I A) ((𝒥).proj A)
    (fun t => wtD_d_bas t) _

/-! ## The internal part of the differential of `ΩB(P, I)` -/

variable (I) in
/-- **The differential of `ΩB(P, I)`**, as a derivation of the cobar construction of the
underlying cut cooperad. -/
noncomputable def DB : GrDer (GrOperadHom.id R (CobarGr R 𝒞)) true := CobarDG.d R (BarCoop I)

private lemma DB_DB (Y : CobarGr R 𝒞 A) : (DB I).app A ((DB I).app A Y) = 0 := by
  have h : ∀ Y' : CobarGr R (BarCoop I) A,
      (CobarDG.d R (BarCoop I)).app A ((CobarDG.d R (BarCoop I)).app A Y') = 0 :=
    fun Y' => CobarDG.d_d R (BarCoop I) Y'
  exact h Y

variable (I) in
/-- **The internal part of the differential of `ΩB(P, I)`**: the cobar differential of the cut
cooperad minus the differential of `ΩB(P, I)`, the derivation extending `s⁻¹ c̄ ↦ s⁻¹ (d c)‾`. -/
noncomputable def δI : GrDer (GrOperadHom.id R (CobarGr R 𝒞)) true :=
  (Cobar.d R 𝒞).sub (DB I)

private lemma d_sub_δI (Y : CobarGr R 𝒞 A) :
    (Cobar.d R 𝒞).app A Y - (δI I).app A Y = (DB I).app A Y :=
  sub_sub_cancel _ _

private lemma δB_ιL (c : BarCoop I A) :
    (Cobar.d R (BarCoop I)).app A (Cobar.ιL R (BarCoop I) A c)
      - (CobarDG.d R (BarCoop I)).app A (Cobar.ιL R (BarCoop I) A c)
      = Cobar.ιL R (BarCoop I) A (DGCooperad.d (R := R) c) :=
  (congrArg₂ (· - ·) (Cobar.d_ιL R (BarCoop I) c) (CobarDG.d_ιL R (BarCoop I) c)).trans
    (alg_δι _ _)

private lemma δI_ιL (c : 𝒞 A) :
    (δI I).app A (Cobar.ιL R 𝒞 A c) = Cobar.ιL R 𝒞 A (Bar.d I A c) := by
  have h : ∀ c' : BarCoop I A,
      (Cobar.d R (BarCoop I)).app A (Cobar.ιL R (BarCoop I) A c')
        - (CobarDG.d R (BarCoop I)).app A (Cobar.ιL R (BarCoop I) A c')
        = Cobar.ιL R (BarCoop I) A (DGCooperad.d (R := R) c') := fun c' => δB_ιL c'
  exact h c

/-! ## The counit -/

/-- No generators without inputs when the ideal has no operations without inputs. -/
lemma barGen_zero (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (v : BarGen I (Fin 0)) : v = 0 :=
  IdealSp.ext I ((hI0 _ (IdealSp.mem I v)).trans (IdealSp.val_zero (I := I)).symm)

variable (P) in
/-- The span of the relabellings of the unit of a graded operad. -/
abbrev unitsP (A : Type) [Fintype A] [DecidableEq A] : Submodule R (P A) :=
  Submodule.span R (Set.range fun e : Unit ≃ A =>
    GrOperad.map (R := R) e (GrOperad.one (R := R) (P := P)))

variable (I) in
/-- **The counit `ΩB(P, I) → P`**, on the cobar construction of the underlying cut cooperad. -/
noncomputable def cΩ (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (A : Type) [Fintype A]
    [DecidableEq A] : CobarGr R 𝒞 A →ₗ[R] P A :=
  (counit I hI0).1.app A

private lemma cΩ_DB (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (Y : CobarGr R 𝒞 A) :
    cΩ I hI0 A ((DB I).app A Y) = 0 := by
  have h : ∀ Y' : CobarGr R (BarCoop I) A,
      (counit I hI0).1.app A ((CobarDG.d R (BarCoop I)).app A Y') = 0 :=
    fun Y' => ((counit I hI0).2 A Y').trans (LinearMap.zero_apply _)
  exact h Y

private lemma cΩ_unit (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (e : Unit ≃ A) :
    cΩ I hI0 A (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞)))
      = GrOperad.map (R := R) e (GrOperad.one (R := R) (P := P)) := by
  have h : (counit I hI0).1.app A (GrOperad.map (R := R) e
      (GrOperad.one (R := R) (P := CobarGr R (BarCoop I))))
      = GrOperad.map (R := R) e (GrOperad.one (R := R) (P := ZeroDG R P)) :=
    ((counit I hI0).1.app_map e _).trans (congrArg _ (counit I hI0).1.app_one)
  exact h

private lemma cΩ_ιL (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (v : BarGen I A) :
    cΩ I hI0 A (Cobar.ιL R 𝒞 A ((FreeGrL.ι R (BarGen I)).app A v)) = IdealSp.val I v := by
  have h : ∀ v' : BarGen I A, (counit I hI0).1.app A
      (Cobar.ιL R (BarCoop I) A ((FreeGrL.ι R (BarGen I)).app A v')) = IdealSp.val I v' :=
    fun v' => (counit_ιL hI0 _).trans (piL_ι v')
  exact h v

omit [Fintype A] [DecidableEq A] in
private lemma smul_one_eq_zero [Fintype A] [DecidableEq A] {a : R} (e : Unit ≃ A)
    (h : a • GrOperad.map (R := R) e (GrOperad.one (R := R) (P := P)) = 0) :
    a • GrOperad.one (R := R) (P := P) = 0 := by
  have h3 := congrArg (GrOperad.map (R := R) e.symm) h
  rwa [map_smul, ← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl, map_zero] at h3

/-- **The counit is injective on the units and the generators of the corollas**, for an augmented
operad `P = R 1 ⊕ I` with a free unit. -/
private lemma base (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (hcompl : IsCompl (unitsP P A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := P) = 0 → a = 0) :
    ∀ u ∈ Cobar.unitsΩ R (BarGen I) A, ∀ v : BarGen I A,
      cΩ I hI0 A (u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R (BarGen I)).app A v)) = 0 →
        u + Cobar.ιL R 𝒞 A ((FreeGrL.ι R (BarGen I)).app A v) = 0 := by
  intro u hu v hc
  have hsum : cΩ I hI0 A u + IdealSp.val I v = 0 :=
    (congrArg (cΩ I hI0 A u + ·) (cΩ_ιL hI0 v)).symm.trans ((map_add _ _ _).symm.trans hc)
  have hmem : cΩ I hI0 A u ∈ I.sub A :=
    (congrArg (· ∈ I.sub A) (eq_neg_of_add_eq_zero_left hsum)).mpr
      (Submodule.neg_mem _ (IdealSp.mem I v))
  have hunit : ∀ e : Unit ≃ A, cΩ I hI0 A
      (GrOperad.map (R := R) e (GrOperad.one (R := R) (P := CobarGr R 𝒞))) ∈ unitsP P A :=
    fun e => (congrArg (· ∈ unitsP P A) (cΩ_unit hI0 e)).mpr
      (Submodule.subset_span ⟨e, rfl⟩ :
        GrOperad.map (R := R) e (GrOperad.one (R := R) (P := P)) ∈ unitsP P A)
  have h0 : cΩ I hI0 A u = 0 :=
    Submodule.disjoint_def.1 hcompl.disjoint _ (Cobar.map_mem_of_unitsΩ _ hunit hu) hmem
  have hval : IdealSp.val I v = 0 :=
    (zero_add _).symm.trans ((congrArg (· + IdealSp.val I v) h0).symm.trans hsum)
  have hv0 : v = 0 := IdealSp.ext I (hval.trans (IdealSp.val_zero (I := I)).symm)
  have hu0 : u = 0 := Cobar.eq_zero_of_unitsΩ (cΩ I hI0 A)
    (fun e a h => hone a (smul_one_eq_zero e ((congrArg (a • ·) (cΩ_unit hI0 e)).symm.trans h)))
    hu h0
  exact (congrArg₂ (· + ·) hu0 ((congrArg (fun w => Cobar.ιL R 𝒞 A
    ((FreeGrL.ι R (BarGen I)).app A w)) hv0).trans ((congrArg _ (map_zero _)).trans
      (map_zero _)))).trans (add_zero 0)

private lemma hDD (Y : CobarGr R 𝒞 A) :
    (Cobar.d R 𝒞).app A ((Cobar.d R 𝒞).app A Y - (δI I).app A Y)
      - (δI I).app A ((Cobar.d R 𝒞).app A Y - (δI I).app A Y) = 0 :=
  (d_sub_δI _).trans ((congrArg _ (d_sub_δI Y)).trans (DB_DB Y))

/-! ## Theorem A -/

/-- **A cycle of `ΩB(P, I)` killed by the counit is a boundary**, on the cobar construction of the
underlying cut cooperad. -/
private theorem exists_DB_eq [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hcompl : IsCompl (unitsP P A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := P) = 0 → a = 0) {Y : CobarGr R 𝒞 A}
    (hY : (DB I).app A Y = 0) (hc : cΩ I hI0 A Y = 0) : ∃ Z, (DB I).app A Z = Y :=
  (Cobar.exists_sub_eq (δI I) (Bar.d I) (fun _ _ _ c => δI_ιL c) (fun _ _ _ c => wtD_d c)
    (cΩ I hI0 A) (barGen_zero hI0) hDD
    (fun y => (congrArg _ (d_sub_δI y)).trans (cΩ_DB hI0 y)) (base hI0 hcompl hone) Y
    ((d_sub_δI Y).trans hY) hc).elim fun Z hZ => ⟨Z, (d_sub_δI Z).symm.trans hZ⟩

/-- **Every operation is the counit of a cycle of `ΩB(P, I)`**, on the cobar construction of the
underlying cut cooperad. -/
private theorem exists_DB_eq_zero_cΩ_eq [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hcompl : IsCompl (unitsP P A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := P) = 0 → a = 0) (p : P A) :
    ∃ Y : CobarGr R 𝒞 A, (DB I).app A Y = 0 ∧ cΩ I hI0 A Y = p := by
  have hp : p ∈ unitsP P A ⊔ I.sub A := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  have hle : unitsP P A ≤ (Cobar.unitsΩ R (BarGen I) A).map (cΩ I hI0 A) :=
    Submodule.span_le.2 fun _ ⟨e, he⟩ => he ▸ Submodule.mem_map.2
      ⟨_, Submodule.subset_span ⟨e, rfl⟩, cΩ_unit hI0 e⟩
  exact (Submodule.mem_sup.1 hp).elim fun u hu => hu.2.elim fun a ha =>
    (Submodule.mem_map.1 (hle hu.1)).elim fun û hû =>
      ⟨û + Cobar.ιL R 𝒞 A ((FreeGrL.ι R (BarGen I)).app A (IdealSp.mk I a ha.1)),
        (d_sub_δI _).symm.trans (Cobar.sub_eq_zero_of_low (δI I) (Bar.d I)
          (fun _ _ _ c => δI_ιL c) (fun _ _ _ c => wtD_d c) (cΩ I hI0 A) (barGen_zero hI0)
          (fun y => (congrArg _ (d_sub_δI y)).trans (cΩ_DB hI0 y)) (base hI0 hcompl hone)
          hû.1 (IdealSp.mk I a ha.1)),
        ((map_add _ _ _).trans (congrArg₂ (· + ·) hû.2 (cΩ_ιL hI0 _))).trans ha.2⟩

/-! ## The bar–cobar resolution -/

/-- **Theorem A: the bar–cobar resolution, injectivity on homology.** Over a `ℚ`-algebra, for a
graded operad `P = R 1 ⊕ I` augmented by an ideal without operations without inputs, with a free
unit, a cycle of `ΩB(P, I)` mapped to zero by the counit is a boundary. -/
theorem exists_d_eq_of_counit_eq_zero [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hcompl : IsCompl (unitsP P A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := P) = 0 → a = 0)
    {Y : CobarGr R (BarCoop I) A} (hY : (CobarDG.d R (BarCoop I)).app A Y = 0)
    (hc : (counit I hI0).1.app A Y = 0) :
    ∃ Z : CobarGr R (BarCoop I) A, (CobarDG.d R (BarCoop I)).app A Z = Y :=
  exists_DB_eq hI0 hcompl hone hY hc

/-- **Theorem A: the bar–cobar resolution, surjectivity on homology**: every operation of `P` is
the counit of a cycle of `ΩB(P, I)`. -/
theorem exists_cycle_counit_eq [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hcompl : IsCompl (unitsP P A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := P) = 0 → a = 0) (p : P A) :
    ∃ Y : CobarGr R (BarCoop I) A,
      (CobarDG.d R (BarCoop I)).app A Y = 0 ∧ (counit I hI0).1.app A Y = p :=
  exists_DB_eq_zero_cΩ_eq hI0 hcompl hone p

variable (I) in
/-- **The homology of the bar–cobar resolution**: the cycles modulo the boundaries. -/
abbrev Homology (A : Type) [Fintype A] [DecidableEq A] : Type _ :=
  LinearMap.ker ((CobarDG.d R (BarCoop I)).app A) ⧸
    (LinearMap.range ((CobarDG.d R (BarCoop I)).app A)).comap
      (LinearMap.ker ((CobarDG.d R (BarCoop I)).app A)).subtype

variable (I) in
/-- The counit on the cycles. -/
noncomputable def counitCycles (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0) (A : Type) [Fintype A]
    [DecidableEq A] : LinearMap.ker ((CobarDG.d R (BarCoop I)).app A) →ₗ[R] ZeroDG R P A :=
  (counit I hI0).1.app A ∘ₗ (LinearMap.ker ((CobarDG.d R (BarCoop I)).app A)).subtype

private lemma ker_counitCycles [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hcompl : IsCompl (unitsP P A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := P) = 0 → a = 0) :
    LinearMap.ker (counitCycles I hI0 A)
      = (LinearMap.range ((CobarDG.d R (BarCoop I)).app A)).comap
          (LinearMap.ker ((CobarDG.d R (BarCoop I)).app A)).subtype := by
  ext ⟨y, hy⟩
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range]
  constructor
  · exact fun hc => exists_d_eq_of_counit_eq_zero hI0 hcompl hone hy hc
  · rintro ⟨Z, rfl⟩
    exact ((counit I hI0).2 A Z).trans (LinearMap.zero_apply _)

private lemma counitCycles_surjective [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hcompl : IsCompl (unitsP P A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := P) = 0 → a = 0) :
    Function.Surjective (counitCycles I hI0 A) := fun p =>
  (exists_cycle_counit_eq hI0 hcompl hone p).elim fun Y hY => ⟨⟨Y, hY.1⟩, hY.2⟩

variable (I) in
/-- **Theorem A: the bar–cobar resolution.** Over a `ℚ`-algebra, for a graded operad `P = R 1 ⊕ I`
augmented by an ideal without operations without inputs, with a free unit, **the counit
`ΩB(P, I) → P` is a quasi-isomorphism**: it induces an isomorphism from the homology of
`ΩB(P, I)` onto `P`. -/
noncomputable def homologyEquiv [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hcompl : IsCompl (unitsP P A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := P) = 0 → a = 0) :
    Homology I A ≃ₗ[R] ZeroDG R P A :=
  (Submodule.quotEquivOfEq _ _ (ker_counitCycles hI0 hcompl hone)).symm.trans
    (LinearMap.quotKerEquivOfSurjective _ (counitCycles_surjective hI0 hcompl hone))

lemma homologyEquiv_mk [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hcompl : IsCompl (unitsP P A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := P) = 0 → a = 0)
    (y : LinearMap.ker ((CobarDG.d R (BarCoop I)).app A)) :
    homologyEquiv I hI0 hcompl hone (Submodule.Quotient.mk y) = (counit I hI0).1.app A y :=
  rfl

/-- **Theorem A: the bar–cobar resolution.** Over a `ℚ`-algebra, for a graded operad
`P = R 1 ⊕ I` augmented by an ideal without operations without inputs, with a free unit, **the
counit `ΩB(P, I) → P` is a quasi-isomorphism**: it induces a bijection on homology. -/
theorem counit_bijective [Algebra ℚ R] (hI0 : ∀ x ∈ I.sub (Fin 0), x = 0)
    (hcompl : IsCompl (unitsP P A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := P) = 0 → a = 0) :
    Function.Bijective (Operad.Homology.map (dV := (CobarDG.d R (BarCoop I)).app A)
      (dW := DGOperad.d (R := R) (P := ZeroDG R P) (A := A))
      ((counit I hI0).1.app A) ((counit I hI0).2 A)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, fun w => ?_⟩
  · refine (Operad.Homology.mk_surjective _ z).elim fun y hy => ?_
    subst hy
    have h0 : (counit I hI0).1.app A y.1 = 0 := by
      have h1 := (Operad.Homology.mk_eq_mk_iff
        (d := DGOperad.d (R := R) (P := ZeroDG R P) (A := A)) _ 0).1 (hz.trans (map_zero _).symm)
      exact h1.elim fun v hv => (sub_zero _).symm.trans (hv.symm.trans (LinearMap.zero_apply v))
    refine (exists_d_eq_of_counit_eq_zero hI0 hcompl hone y.2 h0).elim fun Z hZ => ?_
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨Z, hZ⟩
  · refine (Operad.Homology.mk_surjective _ w).elim fun p hp => ?_
    subst hp
    refine (exists_cycle_counit_eq hI0 hcompl hone p.1).elim fun Y hY =>
      ⟨Operad.Homology.mk _ ⟨Y, hY.1⟩, ?_⟩
    exact congrArg (Operad.Homology.mk _) (Subtype.ext hY.2)

end Bar

end Internal

end Operad
