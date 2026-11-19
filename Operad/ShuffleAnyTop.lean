/-
# The comparison morphism onto the cycles on the diagonal, for generators of any arity

Step (2c) of the symmetric–shuffle bridge for generators of any arity, third part; the binary
case is `Operad.ShuffleBarTop`. Setting as in `Operad.ShuffleAnyQuot`, with quadratic relators
over a field of characteristic zero.

* **Cycles along a morphism with a retraction** (`Bar.decomp_mem_cyc_of_retr`, `Bar.cycSubRetr`):
  for a morphism of graded cooperads `f : C → B(P, I)` with a retraction `ρ` killing the
  boundaries `d (f y)`, the elements `y` with `d (f y) = 0` form a subcooperad: by the
  coderivation rule the two terms of the decomposition of a boundary vanish separately,
  `f ∘ ρ` fixing one and killing the other. For binary generators the vertex count separated
  them; with generators of several arities it does not.
* **The retraction kills the boundaries of `T^c(sE)`** (`ShuffleAnySym.barRet_d_cutBar`): the
  retraction `ShuffleAnySym.barRet` factors through the bar construction of the quotient of
  `T(E)` by all the trees with two vertices (`ShuffleAnySym.quadAll`, `ShuffleAnySym.toQuadAll`),
  in which the bar differential kills `T^c(sE)` (`ShuffleAnySym.d_cutBar_quadAll`, by
  `Bar.d_app_eq_zero`, `κ_T ⋆ κ_T` landing in the trees with two vertices).
* Hence the cycles of `T^c(sE) → B(P, Ī_P)` are a subcooperad inside `P^¡`
  (`ShuffleAnySym.cutCyc_le`), and **`P^¡` maps onto the cycles of `B(P, Ī_P)` in the image of
  `T^c(sE)`** (`ShuffleAnySym.toBar_surj_diag`).
-/
import Operad.ShuffleAnyProj
import Operad.ShuffleBarTop
import Operad.KoszulCorel

universe u v

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace Bar

variable {R : Type u} [Field R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (I : GrOperadIdeal R P) {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  (f : GrCooperadHom R C (FreeGrL R (BarGen I)))
  (ρ : ∀ (A : Type) [Fintype A] [DecidableEq A], FreeGrL R (BarGen I) A →ₗ[R] C A)
  (hρ : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : C A), ρ A (f.app A y) = y)
  (hρd : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : C A), ρ A (d I A (f.app A y)) = 0)

local notation "𝒞" => FreeGrL R (BarGen I)

include hρ hρd in
/-- **The cycles along a morphism of graded cooperads with a retraction killing its boundaries
are closed under the decompositions**: by the coderivation rule, `d ⊗ 1` and `1 ⊗ d` kill the
decomposition of a cycle separately, the retraction followed by the morphism fixing the values
and killing their boundaries. -/
theorem decomp_mem_cyc_of_retr {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (i : A) {x : C (Without A i ⊕ B)} (hx : d I _ (f.app _ x) = 0) :
    GrCooperad.decomp (R := R) i x ∈ LinearMap.range (TensorProduct.map
      (LinearMap.ker (d I A ∘ₗ f.app A)).subtype (LinearMap.ker (d I B ∘ₗ f.app B)).subtype) := by
  have hf : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Injective (f.app A) :=
    fun A _ _ y y' h => by rw [← hρ A y, ← hρ A y', h]
  have e : GrCooperad.decomp (R := R) (C := 𝒞) i (d I _ (f.app _ x))
      = TensorProduct.map (d I A) LinearMap.id (GrCooperad.decomp (R := R) (C := 𝒞) i (f.app _ x))
        + TensorProduct.map (GrSpecies.par (R := R) (V := 𝒞) false
          - GrSpecies.par (R := R) (V := 𝒞) true) (d I B)
            (GrCooperad.decomp (R := R) (C := 𝒞) i (f.app _ x)) :=
    (instDGCooperad I).decomp_d i (f.app _ x)
  have e2 := LinearMap.congr_fun (f.decomp_app i) x
  simp only [LinearMap.comp_apply] at e2
  refine TensorProduct.mem_range_of_coderiv (f.app A) (f.app B) (d I A)
    (f.app A ∘ₗ ρ A) (GrSpecies.par (R := R) (V := 𝒞) false
      - GrSpecies.par (R := R) (V := 𝒞) true) (d I B) (GrSpecies.tw (R := R) (V := C) true)
    (2 : R) (hf A) (hf B) (fun y => ?_) (fun y => (app_tw I f y).symm)
    (fun y => ?_) (fun y => ?_) ?_
  · rw [GrSpecies.tw_tw, Bool.xor_self, GrSpecies.tw_false]
  · rw [LinearMap.comp_apply, hρd, map_zero, sub_self, zero_smul]
  · rw [LinearMap.comp_apply, hρ, show (2 : R) - 1 = 1 by norm_num, one_smul]
  · rw [← e2, ← e, hx, map_zero]

/-- **The cycles along a morphism of graded cooperads into the bar construction with a retraction
killing its boundaries**: the elements `y` with `d (f y) = 0`, a subcooperad. -/
noncomputable def cycSubRetr : GrSubCooperad R C where
  sub A _ _ := LinearMap.ker (d I A ∘ₗ f.app A)
  par_mem {A} _ _ b x hx := by
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    rw [f.app_par]
    exact ((instDGCooperad I).d_par b (f.app A x)).trans (by
      show GrSpecies.par (R := R) (V := 𝒞) (!b) (d I A (f.app A x)) = 0
      rw [hx, map_zero])
  map_mem {A B} _ _ _ _ e x hx := by
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    rw [f.app_map]
    exact ((instDGCooperad I).map_d e (f.app A x)).symm.trans (by
      show SymSpecies.map (R := R) (V := 𝒞) e (d I A (f.app A x)) = 0
      rw [hx, map_zero])
  decomp_mem {A B} _ _ _ _ i x hx := decomp_mem_cyc_of_retr I f ρ hρ hρd i hx

end Bar

namespace ShuffleAnySym

open ShuffleBarSym

variable {K : Type u} [Field K] [CharZero K]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {T : ℕ → Type} [IsEmpty (T 0)] [IsEmpty (T 1)]
  (c : ∀ k, Module.Basis (T k) K (E (Fin k)))
  (hc : ∀ k (β : T k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))
  (hq : Koszul.IsQuadratic K E r)

local notation "𝒥" => GrOperadIdeal.span K r

/-- **The morphism of cut cooperads `T^c(sE) → B(P, Ī_P)`** induced by `sE → sĪ_P`. -/
noncomputable abbrev cutBarP :
    GrCooperadHom K (Koszul.Cut K E) (FreeGrL K (BarGen (Ipres K E c hc r))) :=
  FreeGrL.mapCoop (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))

/-! ### The quotient by all the trees with two vertices -/

variable (K E) in
/-- **All the quadratic relators**: the trees with two vertices. -/
def quadAll (n : ℕ) : Set (FreeGrL K E (Fin n)) := (FreeGrL.wtEqL K E 2 (Fin n) : Set _)

omit [CharZero K] in
lemma isQuadratic_quadAll : Koszul.IsQuadratic K E (quadAll K E) := fun _ _ hx => hx

omit [CharZero K] [IsEmpty (T 0)] [IsEmpty (T 1)] in
include hq in
lemma span_le_quadAll : GrOperadIdeal.span K r ≤ GrOperadIdeal.span K (quadAll K E) :=
  GrOperadIdeal.span_le.2 fun n _ hx => GrOperadIdeal.subset_span n (hq n hx)

omit [IsEmpty (T 0)] [IsEmpty (T 1)] in
/-- The trees with two vertices lie in the ideal they generate, in every arity. -/
lemma vx_two_le_quadAll {A : Type} [Fintype A] [DecidableEq A] :
    FreeGrL.vx K E 2 A ≤ (GrOperadIdeal.span K (quadAll K E)).sub A := by
  intro x hx
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  have h1 : GrOperad.map (R := K) e x ∈ (GrOperadIdeal.span K (quadAll K E)).sub (Fin _) :=
    GrOperadIdeal.subset_span _ ((FreeGrL.wtEqL_eq_vx 2).ge (FreeGrL.map_mem_eig e hx))
  have h2 := (GrOperadIdeal.span K (quadAll K E)).map_mem e.symm h1
  rwa [← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl] at h2

/-- **The projection of the presented operad onto the quotient by all the trees with two
vertices.** -/
noncomputable def toQuadAll :
    GrOperadHom K (Koszul.Pres K E r) (Koszul.Pres K E (quadAll K E)) :=
  (GrOperadIdeal.span K r).liftHom (GrOperadIdeal.span K (quadAll K E)).projHom
    fun A _ _ x hx => by
      rw [GrOperadIdeal.projHom_app, GrOperadIdeal.proj_eq_zero_iff]
      exact span_le_quadAll r hq A hx

omit [CharZero K] [IsEmpty (T 0)] [IsEmpty (T 1)] in
lemma toQuadAll_proj {A : Type} [Fintype A] [DecidableEq A] (y : FreeGrL K E A) :
    (toQuadAll r hq).app A ((𝒥).proj A y) = (GrOperadIdeal.span K (quadAll K E)).proj A y :=
  rfl

/-- The projection of the suspended ideals. -/
noncomputable def quadGen : GrSpeciesHom K (BarGen (Ipres K E c hc r))
    (BarGen (Ipres K E c hc (quadAll K E))) :=
  Bar.mapGen (toQuadAll r hq) fun A _ _ x hx => by
    by_cases h : 2 ≤ Fintype.card A
    · rw [GrOperadIdeal.atLeastTwo_sub_of_le h]
      trivial
    · rw [GrOperadIdeal.atLeastTwo_sub_of_lt (by omega), Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact zero_mem _

omit [CharZero K] in
lemma quadGen_barGen {A : Type} [Fintype A] [DecidableEq A] (v : GrSpecies.Shift E K A) :
    (quadGen c hc r hq).app A ((Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r)).app A v)
      = (Koszul.barGen (Ipres K E c hc (quadAll K E)) (hE_pres c hc (quadAll K E))).app A v :=
  IdealSp.ext _ rfl

omit [IsEmpty (T 1)] in
lemma barRet_quadGen {A : Type} [Fintype A] [DecidableEq A]
    (w : BarGen (Ipres K E c hc r) A) :
    (barRet c hc (quadAll K E) isQuadratic_quadAll).app A ((quadGen c hc r hq).app A w)
      = (barRet c hc r hq).app A w := by
  obtain ⟨y, hy⟩ := (𝒥).proj_surjective A (IdealSp.val _ w)
  show presCoef (quadAll K E) isQuadratic_quadAll A
      ((toQuadAll r hq).app A (IdealSp.val _ w)) = presCoef r hq A (IdealSp.val _ w)
  rw [← hy, toQuadAll_proj, presCoef_proj, presCoef_proj]

/-- **The bar differential kills `T^c(sE)` in the quotient by all the trees with two vertices**:
`π ∘ d` is `κ_T ⋆ κ_T`, which lands in the trees with two vertices. -/
theorem d_cutBar_quadAll {A : Type} [Fintype A] [DecidableEq A] (y : Koszul.Cut K E A) :
    Bar.d (Ipres K E c hc (quadAll K E)) A
      ((FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc (quadAll K E))
        (hE_pres c hc (quadAll K E)))).app A y) = 0 := by
  have hI1 : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ y ∈ (Ipres K E c hc (quadAll K E)).sub B, y = 0 :=
    GrOperadIdeal.atLeastTwo_hI1 (pres_zero c hc (quadAll K E))
  have hred : ∀ (B : Type) [Fintype B] [DecidableEq B], Fintype.card B ≤ 1 →
      ∀ v : BarGen (Ipres K E c hc (quadAll K E)) B, v = 0 :=
    fun B _ _ hB v => IdealSp.ext _ (hI1 B hB _ (IdealSp.mem _ v))
  have hI0 : ∀ x ∈ (Ipres K E c hc (quadAll K E)).sub (Fin 0), x = 0 := hI1 (Fin 0) (by simp)
  refine Bar.d_app_eq_zero hred (cutBarP c hc (quadAll K E)) (fun A' _ _ x => ?_) A y
  refine Bar.piL_d_app hI0 (Koszul.cutBar (Ipres K E c hc (quadAll K E))
    (hE_pres c hc (quadAll K E))) (Koszul.pi_cutBar _ _) x ?_
  have e2 := GrOperad.Inv.appHom_star (ConvOp.postHom (C := Koszul.Cut K E)
    (GrOperadHom.toZeroDG (GrOperadIdeal.span K (quadAll K E)).projHom)) (Koszul.kapT K E)
    (Koszul.kapT K E)
  have h2 := congrArg (fun q : GrOperad.Inv K (ConvOp K (Koszul.Cut K E)
    (ZeroDG K (Koszul.Pres K E (quadAll K E)))) => ConvOp.toLin (q.1 A') x) e2
  have hr : ConvOp.toLin ((GrOperad.Inv.appHom (ConvOp.postHom (C := Koszul.Cut K E)
      (GrOperadHom.toZeroDG (GrOperadIdeal.span K (quadAll K E)).projHom))
      (GrOperad.Inv.star K _ (Koszul.kapT K E) (Koszul.kapT K E))).1 A') x
      = (GrOperadIdeal.span K (quadAll K E)).proj A'
        (ConvOp.toLin ((GrOperad.Inv.star K _ (Koszul.kapT K E) (Koszul.kapT K E)).1 A') x) :=
    rfl
  exact h2.symm.trans (hr.trans ((GrOperadIdeal.proj_eq_zero_iff _ _).2
    (vx_two_le_quadAll (Koszul.star_mem_vx x))))

/-! ### The cycles on the diagonal -/

omit [IsEmpty (T 1)] in
lemma mapSp_barRet_quadGen {A : Type} [Fintype A] [DecidableEq A]
    (z : FreeGrL K (BarGen (Ipres K E c hc r)) A) :
    (FreeGrL.mapSp (barRet c hc (quadAll K E) isQuadratic_quadAll)).app A
      ((FreeGrL.mapSp (quadGen c hc r hq)).app A z)
        = (FreeGrL.mapSp (barRet c hc r hq)).app A z :=
  (FreeGrL.mapSp_comp (barRet c hc (quadAll K E) isQuadratic_quadAll)
    (quadGen c hc r hq) z).trans
    (FreeGrL.mapSp_congr
      (φ := (barRet c hc (quadAll K E) isQuadratic_quadAll).comp (quadGen c hc r hq))
      (ψ := barRet c hc r hq) (fun _ _ _ w => barRet_quadGen c hc r hq w) z)

omit [CharZero K] in
lemma mapSp_quadGen_barGen {A : Type} [Fintype A] [DecidableEq A] (y : Koszul.Cut K E A) :
    (FreeGrL.mapSp (quadGen c hc r hq)).app A
      ((FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app A y)
        = (FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc (quadAll K E))
          (hE_pres c hc (quadAll K E)))).app A y :=
  (FreeGrL.mapSp_comp (quadGen c hc r hq)
    (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r)) y).trans
    (FreeGrL.mapSp_congr
      (φ := (quadGen c hc r hq).comp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r)))
      (ψ := Koszul.barGen (Ipres K E c hc (quadAll K E)) (hE_pres c hc (quadAll K E)))
      (fun _ _ _ v => quadGen_barGen c hc r hq v) y)

omit [CharZero K] [IsEmpty (T 1)] in
/-- The projection onto the quotient by all the trees with two vertices is a chain map of the
bar constructions. -/
lemma quadGen_d {A : Type} [Fintype A] [DecidableEq A]
    (X : FreeGrL K (BarGen (Ipres K E c hc r)) A) :
    (FreeGrL.mapSp (quadGen c hc r hq)).app A (Bar.d (Ipres K E c hc r) A X)
      = Bar.d (Ipres K E c hc (quadAll K E)) A ((FreeGrL.mapSp (quadGen c hc r hq)).app A X) :=
  Bar.map_d _ _ X

/-- **The retraction onto the generators kills the boundaries of `T^c(sE)`** in `B(P, Ī_P)`:
through the quotient by all the trees with two vertices, where they vanish. -/
theorem barRet_d_cutBar {A : Type} [Fintype A] [DecidableEq A] (y : Koszul.Cut K E A) :
    (FreeGrL.mapSp (barRet c hc r hq)).app A (Bar.d (Ipres K E c hc r) A
      ((FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app A y)) = 0 := by
  have h4 := (quadGen_d c hc r hq
    ((FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app A y)).trans
    ((congrArg (Bar.d (Ipres K E c hc (quadAll K E)) A)
      (mapSp_quadGen_barGen c hc r hq y)).trans (d_cutBar_quadAll c hc y))
  exact (mapSp_barRet_quadGen c hc r hq _).symm.trans
    ((congrArg ((FreeGrL.mapSp (barRet c hc (quadAll K E) isQuadratic_quadAll)).app A)
      h4).trans (map_zero _))

variable (K E) in
/-- **The cycles of `B(P, Ī_P)` on `T^c(sE)`**: the elements `y` of the cut cooperad with
`d (i y) = 0`, `i : T^c(sE) → B(P, Ī_P)`, a subcooperad. -/
noncomputable def cutCyc : GrSubCooperad K (Koszul.Cut K E) :=
  Bar.cycSubRetr (Ipres K E c hc r) (cutBarP c hc r)
    (fun A _ _ => (FreeGrL.mapSp (barRet c hc r hq)).app A)
    (fun _ _ _ y => mapSp_barRet_barGen c hc r hq y)
    (fun _ _ _ y => barRet_d_cutBar c hc r hq y)

/-- **The cycles lie in the Koszul dual cooperad**: on them `κ_T ⋆ κ_T` lands in the ideal of
the relators (`Koszul.star_mem_of_d`). -/
theorem cutCyc_le : cutCyc K E c hc r hq ≤ Koszul.dualSub K E r :=
  Koszul.le_dualSub r fun _ _ _ x hx => Koszul.star_mem_of_d _ (hE_pres c hc r)
    (GrOperadIdeal.atLeastTwo_hI1 (pres_zero c hc r) (Fin 0) (by simp)) x hx

include hq in
/-- **`P^¡` maps onto the cycles of `B(P, Ī_P)` on the diagonal**, the image of `T^c(sE)`, for
quadratic relators on generators of any arity, over a field of characteristic zero: the cycles
of `T^c(sE)` form a subcooperad on which `κ_T ⋆ κ_T` lands in the ideal of the relators. -/
theorem toBar_surj_diag {A : Type} [Fintype A] [DecidableEq A] (y : Koszul.Cut K E A)
    (hdy : Bar.d (Ipres K E c hc r) A
      ((FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app A y) = 0) :
    ∃ x, (Koszul.toBar (Ipres K E c hc r) (hE_pres c hc r)).app A x
      = (FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app A y :=
  ⟨⟨y, cutCyc_le c hc r hq A (LinearMap.mem_ker.2 hdy)⟩, rfl⟩

end ShuffleAnySym

end Operad
