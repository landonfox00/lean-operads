/-
# The resolution of an operad with quadratic-linear relations

For quadratic-linear data (`Koszul.IsQL`) over a field of characteristic zero, with Koszul dual
dg cooperad `(qP^¡, d_φ)` (`Operad.KoszulInhom`):

* **The resolution** (`Koszul.cobarMorQL_bijective`): when the quadratic part `qP` is Koszul
  (`Koszul.IsKoszul`) and `P` has the Poincaré–Birkhoff–Witt property (`Koszul.IsPBW`), **the
  morphism `Ω(qP^¡, d_φ) → P` is a quasi-isomorphism**.
* **The comparison morphism** `(qP^¡, d_φ) → B(P, I)` is then a quasi-isomorphism in the arities
  at least two (`Koszul.toBarDG_bijective`), by the Koszul criterion for quadratic-linear data
  (`Koszul.cobarMorQL_bijective_iff`).

A cycle killed by the morphism is a boundary (`Koszul.exists_cobarDG_d_eq`), by the exactness
criterion by weights of `Operad.KoszulInhomRes` (`exists_eq_D_of_graded`). The morphism maps the
cycles onto `P`: the morphism of graded operads `T(E) → Ω(qP^¡, d_φ)` with `v ↦ s⁻¹ (s v)‾`
(`Koszul.cobarSec`) is a section of it over the projection `T(E) → P`
(`Koszul.cobarMorQL_cobarSec`), with values in the cycles (`Koszul.cobarDG_d_cobarSec`): `d_φ`
takes the suspended generators into the coaugmentation (`Koszul.dQL_sgen_mem_unitSpan`), and
`ι ⋆ ι` vanishes on the trees with one vertex of a cut cooperad
(`Cobar.ιι_eq_zero_of_mem_vx_one`).

The Poincaré–Birkhoff–Witt property is a hypothesis. It is not derived from the Koszulness of
`qP` and the conditions on the relators, as in Loday and Vallette, and the PBW theorem of
`ShuffleAnyInhom.lean`, in the shuffle setting, is not connected to it.
-/
import Operad.KoszulInhomRes

universe u v w

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

/-! ## Homology: a criterion for a quasi-isomorphism onto a module with zero differential -/

/-- **A chain map onto a module with the zero differential is a quasi-isomorphism** when the
cycles it kills are boundaries and it maps the cycles onto the target. -/
lemma Homology.map_bijective_of_zero {R : Type*} [CommRing R] {V W : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] {dV : V →ₗ[R] V}
    {dW : W →ₗ[R] W} (f : V →ₗ[R] W) (hf : ∀ v, f (dV v) = dW (f v)) (hdW : dW = 0)
    (hinj : ∀ y, dV y = 0 → f y = 0 → ∃ Z, dV Z = y)
    (hsurj : ∀ p, ∃ y, dV y = 0 ∧ f y = p) :
    Function.Bijective (Homology.map f hf) := by
  subst hdW
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, fun w => ?_⟩
  · obtain ⟨y, rfl⟩ := Homology.mk_surjective dV z
    have h1 := (Homology.mk_eq_mk_iff (d := (0 : W →ₗ[R] W)) _ 0).1
      (hz.trans (map_zero (Homology.mk (0 : W →ₗ[R] W))).symm)
    have h0 : f y.1 = 0 :=
      h1.elim fun v hv => (sub_zero _).symm.trans (hv.symm.trans (LinearMap.zero_apply v))
    obtain ⟨Z, hZ⟩ := hinj y.1 y.2 h0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨Z, hZ⟩
  · obtain ⟨p, rfl⟩ := Homology.mk_surjective (0 : W →ₗ[R] W) w
    obtain ⟨y, hy, hfy⟩ := hsurj p.1
    exact ⟨Homology.mk dV ⟨y, hy⟩, congrArg (Homology.mk (0 : W →ₗ[R] W)) (Subtype.ext hfy)⟩

/-! ## The universal twisting morphism of a cut cooperad on the trees with one vertex -/

namespace Cobar

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {A : Type} [Fintype A] [DecidableEq A]

local notation "𝒞" => FreeGrL R V

omit [Algebra ℚ R] in
/-- The generators of the corollas have one vertex. -/
lemma corGen_le_vx : corGen R V A ≤ FreeGrL.vx R (CobarGen R 𝒞) 1 A := by
  rintro _ ⟨v, rfl⟩
  exact FreeGrL.ι_mem_vx _

omit [Algebra ℚ R] in
/-- `ι ⋆ ι` takes the trees with one vertex to elements of weight one. -/
lemma ιι_mem_wt_one (hV0 : ∀ v : V (Fin 0), v = 0) {x : 𝒞 A}
    (hx : x ∈ FreeGrL.vx R V 1 A) : ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) x ∈ wt R V 1 A := by
  have hd : (Cobar.d R 𝒞).app A (Cobar.ιL R 𝒞 A x)
      = -ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) x := Cobar.d_ιL R 𝒞 x
  have aux : ∀ y : CobarGr R 𝒞 A, ((1 : ℕ) : R) • y = y := fun y => by
    rw [Nat.cast_one, one_smul]
  have hx' : (FreeGrL.wtD R V).app A x = x :=
    (congrArg (fun D : GrDer (GrOperadHom.id R 𝒞) false => D.app A x) wtD_eq_derSp).trans
      ((FreeGrL.mem_eig.1 hx).trans (by rw [Nat.cast_one, one_smul]))
  have hw : (wtΩ R V).app A (Cobar.ιL R 𝒞 A x) = Cobar.ιL R 𝒞 A x :=
    (wtΩ_ιL x).trans (congrArg (Cobar.ιL R 𝒞 A) hx')
  have e : ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) x
      = -(Cobar.d R 𝒞).app A (Cobar.ιL R 𝒞 A x) := neg_eq_iff_eq_neg.1 hd.symm
  exact mem_wt.2 ((congrArg ((wtΩ R V).app A) e).trans ((map_neg _ _).trans
    ((congrArg Neg.neg ((d_wtΩ hV0 _).symm.trans
      (congrArg ((Cobar.d R 𝒞).app A) hw))).trans (e.symm.trans (aux _).symm))))

omit [Algebra ℚ R] [GrSpecies R V] in
/-- An eigenvector for both one and two vanishes. -/
private lemma eq_zero_of_two_one {M : Type*} [AddCommGroup M] [Module R M] {y : M}
    (h : ((2 : ℕ) : R) • y = ((1 : ℕ) : R) • y) : y = 0 := by
  rw [Nat.cast_ofNat, Nat.cast_one, one_smul, two_smul] at h
  exact add_eq_right.1 h

/-- **`ι ⋆ ι` vanishes on the trees with one vertex** of a cut cooperad: its value has weight one
and two vertices. -/
theorem ιι_eq_zero_of_mem_vx_one (hV0 : ∀ v : V (Fin 0), v = 0) {x : 𝒞 A}
    (hx : x ∈ FreeGrL.vx R V 1 A) : ConvOp.toLin ((Cobar.ιι R 𝒞).1 A) x = 0 :=
  eq_zero_of_two_one
    ((FreeGrL.mem_eig.1 (CobarMap.ιι_mem_vx (R := R) (C := 𝒞) x)).symm.trans
      (FreeGrL.mem_eig.1 (corGen_le_vx (mem_corGen_of_mem_wt (ιι_mem_wt_one hV0 hx)))))

end Cobar

/-! ## The cycles of the generators and the resolution -/

namespace Koszul

open FreeGrL

variable {R : Type u} [Field R] [CharZero R]
  {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  {r : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} {I : GrOperadIdeal R (Pres R E r)}
  (hE : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : E A),
    (GrOperadIdeal.span R r).proj A ((FreeGrL.ι R E).app A v) ∈ I.sub A)
  {q : ∀ n : ℕ, Set (FreeGrL R E (Fin n))} (h : IsQL I q)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

local notation "𝒥" => GrOperadIdeal.span R r

/-- The suspended generators, in the Koszul dual dg cooperad. -/
noncomputable def sgen (A : Type) [Fintype A] [DecidableEq A] : E A →ₗ[R] DualQL hE h A :=
  LinearMap.codRestrict ((dualSub R E q).sub A)
    ((FreeGrL.ι R (GrSpecies.Shift E R)).app A ∘ₗ
      (GrSpecies.Shift.of (R := R) (V := E) A).toLinearMap) (fun v => ι_mem_dual q v)

lemma inclQL_sgen (v : E A) :
    (inclQL hE h).app A (sgen hE h A v)
      = (FreeGrL.ι R (GrSpecies.Shift E R)).app A (GrSpecies.Shift.of A v) := rfl

/-- The suspended generators have one vertex. -/
lemma vcountL_sgen (v : E A) : vcountL hE h A (sgen hE h A v) = sgen hE h A v :=
  inclQL_injective hE h (derSp_ι (GrSpEnd.id R (GrSpecies.Shift E R)) _)

/-- An element of `qP^¡` in the coaugmentation of `T^c(sE)` is in the coaugmentation of
`qP^¡`. -/
lemma mem_unitSpan_of_inclQL {x : DualQL hE h A}
    (hx : (inclQL hE h).app A x ∈ GrCooperad.unitSpan R (Cut R E) A) :
    x ∈ GrCooperad.unitSpan R (DualQL hE h) A := by
  have h2 : Submodule.map ((inclQL hE h).app A) (GrCooperad.unitSpan R (DualQL hE h) A)
      = GrCooperad.unitSpan R (Cut R E) A := by
    rw [GrCooperad.unitSpan, GrCooperad.unitSpanOf, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← h2] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hyx : y = x := inclQL_injective hE h hxy
  exact hyx ▸ hy

/-- **`d_φ` takes the suspended generators into the coaugmentation.** -/
lemma dQL_sgen_mem_unitSpan (v : E A) :
    dQL hE h A (sgen hE h A v) ∈ GrCooperad.unitSpan R (DualQL hE h) A := by
  apply mem_unitSpan_of_inclQL hE h
  have h0 : vcountL hE h A (dQL hE h A (sgen hE h A v)) = 0 :=
    (vcountL_dQL hE h _).trans ((congrArg (fun y : DualQL hE h A =>
      dQL hE h A y - dQL hE h A (sgen hE h A v)) (vcountL_sgen hE h v)).trans (sub_self _))
  have aux0 : ∀ y : Cut R E A, ((0 : ℕ) : R) • y = 0 := fun y => by
    rw [Nat.cast_zero, zero_smul]
  have h1 : (inclQL hE h).app A (dQL hE h A (sgen hE h A v))
      ∈ vx R (GrSpecies.Shift E R) 0 A :=
    mem_eig.2 ((congrArg ((inclQL hE h).app A) h0).trans
      ((map_zero ((inclQL hE h).app A)).trans (aux0 _).symm))
  rw [← wtEqL_eq_vx] at h1
  exact wtEqL_zero_le_unitSpan h1

/-- The generators of the section `T(E) → Ω(qP^¡, d_φ)`: `v ↦ s⁻¹ (s v)‾`. -/
noncomputable def secGen : GrSpeciesHom R E (CobarGr R (DualQL hE h)) where
  app A _ _ := Cobar.ιL R (DualQL hE h) A ∘ₗ sgen hE h A
  app_map {A B} _ _ _ _ e v := by
    have h1 : sgen hE h B (SymSpecies.map (R := R) e v)
        = SymSpecies.map (R := R) e (sgen hE h A v) :=
      inclQL_injective hE h (by
        rw [inclQL_sgen, (inclQL hE h).app_map, inclQL_sgen,
          ← (FreeGrL.ι R (GrSpecies.Shift E R)).app_map]
        rfl)
    show Cobar.ιL R (DualQL hE h) B (sgen hE h B (SymSpecies.map (R := R) e v)) = _
    rw [h1, Cobar.ιL_map]
    rfl
  app_par {A} _ _ b v := by
    have h1 : sgen hE h A (GrSpecies.par (R := R) b v)
        = GrSpecies.par (R := R) (!b) (sgen hE h A v) :=
      inclQL_injective hE h (by
        rw [inclQL_sgen, (inclQL hE h).app_par, inclQL_sgen,
          ← (FreeGrL.ι R (GrSpecies.Shift E R)).app_par, GrSpecies.Shift.par_of, Bool.not_not])
    show Cobar.ιL R (DualQL hE h) A (sgen hE h A (GrSpecies.par (R := R) b v)) = _
    rw [h1, Cobar.ιL_par, Bool.not_not]
    rfl

/-- **The section `T(E) → Ω(qP^¡, d_φ)`**: the morphism of graded operads with
`v ↦ s⁻¹ (s v)‾` on the generators. -/
noncomputable def cobarSec : GrOperadHom R (FreeGrL R E) (CobarGr R (DualQL hE h)) :=
  FreeGrL.homEquiv.symm (secGen hE h)

lemma cobarSec_ι (v : E A) :
    (cobarSec hE h).app A ((FreeGrL.ι R E).app A v)
      = Cobar.ιL R (DualQL hE h) A (sgen hE h A v) :=
  FreeGrL.homEquiv_symm_ι _ v

/-- **The section is a section**: `Ω(qP^¡, d_φ) → P` after it is the projection `T(E) → P`. -/
theorem cobarMorQL_cobarSec (t : FreeGrL R E A) :
    (cobarMorQL hE h).app A ((cobarSec hE h).app A t) = (𝒥).proj A t := by
  have hc : (cobarMorQL hE h).comp (cobarSec hE h) = GrOperadHom.toZeroDG (𝒥).projHom :=
    FreeGrL.hom_ext fun A _ _ v =>
      (congrArg ((cobarMorQL hE h).app A) (cobarSec_ι hE h v)).trans
        ((cobarMorQL_ιL hE h (sgen hE h A v)).trans (congrArg ((𝒥).proj A) (kapL_ι v)))
  exact congrArg (fun φ : GrOperadHom R (FreeGrL R E) (ZeroDG R (Pres R E r)) => φ.app A t) hc

/-- **The section has values in the cycles.** -/
theorem cobarDG_d_cobarSec (t : FreeGrL R E A) :
    (CobarDG.d R (DualQL hE h)).app A ((cobarSec hE h).app A t) = 0 := by
  have hV0 : ∀ v : GrSpecies.Shift E R (Fin 0), v = 0 := fun v =>
    h.gen_eq_zero hE (Fin 0) (by simp) v
  have hD : (CobarDG.d R (DualQL hE h)).compHom (cobarSec hE h)
      = GrDer.zero (cobarSec hE h) true :=
    FreeGrL.der_eq_zero fun A _ _ v => by
      have hιι : ConvOp.toLin ((Cobar.ιι R (DualQL hE h)).1 A) (sgen hE h A v) = 0 := by
        apply cobarIncl_injective hE h
        have h1 := CobarMap.ιι_map (inclQL hE h) (inclQL_one hE h) (sgen hE h A v)
        exact h1.symm.trans ((Cobar.ιι_eq_zero_of_mem_vx_one hV0 (FreeGrL.ι_mem_vx _)).trans
          (map_zero ((cobarIncl hE h).app A)).symm)
      have h2 : (CobarDG.d R (DualQL hE h)).app A (Cobar.ιL R (DualQL hE h) A (sgen hE h A v))
          = 0 := by
        rw [CobarDG.d_ιL, hιι, neg_zero, zero_sub, neg_eq_zero]
        exact Cobar.ιL_unitSpan R (DualQL hE h) (dQL_sgen_mem_unitSpan hE h v)
      exact (congrArg ((CobarDG.d R (DualQL hE h)).app A) (cobarSec_ι hE h v)).trans h2
  exact congrArg (fun D : GrDer (cobarSec hE h) true => D.app A t) hD

/-- **A cycle of `Ω(qP^¡, d_φ)` killed by `Ω(qP^¡, d_φ) → P` is a boundary**, when `qP` is
Koszul and `P` has the Poincaré–Birkhoff–Witt property. -/
theorem exists_cobarDG_d_eq (hK : IsKoszul R E q)
    (hPBW : IsPBW r q)
    {y : CobarGr R (DualQL hE h) A} (hy : (CobarDG.d R (DualQL hE h)).app A y = 0)
    (hγ : (cobarMorQL hE h).app A y = 0) :
    ∃ Z, (CobarDG.d R (DualQL hE h)).app A Z = y := by
  have hD : ∀ z : CobarGr R (DualQL hE h) A,
      ((Cobar.d R (DualQL hE h)).app A - (deltaQL hE h).app A) z
        = (CobarDG.d R (DualQL hE h)).app A z := fun z => (cobarDG_d_app hE h z).symm
  obtain ⟨u, hu⟩ := exists_eq_D_of_graded ((wtQL hE h).app A)
    ((Cobar.d R (DualQL hE h)).app A) ((deltaQL hE h).app A) ((cobarMorQL hE h).app A)
    ((cobarMorQ hE h).app A) (iSup_wtQL hE h A) (d_wtQL hE h) (wtQL_deltaQL hE h)
    (fun z => (hD _).trans ((congrArg ((CobarDG.d R (DualQL hE h)).app A) (hD z)).trans
      (CobarDG.d_d R (DualQL hE h) z)))
    (fun z => (congrArg ((cobarMorQL hE h).app A) (hD z)).trans (cobarMorQL_d hE h z))
    (fun n x hx y hy hxy => cobarMorQ_eq_zero_of_pbw hE h hPBW hx hy hxy)
    (fun n x hx hdx hσx => exists_d_eq_of_isKoszul hE h hK hx hdx hσx) y
    ((hD y).trans hy) hγ
  exact ⟨u, (hD u).symm.trans hu⟩

/-- **The resolution of an operad with quadratic-linear relations.** Over a field of
characteristic zero, for quadratic-linear data whose quadratic part `qP` is Koszul and with the
Poincaré–Birkhoff–Witt property, **the morphism `Ω(qP^¡, d_φ) → P` is a quasi-isomorphism**. -/
theorem cobarMorQL_bijective (hK : IsKoszul R E q)
    (hPBW : IsPBW r q)
    (A : Type) [Fintype A] [DecidableEq A] :
    Function.Bijective (Homology.map (dV := (CobarDG.d R (DualQL hE h)).app A)
      (dW := DGOperad.d (R := R) (P := ZeroDG R (Pres R E r)) (A := A))
      ((cobarMorQL hE h).app A) fun y => cobarMorQL_d hE h y) :=
  Homology.map_bijective_of_zero _ _ rfl
    (fun _ hy hγ => exists_cobarDG_d_eq hE h hK hPBW hy hγ)
    (fun p => by
      obtain ⟨t, ht⟩ := (𝒥).proj_surjective A p
      exact ⟨(cobarSec hE h).app A t, cobarDG_d_cobarSec hE h t,
        (cobarMorQL_cobarSec hE h t).trans ht⟩)

/-- **The comparison morphism `(qP^¡, d_φ) → B(P, I)` is a quasi-isomorphism in the arities at
least two**, when `qP` is Koszul and `P` has the Poincaré–Birkhoff–Witt property, by the Koszul
criterion for quadratic-linear data. -/
theorem toBarDG_bijective (hK : IsKoszul R E q)
    (hPBW : IsPBW r q)
    (hcompl : ∀ (A : Type) [Fintype A] [DecidableEq A],
      IsCompl (Bar.unitsP (Pres R E r) A) (I.sub A))
    (hone : ∀ a : R, a • GrOperad.one (R := R) (P := Pres R E r) = 0 → a = 0)
    (B : Type) [Fintype B] [DecidableEq B] (hB : 2 ≤ Fintype.card B) :
    Function.Bijective (Homology.map (dV := DGCooperad.d (R := R) (C := DualQL hE h) (A := B))
      (dW := DGCooperad.d (R := R) (C := BarCoop I) (A := B)) ((toBarDG hE h).app B)
        fun x => (toBarDG hE h).app_d x) :=
  (cobarMorQL_bijective_iff hE h hcompl hone).1
    (fun A _ _ => cobarMorQL_bijective hE h hK hPBW A) B hB

end Koszul

end Operad
