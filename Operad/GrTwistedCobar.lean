/-
# The twisted composite product `C ∘_ι ΩC` is acyclic

Let `C` be a reduced coaugmented graded cooperad (spanned by the coaugmentation in the arities at
most one) and `ΩC` its cobar construction, with the universal twisting morphism `ι : C → ΩC`. The
twisted composite product `C ∘_ι ΩC` has the contracting homotopy

  `h = (s ∘ 1) ∘ ρ ∘ (ε ∘ 1)`

(`GrComposite.cobarH`): the counit of the outer cooperation, leaving its single inner operation
`x ∈ ΩC` (`GrComposite.cobarE`), the root decomposition of `x` (`FreeGrL.root`), and the
suspension of the root vertex back into `C` (`GrComposite.cobarSusp`).
-/
import Operad.GrTwistedDG
import Operad.ConvUnit
import Operad.Twisting
import Operad.FreeGrGraft

universe u v

namespace Operad

open Function Sym GerBV ConvOp

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]

namespace GrCooperad

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The span of the coaugmentation vanishes outside the arities of one element. -/
lemma unitSpan_eq_bot (h : IsEmpty (Unit ≃ A)) : unitSpan R C A = ⊥ := by
  rw [unitSpan, unitSpanOf, Submodule.span_eq_bot]
  rintro _ ⟨e, rfl⟩
  exact h.elim e

/-- **The section of the reduced part**: the identity outside the arities of one element. -/
noncomputable def Red.sec (A : Type) [Fintype A] [DecidableEq A] : Red R C A →ₗ[R] C A :=
  @dite _ (IsEmpty (Unit ≃ A)) (Classical.dec _)
    (fun h => (Submodule.quotEquivOfEqBot (unitSpan R C A) (unitSpan_eq_bot h)).toLinearMap)
    (fun _ => 0)

lemma Red.sec_proj (h : IsEmpty (Unit ≃ A)) (x : C A) : Red.sec A (Red.proj R C A x) = x := by
  rw [Red.sec, dif_pos h]
  rfl

lemma Red.sec_of_nonempty (h : Nonempty (Unit ≃ A)) (v : Red R C A) : Red.sec A v = 0 := by
  rw [Red.sec, dif_neg (not_isEmpty_iff.2 h)]
  rfl

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
lemma isEmpty_congr (σ : A ≃ B) : IsEmpty (Unit ≃ A) ↔ IsEmpty (Unit ≃ B) :=
  ⟨fun h => ⟨fun e => h.elim (e.trans σ.symm)⟩, fun h => ⟨fun e => h.elim (e.trans σ)⟩⟩

lemma Red.sec_map (σ : A ≃ B) (v : Red R C A) :
    Red.sec B (SymSpecies.map (R := R) σ v) = SymSpecies.map (R := R) σ (Red.sec A v) := by
  obtain ⟨x, rfl⟩ := Red.proj_surjective (R := R) (C := C) A v
  by_cases h : IsEmpty (Unit ≃ A)
  · rw [Red.map_proj, Red.sec_proj ((isEmpty_congr σ).1 h), Red.sec_proj h]
  · rw [not_isEmpty_iff] at h
    rw [Red.sec_of_nonempty h, Red.sec_of_nonempty (h.map fun e => e.trans σ), map_zero]

lemma Red.sec_par (b : Bool) (v : Red R C A) :
    Red.sec A (GrSpecies.par (R := R) b v) = GrSpecies.par (R := R) b (Red.sec A v) := by
  obtain ⟨x, rfl⟩ := Red.proj_surjective (R := R) (C := C) A v
  by_cases h : IsEmpty (Unit ≃ A)
  · rw [Red.par_proj, Red.sec_proj h, Red.sec_proj h]
  · rw [not_isEmpty_iff] at h
    rw [Red.sec_of_nonempty h, Red.sec_of_nonempty h, map_zero]

/-- **A cooperation in an arity of one element** is a multiple of the relabelled coaugmentation,
for a reduced cooperad. -/
lemma eq_counit_smul (hred : ∀ x : C A, x ∈ unitSpan R C A) (e : Unit ≃ A) (x : C A) :
    x = counit (R := R) (SymSpecies.map (R := R) e.symm x)
      • SymSpecies.map (R := R) e (Coaug.one (R := R) (C := C)) := by
  have hx := hred x
  rw [unitSpan, unitSpanOf, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  haveI : Subsingleton (Unit ≃ A) := ⟨fun e₁ e₂ => Equiv.ext fun u => by
    have : ∀ a a' : A, a = a' := fun a a' => by
      rw [← e.apply_symm_apply a, ← e.apply_symm_apply a']
    exact this _ _⟩
  rw [Fintype.sum_subsingleton _ e] at hc
  subst hc
  rw [map_smul, ← SymSpecies.map_trans, Equiv.self_trans_symm, SymSpecies.map_refl, map_smul,
    Coaug.counit_one, smul_eq_mul, mul_one]

end GrCooperad

namespace GrComposite

open GrCooperad

/-! ## The maps of the homotopy -/

section Maps

variable (R C) in
/-- **The suspension** of the generators of the cobar construction back into `C`: the section of
the reduced part. -/
noncomputable def cobarSusp : SymSpeciesHom R (CobarGen R C) C where
  app A _ _ := Red.sec A ∘ₗ (GrSpecies.Shift.of (R := R) (V := Red R C) A).symm.toLinearMap
  app_map σ v := Red.sec_map σ v

lemma cobarSusp_of {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    (cobarSusp R C).app A (GrSpecies.Shift.of (R := R) (V := Red R C) A (Red.proj R C A x))
      = Red.sec A (Red.proj R C A x) := rfl

variable (R C) in
/-- **The counit**, as a morphism of linear species `C → ΩC` into the units. -/
noncomputable def cobarEps : SymSpeciesHom R C (CobarGr R C) where
  app A _ _ := ∑ e : Unit ≃ A, (LinearMap.smulRight (counit (R := R) (C := C)) (GrOperad.map (R := R)
    (P := CobarGr R C) e (GrOperad.one (R := R)))).comp (SymSpecies.map (R := R) e.symm)
  app_map {A B} _ _ _ _ σ x := by
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
      LinearMap.smulRight_apply, map_sum, map_smul]
    refine Fintype.sum_equiv (Equiv.mk (fun e => e.trans σ.symm) (fun e => e.trans σ)
      (fun e => by ext; simp) (fun e => by ext; simp)) _ _ fun e => ?_
    show _ = _ • GrOperad.map (R := R) σ (GrOperad.map (R := R) (e.trans σ.symm) _)
    rw [← SymSpecies.map_trans, ← GrOperad.map_trans]
    congr 2

lemma cobarEps_apply {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    (cobarEps R C).app A x = ∑ e : Unit ≃ A, counit (R := R) (SymSpecies.map (R := R) e.symm x)
      • GrOperad.map (R := R) (P := CobarGr R C) e (GrOperad.one (R := R)) := by
  simp [cobarEps]

end Maps

/-! ## Relabelling the outer operations along an odd map -/

section OddOuter

variable {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [GrSpecies R M]
  {M' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M' A)] [GrSpecies R M']
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrSpecies R N]
  {N' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N' A)] [GrSpecies R N']
  {S : Type} [Fintype S] [DecidableEq S]

/-- **An odd map of the outer operations shifts the parities of the composite.** -/
lemma map₂_par_odd (φ : SymSpeciesHom R M M')
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A] (b : Bool) (x : M A),
      φ.app A (GrSpecies.par (R := R) b x) = GrSpecies.par (R := R) (!b) (φ.app A x))
    (ψ : GrSpeciesHom R N N') (b : Bool) (w : GrComposite R M N S) :
    (map₂ φ ψ).app S (par R M N b w) = par R M' N' (!b) ((map₂ φ ψ).app S w) := by
  induction w using induction_on with
  | h0 => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul r x hx => simp only [map_smul, hx]
  | hmk g =>
    have hg : ∀ p (c : g.A → Bool), genMap₂ φ ψ (parGen (R := R) g p c)
        = parGen (R := R) (genMap₂ φ ψ g) (!p) c := fun p c => by
      simp only [genMap₂, parGen, hφ, ψ.app_par]
    rw [mk_eq_sum (R := R) g]
    simp only [map_sum, par_parGen, apply_ite ((map₂ φ ψ).app S), map_zero, map₂_mk, hg]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
    by_cases h : xor p (GrEnd.tot c) = b
    · rw [if_pos h, if_pos (by rw [← h]; cases p <;> simp)]
    · rw [if_neg h, if_neg (fun h' => h (by cases p <;> cases b <;> simp_all))]

end OddOuter

/-! ## Products of the corollas, totally composed -/

section TotalStar

variable {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P] (ε : GrAug R P)

omit [GrCooperad.Coaug R C] in
/-- A morphism of linear species, as an invariant family of the convolution operad. -/
noncomputable def famOf (F : SymSpeciesHom R C P) : GrOperad.Inv R (ConvOp R C P) :=
  ⟨fun A _ _ => ConvOp.of (F.app A), fun A B _ _ _ _ e => by
    show ConvOp.mapC e (ConvOp.of _) = ConvOp.of _
    ext x
    rw [ConvOp.mapC_apply, ConvOp.toLin_of, ConvOp.toLin_of]
    show SymSpecies.map (R := R) e (F.app A (SymSpecies.map (R := R) e.symm x)) = _
    rw [← F.app_map, SymSpecies.map_map_symm]⟩

omit [GrCooperad.Coaug R C] in
lemma toLin_famOf (F : SymSpeciesHom R C P) {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    ConvOp.toLin ((famOf F).1 A) x = F.app A x := rfl

omit [GrCooperad.Coaug R C] in
/-- **The total composite of a product of the corollas** with a homogeneous family. -/
lemma total_snd_star (F : SymSpeciesHom R C P) {p : Bool} {β : GrOperad.Inv R (ConvOp R C P)}
    (hβ : GrOperad.Inv.IsPar p β) {X : Type} [Fintype X] [DecidableEq X] (c : C X) :
    total R F (SqExt.snd (ConvOp.toLin ((GrOperad.Inv.star R _ (corFam (C := C) ε)
      (liftFam ε β)).1 X) c))
      = ConvOp.toLin ((GrOperad.Inv.star R _ (famOf F) β).1 X) c := by
  rw [toLin_star, toLin_star, map_sum, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [toLin_term, toLin_term, SqExt.map_def, SqExt.snd_mapE, total_map]
  congr 1
  generalize GrCooperad.decomp (R := R) (C := C) none
    (SymSpecies.map (R := R) (splitEquiv S).symm c) = t
  have hβ' := isParC_of_isPar (isPar_liftFam ε hβ) (SIn S)
  rw [ConvOp.kap_hom _ hβ', ConvOp.kap_hom _ (isParC_of_isPar hβ (SIn S))]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, ConvOp.mu_tmul, LinearMap.comp_apply, SqExt.comp_def,
      SqExt.snd_compE]
    rw [show ConvOp.toLin ((liftFam ε β).1 (SIn S)) y
        = (inclHom C ε).app _ (ConvOp.toLin (β.1 (SIn S)) y) from rfl,
      fst_inclHom, snd_inclHom, map_zero, add_zero, total_act]
    congr 2
    show total R F (corolla R P (SOut S) _) = _
    rw [corolla_apply, total_corGen, GrOperad.map_refl]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

omit [GrCooperad.Coaug R C] in
/-- A morphism into `C ∘ P`, into the second factor of the square-zero extension. -/
noncomputable def sndHom (Ψ : SymSpeciesHom R C (GrComposite R C P)) :
    SymSpeciesHom R C (SqExt R C P ε) where
  app A _ _ :=
    { toFun := fun x => SqExt.mk 0 (Ψ.app A x)
      map_add' := fun x y => SqExt.ext (by simp) (by simp)
      map_smul' := fun r x => SqExt.ext (by simp) (by simp) }
  app_map {A B} _ _ _ _ σ x := by
    refine SqExt.ext ?_ ?_
    · show (0 : P B) = GrOperad.map (R := R) σ 0
      exact (map_zero _).symm
    · show Ψ.app B (SymSpecies.map (R := R) σ x) = map σ (Ψ.app A x)
      exact Ψ.app_map σ x

omit [GrCooperad.Coaug R C] in
lemma star_add_left_apply {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    (G G' H : GrOperad.Inv R (ConvOp R C Q)) {X : Type} [Fintype X] [DecidableEq X] (c : C X) :
    ConvOp.toLin ((GrOperad.Inv.star R _ (G + G') H).1 X) c
      = ConvOp.toLin ((GrOperad.Inv.star R _ G H).1 X) c
        + ConvOp.toLin ((GrOperad.Inv.star R _ G' H).1 X) c := by
  rw [map_add, LinearMap.add_apply]
  rfl

omit [GrCooperad.Coaug R C] in
/-- **A product of a family of elements of `C ∘ P` given by a derivation-like map.** -/
lemma snd_star_sndHom (Ψ : SymSpeciesHom R C (GrComposite R C P))
    (Φ : ∀ (A : Type) [Fintype A] [DecidableEq A], P A →ₗ[R] GrComposite R C P A)
    (hΦmap : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (σ : A ≃ B)
      (x : P A), Φ B (GrOperad.map (R := R) σ x) = map σ (Φ A x))
    (hΦcomp : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (x : P A) (y : P B),
      Φ _ (GrOperad.comp (R := R) i x y) = act R C i y (Φ A x) + lact R C ε i x (Φ B y))
    (G : GrOperad.Inv R (ConvOp R C P))
    (hGu : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      ε.u A (ConvOp.toLin (G.1 A) x) = 0)
    (hΨ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      Ψ.app A x = Φ A (ConvOp.toLin (G.1 A) x))
    {p : Bool} {β : GrOperad.Inv R (ConvOp R C P)} (hβ : GrOperad.Inv.IsPar p β)
    {X : Type} [Fintype X] [DecidableEq X] (c : C X) :
    SqExt.snd (ConvOp.toLin ((GrOperad.Inv.star R _ (famOf (sndHom ε Ψ)) (liftFam ε β)).1 X) c)
      = Φ X (ConvOp.toLin ((GrOperad.Inv.star R _ G β).1 X) c) := by
  rw [toLin_star, toLin_star, map_sum, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [toLin_term, toLin_term, SqExt.map_def, SqExt.snd_mapE, hΦmap]
  congr 1
  generalize GrCooperad.decomp (R := R) (C := C) none
    (SymSpecies.map (R := R) (splitEquiv S).symm c) = t
  have hβ' := isParC_of_isPar (isPar_liftFam ε hβ) (SIn S)
  rw [ConvOp.kap_hom _ hβ', ConvOp.kap_hom _ (isParC_of_isPar hβ (SIn S))]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, ConvOp.mu_tmul, LinearMap.comp_apply, SqExt.comp_def,
      SqExt.snd_compE]
    rw [show ConvOp.toLin ((liftFam ε β).1 (SIn S)) y
        = (inclHom C ε).app _ (ConvOp.toLin (β.1 (SIn S)) y) from rfl,
      fst_inclHom, snd_inclHom, map_zero, add_zero, hΦcomp, lact_of_u ε _ (hGu _ _),
      LinearMap.zero_apply, add_zero]
    congr 1
    exact hΨ _ _
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **A product with a family supported in arity one**, in the second factor of the square-zero
extension. -/
lemma snd_star_unit (G : GrOperad.Inv R (ConvOp R C (SqExt R C P ε)))
    (hG : ∀ (A : Type) [Fintype A] [DecidableEq A] (e : Unit ≃ A) (x : C A),
      ConvOp.toLin (G.1 A) x = GrCooperad.counit (R := R) (SymSpecies.map (R := R) e.symm x)
        • SqExt.mk 0 (corolla R P A (SymSpecies.map (R := R) e (Coaug.one (R := R) (C := C)))))
    (hG0 : ∀ (A : Type) [Fintype A] [DecidableEq A], IsEmpty (Unit ≃ A) → G.1 A = 0)
    {p : Bool} {β : GrOperad.Inv R (ConvOp R C P)} (hβ : GrOperad.Inv.IsPar p β)
    {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (c : C X) :
    SqExt.snd (ConvOp.toLin ((GrOperad.Inv.star R _ G (liftFam ε β)).1 X) c)
      = map (leftUnitEquiv X) (act R C () (ConvOp.toLin (β.1 X) c)
          (corolla R P Unit (Coaug.one (R := R) (C := C)))) := by
  rw [GrOperad.Inv.star_counit_left G (liftFam ε β)
    (SqExt.mk 0 (corolla R P Unit (Coaug.one (R := R) (C := C)))) (fun A _ _ e x => ?_) hG0
    (isPar_liftFam ε hβ) c]
  · rw [SqExt.map_def, SqExt.snd_mapE, SqExt.comp_def, SqExt.snd_compE]
    show map _ (act R C () (ConvOp.toLin (β.1 X) c) (corolla R P Unit _)
      + lact R C ε () 0 0) = _
    rw [map_zero, add_zero]
  · rw [hG A e x]
    congr 1
    refine SqExt.ext ?_ ?_
    · show (0 : P A) = GrOperad.map (R := R) e 0
      exact (map_zero _).symm
    · show _ = map e (corolla R P Unit _)
      rw [map_corolla]
      rfl

/-- **The twisted differential of a corolla**, split into the part of a derivation-like map and
the part of the coaugmentation. -/
lemma snd_star_corFam (Ψ : SymSpeciesHom R C (GrComposite R C P))
    (Φ : ∀ (A : Type) [Fintype A] [DecidableEq A], P A →ₗ[R] GrComposite R C P A)
    (hΦmap : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (σ : A ≃ B)
      (x : P A), Φ B (GrOperad.map (R := R) σ x) = map σ (Φ A x))
    (hΦcomp : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
      (x : P A) (y : P B),
      Φ _ (GrOperad.comp (R := R) i x y) = act R C i y (Φ A x) + lact R C ε i x (Φ B y))
    (G : GrOperad.Inv R (ConvOp R C P))
    (hGu : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      ε.u A (ConvOp.toLin (G.1 A) x) = 0)
    (hΨ : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      Ψ.app A x = Φ A (ConvOp.toLin (G.1 A) x))
    (hΨ1 : ∀ (A : Type) [Fintype A] [DecidableEq A] (e : Unit ≃ A) (x : C A),
      corolla R P A x - Ψ.app A x = GrCooperad.counit (R := R) (SymSpecies.map (R := R) e.symm x)
        • corolla R P A (SymSpecies.map (R := R) e (Coaug.one (R := R) (C := C))))
    (hΨ0 : ∀ (A : Type) [Fintype A] [DecidableEq A], IsEmpty (Unit ≃ A) →
      ∀ x : C A, Ψ.app A x = corolla R P A x)
    {p : Bool} {β : GrOperad.Inv R (ConvOp R C P)} (hβ : GrOperad.Inv.IsPar p β)
    {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (c : C X) :
    SqExt.snd (ConvOp.toLin ((GrOperad.Inv.star R _ (corFam (C := C) ε) (liftFam ε β)).1 X) c)
      = Φ X (ConvOp.toLin ((GrOperad.Inv.star R _ G β).1 X) c)
        + map (leftUnitEquiv X) (act R C () (ConvOp.toLin (β.1 X) c)
          (corolla R P Unit (Coaug.one (R := R) (C := C)))) := by
  have hsplit : corFam (C := C) ε
      = famOf (sndHom ε Ψ) + (corFam (C := C) ε - famOf (sndHom ε Ψ)) := by abel
  rw [hsplit, star_add_left_apply, map_add,
    snd_star_sndHom ε Ψ Φ hΦmap hΦcomp G hGu hΨ hβ c]
  congr 1
  refine snd_star_unit ε _ (fun A _ _ e x => ?_) (fun A _ _ h => ?_) hβ c
  · refine SqExt.ext ?_ ?_
    · show SqExt.fst (corLin ε A x - (sndHom ε Ψ).app A x) = _
      rw [map_sub, map_smul]
      show (0 : P A) - 0 = _ • (0 : P A)
      rw [sub_zero, smul_zero]
    · show SqExt.snd (corLin ε A x - (sndHom ε Ψ).app A x) = _
      rw [map_sub, map_smul]
      exact hΨ1 A e x
  · refine ConvOp.ext fun x => ?_
    show corLin ε A x - (sndHom ε Ψ).app A x = 0
    refine sub_eq_zero.2 (SqExt.ext rfl ?_)
    exact (hΨ0 A h x).symm

end TotalStar

/-! ## Induction on free graded operads -/

lemma _root_.Operad.FreeGrL.mem_of_ι {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
    (S : GrSuboperad R (FreeGrL R W))
    (h : ∀ (k : ℕ) (v : W (Fin k)) (b : Bool), GrSpecies.par (R := R) b v = v →
      (FreeGrL.ι R W).app (Fin k) v ∈ S.sub (Fin k)) {A : Type} [Fintype A] [DecidableEq A]
    (x : FreeGrL R W A) : x ∈ S.sub A :=
  FreeGr.mem_of_presGen S (fun k e => by
    obtain ⟨⟨v, b⟩, hv⟩ := e
    rw [← FreeGrL.ι_app_hom hv]
    exact h k v b hv) x

/-! ## The homotopy -/

section Homotopy

local notation "𝒲" => CobarGen R C
local notation "Ω" => CobarGr R C
local notation "εΩ" => FreeGrL.aug R (CobarGen R C)

variable (R C) in
/-- **The counit of the outer cooperation**, leaving the inner operation. -/
noncomputable abbrev cobarE (S : Type) [Fintype S] [DecidableEq S] :
    GrComposite R C Ω S →ₗ[R] Ω S :=
  total R (cobarEps R C)

variable (R C) in
/-- The suspension of the outer operations. -/
noncomputable abbrev suspMap (S : Type) [Fintype S] [DecidableEq S] :
    GrComposite R 𝒲 Ω S →ₗ[R] GrComposite R C Ω S :=
  (map₂ (cobarSusp R C) (GrOperadHom.id R Ω).toGrSpeciesHom).app S

variable (R C) in
/-- **The root vertex, suspended back into `C`.** -/
noncomputable abbrev cobarHs (S : Type) [Fintype S] [DecidableEq S] :
    Ω S →ₗ[R] GrComposite R C Ω S :=
  suspMap R C S ∘ₗ FreeGrL.root R 𝒲 S

variable (R C) in
/-- **The contracting homotopy** `(s ∘ 1) ∘ ρ ∘ (ε ∘ 1)` of `C ∘_ι ΩC`. -/
noncomputable abbrev cobarH (S : Type) [Fintype S] [DecidableEq S] :
    GrComposite R C Ω S →ₗ[R] GrComposite R C Ω S :=
  cobarHs R C S ∘ₗ cobarE R C S

variable (R C) in
/-- The element `1 ⊗ z`: the coaugmentation with the single inner operation `z`. -/
noncomputable def unitCor (B : Type) [Fintype B] [DecidableEq B] :
    Ω B →ₗ[R] GrComposite R C Ω B :=
  map (leftUnitEquiv B) ∘ₗ (actL R C ()).flip (corolla R Ω Unit (Coaug.one (R := R) (C := C)))

lemma unitCor_apply {B : Type} [Fintype B] [DecidableEq B] (z : Ω B) :
    unitCor R C B z = map (leftUnitEquiv B)
      (act R C () z (corolla R Ω Unit (Coaug.one (R := R) (C := C)))) := rfl

variable {S : Type} [Fintype S] [DecidableEq S]

lemma cobarE_act {Y : Type} [Fintype Y] [DecidableEq Y] (i : S) (z : Ω Y)
    (w : GrComposite R C Ω S) :
    cobarE R C _ (act R C i z w) = GrOperad.comp (R := R) i (cobarE R C S w) z :=
  total_act R C (cobarEps R C) i z w

lemma cobarE_map {S' : Type} [Fintype S'] [DecidableEq S'] (σ : S ≃ S')
    (w : GrComposite R C Ω S) :
    cobarE R C S' (map σ w) = GrOperad.map (R := R) σ (cobarE R C S w) :=
  total_map (cobarEps R C) σ w

lemma cobarE_corolla {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    cobarE R C A (corolla R Ω A c) = (cobarEps R C).app A c := by
  rw [corolla_apply, total_corGen, GrOperad.map_refl]

lemma suspMap_act {Y : Type} [Fintype Y] [DecidableEq Y] (i : S) (z : Ω Y)
    (w : GrComposite R 𝒲 Ω S) :
    suspMap R C _ (act R 𝒲 i z w) = act R C i z (suspMap R C S w) :=
  map₂_act _ _ i z w

lemma suspMap_map {S' : Type} [Fintype S'] [DecidableEq S'] (σ : S ≃ S')
    (w : GrComposite R 𝒲 Ω S) :
    suspMap R C S' (map σ w) = map σ (suspMap R C S w) :=
  (map₂ (cobarSusp R C) (GrOperadHom.id R Ω).toGrSpeciesHom).app_map σ w

lemma suspMap_lact {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    (i : A) (x : Ω A) (ν : GrComposite R 𝒲 Ω Y) :
    suspMap R C _ (lact R 𝒲 εΩ i x ν) = lact R C εΩ i x (suspMap R C Y ν) := by
  simp only [lact, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, map_sum,
    map_smul, suspMap_map]

/-- **The root decomposition, suspended, of a composite.** -/
lemma cobarHs_comp {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] (i : A)
    (x : Ω A) (z : Ω Y) :
    cobarHs R C _ (GrOperad.comp (R := R) i x z)
      = act R C i z (cobarHs R C A x) + lact R C εΩ i x (cobarHs R C Y z) := by
  simp only [LinearMap.comp_apply]
  rw [FreeGrL.root_comp, map_add, suspMap_act, suspMap_lact]

lemma cobarHs_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : A ≃ B) (x : Ω A) :
    cobarHs R C B (GrOperad.map (R := R) σ x) = map σ (cobarHs R C A x) := by
  simp only [LinearMap.comp_apply]
  rw [FreeGrL.root_map, suspMap_map]

lemma cobarHs_one : cobarHs R C Unit (GrOperad.one (R := R)) = 0 := by
  simp only [LinearMap.comp_apply, FreeGrL.root_one, map_zero]

lemma cobarHs_ιL {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    cobarHs R C A (Cobar.ιL R C A c) = corolla R Ω A (Red.sec A (Red.proj R C A c)) := by
  simp only [LinearMap.comp_apply]
  rw [Cobar.ιL_apply, FreeGrL.root_ι, corolla_apply, map₂_mk]
  rfl

lemma cobarSusp_par {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (v : 𝒲 A) :
    (cobarSusp R C).app A (GrSpecies.par (R := R) b v)
      = GrSpecies.par (R := R) (!b) ((cobarSusp R C).app A v) := by
  obtain ⟨x, rfl⟩ := Red.proj_surjective (R := R) (C := C) A
    ((GrSpecies.Shift.of (R := R) (V := Red R C) A).symm v)
  show Red.sec A (GrSpecies.par (R := R) (!b) (Red.proj R C A x)) = _
  rw [Red.sec_par]
  rfl

/-- **The suspended root decomposition is odd.** -/
lemma cobarHs_par {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (x : Ω A) :
    cobarHs R C A (GrOperad.par (R := R) b x) = par R C Ω (!b) (cobarHs R C A x) := by
  simp only [LinearMap.comp_apply]
  rw [FreeGrL.root_par]
  exact map₂_par_odd _ (fun A _ _ b v => cobarSusp_par b v) _ b _

/-- `1 ⊗ (x ∘ᵢ z) = (1 ⊗ x) ◁ᵢ z`. -/
lemma unitCor_comp {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] (i : A)
    (x : Ω A) (z : Ω Y) :
    unitCor R C _ (GrOperad.comp (R := R) i x z) = act R C i z (unitCor R C A x) := by
  set w := act R C () x (corolla R Ω Unit (Coaug.one (R := R) (C := C)))
  have h1 := map_act_seq (V := C) () i x z (corolla R Ω Unit (Coaug.one (R := R) (C := C)))
  have h2 := map_act (V := C) (leftUnitEquiv A) (Equiv.refl Y) (Sum.inr i) z w
  rw [GrOperad.map_refl] at h2
  rw [unitCor_apply, unitCor_apply, ← h1]
  refine Eq.trans ?_ h2
  rw [← map_trans]
  refine map_congr (fun s => ?_) _
  rcases s with ⟨u | a, hs⟩ | y
  · exact absurd (Subsingleton.elim u.1 ()) u.2
  · rfl
  · rfl

lemma unitCor_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : A ≃ B) (x : Ω A) :
    unitCor R C B (GrOperad.map (R := R) σ x) = map σ (unitCor R C A x) := by
  rw [unitCor_apply, unitCor_apply]
  have h := map_act (V := C) (Equiv.refl Unit) σ () x
    (corolla R Ω Unit (Coaug.one (R := R) (C := C)))
  rw [map_refl] at h
  erw [← h]
  simp only [← map_trans]
  exact map_congr (fun s => by rcases s with ⟨a, ha⟩ | y <;> first | rfl | exact absurd rfl ha) _

lemma unitCor_one : unitCor R C Unit (GrOperad.one (R := R)) = corolla R Ω Unit
    (Coaug.one (R := R) (C := C)) := by
  rw [unitCor_apply]
  refine Eq.trans ?_ (map_act_one (V := C) () _)
  exact map_congr (fun s => by rcases s with ⟨a, ha⟩ | y <;> rfl) _

/-! ### Parities -/

omit [GrCooperad.Coaug R C] in
lemma _root_.Operad.GrOperad.par_comp_par {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (b r : Bool) (i : A) (x : P A) (z : P B) :
    GrOperad.par (R := R) b (GrOperad.comp (R := R) i x (GrOperad.par (R := R) r z))
      = GrOperad.comp (R := R) i (GrOperad.par (R := R) (xor b r) x)
          (GrOperad.par (R := R) r z) := by
  have key : ∀ p, GrOperad.par (R := R) b (GrOperad.comp (R := R) i (GrOperad.par (R := R) p x)
      (GrOperad.par (R := R) r z)) = if b = xor p r then GrOperad.comp (R := R) i
        (GrOperad.par (R := R) p x) (GrOperad.par (R := R) r z) else 0 := fun p => by
    rw [← GrOperad.comp_par i p r x z, GrOperad.par_par, GrOperad.comp_par]
  conv_lhs => rw [← GrOperad.par_add (R := R) x]
  rw [map_add, LinearMap.add_apply, map_add, key, key]
  cases b <;> cases r <;> simp

lemma cobarEps_par {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (x : C A) :
    (cobarEps R C).app A (GrSpecies.par (R := R) b x)
      = GrOperad.par (R := R) b ((cobarEps R C).app A x) := by
  rw [cobarEps_apply, cobarEps_apply, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul, GrSpecies.map_par, ← GrOperad.map_par]
  have h := LinearMap.congr_fun (GrCooperad.counit_par (R := R) (C := C))
    (SymSpecies.map (R := R) e.symm x)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  cases b
  · rw [ConvOp.counit_par_false, GrOperad.par_one]
  · rw [h, zero_smul, ← GrOperad.par_one (R := R) (P := Ω), GrOperad.par_par, if_neg (by decide),
      map_zero, smul_zero]

/-- **The counit of the outer cooperation is even.** -/
lemma cobarE_par (b : Bool) (w : GrComposite R C Ω S) :
    cobarE R C S (par R C Ω b w) = GrOperad.par (R := R) b (cobarE R C S w) := by
  revert b
  refine induction_act (fun S _ _ w => ∀ b : Bool,
      cobarE R C S (par R C Ω b w) = GrOperad.par (R := R) b (cobarE R C S w))
    (fun S _ _ b => by simp) (fun S _ _ x y hx hy b => by simp only [map_add, hx, hy])
    (fun S _ _ r x hx b => by simp only [map_smul, hx])
    (fun S S' _ _ _ _ σ x hx b => ?_) (fun S Y _ _ _ _ i z x hx b => ?_)
    (fun A _ _ c b => ?_) w
  · beta_reduce at hx ⊢
    rw [← map_par', cobarE_map, hx, cobarE_map, GrOperad.map_par]
  · beta_reduce at hx ⊢
    have hz : ∀ r : Bool, cobarE R C _ (par R C Ω b (act R C i (GrOperad.par (R := R) r z) x))
        = GrOperad.par (R := R) b (cobarE R C _ (act R C i (GrOperad.par (R := R) r z) x)) := by
      intro r
      have hr := GrOperad.par_par_self (R := R) r z
      rw [par_act b i _ hr, cobarE_act, hx, cobarE_act, GrOperad.par_comp_par]
    have hadd : ∀ z z' : Ω Y, act R C i (z + z') = act R C i z + act R C i z' := fun z z' =>
      (actL R C i).map_add z z'
    rw [← GrOperad.par_add (R := R) z, hadd, LinearMap.add_apply, map_add, map_add, hz, hz,
      map_add, map_add]
  · rw [par_corolla, cobarE_corolla, cobarE_corolla, cobarEps_par]

lemma cobarE_tw (w : GrComposite R C Ω S) :
    cobarE R C S (GrSpecies.tw (R := R) true w) = GrOperad.tw (R := R) true (cobarE R C S w) := by
  rw [GrSpecies.tw_apply, GrOperad.tw_apply, map_add, map_smul]
  show cobarE R C S (par R C Ω false w) + _ • cobarE R C S (par R C Ω true w) = _
  rw [cobarE_par, cobarE_par]

lemma cobarHs_tw {A : Type} [Fintype A] [DecidableEq A] (x : Ω A) :
    cobarHs R C A (GrOperad.tw (R := R) true x) = -GrSpecies.tw (R := R) true (cobarHs R C A x) := by
  rw [GrOperad.tw_apply, GrSpecies.tw_apply, map_add, map_smul, cobarHs_par, cobarHs_par]
  show _ = -(par R C Ω false _ + _ • par R C Ω true _)
  rw [σ_true, neg_one_smul, neg_one_smul, Bool.not_false, Bool.not_true, neg_add, neg_neg,
    add_comm]

omit [GrCooperad.Coaug R C] in
lemma _root_.Operad.GrAug.u_tw {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P] (ε : GrAug R P)
    {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    ε.u A (GrOperad.tw (R := R) true x) = ε.u A x := by
  conv_rhs => rw [← GrOperad.par_add (R := R) x]
  rw [GrOperad.tw_true, map_sub, map_add, ε.u_par, sub_zero, add_zero]

omit [GrCooperad.Coaug R C] in
lemma _root_.Operad.GrComposite.lact_tw
    {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
    {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P] (ε : GrAug R P)
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) (x : P A) :
    lact R V ε (B := B) i (GrOperad.tw (R := R) true x) = lact R V ε i x := by
  simp only [lact, GrAug.u_tw]

/-! ### The differential -/

variable (R C) in
/-- **The differential of `C ∘_ι ΩC`.** -/
noncomputable abbrev cobarD (S : Type) [Fintype S] [DecidableEq S] :
    GrComposite R C Ω S →ₗ[R] GrComposite R C Ω S :=
  twDiff R C εΩ (Cobar.d R C) (Cobar.ι R C) S

lemma cobarD_map {S' : Type} [Fintype S'] [DecidableEq S'] (σ : S ≃ S')
    (w : GrComposite R C Ω S) : cobarD R C S' (map σ w) = map σ (cobarD R C S w) := by
  simp only [twDiff, LinearMap.add_apply, twD, twF_map, ← leafMap_map, map_add]

lemma cobarD_act {Y : Type} [Fintype Y] [DecidableEq Y] (i : S) (z : Ω Y)
    (w : GrComposite R C Ω S) :
    cobarD R C _ (act R C i z w) = act R C i z (cobarD R C S w)
      + act R C i ((Cobar.d R C).app Y z) (GrSpecies.tw (R := R) true w) := by
  simp only [twDiff, LinearMap.add_apply, twD, twF_act, leafD_act, map_add]
  abel

lemma cobarD_par (b : Bool) (w : GrComposite R C Ω S) :
    cobarD R C S (par R C Ω b w) = par R C Ω (!b) (cobarD R C S w) := by
  simp only [twDiff, LinearMap.add_apply, map_add]
  rw [twD_par εΩ (Cobar.isPar_ι R C), Bool.xor_true]
  congr 1
  have := par_leafMap (M := C) (Cobar.d R C).toSpEnd (xor b true) w
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Bool.xor_true] at this
  exact this.symm

lemma cobarD_tw (w : GrComposite R C Ω S) :
    cobarD R C S (GrSpecies.tw (R := R) true w) = -GrSpecies.tw (R := R) true (cobarD R C S w) := by
  simp only [twDiff, LinearMap.add_apply, map_add]
  rw [twD_tw εΩ (Cobar.isPar_ι R C), leafD_tw, neg_add]

lemma cobarD_lact {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    (i : A) (x : Ω A) (ν : GrComposite R C Ω Y) :
    cobarD R C _ (lact R C εΩ i x ν) = lact R C εΩ i x (cobarD R C Y ν) := by
  simp only [lact, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, map_sum,
    map_smul, cobarD_map]

lemma cobarD_corolla {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    cobarD R C A (corolla R Ω A c) = SqExt.snd (ConvOp.toLin ((GrOperad.Inv.star R _
      (corFam (C := C) εΩ) (liftFam εΩ (Cobar.ι R C))).1 A) c) := by
  have h0 : leafD R C (Cobar.d R C) A (corolla R Ω A c) = 0 := leafD_corolla _ c
  refine (congrArg (twD εΩ (Cobar.ι R C) A (corolla R Ω A c) + ·) h0).trans ?_
  exact (add_zero _).trans (twD_corolla εΩ _ c)

/-! ### The augmentation of the cobar construction -/

omit [GrCooperad.Coaug R C] in
lemma _root_.Operad.GrAug.u_par_false {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P] (ε : GrAug R P)
    {A : Type} [Fintype A] [DecidableEq A] (x : P A) :
    ε.u A (GrOperad.par (R := R) false x) = ε.u A x := by
  conv_rhs => rw [← GrOperad.par_add (R := R) x]
  rw [map_add, ε.u_par, add_zero]

omit [GrCooperad.Coaug R C] in
/-- **A product with a family killed by an augmentation is killed by it.** -/
lemma u_star_left {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P] (ε : GrAug R P)
    (G H : GrOperad.Inv R (ConvOp R C P))
    (hG : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), ε.u A (ConvOp.toLin (G.1 A) x) = 0)
    {X : Type} [Fintype X] [DecidableEq X] (c : C X) :
    ε.u X (ConvOp.toLin ((GrOperad.Inv.star R _ G H).1 X) c) = 0 := by
  rw [toLin_star, map_sum]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [toLin_term, ε.u_map]
  generalize GrCooperad.decomp (R := R) (C := C) none
    (SymSpecies.map (R := R) (splitEquiv S).symm c) = t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [ConvOp.kap, LinearMap.coe_sum, Finset.sum_apply, TensorProduct.map_tmul, map_sum,
      ConvOp.mu_tmul, LinearMap.comp_apply, ε.u_comp, hG, zero_mul, Finset.sum_const_zero]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

lemma exists_ιL {A : Type} [Fintype A] [DecidableEq A] (v : 𝒲 A) :
    ∃ c : C A, (FreeGrL.ι R 𝒲).app A v = Cobar.ιL R C A c := by
  obtain ⟨c, hc⟩ := Red.proj_surjective (R := R) (C := C) A
    ((GrSpecies.Shift.of (R := R) (V := Red R C) A).symm v)
  refine ⟨c, ?_⟩
  rw [Cobar.ιL_apply, hc, LinearEquiv.apply_symm_apply]

lemma u_ιL {A : Type} [Fintype A] [DecidableEq A] (c : C A) : (εΩ).u A (Cobar.ιL R C A c) = 0 :=
  FreeGrL.unitCoeffL_ι _

/-- **The cobar differential lands in the augmentation ideal.** -/
lemma u_d {A : Type} [Fintype A] [DecidableEq A] (z : Ω A) :
    (εΩ).u A ((Cobar.d R C).app A z) = 0 := by
  let T : GrSuboperad R Ω :=
    { sub := fun A _ _ => LinearMap.ker ((εΩ).u A ∘ₗ (Cobar.d R C).app A)
      par_mem := by
        intro A _ _ b x hx
        simp only [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
        rw [(Cobar.d R C).app_par]
        cases b
        · exact (εΩ).u_par _
        · rw [Bool.true_xor, Bool.not_true, GrAug.u_par_false, hx]
      map_mem := by
        intro A B _ _ _ _ e x hx
        simp only [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
        rw [(Cobar.d R C).app_map, (εΩ).u_map, hx]
      one_mem := by
        simp only [LinearMap.mem_ker, LinearMap.comp_apply]
        rw [(Cobar.d R C).app_one, map_zero]
      comp_mem := by
        intro A B _ _ _ _ i x y hx hy
        simp only [LinearMap.mem_ker, LinearMap.comp_apply] at hx hy ⊢
        rw [(Cobar.d R C).app_comp, map_add, (εΩ).u_comp, (εΩ).u_comp, hx, hy, zero_mul, mul_zero,
          add_zero] }
  refine FreeGrL.mem_of_ι T (fun k v b _ => ?_) z
  obtain ⟨c, hc⟩ := exists_ιL (R := R) (C := C) v
  show (εΩ).u _ ((Cobar.d R C).app _ ((FreeGrL.ι R 𝒲).app (Fin k) v)) = 0
  rw [hc, Cobar.d_ιL, map_neg, u_star_left εΩ _ _ (fun A _ _ x => u_ιL x), neg_zero]

/-! ### The counit on the twisted differential of a corolla -/

variable (R C) in
/-- **The counit**, as an invariant family of the convolution operad. -/
noncomputable abbrev epsFam : GrOperad.Inv R (ConvOp R C Ω) := famOf (cobarEps R C)

lemma cobarE_snd_star {X : Type} [Fintype X] [DecidableEq X] (c : C X) :
    cobarE R C X (SqExt.snd (ConvOp.toLin ((GrOperad.Inv.star R _ (corFam (C := C) εΩ)
      (liftFam εΩ (Cobar.ι R C))).1 X) c))
      = ConvOp.toLin ((GrOperad.Inv.star R _ (epsFam R C) (Cobar.ι R C)).1 X) c :=
  total_snd_star εΩ (cobarEps R C) (Cobar.isPar_ι R C) c

lemma subsingleton_of_unit {A : Type} (e : Unit ≃ A) : Subsingleton (Unit ≃ A) :=
  ⟨fun e₁ e₂ => Equiv.ext fun _ => by
    rw [← e.apply_symm_apply (e₁ _), ← e.apply_symm_apply (e₂ _)]⟩

/-- **The counit of the twisted differential of a corolla** is the universal twisting morphism. -/
lemma cobarE_cobarD_corolla {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] (c : C A) :
    cobarE R C A (cobarD R C A (corolla R Ω A c)) = Cobar.ιL R C A c := by
  rw [cobarD_corolla, cobarE_snd_star]
  rw [GrOperad.Inv.star_counit_left (epsFam R C) (Cobar.ι R C) (GrOperad.one (R := R))
    (fun A _ _ e x => ?_) (fun A _ _ h => ?_) (Cobar.isPar_ι R C) c]
  · exact GrOperad.one_comp _
  · haveI := subsingleton_of_unit e
    show (cobarEps R C).app A x = _
    rw [cobarEps_apply, Fintype.sum_subsingleton _ e]
  · ext x
    show (cobarEps R C).app A x = 0
    rw [cobarEps_apply, Finset.univ_eq_empty, Finset.sum_empty]

/-! ### The cycle `1 ⊗ 1` -/

variable (R C) in
/-- **The cycle `1 ⊗ 1`**, zero outside the arities of one element. -/
noncomputable abbrev unitTerm (B : Type) [Fintype B] [DecidableEq B] : GrComposite R C Ω B :=
  unitCor R C B (FreeGrL.unitL R 𝒲 B)

lemma unitTerm_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : A ≃ B) : map σ (unitTerm R C A) = unitTerm R C B := by
  rw [unitTerm, ← unitCor_map, FreeGrL.map_unitL]

lemma par_corolla_one (r : Bool) :
    par R C Ω r (corolla R Ω Unit (Coaug.one (R := R) (C := C)))
      = if r = false then corolla R Ω Unit (Coaug.one (R := R) (C := C)) else 0 := by
  rw [par_corolla]
  cases r
  · rw [Coaug.par_one, if_pos rfl]
  · rw [if_neg (by decide), ← Coaug.par_one (R := R) (C := C), GrSpecies.par_par,
      if_neg (by decide), map_zero]

lemma unitCor_par {B : Type} [Fintype B] [DecidableEq B] (b : Bool) (z : Ω B) :
    unitCor R C B (GrOperad.par (R := R) b z) = par R C Ω b (unitCor R C B z) := by
  rw [unitCor_apply, unitCor_apply, ← map_par']
  congr 1
  have key : ∀ r : Bool, par R C Ω b (act R C () (GrOperad.par (R := R) r z)
      (corolla R Ω Unit (Coaug.one (R := R) (C := C))))
      = if b = r then act R C () (GrOperad.par (R := R) r z)
          (corolla R Ω Unit (Coaug.one (R := R) (C := C))) else 0 := fun r => by
    rw [par_act b () _ (GrOperad.par_par_self (R := R) r z), par_corolla_one]
    cases b <;> cases r <;> simp
  have hadd : ∀ z z' : Ω B, act R C () (z + z') = act R C () z + act R C () z' := fun z z' =>
    (actL R C ()).map_add z z'
  conv_rhs => rw [← GrOperad.par_add (R := R) z, hadd, LinearMap.add_apply, map_add, key, key]
  cases b <;> simp

lemma par_smul_unitTerm {B : Type} [Fintype B] [DecidableEq B] (b : Bool) (z : Ω B) :
    (εΩ).u B (GrOperad.par (R := R) b z) • unitTerm R C B
      = par R C Ω b ((εΩ).u B z • unitTerm R C B) := by
  have hL : ∀ r : Bool, GrOperad.par (R := R) r (FreeGrL.unitL R 𝒲 B)
      = if r = false then FreeGrL.unitL R 𝒲 B else 0 := fun r => by
    rw [FreeGrL.unitL, map_sum]
    cases r
    · rw [if_pos rfl]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← GrOperad.map_par, GrOperad.par_one]
    · rw [if_neg (by decide)]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [← GrOperad.map_par, ← GrOperad.par_one (R := R) (P := Ω), GrOperad.par_par,
        if_neg (by decide), map_zero]
  rw [map_smul, unitTerm, ← unitCor_par, hL]
  cases b
  · rw [GrAug.u_par_false, if_pos rfl]
  · rw [(εΩ).u_par, zero_smul, if_neg (by decide), map_zero, smul_zero]

/-- `x ∘ᵢ (1 ⊗ y) = ε(x) (1 ⊗ x ∘ᵢ y)` -/
lemma lact_unitCor {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : Ω A) (y : Ω B) :
    lact R C εΩ i x (unitCor R C B y) = (εΩ).u A x • act R C i y (unitTerm R C A) := by
  by_cases h : IsEmpty (Unit ≃ A)
  · rw [lact_of_isEmpty εΩ h, (εΩ).u_eq_zero h, zero_smul]
    rfl
  · obtain ⟨e⟩ := not_isEmpty_iff.1 h
    haveI := subsingleton_of_unit e
    rw [lact_eq εΩ i x e, unitTerm, ← unitCor_comp, FreeGrL.comp_unitL,
      Fintype.sum_subsingleton _ e, unitCor_map]

lemma lact_unitTerm {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : Ω A) :
    lact R C εΩ i x (unitTerm R C B) = (εΩ).u A x • unitTerm R C (Without A i ⊕ B) := by
  by_cases h : IsEmpty (Unit ≃ A)
  · rw [lact_of_isEmpty εΩ h, (εΩ).u_eq_zero h, zero_smul]
    rfl
  · obtain ⟨e⟩ := not_isEmpty_iff.1 h
    rw [lact_eq εΩ i x e, unitTerm_map]

/-! ### The suspended root decomposition of a generator -/

variable (R C) in
/-- **The suspended root decomposition of the universal twisting morphism**:
`c ↦ c̄ ⊗ (1, …, 1)`. -/
noncomputable def corBarHom : SymSpeciesHom R C (GrComposite R C Ω) where
  app A _ _ := cobarHs R C A ∘ₗ Cobar.ιL R C A
  app_map {A B} _ _ _ _ σ x := by
    show cobarHs R C B (Cobar.ιL R C B (SymSpecies.map (R := R) σ x))
      = map σ (cobarHs R C A (Cobar.ιL R C A x))
    rw [Cobar.ιL_map, cobarHs_map]

lemma card_eq_one_of_unit {A : Type} [Fintype A] (e : Unit ≃ A) : Fintype.card A = 1 := by
  rw [← Fintype.card_congr e, Fintype.card_unit]

/-- **The differential of the corolla of a reduced cooperation**:
`d(c̄ ⊗ 1) = ρ̃((ι ⋆ ι)(c)) + 1 ⊗ ι(c)`. -/
theorem cobarD_corolla_eq
    (hred : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A ≤ 1 →
      ∀ x : C A, x ∈ unitSpan R C A) {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    cobarD R C A (corolla R Ω A (Red.sec A (Red.proj R C A c)))
      = cobarHs R C A (ConvOp.toLin ((Cobar.ιι R C).1 A) c)
        + unitCor R C A (Cobar.ιL R C A c) := by
  by_cases hA : Fintype.card A ≤ 1
  · have hc := hred A hA c
    rw [show Red.proj R C A c = 0 from (Submodule.Quotient.mk_eq_zero _).2 hc,
      Cobar.star_ι_ι_unit R C hc, Cobar.ιL_unitSpan R C hc]
    simp only [map_zero, add_zero]
  · have hE : IsEmpty (Unit ≃ A) := ⟨fun e => hA (by rw [card_eq_one_of_unit e])⟩
    haveI : Nonempty A := Fintype.card_pos_iff.1 (by omega)
    rw [Red.sec_proj hE, unitCor_apply, cobarD_corolla]
    have h1 : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
        (σ : A ≃ B) (x : Ω A), cobarHs R C B (GrOperad.map (R := R) σ x)
          = map σ (cobarHs R C A x) := fun A B _ _ _ _ σ x => cobarHs_map σ x
    have h2 : ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
        (x : Ω A) (y : Ω B), cobarHs R C _ (GrOperad.comp (R := R) i x y)
          = act R C i y (cobarHs R C A x) + lact R C εΩ i x (cobarHs R C B y) :=
      fun A B _ _ _ _ i x y => cobarHs_comp i x y
    have h3 := snd_star_corFam εΩ (corBarHom R C) (fun A _ _ => cobarHs R C A) h1 h2
      (Cobar.ι R C) (fun A _ _ x => u_ιL x) (fun A _ _ x => rfl)
    refine h3 (fun A _ _ e x => ?_) (fun A _ _ h x => ?_) (Cobar.isPar_ι R C) c
    · show corolla R Ω A x - cobarHs R C A (Cobar.ιL R C A x) = _
      rw [cobarHs_ιL, Red.sec_of_nonempty ⟨e⟩, map_zero, sub_zero]
      conv_lhs => rw [eq_counit_smul (hred A (by rw [card_eq_one_of_unit e])) e x]
      rw [map_smul]
    · show cobarHs R C A (Cobar.ιL R C A x) = corolla R Ω A x
      rw [cobarHs_ιL, Red.sec_proj h]

/-! ### The homotopy on the inner operations -/

variable (R C) in
/-- The defect `d ρ̃ + ρ̃ d - (1 ⊗ ·) + ε (1 ⊗ 1)` of the suspended root decomposition. -/
noncomputable def cobarΦ (B : Type) [Fintype B] [DecidableEq B] :
    Ω B →ₗ[R] GrComposite R C Ω B :=
  cobarD R C B ∘ₗ cobarHs R C B + cobarHs R C B ∘ₗ (Cobar.d R C).app B
    - unitCor R C B + LinearMap.smulRight ((εΩ).u B) (unitTerm R C B)

lemma cobarΦ_apply {B : Type} [Fintype B] [DecidableEq B] (z : Ω B) :
    cobarΦ R C B z = cobarD R C B (cobarHs R C B z) + cobarHs R C B ((Cobar.d R C).app B z)
      - unitCor R C B z + (εΩ).u B z • unitTerm R C B := rfl

lemma cobarΦ_par {B : Type} [Fintype B] [DecidableEq B] (b : Bool) (z : Ω B) :
    cobarΦ R C B (GrOperad.par (R := R) b z) = par R C Ω b (cobarΦ R C B z) := by
  rw [cobarΦ_apply, cobarΦ_apply, cobarHs_par, cobarD_par, (Cobar.d R C).app_par, cobarHs_par,
    unitCor_par, par_smul_unitTerm]
  simp only [Bool.xor_true, Bool.not_not, map_add, map_sub]

lemma cobarΦ_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : A ≃ B) (z : Ω A) :
    cobarΦ R C B (GrOperad.map (R := R) σ z) = map σ (cobarΦ R C A z) := by
  rw [cobarΦ_apply, cobarΦ_apply, cobarHs_map, cobarD_map, (Cobar.d R C).app_map, cobarHs_map,
    unitCor_map, (εΩ).u_map, ← unitTerm_map σ]
  simp only [map_add, map_sub, map_smul]

lemma cobarΦ_one : cobarΦ R C Unit (GrOperad.one (R := R)) = 0 := by
  rw [cobarΦ_apply, cobarHs_one, map_zero, zero_add, (Cobar.d R C).app_one, map_zero, zero_sub,
    (εΩ).u_one, one_smul, unitTerm, FreeGrL.unitL_eq (Equiv.refl Unit), GrOperad.map_refl,
    neg_add_cancel]

set_option maxHeartbeats 1000000 in
lemma cobarΦ_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    {x : Ω A} {y : Ω B} (hx : cobarΦ R C A x = 0) (hy : cobarΦ R C B y = 0) :
    cobarΦ R C _ (GrOperad.comp (R := R) i x y) = 0 := by
  rw [cobarΦ_apply] at hx hy
  have hx' : cobarD R C A (cobarHs R C A x) + cobarHs R C A ((Cobar.d R C).app A x)
      = unitCor R C A x - (εΩ).u A x • unitTerm R C A := by
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← hx]
    abel
  have hy' : cobarD R C B (cobarHs R C B y) + cobarHs R C B ((Cobar.d R C).app B y)
      = unitCor R C B y - (εΩ).u B y • unitTerm R C B := by
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← hy]
    abel
  have e1 : act R C i y (cobarD R C A (cobarHs R C A x))
      + act R C i y (cobarHs R C A ((Cobar.d R C).app A x))
      = act R C i y (unitCor R C A x) - (εΩ).u A x • act R C i y (unitTerm R C A) := by
    rw [← map_add, hx', map_sub, map_smul]
  have e2 : lact R C εΩ i x (cobarD R C B (cobarHs R C B y))
      + lact R C εΩ i x (cobarHs R C B ((Cobar.d R C).app B y))
      = (εΩ).u A x • act R C i y (unitTerm R C A)
        - (εΩ).u B y • ((εΩ).u A x • unitTerm R C (Without A i ⊕ B)) := by
    rw [← map_add, hy', map_sub, map_smul, lact_unitCor, lact_unitTerm]
  rw [cobarΦ_apply, cobarHs_comp, map_add, cobarD_act, cobarD_lact, (Cobar.d R C).app_comp,
    GrOperadHom.id_app, GrOperadHom.id_app, map_add, cobarHs_comp, cobarHs_comp,
    lact_of_u εΩ _ (u_d x), LinearMap.zero_apply, add_zero, cobarHs_tw, lact_tw,
    unitCor_comp, (εΩ).u_comp, map_neg]
  linear_combination (norm := module) e1 + e2

lemma cobarΦ_ιL
    (hred : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A ≤ 1 →
      ∀ x : C A, x ∈ unitSpan R C A) {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    cobarΦ R C A (Cobar.ιL R C A c) = 0 := by
  rw [cobarΦ_apply, cobarHs_ιL, Cobar.d_ιL, map_neg, cobarD_corolla_eq hred, u_ιL, zero_smul,
    add_zero]
  abel

variable (R C) in
/-- The suboperad on which the defect vanishes. -/
noncomputable def cobarΦSub : GrSuboperad R Ω where
  sub B _ _ := LinearMap.ker (cobarΦ R C B)
  par_mem := by
    intro B _ _ b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [cobarΦ_par, hx, map_zero]
  map_mem := by
    intro A B _ _ _ _ σ x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [cobarΦ_map, hx, map_zero]
  one_mem := cobarΦ_one
  comp_mem := by
    intro A B _ _ _ _ i x y hx hy
    exact cobarΦ_comp i hx hy

/-- **The suspended root decomposition is a homotopy from `1 ⊗ ·` to `ε (1 ⊗ 1)`**:
`d(ρ̃ z) + ρ̃(d z) = 1 ⊗ z - ε(z) (1 ⊗ 1)`. -/
theorem cobarD_cobarHs
    (hred : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A ≤ 1 →
      ∀ x : C A, x ∈ unitSpan R C A) {B : Type} [Fintype B] [DecidableEq B] (z : Ω B) :
    cobarD R C B (cobarHs R C B z) + cobarHs R C B ((Cobar.d R C).app B z)
      = unitCor R C B z - (εΩ).u B z • unitTerm R C B := by
  have h : cobarΦ R C B z = 0 := LinearMap.mem_ker.1 (FreeGrL.mem_of_ι (cobarΦSub R C)
    (fun k v b _ => by
      obtain ⟨c, hc⟩ := exists_ιL (R := R) (C := C) v
      show _ ∈ LinearMap.ker (cobarΦ R C (Fin k))
      rw [hc, LinearMap.mem_ker]
      exact cobarΦ_ιL hred c) z)
  rw [cobarΦ_apply] at h
  rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← h]
  abel

end Homotopy

end GrComposite

end Operad
