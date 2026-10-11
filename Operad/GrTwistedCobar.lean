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

end Homotopy

end GrComposite

end Operad
