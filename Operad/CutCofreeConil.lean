/-
# The cut cooperad on a species with elements of one input

Let `V` be a graded linear species without elements without inputs, possibly with elements of one
input, and `C` a coaugmented graded cooperad, over a `ℚ`-algebra `R`.

* **Uniqueness** holds for every graded cooperad `C`: two morphisms of graded cooperads
  `C → T^c(V)` with the same coefficient of the generators agree (`FreeGrL.app_eq_of_genCoef₀`,
  `Operad/CutCofree.lean`). Their difference has values with arbitrarily many vertices, and an
  element of `T^c(V)` is a finite sum of trees (`FreeGrL.eq_zero_of_forall_mem_vxGe`).
* **The graded coradical filtration** (`GrCooperad.filt`) mirrors the ungraded one
  (`SymCooperad.filt`): `F₀ = R·1`, and `F_{n+1}` consists of the cooperations all of whose
  relabelled decompositions lie in `R·1 ⊗ C + C ⊗ R·1 + Fₙ ⊗ Fₙ`. The cooperad is
  **conilpotent** when the filtration is exhaustive (`GrCooperad.Conilpotent`).
* **Existence.** On a conilpotent `C`, a lift to the homogeneous generators killing the
  coaugmentation has locally finite coefficients (`FreeGrL.coefFinite_of_conil`): a tree with
  vertices pairs trivially with `R·1` (`FreeGrL.coefF_eq_zero_of_unitSpan`), and a cooperation
  of `F_{n+1}` pairs nontrivially, up to `R·1`, only through decompositions in `Fₙ ⊗ Fₙ`. The
  resulting morphism is coaugmented (`FreeGrL.liftOf_app_one`). A morphism `C̄ → V` from the
  reduced part lifts to the generators when in each arity the reduced cooperations or the elements
  of `V` form a projective module (`FreeGrL.redGenLift`).

So **the coaugmented morphisms of graded cooperads `C → T^c(V)` are the morphisms of graded
linear species `C̄ → V`** (`FreeGrL.cofreeHomEquivConil`, `FreeGrL.existsUnique_liftConil`).
Species with elements without inputs are not treated, and projectivity on one side remains
needed for existence: the transposition goes through scalar functionals on `C`.
-/
import Operad.CutCofree
import Operad.CofreeCooperad

universe u v w

namespace Operad

open Sym GerBV TreeOfArity FreeGr FreeReg
open scoped TensorProduct

/-! ## The graded coradical filtration -/

namespace GrCooperad

variable (R : Type u) [CommRing R] (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C] [Coaug R C]

/-- The decompositions allowed in the stage after `F` of the graded coradical filtration:
`R·1 ⊗ C + C ⊗ R·1 + F ⊗ F`. -/
def filtTarget (F : ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (C A)) (A B : Type)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] : Submodule R (C A ⊗[R] C B) :=
  SymCooperad.tensSub R (unitSpan R C A) ⊤ ⊔ SymCooperad.tensSub R ⊤ (unitSpan R C B) ⊔
    SymCooperad.tensSub R (F A) (F B)

/-- **The graded coradical filtration**: `F₀ = R·1`, and `F_{n+1}` consists of the cooperations
all of whose relabelled decompositions lie in `R·1 ⊗ C + C ⊗ R·1 + Fₙ ⊗ Fₙ`. -/
def filt : ℕ → ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (C A)
  | 0 => fun A _ _ => unitSpan R C A
  | n + 1 => fun A _ _ =>
    { carrier := {c | ∀ (B D : Type) [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
          (i : B) (e : Without B i ⊕ D ≃ A),
          decomp (R := R) i (SymSpecies.map (R := R) e.symm c) ∈ filtTarget R C (filt n) B D}
      add_mem' := fun ha hb B D _ _ _ _ i e => by
        simpa only [map_add] using add_mem (ha B D i e) (hb B D i e)
      zero_mem' := fun B D _ _ _ _ i e => by simp only [map_zero, zero_mem]
      smul_mem' := fun r c hc B D _ _ _ _ i e => by
        simpa only [map_smul] using Submodule.smul_mem _ r (hc B D i e) }

/-- **A conilpotent graded cooperad**: its coradical filtration is exhaustive. -/
def Conilpotent : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (c : C A), ∃ n, c ∈ filt R C n A

variable {R C}
variable {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
  [DecidableEq D]

lemma filtTarget_mono {F G : ∀ (A : Type) [Fintype A] [DecidableEq A], Submodule R (C A)}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], F A ≤ G A) :
    filtTarget R C F B D ≤ filtTarget R C G B D :=
  sup_le_sup_left (Submodule.map₂_le_map₂ (h B) (h D)) _

lemma mem_filt_succ {n : ℕ} {c : C A} :
    c ∈ filt R C (n + 1) A ↔ ∀ (B D : Type) [Fintype B] [DecidableEq B] [Fintype D]
      [DecidableEq D] (i : B) (e : Without B i ⊕ D ≃ A),
      decomp (R := R) i (SymSpecies.map (R := R) e.symm c) ∈ filtTarget R C (filt R C n) B D :=
  Iff.rfl

lemma filt_zero : filt R C 0 A = unitSpan R C A :=
  rfl

/-- **The span of the coaugmentation is a subcooperad.** -/
lemma decomp_mem_unitSpan (i : A) {c : C (Without A i ⊕ B)}
    (hc : c ∈ unitSpan R C (Without A i ⊕ B)) :
    decomp (R := R) i c ∈ SymCooperad.tensSub R (unitSpan R C A) (unitSpan R C B) := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    exact Coaug.decomp_mem i e
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx

/-- **Every stage of the filtration contains the coaugmentation.** -/
lemma unitSpan_le_filt (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    unitSpan R C A ≤ filt R C n A := by
  induction n generalizing A with
  | zero => exact le_rfl
  | succ n ih =>
    intro c hc B D _ _ _ _ i e
    have := decomp_mem_unitSpan (R := R) (C := C) i (unitSpan_le_comap_map e.symm hc)
    exact Submodule.mem_sup_right ((Submodule.map₂_le_map₂ (ih B) (ih D)) this)

/-- **The graded coradical filtration is increasing.** -/
lemma filt_mono (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    filt R C n A ≤ filt R C (n + 1) A := by
  induction n generalizing A with
  | zero => exact unitSpan_le_filt 1 A
  | succ n ih =>
    intro c hc B D _ _ _ _ i e
    exact filtTarget_mono (fun A _ _ => ih A) (hc B D i e)

end GrCooperad

/-! ## Lifts on a conilpotent cooperad -/

namespace FreeGrL

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Algebra ℚ R] {φ : GrSpeciesHom R C V}

local notation "𝟙" => GrCooperad.Coaug.one (R := R) (C := C)

omit [Algebra ℚ R] in
/-- A lift killing the relabellings of the coaugmentation kills their span. -/
lemma genLift_L_eq_zero (ℓ : GenLift₀ φ)
    (hℓ : ∀ (k : ℕ) (e : Unit ≃ Fin k), ℓ.L k (SymSpecies.map (R := R) e 𝟙) = 0) {k : ℕ}
    {c : C (Fin k)} (hc : c ∈ GrCooperad.unitSpan R C (Fin k)) : ℓ.L k c = 0 := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    exact hℓ k e
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

/-- **A tree with vertices pairs trivially with the coaugmentation**, for a lift killing it. -/
lemma coefF_eq_zero_of_unitSpan (ℓ : GenLift₀ φ)
    (hℓ : ∀ (k : ℕ) (e : Unit ≃ Fin k), ℓ.L k (SymSpecies.map (R := R) e 𝟙) = 0)
    (x : Reg (TreeOfArity (GrGen R V)) A) (hx : FreeGr.vcnt x ≠ 0) {c : C A}
    (hc : c ∈ GrCooperad.unitSpan R C A) : FreeGr.coefF (liftOp ℓ) x c = 0 := by
  refine FreeReg.induction (P := fun A _ _ x => FreeGr.vcnt x ≠ 0 → ∀ c : C A,
    c ∈ GrCooperad.unitSpan R C A → FreeGr.coefF (liftOp ℓ) x c = 0) ?_ ?_ ?_ ?_ x hx c hc
  · intro A B _ _ _ _ e x ih hv c hc
    rw [FreeGr.coefF_map]
    exact ih (by rwa [FreeGr.vcnt_map] at hv) _ (GrCooperad.unitSpan_le_comap_map e.symm hc)
  · intro hv
    exact absurd FreeGr.vcnt_one hv
  · intro A B _ _ _ _ i x y ihx ihy hv c hc
    rw [FreeGr.coefF_comp]
    refine mul_eq_zero_of_right _ (SymCooperad.pair_eq_zero_of_mem ?_
      (GrCooperad.decomp_mem_unitSpan i hc))
    rw [FreeGr.vcnt_comp] at hv
    by_cases h0 : FreeGr.vcnt x = 0
    · exact Or.inr (ihy (by omega))
    · exact Or.inl (ihx h0)
  · intro k g _ c hc
    rw [coefF_std, genLift_L_eq_zero ℓ hℓ hc, Finsupp.coe_zero, Pi.zero_apply, mul_zero]

/-- **On a conilpotent cooperad, the coefficients of a lift killing the coaugmentation are
locally finite**: by induction on the stage of the coradical filtration, a cooperation pairs
nontrivially with finitely many trees. -/
theorem coefFinite_of_conil (hC : GrCooperad.Conilpotent R C) (ℓ : GenLift₀ φ)
    (hℓ : ∀ (k : ℕ) (e : Unit ≃ Fin k), ℓ.L k (SymSpecies.map (R := R) e 𝟙) = 0) :
    FreeGr.CoefFinite (liftOp ℓ) := by
  have hunit : ∀ {A : Type} [Fintype A] [DecidableEq A] (t : Reg (TreeOfArity (GrGen R V)) A),
      FreeGr.vcnt t ≠ 0 → ∀ c ∈ GrCooperad.unitSpan R C A, FreeGr.coefF (liftOp ℓ) t c = 0 :=
    fun t ht _ hc => coefF_eq_zero_of_unitSpan ℓ hℓ t ht hc
  suffices h : ∀ n (A : Type) [Fintype A] [DecidableEq A], ∀ c ∈ GrCooperad.filt R C n A,
      (Function.support fun t : Reg (TreeOfArity (GrGen R V)) A =>
        FreeGr.coefF (liftOp ℓ) t c).Finite by
    intro A _ _ c
    obtain ⟨n, hn⟩ := hC A c
    exact h n A c hn
  intro n
  induction n with
  | zero =>
    intro A _ _ c hc
    refine (Set.finite_range fun e : Unit ≃ A =>
      (SetOperad.map e SetOperad.one : Reg (TreeOfArity (GrGen R V)) A)).subset fun t ht => ?_
    by_contra hne
    refine ht (hunit t (fun h0 => hne ?_) c hc)
    obtain ⟨e, he⟩ := FreeGr.eq_map_one_of_vcnt h0
    exact ⟨e, he.symm⟩
  | succ n ih =>
    intro A _ _ c hc
    have hV : ∀ (a b : ℕ) (i : Fin a) (e : Without (Fin a) i ⊕ Fin b ≃ A),
        {pq : Reg (TreeOfArity (GrGen R V)) (Fin a) × Reg (TreeOfArity (GrGen R V)) (Fin b) |
          FreeGr.vcnt pq.1 ≠ 0 ∧ FreeGr.vcnt pq.2 ≠ 0 ∧
          SymCooperad.pair (FreeGr.coefF (liftOp ℓ) pq.1) (FreeGr.coefF (liftOp ℓ) pq.2)
            (GrCooperad.decomp (R := R) i (SymSpecies.map (R := R) e.symm c)) ≠ 0}.Finite := by
      intro a b i e
      obtain ⟨w₁₂, hw₁₂, w₃, hw₃, hsum⟩ := Submodule.mem_sup.1 (hc (Fin a) (Fin b) i e)
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 hw₁₂
      refine (SymCooperad.finite_support_pair (fun p => FreeGr.coefF (liftOp ℓ) p)
        (fun q => FreeGr.coefF (liftOp ℓ) q) (fun m hm => ih (Fin a) m hm)
        (fun m hm => ih (Fin b) m hm) hw₃).subset fun pq ⟨hp, hq, hne⟩ => ?_
      rw [← hsum, map_add, map_add,
        SymCooperad.pair_eq_zero_of_mem (Or.inl (hunit pq.1 hp)) hw₁,
        SymCooperad.pair_eq_zero_of_mem (Or.inr (hunit pq.2 hq)) hw₂, zero_add, zero_add] at hne
      exact hne
    let U₀ : Set (Reg (TreeOfArity (GrGen R V)) A) :=
      Set.range fun e : Unit ≃ A => SetOperad.map e SetOperad.one
    let U₁ : Set (Reg (TreeOfArity (GrGen R V)) A) := ⋃ e : Fin (Fintype.card A) ≃ A,
      (fun g => SetOperad.map e (Reg.std (corolla g))) ''
        ↑(ℓ.L (Fintype.card A) (SymSpecies.map (R := R) e.symm c)).support
    let U₂ : Set (Reg (TreeOfArity (GrGen R V)) A) := ⋃ a ∈ Finset.range (Fintype.card A + 2),
      ⋃ b ∈ Finset.range (Fintype.card A + 1), ⋃ i : Fin a,
        ⋃ e : Without (Fin a) i ⊕ Fin b ≃ A,
        (fun pq : Reg (TreeOfArity (GrGen R V)) (Fin a) ×
            Reg (TreeOfArity (GrGen R V)) (Fin b) =>
          SetOperad.map e (SetOperad.comp i pq.1 pq.2)) ''
          {pq | FreeGr.vcnt pq.1 ≠ 0 ∧ FreeGr.vcnt pq.2 ≠ 0 ∧
            SymCooperad.pair (FreeGr.coefF (liftOp ℓ) pq.1) (FreeGr.coefF (liftOp ℓ) pq.2)
              (GrCooperad.decomp (R := R) i (SymSpecies.map (R := R) e.symm c)) ≠ 0}
    have h₀ : U₀.Finite := Set.finite_range _
    have h₁ : U₁.Finite := Set.finite_iUnion fun e => (Finset.finite_toSet _).image _
    have h₂ : U₂.Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) fun a _ =>
        Set.Finite.biUnion (Finset.finite_toSet _) fun b _ =>
          Set.finite_iUnion fun i => Set.finite_iUnion fun e => (hV _ _ i e).image _
    refine ((h₀.union h₁).union h₂).subset fun t ht => ?_
    rw [Function.mem_support] at ht
    rcases FreeGr.shapeR t with ⟨e, rfl⟩ | ⟨k, g, e, rfl⟩ | ⟨a, b, i, p, q, e, hp, hq, rfl⟩
    · exact Or.inl (Or.inl ⟨e, rfl⟩)
    · obtain rfl : k = Fintype.card A := by simpa using Fintype.card_congr e
      rw [FreeGr.coefF_map, coefF_std] at ht
      refine Or.inl (Or.inr (Set.mem_iUnion.2 ⟨e, g, Finsupp.mem_support_iff.2 ?_, rfl⟩))
      exact right_ne_zero_of_mul ht
    · have hcard := Fintype.card_congr e
      rw [Fintype.card_sum, Reg.card_without, Fintype.card_fin, Fintype.card_fin] at hcard
      have ha := i.pos
      rw [FreeGr.coefF_map, FreeGr.coefF_comp] at ht
      refine Or.inr (Set.mem_iUnion₂.2 ⟨a, ?_, Set.mem_iUnion₂.2 ⟨b, ?_, Set.mem_iUnion.2 ⟨i,
        Set.mem_iUnion.2 ⟨e, ⟨(p, q), ⟨hp, hq, right_ne_zero_of_mul ht⟩, rfl⟩⟩⟩⟩⟩)
      · exact Finset.mem_coe.2 (Finset.mem_range.2 (by omega))
      · exact Finset.mem_coe.2 (Finset.mem_range.2 (by omega))

/-- **The morphism given by a lift killing the coaugmentation is coaugmented.** -/
theorem liftOf_app_one (ℓ : GenLift₀ φ)
    (hℓ : ∀ (k : ℕ) (e : Unit ≃ Fin k), ℓ.L k (SymSpecies.map (R := R) e 𝟙) = 0)
    (hΨ : FreeGr.CoefFinite (liftOp ℓ)) :
    (liftOf ℓ hΨ).app Unit 𝟙 = GrCooperad.Coaug.one (R := R) (C := FreeGrL R V) := by
  have h1 : 𝟙 ∈ GrCooperad.unitSpan R C Unit := by
    have := GrCooperad.map_one_mem (R := R) (C := C) (Equiv.refl Unit)
    rwa [SymSpecies.map_refl] at this
  have h : FreeGr.ofCoefL (liftOp ℓ) hΨ Unit 𝟙
      = GrCooperad.Coaug.one (R := R) (C := FreeGr R (grGenPar R V)) := by
    refine Finsupp.ext fun t => ?_
    rw [FreeGr.ofCoefL_apply]
    show _ = (Finsupp.single (SetOperad.one : Reg (TreeOfArity (GrGen R V)) Unit) (1 : R)) t
    by_cases ht : t = SetOperad.one
    · subst ht
      rw [FreeGr.coefF_one, GrCooperad.Coaug.counit_one, Finsupp.single_eq_same]
    · have hw : FreeGr.vcnt t ≠ 0 := fun h0 => ht (by
        obtain ⟨e, he⟩ := FreeGr.eq_map_one_of_vcnt h0
        rw [he, Subsingleton.elim e (Equiv.refl Unit), SetOperad.map_refl])
      rw [Finsupp.single_eq_of_ne ht]
      exact coefF_eq_zero_of_unitSpan ℓ hℓ t hw h1
  show (projHom R V).app Unit (FreeGr.ofCoefL (liftOp ℓ) hΨ Unit 𝟙) = _
  rw [h]
  rfl

/-! ## Lifts from the reduced part -/

omit [Algebra ℚ R] in
/-- **The coefficient of the generators kills the units.** -/
lemma genCoef_one :
    genCoef R V Unit (GrCooperad.Coaug.one (R := R) (C := FreeGrL R V)) = 0 := by
  show genCoef R V Unit ((GrOperadIdeal.span R (grLinRel R V)).proj Unit
    (SgnLin.bas (treeSgn (grGenPar R V)) R SetOperad.one)) = 0
  rw [genCoef_proj, genCoefF_bas, coefReg_of_weight_ne]
  exact Nat.zero_ne_one

omit [Algebra ℚ R] in
/-- **A coaugmented morphism into the cut cooperad has a cogenerator part killing the
coaugmentation.** -/
lemma genCoef_app_unitSpan (f : GrCooperadHom R C (FreeGrL R V))
    (hf : f.app Unit 𝟙 = GrCooperad.Coaug.one (R := R) (C := FreeGrL R V)) :
    GrCooperad.unitSpan R C A ≤ LinearMap.ker (genCoef R V A ∘ₗ f.app A) :=
  Submodule.span_le.2 fun _ ⟨e, he⟩ => LinearMap.mem_ker.2 (by
    rw [← he, LinearMap.comp_apply, f.app_map, hf]
    show genCoef R V A (GrOperad.map (R := R) e _) = 0
    rw [genCoef_map, genCoef_one, map_zero])

omit [Algebra ℚ R] in
variable (φ) in
/-- **A morphism killing the coaugmentation is a morphism from the reduced part.** -/
noncomputable def redLift
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A],
      GrCooperad.unitSpan R C A ≤ LinearMap.ker (φ.app A)) :
    GrSpeciesHom R (GrCooperad.Red R C) V where
  app A _ _ := (GrCooperad.unitSpan R C A).liftQ (φ.app A) (hφ A)
  app_map {A B} _ _ _ _ e X := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective A X
    exact φ.app_map e x
  app_par {A} _ _ b X := by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective A X
    exact φ.app_par b x

omit [Algebra ℚ R] in
@[simp] lemma redLift_app_proj
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A],
      GrCooperad.unitSpan R C A ≤ LinearMap.ker (φ.app A)) (x : C A) :
    (redLift φ hφ).app A (GrCooperad.Red.proj R C A x) = φ.app A x :=
  rfl

omit [Algebra ℚ R] in
/-- **The lift of a morphism from the reduced part**, through the projection, when in each arity
the reduced cooperations or the elements of `V` form a projective module. -/
noncomputable def redGenLift (ψ : GrSpeciesHom R (GrCooperad.Red R C) V)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (V (Fin k))) :
    GenLift₀ (ψ.comp (redProjHom R C)) where
  L k := liftLOf ψ k (hproj k) ∘ₗ GrCooperad.Red.proj R C (Fin k)
  lc k x := lc_liftLOf ψ (hproj k) (GrCooperad.Red.proj R C (Fin k) x)
  par k b x g := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← GrCooperad.Red.par_proj, liftLOf_par]

omit [Algebra ℚ R] in
lemma redGenLift_one (ψ : GrSpeciesHom R (GrCooperad.Red R C) V)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (V (Fin k))) (k : ℕ) (e : Unit ≃ Fin k) :
    (redGenLift ψ hproj).L k (SymSpecies.map (R := R) e 𝟙) = 0 := by
  show liftLOf ψ k (hproj k) (GrCooperad.Red.proj R C (Fin k) (SymSpecies.map (R := R) e 𝟙)) = 0
  rw [GrCooperad.Red.proj_map_one, map_zero]

/-- **The coaugmented morphism given by a morphism from the reduced part**, on a conilpotent
cooperad. -/
noncomputable def liftConil (hC : GrCooperad.Conilpotent R C)
    (ψ : GrSpeciesHom R (GrCooperad.Red R C) V)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (V (Fin k))) :
    GrCooperadHom R C (FreeGrL R V) :=
  liftOf (redGenLift ψ hproj) (coefFinite_of_conil hC _ (redGenLift_one ψ hproj))

lemma liftConil_app_one (hC : GrCooperad.Conilpotent R C)
    (ψ : GrSpeciesHom R (GrCooperad.Red R C) V)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (V (Fin k))) :
    (liftConil hC ψ hproj).app Unit 𝟙 = GrCooperad.Coaug.one (R := R) (C := FreeGrL R V) :=
  liftOf_app_one _ (redGenLift_one ψ hproj) _

/-- **The cogenerator part of the lift is the given morphism.** -/
lemma genCoef_liftConil (hC : GrCooperad.Conilpotent R C)
    (ψ : GrSpeciesHom R (GrCooperad.Red R C) V)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (V (Fin k))) (x : C A) :
    genCoef R V A ((liftConil hC ψ hproj).app A x) = ψ.app A (GrCooperad.Red.proj R C A x) :=
  genCoef_liftOf _ _ x

/-! ## The universal property -/

/-- **The universal property of the cut cooperad on a species with elements of one input**: over
a `ℚ`-algebra, for a graded linear species `V` without elements without inputs and a conilpotent
coaugmented graded cooperad `C` such that in each arity the reduced cooperations or the elements
of `V` form a projective module, the coaugmented morphisms of graded cooperads `C → T^c(V)` are
the morphisms of graded linear species `C̄ → V` from the reduced part, by composition with the
projection onto the cogenerators. -/
noncomputable def cofreeHomEquivConil (hV0 : ∀ v : V (Fin 0), v = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (V (Fin k))) :
    {f : GrCooperadHom R C (FreeGrL R V) //
      f.app Unit 𝟙 = GrCooperad.Coaug.one (R := R) (C := FreeGrL R V)} ≃
    GrSpeciesHom R (GrCooperad.Red R C) V where
  toFun f := redLift ((genCoefHom R V).comp f.1.toGrSpeciesHom)
    fun _ _ _ => genCoef_app_unitSpan f.1 f.2
  invFun ψ := ⟨liftConil hC ψ hproj, liftConil_app_one hC ψ hproj⟩
  left_inv f := Subtype.ext (GrCooperadHom.ext (app_eq_of_genCoef₀ hV0
    fun _ _ _ x => genCoef_liftConil hC _ hproj x))
  right_inv ψ := GrSpeciesHom.ext fun A _ _ X => by
    obtain ⟨x, rfl⟩ := GrCooperad.Red.proj_surjective A X
    exact genCoef_liftConil hC ψ hproj x

lemma cofreeHomEquivConil_apply (hV0 : ∀ v : V (Fin 0), v = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (V (Fin k)))
    (f : {f : GrCooperadHom R C (FreeGrL R V) //
      f.app Unit 𝟙 = GrCooperad.Coaug.one (R := R) (C := FreeGrL R V)}) (x : C A) :
    (cofreeHomEquivConil hV0 hC hproj f).app A (GrCooperad.Red.proj R C A x)
      = genCoef R V A (f.1.app A x) :=
  rfl

/-- **The cofree property of the cut cooperad on a species with elements of one input**: on a
conilpotent coaugmented graded cooperad, every morphism of graded linear species into a graded
linear species `V` without elements without inputs killing the coaugmentation lifts uniquely to
a morphism of graded cooperads into `T^c(V)`, over a `ℚ`-algebra, when in each arity the reduced
cooperations or the elements of `V` form a projective module. The lift is coaugmented
(`FreeGrL.liftConil_app_one`). -/
theorem existsUnique_liftConil (hV0 : ∀ v : V (Fin 0), v = 0)
    (hC : GrCooperad.Conilpotent R C)
    (hproj : ∀ k, Module.Projective R (GrCooperad.Red R C (Fin k)) ∨
      Module.Projective R (V (Fin k)))
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A],
      GrCooperad.unitSpan R C A ≤ LinearMap.ker (φ.app A)) :
    ∃! f : GrCooperadHom R C (FreeGrL R V), ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
      genCoef R V A (f.app A x) = φ.app A x :=
  ⟨liftConil hC (redLift φ hφ) hproj, fun _ _ _ x => genCoef_liftConil hC (redLift φ hφ) hproj x,
    fun _ hf => GrCooperadHom.ext (app_eq_of_genCoef₀ hV0 fun A _ _ x =>
      (hf A x).trans (genCoef_liftConil hC (redLift φ hφ) hproj x).symm)⟩

end FreeGrL

end Operad
