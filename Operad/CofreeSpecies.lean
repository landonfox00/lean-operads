/-
# The cofree conilpotent cooperad on a linear species

For a linear species `V` over a `ℚ`-algebra `R`, **the cofree conilpotent cooperad** `T^c(V)`
(`CofreeSp R V`) is the species of the trees with vertices decorated by `V`, with decomposition
by cutting: a symmetric cooperad in `R`-modules (`CofreeSp.instSymCooperad`), coaugmented by the
trivial tree (`CofreeSp.one`). For `V` without elements without inputs and a conilpotent
coaugmented symmetric cooperad `C`, **the coaugmented morphisms of cooperads `C → T^c(V)` are the
morphisms of linear species `C → V` killing the coaugmentation** (`CofreeSp.homEquiv`,
`CofreeSp.existsUnique_lift`), by composition with the projection onto the cogenerators
(`CofreeSp.gen`). No freeness or projectivity is assumed: `Operad/CofreeCooperad.lean` treats the
species free over a collection of generators.

This is the even case of the graded statement. A linear species is a graded linear species
concentrated in even parity (`Ev`), a symmetric cooperad is a graded cooperad concentrated in
even parity (`Ev.instGrCooperad`), with the same coaugmentation and coradical filtration
(`Ev.instCoaug`, `Ev.conilpotent`), and the cut cooperad `T^c(Ev V)` of `Operad/CofreeGrL.lean`
is even, so the Koszul sign of its parallel coassociativity is trivial
(`sswapLast_of_even`). The universal property is `FreeGrL.cofreeHomEquivCut`
(`Operad/CutLift.lean`).

Not included: the comparison of `CofreeSp R V`, for `V` free over a collection `T`, with the
cooperad `Cofree R T` of `Operad/CofreeCooperad.lean`.
-/
import Operad.CutLift
import Operad.GrFreeEven

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-! ## Even parity -/

section Tensor

variable {R : Type u} [CommRing R] {X Y Z : Type v} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]

/-- **The super swap of even factors is the swap.** -/
lemma sswapLast_of_even (pY : Bool → Y →ₗ[R] Y) (pZ : Bool → Z →ₗ[R] Z)
    (hY : pY false = LinearMap.id) (hY' : pY true = 0) (hZ : pZ false = LinearMap.id)
    (hZ' : pZ true = 0) :
    sswapLast R pY pZ = (swapLast R X Y Z).toLinearMap := by
  simp only [sswapLast, Fintype.sum_bool, hY, hY', hZ, hZ', Bool.and_true,
    Bool.and_false, σ_false, one_smul, LinearMap.lTensor_id, LinearMap.lTensor_zero,
    TensorProduct.map_id, TensorProduct.map_zero_left, TensorProduct.map_zero_right,
    LinearMap.comp_id, LinearMap.comp_zero, smul_zero, zero_add]

end Tensor

section Ev

variable {R : Type u} [CommRing R]

variable (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)]

/-- **A linear species in even parity.** -/
@[nolint unusedArguments]
def Ev (A : Type) [Fintype A] [DecidableEq A] : Type w := Q A

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (Ev Q A) :=
  inferInstanceAs (AddCommGroup (Q A))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (Ev Q A) :=
  inferInstanceAs (Module R (Q A))

/-- The parity projections of `Ev Q`: the identity on the even part and zero on the odd part. -/
def Ev.par {A : Type} [Fintype A] [DecidableEq A] (b : Bool) : Ev Q A →ₗ[R] Ev Q A :=
  cond b 0 LinearMap.id

@[simp] lemma Ev.par_false {A : Type} [Fintype A] [DecidableEq A] (x : Ev Q A) :
    Ev.par (R := R) Q false x = x := rfl

@[simp] lemma Ev.par_true {A : Type} [Fintype A] [DecidableEq A] (x : Ev Q A) :
    Ev.par (R := R) Q true x = 0 := rfl

/-- **The underlying linear species of a symmetric cooperad.** -/
instance (priority := 100) SymCooperad.toSymSpecies [SymCooperad R Q] : SymSpecies R Q where
  map := SymCooperad.map (R := R)
  map_refl := SymCooperad.map_refl (R := R)
  map_trans := SymCooperad.map_trans (R := R)

/-- **A linear species is a graded linear species concentrated in even parity.** -/
instance Ev.instGrSpecies [SymSpecies R Q] : GrSpecies R (Ev Q) where
  map e := SymSpecies.map (R := R) (V := Q) e
  map_refl := SymSpecies.map_refl (R := R) (V := Q)
  map_trans := SymSpecies.map_trans (R := R) (V := Q)
  par b := Ev.par Q b
  par_add x := by simp
  par_par b b' x := by cases b <;> cases b' <;> simp
  map_par e b x := by cases b <;> simp

lemma Ev.isEven [SymSpecies R Q] : GrSpecies.IsEven R (Ev Q) := fun _ _ _ _ => rfl

variable [SymCooperad R Q]

/-- **A symmetric cooperad is a graded cooperad concentrated in even parity.** -/
noncomputable instance Ev.instGrCooperad : GrCooperad R (Ev Q) where
  map e := SymCooperad.map (R := R) (C := Q) e
  map_refl := SymCooperad.map_refl (R := R) (C := Q)
  map_trans := SymCooperad.map_trans (R := R) (C := Q)
  par b := Ev.par Q b
  par_add x := by simp
  par_par b b' x := by cases b <;> cases b' <;> simp
  map_par e b x := by cases b <;> simp
  counit := SymCooperad.counit (R := R) (C := Q)
  counit_par := LinearMap.comp_zero _
  decomp i := SymCooperad.decomp (R := R) (C := Q) i
  decomp_par {A B} _ _ _ _ i b := by
    refine LinearMap.ext fun x => ?_
    cases b
    · show SymCooperad.decomp (R := R) (C := Q) i x
        = TensorProduct.map LinearMap.id LinearMap.id (SymCooperad.decomp (R := R) (C := Q) i x)
          + TensorProduct.map 0 0 (SymCooperad.decomp (R := R) (C := Q) i x)
      rw [TensorProduct.map_id, LinearMap.id_apply, TensorProduct.map_zero_left,
        LinearMap.zero_apply, add_zero]
    · show SymCooperad.decomp (R := R) (C := Q) i (0 : Q _)
        = TensorProduct.map LinearMap.id 0 (SymCooperad.decomp (R := R) (C := Q) i x)
          + TensorProduct.map 0 LinearMap.id (SymCooperad.decomp (R := R) (C := Q) i x)
      rw [map_zero, TensorProduct.map_zero_right, TensorProduct.map_zero_left,
        LinearMap.zero_apply, add_zero]
  decomp_map := SymCooperad.decomp_map (R := R) (C := Q)
  counit_right := SymCooperad.counit_right (R := R) (C := Q)
  counit_left := SymCooperad.counit_left (R := R) (C := Q)
  decomp_assoc_seq := SymCooperad.decomp_assoc_seq (R := R) (C := Q)
  decomp_assoc_par {A B D} _ _ _ _ _ _ i k hik :=
    (SymCooperad.decomp_assoc_par (R := R) (C := Q) (B := B) (D := D) hik).trans
      (congrArg (fun s : (Q A ⊗[R] Q B) ⊗[R] Q D →ₗ[R] (Q A ⊗[R] Q D) ⊗[R] Q B => s ∘ₗ _)
        (sswapLast_of_even (R := R) (X := Q A) (Y := Q B) (Z := Q D)
          (fun c => cond c 0 LinearMap.id) (fun c => cond c 0 LinearMap.id)
          rfl rfl rfl rfl).symm)

variable [SymCooperad.Coaug R Q]

/-- The coaugmentation of a symmetric cooperad, in even parity. -/
noncomputable instance Ev.instCoaug : GrCooperad.Coaug R (Ev Q) where
  one := SymCooperad.Coaug.one (R := R) (C := Q)
  par_one := rfl
  counit_one := SymCooperad.Coaug.counit_one
  decomp_mem i e := SymCooperad.Coaug.decomp_mem (R := R) (C := Q) i e

variable {Q}

/-- The coradical filtrations agree. -/
lemma Ev.filt_le (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    SymCooperad.filt R Q n A ≤ GrCooperad.filt R (Ev Q) n A := by
  induction n generalizing A with
  | zero => exact le_rfl
  | succ n ih =>
    intro c hc B D _ _ _ _ i e
    exact GrCooperad.filtTarget_mono (C := Ev Q) (fun A _ _ => ih A) (hc B D i e)

/-- **A conilpotent symmetric cooperad is conilpotent as a graded cooperad.** -/
lemma Ev.conilpotent (hC : SymCooperad.Conilpotent R Q) : GrCooperad.Conilpotent R (Ev Q) :=
  fun A _ _ c => (hC A c).imp fun n hn => Ev.filt_le n A hn

end Ev

/-! ## The cofree conilpotent cooperad -/

section Cofree

variable (R : Type u) [CommRing R]
  (V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [SymSpecies R V]

/-- **The cofree conilpotent cooperad on a linear species**: the trees with vertices decorated
by `V`. -/
def CofreeSp (A : Type) [Fintype A] [DecidableEq A] : Type (max u v) := FreeGrL R (Ev V) A

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (CofreeSp R V A) :=
  inferInstanceAs (AddCommGroup (FreeGrL R (Ev V) A))

noncomputable instance (A : Type) [Fintype A] [DecidableEq A] : Module R (CofreeSp R V A) :=
  inferInstanceAs (Module R (FreeGrL R (Ev V) A))

variable {R V}

/-- The trees decorated by a linear species are even. -/
lemma CofreeSp.par_true {A : Type} [Fintype A] [DecidableEq A] :
    GrSpecies.par (R := R) (V := FreeGrL R (Ev V)) (A := A) true = 0 :=
  LinearMap.ext fun x => (FreeGrL.grPar_eq true x).trans (FreeGrL.isEven (Ev.isEven V) A x)

lemma CofreeSp.par_false {A : Type} [Fintype A] [DecidableEq A] :
    GrSpecies.par (R := R) (V := FreeGrL R (Ev V)) (A := A) false = LinearMap.id :=
  LinearMap.ext fun x => by
    have h := GrSpecies.par_add (R := R) x
    rw [LinearMap.congr_fun CofreeSp.par_true x, LinearMap.zero_apply, add_zero] at h
    exact h

/-- **The cofree conilpotent cooperad on a linear species is a symmetric cooperad**, decomposing
a tree by cutting it. -/
noncomputable instance CofreeSp.instSymCooperad : SymCooperad R (CofreeSp R V) where
  map e := SymSpecies.map (R := R) (V := FreeGrL R (Ev V)) e
  map_refl := SymSpecies.map_refl (R := R) (V := FreeGrL R (Ev V))
  map_trans := SymSpecies.map_trans (R := R) (V := FreeGrL R (Ev V))
  counit := GrCooperad.counit (R := R) (C := FreeGrL R (Ev V))
  decomp i := GrCooperad.decomp (R := R) (C := FreeGrL R (Ev V)) i
  decomp_map := GrCooperad.decomp_map (R := R) (C := FreeGrL R (Ev V))
  counit_right := GrCooperad.counit_right (R := R) (C := FreeGrL R (Ev V))
  counit_left := GrCooperad.counit_left (R := R) (C := FreeGrL R (Ev V))
  decomp_assoc_seq := GrCooperad.decomp_assoc_seq (R := R) (C := FreeGrL R (Ev V))
  decomp_assoc_par {A B D} _ _ _ _ _ _ i k hik := by
    have h := GrCooperad.decomp_assoc_par (R := R) (C := FreeGrL R (Ev V)) (B := B) (D := D) hik
    rw [sswapLast_of_even (X := FreeGrL R (Ev V) A) _ _ CofreeSp.par_false CofreeSp.par_true
      CofreeSp.par_false CofreeSp.par_true] at h
    exact h

variable (R V) in
/-- **The coaugmentation of the cofree conilpotent cooperad**: the trivial tree. -/
noncomputable def CofreeSp.one : CofreeSp R V Unit :=
  GrCooperad.Coaug.one (R := R) (C := FreeGrL R (Ev V))

variable (R V) in
/-- **The projection onto the cogenerators**: the decoration of a tree with one vertex. -/
noncomputable def CofreeSp.gen (A : Type) [Fintype A] [DecidableEq A] :
    CofreeSp R V A →ₗ[R] V A :=
  FreeGrL.genCoef R (Ev V) A

variable {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [SymCooperad R C]

/-- A morphism of symmetric cooperads into `T^c(V)`, as a morphism of graded cooperads. -/
noncomputable def CofreeSp.toGr (f : SymCooperadHom R C (CofreeSp R V)) :
    GrCooperadHom R (Ev C) (FreeGrL R (Ev V)) where
  app A := f.app A
  app_map e x := LinearMap.congr_fun (f.app_map e) x
  app_par {A} _ _ b x := by
    cases b
    · exact (LinearMap.congr_fun CofreeSp.par_false _).symm
    · exact (map_zero _).trans (LinearMap.congr_fun CofreeSp.par_true _).symm
  counit_app := f.counit_app
  decomp_app i := f.decomp_app i

/-- A morphism of graded cooperads into `T^c(Ev V)`, as a morphism of symmetric cooperads. -/
noncomputable def CofreeSp.ofGr (g : GrCooperadHom R (Ev C) (FreeGrL R (Ev V))) :
    SymCooperadHom R C (CofreeSp R V) where
  app A := g.app A
  app_map e := LinearMap.ext fun x => g.app_map e x
  counit_app := g.counit_app
  decomp_app i := g.decomp_app i

omit [SymSpecies R V] in
lemma SymCooperadHom.ext' {D : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (D A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (D A)] [SymCooperad R D]
    {f g : SymCooperadHom R C D}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A), f.app A x = g.app A x) : f = g := by
  obtain ⟨f, _, _, _⟩ := f
  obtain ⟨g, _, _, _⟩ := g
  have : f = g := funext fun A => funext fun _ => funext fun _ => LinearMap.ext (h A)
  subst this
  rfl

variable [SymCooperad.Coaug R C]

/-- A morphism of linear species killing the coaugmentation, as a morphism from the reduced
part in even parity. -/
noncomputable def CofreeSp.redOf (φ : SymSpeciesHom R C V)
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A],
      SymCooperad.coaugSpan R C A ≤ LinearMap.ker (φ.app A)) :
    GrSpeciesHom R (GrCooperad.Red R (Ev C)) (Ev V) :=
  FreeGrL.redLift (C := Ev C) (V := Ev V)
    { app := fun A _ _ => φ.app A
      app_map := fun e x => φ.app_map e x
      app_par := fun b x => by cases b <;> simp [GrSpecies.par] } hφ

variable [Algebra ℚ R]

/-- **The universal property of the cofree conilpotent cooperad on a linear species**: over a
`ℚ`-algebra, for a linear species `V` without elements without inputs and a conilpotent
coaugmented symmetric cooperad `C`, the coaugmented morphisms of cooperads `C → T^c(V)` are the
morphisms of linear species `C → V` killing the coaugmentation, by composition with the
projection onto the cogenerators. -/
noncomputable def CofreeSp.homEquiv (hV0 : ∀ v : V (Fin 0), v = 0)
    (hC : SymCooperad.Conilpotent R C) :
    {f : SymCooperadHom R C (CofreeSp R V) //
      f.app Unit (SymCooperad.Coaug.one (R := R) (C := C)) = CofreeSp.one R V} ≃
    {φ : SymSpeciesHom R C V // ∀ (A : Type) [Fintype A] [DecidableEq A],
      SymCooperad.coaugSpan R C A ≤ LinearMap.ker (φ.app A)} where
  toFun f :=
    ⟨{ app := fun A _ _ => CofreeSp.gen R V A ∘ₗ f.1.app A
       app_map := fun e x => by
         have h := LinearMap.congr_fun (f.1.app_map e) x
         rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
         show FreeGrL.genCoef R (Ev V) _ (f.1.app _ (SymCooperad.map (R := R) e x)) = _
         rw [h]
         show FreeGrL.genCoef R (Ev V) _ (SymSpecies.map (R := R) (V := FreeGrL R (Ev V)) e _) = _
         rw [FreeGrL.symMap_eq, FreeGrL.genCoef_map]
         rfl },
      fun A _ _ => FreeGrL.genCoef_app_unitSpan (V := Ev V) (C := Ev C) (CofreeSp.toGr f.1) f.2⟩
  invFun φ := ⟨CofreeSp.ofGr (FreeGrL.liftCut (V := Ev V) (C := Ev C) hV0 (Ev.conilpotent hC)
      (CofreeSp.redOf φ.1 φ.2)),
    FreeGrL.liftCut_app_one (V := Ev V) (C := Ev C) hV0 (Ev.conilpotent hC)
      (CofreeSp.redOf φ.1 φ.2)⟩
  left_inv f := Subtype.ext (SymCooperadHom.ext' fun A _ _ x =>
    FreeGrL.app_eq_of_genCoef₀ (V := Ev V) (C := Ev C)
      (f := FreeGrL.liftCut (V := Ev V) (C := Ev C) hV0 (Ev.conilpotent hC)
        (CofreeSp.redOf _ _))
      (f' := CofreeSp.toGr f.1) hV0
      (fun A _ _ x => FreeGrL.genCoef_liftCut (V := Ev V) (C := Ev C) hV0 (Ev.conilpotent hC)
        _ x) A x)
  right_inv φ := Subtype.ext (SymSpeciesHom.ext fun A _ _ x =>
    FreeGrL.genCoef_liftCut (V := Ev V) (C := Ev C) hV0 (Ev.conilpotent hC)
      (CofreeSp.redOf φ.1 φ.2) x)

lemma CofreeSp.homEquiv_apply (hV0 : ∀ v : V (Fin 0), v = 0)
    (hC : SymCooperad.Conilpotent R C)
    (f : {f : SymCooperadHom R C (CofreeSp R V) //
      f.app Unit (SymCooperad.Coaug.one (R := R) (C := C)) = CofreeSp.one R V})
    {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    (CofreeSp.homEquiv hV0 hC f).1.app A x = CofreeSp.gen R V A (f.1.app A x) := rfl

/-- **The cofree property**: on a conilpotent coaugmented symmetric cooperad, a morphism of
linear species into a linear species `V` without elements without inputs killing the
coaugmentation lifts uniquely to a coaugmented morphism of cooperads into `T^c(V)`, over a
`ℚ`-algebra. -/
theorem CofreeSp.existsUnique_lift (hV0 : ∀ v : V (Fin 0), v = 0)
    (hC : SymCooperad.Conilpotent R C) (φ : SymSpeciesHom R C V)
    (hφ : ∀ (A : Type) [Fintype A] [DecidableEq A],
      SymCooperad.coaugSpan R C A ≤ LinearMap.ker (φ.app A)) :
    ∃! f : {f : SymCooperadHom R C (CofreeSp R V) //
        f.app Unit (SymCooperad.Coaug.one (R := R) (C := C)) = CofreeSp.one R V},
      ∀ (A : Type) [Fintype A] [DecidableEq A] (x : C A),
        CofreeSp.gen R V A (f.1.app A x) = φ.app A x := by
  refine ⟨(CofreeSp.homEquiv hV0 hC).symm ⟨φ, hφ⟩, fun A _ _ x => ?_, fun f hf => ?_⟩
  · exact congrArg (fun ψ : {φ : SymSpeciesHom R C V // ∀ (A : Type) [Fintype A]
        [DecidableEq A], SymCooperad.coaugSpan R C A ≤ LinearMap.ker (φ.app A)} => ψ.1.app A x)
      ((CofreeSp.homEquiv hV0 hC).apply_symm_apply ⟨φ, hφ⟩)
  · refine ((CofreeSp.homEquiv hV0 hC).symm_apply_apply f).symm.trans (congrArg _ ?_)
    exact Subtype.ext (SymSpeciesHom.ext fun A _ _ x => hf A x)

end Cofree

end Operad
