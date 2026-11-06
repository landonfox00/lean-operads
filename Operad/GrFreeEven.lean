/-
# The free graded operad on even generators is the free operad in modules

A symmetric operad in modules is a graded operad concentrated in even parity (`SymGr`, with the
parity projections `1` and `0`). Morphisms of graded operads into `SymGr Q` restrict on even
parts to morphisms of symmetric operads into `Q` (`GrOperadHom.toSymOfEven`), and morphisms of
symmetric operads into the even part of a graded operad `P` are morphisms of graded operads
`SymGr Q → P` (`SymOperadHom.toGrEven`).

For an even graded linear species `E` (`GrSpecies.IsEven`), the universal properties of the free
graded operad `FreeGrL R E` and of the free operad in modules `FreeL R E` (`FreeSpecies.lean`)
give inverse morphisms (`FreeGrL.toFreeL`, `FreeGrL.ofFreeL`, `FreeGrL.toFreeL_ofFreeL`,
`FreeGrL.ofFreeL_toFreeL`). So **the free graded operad on even generators is, arity by arity,
the free operad in modules** (`FreeGrL.freeLEquiv`), and its even part is the free operad as a
symmetric operad (`FreeGrL.evenFreeLHom`, `FreeGrL.evenFreeLHom_bijective`). This moves
`T(E)` into the ungraded framework of `ShuffleFreeSym.lean` and `ShuffleSymPres.lean`, where the
free operad on a set of generators, a free species, has a basis of shuffle monomials
(`FreeSet.shuffleBasis`). Open: the same for `FreeL R E` when `E(2)` is not a free
`𝔖₂`-module, as for `Com`, `Lie` and `Pois`, and the comparison of the bar constructions.
-/
import Operad.GrShuffle
import Operad.FreeSpecies

universe u v w

namespace Operad

open Sym GerBV

/-! ## Symmetric operads as even graded operads -/

section SymGr

variable {R : Type u} [CommRing R]

variable (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)]

/-- **A symmetric operad as a graded operad**, every operation being even. -/
def SymGr (A : Type) [Fintype A] [DecidableEq A] : Type w := Q A

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (SymGr Q A) :=
  inferInstanceAs (AddCommGroup (Q A))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (SymGr Q A) :=
  inferInstanceAs (Module R (Q A))

/-- The parity projections of `SymGr Q`: the identity on the even part and zero on the odd
part. -/
def SymGr.par {A : Type} [Fintype A] [DecidableEq A] (b : Bool) : SymGr Q A →ₗ[R] SymGr Q A :=
  cond b 0 LinearMap.id

@[simp] lemma SymGr.par_false {A : Type} [Fintype A] [DecidableEq A] (x : SymGr Q A) :
    SymGr.par (R := R) Q false x = x := rfl

@[simp] lemma SymGr.par_true {A : Type} [Fintype A] [DecidableEq A] (x : SymGr Q A) :
    SymGr.par (R := R) Q true x = 0 := rfl

variable [SymOperad R Q]

/-- **A symmetric operad is a graded operad concentrated in even parity.** -/
instance SymGr.instGrOperad : GrOperad R (SymGr Q) where
  par b := SymGr.par Q b
  par_add x := by simp
  par_par b b' x := by cases b <;> cases b' <;> simp
  map e := SymOperad.map (R := R) (P := Q) e
  map_refl := SymOperad.map_refl (R := R) (P := Q)
  map_trans := SymOperad.map_trans (R := R) (P := Q)
  map_par e b x := by cases b <;> simp
  one := SymOperad.one R (P := Q)
  par_one := rfl
  comp i := SymOperad.comp (R := R) (P := Q) i
  comp_par i p q x y := by cases p <;> cases q <;> simp
  map_comp := SymOperad.map_comp (R := R) (P := Q)
  comp_one := SymOperad.comp_one (R := R) (P := Q)
  one_comp := SymOperad.one_comp (R := R) (P := Q)
  comp_assoc_seq := SymOperad.comp_assoc_seq (R := R) (P := Q)
  comp_assoc_par := by
    intro A B D _ _ _ _ _ _ i k hik x q r y z hy hz
    cases q
    · cases r
      · rw [Bool.and_self, σ_false, one_smul]
        exact SymOperad.comp_assoc_par (R := R) (P := Q) hik x y z
      · have hz0 : z = 0 := hz.symm
        subst hz0
        simp
    · have hy0 : y = 0 := hy.symm
      subst hy0
      simp

@[simp] lemma SymGr.grPar (b : Bool) {A : Type} [Fintype A] [DecidableEq A] (x : SymGr Q A) :
    GrOperad.par (R := R) b x = SymGr.par (R := R) Q b x := rfl

end SymGr

section Transfer

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **A morphism of graded operads into `SymGr Q`, on the even part**, a morphism of symmetric
operads into `Q`. -/
def GrOperadHom.toSymOfEven (φ : GrOperadHom R P (SymGr Q)) :
    SymOperadHom R (GrOperad.EvenOp R P) Q where
  app A _ _ := φ.app A ∘ₗ (GrOperad.evenSub R P).incl.app A
  app_map e x := φ.app_map e x.val
  app_one := φ.app_one
  app_comp i x y := φ.app_comp i x.val y.val

@[simp] lemma GrOperadHom.toSymOfEven_app (φ : GrOperadHom R P (SymGr Q)) {A : Type} [Fintype A]
    [DecidableEq A] (x : GrOperad.EvenOp R P A) : φ.toSymOfEven.app A x = φ.app A x.val := rfl

/-- The even part of an operation of the even part. -/
lemma GrOperad.EvenOp.par_false_val {A : Type} [Fintype A] [DecidableEq A]
    (x : GrOperad.EvenOp R P A) : GrOperad.par (R := R) false x.val = x.val := by
  have e := GrOperad.par_add (R := R) x.val
  rwa [(GrOperad.mem_evenSub x.val).1 x.2, add_zero] at e

/-- The odd part of an operation of the even part vanishes. -/
lemma GrOperad.EvenOp.par_true_val {A : Type} [Fintype A] [DecidableEq A]
    (x : GrOperad.EvenOp R P A) : GrOperad.par (R := R) true x.val = 0 :=
  (GrOperad.mem_evenSub x.val).1 x.2

/-- **A morphism of symmetric operads into the even part of `P`**, a morphism of graded operads
`SymGr Q → P`. -/
def SymOperadHom.toGrEven (ψ : SymOperadHom R Q (GrOperad.EvenOp R P)) :
    GrOperadHom R (SymGr Q) P where
  app A _ _ := (GrOperad.evenSub R P).incl.app A ∘ₗ ψ.app A
  app_par b x := by
    cases b
    · exact (GrOperad.EvenOp.par_false_val (ψ.app _ x)).symm
    · show (ψ.app _ 0).val = _
      rw [map_zero]
      exact (GrOperad.EvenOp.par_true_val (ψ.app _ x)).symm
  app_map e x := congrArg GrOperad.EvenOp.val (ψ.app_map e x)
  app_one := congrArg GrOperad.EvenOp.val ψ.app_one
  app_comp i x y := congrArg GrOperad.EvenOp.val (ψ.app_comp i x y)

@[simp] lemma SymOperadHom.toGrEven_app (ψ : SymOperadHom R Q (GrOperad.EvenOp R P))
    {A : Type} [Fintype A] [DecidableEq A] (x : SymGr Q A) :
    ψ.toGrEven.app A x = (ψ.app A x).val := rfl

end Transfer

/-! ## The free graded operad on even generators -/

namespace GrSpecies

variable {R : Type u} [CommRing R] {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

/-- In an even graded linear species every element is its even part. -/
lemma par_false_of_isEven (hV : IsEven R V) {A : Type} [Fintype A] [DecidableEq A] (v : V A) :
    GrSpecies.par (R := R) false v = v := by
  have e := GrSpecies.par_add (R := R) v
  rwa [hV A v, add_zero] at e

end GrSpecies

namespace FreeGrL

variable {R : Type u} [CommRing R] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (E A)] [GrSpecies R E]
  (hE : GrSpecies.IsEven R E)

/-- The generators of the free operad in modules, as a morphism of graded linear species into
`SymGr (FreeL R E)`. -/
noncomputable def toFreeLSp : GrSpeciesHom R E (SymGr (FreeL R E)) where
  app A _ _ := (FreeL.ι R E).app A
  app_map e x := (FreeL.ι R E).app_map e x
  app_par b x := by
    cases b
    · show (FreeL.ι R E).app _ (GrSpecies.par (R := R) false x) = (FreeL.ι R E).app _ x
      rw [GrSpecies.par_false_of_isEven hE]
    · show (FreeL.ι R E).app _ (GrSpecies.par (R := R) true x) = 0
      rw [hE _ x, map_zero]

/-- **The comparison morphism `T(E) → FreeL R E`**, of graded operads. -/
noncomputable def toFreeL : GrOperadHom R (FreeGrL R E) (SymGr (FreeL R E)) :=
  homEquiv.symm (toFreeLSp hE)

@[simp] lemma toFreeL_ι {A : Type} [Fintype A] [DecidableEq A] (v : E A) :
    (toFreeL hE).app A ((ι R E).app A v) = (FreeL.ι R E).app A v :=
  homEquiv_symm_ι _ v

/-- The generators of the free graded operad, as a morphism of linear species into its even
part. -/
noncomputable def ofFreeLSp : SymSpeciesHom R E (GrOperad.EvenOp R (FreeGrL R E)) where
  app A _ _ := ((ι R E).app A).codRestrict ((GrOperad.evenSub R (FreeGrL R E)).sub A)
    fun _ => (GrOperad.mem_evenSub _).2 (isEven hE A _)
  app_map e x := GrOperad.EvenOp.ext ((ι R E).app_map e x)

/-- **The comparison morphism `FreeL R E → T(E)`**, of symmetric operads into the even part. -/
noncomputable def ofFreeL : SymOperadHom R (FreeL R E) (GrOperad.EvenOp R (FreeGrL R E)) :=
  FreeL.homEquiv.symm (ofFreeLSp hE)

@[simp] lemma ofFreeL_ι_val {A : Type} [Fintype A] [DecidableEq A] (v : E A) :
    ((ofFreeL hE).app A ((FreeL.ι R E).app A v)).val = (ι R E).app A v := by
  rw [ofFreeL, FreeL.homEquiv_symm_ι]
  rfl

/-- **`T(E) → FreeL R E → T(E)` is the identity.** -/
theorem ofFreeL_toFreeL : (ofFreeL hE).toGrEven.comp (toFreeL hE) = GrOperadHom.id R _ :=
  hom_ext fun A _ _ v => by
    rw [GrOperadHom.comp_app, toFreeL_ι, SymOperadHom.toGrEven_app, ofFreeL_ι_val]
    rfl

/-- **`FreeL R E → T(E) → FreeL R E` is the identity.** -/
theorem toFreeL_ofFreeL : (toFreeL hE).toSymOfEven.comp (ofFreeL hE) = SymOperadHom.id :=
  FreeL.hom_ext fun A _ _ v => by
    rw [SymOperadHom.comp_app, GrOperadHom.toSymOfEven_app, ofFreeL_ι_val, toFreeL_ι]
    rfl

lemma ofFreeL_toFreeL_app {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R E A) :
    ((ofFreeL hE).app A ((toFreeL hE).app A x)).val = x :=
  congrArg (fun φ : GrOperadHom R (FreeGrL R E) (FreeGrL R E) => φ.app A x) (ofFreeL_toFreeL hE)

lemma toFreeL_ofFreeL_app {A : Type} [Fintype A] [DecidableEq A] (y : FreeL R E A) :
    (toFreeL hE).app A ((ofFreeL hE).app A y).val = y :=
  congrArg (fun φ : SymOperadHom R (FreeL R E) (FreeL R E) => φ.app A y) (toFreeL_ofFreeL hE)

/-- **The free graded operad on even generators is the free operad in modules**, arity by
arity. -/
noncomputable def freeLEquiv (A : Type) [Fintype A] [DecidableEq A] :
    FreeGrL R E A ≃ₗ[R] FreeL R E A where
  toFun x := (toFreeL hE).app A x
  map_add' x y := map_add _ x y
  map_smul' c x := map_smul _ c x
  invFun y := ((ofFreeL hE).app A y).val
  left_inv x := ofFreeL_toFreeL_app hE x
  right_inv y := toFreeL_ofFreeL_app hE y

/-- **The even part of the free graded operad on even generators is the free operad in
modules**, as a symmetric operad. -/
noncomputable def evenFreeLHom : SymOperadHom R (GrOperad.EvenOp R (FreeGrL R E)) (FreeL R E) :=
  (toFreeL hE).toSymOfEven

theorem evenFreeLHom_bijective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Bijective ((evenFreeLHom hE).app A) := by
  refine ⟨fun x y h => GrOperad.EvenOp.ext ?_, fun y => ⟨(ofFreeL hE).app A y, ?_⟩⟩
  · have hx := ofFreeL_toFreeL_app hE x.val
    have hy := ofFreeL_toFreeL_app hE y.val
    have h' : (toFreeL hE).app A x.val = (toFreeL hE).app A y.val := h
    rw [← hx, ← hy, h']
  · exact toFreeL_ofFreeL_app hE y

end FreeGrL

end Operad
