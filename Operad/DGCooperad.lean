/-
# dg cooperads

**A dg cooperad** (`DGCooperad`) is a graded cooperad with an odd differential squaring to zero,
commuting with the relabellings and killed by the counit, which is a **coderivation** of the
decompositions:

  `Δᵢ ∘ d = (d ⊗ 1 + (-1)^• ⊗ d) ∘ Δᵢ`,

the Koszul sign of `d` passing the outer factor. **A morphism of dg cooperads**
(`DGCooperadHom`) is a morphism of graded cooperads commuting with the differentials.
-/
import Operad.GrCoideal

universe u v w

namespace Operad

open Sym GerBV
open scoped TensorProduct

/-- **A dg cooperad**: a graded cooperad with an odd differential commuting with relabellings,
killed by the counit, which is a coderivation of the decompositions. -/
class DGCooperad (R : Type u) [CommRing R]
    (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] extends GrCooperad R C where
  /-- The differential. -/
  d {A : Type} [Fintype A] [DecidableEq A] : C A →ₗ[R] C A
  d_d {A : Type} [Fintype A] [DecidableEq A] (x : C A) : d (d x) = 0
  /-- The differential is odd. -/
  d_par {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (x : C A) :
    d (par b x) = par (!b) (d x)
  map_d {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : C A) : map e (d x) = d (map e x)
  /-- The counit kills the differential. -/
  counit_d (x : C Unit) : counit (d x) = 0
  /-- **The coderivation rule**, the sign carried by the parity involution. -/
  decomp_d {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : C (Without A i ⊕ B)) :
    decomp i (d x) = TensorProduct.map d LinearMap.id (decomp i x)
      + TensorProduct.map (par false - par true) d (decomp i x)

/-- **A morphism of dg cooperads**: a morphism of graded cooperads commuting with the
differentials. -/
structure DGCooperadHom (R : Type u) [CommRing R]
    (C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (D : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (D A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (D A)] [DGCooperad R C]
    [DGCooperad R D] extends GrCooperadHom R C D where
  app_d {A : Type} [Fintype A] [DecidableEq A] (x : C A) :
    app A (DGCooperad.d (R := R) x) = DGCooperad.d (R := R) (app A x)

namespace DGCooperad

variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [DGCooperad R C]

/-- **The coderivation rule**, with the sign twist. -/
lemma decomp_d_tw {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : C (Without A i ⊕ B)) :
    GrCooperad.decomp (R := R) (C := C) i (d (R := R) x)
      = TensorProduct.map (d (R := R)) LinearMap.id (GrCooperad.decomp (R := R) (C := C) i x)
        + TensorProduct.map (GrSpecies.tw (R := R) (V := C) true) (d (R := R))
            (GrCooperad.decomp (R := R) (C := C) i x) := by
  have h : GrSpecies.tw (R := R) (V := C) (A := A) true
      = GrSpecies.par (R := R) false - GrSpecies.par (R := R) true :=
    LinearMap.ext fun y => by
      rw [GrSpecies.tw_apply, σ_true, neg_one_smul, ← sub_eq_add_neg]
      rfl
  rw [decomp_d, h]

variable (R C) in
/-- **A coaugmented dg cooperad**: the differential kills the coaugmentation. -/
class DOne [GrCooperad.Coaug R C] : Prop where
  d_one : d (R := R) (GrCooperad.Coaug.one (R := R) (C := C)) = 0

/-- **The differential kills the relabellings of the coaugmentation.** -/
lemma d_unitSpan [GrCooperad.Coaug R C] [DOne R C] {A : Type} [Fintype A] [DecidableEq A]
    {x : C A} (hx : x ∈ GrCooperad.unitSpan R C A) : d (R := R) x = 0 := by
  refine Submodule.span_induction (p := fun x _ => d (R := R) x = 0) ?_ (map_zero _) ?_ ?_ hx
  · rintro _ ⟨e, rfl⟩
    rw [← map_d, DOne.d_one, map_zero]
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro a x _ hx
    rw [map_smul, hx, smul_zero]

end DGCooperad

end Operad
