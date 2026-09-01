/-
# Generators inside the free operad, and the magmatic operad

`Operad.Free` builds the operad of planar trees on a collection `E`; `Operad.TotalComp` evaluates
such a tree in an arbitrary operad. This file connects the two ends: `genOf` includes a generator
into the free operad as its corolla, and `extend_genOf` records that evaluation sends it back to
where it came from.

It also gives the library its first operad beyond `Ass` and `End`: the magmatic operad, free on a
single binary operation. Its algebras are magmas — a binary operation with no axioms at all —
which is exactly what a free operad on one binary generator should present.
-/
import Operad.Free
import Operad.TotalComp

universe u v w

namespace Operad

open NSOperad

section

variable {R : Type u} [CommRing R] {E : ℕ → Type v}

/-- A generator, viewed inside the free operad as its corolla. -/
noncomputable def genOf {k : ℕ} (e : E k) : Free R E k :=
  Free.gen ⟨corolla e, arity_corolla e⟩

lemma genOf_def {k : ℕ} (e : E k) :
    genOf (R := R) e = Free.gen ⟨corolla e, arity_corolla e⟩ := rfl

variable {Q : ℕ → Type w} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

/-- Evaluation sends a generator's corolla back to the generator. -/
theorem extend_genOf (f : ∀ k, E k → Q k) {k : ℕ} (e : E k) :
    extend (R := R) f (corolla e) = reindex R Q (arity_corolla e).symm (f k e) :=
  extend_corolla f e

end

/-! ### The magmatic operad -/

/-- The generating collection of the magmatic operad: exactly one operation, of arity two. -/
def MagGen : ℕ → Type
  | 2 => PUnit
  | _ => PEmpty

/-- The single binary generator. -/
def magMul : MagGen 2 := PUnit.unit

/-- **The magmatic operad**: the free non-symmetric operad on one binary operation. Its algebras
are magmas, since the generator satisfies no relations. -/
noncomputable abbrev Mag (R : Type u) [CommRing R] : ℕ → Type u := Free R MagGen

noncomputable example (R : Type u) [CommRing R] : NSOperad R (Mag R) := inferInstance

/-- The binary operation of the magmatic operad. -/
noncomputable def magOp (R : Type u) [CommRing R] : Mag R 2 := genOf magMul

end Operad
