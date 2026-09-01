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
import Operad.Ideal

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

/-! ### An operad presented by generators and relations

The associative operad is the magmatic operad modulo associativity. This is the first operad in
the library given by a presentation rather than built by hand, which is what ideals were for. -/

/-- The associator of the magmatic generator: the difference of the two ternary composites. -/
noncomputable def assocRel (R : Type u) [CommRing R] : Mag R 3 :=
  compFin (R := R) (⟨0, by omega⟩ : Fin 2) (magOp R) (magOp R)
    - compFin (R := R) (⟨1, by omega⟩ : Fin 2) (magOp R) (magOp R)

/-- The single relation presenting associativity, in arity three. -/
def assocRels (R : Type u) [CommRing R] : ∀ n, Set (Mag R n)
  | 3 => {assocRel R}
  | _ => ∅

/-- **The associative operad by a presentation**: one binary generator modulo associativity. -/
noncomputable abbrev AssPres (R : Type u) [CommRing R] : ℕ → Type u :=
  (generated (R := R) (assocRels R)).Quot

noncomputable example (R : Type u) [CommRing R] : NSOperad R (AssPres R) := inferInstance

/-- Associativity holds in the presented operad, by construction. -/
theorem assocRel_eq_zero (R : Type u) [CommRing R] :
    (generated (R := R) (assocRels R)).proj 3 (assocRel R) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (subset_generated _ (by simp [assocRels]))

end Operad
