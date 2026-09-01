import Operad

/-! Axiom audit. Every declaration below should rest only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — in particular never on `sorryAx`. -/

open Operad NSOperad

#print axioms Operad.reindex
#print axioms Operad.reindex_self
#print axioms Operad.reindex_reindex
#print axioms Operad.NSOperad.comp_add_left
#print axioms Operad.NSOperad.comp_add_right
#print axioms Operad.NSOperad.comp_smul_left
#print axioms Operad.NSOperad.comp_smul_right
#print axioms Operad.instNSOperadAss
#print axioms Operad.compFin
#print axioms Operad.comp_index_congr
#print axioms Operad.compFin_eq_comp
#print axioms Operad.NSOperadHom.id

/-- The associative operad really is an instance: this elaborates only if all four
operad axioms were discharged for `Ass`. -/
example (R : Type) [CommRing R] : NSOperad R (Ass R) := inferInstance

/-- Sanity check that composition in `Ass` is multiplication. The arity `n` must be given
explicitly: `Ass R n = R` for every `n`, so a bare scalar does not determine it. -/
example (R : Type) [CommRing R] (x y : R) :
    comp (R := R) (P := Ass R) (n := 4) 2 3 x y = x * y := rfl

/-- The right unit law holds definitionally in this convention, as designed. -/
example (R : Type) [CommRing R] (a b : ℕ) (α : Ass R (a + 1 + b)) :
    comp (R := R) (P := Ass R) a b α (one (R := R) (P := Ass R)) = α :=
  comp_one_right a b α

/-! ## The endomorphism operad -/

#print axioms Operad.End.compMap
#print axioms Operad.End.compL
#print axioms Operad.End.idEnd
#print axioms Operad.End.comp_one_right'
#print axioms Operad.End.comp_one_left'
#print axioms Operad.End.comp_assoc_seq'
#print axioms Operad.End.comp_assoc_par'
#print axioms Operad.End.endOperad

/-- `End R V` really is an operad: this elaborates only if all four axioms were discharged. -/
example (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] :
    NSOperad R (End R V) := inferInstance

/-- Composition in `End` really is "plug `β` into the distinguished slot". -/
example (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
    (a b n : ℕ) (α : End R V (a + 1 + b)) (β : End R V n) (v : Fin (a + n + b) → V) :
    comp (R := R) a b α β v = α (End.insTuple a b (β (End.midTuple a b v)) v) := rfl

/-! ## Morphisms, algebras, the `⋆` product, and the capstone -/

#print axioms Operad.NSOperadHom.comp
#print axioms Operad.Algebra.act
#print axioms Operad.Algebra.act_comp
#print axioms Operad.Algebra.self
#print axioms Operad.Algebra.comap
#print axioms Operad.star
#print axioms Operad.star_add_left
#print axioms Operad.star_smul_left
#print axioms Operad.one_star
#print axioms Operad.star_one
#print axioms Operad.bracket
#print axioms Operad.bracket_antisymm
#print axioms Operad.bracket_self
#print axioms Operad.AssAlgebra.mul_assoc

/-- **The capstone.** Every algebra over `Ass` carries an associative multiplication, and
associativity is *derived* from the operad axioms rather than assumed. -/
example (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
    (A : Algebra R (Ass R) V) (x y z : V) :
    AssAlgebra.mul A (AssAlgebra.mul A x y) z = AssAlgebra.mul A x (AssAlgebra.mul A y z) :=
  AssAlgebra.mul_assoc A x y z

/-- Degrees add under `⋆`: `P (j+1) → P (k+1) → P (j+k+1)`, with no reindexing. -/
example (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (j k : ℕ)
    (α : End R V (j + 1)) (β : End R V (k + 1)) : End R V (j + k + 1) :=
  star (R := R) α β

/-! ## Suboperads and associativity in `∘ᵢ` form -/

#print axioms Operad.Suboperad.instNSOperadSub
#print axioms Operad.Suboperad.incl
#print axioms Operad.comp_arity_congr
#print axioms Operad.compFin_assoc_seq
#print axioms Operad.comp_leading_congr
#print axioms Operad.compFin_assoc_par
#print axioms Operad.compFin_sum_left
#print axioms Operad.sum_nested
#print axioms Operad.star_star_left_split
#print axioms Operad.sum_before_eq
#print axioms Operad.sum_after_eq
#print axioms Operad.disjointPart_symm
#print axioms Operad.star_assoc_symm

/-! ## The total space as a pre-Lie ring -/

#print axioms Operad.tot_assoc_symm
#print axioms Operad.jacobi

/-- `⨁ k, P (k+1)` is a right pre-Lie ring for every non-symmetric operad `P`. -/
example (R : Type) [CommRing R] (P : ℕ → Type)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] :
    RightPreLieRing (Operad.Tot R P) := inferInstance

/-- ... and a Lie algebra over `R`. -/
example (R : Type) [CommRing R] (P : ℕ → Type)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] :
    LieAlgebra R (Operad.Tot R P) := inferInstance

/-- Gerstenhaber's bracket on the endomorphism operad of a module. -/
example (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] :
    LieAlgebra R (Operad.Gerstenhaber R V) := inferInstance

/-! ## The operad of planar trees -/

#print axioms Operad.Tree.graft_graft_seq
#print axioms Operad.Tree.graft_graft_par

/-- Planar trees labelled by any collection `E` form a non-symmetric operad. -/
noncomputable example (R : Type) [CommRing R] (E : ℕ → Type) :
    NSOperad R (Operad.Free R E) := inferInstance

/-! ## The signed product and Maurer–Cartan -/

#print axioms Operad.maurerCartan_iff
#print axioms Operad.ass_maurerCartan

/-! ## The graded pre-Lie identity -/

#print axioms Operad.disjointPartS_symm
#print axioms Operad.sstar_assoc_symm

/-! ## Graded Jacobi -/

#print axioms Operad.jacobiS
#print axioms Operad.two_smul_associator_odd

/-! ## The differential and cohomology -/

#print axioms Operad.dsq_eq
#print axioms Operad.dsq_eq_zero
#print axioms Operad.dLin_dLin
#print axioms Operad.coboundaries_le_cocycles

/-! ## Total composition -/

#print axioms Operad.extend_corolla

/-! ## Ideals, quotients, and presentations -/

#print axioms Operad.OperadIdeal.projHom

/-- The quotient of an operad by an ideal is an operad. -/
noncomputable example (R : Type) [CommRing R] (P : ℕ → Type)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] (I : Operad.OperadIdeal R P) :
    NSOperad R I.Quot := inferInstance

/-- The associative operad, by a presentation. -/
noncomputable example (R : Type) [CommRing R] : NSOperad R (Operad.AssPres R) := inferInstance
