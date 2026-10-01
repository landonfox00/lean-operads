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

/-! ## Species -/

#print axioms Operad.Species.act_trans

/-- The endomorphism species exists for every module. -/
noncomputable example (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] :
    Operad.Species R := Operad.Species.endSpecies R V

/-! ## Toward the universal property -/

#print axioms Operad.substF_comp

#print axioms Operad.extend_graft
#print axioms Operad.substF_graftF

#print axioms Operad.extendHom
#print axioms Operad.extendHom_corolla

#print axioms Operad.OperadIdeal.liftHom
#print axioms Operad.assPresToAss

#print axioms Operad.app_extend
#print axioms Operad.arity_substTree

#print axioms Operad.Species.unitSpecies

#print axioms Operad.partMap_refl
#print axioms Operad.partMap_trans

#print axioms Operad.extend_genMap_self
#print axioms Operad.extendHom_unique

/-! ## The weight grading -/

#print axioms Operad.Tree.weight_graft
#print axioms Operad.Free.comp_mem_weightSpan
#print axioms Operad.assocRel_mem_weightSpan

/-! ## Cooperads -/

#print axioms Operad.instNSCooperadAss

/-- Every commutative ring gives an associative cooperad. -/
noncomputable example (R : Type) [CommRing R] : Operad.NSCooperad R (Operad.Ass R) :=
  inferInstance

/-! ## Presentations -/

#print axioms Operad.Presentation.Op
#print axioms Operad.Presentation.proj
#print axioms Operad.Presentation.gen
#print axioms Operad.Presentation.rel_eq_zero
#print axioms Operad.Presentation.lift
#print axioms Operad.Presentation.lift_gen
#print axioms Operad.Presentation.hom_ext
#print axioms Operad.Presentation.lift_unique
#print axioms Operad.assPresToAssOfRep
#print axioms Operad.assPresToAssOfRep_eq

/-- The presented operad really is an operad: this elaborates only if the quotient
instance applies to the ideal generated by an arbitrary family of relations. -/
noncomputable example (R : Type) [CommRing R] (E : ℕ → Type) (p : Operad.Presentation R E) :
    Operad.NSOperad R p.Op := inferInstance

/-! ## The convolution algebra -/

#print axioms Operad.Conv.compT
#print axioms Operad.Conv.convTerm
#print axioms Operad.Conv.star
#print axioms Operad.Conv.star_add_left
#print axioms Operad.Conv.star_add_right
#print axioms Operad.Conv.star_smul_left
#print axioms Operad.Conv.star_smul_right
#print axioms Operad.Conv.star_zero_left
#print axioms Operad.Conv.star_zero_right
#print axioms Operad.Conv.bracket
#print axioms Operad.Conv.bracket_antisymm
#print axioms Operad.Conv.bracket_self
#print axioms Operad.Conv.convTerm_ass

/-- The convolution algebra of the associative cooperad into the associative operad is a
module: this elaborates only if the `Pi` structure on degreewise maps is available. -/
noncomputable example (R : Type) [CommRing R] :
    Module R (Operad.Conv R (Operad.Ass R) (Operad.Ass R)) := inferInstance

/-! ## The operad `Perm` -/

#print axioms Operad.Perm.sum_split3
#print axioms Operad.Perm.permComp
#print axioms Operad.Perm.permComp_apply_lt
#print axioms Operad.Perm.permComp_apply_mid
#print axioms Operad.Perm.permComp_apply_ge
#print axioms Operad.Perm.compL
#print axioms Operad.Perm.sum_permComp
#print axioms Operad.Perm.permComp_one_right
#print axioms Operad.Perm.permComp_one_left
#print axioms Operad.Perm.permComp_assoc_seq
#print axioms Operad.Perm.permComp_assoc_par
#print axioms Operad.instNSOperadPerm
#print axioms Operad.Perm.evHom

/-- `Perm` really is an instance: this elaborates only if all four operad axioms were
discharged for it. -/
example (R : Type) [CommRing R] : Operad.NSOperad R (Operad.Perm R) := inferInstance

/-- And `ev` really is a morphism `Perm → Ass`: the total of a composite is the product
of the totals. -/
noncomputable example (R : Type) [CommRing R] :
    Operad.NSOperadHom R (Operad.Perm R) (Operad.Ass R) := Operad.Perm.evHom R

/-! ## The convolution algebra is pre-Lie -/

#print axioms RightPreLieRing.jacobi
#print axioms RightPreLieRing.toLieRing
#print axioms RightPreLieRing.toLieAlgebra
#print axioms Operad.Conv.star_eq_sum
#print axioms Operad.Conv.nested_term
#print axioms Operad.Conv.parallel_term
#print axioms Operad.Conv.sum_nested
#print axioms Operad.Conv.sum_after_eq_sum_before
#print axioms Operad.Conv.associator_eq
#print axioms Operad.Conv.star_assoc_symm
#print axioms Operad.ConvAlg.instRightPreLieRing
#print axioms Operad.ConvAlg.instRightPreLieAlgebra
#print axioms Operad.ConvAlg.instLieRing
#print axioms Operad.ConvAlg.instLieAlgebra

/-- The convolution algebra of any cooperad into any operad is a Lie algebra over `R`: this
elaborates only if the pre-Lie identity was proved. -/
noncomputable example (R : Type) [CommRing R] :
    LieAlgebra R (Operad.ConvAlg R (Operad.Ass R) (Operad.Ass R)) := inferInstance

/-! ## Symmetric operads, by partial composition over finite types -/

#print axioms Operad.Sym.seqEquiv
#print axioms Operad.Sym.parEquiv
#print axioms Operad.Sym.compEquiv
#print axioms Operad.Sym.rightUnitEquiv
#print axioms Operad.Sym.leftUnitEquiv
#print axioms Operad.SymOperad.map_symm_map
#print axioms Operad.SymOperad.comp_one'
#print axioms Operad.SymOperad.one_comp'
#print axioms Operad.SymOperadHom.ext
#print axioms Operad.SymOperadHom.comp
#print axioms Operad.Sym.instSymOperadCom
#print axioms Operad.Sym.Perm.sum_compFun
#print axioms Operad.Sym.instSymOperadPerm
#print axioms Operad.Sym.Perm.sumHom

/-! ## The underlying non-symmetric operad -/

#print axioms Operad.Sym.insertEquiv
#print axioms Operad.SymOperad.comp_map_left
#print axioms Operad.SymOperad.comp_map_right
#print axioms Operad.SymOperad.comp_slot
#print axioms Operad.SymOperad.nsComp_one_right
#print axioms Operad.SymOperad.nsComp_one_left
#print axioms Operad.SymOperad.nsComp_assoc_seq
#print axioms Operad.SymOperad.nsComp_assoc_par
#print axioms Operad.SymOperad.instNSOperadToNS
#print axioms Operad.SymOperadHom.toNS
#print axioms Operad.Sym.Perm.toNS_comp_eq_permComp
#print axioms Operad.Sym.Perm.toNSHom

/-- `Com` and `Perm` really are symmetric operads, summing is a morphism between them, and every
symmetric operad has an underlying non-symmetric one. -/
example (R : Type) [CommRing R] : Operad.SymOperad R (Operad.Sym.Perm R) := inferInstance
example (R : Type) [CommRing R] :
    Operad.NSOperad R (Operad.SymOperad.toNS (Operad.Sym.Perm R)) := inferInstance

/-! ## Set operads and linearization -/

#print axioms Operad.SetOperadHom.ext
#print axioms Operad.SetOperadHom.comp
#print axioms Operad.SetOperad.map_injective
#print axioms Operad.Lin.compL_single
#print axioms Operad.instSymOperadLin
#print axioms Operad.instSetOperadUnd
#print axioms Operad.SetOperadHom.linExtend
#print axioms Operad.SymOperadHom.restrictBasis
#print axioms Operad.linHomEquiv

/-! ## Presented set operads, and the binary calculus -/

#print axioms Operad.Syn.eval_eq_of_rel
#print axioms Operad.Pres.instSetOperad
#print axioms Operad.Pres.lift
#print axioms Operad.Pres.hom_ext
#print axioms Operad.Pres.homEquiv
#print axioms Operad.Pres.linHomEquiv
#print axioms Operad.FreeSet.homEquiv
#print axioms Operad.SetOperad.comp_map_left_of
#print axioms Operad.SetOperad.bin_map
#print axioms Operad.SetOperad.bin_one_one
#print axioms Operad.SetOperad.bin_swap
#print axioms Operad.SetOperad.comp_inl_bin
#print axioms Operad.SetOperad.comp_inr_bin
#print axioms Operad.SetOperad.subst3_map
#print axioms Operad.SetOperad.subst3_bin_left
#print axioms Operad.SetOperad.subst3_bin_right
#print axioms Operad.SetOperad.bin_assoc_of
#print axioms Operad.SetOperad.bin_right_of
#print axioms Operad.SetOperad.bin_left_of
#print axioms Operad.SetOperad.bin_comm_of

/-! ## The commutative set operad: generalized associativity and commutativity -/

#print axioms Operad.SetOperadIso.equiv
#print axioms Operad.SetOperadHom.app_bin
#print axioms Operad.SetOperad.comb_perm
#print axioms Operad.SetOperad.map_prod
#print axioms Operad.SetOperad.bin_prod
#print axioms Operad.SetOperad.comp_prod
#print axioms Operad.ComSet.lift
#print axioms Operad.ComSet.hom_ext
#print axioms Operad.ComSet.homEquiv
#print axioms Operad.ComSet.linHomEquiv
#print axioms Operad.ComSet.comPresIso
#print axioms Operad.SetOperad.app_prod
#print axioms Operad.SymOperadHom.und
#print axioms Operad.Sym.Perm.eq_zero_of_isComm_isAssoc
#print axioms Operad.Sym.Perm.app_eq_zero_of_isComm_isAssoc
#print axioms Operad.SymOperadHom.invOfBijective
#print axioms Operad.SymOperadHom.precompEquiv

/-! ## Infinitesimal bimodules -/

#print axioms Operad.SymInfBimodule.self
#print axioms Operad.SymInfBimodule.restrict
#print axioms Operad.SymOperadHom.ker
#print axioms Operad.Sym.Perm.mem_kerSum

/-! ## Non-symmetric set operads -/

#print axioms Operad.instNSOperadLinNS
#print axioms Operad.SetOperad.instNSSetOperadToNSSet
#print axioms Operad.NSSyn.eval_eq_of_rel
#print axioms Operad.NSPres.instNSSetOperad
#print axioms Operad.NSPres.hom_ext
#print axioms Operad.NSPres.homEquiv
#print axioms Operad.NSSetOperadHom.invOfBijective
#print axioms Operad.NSSetOperadIso.ofBijective

/-! ## The planar calculus without reindexing; right-comb normal forms -/

#print axioms Operad.NSSetOperad.Arr.mk_comp
#print axioms Operad.NSSetOperad.Arr.comp_one
#print axioms Operad.NSSetOperad.Arr.one_comp
#print axioms Operad.NSSetOperad.Arr.comp_comp_nested
#print axioms Operad.NSSetOperad.Arr.comp_comp_disjoint
#print axioms Operad.NSSetOperad.Arr.comp_bin_left
#print axioms Operad.NSSetOperad.Arr.comp_bin_right
#print axioms Operad.NSSetOperad.Arr.bin_bin_of_left_right
#print axioms Operad.NSSetOperad.Arr.bin_right_of
#print axioms Operad.NSSetOperad.Arr.bin_left_of
#print axioms Operad.NSSetOperad.Arr.leftComb_eq
#print axioms Operad.NSSetOperad.Arr.rightComb_eq
#print axioms Operad.NSSetOperad.Arr.isRComb_bin
#print axioms Operad.NSSetOperad.Arr.isRComb_comp
#print axioms Operad.NSSetOperad.Arr.map_comp
#print axioms Operad.NSSetOperad.Arr.map_rcomb
#print axioms Operad.NSSetOperad.Arr.pres_induction
#print axioms Operad.NSSetOperad.Arr.pres_isRComb

/-! ## Non-symmetric operads in modules and non-symmetric set operads -/

#print axioms Operad.NSOperadIso.trans
#print axioms Operad.NSOperadIso.bijective
#print axioms Operad.NSOperadIso.ofBijective
#print axioms Operad.instNSSetOperadUndNS
#print axioms Operad.NSOperadHom.und
#print axioms Operad.linHomEquivNS
#print axioms Operad.NSOperadHom.ext_single
#print axioms Operad.NSSetOperadHom.lin
#print axioms Operad.NSSetOperadIso.lin
#print axioms Operad.SetOperad.toNSLinIso

/-! ## Suboperads and filtered symmetric operads -/

#print axioms Operad.SymOperadHom.range
#print axioms Operad.SymOperadFiltration.zero
#print axioms Operad.SymOperadFiltration.map
#print axioms Operad.weightFiltration

/-! ## The endomorphism operad and algebras over a symmetric operad -/

#print axioms Operad.Sym.EndOp.compML
#print axioms Operad.Sym.instSymOperadEndOp
#print axioms Operad.Sym.SymAlgebra.act_comp
#print axioms Operad.Sym.SymAlgebra.act_map
#print axioms Operad.Sym.SymAlgebra.act_one
#print axioms Operad.SymOperadHom.ext_single
#print axioms Operad.SetOperadHom.lin

/-! ## Isomorphisms of symmetric operads -/

#print axioms Operad.SymOperadHom.comp_id
#print axioms Operad.SymOperadHom.id_comp
#print axioms Operad.SymOperadHom.comp_assoc
#print axioms Operad.SymOperadIso.trans
#print axioms Operad.SymOperadIso.bijective
#print axioms Operad.SymOperadIso.ofBijective

/-! ## Weighted set operads: the associated graded and the Rees family -/

#print axioms Operad.SetOperadWeight.defect_assoc_seq
#print axioms Operad.SetOperadWeight.defect_assoc_par
#print axioms Operad.instSymOperadTwLin
#print axioms Operad.TwLin.filtration
#print axioms Operad.TwLin.liftHom
#print axioms Operad.TwLin.isoLin
#print axioms Operad.Gr.comp_single
#print axioms Operad.Gr.sign
#print axioms Operad.Gr.sign_comp_sign
#print axioms Operad.Gr.evZero
#print axioms Operad.TwLin.specialize
#print axioms Operad.TwLin.specializeL_surjective
#print axioms Operad.TwLin.specializeL_eq_zero_iff

/-! ## Binary trees, the convolution operad of the free binary operad, and Koszul duals -/

#print axioms Operad.BTree.graft_inj
#print axioms Operad.BTree.graft_graft_seq
#print axioms Operad.BTree.graft_graft_par
#print axioms Operad.BTree.mem_ofArityFinset
#print axioms Operad.instNSOperadTConv
#print axioms Operad.TConv.valuedIn
#print axioms Operad.TConv.eval_comp_outer
#print axioms Operad.TConv.eval_comp_inner
#print axioms Operad.TConv.ann
#print axioms Operad.TConv.koszulDual_sliceClosed
#print axioms Operad.BTree.OfArity.cases_four
#print axioms Operad.TConv.compFin_apply_graft
#print axioms Operad.TConv.sstar_apply_lc
#print axioms Operad.TConv.sstar_apply_rc
#print axioms Operad.TConv.sstar12_apply_ll
#print axioms Operad.TConv.sstar21_apply_bl
#print axioms Operad.TConv.gbracket11_apply
#print axioms Operad.TConv.gbracket12_apply
#print axioms Operad.Perm.compFin_3_2_two
#print axioms Operad.Perm.sumZero
#print axioms Operad.TConv.eval_compFin_in
#print axioms Operad.TConv.eval_compFin_out
#print axioms Operad.TConv.eval_sstar
#print axioms Operad.TConv.eval_sub
#print axioms Operad.BTree.OfArity.bl_inj
#print axioms Operad.BTree.OfArity.rr_ne_rl
#print axioms Operad.TConv.eval_gbracket12
#print axioms Operad.TConv.mem_koszulDual_four_iff

/-! ## The symmetric associative operad -/

#print axioms Operad.Sym.instSetOperadLinOrd
#print axioms Operad.Sym.Ass.toCom
#print axioms Operad.Sym.Ass.toCom_single
#print axioms Operad.Sym.LinOrd.map_insertEquiv_comp_std
#print axioms Operad.Sym.Ass.ofNS

/-! ## Morphisms and brackets; twisting on a Koszul dual; mirror images of trees -/

#print axioms Operad.NSOperadHom.app_sstar
#print axioms Operad.NSOperadHom.app_gbracket
#print axioms Operad.TConv.projHom_app_eq_iff
#print axioms Operad.TConv.eval_gbracket_congr
#print axioms Operad.TConv.eval_gbracket_gbracket_eq_zero
#print axioms Operad.BTree.arity_mirror
#print axioms Operad.BTree.mirror_mirror
#print axioms Operad.BTree.OfArity.mirrorEquiv
#print axioms Operad.BTree.OfArity.mirror_bl
