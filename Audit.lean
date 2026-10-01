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

/-! ## Quotients of symmetric operads -/

#print axioms Operad.SymOperadIdeal.instSymOperad
#print axioms Operad.SymOperadIdeal.projHom
#print axioms Operad.SymOperadIdeal.mem_ker_projHom
#print axioms Operad.SymOperadIdeal.liftHom
#print axioms Operad.SymOperadIdeal.liftHom_unique
#print axioms Operad.SymOperadHom.kerLift_injective
#print axioms Operad.SymOperadHom.kerLift_bijective

/-! ## Hadamard products of set operads; dialgebras and trialgebras -/

#print axioms Operad.Hadamard.instSetOperad
#print axioms Operad.Hadamard.lift
#print axioms Operad.Hadamard.lift_unique
#print axioms Operad.Hadamard.prodMap_injective
#print axioms Operad.Hadamard.commIso
#print axioms Operad.PointedSet.instSetOperad
#print axioms Operad.NonemptySubset.instSetOperad
#print axioms Operad.Sym.LinOrd.equivRank
#print axioms Operad.Sym.LinOrd.card
#print axioms Operad.Sym.LinOrd.nestL_std
#print axioms Operad.Sym.Ass.finrank
#print axioms Operad.PointedSet.linPermIso
#print axioms Operad.PointedSet.toNonemptySubset_injective
#print axioms Operad.NonemptySubset.card
#print axioms Operad.DiasSet.relations
#print axioms Operad.DiasSet.card
#print axioms Operad.Dias.finrank
#print axioms Operad.TriasSet.relations
#print axioms Operad.TriasSet.card
#print axioms Operad.Trias.finrank
#print axioms Operad.TriasSet.toTrias_left
#print axioms Operad.TriasSet.toTrias_right
#print axioms Operad.Dias.toTrias_injective

/-! ## Generated ideals; operads presented by relators -/

#print axioms Operad.SymOperadIdeal.sInf
#print axioms Operad.SymOperadIdeal.span
#print axioms Operad.SymOperadIdeal.subset_span
#print axioms Operad.SymOperadIdeal.span_le
#print axioms Operad.SymOperadIdeal.span_le_ker_iff
#print axioms Operad.SymOperadIdeal.presHomEquiv
#print axioms Operad.presLinHomEquiv

/-! ## Symmetric cochains on binary trees; twisting; coefficients in an ideal -/

#print axioms Operad.BTree.graft_cutAt_subAt
#print axioms Operad.BTree.leafPath_graft
#print axioms Operad.BTree.eq_of_posAt_eq
#print axioms Operad.BTree.swapAt_swapAt
#print axioms Operad.BTree.mem_paths_swapAt
#print axioms Operad.BTree.swapAt_cut_of_not_prefix
#print axioms Operad.BTree.swapAt_cut_of_prefix
#print axioms Operad.BTree.swapPos_cut_of_not_prefix
#print axioms Operad.BTree.swapPos_cut_of_prefix
#print axioms Operad.BTree.splitAt_cut_of_not_prefix
#print axioms Operad.BTree.splitAt_cut_of_prefix
#print axioms Operad.SymOperad.compFin_toNS
#print axioms Operad.SymOperad.map_comp_map_left
#print axioms Operad.SymOperad.map_comp_map_right
#print axioms Operad.TConv.sstar_apply_paths
#print axioms Operad.TConv.pathTerm_swap
#print axioms Operad.TConv.isSymm_sstar
#print axioms Operad.TConv.isSymm_gbracket
#print axioms Operad.TConv.isSymm_two_iff
#print axioms Operad.TConv.symmCochains
#print axioms Operad.brT_brT_eq
#print axioms Operad.gbracket_gbracket_eq
#print axioms Operad.OperadIdeal.sstar_mem_left
#print axioms Operad.OperadIdeal.sstar_mem_right
#print axioms Operad.OperadIdeal.gbracket_mem_left
#print axioms Operad.OperadIdeal.gbracket_mem_right
#print axioms Operad.SymOperadIdeal.toNS
#print axioms Operad.LTree.window_left_shape
#print axioms Operad.LTree.window_right_eq
#print axioms Operad.LTree.isRightCombShape_of_normal
#print axioms Operad.LTree.labels_sorted_of_rightCombShape
#print axioms Operad.LTree.eq_rightComb_of_rightCombShape
#print axioms Operad.LTree.windows_rightComb
#print axioms Operad.LTree.isNormal_iff
#print axioms Operad.LTree.labels_graft
#print axioms Operad.LTree.isShuffle_graft
#print axioms Operad.LTree.prune_graft
#print axioms Operad.LTree.graft_inj
#print axioms Operad.LTree.exists_graft
#print axioms Operad.LTree.mem_monomials
#print axioms Operad.LTree.card_monomials
#print axioms Operad.IsLeadingOf.unique
#print axioms Operad.isLeading_fiberKer_iff
#print axioms Operad.Sym.LinOrd.rank_map
#print axioms Operad.Sym.LinOrd.rank_comp_inr
#print axioms Operad.Sym.LinOrd.rank_comp_inl_of_lt
#print axioms Operad.Sym.LinOrd.rank_comp_inl_of_gt
#print axioms Operad.SetOperadHom.toNSSet
#print axioms Operad.Reg.instSetOperad
#print axioms Operad.Reg.eta
#print axioms Operad.Reg.eq_map_std
#print axioms Operad.Reg.place_comp
#print axioms Operad.Reg.lift
#print axioms Operad.Reg.lift_std
#print axioms Operad.Reg.hom_ext
#print axioms Operad.Reg.homEquiv
#print axioms Operad.Reg.hadamardIso
#print axioms Operad.SetOperadIso.ofBijective
#print axioms Operad.SetOperadIso.trans
#print axioms Operad.SetOperadIso.precompEquiv
#print axioms Operad.Reg.mapIso
#print axioms Operad.NSSyn.eval_toSyn
#print axioms Operad.respects_symRel_iff
#print axioms Operad.Reg.presIso
#print axioms Operad.DiasData.rotClosed
#print axioms Operad.DiasData.rcomb_norm
#print axioms Operad.PDias.norm_eq_of_ptOf_eq
#print axioms Operad.PDias.ev_bijective
#print axioms Operad.PDias.presIso
#print axioms Operad.DiasData.equivRespects
#print axioms Operad.DiasSet.presIso
#print axioms Operad.Dias.homEquiv
#print axioms Operad.TriasData.rotClosed
#print axioms Operad.TriasData.rcomb_norm
#print axioms Operad.PTrias.norm_eq_of_marks_eq
#print axioms Operad.PTrias.marks_ofMarks
#print axioms Operad.PTrias.ev_bijective
#print axioms Operad.PTrias.presIso
#print axioms Operad.TriasData.equivRespects
#print axioms Operad.TriasSet.presIso
#print axioms Operad.Trias.homEquiv
#print axioms Operad.PermElt.nu_nu_comm
#print axioms Operad.PermElt.adj_perm
#print axioms Operad.PermElt.adjN_eq
#print axioms Operad.PermElt.adjN_adjN
#print axioms Operad.PermElt.comp_inl_adjN
#print axioms Operad.PermElt.bin_nu_adjN
#print axioms Operad.PermElt.app_adjN
#print axioms Operad.PermElt.psi_eq
#print axioms Operad.PermElt.psi_map
#print axioms Operad.PermElt.psi_comp
#print axioms Operad.PermElt.lift
#print axioms Operad.PointedSet.permElt_psi
#print axioms Operad.PointedSet.hom_ext
#print axioms Operad.PointedSet.homEquiv
#print axioms Operad.SymOperadIso.precompEquiv
#print axioms Operad.Perm.homEquiv
#print axioms Operad.PAss.eq_rcomb
#print axioms Operad.PAss.presIso
#print axioms Operad.AssSet.presIso
#print axioms Operad.Ass.homEquiv
#print axioms Operad.EndOp.ap_bin
#print axioms Operad.EndOp.isComm_iff
#print axioms Operad.EndOp.isAssoc_iff
#print axioms Operad.EndOp.r2b_iff
#print axioms Operad.EndOp.leftComb_eq_rightComb_iff
#print axioms Operad.Com.algebraEquiv
#print axioms Operad.Perm.algebraEquiv
#print axioms Operad.Ass.algebraEquiv
#print axioms Operad.Dias.algebraEquiv
#print axioms Operad.Trias.algebraEquiv
#print axioms Operad.ComTriasData.psi_eq
#print axioms Operad.ComTriasData.psi_comp
#print axioms Operad.ComTriasData.bin_left_psi
#print axioms Operad.ComTriasData.lift
#print axioms Operad.NonemptySubset.data_psi
#print axioms Operad.NonemptySubset.hom_ext
#print axioms Operad.NonemptySubset.homEquiv
#print axioms Operad.NonemptySubset.presIso
#print axioms Operad.ComTrias.homEquiv
#print axioms Operad.EndOp.assocShape_iff
#print axioms Operad.EndOp.rightShape_iff
#print axioms Operad.ComTrias.algebraEquiv
#print axioms Operad.forall_rel23
#print axioms Operad.freeBinEquiv
#print axioms Operad.binHom_single
#print axioms Operad.binHom_bin2
#print axioms Operad.binHom_binL
#print axioms Operad.binHom_binR
#print axioms Operad.endOp_eq_zero_iff₂
#print axioms Operad.endOp_eq_zero_iff₃
#print axioms Operad.BinPres.algebraEquiv
#print axioms Operad.BinRel.comm_iff
#print axioms Operad.BinRel.antisymm_iff
#print axioms Operad.BinRel.assoc_iff
#print axioms Operad.BinRel.jacobi_iff
#print axioms Operad.BinRel.preLie_iff
#print axioms Operad.BinRel.leib_iff
#print axioms Operad.BinRel.zinb_iff
#print axioms Operad.BinRel.leibnizRule_iff
#print axioms Operad.BinRel.dend₁_iff
#print axioms Operad.BinRel.dend₂_iff
#print axioms Operad.BinRel.dend₃_iff
#print axioms Operad.Lie.algebraEquiv
#print axioms Operad.PreLie.algebraEquiv
#print axioms Operad.Leib.algebraEquiv
#print axioms Operad.Zinb.algebraEquiv
#print axioms Operad.Dend.algebraEquiv
#print axioms Operad.Pois.algebraEquiv
#print axioms Operad.exists_reduction
#print axioms Operad.isLeading_iff_of_supportedOn
#print axioms Operad.isCompl_supportedOn
#print axioms Operad.LTree.map_range_lt_iff
#print axioms Operad.LTree.flatten_lt_flatten_iff
#print axioms Operad.LTree.labels_replaceAt_perm
#print axioms Operad.LTree.path_of_mem_subtreeAt
#print axioms Operad.LTree.path_replaceAt_of_mem
#print axioms Operad.LTree.path_replaceAt_of_not_mem
#print axioms Operad.LTree.path_plug
#print axioms Operad.LTree.mem_windows_iff
#print axioms Operad.LTree.winSpec
#print axioms Operad.LTree.substAt_windowAt
#print axioms Operad.LTree.perm_labels_substAt
#print axioms Operad.LTree.isShuffle_substAt
#print axioms Operad.LTree.path_substAt_of_mem
#print axioms Operad.LTree.path_substAt_of_not_mem
#print axioms Operad.LTree.pathKey_lt_iff
#print axioms Operad.LTree.pathKey_substAt_lt
#print axioms Operad.LTree.substAt_mem_monomials
#print axioms Operad.LTree.not_isNormal_iff
#print axioms Operad.LTree.pathKey_substAt_lt'
#print axioms Operad.BTree.OfArity.instNSSetOperad
#print axioms Operad.BTree.OfArity.toArr_node
#print axioms Operad.BTree.evalArr_graft
#print axioms Operad.BTree.OfArity.lift
#print axioms Operad.BTree.OfArity.lift_corolla
#print axioms Operad.BTree.OfArity.hom_ext
#print axioms Operad.BTree.OfArity.homEquiv
#print axioms Operad.FreeBin.regHom_ext
#print axioms Operad.FreeBin.regIso
#print axioms Operad.FreeBin.basis
#print axioms Operad.FreeBin.basis_apply
#print axioms Operad.FreeBin.card_reg
#print axioms Operad.FreeBin.finrank_eq
#print axioms Operad.BinRel.perm_iff
#print axioms Operad.BinRel.dias₁_iff
#print axioms Operad.BinRel.dias₅_iff
#print axioms Operad.BinAss.algebraEquiv
#print axioms Operad.BinPerm.algebraEquiv
#print axioms Operad.BinDias.algebraEquiv
#print axioms Operad.FreeBin.mono3_independent
#print axioms Operad.FreeBin.basis3
#print axioms Operad.FreeBin.span_sub_three
#print axioms Operad.FreeBin.span_eq_of_span_orbit3_eq
#print axioms Operad.FreeBin.pair3_nondegenerate
#print axioms Operad.FreeBin.pair3_map
#print axioms Operad.FreeBin.dualRel_dualRel
#print axioms Operad.FreeBin.finrank_dualRel
#print axioms Operad.FreeBin.dual_dual
#print axioms Operad.FreeBin.dualRel_eq_of_orthogonal
#print axioms Operad.FreeBin.le_finrank_of_private
#print axioms Operad.FreeBin.BinPres.dual_eq
#print axioms Operad.FreeBin.dualRel_assoc
#print axioms Operad.FreeBin.dualRel_leib_zinb
#print axioms Operad.FreeBin.dualRel_preLie_perm
#print axioms Operad.FreeBin.dualRel_dend_dias
#print axioms Operad.BinAss.dual
#print axioms Operad.PreLie.dual
#print axioms Operad.BinPerm.dual
#print axioms Operad.Leib.dual
#print axioms Operad.Zinb.dual
#print axioms Operad.Dend.dual
#print axioms Operad.BinDias.dual
#print axioms Operad.SymCochain.isCocycle_zero
#print axioms Operad.SymCochain.IsCocycle.add_smul
#print axioms Operad.Deformed.instSymOperad
#print axioms Operad.Deformed.isCocycle_of_symOperad
#print axioms Operad.SymEndo.isCocycle_coboundary
#print axioms Operad.isCoboundary_iff_exists_lift
#print axioms Operad.SymDerivation.liftEquiv
#print axioms Operad.SymDerivation.ad_one
#print axioms Operad.SymDerivation.smul_euler_eq_ad
#print axioms Operad.SymOperadIso.forall_isCoboundary
#print axioms Operad.SymOperadIso.forall_eq_smul_euler
#print axioms Operad.LTree.substAt_relabel
#print axioms Operad.LTree.std_substAt
#print axioms Operad.LTree.IsGroebner.isLeading
#print axioms Operad.LTree.IsGroebner.isCompl
#print axioms Operad.LTree.IsGroebner.nf_of_isNormal
#print axioms Operad.LTree.IsGroebner.sum_nf_substAt
#print axioms Operad.LTree.IsGroebner.mem_support_nf
#print axioms Operad.ShuffleBar.cutKeys_mergeK
#print axioms Operad.ShuffleBar.mergeK_comm
#print axioms Operad.ShuffleBar.d_dTree
#print axioms Operad.ShuffleBar.cutKeys_substBar
#print axioms Operad.ShuffleBar.mergeK_substBar
#print axioms Operad.ShuffleBar.d_substRel
#print axioms Operad.ShuffleBar.d_mem_J
#print axioms Operad.LTree.card_edgeKeys
#print axioms Operad.ShuffleBar.mergeK_cutK
#print axioms Operad.ShuffleBar.cutK_mergeK
#print axioms Operad.ShuffleBar.mergeK_cutK_comm
#print axioms Operad.ShuffleBar.d₀_hTree_add
#print axioms Operad.ShuffleBar.plug_top
#print axioms Operad.ShuffleBar.top_hang_substBar
#print axioms Operad.ShuffleBar.isNormal_top
#print axioms Operad.ShuffleBar.Φ_of_normal
#print axioms Operad.ShuffleBar.Φ_substRel
#print axioms Operad.ShuffleBar.reduce
#print axioms Operad.ShuffleBar.ΦL_spec
#print axioms Operad.ShuffleBar.ΦL_dTree_sub
#print axioms Operad.ShuffleBar.acyclic
#print axioms Operad.ShuffleBar.isKoszul
#print axioms Operad.LTree.zipDec_mapDec
#print axioms Operad.ShuffleBar.mem_barTrees
#print axioms Operad.ShuffleBar.finite_adm
#print axioms Operad.ShuffleBar.finite_nrm
#print axioms Operad.ShuffleBar.adm_top_normal
#print axioms Operad.ShuffleBar.finrank_supported
#print axioms Operad.ShuffleBar.finrank_eq_map_add
#print axioms Operad.ShuffleBar.euler
#print axioms Operad.ShuffleBar.KD_of_lt_two
#print axioms Operad.ShuffleBar.mem_J_iff
#print axioms Operad.ShuffleBar.normalized_eq
#print axioms Operad.ShuffleBar.normalized_injective
#print axioms Operad.ShuffleBar.dN_mem
#print axioms Operad.ShuffleBar.dN_dN
#print axioms Operad.ShuffleBar.exact_dN
#print axioms Operad.ShuffleBar.KD_eq
#print axioms Operad.ShuffleBar.finrank_KD
#print axioms Operad.ShuffleBar.finrank_KD_eq
#print axioms Operad.ShuffleBar.full_flagBy
#print axioms Operad.ShuffleBar.cutKeys_flagBy
#print axioms Operad.ShuffleBar.rootFlag_flagBy
#print axioms Operad.ShuffleBar.flagBy_cutKeys
#print axioms Operad.ShuffleBar.nodup_edgeWins_keys
#print axioms Operad.ShuffleBar.ncard_nrm
#print axioms Operad.ShuffleBar.sum_good_sets
#print axioms Operad.ShuffleBar.sum_ncard_nrm
#print axioms Operad.ShuffleBar.finrank_KD_eq_ncard
#print axioms Operad.LTree.joinAt_mem
#print axioms Operad.LTree.eq_joinAt
#print axioms Operad.LTree.joinAt_injective
#print axioms Operad.LTree.rootP_joinAt
#print axioms Operad.LTree.card_sets_zero
#print axioms Operad.LTree.card_filter_rootP
#print axioms Operad.ShuffleBar.edgeWins_map_snd
#print axioms Operad.ShuffleBar.isFull_iff_windows
#print axioms Operad.ShuffleBar.isFull_std
#print axioms Operad.SetOperad.comp_prod_of_nonempty
#print axioms Operad.SetOperad.comp_prod_of_isEmpty
#print axioms Operad.SetOperad.prod_of_unique
#print axioms Operad.und_map_zero
#print axioms Operad.und_comp_zero_left
#print axioms Operad.und_comp_zero_right
#print axioms Operad.und_bin_zero_left
#print axioms Operad.und_bin_zero_mid
#print axioms Operad.PermElt.adj_und_zero
#print axioms Operad.PermElt.adjN_und_zero
#print axioms Operad.twLin_bin_single
#print axioms Operad.gr_bin_single
#print axioms Operad.presLin_hom_ext
#print axioms Operad.FreeBin.span_sub_three_23
#print axioms Operad.FreeBin.span_le_23
#print axioms Operad.FreeBin.mono2_independent
#print axioms Operad.FreeBin.mono2Set_bijective
#print axioms Operad.FreeBin.basis2
#print axioms Operad.FreeBin.twist2_bin2
#print axioms Operad.FreeBin.evalW_injective
#print axioms Operad.FreeBin.comp_e0_bin2
#print axioms Operad.FreeBin.comp_e1_bin2
#print axioms Operad.FreeBin.ideal3Of_le
#print axioms Operad.FreeBin.dualRel23_empty
#print axioms Operad.FreeBin.BinPres.dual23_empty
#print axioms Operad.FreeBin.pair3_asym3
#print axioms Operad.FreeBin.sumCoord_eq_zero
#print axioms Operad.FreeBin.finrank_comRel3
#print axioms Operad.FreeBin.dualRel23_com
#print axioms Operad.FreeBin.asym3_eq
#print axioms Operad.FreeBin.BinPres.dual23_com_eq
#print axioms Operad.FreeBin.BinCom.dual
#print axioms Operad.FreeBin.comRel3_eq_ker
#print axioms Operad.FreeBin.uDiff_mem_dualRel
#print axioms Operad.FreeBin.dualRel_lie_le
#print axioms Operad.FreeBin.four_assoc
#print axioms Operad.FreeBin.BinPres.dual23_lie_eq
#print axioms Operad.FreeBin.Lie.dual
#print axioms Operad.Pres.lin_hom_ext
#print axioms Operad.SymDerivationAlong.app_one
#print axioms Operad.SymDerivation.compHom
#print axioms Operad.SymDerivationAlong.ofLifts
#print axioms Operad.Deformed.liftAdd
#print axioms Operad.SymDerivationAlong.liftEquiv
#print axioms Operad.FreeSet.linHom_gen
#print axioms Operad.SymDerivationAlong.freeEquiv
#print axioms Operad.SymDerivationAlong.freeEquiv_symm_gen
#print axioms Operad.SymDerivationAlong.free_ext
#print axioms Operad.Deformed.fst_freeLift
#print axioms Operad.Deformed.snd_freeLift_gen
