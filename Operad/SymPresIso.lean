/-
# The step-3 presentations of `Com`, `Lie`, `Ass` and `Pois` are the library's operads

`Operad.SymPresIdent` identifies the algebras over the graded presentations
`Koszul.Pres K E r` of step 3 of the bridge between symmetric and shuffle operads
(`Operad.SymPresComLie`, `Operad.SymPresAss`, `Operad.SymPresPois`) with the algebras over the
ungraded binary quadratic operads `BinCom`, `Lie`, `BinAss` and `Pois` (`Operad.BinaryQuadratic`,
`Operad.BinaryKoszulSym`). This file upgrades the identification to **isomorphisms of graded
operads** `Koszul.Pres K E r ≅ SymGr (BinPres …)` (`GrOperadIso`), generators to generators,
over a field `K`, through `SymPresIso.iso` (`Operad.SymPresIsoGen`). Each relator is tested on a
free algebra, where the algebra-level identification applies; no normal forms and no dictionary
between the monomials of `FreeBin` and the tree basis of `FreeGrL` are used.

`SymPresIso.genP r v` is the class in `Koszul.Pres K E r` of a generator `v`, and
`SymPresIso.genQ r₂ r₃ g` the class in `BinPres K r₂ r₃` of the binary generator `g`.

* **`Ass`**, any field: **`SymPresIso.assIso : GrOperadIso K (Koszul.Pres K (SymPresAss.E K)
  (SymPresAss.rel K)) (SymGr (BinAss K))`**, the product `x₁x₂` to the product and the opposite
  product `x₂x₁` to its transpose (`SymPresIso.assIso_hom_mu`, `SymPresIso.assIso_hom_op`,
  `SymPresIso.assIso_inv_gen`).
* **`Com`**, characteristic zero: **`SymPresIso.comIso : GrOperadIso K (Koszul.Pres K (ECom K)
  (rCom K)) (SymGr (FreeBin.BinCom K))`**, the product to the product
  (`SymPresIso.comIso_hom_gen`, `SymPresIso.comIso_inv_gen`).
* **`Lie`**, characteristic zero: **`SymPresIso.lieIso : GrOperadIso K (Koszul.Pres K (ELie K)
  (rLie K)) (SymGr (Lie K))`**, the bracket to the bracket (`SymPresIso.lieIso_hom_gen`,
  `SymPresIso.lieIso_inv_gen`).
* **`Pois`**, characteristic zero: **`SymPresIso.poisIso : GrOperadIso K (Koszul.Pres K
  (SymPresPois.E K) (SymPresPois.rel K)) (SymGr (Pois K))`**, the product to the product and the
  bracket to the bracket (`SymPresIso.poisIso_hom_mul`, `SymPresIso.poisIso_hom_br`,
  `SymPresIso.poisIso_inv_mul`, `SymPresIso.poisIso_inv_br`).

Characteristic zero enters for `Com` and `Lie` through the symmetrization of a product on the
one-dimensional representations of `𝔖₂` (`2` invertible would do), as in `Operad.SymPresIdent`,
and for `Pois` already in the definition of its presentation; `Ass` needs no hypothesis. The
arity-wise linear equivalences are `(SymPresIso.assIso K).linearEquiv A`, and so on.
-/
import Operad.SymPresIsoGen

universe u

namespace Operad

open Sym SymPresB

namespace SymPresIso

/-! ## `Ass` -/

section Ass

open SymPresAss AssShGen SymPresIdent

variable (K : Type u) [Field K]

/-- The product of `BinAss`. -/
noncomputable abbrev assGen : BinAss K (Fin 2) := genQ ∅ {BinRel.assoc K ()} ()

/-- The generator map of `Ass`: the identity numbering to the product. -/
noncomputable def assF : GrSpeciesHom K (Reg2 K) (SymGr (BinAss K)) :=
  regHom (assGen K)

lemma ass_hF (V : Type (max u 1)) [AddCommGroup V] [Module K V]
    (α : SymAlgebra K (BinAss K) V) :
    ∃ δ : PresAlg K (E K) (rel K) V, ∀ (A : Type) [Fintype A] [DecidableEq A] (v : Reg2 K A),
      δ.app A (genP (rel K) v) = α.app A ((assF K).app A v) :=
  ⟨(assEquiv K V).symm α, fun _ _ _ v =>
    (FreeGrL.homEquiv_symm_ι (modelHom (bil (BinAss.algebraEquiv α).mul)) v).trans
      (app_regApp α (assGen K) v).symm⟩

lemma ass_hq (V : Type u) [AddCommGroup V] [Module K V] (δ : PresAlg K (E K) (rel K) V) :
    ∃ γ : SymAlgebra K (BinAss K) V, ∀ g : Unit,
      γ.app (Fin 2) (genQ ∅ {BinRel.assoc K ()} g)
        = δ.app (Fin 2) (genP (rel K) (c K 2 (.op mu))) :=
  ⟨assEquiv K V δ, fun _ => congrArg AssAlg.mul
    ((BinAss.algebraEquiv (R := K) (V := V)).apply_symm_apply (assAlgEquiv K V δ))⟩

lemma assF_mu : (assF K).app (Fin 2) (c K 2 (.op mu)) = assGen K := by
  show regApp _ (Fin 2) _ = _
  rw [regApp_two, val_c, val_c]
  simp [genEquiv]

lemma assF_op : (assF K).app (Fin 2) (c K 2 (.op op))
    = SymOperad.map (R := K) (Equiv.swap (0 : Fin 2) 1) (assGen K) := by
  have hne : Equiv.refl (Fin 2) ≠ Equiv.swap 0 1 := by decide
  show regApp _ (Fin 2) _ = _
  rw [regApp_two, val_c, val_c]
  simp [genEquiv, hne]

lemma ass_h₂ (g : AssShGen 2) :
    ((ofBin isEven_reg2 (fun _ : Unit => c K 2 (.op mu)) (ass_hq K)).app (Fin 2)
      ((assF K).app (Fin 2) (c K 2 (.op g)))).val = genP (rel K) (c K 2 (.op g)) := by
  cases g
  · exact (congrArg (fun x => ((ofBin isEven_reg2 (fun _ : Unit => c K 2 (.op mu))
      (ass_hq K)).app (Fin 2) x).val) (assF_mu K)).trans
        (ofBin_gen isEven_reg2 (fun _ : Unit => c K 2 (.op mu)) (ass_hq K) ())
  · refine (congrArg (fun x => ((ofBin isEven_reg2 (fun _ : Unit => c K 2 (.op mu))
      (ass_hq K)).app (Fin 2) x).val) (assF_op K)).trans ?_
    refine (congrArg GrOperad.EvenOp.val ((ofBin isEven_reg2 (fun _ : Unit => c K 2 (.op mu))
      (ass_hq K)).app_map (Equiv.swap (0 : Fin 2) 1) (assGen K))).trans ?_
    exact (congrArg (GrOperad.map (R := K) (Equiv.swap (0 : Fin 2) 1))
      (ofBin_gen isEven_reg2 (fun _ : Unit => c K 2 (.op mu)) (ass_hq K) ())).trans
      ((genP_map (rel K) _ _).symm.trans
        (congrArg (genP (rel K)) (map_swap_c_mu.trans (one_smul K _))))

/-- **The step-3 presentation of `Ass` is the binary quadratic operad `BinAss`**, as graded
operads, over any field. -/
noncomputable def assIso : GrOperadIso K (Koszul.Pres K (E K) (rel K)) (SymGr (BinAss K)) :=
  iso isEven_reg2 (c K) (assF K) (ass_hF K) (fun _ => c K 2 (.op mu)) (ass_hq K)
    (fun _ => assF_mu K) (ass_h₂ K)

/-- The product `x₁x₂` goes to the product. -/
theorem assIso_hom_mu :
    (assIso K).hom.app (Fin 2) (genP (rel K) (c K 2 (.op mu))) = assGen K :=
  (toBin_gen (assF K) (ass_hF K) _).trans (assF_mu K)

/-- The opposite product `x₂x₁` goes to the transposed product. -/
theorem assIso_hom_op : (assIso K).hom.app (Fin 2) (genP (rel K) (c K 2 (.op op)))
    = SymOperad.map (R := K) (Equiv.swap (0 : Fin 2) 1) (assGen K) :=
  (toBin_gen (assF K) (ass_hF K) _).trans (assF_op K)

/-- The product goes back to the product `x₁x₂`. -/
theorem assIso_inv_gen :
    (assIso K).inv.app (Fin 2) (assGen K) = genP (rel K) (c K 2 (.op mu)) :=
  ofBin_gen isEven_reg2 (fun _ : Unit => c K 2 (.op mu)) (ass_hq K) ()

end Ass

/-! ## `Com` -/

section Com

open SymPresComLie SymPresIdent

variable (K : Type u) [Field K] [CharZero K]

/-- The product of `BinCom`. -/
noncomputable abbrev comGen : FreeBin.BinCom K (Fin 2) :=
  genQ {BinRel.comm K ()} {BinRel.assoc K ()} ()

/-- The generator map of `Com`: the halved product on the trivial representation. -/
noncomputable def comF : GrSpeciesHom K (ECom K) (SymGr (FreeBin.BinCom K)) :=
  binSpHom _ ((2 : K)⁻¹ • comGen K)

lemma com_hF (V : Type (max u 1)) [AddCommGroup V] [Module K V]
    (α : SymAlgebra K (FreeBin.BinCom K) V) :
    ∃ δ : PresAlg K (ECom K) (rCom K) V, ∀ (A : Type) [Fintype A] [DecidableEq A]
      (v : ECom K A), δ.app A (genP (rCom K) v) = α.app A ((comF K).app A v) := by
  have hm : bil (α.app (Fin 2) ((2 : K)⁻¹ • comGen K))
      = (2 : K)⁻¹ • bil (FreeBin.BinCom.algebraEquiv α).mul := by
    rw [map_smul]
    rfl
  exact ⟨(comEquiv K V).symm α, fun A _ _ v =>
    (FreeGrL.homEquiv_symm_ι
      (modelBHom _ ((2 : K)⁻¹ • bil (FreeBin.BinCom.algebraEquiv α).mul)) v).trans
      ((congrArg (fun m => modelApp m A (toReg2 A v)) hm.symm).trans
        (app_regApp α ((2 : K)⁻¹ • comGen K) (toReg2 A v)).symm)⟩

lemma com_hq (V : Type u) [AddCommGroup V] [Module K V] (δ : PresAlg K (ECom K) (rCom K) V) :
    ∃ γ : SymAlgebra K (FreeBin.BinCom K) V, ∀ g : Unit,
      γ.app (Fin 2) (genQ {BinRel.comm K ()} {BinRel.assoc K ()} g)
        = δ.app (Fin 2) (genP (rCom K) (cCom K 2 (.op .mu))) :=
  ⟨comEquiv K V δ, fun _ => congrArg ComAlg.mul
    ((FreeBin.BinCom.algebraEquiv (R := K) (V := V)).apply_symm_apply (comAlgEquiv K V δ))⟩

omit [CharZero K] in
lemma map_swap_comGen :
    SymOperad.map (R := K) (Equiv.swap (0 : Fin 2) 1) (comGen K) = comGen K :=
  map_swap_genQ_comm rfl

lemma comF_gen (g : ComGen 2) : (comF K).app (Fin 2) (cCom K 2 (.op g)) = comGen K := by
  have e1 : (toReg2 (Fin 2) (cCom K 2 (.op g))).val (Equiv.refl _) = 1 := cCom_refl K g
  have e2 : (toReg2 (Fin 2) (cCom K 2 (.op g))).val (Equiv.swap 0 1) = 1 := cCom_swap K g
  show regApp _ (Fin 2) _ = _
  rw [regApp_two, e1, e2, one_smul, one_smul, map_smul, map_swap_comGen, ← add_smul,
    ← two_mul, mul_inv_cancel₀ two_ne_zero, one_smul]

lemma com_h₂ (g : ComGen 2) :
    ((ofBin (isEven_binSp _) (fun _ : Unit => cCom K 2 (.op .mu)) (com_hq K)).app (Fin 2)
      ((comF K).app (Fin 2) (cCom K 2 (.op g)))).val = genP (rCom K) (cCom K 2 (.op g)) := by
  cases g
  exact (congrArg (fun x => ((ofBin (isEven_binSp _) (fun _ : Unit => cCom K 2 (.op .mu))
    (com_hq K)).app (Fin 2) x).val) (comF_gen K .mu)).trans
      (ofBin_gen (isEven_binSp _) (fun _ : Unit => cCom K 2 (.op .mu)) (com_hq K) ())

/-- **The step-3 presentation of `Com` is the binary quadratic operad `BinCom`**, as graded
operads, over a field of characteristic zero. -/
noncomputable def comIso :
    GrOperadIso K (Koszul.Pres K (ECom K) (rCom K)) (SymGr (FreeBin.BinCom K)) :=
  iso (isEven_binSp _) (cCom K) (comF K) (com_hF K) (fun _ => cCom K 2 (.op .mu)) (com_hq K)
    (fun _ => comF_gen K .mu) (com_h₂ K)

/-- The product goes to the product. -/
theorem comIso_hom_gen :
    (comIso K).hom.app (Fin 2) (genP (rCom K) (cCom K 2 (.op .mu))) = comGen K :=
  (toBin_gen (comF K) (com_hF K) _).trans (comF_gen K .mu)

/-- The product goes back to the product. -/
theorem comIso_inv_gen :
    (comIso K).inv.app (Fin 2) (comGen K) = genP (rCom K) (cCom K 2 (.op .mu)) :=
  ofBin_gen (isEven_binSp _) (fun _ : Unit => cCom K 2 (.op .mu)) (com_hq K) ()

end Com

/-! ## `Lie` -/

section Lie

open SymPresComLie SymPresIdent

variable (K : Type u) [Field K] [CharZero K]

/-- The bracket of `Lie`. -/
noncomputable abbrev lieGen : Lie K (Fin 2) :=
  genQ {BinRel.antisymm K ()} {BinRel.jacobi K ()} ()

/-- The generator map of `Lie`: the halved bracket on the sign representation. -/
noncomputable def lieF : GrSpeciesHom K (ELie K) (SymGr (Lie K)) :=
  binSpHom _ ((2 : K)⁻¹ • lieGen K)

lemma lie_hF (V : Type (max u 1)) [AddCommGroup V] [Module K V]
    (α : SymAlgebra K (Lie K) V) :
    ∃ δ : PresAlg K (ELie K) (rLie K) V, ∀ (A : Type) [Fintype A] [DecidableEq A]
      (v : ELie K A), δ.app A (genP (rLie K) v) = α.app A ((lieF K).app A v) := by
  have hm : bil (α.app (Fin 2) ((2 : K)⁻¹ • lieGen K))
      = (2 : K)⁻¹ • bil (Lie.algebraEquiv α).bracket := by
    rw [map_smul]
    rfl
  exact ⟨(lieEquiv K V).symm α, fun A _ _ v =>
    (FreeGrL.homEquiv_symm_ι
      (modelBHom _ ((2 : K)⁻¹ • bil (Lie.algebraEquiv α).bracket)) v).trans
      ((congrArg (fun m => modelApp m A (toReg2 A v)) hm.symm).trans
        (app_regApp α ((2 : K)⁻¹ • lieGen K) (toReg2 A v)).symm)⟩

lemma lie_hq (V : Type u) [AddCommGroup V] [Module K V] (δ : PresAlg K (ELie K) (rLie K) V) :
    ∃ γ : SymAlgebra K (Lie K) V, ∀ g : Unit,
      γ.app (Fin 2) (genQ {BinRel.antisymm K ()} {BinRel.jacobi K ()} g)
        = δ.app (Fin 2) (genP (rLie K) (cLie K 2 (.op .mu))) :=
  ⟨lieEquiv K V δ, fun _ => congrArg LieAlg.bracket
    ((Lie.algebraEquiv (R := K) (V := V)).apply_symm_apply (lieAlgEquiv K V δ))⟩

omit [CharZero K] in
lemma map_swap_lieGen :
    SymOperad.map (R := K) (Equiv.swap (0 : Fin 2) 1) (lieGen K) = -lieGen K :=
  map_swap_genQ_antisymm rfl

lemma lieF_gen (g : ComGen 2) : (lieF K).app (Fin 2) (cLie K 2 (.op g)) = lieGen K := by
  have e1 : (toReg2 (Fin 2) (cLie K 2 (.op g))).val (Equiv.refl _) = 1 := cLie_refl K g
  have e2 : (toReg2 (Fin 2) (cLie K 2 (.op g))).val (Equiv.swap 0 1) = -1 := cLie_swap K g
  show regApp _ (Fin 2) _ = _
  rw [regApp_two, e1, e2, one_smul, neg_one_smul, map_smul, map_swap_lieGen, smul_neg,
    neg_neg, ← add_smul, ← two_mul, mul_inv_cancel₀ two_ne_zero, one_smul]

lemma lie_h₂ (g : ComGen 2) :
    ((ofBin (isEven_binSp _) (fun _ : Unit => cLie K 2 (.op .mu)) (lie_hq K)).app (Fin 2)
      ((lieF K).app (Fin 2) (cLie K 2 (.op g)))).val = genP (rLie K) (cLie K 2 (.op g)) := by
  cases g
  exact (congrArg (fun x => ((ofBin (isEven_binSp _) (fun _ : Unit => cLie K 2 (.op .mu))
    (lie_hq K)).app (Fin 2) x).val) (lieF_gen K .mu)).trans
      (ofBin_gen (isEven_binSp _) (fun _ : Unit => cLie K 2 (.op .mu)) (lie_hq K) ())

/-- **The step-3 presentation of `Lie` is the binary quadratic operad `Lie`**, as graded
operads, over a field of characteristic zero. -/
noncomputable def lieIso : GrOperadIso K (Koszul.Pres K (ELie K) (rLie K)) (SymGr (Lie K)) :=
  iso (isEven_binSp _) (cLie K) (lieF K) (lie_hF K) (fun _ => cLie K 2 (.op .mu)) (lie_hq K)
    (fun _ => lieF_gen K .mu) (lie_h₂ K)

/-- The bracket goes to the bracket. -/
theorem lieIso_hom_gen :
    (lieIso K).hom.app (Fin 2) (genP (rLie K) (cLie K 2 (.op .mu))) = lieGen K :=
  (toBin_gen (lieF K) (lie_hF K) _).trans (lieF_gen K .mu)

/-- The bracket goes back to the bracket. -/
theorem lieIso_inv_gen :
    (lieIso K).inv.app (Fin 2) (lieGen K) = genP (rLie K) (cLie K 2 (.op .mu)) :=
  ofBin_gen (isEven_binSp _) (fun _ : Unit => cLie K 2 (.op .mu)) (lie_hq K) ()

end Lie

/-! ## `Pois` -/

section Pois

open SymPresPois PoisShGen SymPresIdent

variable (K : Type u) [Field K] [CharZero K]

/-- The product and the bracket of `Pois`. -/
noncomputable abbrev poisGen (g : PoisOp) : Pois K (Fin 2) :=
  genQ {BinRel.comm K PoisOp.mul, BinRel.antisymm K PoisOp.bracket}
    {BinRel.assoc K PoisOp.mul, BinRel.jacobi K PoisOp.bracket,
      BinRel.leibnizRule K PoisOp.mul PoisOp.bracket} g

/-- The generator map of `Pois`: the identity numbering to the product plus the bracket. -/
noncomputable def poisF : GrSpeciesHom K (Reg2 K) (SymGr (Pois K)) :=
  regHom (poisGen K .mul + poisGen K .bracket)

/-- The vectors of the product and the bracket: the symmetric and the antisymmetric one. -/
noncomputable def poisQ : PoisOp → Reg2 K (Fin 2)
  | .mul => c K 2 (.op mul)
  | .bracket => c K 2 (.op br)

lemma pois_hF (V : Type (max u 1)) [AddCommGroup V] [Module K V]
    (α : SymAlgebra K (Pois K) V) :
    ∃ δ : PresAlg K (E K) (rel K) V, ∀ (A : Type) [Fintype A] [DecidableEq A] (v : Reg2 K A),
      δ.app A (genP (rel K) v) = α.app A ((poisF K).app A v) := by
  have hm : bil (α.app (Fin 2) (poisGen K .mul + poisGen K .bracket))
      = bil (Pois.algebraEquiv α).mul + bil (Pois.algebraEquiv α).bracket := by
    rw [map_add]
    rfl
  exact ⟨(poisEquiv K V).symm α, fun A _ _ v =>
    (FreeGrL.homEquiv_symm_ι (modelHom
      (bil (Pois.algebraEquiv α).mul + bil (Pois.algebraEquiv α).bracket)) v).trans
      ((congrArg (fun m => modelApp m A v) hm.symm).trans
        (app_regApp α (poisGen K .mul + poisGen K .bracket) v).symm)⟩

lemma pois_hq (V : Type u) [AddCommGroup V] [Module K V] (δ : PresAlg K (E K) (rel K) V) :
    ∃ γ : SymAlgebra K (Pois K) V, ∀ g : PoisOp,
      γ.app (Fin 2) (poisGen K g) = δ.app (Fin 2) (genP (rel K) (poisQ K g)) :=
  ⟨poisEquiv K V δ, fun g => by
    cases g
    · exact congrArg PoisAlg.mul
        ((Pois.algebraEquiv (R := K) (V := V)).apply_symm_apply (poisAlgEquiv K V δ))
    · exact congrArg PoisAlg.bracket
        ((Pois.algebraEquiv (R := K) (V := V)).apply_symm_apply (poisAlgEquiv K V δ))⟩

omit [CharZero K] in
lemma map_swap_poisGen_mul : SymOperad.map (R := K) (Equiv.swap (0 : Fin 2) 1)
    (poisGen K .mul) = poisGen K .mul :=
  map_swap_genQ_comm (Or.inl rfl)

omit [CharZero K] in
lemma map_swap_poisGen_br : SymOperad.map (R := K) (Equiv.swap (0 : Fin 2) 1)
    (poisGen K .bracket) = -poisGen K .bracket :=
  map_swap_genQ_antisymm (Or.inr rfl)

lemma poisF_mul : (poisF K).app (Fin 2) (c K 2 (.op mul)) = poisGen K .mul := by
  show regApp _ (Fin 2) (c K 2 (.op mul)) = _
  rw [regApp_two, val_c, val_c, symm_refl, symm_swap, map_add, map_swap_poisGen_mul,
    map_swap_poisGen_br]
  simp only [Pi.single_apply, reduceCtorEq, if_true, if_false]
  show ((1 + 0) / 2 : K) • (poisGen K .mul + poisGen K .bracket)
    + ((1 - 0) / 2 : K) • (poisGen K .mul + -poisGen K .bracket) = poisGen K .mul
  module

lemma poisF_br : (poisF K).app (Fin 2) (c K 2 (.op br)) = poisGen K .bracket := by
  show regApp _ (Fin 2) (c K 2 (.op br)) = _
  rw [regApp_two, val_c, val_c, symm_refl, symm_swap, map_add, map_swap_poisGen_mul,
    map_swap_poisGen_br]
  simp only [Pi.single_apply, reduceCtorEq, if_true, if_false]
  show ((0 + 1) / 2 : K) • (poisGen K .mul + poisGen K .bracket)
    + ((0 - 1) / 2 : K) • (poisGen K .mul + -poisGen K .bracket) = poisGen K .bracket
  module

lemma poisF_gen (g : PoisOp) : (poisF K).app (Fin 2) (poisQ K g) = poisGen K g := by
  cases g
  · exact poisF_mul K
  · exact poisF_br K

lemma pois_h₂ (g : PoisShGen 2) :
    ((ofBin isEven_reg2 (poisQ K) (pois_hq K)).app (Fin 2)
      ((poisF K).app (Fin 2) (c K 2 (.op g)))).val = genP (rel K) (c K 2 (.op g)) := by
  cases g
  · exact (congrArg (fun x => ((ofBin isEven_reg2 (poisQ K) (pois_hq K)).app (Fin 2) x).val)
      (poisF_mul K)).trans (ofBin_gen isEven_reg2 (poisQ K) (pois_hq K) .mul)
  · exact (congrArg (fun x => ((ofBin isEven_reg2 (poisQ K) (pois_hq K)).app (Fin 2) x).val)
      (poisF_br K)).trans (ofBin_gen isEven_reg2 (poisQ K) (pois_hq K) .bracket)

/-- **The step-3 presentation of `Pois` is the binary quadratic operad `Pois`**, as graded
operads, over a field of characteristic zero. -/
noncomputable def poisIso : GrOperadIso K (Koszul.Pres K (E K) (rel K)) (SymGr (Pois K)) :=
  iso isEven_reg2 (c K) (poisF K) (pois_hF K) (poisQ K) (pois_hq K) (poisF_gen K) (pois_h₂ K)

/-- The product goes to the product. -/
theorem poisIso_hom_mul :
    (poisIso K).hom.app (Fin 2) (genP (rel K) (c K 2 (.op mul))) = poisGen K .mul :=
  (toBin_gen (poisF K) (pois_hF K) _).trans (poisF_mul K)

/-- The bracket goes to the bracket. -/
theorem poisIso_hom_br :
    (poisIso K).hom.app (Fin 2) (genP (rel K) (c K 2 (.op br))) = poisGen K .bracket :=
  (toBin_gen (poisF K) (pois_hF K) _).trans (poisF_br K)

/-- The product goes back to the product. -/
theorem poisIso_inv_mul :
    (poisIso K).inv.app (Fin 2) (poisGen K .mul) = genP (rel K) (c K 2 (.op mul)) :=
  ofBin_gen isEven_reg2 (poisQ K) (pois_hq K) .mul

/-- The bracket goes back to the bracket. -/
theorem poisIso_inv_br :
    (poisIso K).inv.app (Fin 2) (poisGen K .bracket) = genP (rel K) (c K 2 (.op br)) :=
  ofBin_gen isEven_reg2 (poisQ K) (pois_hq K) .bracket

end Pois

end SymPresIso

end Operad
