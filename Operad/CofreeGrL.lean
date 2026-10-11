/-
# The cut cooperad of a free graded operad on a graded linear species

The free graded operad `FreeGrL R V` on a graded linear species is the quotient of the free graded
operad on the homogeneous elements of `V` by the ideal of its linearity relations. **This ideal is
a coideal** of the graded decomposition cooperad (`FreeGrL.linCoideal`), so `FreeGrL R V` is a
coaugmented graded cooperad (`FreeGrL.instGrCooperad`, `FreeGrL.instCoaug`), decomposing a tree with
vertices decorated by `V` by cutting it.

The proof substitutes into a marked vertex. Each relation is a combination of relabelled
generators `r = ∑ₖ λₖ σₖ·gₖ` (`RelComb`, `FreeGrL.exists_relComb`). On trees with one more
generator, the mark, consider the morphism `Φᵣ` substituting `r` for the mark, and the morphisms
`Φₖ` substituting `σₖ·gₖ` (`RelComb.subst`, `RelComb.term`). On a tree with one marked vertex,
`Φᵣ = ∑ₖ λₖ Φₖ`, and all of them agree on unmarked trees (`RelComb.subst_bas`). Each `Φₖ` sends
basis elements to signed basis elements along a relabelling of the vertices composed with an
automorphism relabelling the inputs of the mark (`relMarkIso`), bijective on factorizations, so
it is a morphism of decomposition cooperads (`RelComb.term_decomp`). In every cut of a tree with
one marked vertex, the mark lies in exactly one part; so the decomposition of `Φᵣ` of such a tree
lies in `I ⊗ C + C ⊗ I` (`RelComb.decomp_subst_mem`), and its counit vanishes
(`RelComb.counit_subst`). Finally, these substitutions span an ideal (`substIdeal`), since every
tree is a substitution into an unmarked tree (`RelComb.bas_eq_subst`), and it contains the
relations (`FreeGrL.span_le_substIdeal`).
-/
import Operad.GrSubst
import Operad.GrCoideal
import Operad.FreeGrSpecies

universe u v w

namespace Operad

open Sym GerBV TreeOfArity FreeGr FreeReg
open scoped TensorProduct

/-! ## Marked generators -/

/-- **A mark** of arity `n`. -/
inductive Mark (n : ℕ) : ℕ → Type
  | mk : Mark n n

variable {T : ℕ → Type v}

/-- The generators together with a mark of arity `n`. -/
abbrev MarkGen (T : ℕ → Type v) (n : ℕ) (k : ℕ) : Type v := T k ⊕ ULift.{v} (Mark n k)

namespace MarkGen

variable (n : ℕ)

/-- The mark, as a generator. -/
def mark : MarkGen T n n := .inr ⟨.mk⟩

variable (gp : ∀ k, T k → Bool) (b : Bool)

/-- The parities of the marked generators, the mark of parity `b`. -/
def par : ∀ k, MarkGen T n k → Bool
  | k, .inl g => gp k g
  | _, .inr _ => b

/-- The weight counting the marks. -/
def markW : ∀ k, MarkGen T n k → ℕ
  | _, .inl _ => 0
  | _, .inr _ => 1

/-- Unmarking: the mark becomes the generator `g`. -/
def unmark (g : T n) : ∀ k, MarkGen T n k → T k
  | _, .inl g' => g'
  | _, .inr ⟨.mk⟩ => g

lemma par_unmark {g : T n} (hg : gp n g = b) :
    ∀ k (e : MarkGen T n k), gp k (unmark n g k e) = par n gp b k e
  | _, .inl _ => rfl
  | _, .inr ⟨.mk⟩ => hg

/-- The values of relabelling the inputs of the mark along `σ`. -/
noncomputable def relVal (σ : Fin n ≃ Fin n) :
    ∀ k, MarkGen T n k → Reg (TreeOfArity (MarkGen T n)) (Fin k)
  | _, .inl g => Reg.std (corolla (.inl g))
  | _, .inr ⟨.mk⟩ => SetOperad.map σ (Reg.std (corolla (mark n)))

end MarkGen

open MarkGen

/-! ## Relabelling the inputs of the mark -/

section RelMark

variable (n : ℕ)

/-- **Relabelling the inputs of the mark**, an endomorphism of the regular operad of marked
trees. -/
noncomputable def relMark (σ : Fin n ≃ Fin n) :
    SetOperadHom (Reg (TreeOfArity (MarkGen T n))) (Reg (TreeOfArity (MarkGen T n))) :=
  Reg.lift (TreeOfArity.lift (S := SetOperad.toNSSet (Reg (TreeOfArity (MarkGen T n))))
    (relVal n σ))

lemma relMark_std (σ : Fin n ≃ Fin n) {k : ℕ} (e : MarkGen T n k) :
    (relMark n σ).app (Fin k) (Reg.std (corolla e)) = relVal n σ k e := by
  rw [relMark, Reg.lift_std]
  exact TreeOfArity.lift_corolla (S := SetOperad.toNSSet (Reg (TreeOfArity (MarkGen T n)))) _ e

/-- Relabelling the inputs of the mark twice. -/
lemma relMark_comp (σ τ : Fin n ≃ Fin n) :
    (relMark (T := T) n σ).comp (relMark n τ) = relMark n (σ.trans τ) :=
  regHom_ext fun k e => by
    show (relMark n σ).app _ ((relMark n τ).app _ (Reg.std (corolla e))) = _
    rw [relMark_std, relMark_std]
    match k, e with
    | _, .inl g =>
      show (relMark n σ).app _ (Reg.std (corolla (.inl g))) = Reg.std (corolla (.inl g))
      rw [relMark_std]
      rfl
    | _, .inr ⟨.mk⟩ =>
      show (relMark n σ).app _ (SetOperad.map τ (Reg.std (corolla (mark n))))
        = SetOperad.map (σ.trans τ) (Reg.std (corolla (mark n)))
      rw [(relMark n σ).app_map, mark, relMark_std]
      show SetOperad.map τ (SetOperad.map σ (Reg.std (corolla (mark n)))) = _
      rw [← SetOperad.map_trans]
      rfl

lemma relMark_refl : relMark (T := T) n (Equiv.refl (Fin n)) = SetOperadHom.id :=
  regHom_ext fun k e => by
    show (relMark n (Equiv.refl (Fin n))).app _ (Reg.std (corolla e)) = Reg.std (corolla e)
    rw [relMark_std]
    match k, e with
    | _, .inl g => rfl
    | _, .inr ⟨.mk⟩ => exact SetOperad.map_refl _

/-- **Relabelling the inputs of the mark is an automorphism.** -/
noncomputable def relMarkIso (σ : Fin n ≃ Fin n) :
    SetOperadIso (Reg (TreeOfArity (MarkGen T n))) (Reg (TreeOfArity (MarkGen T n))) where
  hom := relMark n σ
  inv := relMark n σ.symm
  hom_inv_id := by rw [relMark_comp, Equiv.symm_trans_self, relMark_refl]
  inv_hom_id := by rw [relMark_comp, Equiv.self_trans_symm, relMark_refl]

end RelMark

/-! ## Basis elements of composites -/

section Bas

variable {R : Type u} [CommRing R] {gp : ∀ k, T k → Bool}
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **A morphism on the basis element of a composite.** -/
lemma app_bas_comp (Φ : GrOperadHom R (FreeGr R gp) Q) (i : A) (x : Reg (TreeOfArity T) A)
    (y : Reg (TreeOfArity T) B) :
    Φ.app _ (SgnLin.bas (treeSgn gp) R (SetOperad.comp i x y))
      = σ R (SgnData.sgn i ((treeSgn gp).app A x) ((treeSgn gp).app B y)) •
          GrOperad.comp (R := R) i (Φ.app A (SgnLin.bas (treeSgn gp) R x))
            (Φ.app B (SgnLin.bas (treeSgn gp) R y)) := by
  rw [← Φ.app_comp, SgnLin.comp_bas, map_smul, smul_smul, σ_mul_self, one_smul]

lemma app_bas_map (Φ : GrOperadHom R (FreeGr R gp) Q) (e : A ≃ B) (x : Reg (TreeOfArity T) A) :
    Φ.app _ (SgnLin.bas (treeSgn gp) R (SetOperad.map e x))
      = GrOperad.map (R := R) e (Φ.app A (SgnLin.bas (treeSgn gp) R x)) := by
  rw [← SgnLin.map_bas, Φ.app_map]

lemma app_bas_one (Φ : GrOperadHom R (FreeGr R gp) Q) :
    Φ.app Unit (SgnLin.bas (treeSgn gp) R SetOperad.one) = GrOperad.one (R := R) :=
  Φ.app_one

end Bas

/-! ## Combinations of relabelled generators and substitutions -/

variable (R : Type u) [CommRing R] (gp : ∀ k, T k → Bool)

/-- **A combination of relabelled generators** of arity `n` and parity `b`: `∑ₖ λₖ σₖ·gₖ`. -/
structure RelComb (n : ℕ) (b : Bool) where
  /-- The number of terms. -/
  m : ℕ
  /-- The coefficients. -/
  coef : Fin m → R
  /-- The generators. -/
  gen : Fin m → T n
  /-- The relabellings. -/
  perm : Fin m → (Fin n ≃ Fin n)
  par_gen : ∀ k, gp n (gen k) = b

namespace RelComb

variable {R gp} {n : ℕ} {b : Bool} (c : RelComb R gp n b)

/-- **The value of a combination.** -/
noncomputable def val : FreeGr R gp (Fin n) :=
  ∑ k, c.coef k • GrOperad.map (R := R) (c.perm k) (FreeGr.gen (c.gen k))

lemma par_val : GrOperad.par (R := R) b c.val = c.val := by
  simp only [val, map_sum, map_smul, ← GrOperad.map_par]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := FreeGr.par_gen (R := R) (gp := gp) (c.gen k)
  rw [c.par_gen k] at h
  rw [h]

/-- The values of the substitution of the combination for the mark. -/
noncomputable def substVal : FreeGr.GenVal R (MarkGen.par n gp b) (FreeGr R gp) :=
  ⟨fun k e => match k, e with
      | _, .inl g => FreeGr.gen g
      | _, .inr ⟨.mk⟩ => c.val,
    fun k e => match k, e with
      | _, .inl g => FreeGr.par_gen g
      | _, .inr ⟨.mk⟩ => c.par_val⟩

/-- **The substitution of the combination for the mark.** -/
noncomputable def subst : GrOperadHom R (FreeGr R (MarkGen.par n gp b)) (FreeGr R gp) :=
  FreeGr.homEquiv.symm c.substVal

lemma subst_gen_inl {k : ℕ} (g : T k) :
    c.subst.app (Fin k) (FreeGr.gen (gp := MarkGen.par n gp b) (Sum.inl g : MarkGen T n k))
      = FreeGr.gen g :=
  FreeGr.homEquiv_symm_gen c.substVal (.inl g)

lemma subst_gen_mark : c.subst.app (Fin n) (FreeGr.gen (mark n)) = c.val :=
  FreeGr.homEquiv_symm_gen c.substVal (mark n)

/-- The signed basis values of the substitution of the `k`-th term for the mark. -/
noncomputable def termVal (k : Fin c.m) : SBVal (MarkGen.par n gp b) gp where
  sg _ _ := false
  tree := fun k' (e : MarkGen T n k') => match k', e with
    | _, .inl g => Reg.std (corolla g)
    | _, .inr ⟨.mk⟩ => SetOperad.map (c.perm k) (Reg.std (corolla (c.gen k)))
  tot_eq := fun k' (e : MarkGen T n k') => match k', e with
    | _, .inl g => treeSgn_tot g
    | _, .inr ⟨.mk⟩ => by
      show ((treeSgn gp).app _ (SetOperad.map (c.perm k) (Reg.std (corolla (c.gen k))))).tot = b
      rw [(treeSgn gp).app_map, SgnData.map_def, SgnData.map_tot, treeSgn_tot, c.par_gen]

variable (R) in
/-- **The substitution of the `k`-th relabelled generator for the mark.** -/
noncomputable def term (k : Fin c.m) :
    GrOperadHom R (FreeGr R (MarkGen.par n gp b)) (FreeGr R gp) :=
  (c.termVal k).hom R

lemma term_gen_inl (k : Fin c.m) {k' : ℕ} (g : T k') :
    (c.term R k).app (Fin k') (FreeGr.gen (gp := MarkGen.par n gp b) (Sum.inl g : MarkGen T n k'))
      = FreeGr.gen g := by
  rw [term, SBVal.hom_gen]
  show σ R false • _ = _
  rw [σ_false, one_smul]
  rfl

lemma term_gen_mark (k : Fin c.m) :
    (c.term R k).app (Fin n) (FreeGr.gen (mark n))
      = GrOperad.map (R := R) (c.perm k) (FreeGr.gen (c.gen k)) := by
  rw [term, SBVal.hom_gen]
  show σ R false • SgnLin.bas _ R (SetOperad.map (c.perm k) (Reg.std (corolla (c.gen k)))) = _
  rw [σ_false, one_smul, ← SgnLin.map_bas]
  rfl

/-- The underlying morphism of set operads of the `k`-th substitution: relabel the inputs of the
mark, then unmark. -/
lemma term_ψ (k : Fin c.m) :
    ((c.termVal k).sbm R).ψ
      = (relabel (MarkGen.unmark n (c.gen k))).comp (relMark n (c.perm k)) :=
  regHom_ext fun k' e => by
    rw [SBVal.sbm_ψ_std]
    show _ = relabelR _ ((relMark n (c.perm k)).app _ (Reg.std (corolla e)))
    rw [relMark_std]
    match k', e with
    | _, .inl g =>
      show Reg.std (corolla g) = relabelR (MarkGen.unmark n (c.gen k))
        (Reg.std (corolla (Sum.inl g : MarkGen T n _)))
      rw [← relabel_app, relabel_std]
      rfl
    | _, .inr ⟨.mk⟩ =>
      show SetOperad.map (c.perm k) (Reg.std (corolla (c.gen k)))
        = relabelR (MarkGen.unmark n (c.gen k))
          (SetOperad.map (c.perm k) (Reg.std (corolla (mark (T := T) n))))
      rw [← relabel_app, (relabel _).app_map, relabel_std]
      rfl

/-- **The substitutions of the terms are bijective on factorizations.** -/
theorem term_factBij (k : Fin c.m) : ((c.termVal k).sbm R).ψ.FactBij := by
  rw [term_ψ]
  exact SetOperadHom.FactBij.comp (SetOperadIso.factBij (relMarkIso n (c.perm k)))
    (relabel_factBij _)

/-- **The substitutions of the terms are morphisms of decomposition cooperads.** -/
theorem term_decomp (k : Fin c.m) {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (i : A) :
    SgnLin.decompT R (treeSgn gp) (B := B) i ∘ₗ (c.term R k).app (Without A i ⊕ B)
      = TensorProduct.map ((c.term R k).app A) ((c.term R k).app B) ∘ₗ
          SgnLin.decompT R (treeSgn (MarkGen.par n gp b)) i :=
  ((c.termVal k).sbm R).decomp_app (c.term_factBij k) i

/-! ### Substituting into trees with one marked vertex -/

/-- **All substitutions agree on unmarked trees, and on trees with one marked vertex the
substitution of the combination is the combination of the substitutions of its terms.** -/
theorem subst_bas {A : Type} [Fintype A] [DecidableEq A]
    (x : Reg (TreeOfArity (MarkGen T n)) A) :
    (cntR (markW n) x = 0 → ∀ k, (c.term R k).app A (SgnLin.bas _ R x)
        = c.subst.app A (SgnLin.bas _ R x)) ∧
      (cntR (markW n) x = 1 → c.subst.app A (SgnLin.bas _ R x)
        = ∑ k, c.coef k • (c.term R k).app A (SgnLin.bas _ R x)) := by
  refine FreeReg.induction (P := fun A _ _ x => (cntR (markW n) x = 0 → ∀ k,
      (c.term R k).app A (SgnLin.bas _ R x) = c.subst.app A (SgnLin.bas _ R x)) ∧
      (cntR (markW n) x = 1 → c.subst.app A (SgnLin.bas _ R x)
        = ∑ k, c.coef k • (c.term R k).app A (SgnLin.bas _ R x))) ?_ ?_ ?_ ?_ x
  · intro A B _ _ _ _ e x ⟨h0, h1⟩
    rw [cntR_map]
    refine ⟨fun hx k => ?_, fun hx => ?_⟩
    · rw [app_bas_map, app_bas_map, h0 hx k]
    · rw [app_bas_map, h1 hx, map_sum]
      simp only [map_smul, app_bas_map]
  · exact ⟨fun _ k => by rw [app_bas_one, app_bas_one],
      fun h => absurd h (by rw [cntR_one]; decide)⟩
  · intro A B _ _ _ _ i x y ⟨hx0, hx1⟩ ⟨hy0, hy1⟩
    rw [cntR_comp]
    refine ⟨fun h k => ?_, fun h => ?_⟩
    · rw [app_bas_comp, app_bas_comp, hx0 (by omega) k, hy0 (by omega) k]
    · rcases (show (cntR (markW n) x = 1 ∧ cntR (markW n) y = 0) ∨
          (cntR (markW n) x = 0 ∧ cntR (markW n) y = 1) by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [app_bas_comp, hx1 h1, map_sum, LinearMap.coe_sum, Finset.sum_apply,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [app_bas_comp, ← hy0 h2 k, map_smul, LinearMap.smul_apply, smul_comm]
      · rw [app_bas_comp, hy1 h2, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [app_bas_comp, ← hx0 h1 k, map_smul, smul_comm]
  · intro k' e
    match k', e with
    | _, .inl g =>
      refine ⟨fun _ k => ?_, fun h => absurd h (by rw [cntR_std]; exact Nat.zero_ne_one)⟩
      show (c.term R k).app _ (FreeGr.gen (gp := MarkGen.par n gp b)
          (Sum.inl g : MarkGen T n _))
        = c.subst.app _ (FreeGr.gen (gp := MarkGen.par n gp b) (Sum.inl g : MarkGen T n _))
      rw [term_gen_inl, subst_gen_inl]
    | _, .inr ⟨.mk⟩ =>
      refine ⟨fun h => absurd h (by rw [cntR_std]; exact Nat.one_ne_zero), fun _ => ?_⟩
      show c.subst.app _ (FreeGr.gen (mark n))
        = ∑ k, c.coef k • (c.term R k).app _ (FreeGr.gen (mark n))
      rw [subst_gen_mark]
      simp only [term_gen_mark]
      rfl

/-- **Substituting a combination lying in an ideal into a marked tree lands in the ideal.** -/
theorem subst_bas_mem (I : GrOperadIdeal R (FreeGr R gp)) (hc : c.val ∈ I.sub (Fin n))
    {A : Type} [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity (MarkGen T n)) A) :
    1 ≤ cntR (markW n) x → c.subst.app A (SgnLin.bas _ R x) ∈ I.sub A := by
  refine FreeReg.induction (P := fun A _ _ x => 1 ≤ cntR (markW n) x →
      c.subst.app A (SgnLin.bas _ R x) ∈ I.sub A) ?_ ?_ ?_ ?_ x
  · intro A B _ _ _ _ e x hx h
    rw [cntR_map] at h
    rw [app_bas_map]
    exact I.map_mem e (hx h)
  · intro h
    exact absurd h (by rw [cntR_one]; decide)
  · intro A B _ _ _ _ i x y hx hy h
    rw [cntR_comp] at h
    rw [app_bas_comp]
    refine Submodule.smul_mem _ _ ?_
    by_cases h1 : 1 ≤ cntR (markW n) x
    · exact I.comp_mem_left i _ (hx h1)
    · exact I.comp_mem_right i _ (hy (by omega))
  · intro k' e
    match k', e with
    | _, .inl g => exact fun h => absurd h (by rw [cntR_std]; exact Nat.not_succ_le_zero 0)
    | _, .inr ⟨.mk⟩ =>
      intro _
      show c.subst.app _ (FreeGr.gen (mark n)) ∈ _
      rw [subst_gen_mark]
      exact hc

/-- **The decomposition of a substitution into a tree with one marked vertex lies in
`I ⊗ C + C ⊗ I`**: in every cut, the marked vertex lies in exactly one part. -/
theorem decomp_subst_mem (I : GrOperadIdeal R (FreeGr R gp)) (hc : c.val ∈ I.sub (Fin n))
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : Reg (TreeOfArity (MarkGen T n)) (Without A i ⊕ B)) (hx : cntR (markW n) x = 1) :
    GrCooperad.decomp (R := R) (C := FreeGr R gp) i (c.subst.app _ (SgnLin.bas _ R x)) ∈
      LinearMap.range (LinearMap.lTensor (FreeGr R gp A) (I.sub B).subtype) ⊔
        LinearMap.range (LinearMap.rTensor (FreeGr R gp B) (I.sub A).subtype) := by
  let K := LinearMap.range (LinearMap.lTensor (FreeGr R gp A) (I.sub B).subtype) ⊔
    LinearMap.range (LinearMap.rTensor (FreeGr R gp B) (I.sub A).subtype)
  -- the decomposition of the substitution of each term
  have hk : ∀ k, GrCooperad.decomp (R := R) (C := FreeGr R gp) i
      ((c.term R k).app _ (SgnLin.bas _ R x))
      = ∑ pq ∈ (SetOperad.FiniteFact.finite i x).toFinset,
          (σ R (SgnData.sgn i ((treeSgn (MarkGen.par n gp b)).app A pq.1)
            ((treeSgn (MarkGen.par n gp b)).app B pq.2)) * 1) •
            ((c.term R k).app A (SgnLin.bas _ R pq.1) ⊗ₜ[R]
              (c.term R k).app B (SgnLin.bas _ R pq.2)) := fun k => by
    have h := LinearMap.congr_fun (c.term_decomp k (B := B) i) (SgnLin.bas _ R x)
    rw [LinearMap.comp_apply] at h
    refine h.trans ?_
    show TensorProduct.map ((c.term R k).app A) ((c.term R k).app B)
      (SgnLin.decompT R (treeSgn (MarkGen.par n gp b)) i (Finsupp.single x (1 : R))) = _
    rw [SgnLin.decompT_single]
    erw [map_sum]
    refine Finset.sum_congr rfl fun pq _ => ?_
    erw [map_smul, TensorProduct.map_tmul]
    rfl
  rw [(c.subst_bas x).2 hx, map_sum]
  simp only [map_smul, hk, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun pq hpq => ?_
  have hpq' : SetOperad.comp i pq.1 pq.2 = x := (SgnLin.mem_fact_iff i x pq).1 hpq
  have hμ : cntR (markW n) pq.1 + cntR (markW n) pq.2 = 1 := by
    rw [← cntR_comp, hpq', hx]
  simp only [smul_smul, mul_one]
  simp only [mul_comm (c.coef _), ← smul_smul, ← Finset.smul_sum]
  refine Submodule.smul_mem _ _ ?_
  rcases (show (cntR (markW n) pq.1 = 1 ∧ cntR (markW n) pq.2 = 0) ∨
      (cntR (markW n) pq.1 = 0 ∧ cntR (markW n) pq.2 = 1) by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e : ∑ k, c.coef k • ((c.term R k).app A (SgnLin.bas _ R pq.1) ⊗ₜ[R]
          (c.term R k).app B (SgnLin.bas _ R pq.2))
        = c.subst.app A (SgnLin.bas _ R pq.1) ⊗ₜ[R] c.subst.app B (SgnLin.bas _ R pq.2) := by
      rw [(c.subst_bas pq.1).2 h1, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(c.subst_bas pq.2).1 h2 k, TensorProduct.smul_tmul']
    rw [e]
    refine Submodule.mem_sup_right ⟨⟨c.subst.app A (SgnLin.bas _ R pq.1),
      c.subst_bas_mem I hc pq.1 (by omega)⟩ ⊗ₜ[R] c.subst.app B (SgnLin.bas _ R pq.2), ?_⟩
    rw [LinearMap.rTensor_tmul]
    rfl
  · have e : ∑ k, c.coef k • ((c.term R k).app A (SgnLin.bas _ R pq.1) ⊗ₜ[R]
          (c.term R k).app B (SgnLin.bas _ R pq.2))
        = c.subst.app A (SgnLin.bas _ R pq.1) ⊗ₜ[R] c.subst.app B (SgnLin.bas _ R pq.2) := by
      rw [(c.subst_bas pq.2).2 h2, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(c.subst_bas pq.1).1 h1 k, TensorProduct.tmul_smul]
    rw [e]
    refine Submodule.mem_sup_left ⟨c.subst.app A (SgnLin.bas _ R pq.1) ⊗ₜ[R]
      ⟨c.subst.app B (SgnLin.bas _ R pq.2), c.subst_bas_mem I hc pq.2 (by omega)⟩, ?_⟩
    rw [LinearMap.lTensor_tmul]
    rfl

/-- The substitutions of the terms preserve the numbers of vertices. -/
lemma cntR_term (k : Fin c.m) {A : Type} [Fintype A] [DecidableEq A]
    (x : Reg (TreeOfArity (MarkGen T n)) A) :
    cntR (fun _ _ => 1) (((c.termVal k).sbm R).ψ.app A x) = cntR (fun _ _ => 1) x :=
  cntR_hom _ _ _ (fun k' e => by
    rw [SBVal.sbm_ψ_std]
    match k', e with
    | _, .inl g => exact cntR_std _ g
    | _, .inr ⟨.mk⟩ =>
      show cntR _ (SetOperad.map (c.perm k) (Reg.std (corolla (c.gen k)))) = 1
      rw [cntR_map]
      exact cntR_std _ _) x

/-- **The counit vanishes on substitutions into trees with one marked vertex.** -/
theorem counit_subst (x : Reg (TreeOfArity (MarkGen T n)) Unit) (hx : cntR (markW n) x = 1) :
    GrCooperad.counit (R := R) (C := FreeGr R gp) (c.subst.app Unit (SgnLin.bas _ R x)) = 0 := by
  rw [(c.subst_bas x).2 hx, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, term, ((c.termVal k).sbm R).app_bas, map_smul]
  have hne : ((c.termVal k).sbm R).ψ.app Unit x ≠ SetOperad.one := by
    intro h
    have h1 := c.cntR_term k x
    have h2 : cntR (markW n) x ≤ cntR (fun _ _ => 1) x :=
      cntR_mono (fun k' e => match k', e with
        | _, .inl _ => Nat.zero_le 1
        | _, .inr _ => le_rfl) x
    rw [h, cntR_one] at h1
    omega
  have h0 : GrCooperad.counit (R := R) (C := FreeGr R gp)
      (SgnLin.bas _ R (((c.termVal k).sbm R).ψ.app Unit x)) = 0 := by
    show Finsupp.single (((c.termVal k).sbm R).ψ.app Unit x) (1 : R) SetOperad.one = 0
    exact Finsupp.single_eq_of_ne' hne
  rw [h0, smul_zero, smul_zero]

end RelComb

/-! ## Unmarked trees -/

section Incl

variable {R gp} (n : ℕ) (b : Bool)

/-- The signed basis values of the inclusion of the unmarked generators. -/
noncomputable def inclVal : SBVal gp (MarkGen.par n gp b) where
  sg _ _ := false
  tree k g := Reg.std (corolla (Sum.inl g : MarkGen T n k))
  tot_eq k g := treeSgn_tot (gp := MarkGen.par n gp b) (Sum.inl g : MarkGen T n k)

variable {n b}

/-- **Substituting into an unmarked tree recovers it.** -/
lemma RelComb.subst_comp_incl (c : RelComb R gp n b) :
    c.subst.comp ((inclVal (gp := gp) n b).hom R) = GrOperadHom.id R (FreeGr R gp) :=
  FreeGr.hom_ext fun k g => by
    rw [GrOperadHom.comp_app, SBVal.hom_gen]
    show c.subst.app _ (σ R false • FreeGr.gen (gp := MarkGen.par n gp b)
      (Sum.inl g : MarkGen T n k)) = FreeGr.gen g
    rw [σ_false, one_smul, c.subst_gen_inl]

/-- **Basis elements are substitutions into unmarked trees**, up to sign. -/
lemma RelComb.bas_eq_subst (c : RelComb R gp n b) {A : Type} [Fintype A] [DecidableEq A]
    (t : Reg (TreeOfArity T) A) :
    ∃ (s : Bool) (t' : Reg (TreeOfArity (MarkGen T n)) A), cntR (markW n) t' = 0 ∧
      SgnLin.bas (treeSgn gp) R t = σ R s • c.subst.app A (SgnLin.bas _ R t') := by
  refine ⟨((inclVal (gp := gp) n b).sbm R).c A t, ((inclVal (gp := gp) n b).sbm R).ψ.app A t,
    ?_, ?_⟩
  · have hψ := cntR_hom (fun _ _ => 0) (markW n) ((inclVal (gp := gp) n b).sbm R).ψ
      (fun k g => by
        rw [SBVal.sbm_ψ_std]
        exact cntR_std (markW n) (Sum.inl g : MarkGen T n k)) t
    rw [hψ, cntR_zero]
  · have h := congrArg (fun Φ : GrOperadHom R (FreeGr R gp) (FreeGr R gp) =>
      Φ.app A (SgnLin.bas _ R t)) c.subst_comp_incl
    simp only [GrOperadHom.comp_app] at h
    rw [((inclVal (gp := gp) n b).sbm R).app_bas, map_smul] at h
    exact h.symm

end Incl

/-! ## The ideal of substitutions -/

section SubstIdeal

variable {R gp}

lemma par_bas_eq {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (x : Reg (TreeOfArity T) A) :
    GrOperad.par (R := R) b (SgnLin.bas (treeSgn gp) R x)
      = if ((treeSgn gp).app A x).tot = b then SgnLin.bas (treeSgn gp) R x else 0 :=
  SgnLin.parT_single b x 1

/-- A linear map out of a free graded operad sending the basis into a submodule sends everything
into it. -/
lemma mem_of_bas {M : Type*} [AddCommGroup M] [Module R M] {A : Type} [Fintype A]
    [DecidableEq A] (f : FreeGr R gp A →ₗ[R] M) (S : Submodule R M)
    (h : ∀ t, f (SgnLin.bas (treeSgn gp) R t) ∈ S) (y : FreeGr R gp A) : f y ∈ S := by
  have := Lin.induction₁ (S := Reg (TreeOfArity T)) (S.mkQ ∘ₗ f) 0 (fun t => by
    rw [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact h t) y
  rwa [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at this

variable (I : GrOperadIdeal R (FreeGr R gp))

/-- **The substitutions of combinations lying in `I` into trees with one marked vertex.** -/
def substSet (A : Type) [Fintype A] [DecidableEq A] : Set (FreeGr R gp A) :=
  {z | ∃ (n : ℕ) (b : Bool) (c : RelComb R gp n b) (_ : c.val ∈ I.sub (Fin n))
    (x : Reg (TreeOfArity (MarkGen T n)) A), cntR (markW n) x = 1 ∧
      c.subst.app A (SgnLin.bas _ R x) = z}

variable {I}

lemma subst_mem_substSet {n : ℕ} {b : Bool} (c : RelComb R gp n b) (hc : c.val ∈ I.sub (Fin n))
    {A : Type} [Fintype A] [DecidableEq A] (x : Reg (TreeOfArity (MarkGen T n)) A)
    (hx : cntR (markW n) x = 1) : c.subst.app A (SgnLin.bas _ R x) ∈ substSet I A :=
  ⟨n, b, c, hc, x, hx, rfl⟩

/-- A linear map sending the substitutions into a submodule sends their span into it. -/
lemma span_substSet_le {M : Type*} [AddCommGroup M] [Module R M] {A : Type} [Fintype A]
    [DecidableEq A] (f : FreeGr R gp A →ₗ[R] M) (S : Submodule R M)
    (h : ∀ {n : ℕ} {b : Bool} (c : RelComb R gp n b), c.val ∈ I.sub (Fin n) →
      ∀ x : Reg (TreeOfArity (MarkGen T n)) A, cntR (markW n) x = 1 →
        f (c.subst.app A (SgnLin.bas _ R x)) ∈ S)
    {z : FreeGr R gp A} (hz : z ∈ Submodule.span R (substSet I A)) : f z ∈ S := by
  refine (Submodule.span_le (p := S.comap f)).2 ?_ hz
  rintro _ ⟨n, b, c, hc, x, hx, rfl⟩
  exact h c hc x hx

lemma substSet_subset (A : Type) [Fintype A] [DecidableEq A] : substSet I A ⊆ I.sub A := by
  rintro _ ⟨n, b, c, hc, x, hx, rfl⟩
  exact c.subst_bas_mem I hc x hx.ge

/-- The composite of two substitutions, into trees with one marked vertex between them. -/
lemma comp_subst_mem {n : ℕ} {b : Bool} (c : RelComb R gp n b) (hc : c.val ∈ I.sub (Fin n))
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (p : Reg (TreeOfArity (MarkGen T n)) A) (q : Reg (TreeOfArity (MarkGen T n)) B)
    (hpq : cntR (markW n) p + cntR (markW n) q = 1) :
    GrOperad.comp (R := R) i (c.subst.app A (SgnLin.bas _ R p))
        (c.subst.app B (SgnLin.bas _ R q))
      ∈ Submodule.span R (substSet I (Without A i ⊕ B)) := by
  rw [← c.subst.app_comp, SgnLin.comp_bas, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (subst_mem_substSet c hc _ (by rw [cntR_comp]; exact hpq)))

variable (I) in
/-- **The ideal spanned by the substitutions.** -/
noncomputable def substIdeal : GrOperadIdeal R (FreeGr R gp) where
  sub A _ _ := Submodule.span R (substSet I A)
  par_mem := by
    intro A _ _ b' z hz
    refine span_substSet_le (GrOperad.par (R := R) b') _ (fun c hc x hx => ?_) hz
    rw [← c.subst.app_par, par_bas_eq]
    split_ifs
    · exact Submodule.subset_span (subst_mem_substSet c hc x hx)
    · rw [map_zero]
      exact zero_mem _
  map_mem := by
    intro A B _ _ _ _ e z hz
    refine span_substSet_le (GrOperad.map (R := R) e) _ (fun c hc x hx => ?_) hz
    rw [← c.subst.app_map, SgnLin.map_bas]
    exact Submodule.subset_span (subst_mem_substSet c hc _ (by rw [cntR_map]; exact hx))
  comp_mem_left := by
    intro A B _ _ _ _ i z y hz
    refine span_substSet_le ((GrOperad.comp (R := R) i).flip y) _ (fun c hc x hx => ?_) hz
    rw [LinearMap.flip_apply]
    refine mem_of_bas (GrOperad.comp (R := R) i (c.subst.app A (SgnLin.bas _ R x))) _
      (fun t => ?_) y
    obtain ⟨s, t', ht', e⟩ := c.bas_eq_subst t
    rw [e, map_smul]
    exact Submodule.smul_mem _ _ (comp_subst_mem c hc i x t' (by rw [hx, ht']))
  comp_mem_right := by
    intro A B _ _ _ _ i y z hz
    refine span_substSet_le (GrOperad.comp (R := R) i y) _ (fun c hc x hx => ?_) hz
    refine mem_of_bas ((GrOperad.comp (R := R) i).flip (c.subst.app B (SgnLin.bas _ R x))) _
      (fun t => ?_) y
    obtain ⟨s, t', ht', e⟩ := c.bas_eq_subst t
    rw [LinearMap.flip_apply, e, map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (comp_subst_mem c hc i t' x (by rw [hx, ht']))

end SubstIdeal

/-! ## The cut cooperad of a free graded operad on a graded linear species -/

namespace FreeGrL

variable (V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]

variable {R V} in
/-- **Every linearity relation is a combination of relabelled generators.** -/
lemma exists_relComb {n : ℕ} {r : FreeGr R (grGenPar R V) (Fin n)} (hr : r ∈ grLinRel R V n) :
    ∃ (b : Bool) (c : RelComb R (grGenPar R V) n b), c.val = r := by
  rcases hr with (⟨b, v, w, hv, hw, rfl⟩ | ⟨b, a, v, hv, rfl⟩) | ⟨b, e, v, hv, rfl⟩
  · refine ⟨b, ⟨3, ![1, -1, -1], ![⟨(v + w, b), by rw [map_add, hv, hw]⟩, ⟨(v, b), hv⟩,
      ⟨(w, b), hw⟩], fun _ => Equiv.refl _, fun k => by fin_cases k <;> rfl⟩, ?_⟩
    simp only [RelComb.val, Fin.sum_univ_three, GrOperad.map_refl]
    simp [lgen, sub_eq_add_neg, add_assoc]
  · refine ⟨b, ⟨2, ![1, -a], ![⟨(a • v, b), by rw [map_smul, hv]⟩, ⟨(v, b), hv⟩],
      fun _ => Equiv.refl _, fun k => by fin_cases k <;> rfl⟩, ?_⟩
    simp only [RelComb.val, Fin.sum_univ_two, GrOperad.map_refl]
    simp [lgen, sub_eq_add_neg]
  · refine ⟨b, ⟨2, ![1, -1], ![⟨(v, b), hv⟩,
      ⟨(SymSpecies.map (R := R) e v, b), by rw [← GrSpecies.map_par, hv]⟩],
      ![e, Equiv.refl _], fun k => by fin_cases k <;> rfl⟩, ?_⟩
    simp only [RelComb.val, Fin.sum_univ_two]
    simp [lgen, sub_eq_add_neg, GrOperad.map_refl]

/-- **The linearity relations are substitutions into a marked corolla.** -/
lemma grLinRel_subset (n : ℕ) :
    grLinRel R V n ⊆ substSet (GrOperadIdeal.span R (grLinRel R V)) (Fin n) := by
  intro r hr
  obtain ⟨b, c, rfl⟩ := exists_relComb hr
  exact ⟨n, b, c, GrOperadIdeal.subset_span n hr, Reg.std (corolla (mark n)),
    cntR_std (markW n) (mark n), c.subst_gen_mark⟩

/-- **The ideal of the linearity relations is spanned by the substitutions.** -/
lemma span_le_substIdeal :
    GrOperadIdeal.span R (grLinRel R V) ≤ substIdeal (GrOperadIdeal.span R (grLinRel R V)) :=
  GrOperadIdeal.span_le.2 fun n => (grLinRel_subset R V n).trans Submodule.subset_span

/-- **The ideal of the linearity relations is a coideal** of the graded decomposition
cooperad. -/
noncomputable def linCoideal : GrCoideal R (FreeGr R (grGenPar R V)) where
  sub := (GrOperadIdeal.span R (grLinRel R V)).sub
  par_mem b := (GrOperadIdeal.span R (grLinRel R V)).par_mem b
  map_mem e := (GrOperadIdeal.span R (grLinRel R V)).map_mem e
  counit_mem {_} hx := (Submodule.mem_bot R).1 (span_substSet_le (GrCooperad.counit (R := R)) ⊥
    (fun c _ x hx' => (Submodule.mem_bot R).2 (c.counit_subst x hx'))
    (span_le_substIdeal R V Unit hx))
  decomp_mem {A B} _ _ _ _ i {_} hx := span_substSet_le (A := Without A i ⊕ B)
    (GrCooperad.decomp (R := R) (C := FreeGr R (grGenPar R V)) (A := A) (B := B) i) _
    (fun c hc x hx' => c.decomp_subst_mem _ hc i x hx') (span_le_substIdeal R V _ hx)

/-- **The free graded operad on a graded linear species is a graded cooperad**, decomposing a
tree with vertices decorated by `V` by cutting it. -/
noncomputable instance instGrCooperad : GrCooperad R (FreeGrL R V) :=
  { (linCoideal R V).instGrCooperad with toGrSpecies := GrOperad.toGrSpecies R (FreeGrL R V) }

/-- **The cut cooperad is coaugmented** by the unit. -/
noncomputable instance instCoaug : GrCooperad.Coaug R (FreeGrL R V) :=
  (linCoideal R V).instCoaug

/-- **The quotient map from the free graded operad on the homogeneous elements is a morphism of
graded cooperads.** -/
noncomputable def projHom : GrCooperadHom R (FreeGr R (grGenPar R V)) (FreeGrL R V) :=
  (linCoideal R V).projHom

lemma projHom_app {A : Type} [Fintype A] [DecidableEq A] :
    (projHom R V).app A = (GrOperadIdeal.span R (grLinRel R V)).proj A := rfl

end FreeGrL

end Operad
