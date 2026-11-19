/-
# The trees with two vertices of a free graded operad

Let `T(W)` be the free graded operad on a graded linear species `W` (`FreeGrL R W`), with its cut
cooperad structure. **The coefficients of the cut at a set of inputs `S`**
(`FreeGrL.cutCoef`) decompose a tree at the splitting of its inputs by `S` and take the
coefficient of the generators on both sides: a linear map `T(W)(X) → W(X / S) ⊗ W(S)`.

**They read the trees with two vertices.** For `a ∈ W(X / S)` and `b ∈ W(S)` with `S` nonempty,
the composite `a ∘_S b` of the two generators has coefficients `a ⊗ b` at `S`
(`FreeGrL.cutCoef_comp_ι_self`) and `0` at every other set of inputs
(`FreeGrL.cutCoef_comp_ι_of_ne`). So the maps `a ⊗ b ↦ a ∘_S b` are jointly injective: a sum
`∑_S a_S ∘_S b_S` over the nonempty sets of inputs determines its terms
(`FreeGrL.cutCoef_sum_twoVertex`).

The proof is on basis trees. A cut of a composite of two corollas both of whose parts have one
vertex is the cut between the corollas, at the inputs of the inner one (`FreeGr.inner_inputs`,
`FreeGr.fact_corolla_unique`), and the coefficient of the generators vanishes on the trees
without exactly one vertex.
-/
import Operad.BarCobar
import Operad.CutCofree

universe u v

namespace Operad

open Sym GerBV TreeOfArity FreeGr
open scoped TensorProduct

namespace FreeGrL

variable {R : Type u} [CommRing R]
  {W : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (W A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (W A)] [GrSpecies R W]
  {X : Type} [Fintype X] [DecidableEq X]

local notation "𝒥" => GrOperadIdeal.span R (grLinRel R W)
local notation "𝔟" => SgnLin.bas (treeSgn (grGenPar R W)) R

/-! ## On basis trees -/

variable (R W) in
/-- The coefficients of the cut at a set of inputs, on the free graded operad on the homogeneous
elements. -/
noncomputable def cutCoefF (S : Finset X) :
    FreeGr R (grGenPar R W) X →ₗ[R] W (SOut S) ⊗[R] W (SIn S) :=
  TensorProduct.map (genCoefF R W (SOut S)) (genCoefF R W (SIn S)) ∘ₗ
    GrCooperad.decomp (R := R) (C := FreeGr R (grGenPar R W)) none ∘ₗ
    GrOperad.map (R := R) (splitEquiv S).symm

/-- **The coefficients of a cut of a basis tree**: the signed sum over its factorizations of the
decorations of the two parts. -/
lemma cutCoefF_bas (S : Finset X) (t : Reg (TreeOfArity (GrGen R W)) X) :
    cutCoefF R W S (𝔟 t)
      = ∑ pq ∈ (SetOperad.FiniteFact.finite none
            (SetOperad.map (splitEquiv S).symm t)).toFinset,
          σ R (Tree.tpar (grGenPar R W) (treeOf pq.2)
              && Tree.apar (grGenPar R W) (treeOf pq.1) (pq.1.1.rank none)) •
            (coefReg R W pq.1 ⊗ₜ[R] coefReg R W pq.2) := by
  rw [cutCoefF, LinearMap.comp_apply, LinearMap.comp_apply, SgnLin.map_bas, FreeGr.decomp_bas,
    map_sum]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [map_smul, TensorProduct.map_tmul, genCoefF_bas, genCoefF_bas]

lemma coefReg_of_nVert_ne {A : Type} [Fintype A] [DecidableEq A]
    {x : Reg (TreeOfArity (GrGen R W)) A} (hx : FreeGr.nVert x ≠ 1) : coefReg R W x = 0 :=
  coefReg_of_weight_ne (by rwa [← FreeGr.nVert_eq])

lemma nVert_std_corolla {k : ℕ} (c : GrGen R W k) : FreeGr.nVert (Reg.std (corolla c)) = 1 :=
  FreeReg.cntR_std _ c

section Corollas

variable {k l : ℕ} (c : GrGen R W k) (g : GrGen R W l) (r : Fin k)
  (e : Without (Fin k) r ⊕ Fin l ≃ X) (S₀ : Finset X)
  (hS₀ : ∀ x, x ∈ S₀ ↔ ∃ b, e (Sum.inr b) = x)

include hS₀ in
/-- **A composite of two corollas has no coefficients away from the inputs of the inner
corolla.** -/
theorem cutCoefF_corollas_of_ne {S : Finset X} (hS : S ≠ S₀) :
    cutCoefF R W S (𝔟 (SetOperad.map e (SetOperad.comp r (Reg.std (corolla c))
      (Reg.std (corolla g))))) = 0 := by
  rw [cutCoefF_bas]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  by_cases h1 : FreeGr.nVert pq.1 = 1
  · by_cases h2 : FreeGr.nVert pq.2 = 1
    · exfalso
      apply hS
      have hc := FreeGr.mem_fib.1 hpq
      have hx : SetOperad.map (splitEquiv S) (SetOperad.comp none pq.1 pq.2)
          = SetOperad.map e (SetOperad.comp r (Reg.std (corolla c)) (Reg.std (corolla g))) := by
        rw [hc, SetOperad.map_map_symm]
      have key := FreeGr.inner_inputs (splitEquiv S) e h1 h2 (nVert_std_corolla c)
        (nVert_std_corolla g) hx
      ext a
      rw [hS₀ a, ← key a]
      constructor
      · intro ha
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro ⟨b, rfl⟩
        exact b.2
    · rw [coefReg_of_nVert_ne h2, TensorProduct.tmul_zero, smul_zero]
  · rw [coefReg_of_nVert_ne h1, TensorProduct.zero_tmul, smul_zero]

/-- **The coefficients of a composite of two corollas at the inputs of the inner corolla** are
the two decorations, relabelled. -/
theorem cutCoefF_corollas_self (hl : l ≠ 0) :
    cutCoefF R W S₀ (𝔟 (SetOperad.map e (SetOperad.comp r (Reg.std (corolla c))
      (Reg.std (corolla g)))))
      = SymSpecies.map (R := R) (GrOperad.canonOut e S₀ hS₀) c.1.1
          ⊗ₜ[R] SymSpecies.map (R := R) (GrOperad.canonIn e S₀ hS₀) g.1.1 := by
  rw [cutCoefF_bas]
  have hx₀ : SetOperad.map (splitEquiv S₀).symm (SetOperad.map e (SetOperad.comp r
        (Reg.std (corolla c)) (Reg.std (corolla g))))
      = SetOperad.comp none
          (SetOperad.map (GrOperad.canonOut e S₀ hS₀) (Reg.std (corolla c)))
          (SetOperad.map (GrOperad.canonIn e S₀ hS₀) (Reg.std (corolla g))) := by
    rw [FreeGr.map_comp_canon_reg e S₀ hS₀, SetOperad.map_symm_map]
  rw [hx₀]
  set pa := SetOperad.map (GrOperad.canonOut e S₀ hS₀) (Reg.std (corolla c)) with hpa_def
  set pb := SetOperad.map (GrOperad.canonIn e S₀ hS₀) (Reg.std (corolla g)) with hpb_def
  have hpa : FreeGr.nVert pa = 1 := by
    rw [FreeGr.nVert, FreeReg.cntR_map]
    exact nVert_std_corolla c
  have hpb : FreeGr.nVert pb = 1 := by
    rw [FreeGr.nVert, FreeReg.cntR_map]
    exact nVert_std_corolla g
  have b₀ : SIn S₀ := ⟨e (Sum.inr ⟨0, Nat.pos_of_ne_zero hl⟩), (hS₀ _).2 ⟨_, rfl⟩⟩
  rw [Finset.sum_eq_single (pa, pb) ?_ ?_]
  · have h1 : Tree.apar (grGenPar R W) (treeOf pa) (pa.1.rank none) = false :=
      aparF_leaves _ k _
    rw [h1, Bool.and_false, σ_false, one_smul, hpa_def, hpb_def, coefReg_map, coefReg_map,
      coefReg_std_corolla, coefReg_std_corolla]
  · intro pq hpq hne
    by_cases h1 : FreeGr.nVert pq.1 = 1
    · by_cases h2 : FreeGr.nVert pq.2 = 1
      · have hu := FreeGr.fact_corolla_unique b₀ h1 h2 hpa hpb (FreeGr.mem_fib.1 hpq)
        exact absurd (Prod.ext hu.1 hu.2) hne
      · rw [coefReg_of_nVert_ne h2, TensorProduct.tmul_zero, smul_zero]
    · rw [coefReg_of_nVert_ne h1, TensorProduct.zero_tmul, smul_zero]
  · intro h
    exact absurd ((FreeGr.mem_fib (pq := (pa, pb))).2 rfl) h

end Corollas

/-- **A composite of two corollas is the composite of the generators.** -/
lemma bas_corollas {k l : ℕ} (c : GrGen R W k) (g : GrGen R W l) (r : Fin k) :
    𝔟 (SetOperad.comp r (Reg.std (corolla c)) (Reg.std (corolla g)))
      = GrOperad.comp (R := R) r (FreeGr.gen (R := R) (gp := grGenPar R W) c)
          (FreeGr.gen (R := R) (gp := grGenPar R W) g) := by
  rw [FreeGr.bas_comp_eq]
  have h : Tree.apar (grGenPar R W) (treeOf (Reg.std (corolla c)))
      ((Reg.std (corolla c)).1.rank r) = false := aparF_leaves _ k _
  rw [h, Bool.and_false, σ_false, one_smul]
  rfl

/-! ## On the free graded operad on a graded linear species -/

variable (R W) in
/-- **The coefficients of the cut at a set of inputs**: the decomposition at the splitting of the
inputs by `S`, followed by the coefficient of the generators on both sides. -/
noncomputable def cutCoef (S : Finset X) : FreeGrL R W X →ₗ[R] W (SOut S) ⊗[R] W (SIn S) :=
  TensorProduct.map (genCoef R W (SOut S)) (genCoef R W (SIn S)) ∘ₗ
    GrCooperad.decomp (R := R) (C := FreeGrL R W) none ∘ₗ
    GrOperad.map (R := R) (splitEquiv S).symm

lemma genCoef_comp_projHom (A : Type) [Fintype A] [DecidableEq A] :
    genCoef R W A ∘ₗ (projHom R W).app A = genCoefF R W A :=
  LinearMap.ext fun _ => rfl

lemma cutCoef_proj (S : Finset X) (y : FreeGr R (grGenPar R W) X) :
    cutCoef R W S ((𝒥).proj X y) = cutCoefF R W S y := by
  have h := LinearMap.congr_fun ((projHom R W).decomp_app (A := SOut S) (B := SIn S) none)
    (GrOperad.map (R := R) (splitEquiv S).symm y)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  show TensorProduct.map (genCoef R W (SOut S)) (genCoef R W (SIn S))
    (GrCooperad.decomp (R := R) (C := FreeGrL R W) none
      ((projHom R W).app _ (GrOperad.map (R := R) (splitEquiv S).symm y))) = _
  rw [h, ← LinearMap.comp_apply, ← TensorProduct.map_comp, genCoef_comp_projHom,
    genCoef_comp_projHom]
  rfl

/-- **A relabelled composite of two generators is the class of a composite of two corollas.** -/
lemma map_comp_ι_gen {k l : ℕ} (c : GrGen R W k) (g : GrGen R W l) (r : Fin k)
    (e : Without (Fin k) r ⊕ Fin l ≃ X) :
    GrOperad.map (R := R) e (GrOperad.comp (R := R) r ((ι R W).app (Fin k) c.1.1)
        ((ι R W).app (Fin l) g.1.1))
      = (𝒥).proj X (𝔟 (SetOperad.map e (SetOperad.comp r (Reg.std (corolla c))
          (Reg.std (corolla g))))) := by
  rw [ι_app_hom c.2, ι_app_hom g.2, ← SgnLin.map_bas, bas_corollas]
  rfl

/-- **A composite of two homogeneous generators at a nonempty set of inputs is the class of a
relabelled composite of two corollas**, with the inner corolla at that set of inputs and the
decorations relabelled. -/
lemma exists_corollas {S : Finset X} (hS : S.Nonempty) {p q : Bool} {a : W (SOut S)}
    {b : W (SIn S)} (ha : GrSpecies.par (R := R) p a = a)
    (hb : GrSpecies.par (R := R) q b = b) :
    ∃ (k l : ℕ) (c : GrGen R W k) (g : GrGen R W l) (r : Fin k)
      (e : Without (Fin k) r ⊕ Fin l ≃ X) (hS₀ : ∀ x, x ∈ S ↔ ∃ j, e (Sum.inr j) = x),
      l ≠ 0 ∧
      GrOperad.map (R := R) (splitEquiv S) (GrOperad.comp (R := R) none
          ((ι R W).app (SOut S) a) ((ι R W).app (SIn S) b))
        = (𝒥).proj X (𝔟 (SetOperad.map e (SetOperad.comp r (Reg.std (corolla c))
            (Reg.std (corolla g))))) ∧
      SymSpecies.map (R := R) (GrOperad.canonOut e S hS₀) c.1.1 = a ∧
      SymSpecies.map (R := R) (GrOperad.canonIn e S hS₀) g.1.1 = b := by
  obtain ⟨s⟩ : Nonempty (SOut S ≃ Fin (Fintype.card (SOut S))) := ⟨Fintype.equivFin _⟩
  obtain ⟨t⟩ : Nonempty (SIn S ≃ Fin (Fintype.card (SIn S))) := ⟨Fintype.equivFin _⟩
  set e : Without (Fin (Fintype.card (SOut S))) (s none) ⊕ Fin (Fintype.card (SIn S)) ≃ X :=
    (compEquiv s t none).symm.trans (splitEquiv S) with he
  have hS₀ : ∀ x, x ∈ S ↔ ∃ j, e (Sum.inr j) = x := fun x => by
    constructor
    · intro hx
      refine ⟨t ⟨x, hx⟩, ?_⟩
      show splitEquiv S ((compEquiv s t none).symm (Sum.inr (t ⟨x, hx⟩))) = x
      rw [compEquiv_symm_inr, splitEquiv_inr, Equiv.symm_apply_apply]
    · rintro ⟨j, rfl⟩
      show splitEquiv S ((compEquiv s t none).symm (Sum.inr j)) ∈ S
      rw [compEquiv_symm_inr, splitEquiv_inr]
      exact (t.symm j).2
  have hco : GrOperad.canonOut e S hS₀ = s.symm := Equiv.ext fun j => by
    by_cases hj : j = s none
    · rw [hj, GrOperad.canonOut_self, Equiv.symm_apply_apply]
    · rw [GrOperad.canonOut_ne e S hS₀ hj]
      have hne : s.symm j ≠ none := fun h => hj (by rw [← h, Equiv.apply_symm_apply])
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hne
      rw [hx]
      refine congrArg some (Subtype.ext ?_)
      show splitEquiv S ((compEquiv s t none).symm (Sum.inl ⟨j, hj⟩)) = x.1
      rw [compEquiv_symm_inl, splitEquiv_inl]
      exact outVal_eq_of_eq _ hx
  have hci : GrOperad.canonIn e S hS₀ = t.symm := Equiv.ext fun j => Subtype.ext (by
    rw [GrOperad.canonIn_apply]
    show splitEquiv S ((compEquiv s t none).symm (Sum.inr j)) = _
    rw [compEquiv_symm_inr, splitEquiv_inr])
  have hpa : GrSpecies.par (R := R) p (SymSpecies.map (R := R) s a)
      = SymSpecies.map (R := R) s a := by rw [← GrSpecies.map_par, ha]
  have hqb : GrSpecies.par (R := R) q (SymSpecies.map (R := R) t b)
      = SymSpecies.map (R := R) t b := by rw [← GrSpecies.map_par, hb]
  haveI : Nonempty (SIn S) := hS.to_subtype
  refine ⟨_, _, ⟨(SymSpecies.map (R := R) s a, p), hpa⟩, ⟨(SymSpecies.map (R := R) t b, q), hqb⟩,
    s none, e, hS₀, Fintype.card_ne_zero, ?_, ?_, ?_⟩
  · have k1 : GrOperad.comp (R := R) none ((ι R W).app (SOut S) a) ((ι R W).app (SIn S) b)
        = GrOperad.map (R := R) (compEquiv s t none).symm (GrOperad.comp (R := R) (s none)
            (GrOperad.map (R := R) s ((ι R W).app (SOut S) a))
            (GrOperad.map (R := R) t ((ι R W).app (SIn S) b))) := by
      rw [← GrOperad.map_comp, ← GrOperad.map_trans, Equiv.self_trans_symm, GrOperad.map_refl]
    have h1 : GrOperad.map (R := R) s ((ι R W).app (SOut S) a)
        = (ι R W).app _ (SymSpecies.map (R := R) s a) := ((ι R W).app_map s a).symm
    have h2 : GrOperad.map (R := R) t ((ι R W).app (SIn S) b)
        = (ι R W).app _ (SymSpecies.map (R := R) t b) := ((ι R W).app_map t b).symm
    rw [k1, h1, h2, ← GrOperad.map_trans]
    exact map_comp_ι_gen ⟨(SymSpecies.map (R := R) s a, p), hpa⟩
      ⟨(SymSpecies.map (R := R) t b, q), hqb⟩ (s none) e
  · exact (congrArg (fun f => SymSpecies.map (R := R) f (SymSpecies.map (R := R) s a)) hco).trans
      (SymSpecies.map_symm_map s a)
  · exact (congrArg (fun f => SymSpecies.map (R := R) f (SymSpecies.map (R := R) t b)) hci).trans
      (SymSpecies.map_symm_map t b)

/-- The composite of two generators at a set of inputs, relabelled onto all the inputs. -/
noncomputable abbrev twoVertex (S : Finset X) (a : W (SOut S)) (b : W (SIn S)) : FreeGrL R W X :=
  GrOperad.map (R := R) (splitEquiv S) (GrOperad.comp (R := R) none
    ((ι R W).app (SOut S) a) ((ι R W).app (SIn S) b))

variable (R W) in
/-- The composite of two generators at a set of inputs, as a bilinear map. -/
noncomputable def twoVertexL (S : Finset X) :
    W (SOut S) →ₗ[R] W (SIn S) →ₗ[R] FreeGrL R W X :=
  LinearMap.mk₂ R (fun a b => twoVertex S a b)
    (fun a a' b => by simp only [twoVertex, map_add, LinearMap.add_apply])
    (fun c a b => by simp only [twoVertex, map_smul, LinearMap.smul_apply])
    (fun a b b' => by simp only [twoVertex, map_add])
    (fun c a b => by simp only [twoVertex, map_smul])

@[simp] lemma twoVertexL_apply (S : Finset X) (a : W (SOut S)) (b : W (SIn S)) :
    twoVertexL R W S a b = twoVertex S a b := rfl

/-- **The coefficients of a composite of two generators at its own set of inputs** are the two
generators. -/
theorem cutCoef_comp_ι_self {S : Finset X} (hS : S.Nonempty) (a : W (SOut S)) (b : W (SIn S)) :
    cutCoef R W S (twoVertex S a b) = a ⊗ₜ[R] b := by
  have key : ∀ (p q : Bool) (a : W (SOut S)) (b : W (SIn S)),
      GrSpecies.par (R := R) p a = a → GrSpecies.par (R := R) q b = b →
      cutCoef R W S (twoVertexL R W S a b) = a ⊗ₜ[R] b := fun p q a b ha hb => by
    obtain ⟨k, l, c, g, r, e, hS₀, hl, h, hca, hcb⟩ := exists_corollas hS ha hb
    rw [twoVertexL_apply, twoVertex, h, cutCoef_proj, cutCoefF_corollas_self c g r e S hS₀ hl,
      hca, hcb]
  have ha := GrSpecies.par_add (R := R) a
  have hb := GrSpecies.par_add (R := R) b
  show cutCoef R W S (twoVertexL R W S a b) = a ⊗ₜ[R] b
  rw [← ha, ← hb]
  simp only [map_add, LinearMap.add_apply, TensorProduct.add_tmul, TensorProduct.tmul_add,
    key false false _ _ (GrSpecies.par_par_self false a) (GrSpecies.par_par_self false b),
    key false true _ _ (GrSpecies.par_par_self false a) (GrSpecies.par_par_self true b),
    key true false _ _ (GrSpecies.par_par_self true a) (GrSpecies.par_par_self false b),
    key true true _ _ (GrSpecies.par_par_self true a) (GrSpecies.par_par_self true b)]

/-- **A composite of two generators has no coefficients at the other sets of inputs.** -/
theorem cutCoef_comp_ι_of_ne {S S' : Finset X} (hS : S.Nonempty) (h : S' ≠ S)
    (a : W (SOut S)) (b : W (SIn S)) : cutCoef R W S' (twoVertex S a b) = 0 := by
  have key : ∀ (p q : Bool) (a : W (SOut S)) (b : W (SIn S)),
      GrSpecies.par (R := R) p a = a → GrSpecies.par (R := R) q b = b →
      cutCoef R W S' (twoVertexL R W S a b) = 0 := fun p q a b ha hb => by
    obtain ⟨k, l, c, g, r, e, hS₀, hl, h', hca, hcb⟩ := exists_corollas hS ha hb
    rw [twoVertexL_apply, twoVertex, h', cutCoef_proj, cutCoefF_corollas_of_ne c g r e S hS₀ h]
  have ha := GrSpecies.par_add (R := R) a
  have hb := GrSpecies.par_add (R := R) b
  show cutCoef R W S' (twoVertexL R W S a b) = 0
  rw [← ha, ← hb]
  simp only [map_add, LinearMap.add_apply, add_zero,
    key false false _ _ (GrSpecies.par_par_self false a) (GrSpecies.par_par_self false b),
    key false true _ _ (GrSpecies.par_par_self false a) (GrSpecies.par_par_self true b),
    key true false _ _ (GrSpecies.par_par_self true a) (GrSpecies.par_par_self false b),
    key true true _ _ (GrSpecies.par_par_self true a) (GrSpecies.par_par_self true b)]

variable (R W) in
/-- **The trees with two vertices at a set of inputs**, as a linear map on the tensors of the two
generators. -/
noncomputable def twoVertexT (S : Finset X) : W (SOut S) ⊗[R] W (SIn S) →ₗ[R] FreeGrL R W X :=
  TensorProduct.lift (twoVertexL R W S)

@[simp] lemma twoVertexT_tmul (S : Finset X) (a : W (SOut S)) (b : W (SIn S)) :
    twoVertexT R W S (a ⊗ₜ[R] b) = twoVertex S a b :=
  TensorProduct.lift.tmul _ _

theorem cutCoef_twoVertexT_self {S : Finset X} (hS : S.Nonempty)
    (z : W (SOut S) ⊗[R] W (SIn S)) : cutCoef R W S (twoVertexT R W S z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rw [twoVertexT_tmul, cutCoef_comp_ι_self hS]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

theorem cutCoef_twoVertexT_of_ne {S S' : Finset X} (hS : S.Nonempty) (h : S' ≠ S)
    (z : W (SOut S) ⊗[R] W (SIn S)) : cutCoef R W S' (twoVertexT R W S z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rw [twoVertexT_tmul, cutCoef_comp_ι_of_ne hS h]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', add_zero]

/-- **A sum of trees with two vertices over the nonempty sets of inputs determines its terms.** -/
theorem cutCoef_sum_twoVertex (z : ∀ S : Finset X, W (SOut S) ⊗[R] W (SIn S)) {S : Finset X}
    (hS : S ∈ nonempties X) :
    cutCoef R W S (∑ S' ∈ nonempties X, twoVertexT R W S' (z S')) = z S := by
  rw [map_sum, Finset.sum_eq_single S (fun S' hS' h => cutCoef_twoVertexT_of_ne
      (Finset.mem_filter.1 hS').2 (Ne.symm h) (z S')) (fun h => absurd hS h),
    cutCoef_twoVertexT_self (Finset.mem_filter.1 hS).2]

end FreeGrL

end Operad
