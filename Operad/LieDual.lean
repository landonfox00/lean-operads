/-
# The Koszul dual cooperad of `Lie`

Over a field `K` of characteristic zero, for the presentation of `Lie` of
`Operad/SymPresComLie.lean`:

* **`Lie^¡` has dimension one in every arity `n ≥ 2`** (`LieDual.finrank_dual_lie`): by
  `ShuffleBarSym.dualKDEquiv` it is the top homology of the shuffle bar complex, which has the
  dimension of `Com(n)` (`LieDual.finrank_KD_lie`).
* **`Lie` in `Ass`**: the generators of `Lie` go to the generators of `Ass`, the bracket to the
  commutator (`LieDual.jLie`), with the antisymmetrization as a retraction (`LieDual.retLie`).
  The commutator satisfies the Jacobi identity in the free associative model
  (`LieDual.φL_jacobi`), so the relators of `Lie` go to relations of `Ass` (`LieDual.jLie_rel`).
* **`Lie^¡ → Ass^¡`** (`LieDual.toAss`, by `Koszul.dualMap`), and, through the identification of
  `Ass^¡` with the signed linear orders, **`Lie^¡` embeds in the cooperad of signed linear
  orders** (`LieDual.toOrd`, `LieDual.toOrd_injective`).

The image of the embedding is computed in `Operad/LieAlt.lean`.
-/
import Operad.KoszulDualKD
import Operad.SymPresComLie
import Operad.ShuffleKoszulDuals
import Operad.KoszulDualFunctor
import Operad.OrdDual

universe u

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace LieDual

open SymPresComLie

variable (K : Type u) [Field K] [CharZero K]

omit [CharZero K] in
/-- The top homology of the shuffle bar complex of `Lie` has dimension one. -/
theorem finrank_KD_lie {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank K (ShuffleBar.KD K (ShuffleBarSym.Rsh (cLie K) (hcLie K) (rLie K)) n) = 1 := by
  rw [rsh_lie, ← ComBin.dualRel_rel, ← ShuffleBar.finrank_quotient_dualRel _ hn,
    ShuffleBar.dualRel_dualRel]
  exact ComBin.finrank_quotient K (by omega)

/-- **The Koszul dual cooperad of `Lie` has dimension one in every arity `n ≥ 2`.** -/
theorem finrank_dual_lie {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank K (Koszul.Dual K (ELie K) (rLie K) (Fin n)) = 1 :=
  (ShuffleBarSym.dualKDEquiv (cLie K) (hcLie K) (rLie K) (ShuffleBarSym.orbitRel_hr3 _)
    (ShuffleBarSym.orbitRel_hrS _) hn).finrank_eq.trans (finrank_KD_lie K hn)

/-! ## `Lie` in `Ass`: the commutator of an associative product -/

section Commutator

omit [CharZero K] in
/-- **The generators of `Lie` in the generators of `Ass`**: an antisymmetric function on the
orderings of two inputs, as a function on the numberings. The bracket goes to the commutator. -/
def jLie : GrSpeciesHom K (ELie K) (SymPresB.Reg2 K) where
  app A _ _ :=
    { toFun := fun f => (show SymPresB.Reg2 K A from fun τ : Fin 2 ≃ A => f.1 τ.symm)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  app_map _ _ := rfl
  app_par b _ := by cases b <;> rfl

omit [CharZero K] in
lemma jLie_val {A : Type} [Fintype A] [DecidableEq A] (f : ELie K A) (τ : Fin 2 ≃ A) :
    ((jLie K).app A f).val τ = f.1 τ.symm := rfl

/-- **The antisymmetrization**, a retraction of `jLie`. -/
noncomputable def retLie : GrSpeciesHom K (SymPresB.Reg2 K) (ELie K) where
  app A _ _ :=
    { toFun := fun g =>
        ⟨fun e => (2 : K)⁻¹ * (g.val e.symm - g.val (e.trans (Equiv.swap 0 1)).symm),
        fun e => by
          show (2 : K)⁻¹ * (g.val (e.trans (Equiv.swap 0 1)).symm
            - g.val ((e.trans (Equiv.swap 0 1)).trans (Equiv.swap 0 1)).symm)
            = -((2 : K)⁻¹ * (g.val e.symm - g.val (e.trans (Equiv.swap 0 1)).symm))
          have h : (e.trans (Equiv.swap (0 : Fin 2) 1)).trans (Equiv.swap 0 1) = e :=
            Equiv.ext fun a => by simp
          rw [h]
          ring⟩
      map_add' := fun g g' => Subtype.ext (funext fun e => by
        show (2 : K)⁻¹ * ((g.val e.symm + g'.val e.symm)
          - (g.val (e.trans (Equiv.swap 0 1)).symm + g'.val (e.trans (Equiv.swap 0 1)).symm)) = _
        show _ = (2 : K)⁻¹ * (g.val e.symm - g.val (e.trans (Equiv.swap 0 1)).symm)
          + (2 : K)⁻¹ * (g'.val e.symm - g'.val (e.trans (Equiv.swap 0 1)).symm)
        ring)
      map_smul' := fun a g => Subtype.ext (funext fun e => by
        show (2 : K)⁻¹ * (a * g.val e.symm - a * g.val (e.trans (Equiv.swap 0 1)).symm)
          = a * ((2 : K)⁻¹ * (g.val e.symm - g.val (e.trans (Equiv.swap 0 1)).symm))
        ring) }
  app_map _ _ := rfl
  app_par b g := by
    cases b
    · rfl
    · exact Subtype.ext (funext fun e => by
        show (2 : K)⁻¹ * ((0 : K) - 0) = 0
        ring)

lemma retLie_jLie {A : Type} [Fintype A] [DecidableEq A] (f : ELie K A) :
    (retLie K).app A ((jLie K).app A f) = f := by
  refine Subtype.ext (funext fun e => ?_)
  show (2 : K)⁻¹ * (f.1 e.symm.symm - f.1 (e.trans (Equiv.swap 0 1)).symm.symm) = f.1 e
  have h1 : f.1 (e.trans (Equiv.swap 0 1)) = -f.1 e := f.2 e
  rw [Equiv.symm_symm, Equiv.symm_symm, h1]
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  field_simp
  ring

end Commutator

/-! ## The Jacobi identity for the commutator, and `Lie^¡ → Ass^¡` -/

section Model

open LTree ComBin

/-- **The model of `Lie` in the free associative algebra**: the bracket is the commutator. -/
noncomputable def φL :
    GrOperadHom K (FreeGrL K (ELie K)) (SymGr (EndOp K (SymPresAss.V K))) :=
  (SymPresAss.φ K).comp (FreeGrL.mapSp (jLie K))

omit [CharZero K] in
/-- The bracket of the model is the commutator. -/
lemma μ_φL (g : ComGen 2) (x y : SymPresAss.V K) :
    SymPresB.μ (cLie K) (φL K) g x y = x * y - y * x := by
  show SymPresB.sgEv ((SymPresAss.φ K).app (Fin 2) ((FreeGrL.mapSp (jLie K)).app (Fin 2)
    ((FreeGrL.ι K (ELie K)).app (Fin 2) (cLie K 2 (.op g))))) ![x, y] = _
  rw [FreeGrL.mapSp_ι, SymPresAss.φ, SymPresB.model, FreeGrL.homEquiv_symm_ι]
  show SymPresB.sgEv (SymPresB.modelApp _ (Fin 2) ((jLie K).app (Fin 2) (cLie K 2 (.op g))))
    ![x, y] = _
  rw [SymPresB.sgEv_modelApp]
  have huniv : (Finset.univ : Finset (Fin 2 ≃ Fin 2)) = {Equiv.refl _, Equiv.swap 0 1} := by
    decide
  have h1 : (cLie K 2 (.op g)).1 (Equiv.refl _) = 1 := by
    rw [cLie, BinSp.basis_op, BinSp.ofV_apply_refl]
    exact Module.Basis.singleton_apply _ _ _
  have h2 : (cLie K 2 (.op g)).1 (Equiv.swap 0 1) = -1 := by
    have h := (cLie K 2 (.op g)).2 (Equiv.refl _)
    rw [h1] at h
    exact h
  rw [huniv, Finset.sum_pair (by decide), jLie_val, jLie_val, Equiv.refl_symm, Equiv.symm_swap,
    h1, h2]
  simp [sub_eq_add_neg]

omit [CharZero K] in
/-- **The commutator satisfies the Jacobi identity**: the Jacobiator vanishes in the model. -/
theorem φL_jacobi : (φL K).app (Fin 3) (jacobi K) = 0 := by
  refine (SymPresB.eq_zero_iff _).2 fun w => ?_
  have h : ∀ (t : LTree (ComGen 2)) (ht : t ∈ monomials 3),
      SymPresB.sgEv ((φL K).app (Fin 3) (tb (cLie K) (hcLie K) t ht)) w
        = SymPresB.lev (SymPresB.μ (cLie K) (φL K))
          (fun a => if h : a < 3 then w ⟨a, h⟩ else 0) t := fun t ht =>
    SymPresB.app_tBasis (cLie K) (hcLie K) (φL K) _ w
  rw [jacobi, map_sub, map_sub]
  show SymPresB.sgEv ((φL K).app (Fin 3) (tb (cLie K) (hcLie K) lcomb lcomb_mem)) w
    - SymPresB.sgEv ((φL K).app (Fin 3) (tb (cLie K) (hcLie K) tcomb tcomb_mem)) w
    - SymPresB.sgEv ((φL K).app (Fin 3) (tb (cLie K) (hcLie K) rcomb rcomb_mem)) w = 0
  rw [h, h, h]
  simp only [lcomb, tcomb, rcomb, SymPresB.lev, μ_φL]
  simp only [show (0 : ℕ) < 3 from by decide, show (1 : ℕ) < 3 from by decide,
    show (2 : ℕ) < 3 from by decide, dite_true]
  noncomm_ring

omit [CharZero K] in
/-- **The relators of `Lie` go to relations of `Ass`.** -/
theorem jLie_rel (n : ℕ) (x : FreeGrL K (ELie K) (Fin n)) (hx : x ∈ rLie K n) :
    (FreeGrL.mapSp (jLie K)).app (Fin n) x
      ∈ (GrOperadIdeal.span K (SymPresAss.rel K)).sub (Fin n) := by
  obtain ⟨e, y, hy, rfl⟩ := hx
  obtain rfl : n = 3 := by simpa using (Fintype.card_congr e).symm
  rw [Set.mem_singleton_iff] at hy
  subst hy
  refine GrOperadIdeal.subset_span 3 ⟨rfl, ?_⟩
  have h := congrArg (GrOperad.map (R := K) e) (φL_jacobi K)
  rw [map_zero, ← (φL K).app_map] at h
  exact h

/-- **The morphism `Lie^¡ → Ass^¡`** of Koszul dual cooperads induced by the commutator. -/
noncomputable def toAss :
    GrCooperadHom K (Koszul.Dual K (ELie K) (rLie K))
      (Koszul.Dual K (SymPresB.Reg2 K) (SymPresAss.rel K)) :=
  Koszul.dualMap (rLie K) (SymPresAss.rel K) (jLie K)
    (Koszul.mapSp_mem_span (rLie K) (SymPresAss.rel K) (jLie K) (jLie_rel K))

/-- **`Lie^¡` in the cooperad of signed linear orders.** -/
noncomputable def toOrd : GrCooperadHom K (Koszul.Dual K (ELie K) (rLie K)) (OrdCo K) :=
  ((OrdCo.toDual K).symmOfBijective (OrdCo.toDual_bijective K)).comp (toAss K)

lemma toDual_toOrd {A : Type} [Fintype A] [DecidableEq A]
    (x : Koszul.Dual K (ELie K) (rLie K) A) :
    (OrdCo.toDual K).app A ((toOrd K).app A x) = (toAss K).app A x :=
  (OrdCo.toDual K).app_symmOfBijective (OrdCo.toDual_bijective K) _

/-- **`Lie^¡` embeds in the cooperad of signed linear orders.** -/
theorem toOrd_injective (A : Type) [Fintype A] [DecidableEq A] :
    Function.Injective ((toOrd K).app A) := by
  intro x y h
  have h1 : (toAss K).app A x = (toAss K).app A y := by
    rw [← toDual_toOrd, ← toDual_toOrd, h]
  have h2 := congrArg ((Koszul.dualSub K (SymPresB.Reg2 K) (SymPresAss.rel K)).incl A) h1
  have hinj : Function.Injective ((FreeGrL.mapSp (Koszul.shiftHom (jLie K))).app A) :=
    FreeGrL.mapSp_injective_of_retraction (f := Koszul.shiftHom (jLie K))
      (g := Koszul.shiftHom (retLie K)) fun B _ _ v => retLie_jLie K v
  exact (Koszul.dualSub K (ELie K) (rLie K)).incl_injective A (hinj h2)

end Model

end LieDual

end Operad
