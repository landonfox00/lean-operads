/-
# The Koszul dual cooperad of `Com`, as a quotient of the signed linear orders

Over a field `K` of characteristic zero, for the presentations of `Ass` and `Com` of
`Operad/SymPresAss.lean` and `Operad/SymPresComLie.lean`:

* **`Ass` onto `Com`**: the generators of `Ass` go to the generators of `Com` by symmetrization
  (`ComDual.jCom`), with half of the inclusion as a section (`ComDual.sCom`).
* **The relators of `Ass` go to relations of `Com`** (`ComDual.jCom_rel`): an operation of arity
  three vanishing in the free associative algebra vanishes in the commutative algebra `K`
  (`ComDual.φK_eq_zero`, evaluating on scalars), the evaluation in `K` factors through the
  symmetrization (`ComDual.ψK_mapSp`), and the operations of arity three of `Com` vanishing in
  `K` are the relations (`ComDual.mem_span_of_ψK`): their coordinates sum to zero.
* **`Ass^¡ → Com^¡`** (`ComDual.toCom`, by `Koszul.dualMap`) and, from the signed linear orders,
  `ComDual.rho : OrdCo K → Com^¡`, whose generators are the symmetrizations of the orders on two
  inputs (`ComDual.genCoef_rho`).
* **`Com^¡` has dimension `(n - 1)!` in every arity `n ≥ 2`** (`ComDual.finrank_dual_com`), by
  `ShuffleBarSym.dualKDEquiv`.

The kernel of `ComDual.rho` is computed in `Operad/ComShuffle.lean` and `Operad/ComKernel.lean`.
-/
import Operad.LieTwisting

universe u

namespace Operad

open Sym GerBV
open scoped TensorProduct

namespace ComDual

open SymPresComLie SymPresB LTree ComBin

variable (K : Type u) [Field K]

/-! ## `Ass` onto `Com`: the symmetrization of the generators -/

/-- **The generators of `Ass` onto the generators of `Com`**: a function on the numberings of two
inputs to its symmetrization. Both products go to the commutative product. -/
def jCom : GrSpeciesHom K (Reg2 K) (ECom K) where
  app A _ _ :=
    { toFun := fun g =>
        ⟨fun e => g.val e.symm + g.val (e.trans (Equiv.swap 0 1)).symm, fun e => by
          show g.val (e.trans (Equiv.swap 0 1)).symm
              + g.val ((e.trans (Equiv.swap 0 1)).trans (Equiv.swap 0 1)).symm
            = g.val e.symm + g.val (e.trans (Equiv.swap 0 1)).symm
          have h : (e.trans (Equiv.swap (0 : Fin 2) 1)).trans (Equiv.swap 0 1) = e :=
            Equiv.ext fun a => by simp
          rw [h, add_comm]⟩
      map_add' := fun g g' => Subtype.ext (funext fun e => by
        show (g.val e.symm + g'.val e.symm)
            + (g.val (e.trans (Equiv.swap 0 1)).symm + g'.val (e.trans (Equiv.swap 0 1)).symm)
          = (g.val e.symm + g.val (e.trans (Equiv.swap 0 1)).symm)
            + (g'.val e.symm + g'.val (e.trans (Equiv.swap 0 1)).symm)
        ring)
      map_smul' := fun a g => Subtype.ext (funext fun e => by
        show a * g.val e.symm + a * g.val (e.trans (Equiv.swap 0 1)).symm
          = a * (g.val e.symm + g.val (e.trans (Equiv.swap 0 1)).symm)
        ring) }
  app_map _ _ := rfl
  app_par b g := by
    cases b
    · rfl
    · exact Subtype.ext (funext fun e => by
        show (0 : K) + 0 = 0
        ring)

lemma jCom_val {A : Type} [Fintype A] [DecidableEq A] (g : Reg2 K A) (e : A ≃ Fin 2) :
    ((jCom K).app A g).1 e = g.val e.symm + g.val (e.trans (Equiv.swap 0 1)).symm := rfl

/-- **Half of the inclusion of the symmetric functions**, a section of `jCom`. -/
noncomputable def sCom : GrSpeciesHom K (ECom K) (Reg2 K) where
  app A _ _ :=
    { toFun := fun f => (show Reg2 K A from fun τ : Fin 2 ≃ A => (2 : K)⁻¹ * f.1 τ.symm)
      map_add' := fun f f' => funext fun τ => by
        show (2 : K)⁻¹ * (f.1 τ.symm + f'.1 τ.symm)
          = (2 : K)⁻¹ * f.1 τ.symm + (2 : K)⁻¹ * f'.1 τ.symm
        ring
      map_smul' := fun a f => funext fun τ => by
        show (2 : K)⁻¹ * (a * f.1 τ.symm) = a * ((2 : K)⁻¹ * f.1 τ.symm)
        ring }
  app_map _ _ := rfl
  app_par b f := by
    cases b
    · rfl
    · exact funext fun τ => by
        show (2 : K)⁻¹ * (0 : K) = 0
        ring

lemma sCom_val {A : Type} [Fintype A] [DecidableEq A] (f : ECom K A) (τ : Fin 2 ≃ A) :
    ((sCom K).app A f).val τ = (2 : K)⁻¹ * f.1 τ.symm := rfl

/-! ## The models in the commutative algebra `K` -/

/-- **The evaluation of `Ass` in the commutative algebra `K`.** -/
noncomputable def φK : GrOperadHom K (FreeGrL K (Reg2 K)) (SymGr (EndOp K K)) :=
  model (LinearMap.mul K K)

/-- **The evaluation of `Com` in the commutative algebra `K`.** -/
noncomputable def ψK : GrOperadHom K (FreeGrL K (ECom K)) (SymGr (EndOp K K)) :=
  (φK K).comp (FreeGrL.mapSp (sCom K))

/-! ## The relations of `Ass` go to the relations of `Com` -/

/-- The value of a tree commutes with a map compatible with the binary operations. -/
lemma lev_map {G : Type} {V V' : Type*} (f : V' → V) (μ' : G → V' → V' → V') (μ₀ : G → V → V → V)
    (hf : ∀ g x y, f (μ' g x y) = μ₀ g (f x) (f y)) (v : ℕ → V') :
    ∀ t : LTree G, f (lev μ' v t) = lev μ₀ (fun a => f (v a)) t
  | .leaf _ => rfl
  | .node g l r => by
    show f (μ' g (lev μ' v l) (lev μ' v r)) = μ₀ g (lev μ₀ _ l) (lev μ₀ _ r)
    rw [hf, lev_map f μ' μ₀ hf v l, lev_map f μ' μ₀ hf v r]

/-- **An identity of the free associative algebra holds in the commutative algebra `K`.** -/
theorem φK_eq_zero {x : FreeGrL K (Reg2 K) (Fin 3)}
    (hx : (SymPresAss.φ K).app (Fin 3) x = 0) : (φK K).app (Fin 3) x = 0 := by
  refine (SymPresB.eq_zero_iff _).2 fun w => ?_
  have hsum := (ShuffleBarSym.tBasis (SymPresAss.c K) (SymPresAss.hc K) (Fin 3)).sum_repr x
  rw [← hsum] at hx ⊢
  have h1 := (SymPresB.eq_zero_iff _).1 hx (fun i => algebraMap K (SymPresAss.V K) (w i))
  rw [sgEv_app_sum (SymPresAss.c K) (SymPresAss.hc K) (SymPresAss.φ K)] at h1
  rw [sgEv_app_sum (SymPresAss.c K) (SymPresAss.hc K) (φK K)]
  have hμ : ∀ (g : AssShGen 2) (x y : K), algebraMap K (SymPresAss.V K)
      (μ (SymPresAss.c K) (φK K) g x y)
        = μ (SymPresAss.c K) (SymPresAss.φ K) g (algebraMap K (SymPresAss.V K) x)
          (algebraMap K (SymPresAss.V K) y) := fun g x y => by
    rw [φK, SymPresAss.φ, μ_model, μ_model]
    simp only [LinearMap.mul_apply', map_add, smul_eq_mul, map_mul, Algebra.smul_def]
  refine (algebraMap K (SymPresAss.V K)).injective ?_
  rw [map_zero, map_sum, ← h1]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_eq_mul, map_mul, ← Algebra.smul_def,
    lev_map (algebraMap K (SymPresAss.V K)) _ _ hμ]
  congr 2
  funext a
  unfold ext3
  split_ifs
  · rfl
  · exact map_zero _

variable [CharZero K]

/-- **The evaluation of `Ass` in `K` factors through the symmetrization.** -/
theorem ψK_mapSp : (ψK K).comp (FreeGrL.mapSp (jCom K)) = φK K := by
  refine FreeGrL.hom_ext fun A _ _ g => ?_
  show (φK K).app A ((FreeGrL.mapSp (sCom K)).app A ((FreeGrL.mapSp (jCom K)).app A
    ((FreeGrL.ι K (Reg2 K)).app A g))) = _
  rw [FreeGrL.mapSp_ι, FreeGrL.mapSp_ι, φK, model, FreeGrL.homEquiv_symm_ι,
    FreeGrL.homEquiv_symm_ι]
  refine MultilinearMap.ext fun w => ?_
  show sgEv (modelApp (LinearMap.mul K K) A ((sCom K).app A ((jCom K).app A g))) w
    = sgEv (modelApp (LinearMap.mul K K) A g) w
  rw [sgEv_modelApp, sgEv_modelApp]
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hsw : ∑ τ : Fin 2 ≃ A, g.val ((Equiv.swap 0 1).trans τ) • (w (τ 0) * w (τ 1))
      = ∑ τ : Fin 2 ≃ A, g.val τ • (w (τ 0) * w (τ 1)) := by
    refine Fintype.sum_equiv ⟨fun τ => (Equiv.swap 0 1).trans τ,
      fun τ => (Equiv.swap 0 1).trans τ, fun τ => by ext; simp, fun τ => by ext; simp⟩ _ _
        fun τ => ?_
    show g.val ((Equiv.swap 0 1).trans τ) • (w (τ 0) * w (τ 1))
      = g.val ((Equiv.swap 0 1).trans τ) • (w (τ (Equiv.swap 0 1 0)) * w (τ (Equiv.swap 0 1 1)))
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm (w (τ 1))]
  have hterm : ∀ τ : Fin 2 ≃ A, ((sCom K).app A ((jCom K).app A g)).val τ •
      (LinearMap.mul K K (w (τ 0)) (w (τ 1)))
        = (2 : K)⁻¹ * (g.val τ • (w (τ 0) * w (τ 1))
          + g.val ((Equiv.swap 0 1).trans τ) • (w (τ 0) * w (τ 1))) := fun τ => by
    rw [sCom_val, jCom_val, Equiv.symm_symm]
    show (2 : K)⁻¹ * (g.val τ + g.val ((Equiv.swap 0 1).trans τ)) * (w (τ 0) * w (τ 1)) = _
    simp only [smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun τ _ => hterm τ, ← Finset.mul_sum, Finset.sum_add_distrib, hsw]
  simp only [LinearMap.mul_apply', smul_eq_mul]
  field_simp
  ring

/-- The commutative product of the model of `Com`. -/
lemma μ_ψK (g : ComGen 2) (x y : K) : μ (cCom K) (ψK K) g x y = x * y := by
  show sgEv ((φK K).app (Fin 2) ((FreeGrL.mapSp (sCom K)).app (Fin 2)
    ((FreeGrL.ι K (ECom K)).app (Fin 2) (cCom K 2 (.op g))))) ![x, y] = _
  rw [FreeGrL.mapSp_ι, φK, model, FreeGrL.homEquiv_symm_ι]
  show sgEv (modelApp (LinearMap.mul K K) (Fin 2) ((sCom K).app (Fin 2) (cCom K 2 (.op g))))
    ![x, y] = _
  rw [sgEv_modelApp]
  have huniv : (Finset.univ : Finset (Fin 2 ≃ Fin 2)) = {Equiv.refl _, Equiv.swap 0 1} := by
    decide
  have h1 : (cCom K 2 (.op g)).1 (Equiv.refl _) = 1 := by
    rw [cCom, BinSp.basis_op, BinSp.ofV_apply_refl]
    exact Module.Basis.singleton_apply _ _ _
  have h2 : (cCom K 2 (.op g)).1 (Equiv.swap 0 1) = 1 := by
    have h := (cCom K 2 (.op g)).2 (Equiv.refl _)
    rw [h1] at h
    exact h
  have h20 : (2 : K) ≠ 0 := two_ne_zero
  rw [huniv, Finset.sum_pair (by decide), sCom_val, sCom_val, Equiv.refl_symm, Equiv.symm_swap,
    h1, h2]
  simp only [LinearMap.mul_apply', smul_eq_mul, Equiv.refl_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- **The operations of arity three of `Com` vanishing in `K` are the relations.** -/
theorem mem_span_of_ψK {y : FreeGrL K (ECom K) (Fin 3)} (hy : (ψK K).app (Fin 3) y = 0) :
    y ∈ Submodule.span K (rCom K 3) := by
  have hsum := (ShuffleBarSym.tBasis (cCom K) (hcCom K) (Fin 3)).sum_repr y
  obtain ⟨a, ha⟩ : ∃ a : _ → K, a = fun t =>
      (ShuffleBarSym.tBasis (cCom K) (hcCom K) (Fin 3)).repr y t := ⟨_, rfl⟩
  have hsum' : ∑ t, a t • ShuffleBarSym.tBasis (cCom K) (hcCom K) (Fin 3) t = y := by
    rw [ha]
    exact hsum
  rw [← hsum'] at hy ⊢
  have h1 := (SymPresB.eq_zero_iff _).1 hy (fun _ => (1 : K))
  rw [sgEv_app_sum (cCom K) (hcCom K) (ψK K)] at h1
  have hlev : ∀ σ : LTree.Mono (ComGen 2) 3,
      lev (μ (cCom K) (ψK K)) (ext3 fun _ : Fin 3 => (1 : K)) σ.1 = 1 := fun σ => by
    rcases mono3_eq σ with h | h | h <;> rw [h] <;>
      simp [lcomb, tcomb, rcomb, lev, ext3, μ_ψK]
  simp only [hlev, smul_eq_mul, mul_one] at h1
  have haug : aug K 3 (ShuffleBarSym.coord3L (cCom K) (hcCom K)
      (∑ t, a t • ShuffleBarSym.tBasis (cCom K) (hcCom K) (Fin 3) t)) = 0 := by
    rw [map_sum, map_sum]
    simp only [map_smul, ShuffleBarSym.coord3L_tBasis, smul_eq_mul]
    rw [← h1]
    refine Fintype.sum_equiv monoEquiv _ _ fun t => ?_
    rw [aug_vecOf (by simp), mul_one, Equiv.symm_apply_apply]
  have hmem : ShuffleBarSym.coord3L (cCom K) (hcCom K)
      (∑ t, a t • ShuffleBarSym.tBasis (cCom K) (hcCom K) (Fin 3) t)
        ∈ ShuffleBarSym.Rsh (cCom K) (hcCom K) (rCom K) := by
    rw [rsh_com]
    exact haug
  have h3 : ShuffleBarSym.coord3L (cCom K) (hcCom K)
      (∑ t, a t • ShuffleBarSym.tBasis (cCom K) (hcCom K) (Fin 3) t)
        ∈ (Submodule.span K (rCom K 3)).map (ShuffleBarSym.coord3L (cCom K) (hcCom K)) := by
    rw [Submodule.map_span]
    exact hmem
  obtain ⟨y', hy', he⟩ := Submodule.mem_map.1 h3
  have hinj : y' = ∑ t, a t • ShuffleBarSym.tBasis (cCom K) (hcCom K) (Fin 3) t :=
    (ShuffleBarSym.tBasis (cCom K) (hcCom K) (Fin 3)).repr.injective
      (Finsupp.ext fun t => congrFun he (monoEquiv t))
  exact hinj ▸ hy'

/-- **The relators of `Ass` go to relations of `Com`.** -/
theorem jCom_rel (n : ℕ) (x : FreeGrL K (Reg2 K) (Fin n)) (hx : x ∈ SymPresAss.rel K n) :
    (FreeGrL.mapSp (jCom K)).app (Fin n) x ∈ (GrOperadIdeal.span K (rCom K)).sub (Fin n) := by
  obtain ⟨rfl, hx⟩ := hx
  have h1 : (ψK K).app (Fin 3) ((FreeGrL.mapSp (jCom K)).app (Fin 3) x) = 0 :=
    (congrArg (fun F : GrOperadHom K (FreeGrL K (Reg2 K)) (SymGr (EndOp K K)) =>
      F.app (Fin 3) x) (ψK_mapSp K)).trans (φK_eq_zero K hx)
  exact (Submodule.span_le.2 fun z hz => GrOperadIdeal.subset_span 3 hz :
    Submodule.span K (rCom K 3) ≤ (GrOperadIdeal.span K (rCom K)).sub (Fin 3))
      (mem_span_of_ψK K h1)

/-- **The morphism `Ass^¡ → Com^¡`** of Koszul dual cooperads induced by the symmetrization. -/
noncomputable def toCom :
    GrCooperadHom K (Koszul.Dual K (Reg2 K) (SymPresAss.rel K))
      (Koszul.Dual K (ECom K) (rCom K)) :=
  Koszul.dualMap (SymPresAss.rel K) (rCom K) (jCom K)
    (Koszul.mapSp_mem_span (SymPresAss.rel K) (rCom K) (jCom K) (jCom_rel K))

/-- **The signed linear orders onto `Com^¡`.** -/
noncomputable def rho : GrCooperadHom K (OrdCo K) (Koszul.Dual K (ECom K) (rCom K)) :=
  (toCom K).comp (OrdCo.toDual K)

/-- **The Koszul dual cooperad of `Com` has dimension `(n - 1)!` in every arity `n ≥ 2`.** -/
theorem finrank_dual_com {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank K (Koszul.Dual K (ECom K) (rCom K) (Fin n)) = (n - 1).factorial :=
  (ShuffleBarSym.dualKDEquiv (cCom K) (hcCom K) (rCom K) (rCom_hr3 K) (rCom_hrS K)
    hn).finrank_eq.trans (by
      rw [rsh_com, ← ShuffleBar.finrank_quotient_dualRel _ hn]
      exact ComBin.finrank_quotient_dualRel K hn)

/-- The generators of `rho`: the symmetrization of the orders on two inputs. -/
lemma genCoef_rho {A : Type} [Fintype A] [DecidableEq A] (y : OrdCo K A) :
    FreeGrL.genCoef K (GrSpecies.Shift (ECom K) K) A
        ((Koszul.dualSub K (ECom K) (rCom K)).incl A ((rho K).app A y))
      = (jCom K).app A ((OrdCo.gen K).app A y) := by
  exact (FreeGrL.genCoef_mapSp (Koszul.shiftHom (jCom K)) ((OrdCo.toCut K).app A y)).trans
    (congrArg ((jCom K).app A) (OrdCo.genCoef_toCut K y))

end ComDual

end Operad
