/-
# The Koszul dual cooperad in the top homology of the shuffle bar complex

For binary quadratic data `(E, r)` with an even basis of the generators, relators of arity three
stable under the permutations, over a field of characteristic zero, **the Koszul dual cooperad
`P^¡(Fin n)` embeds in the top homology `ShuffleBar.KD K R n` of the shuffle bar complex** of the
shuffle relators `R = Rsh c hc r`, in every arity `n ≥ 2` (`ShuffleBarSym.dualKD`,
`ShuffleBarSym.dualKD_injective`, `ShuffleBarSym.dualKD_mem`): the inclusion into the cut
cooperad `T^c(sE)`, the morphism of cut cooperads `T^c(sE) → B(T, Ī)` induced by the suspended
generators (`ShuffleBarSym.freeGen`), and the comparison `ΦL`. An element of `P^¡` has `n - 1`
vertices, its image in `B(P, Ī_P)` is a cycle (`Koszul.d_toBar`), so the differential of its
image in `B(T, Ī)` lies in the relator ideal, which `ΦL` carries onto `ShuffleBar.J`
(`ShuffleBarSym.map_ΦL_Krel`).

Hence `dim P^¡(Fin n) ≤ dim ShuffleBar.KD K R n` (`ShuffleBarSym.finrank_dual_le`), the dimension
of the operad presented by the Koszul dual relators (`ShuffleBar.finrank_quotient_dualRel`). The
converse inequality is not proved here in general; for `Ass` it follows from the cooperad of
signed linear orders (`Operad/OrdDual.lean`).
-/
import Operad.ShuffleBarJ
import Operad.ShuffleKoszulOperad
import Operad.KoszulInhom

universe u

namespace Operad

open Function Sym GerBV STree
open scoped TensorProduct

namespace ShuffleBarSym

open LTree ShuffleBar

variable {K : Type u} [Field K] {E : (A : Type) → [Fintype A] → [DecidableEq A] → Type u}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (E A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module K (E A)] [GrSpecies K E]
  {G : Type} [Fintype G] [DecidableEq G]
  (c : ∀ k, Module.Basis (BinGen G k) K (E (Fin k)))
  (hc : ∀ k (β : BinGen G k), GrSpecies.par (R := K) false (c k β) = c k β)
  (r : ∀ n : ℕ, Set (FreeGrL K E (Fin n)))
  (hr2 : ∀ n, n < 3 → r n = ∅)

local notation "𝒥" => GrOperadIdeal.span K r

include c in
/-- The generators lie in the augmentation ideal of the free operad. -/
lemma ι_mem_Ibar (A : Type) [Fintype A] [DecidableEq A] (v : E A) :
    (FreeGrL.ι K E).app A v ∈ (Ibar K E c hc).sub A := by
  by_cases h : 2 ≤ Fintype.card A
  · rw [GrOperadIdeal.atLeastTwo_sub_of_le h]
    trivial
  · rw [hEred c A (by omega) v, map_zero]
    exact zero_mem _

/-- **The suspended generators** `sE → sĪ`, in the suspended augmentation ideal of the free
operad. -/
noncomputable def freeGen : GrSpeciesHom K (GrSpecies.Shift E K) (BarGen (Ibar K E c hc)) where
  app A _ _ := ((FreeGrL.ι K E).app A).codRestrict ((Ibar K E c hc).sub A) (ι_mem_Ibar c hc A)
  app_map {A B} _ _ _ _ σ' w := IdealSp.ext _ (by
    show (FreeGrL.ι K E).app B (SymSpecies.map (R := K) (V := E) σ' w)
      = GrOperad.map (R := K) σ' ((FreeGrL.ι K E).app A w)
    rw [(FreeGrL.ι K E).app_map, FreeGrL.symMap_eq])
  app_par {A} _ _ b w := IdealSp.ext _ (by
    show (FreeGrL.ι K E).app A (GrSpecies.par (R := K) (V := E) (!b) w)
      = GrOperad.par (R := K) (!b) ((FreeGrL.ι K E).app A w)
    rw [(FreeGrL.ι K E).app_par, FreeGrL.grPar_eq])

/-- The suspended generators of the free operad project onto those of the presented operad. -/
lemma barProjGen_freeGen (A : Type) [Fintype A] [DecidableEq A] (w : GrSpecies.Shift E K A) :
    (barProjGen c hc r).app A ((freeGen c hc).app A w)
      = (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r)).app A w :=
  IdealSp.ext _ rfl

/-- **The Koszul dual cooperad in the shuffle bar complex**: the inclusion into the cut cooperad,
the morphism of cut cooperads `T^c(sE) → B(T, Ī)`, and the comparison `ΦL`. -/
noncomputable def dualKD (n : ℕ) : Koszul.Dual K E r (Fin n) →ₗ[K] (BarTree G →₀ K) :=
  ΦL c hc n ∘ₗ (FreeGrL.mapSp (freeGen c hc)).app (Fin n) ∘ₗ (Koszul.dualSub K E r).incl (Fin n)

include hr2 in
theorem dualKD_injective (n : ℕ) : Function.Injective (dualKD c hc r n) := by
  have h1 : Function.Injective ((FreeGrL.mapSp (freeGen c hc)).app (Fin n)) :=
    FreeGrL.mapSp_injective_of_retraction (f := freeGen c hc)
      (g := (barRet c hc r hr2).comp (barProjGen c hc r)) fun A _ _ v => by
        show (barRet c hc r hr2).app A ((barProjGen c hc r).app A ((freeGen c hc).app A v)) = v
        rw [barProjGen_freeGen]
        exact barRet_barGen c hc r hr2 v
  intro x y h
  exact (Koszul.dualSub K E r).incl_injective (Fin n) (h1 (ΦL_injective c hc n h))

variable [CharZero K]

/-- **The image lies in the top homology of the shuffle bar complex** `ShuffleBar.KD`, for
relators of arity three stable under the permutations. -/
theorem dualKD_mem (hr3 : ∀ n ≠ 3, r n = ∅)
    (hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ r 3,
      GrOperad.map (R := K) σ x ∈ Submodule.span K (r 3)) {n : ℕ} (hn : 2 ≤ n)
    (x : Koszul.Dual K E r (Fin n)) :
    dualKD c hc r n x ∈ ShuffleBar.KD K (Rsh c hc r) n := by
  have hvx : (Koszul.dualSub K E r).incl (Fin n) x
      ∈ FreeGrL.vx K (GrSpecies.Shift E K) (n - 1) (Fin n) := by
    have h := FreeGrL.mem_vx_of_binary (R := K) (V := GrSpecies.Shift E K)
      (fun B _ _ hB v => gen_eq_zero c hB v) (by rw [Fintype.card_fin]; omega)
      ((Koszul.dualSub K E r).incl (Fin n) x)
    rwa [Fintype.card_fin] at h
  have hdeg : (FreeGrL.mapSp (freeGen c hc)).app (Fin n) ((Koszul.dualSub K E r).incl (Fin n) x)
      ∈ deg c hc n (n - 1) := by
    rw [deg_eq_vx]
    exact FreeGrL.mapSp_mem_vx hvx
  have hC : dualKD c hc r n x ∈ ShuffleBar.C (E := G) K n (n - 1) :=
    (SetLike.ext_iff.1 (map_ΦL_deg c hc hn (n - 1)) _).1 (Submodule.mem_map_of_mem hdeg)
  have e1 : (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n)
      ((FreeGrL.mapSp (freeGen c hc)).app (Fin n) ((Koszul.dualSub K E r).incl (Fin n) x))
      = (FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app (Fin n)
        ((Koszul.dualSub K E r).incl (Fin n) x) :=
    (FreeGrL.mapSp_comp _ _ _).trans
      (FreeGrL.mapSp_congr (fun A _ _ w => barProjGen_freeGen c hc r A w) _)
  have hk : Bar.d (Ibar K E c hc) (Fin n) ((FreeGrL.mapSp (freeGen c hc)).app (Fin n)
      ((Koszul.dualSub K E r).incl (Fin n) x)) ∈ (Krel K E c hc r).sub (Fin n) :=
    (mem_Krel_iff c hc r _).2 ((barProj_d c hc r _).trans
      ((congrArg (Bar.d (Ipres K E c hc r) (Fin n)) e1).trans
        (Koszul.d_toBar (Ipres K E c hc r) (hE_pres c hc r) (fun B _ _ hB y hy => by
          rwa [GrOperadIdeal.atLeastTwo_sub_of_lt (by omega), Submodule.mem_bot] at hy) x)))
  have h2 : ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n)
      ((FreeGrL.mapSp (freeGen c hc)).app (Fin n) ((Koszul.dualSub K E r).incl (Fin n) x)))
      ∈ ShuffleBar.J K (Rsh c hc r) ⊓ Finsupp.supported K K (barSet G n) :=
    (SetLike.ext_iff.1 (map_ΦL_Krel c hc hr3 hrS n) _).1 (Submodule.mem_map_of_mem hk)
  refine Submodule.mem_inf.2 ⟨hC, ?_⟩
  show ShuffleBar.d K (dualKD c hc r n x) ∈ ShuffleBar.J K (Rsh c hc r)
  exact (ΦL_d c hc _) ▸ h2.1

/-- **The dimension of the Koszul dual cooperad is at most that of the top homology of the
shuffle bar complex**, in every arity `n ≥ 2`. -/
theorem finrank_dual_le (hr3 : ∀ n ≠ 3, r n = ∅)
    (hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ r 3,
      GrOperad.map (R := K) σ x ∈ Submodule.span K (r 3)) {n : ℕ} (hn : 2 ≤ n)
    [FiniteDimensional K (ShuffleBar.KD K (Rsh c hc r) n)] :
    FiniteDimensional K (Koszul.Dual K E r (Fin n)) ∧
      Module.finrank K (Koszul.Dual K E r (Fin n))
        ≤ Module.finrank K (ShuffleBar.KD K (Rsh c hc r) n) := by
  have hr2 : ∀ n, n < 3 → r n = ∅ := fun n hn => hr3 n (by omega)
  obtain ⟨f, hf⟩ : ∃ f : Koszul.Dual K E r (Fin n) →ₗ[K] ShuffleBar.KD K (Rsh c hc r) n,
      ∀ x, (f x).1 = dualKD c hc r n x :=
    ⟨(dualKD c hc r n).codRestrict _ (dualKD_mem c hc r hr3 hrS hn), fun _ => rfl⟩
  have hinj : Function.Injective f := fun x y h =>
    dualKD_injective c hc r hr2 n ((hf x).symm.trans ((congrArg Subtype.val h).trans (hf y)))
  haveI : IsNoetherian K (ShuffleBar.KD K (Rsh c hc r) n) :=
    isNoetherian_of_isNoetherianRing_of_finite K (ShuffleBar.KD K (Rsh c hc r) n)
  exact ⟨Module.Finite.of_injective f hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩

end ShuffleBarSym

end Operad
