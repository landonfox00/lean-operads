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
of the operad presented by the Koszul dual relators (`ShuffleBar.finrank_quotient_dualRel`).

**The embedding is onto** (`ShuffleBarSym.dualKD_surjective`, `ShuffleBarSym.dualKDEquiv`): a top
chain whose differential lies in `ShuffleBar.J` has only binary vertices, so it is the image of
an element of the cut cooperad (`ShuffleBarSym.freeGen_ret`, `FreeGrL.mapSp_eq_of_top`), which is
a cycle of `B(P, Ī_P)`, hence in `P^¡` (`ShuffleBarSym.cutCyc_le`).
-/
import Operad.ShuffleBarJ
import Operad.ShuffleKoszulOperad
import Operad.KoszulInhom
import Operad.ShuffleBarTop

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

omit [CharZero K] in
/-- No suspended operations of `Ī` with at most one input. -/
lemma freeGen_red (B : Type) [Fintype B] [DecidableEq B] (hB : Fintype.card B ≤ 1)
    (v : BarGen (Ibar K E c hc) B) : v = 0 :=
  IdealSp.ext _ (by
    have h := IdealSp.mem _ v
    rwa [GrOperadIdeal.atLeastTwo_sub_of_lt (by omega), Submodule.mem_bot] at h)

/-- **`sĪ → sE → sĪ` is the identity with at most two inputs**, for relators with at least three
inputs: the binary operations of the free operad are its generators. -/
lemma freeGen_ret (hr2 : ∀ n, n < 3 → r n = ∅) {B : Type} [Fintype B] [DecidableEq B]
    (hB : Fintype.card B ≤ 2) (w : BarGen (Ibar K E c hc) B) :
    (freeGen c hc).app B ((barRet c hc r hr2).app B ((barProjGen c hc r).app B w)) = w := by
  refine IdealSp.ext _ ?_
  have h1 : (barProjGen c hc r).app B ((freeGen c hc).app B
      ((barRet c hc r hr2).app B ((barProjGen c hc r).app B w)))
      = (barProjGen c hc r).app B w := by
    rw [barProjGen_freeGen]
    exact barGen_barRet c hc r hr2 hB _
  have h2 := congrArg (IdealSp.val _) h1
  rw [val_barProjGen, val_barProjGen] at h2
  have h3 : IdealSp.val _ ((freeGen c hc).app B
      ((barRet c hc r hr2).app B ((barProjGen c hc r).app B w))) - IdealSp.val _ w
      ∈ (GrOperadIdeal.span K r).sub B := by
    rw [← GrOperadIdeal.proj_eq_zero_iff, map_sub, h2, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_mem_span c hc r hr2 hB h3)

/-- **Every top cycle of the shuffle bar complex modulo the relators comes from the Koszul dual
cooperad**: such a chain has only binary vertices, so it is the image of an element of the cut
cooperad, which is a cycle of `B(P, Ī_P)`, hence in `P^¡`. -/
theorem dualKD_surjective (hr3 : ∀ n ≠ 3, r n = ∅)
    (hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ r 3,
      GrOperad.map (R := K) σ x ∈ Submodule.span K (r 3)) {n : ℕ} (hn : 2 ≤ n)
    {v : BarTree G →₀ K} (hv : v ∈ ShuffleBar.KD K (Rsh c hc r) n) :
    ∃ x, dualKD c hc r n x = v := by
  have hr2 : ∀ n, n < 3 → r n = ∅ := fun n hn => hr3 n (by omega)
  obtain ⟨hvC, hvJ⟩ := Submodule.mem_inf.1 hv
  obtain ⟨y, hy, rfl⟩ := (SetLike.ext_iff.1 (map_ΦL_deg c hc hn (n - 1)) v).2 hvC
  rw [deg_eq_vx] at hy
  have hdy : Bar.d (Ibar K E c hc) (Fin n) y ∈ (Krel K E c hc r).sub (Fin n) := by
    have h1 : ΦL c hc n (Bar.d (Ibar K E c hc) (Fin n) y)
        ∈ ShuffleBar.J K (Rsh c hc r) ⊓ Finsupp.supported K K (barSet G n) :=
      Submodule.mem_inf.2 ⟨(ΦL_d c hc y) ▸ hvJ, (ΦL_range c hc n) ▸ ⟨_, rfl⟩⟩
    obtain ⟨k, hk, hk'⟩ := (SetLike.ext_iff.1 (map_ΦL_Krel c hc hr3 hrS n) _).2 h1
    rwa [← ΦL_injective c hc n hk']
  have hyy : (FreeGrL.mapSp (freeGen c hc)).app (Fin n)
      ((FreeGrL.mapSp ((barRet c hc r hr2).comp (barProjGen c hc r))).app (Fin n) y) = y := by
    rw [FreeGrL.mapSp_comp]
    exact (FreeGrL.mapSp_eq_of_top (freeGen_red c hc)
      (g' := (GrSpEnd.id K (BarGen (Ibar K E c hc))).toHom)
      (fun B _ _ hB w => freeGen_ret c hc r hr2 hB w)
      (by rw [Fintype.card_fin]; omega) (by rw [Fintype.card_fin]; exact hy)).trans
      (FreeGrL.mapSp_id y)
  have e1 : (FreeGrL.mapSp (Koszul.barGen (Ipres K E c hc r) (hE_pres c hc r))).app (Fin n)
      ((FreeGrL.mapSp ((barRet c hc r hr2).comp (barProjGen c hc r))).app (Fin n) y)
      = (FreeGrL.mapSp (barProjGen c hc r)).app (Fin n) y :=
    ((FreeGrL.mapSp_comp _ _ _).trans
      (FreeGrL.mapSp_congr (fun A _ _ w => barProjGen_freeGen c hc r A w) _)).symm.trans
      (congrArg _ hyy)
  have hu : (FreeGrL.mapSp ((barRet c hc r hr2).comp (barProjGen c hc r))).app (Fin n) y
      ∈ (cutCyc K E c hc r hr2).sub (Fin n) :=
    LinearMap.mem_ker.2 ((congrArg (Bar.d (Ipres K E c hc r) (Fin n)) e1).trans
      ((barProj_d c hc r y).symm.trans ((mem_Krel_iff c hc r _).1 hdy)))
  exact ⟨⟨_, cutCyc_le c hc r hr2 (Fin n) hu⟩, congrArg (ΦL c hc n) hyy⟩

/-- **The Koszul dual cooperad is the top homology of the shuffle bar complex**, in every arity
`n ≥ 2`, for binary quadratic data with relators of arity three stable under the permutations,
over a field of characteristic zero. -/
noncomputable def dualKDEquiv (hr3 : ∀ n ≠ 3, r n = ∅)
    (hrS : ∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ r 3,
      GrOperad.map (R := K) σ x ∈ Submodule.span K (r 3)) {n : ℕ} (hn : 2 ≤ n) :
    Koszul.Dual K E r (Fin n) ≃ₗ[K] ShuffleBar.KD K (Rsh c hc r) n :=
  LinearEquiv.ofBijective ((dualKD c hc r n).codRestrict _ (dualKD_mem c hc r hr3 hrS hn))
    ⟨fun x y h => dualKD_injective c hc r (fun n hn => hr3 n (by omega)) n (by
        have h' : (((dualKD c hc r n).codRestrict _ (dualKD_mem c hc r hr3 hrS hn)) x :
            BarTree G →₀ K)
            = ((dualKD c hc r n).codRestrict _ (dualKD_mem c hc r hr3 hrS hn)) y :=
          congrArg _ h
        exact h'),
      fun v => by
        obtain ⟨x, hx⟩ := dualKD_surjective c hc r hr3 hrS hn v.2
        exact ⟨x, Subtype.ext hx⟩⟩

end ShuffleBarSym

end Operad
