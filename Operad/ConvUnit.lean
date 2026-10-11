/-
# Products with families supported in arity one

Let `C` be a graded cooperad and `Q` a graded operad. An invariant family `G` of the convolution
operad of `C` and `Q` **supported in arity one**, `G(x) = ε(x) g₀` for a fixed `g₀ ∈ Q(1)`, acts
on the left of the convolution product through `g₀` alone (`GrOperad.Inv.star_counit_left`):

  `(G ⋆ q)(c) = g₀ ∘ q(c)`,

the only term of the product being the one plugging all of `c` into `g₀`, by the left counit law
of `C`. For `g₀ = 1` this is the left unit law of the convolution product
(`GrOperad.Inv.oneInv_star`).
-/
import Operad.InvPreLie
import Operad.ConvOperad

universe u v w

namespace Operad

open Sym GerBV ConvOp
open scoped TensorProduct

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

namespace GrOperad.Inv

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The unique input of the outer operation of the splitting by all the inputs. -/
def univOut : Unit ≃ SOut (Finset.univ : Finset X) where
  toFun _ := none
  invFun _ := ()
  left_inv _ := rfl
  right_inv o := by
    rcases o with _ | ⟨x, hx⟩
    · rfl
    · exact absurd (Finset.mem_univ x) hx

/-- The counit vanishes on odd cooperations. -/
lemma counit_tw (e : Bool) (x : C Unit) :
    GrCooperad.counit (R := R) (GrSpecies.tw (R := R) e x) = GrCooperad.counit (R := R) x := by
  have h := LinearMap.congr_fun (GrCooperad.counit_par (R := R) (C := C)) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [GrSpecies.tw_apply, map_add, map_smul, h, smul_zero, add_zero]
  have h' := congrArg (GrCooperad.counit (R := R) (C := C)) (GrSpecies.par_add (R := R) x)
  rwa [map_add, h, add_zero] at h'

omit [Fintype X] [DecidableEq X] in
lemma qmap_congr {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {e e' : A ≃ B} (h : ∀ a, e a = e' a) (x : Q A) :
    GrOperad.map (R := R) e x = GrOperad.map (R := R) e' x := by
  rw [Equiv.ext h]

omit [DecidableEq X] in
lemma card_sOut_ne {S : Finset X} (hS : S ≠ Finset.univ) : IsEmpty (Unit ≃ SOut S) := by
  obtain ⟨x, -, hx⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.2 hS)
  refine ⟨fun e => ?_⟩
  have h1 : e.symm none = e.symm (some ⟨x, hx⟩) := Subsingleton.elim _ _
  exact Option.some_ne_none _ (e.symm.injective h1).symm

/-- **A product with a family supported in arity one on the left.** -/
theorem star_counit_left (G q : Inv R (ConvOp R C Q)) (g₀ : Q Unit)
    (hG : ∀ (A : Type) [Fintype A] [DecidableEq A] (e : Unit ≃ A) (x : C A),
      toLin (G.1 A) x = GrCooperad.counit (R := R) (SymSpecies.map (R := R) e.symm x)
        • GrOperad.map (R := R) e g₀)
    (hG0 : ∀ (A : Type) [Fintype A] [DecidableEq A], IsEmpty (Unit ≃ A) → G.1 A = 0)
    {p : Bool} (hq : IsPar p q) [Nonempty X] (c : C X) :
    toLin ((star R _ G q).1 X) c
      = GrOperad.map (R := R) (leftUnitEquiv X) (GrOperad.comp (R := R) () g₀ (toLin (q.1 X) c))
    := by
  rw [star_apply, toLin_sum, LinearMap.coe_sum, Finset.sum_apply,
    Finset.sum_eq_single (Finset.univ : Finset X)]
  · -- the term plugging all of `c` into `g₀`
    set U : Finset X := Finset.univ
    have hq' : IsParC p (q.1 (SIn U)) := parC_eq_self_iff.1 (hq _)
    show GrOperad.map (R := R) (splitEquiv U) (mu none (kap (G.1 (SOut U)) (q.1 (SIn U))
      (GrCooperad.decomp (R := R) none (SymSpecies.map (R := R) (splitEquiv U).symm c)))) = _
    rw [kap_hom _ hq']
    set v := SymSpecies.map (R := R) (splitEquiv U).symm c
    -- move the decomposition to the standard left unit
    have hd := LinearMap.congr_fun (GrCooperad.decomp_map (R := R) (C := C) (univOut (X := X))
      (Equiv.refl (SIn U)) ()) (SymSpecies.map (R := R)
        (compEquiv (univOut (X := X)) (Equiv.refl (SIn U)) ()).symm v)
    simp only [LinearMap.comp_apply, ← SymSpecies.map_trans, Equiv.symm_trans_self,
      SymSpecies.map_refl] at hd
    erw [hd]
    set v₀ := SymSpecies.map (R := R) (compEquiv (univOut (X := X)) (Equiv.refl (SIn U)) ()).symm v
    have hcl := LinearMap.congr_fun (GrCooperad.counit_left (R := R) (C := C) (B := SIn U))
      (SymSpecies.map (R := R) (leftUnitEquiv (SIn U)) v₀)
    simp only [LinearMap.comp_apply, ← SymSpecies.map_trans, Equiv.self_trans_symm,
      SymSpecies.map_refl, LinearEquiv.coe_coe, LinearMap.id_apply] at hcl
    -- the composite as a linear map of the tensor
    have key : ∀ t : C Unit ⊗[R] C (SIn U),
        mu (R := R) none (TensorProduct.map (toLin (G.1 (SOut U)) ∘ₗ GrSpecies.tw (R := R) p)
          (toLin (q.1 (SIn U))) (TensorProduct.map (SymSpecies.map (R := R) (univOut (X := X)))
            (SymSpecies.map (R := R) (Equiv.refl (SIn U))) t))
        = GrOperad.map (R := R) (compEquiv (univOut (X := X)) (Equiv.refl (SIn U)) ())
            (GrOperad.comp (R := R) () g₀ (toLin (q.1 (SIn U))
              (TensorProduct.lid R (C (SIn U))
                (LinearMap.rTensor (C (SIn U)) (GrCooperad.counit (R := R)) t)))) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero]
        try rfl
      | tmul x y =>
        simp only [TensorProduct.map_tmul, LinearMap.comp_apply, mu_tmul,
          LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, SymSpecies.map_refl]
        rw [← GrSpecies.map_tw, hG _ (univOut (X := X)), ← SymSpecies.map_trans, Equiv.self_trans_symm,
          SymSpecies.map_refl, counit_tw, LinearMap.map_smul₂, GrOperad.map_comp,
          GrOperad.map_refl]
        rfl
      | add a b ha hb =>
        simp only [map_add, ha, hb]
        try rfl
    rw [key, hcl]
    -- relabel `q`
    have hqmap : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
        (τ : A ≃ B) (x : C A), toLin (q.1 B) (SymSpecies.map (R := R) τ x)
          = GrOperad.map (R := R) τ (toLin (q.1 A) x) := fun {A B} _ _ _ _ τ x => by
      rw [← map_apply q τ]
      show GrOperad.map (R := R) τ (toLin (q.1 A) (SymSpecies.map (R := R) τ.symm _)) = _
      rw [← SymSpecies.map_trans, Equiv.self_trans_symm, SymSpecies.map_refl]
    simp only [v₀, v, ← SymSpecies.map_trans]
    rw [hqmap, comp_map_right]
    erw [hqmap (splitEquiv U).symm c]
    erw [comp_map_right]
    simp only [← GrOperad.map_trans]
    erw [← GrOperad.map_trans]
    apply qmap_congr
    intro z
    rcases z with ⟨a, ha⟩ | x
    · exact absurd (Subsingleton.elim a ()) ha
    · have hx : (splitEquiv U).symm x = Sum.inr ⟨x, Finset.mem_univ x⟩ :=
        (Equiv.symm_apply_eq _).2 rfl
      erw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, compEquiv_inr,
        Equiv.refl_apply, Equiv.trans_apply, hx]
      rfl
  · intro S _ hS
    have h0 := hG0 _ (card_sOut_ne hS)
    show GrOperad.map (R := R) (splitEquiv S) (mu none (kap (G.1 (SOut S)) (q.1 (SIn S))
      (GrCooperad.decomp (R := R) none (SymSpecies.map (R := R) (splitEquiv S).symm c)))) = 0
    rw [h0]
    simp [kap]
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.univ_nonempty⟩) h

end GrOperad.Inv

end Operad
