/-
# Twisted composite products with a dg operad

For a graded cooperad `C`, an augmented dg operad `P` and an odd invariant family `α` of the
convolution operad, the twisted composite product `C ∘_α P` is `C ∘ P` with the differential

  `D_α = d_α + (1 ∘' d_P)`

(`GrComposite.twDiff`), the twisted differential `d_α` (`GrComposite.twD`) and the differential
of `P` at the inner operations (`GrComposite.leafMap`). The twisted differential is odd
(`GrComposite.twD_par`); with the Leibniz rule for `1 ∘' d_P` against the action, its
anticommutator with `1 ∘' d_P` is again a morphism of right modules, the twisted differential of
`d_P ∘ α` (`GrComposite.twD_leaf_anticomm`), and `(1 ∘' d_P)²` vanishes (`GrComposite.leaf_sq`).
So **`D_α² = d_{α ⋆ α + d_P ∘ α}`, which vanishes for a twisting morphism**
(`GrComposite.twDiff_sq`).
-/
import Operad.GrTwisted
import Operad.GrLeafAct

universe u v w

namespace Operad

open Function Sym GerBV ConvOp

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]

namespace GrComposite

/-! ## Parities -/

section Par

variable [GrOperad R P] (ε : GrAug R P)

lemma isPar_corFam : GrOperad.Inv.IsPar false (corFam (C := C) ε) := fun A _ _ => by
  refine parC_eq_self_iff.2 fun b c => ?_
  show corLin ε A (GrSpecies.par (R := R) b c) = SqExt.parE (xor b false) (corLin ε A c)
  refine SqExt.ext ?_ ?_
  · show (0 : P A) = GrOperad.par (R := R) _ 0
    rw [map_zero]
  · show corolla R P A (GrSpecies.par (R := R) b c) = par R C P _ (corolla R P A c)
    rw [Bool.xor_false, par_corolla]

/-- **The extension of a homogeneous family shifts parities.** -/
theorem twF_par {F : GrOperad.Inv R (ConvOp R C (SqExt R C P ε))} {p : Bool} (hF : GrOperad.Inv.IsPar p F)
    {S : Type} [Fintype S] [DecidableEq S] (w : GrComposite R C P S) :
    ∀ b : Bool, twF ε F S (par R C P b w) = par R C P (xor b p) (twF ε F S w) := by
  refine induction_act (fun S _ _ w => ∀ b : Bool,
      twF ε F S (par R C P b w) = par R C P (xor b p) (twF ε F S w))
    (fun S _ _ b => by simp) (fun S _ _ x y hx hy b => by simp only [map_add, hx, hy])
    (fun S _ _ r x hx b => by simp only [map_smul, hx])
    (fun S S' _ _ _ _ σ x hx b => ?_) (fun S Y _ _ _ _ i z x hx b => ?_)
    (fun A _ _ c b => ?_) w
  · beta_reduce at hx ⊢
    rw [← map_par', twF_map, hx, twF_map, map_par']
  · beta_reduce at hx ⊢
    have hz : ∀ r : Bool, twF ε F _ (par R C P b (act R C i (GrOperad.par (R := R) r z) x))
        = par R C P (xor b p) (twF ε F _ (act R C i (GrOperad.par (R := R) r z) x)) := by
      intro r
      have hr := GrOperad.par_par_self (R := R) r z
      rw [par_act b i _ hr, twF_act, hx, twF_act, par_act _ i _ hr, Bool.xor_right_comm]
    have hadd : ∀ z z' : P Y, act R C i (z + z') = act R C i z + act R C i z' := fun z z' =>
      (actL R C i).map_add z z'
    rw [← GrOperad.par_add (R := R) z, hadd, LinearMap.add_apply, map_add, map_add, hz, hz,
      map_add, map_add]
  · rw [par_corolla, twF_corolla, twF_corolla, ← SqExt.snd_parE]
    congr 1
    exact (isParC_of_isPar hF A) b c

/-- **The twisted differential of a homogeneous family shifts parities.** -/
theorem twD_par {β : GrOperad.Inv R (ConvOp R C P)} {p : Bool} (hβ : GrOperad.Inv.IsPar p β)
    {S : Type} [Fintype S] [DecidableEq S] (b : Bool) (w : GrComposite R C P S) :
    twD ε β S (par R C P b w) = par R C P (xor b p) (twD ε β S w) := by
  have h := twF_par ε (GrOperad.Inv.isPar_star (isPar_corFam (C := C) ε) (isPar_liftFam ε hβ)) w b
  rwa [Bool.false_xor] at h

/-- **The twisted differential is additive in the family.** -/
theorem twD_add (β β' : GrOperad.Inv R (ConvOp R C P)) {S : Type} [Fintype S] [DecidableEq S]
    (w : GrComposite R C P S) : twD ε (β + β') S w = twD ε β S w + twD ε β' S w :=
  eq_of_corolla (fun S _ _ => twD ε (β + β') S) (fun S _ _ => twD ε β S + twD ε β' S)
    (fun S S' _ _ _ _ σ w => twF_map ε _ σ w)
    (fun S S' _ _ _ _ σ w => by simp only [LinearMap.add_apply, twD, twF_map, map_add])
    (fun S Y _ _ _ _ i z w => twF_act ε _ i z w)
    (fun S Y _ _ _ _ i z w => by simp only [LinearMap.add_apply, twD, twF_act, map_add])
    (fun A _ _ c => by
      rw [LinearMap.add_apply, twD_corolla, twD_corolla, twD_corolla, map_add, map_add]
      rfl)
    w

end Par

/-! ## The differential at the inner operations -/

section Leaf

variable [GrOperad R P] (D : GrDer (GrOperadHom.id R P) true)

variable (R C) in
/-- **An odd derivation of `P` at the inner operations** of `C ∘ P`. -/
noncomputable abbrev leafD (S : Type) [Fintype S] [DecidableEq S] :
    GrComposite R C P S →ₗ[R] GrComposite R C P S :=
  leafMap R C D.toSpEnd

lemma leafD_corolla {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    leafD R C D A (corolla R P A c) = 0 := by
  rw [corolla_apply, leafD, leafMap_mk]
  refine Finset.sum_eq_zero fun j _ => mk_of_y_eq_zero _ (a := j) ?_
  show leafLin _ _ j j _ = 0
  unfold leafLin
  rw [if_pos rfl]
  exact D.app_one

lemma leafD_act {S Y : Type} [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y] (i : S)
    (z : P Y) (w : GrComposite R C P S) :
    leafD R C D _ (act R C i z w)
      = act R C i z (leafD R C D S w)
        + act R C i (D.app Y z) (GrSpecies.tw (R := R) true w) :=
  leafMap_act _ i z w

lemma leafD_tw {S : Type} [Fintype S] [DecidableEq S] (w : GrComposite R C P S) :
    leafD R C D S (GrSpecies.tw (R := R) true w) = -GrSpecies.tw (R := R) true (leafD R C D S w)
    := by
  have h : ∀ b, leafD R C D S (GrSpecies.par (R := R) b w)
      = GrSpecies.par (R := R) (!b) (leafD R C D S w) := fun b => by
    have := par_leafMap (M := C) D.toSpEnd (xor b true) w
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Bool.xor_true] at this
    exact this.symm
  rw [GrSpecies.tw_apply, GrSpecies.tw_apply, map_add, map_smul, h, h, σ_true, neg_one_smul,
    neg_one_smul, Bool.not_false, Bool.not_true, neg_add, neg_neg, add_comm]

/-- **A differential at the inner operations squares to zero.** -/
theorem leaf_sq (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), D.app A (D.app A x) = 0)
    {S : Type} [Fintype S] [DecidableEq S] (w : GrComposite R C P S) :
    leafD R C D S (leafD R C D S w) = 0 :=
  eq_of_corolla (fun S _ _ => leafD R C D S ∘ₗ leafD R C D S) (fun S _ _ => 0)
    (fun S S' _ _ _ _ σ w => by simp only [LinearMap.comp_apply, ← leafMap_map])
    (fun S S' _ _ _ _ σ w => by simp)
    (fun S Y _ _ _ _ i z w => by
      simp only [LinearMap.comp_apply, leafD_act, map_add, leafD_tw, hD]
      rw [show act R C i (0 : P Y) = 0 from (actL R C i).map_zero, LinearMap.zero_apply,
        map_neg, add_zero]
      abel)
    (fun S Y _ _ _ _ i z w => by simp)
    (fun A _ _ c => by simp [leafD_corolla]) w

end Leaf

/-! ## The twisted composite product -/

section Total

variable [GrOperad R P] (ε : GrAug R P) (D : GrDer (GrOperadHom.id R P) true)

lemma tw_corolla {A : Type} [Fintype A] [DecidableEq A] (e : Bool) (c : C A) :
    GrSpecies.tw (R := R) e (corolla R P A c) = corolla R P A (GrSpecies.tw (R := R) e c) := by
  rw [GrSpecies.tw_apply, GrSpecies.tw_apply, map_add, map_smul]
  show par R C P false _ + _ • par R C P true _ = _
  rw [par_corolla, par_corolla]

lemma twD_tw {α : GrOperad.Inv R (ConvOp R C P)} (hα : GrOperad.Inv.IsPar true α) {S : Type}
    [Fintype S] [DecidableEq S] (w : GrComposite R C P S) :
    twD ε α S (GrSpecies.tw (R := R) true w) = -GrSpecies.tw (R := R) true (twD ε α S w) := by
  rw [GrSpecies.tw_apply, GrSpecies.tw_apply, map_add, map_smul]
  show twD ε α S (par R C P false w) + _ • twD ε α S (par R C P true w)
    = -(par R C P false (twD ε α S w) + _ • par R C P true (twD ε α S w))
  rw [twD_par ε hα, twD_par ε hα, σ_true, neg_one_smul, neg_one_smul, Bool.false_xor,
    Bool.true_xor, Bool.not_true, neg_add, neg_neg, add_comm]

/-- The derivative of a family, by a derivation of `P`. -/
noncomputable abbrev dFam (α : GrOperad.Inv R (ConvOp R C P)) : GrOperad.Inv R (ConvOp R C P) :=
  GrOperad.Inv.appDer (ConvOp.postDer (C := C) D) α

/-- **The differential at the inner operations on a product with the corollas.** -/
theorem leafD_snd_star {X : Type} [Fintype X] [DecidableEq X] {α : GrOperad.Inv R (ConvOp R C P)}
    (hα : GrOperad.Inv.IsPar true α) (c : C X) :
    leafD R C D X (SqExt.snd (toLin ((GrOperad.Inv.star R _ (corFam ε) (liftFam ε α)).1 X) c))
      = SqExt.snd (toLin ((GrOperad.Inv.star R _ (corFam ε) (liftFam ε (dFam D α))).1 X) c) := by
  rw [toLin_star, toLin_star, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [toLin_term, toLin_term, SqExt.map_def, SqExt.map_def, SqExt.snd_mapE, SqExt.snd_mapE,
    ← leafMap_map]
  congr 1
  generalize GrCooperad.decomp (R := R) (C := C) none
    (SymSpecies.map (R := R) (splitEquiv S).symm c) = t
  have hα' := isParC_of_isPar (isPar_liftFam ε hα) (SIn S)
  have hdα := isParC_of_isPar (isPar_liftFam ε (GrOperad.Inv.isPar_appDer
    (ConvOp.postDer (C := C) D) hα)) (SIn S)
  rw [kap_hom _ hα', kap_hom _ hdα]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, mu_tmul, LinearMap.comp_apply, SqExt.comp_def,
      SqExt.snd_compE, fst_corFam]
    rw [show toLin ((liftFam ε α).1 (SIn S)) y = (inclHom C ε).app _ (toLin (α.1 (SIn S)) y)
      from rfl, show toLin ((liftFam ε (dFam D α)).1 (SIn S)) y
        = (inclHom C ε).app _ (D.app _ (toLin (α.1 (SIn S)) y)) from rfl,
      fst_inclHom, fst_inclHom, snd_inclHom, snd_inclHom]
    simp only [map_zero, add_zero]
    rw [show ∀ v, SqExt.snd (toLin ((corFam (C := C) ε).1 (SOut S)) v) = corolla R P _ v
      from fun v => rfl, show SqExt.snd (toLin ((corFam (C := C) ε).1 (SOut S))
        (GrSpecies.tw (R := R) (xor true true) x)) = corolla R P _ _ from rfl, leafD_act, leafD_corolla, map_zero, zero_add, tw_corolla, GrSpecies.tw_tw, Bool.xor_self,
      GrSpecies.tw_false]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **The anticommutator of the twisted differential with the differential at the inner
operations** is the twisted differential of the derivative of the family. -/
theorem twD_leaf_anticomm {α : GrOperad.Inv R (ConvOp R C P)} (hα : GrOperad.Inv.IsPar true α)
    {S : Type} [Fintype S] [DecidableEq S] (w : GrComposite R C P S) :
    twD ε α S (leafD R C D S w) + leafD R C D S (twD ε α S w) = twD ε (dFam D α) S w :=
  eq_of_corolla (fun S _ _ => twD ε α S ∘ₗ leafD R C D S + leafD R C D S ∘ₗ twD ε α S)
    (fun S _ _ => twD ε (dFam D α) S)
    (fun S S' _ _ _ _ σ w => by
      simp only [LinearMap.add_apply, LinearMap.comp_apply, ← leafMap_map, twD, twF_map, map_add])
    (fun S S' _ _ _ _ σ w => twF_map ε _ σ w)
    (fun S Y _ _ _ _ i z w => by
      simp only [LinearMap.add_apply, LinearMap.comp_apply, leafD_act, map_add, twD, twF_act]
      rw [show twF ε _ _ (GrSpecies.tw (R := R) true w)
          = twD ε α S (GrSpecies.tw (R := R) true w) from rfl, twD_tw ε hα, map_neg]
      simp only [twD]
      abel)
    (fun S Y _ _ _ _ i z w => twF_act ε _ i z w)
    (fun A _ _ c => by
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, leafD_corolla,
        map_zero, zero_add, twD_corolla, twD_corolla]
      exact leafD_snd_star ε D hα c)
    w

variable (R C) in
/-- **The differential of the twisted composite product** `C ∘_α P`: `d_α + 1 ∘' d_P`. -/
noncomputable def twDiff (α : GrOperad.Inv R (ConvOp R C P)) (S : Type) [Fintype S]
    [DecidableEq S] : GrComposite R C P S →ₗ[R] GrComposite R C P S :=
  twD ε α S + leafD R C D S

/-- **The square of the differential of a twisted composite product** is the twisted differential
of `α ⋆ α + d_P ∘ α`. -/
theorem twDiff_sq_eq (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A),
    D.app A (D.app A x) = 0) {α : GrOperad.Inv R (ConvOp R C P)} (hα : GrOperad.Inv.IsPar true α)
    {S : Type} [Fintype S] [DecidableEq S] (w : GrComposite R C P S) :
    twDiff R C ε D α S (twDiff R C ε D α S w)
      = twD ε (dFam D α + GrOperad.Inv.star R _ α α) S w := by
  simp only [twDiff, LinearMap.add_apply, map_add]
  rw [twD_add, twD_sq ε hα, leaf_sq D hD, add_zero, ← twD_leaf_anticomm ε D hα]
  abel

/-- **The twisted composite product of a twisting morphism is a complex.** -/
theorem twDiff_sq (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A),
    D.app A (D.app A x) = 0) {α : GrOperad.Inv R (ConvOp R C P)} (hα : GrOperad.Inv.IsPar true α)
    (hmc : dFam D α + GrOperad.Inv.star R _ α α = 0) {S : Type} [Fintype S] [DecidableEq S]
    (w : GrComposite R C P S) : twDiff R C ε D α S (twDiff R C ε D α S w) = 0 := by
  rw [twDiff_sq_eq ε D hD hα, hmc, twD_zero]

end Total

end GrComposite

end Operad
