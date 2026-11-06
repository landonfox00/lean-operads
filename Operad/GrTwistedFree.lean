/-
# The twisted differential without an augmentation

The twisted differential `d_β` of `C ∘ P` (`GrComposite.twD`) is built in the square-zero
extension `P ⋉ (C ∘ P)`, which needs an augmentation of `P`. This file builds it for every graded
operad `P`, augmented or not, through the free graded operad `T(P)` on the graded linear species of
`P`, which is always augmented (`FreeGrL.aug`), and its evaluation `eval : T(P) → P`
(`GrComposite.freeEval`), a morphism of graded operads with the generators `ι : P → T(P)` as a
section of graded linear species.

* **Morphisms of right modules see the inner operations only through `π`**
  (`GrComposite.factor_map₂`): a family of linear maps `T : V ∘ Q → V ∘ P` commuting with the
  relabellings and with `T(w ◁ᵢ z) = T(w) ◁ᵢ π(z)`, for a morphism `π : Q → P`, is unchanged by
  `1 ∘ ψ` for every endomorphism `ψ` of graded linear species with `π ∘ ψ = π`, by composing each
  inner operation into a unit (`GrComposite.map_act_ext`).
* **On the corollas, the image of `d_γ` along a morphism `h : Q → P` only sees `h ∘ γ`**
  (`GrComposite.map₂_twD_corolla`), for homogeneous families and arbitrary augmentations of `Q`; so
  `(1 ∘ h) ∘ d_γ` only depends on `h ∘ γ` (`GrComposite.map₂_twD_congr`).
* **The twisted differential** `twD' β = (1 ∘ eval) ∘ d_{ι ∘ β} ∘ (1 ∘ ι)` (`GrComposite.twD'`)
  satisfies `twD' β ∘ (1 ∘ eval) = (1 ∘ eval) ∘ d_{ι ∘ β}` (`GrComposite.twD'_eval`), so it is
  a morphism of right `P`-modules commuting with the relabellings (`GrComposite.twD'_act`,
  `GrComposite.twD'_map`); it is **`twD ε β` for every augmentation `ε`** of `P`
  (`GrComposite.twD'_eq`), and **for an odd family `twD' α ∘ twD' α = twD' (α ⋆ α)`**
  (`GrComposite.twD'_sq`). It lowers the number of inputs of the outer cooperation and kills the
  elements `1 ⊗ z` for families vanishing in arity one (`GrComposite.twD'_mem_outerLt`,
  `GrComposite.twD'_unitOf`), and it is natural, along morphisms from augmented operads and
  along all morphisms (`GrComposite.map₂_twD_twD'`, `GrComposite.map₂_twD'`).
* **The differential of the twisted composite product** `twDiff' = twD' α + 1 ∘' d_P`
  (`GrComposite.twDiff'`) is `twDiff ε` for every augmentation (`GrComposite.twDiff'_eq`), with
  **`twDiff'² = twD' (d_P ∘ α + α ⋆ α)`**, zero for a twisting morphism
  (`GrComposite.twDiff'_sq_eq`, `GrComposite.twDiff'_sq`), through the derivation of `T(P)`
  extending `d_P` (`GrComposite.freeDer`, `GrComposite.freeEval_freeDer`).

With these, the comparison lemmas (`GrComposite.TwCompareGen`) give the fundamental theorem of
twisting morphisms for every dg operad `P` (`Cobar.fundamental'`, `Operad/KoszulComplex.lean`).
-/
import Operad.GrTwistedConverse

universe u v w x

namespace Operad

open Function Sym GerBV ConvOp

namespace GrComposite

/-! ## Families composed with a morphism of graded linear species -/

section LiftSp

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]

/-- **An invariant family composed with a morphism of graded linear species.** -/
noncomputable def liftSp (ψ : GrSpeciesHom R P Q) :
    GrOperad.Inv R (ConvOp R C P) →ₗ[R] GrOperad.Inv R (ConvOp R C Q) where
  toFun β := ⟨fun A _ _ => postL (ψ.app A) (β.1 A), fun A B _ _ _ _ e => by
    refine ConvOp.ext fun x => ?_
    show toLin (mapC e (postL (ψ.app A) (β.1 A))) x = ψ.app B (toLin (β.1 B) x)
    rw [← GrOperad.Inv.map_apply β e, ConvOp.map_def, mapC_apply, mapC_apply, toLin_postL,
      LinearMap.comp_apply, ← GrOperad.toGrSpecies_map, ← ψ.app_map, GrOperad.toGrSpecies_map]⟩
  map_add' β β' := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    ConvOp.ext fun x => map_add (ψ.app A) _ _)
  map_smul' c β := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    ConvOp.ext fun x => map_smul (ψ.app A) _ _)

@[simp] lemma toLin_liftSp (ψ : GrSpeciesHom R P Q) (β : GrOperad.Inv R (ConvOp R C P))
    {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    toLin ((liftSp ψ β).1 A) c = ψ.app A (toLin (β.1 A) c) := rfl

lemma isPar_liftSp (ψ : GrSpeciesHom R P Q) {p : Bool} {β : GrOperad.Inv R (ConvOp R C P)}
    (hβ : GrOperad.Inv.IsPar p β) : GrOperad.Inv.IsPar p (liftSp ψ β) := fun A _ _ => by
  refine ConvOp.ext fun c => ?_
  have h := congrArg (fun f => ψ.app A (toLin f c)) (hβ A)
  simp only [ConvOp.par_def, parC_apply, map_sum] at h
  rw [ConvOp.par_def, parC_apply, toLin_liftSp, ← h]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [toLin_liftSp, ← GrOperad.toGrSpecies_par, ← ψ.app_par, GrOperad.toGrSpecies_par]

end LiftSp

/-! ## Morphisms of right modules along a morphism of operads -/

section ExtHom

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrOperad R N]
  {N' : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N' A)] [GrOperad R N']

/-- **Two families of linear maps `V ∘ N → V ∘ N'` commuting with the relabellings and with the
action along a morphism `h : N → N'` agree as soon as they agree on the corollas.** -/
theorem eq_of_corolla_hom (h : GrOperadHom R N N')
    (T T' : ∀ (S : Type) [Fintype S] [DecidableEq S],
      GrComposite R V N S →ₗ[R] GrComposite R V N' S)
    (hT : ∀ (S S' : Type) [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] (σ : S ≃ S')
      (w : GrComposite R V N S), T S' (map σ w) = map σ (T S w))
    (hT' : ∀ (S S' : Type) [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] (σ : S ≃ S')
      (w : GrComposite R V N S), T' S' (map σ w) = map σ (T' S w))
    (hTa : ∀ (S Y : Type) [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y] (i : S)
      (z : N Y) (w : GrComposite R V N S), T _ (act R V i z w) = act R V i (h.app Y z) (T S w))
    (hTa' : ∀ (S Y : Type) [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y] (i : S)
      (z : N Y) (w : GrComposite R V N S), T' _ (act R V i z w) = act R V i (h.app Y z) (T' S w))
    (hc : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A),
      T A (corolla R N A v) = T' A (corolla R N A v))
    {S : Type} [Fintype S] [DecidableEq S] (w : GrComposite R V N S) : T S w = T' S w :=
  induction_act (fun S _ _ w => T S w = T' S w) (fun S _ _ => by simp)
    (fun S _ _ x y hx hy => by simp only [map_add, hx, hy])
    (fun S _ _ r x hx => by simp only [map_smul, hx])
    (fun S S' _ _ _ _ σ x hx => by beta_reduce at hx ⊢; rw [hT, hT', hx])
    (fun S Y _ _ _ _ i z x hx => by beta_reduce at hx ⊢; rw [hTa, hTa', hx]) hc w

end ExtHom

/-! ## The twisted differential on the corollas, along a morphism of operads -/

section CorollaHom

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q₁ : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q₁ A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q₁ A)] [GrOperad R Q₁]
  {Q₂ : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q₂ A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q₂ A)] [GrOperad R Q₂]

/-- **The image of the twisted differential of a corolla along a morphism `h : Q → P` depends
only on `h ∘ γ`**, for homogeneous families: each term of `(cor ⋆ γ)(c)` is a corolla acted on by
a value of `γ`. The augmentations of `Q₁` and `Q₂` are arbitrary, and `P` need not have one. -/
theorem map₂_twD_corolla (ε₁ : GrAug R Q₁) (ε₂ : GrAug R Q₂) (h₁ : GrOperadHom R Q₁ P)
    (h₂ : GrOperadHom R Q₂ P) {p : Bool} {γ₁ : GrOperad.Inv R (ConvOp R C Q₁)}
    {γ₂ : GrOperad.Inv R (ConvOp R C Q₂)} (hγ₁ : GrOperad.Inv.IsPar p γ₁)
    (hγ₂ : GrOperad.Inv.IsPar p γ₂)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : C A),
      h₁.app A (toLin (γ₁.1 A) y) = h₂.app A (toLin (γ₂.1 A) y))
    {X : Type} [Fintype X] [DecidableEq X] (c : C X) :
    (map₂ idSpHom h₁.toGrSpeciesHom).app X (twD ε₁ γ₁ X (corolla R Q₁ X c))
      = (map₂ idSpHom h₂.toGrSpeciesHom).app X (twD ε₂ γ₂ X (corolla R Q₂ X c)) := by
  rw [twD_corolla, twD_corolla, toLin_star, toLin_star, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [toLin_term, toLin_term, SqExt.map_def, SqExt.map_def, SqExt.snd_mapE, SqExt.snd_mapE,
    show (map₂ idSpHom h₁.toGrSpeciesHom).app X (map (splitEquiv T) _)
      = map (splitEquiv T) ((map₂ idSpHom h₁.toGrSpeciesHom).app _ _) from
      (map₂ idSpHom h₁.toGrSpeciesHom).app_map _ _,
    show (map₂ idSpHom h₂.toGrSpeciesHom).app X (map (splitEquiv T) _)
      = map (splitEquiv T) ((map₂ idSpHom h₂.toGrSpeciesHom).app _ _) from
      (map₂ idSpHom h₂.toGrSpeciesHom).app_map _ _]
  congr 1
  generalize GrCooperad.decomp (R := R) (C := C) none
    (SymSpecies.map (R := R) (splitEquiv T).symm c) = t
  rw [kap_hom _ (isParC_of_isPar (isPar_liftFam ε₁ hγ₁) (SIn T)),
    kap_hom _ (isParC_of_isPar (isPar_liftFam ε₂ hγ₂) (SIn T))]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, mu_tmul, LinearMap.comp_apply, SqExt.comp_def,
      SqExt.snd_compE]
    rw [show toLin ((liftFam ε₁ γ₁).1 (SIn T)) y
        = (inclHom C ε₁).app _ (toLin (γ₁.1 (SIn T)) y) from rfl,
      show toLin ((liftFam ε₂ γ₂).1 (SIn T)) y
        = (inclHom C ε₂).app _ (toLin (γ₂.1 (SIn T)) y) from rfl,
      fst_inclHom, snd_inclHom, fst_inclHom, snd_inclHom, map_zero, add_zero, map_zero,
      add_zero, map₂_act, map₂_act, h]
    congr 1
    exact (map₂_corolla h₁ _).trans (map₂_corolla h₂ _).symm
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **The image of the twisted differential along a morphism `h : Q → P` depends only on
`h ∘ γ`**, for homogeneous families. -/
theorem map₂_twD_congr (ε : GrAug R Q₁) (h : GrOperadHom R Q₁ P) {p : Bool}
    {γ₁ γ₂ : GrOperad.Inv R (ConvOp R C Q₁)} (hγ₁ : GrOperad.Inv.IsPar p γ₁)
    (hγ₂ : GrOperad.Inv.IsPar p γ₂)
    (hh : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : C A),
      h.app A (toLin (γ₁.1 A) y) = h.app A (toLin (γ₂.1 A) y))
    {S : Type} [Fintype S] [DecidableEq S] (w : GrComposite R C Q₁ S) :
    (map₂ idSpHom h.toGrSpeciesHom).app S (twD ε γ₁ S w)
      = (map₂ idSpHom h.toGrSpeciesHom).app S (twD ε γ₂ S w) :=
  eq_of_corolla_hom h (fun S _ _ => (map₂ idSpHom h.toGrSpeciesHom).app S ∘ₗ twD ε γ₁ S)
    (fun S _ _ => (map₂ idSpHom h.toGrSpeciesHom).app S ∘ₗ twD ε γ₂ S)
    (fun S S' _ _ _ _ σ w => by
      simp only [LinearMap.comp_apply, twD, twF_map]
      exact (map₂ idSpHom h.toGrSpeciesHom).app_map σ _)
    (fun S S' _ _ _ _ σ w => by
      simp only [LinearMap.comp_apply, twD, twF_map]
      exact (map₂ idSpHom h.toGrSpeciesHom).app_map σ _)
    (fun S Y _ _ _ _ i z w => by simp only [LinearMap.comp_apply, twD, twF_act, map₂_act])
    (fun S Y _ _ _ _ i z w => by simp only [LinearMap.comp_apply, twD, twF_act, map₂_act])
    (fun A _ _ c => map₂_twD_corolla ε ε h h hγ₁ hγ₂ hh c) w

end CorollaHom

/-! ## Morphisms of right modules see the inner operations only through `π` -/

section Factor

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  (π : GrOperadHom R Q P)
  (T : ∀ (S : Type) [Fintype S] [DecidableEq S], GrComposite R V Q S →ₗ[R] GrComposite R V P S)
  (hTm : ∀ (S S' : Type) [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] (σ : S ≃ S')
    (w : GrComposite R V Q S), T S' (map σ w) = map σ (T S w))
  (hTa : ∀ (S Y : Type) [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y] (i : S)
    (z : Q Y) (w : GrComposite R V Q S), T _ (act R V i z w) = act R V i (π.app Y z) (T S w))

include hTm hTa in
/-- On generators given by owners, induction on the positions where the inner operations may
differ. -/
lemma factor_ownGen {A : Type} [Fintype A] [DecidableEq A] (L : LinOrd A) (m : V A)
    (F : Finset A) :
    ∀ (S : Type) [Fintype S] [DecidableEq S] (f : S → A) (yy yy' : ∀ a, Q (Fib f a))
    (c : A → Bool), (∀ a, GrOperad.par (R := R) (c a) (yy a) = yy a) →
    (∀ a, GrOperad.par (R := R) (c a) (yy' a) = yy' a) → (∀ a ∉ F, yy a = yy' a) →
    (∀ a, π.app _ (yy a) = π.app _ (yy' a)) →
    T S (mk R (ownGen L m f yy)) = T S (mk R (ownGen L m f yy')) := by
  induction F using Finset.induction_on with
  | empty =>
    intro S _ _ f yy yy' c _ _ he _
    rw [show yy = yy' from funext fun a => he a (Finset.notMem_empty a)]
  | insert a₀ F ha₀ ih =>
    intro S _ _ f yy yy' c hyy hyy' he hπ
    have hpar : ∀ yy₀ : ∀ a, Q (Fib f a), (∀ a, GrOperad.par (R := R) (c a) (yy₀ a) = yy₀ a) →
        ∀ a, GrOperad.par (R := R) (update c a₀ false a) (extY (R := R) f yy₀ a₀ a)
          = extY (R := R) f yy₀ a₀ a := fun yy₀ hyy₀ a => by
      by_cases h : a₀ = a
      · subst h
        rw [update_self, extY, dif_pos rfl, ← GrOperad.map_par, GrOperad.par_one]
      · rw [update_of_ne (Ne.symm h), extY, dif_neg h, ← GrOperad.map_par, hyy₀]
    have h1 := ih (Ext f a₀) (extOwner f a₀) (extY (R := R) f yy a₀) (extY (R := R) f yy' a₀)
      (update c a₀ false) (hpar yy hyy) (hpar yy' hyy')
      (fun a ha => by
        by_cases h : a₀ = a
        · rw [extY, extY, dif_pos h, dif_pos h]
        · rw [extY, extY, dif_neg h, dif_neg h,
            he a (by simp [Finset.mem_insert, Ne.symm h, ha])])
      (fun a => by
        by_cases h : a₀ = a
        · rw [extY, extY, dif_pos h, dif_pos h]
        · rw [extY, extY, dif_neg h, dif_neg h, π.app_map, π.app_map, hπ])
    have e1 := map_act_ext L m f yy c hyy a₀
    have e2 := map_act_ext L m f yy' c hyy' a₀
    have h2 : (∏ a, σ R ((c a₀ && ltB L a₀ a) && c a)) • T S (mk R (ownGen L m f yy))
        = (∏ a, σ R ((c a₀ && ltB L a₀ a) && c a)) • T S (mk R (ownGen L m f yy')) := by
      rw [← map_smul, ← map_smul, ← e1, ← e2, hTm, hTm, hTa, hTa, hπ a₀, h1]
    have h3 := congrArg ((∏ a, σ R ((c a₀ && ltB L a₀ a) && c a)) • ·) h2
    simp only [smul_smul, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl fun a _ => σ_mul_self R ((c a₀ && ltB L a₀ a) && c a),
      Finset.prod_const_one, one_smul] at h3
    exact h3

include hTm hTa in
/-- **A morphism of right modules along `π` does not see an endomorphism of the inner operations
preserving `π`.** -/
lemma factor_mk (ψ : GrSpeciesHom R Q Q)
    (hψ : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : Q A), π.app A (ψ.app A y) = π.app A y)
    {S : Type} [Fintype S] [DecidableEq S] (g : GrCompGen V Q S) :
    T S (mk R (genMap₂ idSpHom ψ g)) = T S (mk R g) := by
  rw [mk_eq_sum (R := R) (genMap₂ idSpHom ψ g), mk_eq_sum (R := R) g, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mk_eq_ownGen (R := R) (parGen (R := R) (genMap₂ idSpHom ψ g) p c),
    mk_eq_ownGen (R := R) (parGen (R := R) g p c)]
  refine factor_ownGen π T hTm hTa g.L (GrSpecies.par (R := R) p g.m) Finset.univ S (owner g)
    _ _ c (fun a => ?_) (fun a => ?_) (fun a ha => absurd (Finset.mem_univ a) ha) (fun a => ?_)
  · show GrOperad.par (R := R) (c a) (GrOperad.map (R := R) _ (GrSpecies.par (R := R) (c a)
      (ψ.app _ (g.y a)))) = _
    rw [← GrOperad.map_par]
    exact congrArg _ (GrOperad.par_par_self (R := R) (c a) _)
  · show GrOperad.par (R := R) (c a) (GrOperad.map (R := R) _ (GrSpecies.par (R := R) (c a)
      (g.y a))) = _
    rw [← GrOperad.map_par]
    exact congrArg _ (GrOperad.par_par_self (R := R) (c a) _)
  · show π.app _ (GrOperad.map (R := R) _ (GrOperad.par (R := R) (c a) (ψ.app _ (g.y a))))
      = π.app _ (GrOperad.map (R := R) _ (GrOperad.par (R := R) (c a) (g.y a)))
    rw [π.app_map, π.app_map, π.app_par, π.app_par, hψ]
    rfl

include hTm hTa in
/-- **A morphism of right modules along `π` factors through `1 ∘ π`**: it agrees with its
composite with `1 ∘ (ι ∘ π)`, for a section `ι` of `π`. -/
theorem factor_map₂ (ψ : GrSpeciesHom R Q Q)
    (hψ : ∀ (A : Type) [Fintype A] [DecidableEq A] (y : Q A), π.app A (ψ.app A y) = π.app A y)
    {S : Type} [Fintype S] [DecidableEq S] (w : GrComposite R V Q S) :
    T S ((map₂ idSpHom ψ).app S w) = T S w := by
  have h : (T S).comp ((map₂ idSpHom ψ).app S) = T S := hom_ext fun g => by
    rw [LinearMap.comp_apply, map₂_mk]
    exact factor_mk π T hTm hTa ψ hψ g
  exact LinearMap.congr_fun h w

end Factor

/-! ## The twisted differential through the free graded operad -/

section Free

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {S : Type} [Fintype S] [DecidableEq S]

variable (R P) in
/-- **The evaluation** `T(P) → P` of the free graded operad on the graded linear species of `P`:
the morphism of graded operads restricting to the identity on the generators. -/
noncomputable def freeEval : GrOperadHom R (FreeGrL R P) P :=
  FreeGrL.homEquiv.symm (GrOperadHom.id R P).toGrSpeciesHom

@[simp] lemma freeEval_ι {A : Type} [Fintype A] [DecidableEq A] (y : P A) :
    (freeEval R P).app A ((FreeGrL.ι R P).app A y) = y :=
  FreeGrL.homEquiv_symm_ι _ y

/-- The identity at the inner operations is the identity. -/
lemma map₂_id_app {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrOperad R N]
    (x : GrComposite R C N S) : (map₂ idSpHom (GrOperadHom.id R N).toGrSpeciesHom).app S x = x := by
  have h : (map₂ idSpHom (GrOperadHom.id R N).toGrSpeciesHom).app S = LinearMap.id :=
    hom_ext (M := C) (N := N) fun g => by rw [map₂_mk]; rfl
  rw [h, LinearMap.id_apply]

/-- **`1 ∘ eval` is a retraction of `1 ∘ ι`.** -/
lemma map₂_eval_ι (x : GrComposite R C P S) :
    (map₂ idSpHom (freeEval R P).toGrSpeciesHom).app S ((map₂ idSpHom (FreeGrL.ι R P)).app S x)
      = x := by
  rw [map₂_map₂ _ _ (GrOperadHom.id R P).toGrSpeciesHom (fun A _ _ y => freeEval_ι y),
    map₂_id_app]

/-- The part of parity `b` of an invariant family. -/
noncomputable def parFam (b : Bool) :
    GrOperad.Inv R (ConvOp R C P) →ₗ[R] GrOperad.Inv R (ConvOp R C P) where
  toFun β := ⟨fun A _ _ => GrOperad.par (R := R) b (β.1 A), fun A B _ _ _ _ e => by
    show GrOperad.map (R := R) e (GrOperad.par (R := R) b (β.1 A)) = GrOperad.par (R := R) b (β.1 B)
    rw [GrOperad.map_par, GrOperad.Inv.map_apply]⟩
  map_add' β β' := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_add (GrOperad.par (R := R) b) _ _)
  map_smul' c β := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_smul (GrOperad.par (R := R) b) _ _)

lemma isPar_parFam (b : Bool) (β : GrOperad.Inv R (ConvOp R C P)) :
    GrOperad.Inv.IsPar b (parFam b β) := fun A _ _ => GrOperad.par_par_self (R := R) b (β.1 A)

lemma parFam_add (β : GrOperad.Inv R (ConvOp R C P)) : parFam false β + parFam true β = β :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => GrOperad.par_add (R := R) (β.1 A))

/-- **The twisted differential `d_β` of `C ∘ P`, for any graded operad `P`**, augmented or not:
the twisted differential of `C ∘ T(P)`, for the augmentation of the free graded operad `T(P)` and
the family `ι ∘ β`, between `1 ∘ ι : C ∘ P → C ∘ T(P)` and `1 ∘ eval : C ∘ T(P) → C ∘ P`. It is
the twisted differential `twD ε β` for every augmentation `ε` of `P` (`GrComposite.twD'_eq`). -/
noncomputable def twD' (β : GrOperad.Inv R (ConvOp R C P)) (S : Type) [Fintype S]
    [DecidableEq S] : GrComposite R C P S →ₗ[R] GrComposite R C P S :=
  (map₂ idSpHom (freeEval R P).toGrSpeciesHom).app S
    ∘ₗ twD (FreeGrL.aug R P) (liftSp (FreeGrL.ι R P) β) S
    ∘ₗ (map₂ idSpHom (FreeGrL.ι R P)).app S

/-- **The twisted differential of `C ∘ P` is the image of that of `C ∘ T(P)`** along
`1 ∘ eval`, by the factorization of morphisms of right modules through `1 ∘ eval`. -/
theorem twD'_eval (β : GrOperad.Inv R (ConvOp R C P)) (w : GrComposite R C (FreeGrL R P) S) :
    twD' β S ((map₂ idSpHom (freeEval R P).toGrSpeciesHom).app S w)
      = (map₂ idSpHom (freeEval R P).toGrSpeciesHom).app S
          (twD (FreeGrL.aug R P) (liftSp (FreeGrL.ι R P) β) S w) := by
  rw [twD', LinearMap.comp_apply, LinearMap.comp_apply, map₂_map₂ _ _
    ((FreeGrL.ι R P).comp (freeEval R P).toGrSpeciesHom) (fun _ _ _ _ => rfl)]
  exact factor_map₂ (freeEval R P)
    (fun S _ _ => (map₂ idSpHom (freeEval R P).toGrSpeciesHom).app S
      ∘ₗ twD (FreeGrL.aug R P) (liftSp (FreeGrL.ι R P) β) S)
    (fun S S' _ _ _ _ σ w => by
      simp only [LinearMap.comp_apply, twD, twF_map]
      exact (map₂ idSpHom (freeEval R P).toGrSpeciesHom).app_map σ _)
    (fun S Y _ _ _ _ i z w => by simp only [LinearMap.comp_apply, twD, twF_act, map₂_act])
    ((FreeGrL.ι R P).comp (freeEval R P).toGrSpeciesHom)
    (fun A _ _ y => by rw [GrSpeciesHom.comp_app]; exact freeEval_ι _) w

/-- **The twisted differential commutes with the relabellings.** -/
theorem twD'_map {S' : Type} [Fintype S'] [DecidableEq S'] (β : GrOperad.Inv R (ConvOp R C P))
    (σ : S ≃ S') (w : GrComposite R C P S) : twD' β S' (map σ w) = map σ (twD' β S w) := by
  simp only [twD', LinearMap.comp_apply]
  rw [show (map₂ idSpHom (FreeGrL.ι R P)).app S' (map σ w)
      = map σ ((map₂ idSpHom (FreeGrL.ι R P)).app S w) from
    (map₂ idSpHom (FreeGrL.ι R P)).app_map σ w, twD, twF_map]
  exact (map₂ idSpHom (freeEval R P).toGrSpeciesHom).app_map σ _

/-- **The twisted differential is a morphism of right `P`-modules.** -/
theorem twD'_act {Y : Type} [Fintype Y] [DecidableEq Y] (β : GrOperad.Inv R (ConvOp R C P))
    (i : S) (z : P Y) (w : GrComposite R C P S) :
    twD' β _ (act R C i z w) = act R C i z (twD' β S w) := by
  conv_lhs => rw [← map₂_eval_ι w, ← freeEval_ι (R := R) z, ← map₂_act, twD'_eval, twD,
    twF_act, map₂_act, freeEval_ι]
  rfl

/-- **The value of the twisted differential on a corolla.** -/
theorem twD'_corolla (β : GrOperad.Inv R (ConvOp R C P)) {A : Type} [Fintype A] [DecidableEq A]
    (c : C A) : twD' β A (corolla R P A c)
      = (map₂ idSpHom (freeEval R P).toGrSpeciesHom).app A
          (twD (FreeGrL.aug R P) (liftSp (FreeGrL.ι R P) β) A (corolla R (FreeGrL R P) A c)) := by
  rw [← twD'_eval, map₂_corolla]

/-- **The twisted differential is additive in the family.** -/
theorem twD'_add (β β' : GrOperad.Inv R (ConvOp R C P)) (w : GrComposite R C P S) :
    twD' (β + β') S w = twD' β S w + twD' β' S w := by
  simp only [twD', LinearMap.comp_apply, map_add, twD_add]

/-- The twisted differential of the zero family vanishes. -/
theorem twD'_zero (w : GrComposite R C P S) : twD' (0 : GrOperad.Inv R (ConvOp R C P)) S w = 0 := by
  simp only [twD', LinearMap.comp_apply, map_zero, twD_zero]

/-- **The twisted differential is that of every augmentation**, for a homogeneous family. -/
theorem twD'_eq_of_isPar (ε : GrAug R P) {p : Bool} {β : GrOperad.Inv R (ConvOp R C P)}
    (hβ : GrOperad.Inv.IsPar p β) (w : GrComposite R C P S) : twD' β S w = twD ε β S w :=
  eq_of_corolla (fun S _ _ => twD' β S) (fun S _ _ => twD ε β S)
    (fun S S' _ _ _ _ σ w => twD'_map β σ w) (fun S S' _ _ _ _ σ w => twF_map ε _ σ w)
    (fun S Y _ _ _ _ i z w => twD'_act β i z w) (fun S Y _ _ _ _ i z w => twF_act ε _ i z w)
    (fun A _ _ c => by
      rw [twD'_corolla, map₂_twD_corolla (FreeGrL.aug R P) ε (freeEval R P)
        (GrOperadHom.id R P) (isPar_liftSp _ hβ) hβ (fun A _ _ y => freeEval_ι _) c,
        map₂_id_app]) w

/-- **The twisted differential is that of every augmentation of `P`**: `twD' β = twD ε β`. -/
theorem twD'_eq (ε : GrAug R P) (β : GrOperad.Inv R (ConvOp R C P)) (S : Type) [Fintype S]
    [DecidableEq S] : twD' β S = twD ε β S := by
  refine LinearMap.ext fun w => ?_
  conv_lhs => rw [← parFam_add β]
  conv_rhs => rw [← parFam_add β]
  rw [twD'_add, twD_add, twD'_eq_of_isPar ε (isPar_parFam false β),
    twD'_eq_of_isPar ε (isPar_parFam true β)]

end Free

/-! ## Squares, filtrations and units -/

section FreeProps

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {S : Type} [Fintype S] [DecidableEq S]

/-- The evaluation undoes the generators, on families. -/
lemma appHom_liftSp (β : GrOperad.Inv R (ConvOp R C P)) :
    GrOperad.Inv.appHom (postHom (C := C) (freeEval R P)) (liftSp (FreeGrL.ι R P) β) = β :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    ConvOp.ext fun c => freeEval_ι (toLin (β.1 A) c))

lemma isPar_add' {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {p : Bool}
    {q q' : GrOperad.Inv R Q} (hq : GrOperad.Inv.IsPar p q) (hq' : GrOperad.Inv.IsPar p q') :
    GrOperad.Inv.IsPar p (q + q') := fun A _ _ => by
  show GrOperad.par (R := R) p (q.1 A + q'.1 A) = q.1 A + q'.1 A
  rw [map_add, hq A, hq' A]

/-- **The square of the twisted differential of an odd family** is the twisted differential of its
square. -/
theorem twD'_sq {α : GrOperad.Inv R (ConvOp R C P)} (hα : GrOperad.Inv.IsPar true α)
    (w : GrComposite R C P S) :
    twD' α S (twD' α S w) = twD' (GrOperad.Inv.star R _ α α) S w := by
  rw [← map₂_eval_ι w, twD'_eval, twD'_eval, twD'_eval, twD_sq _ (isPar_liftSp _ hα)]
  refine map₂_twD_congr (FreeGrL.aug R P) (freeEval R P)
    (GrOperad.Inv.isPar_star (isPar_liftSp _ hα) (isPar_liftSp _ hα))
    (isPar_liftSp _ (GrOperad.Inv.isPar_star hα hα)) (fun A _ _ y => ?_) _
  rw [toLin_liftSp, freeEval_ι]
  show toLin ((GrOperad.Inv.appHom (postHom (C := C) (freeEval R P)) _).1 A) y = _
  rw [GrOperad.Inv.appHom_star, appHom_liftSp]

/-- **The twisted differential of an odd family with vanishing square squares to zero.** -/
theorem twD'_twD'_eq_zero {α : GrOperad.Inv R (ConvOp R C P)} (hα : GrOperad.Inv.IsPar true α)
    (h : GrOperad.Inv.star R _ α α = 0) (w : GrComposite R C P S) :
    twD' α S (twD' α S w) = 0 := by
  rw [twD'_sq hα, h, twD'_zero]

/-- **The twisted differential lowers the number of inputs of the outer operation**, for a family
vanishing in the arities of one element. -/
theorem twD'_mem_outerLt {β : GrOperad.Inv R (ConvOp R C P)} {p : Bool}
    (hβ : GrOperad.Inv.IsPar p β)
    (hβ1 : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = 1 →
      ∀ x : C A, toLin (β.1 A) x = 0)
    {k : ℕ} {x : GrComposite R C P S} (hx : x ∈ outerSpan R C P S k) :
    twD' β S x ∈ outerLt R C P S k :=
  map₂_mem_outerSpanP _ (twD_mem_outerLt (FreeGrL.aug R P) (isPar_liftSp _ hβ)
    (fun A _ _ hA y => by rw [toLin_liftSp, hβ1 A hA y, map_zero]) (map₂_mem_outerSpanP _ hx))

lemma twD'_mem_outerLt_of_lt {β : GrOperad.Inv R (ConvOp R C P)} {p : Bool}
    (hβ : GrOperad.Inv.IsPar p β)
    (hβ1 : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = 1 →
      ∀ x : C A, toLin (β.1 A) x = 0)
    {k : ℕ} {x : GrComposite R C P S} (hx : x ∈ outerLt R C P S k) :
    twD' β S x ∈ outerLt R C P S k :=
  map₂_mem_outerSpanP _ (twD_mem_outerLt_of_lt (FreeGrL.aug R P) (isPar_liftSp _ hβ)
    (fun A _ _ hA y => by rw [toLin_liftSp, hβ1 A hA y, map_zero]) (map₂_mem_outerSpanP _ hx))



/-- **The twisted differential vanishes on the elements `1 ⊗ z`**, for a family vanishing in the
arities of one element. -/
theorem twD'_unitOf [GrCooperad.Coaug R C] {β : GrOperad.Inv R (ConvOp R C P)} {p : Bool}
    (hβ : GrOperad.Inv.IsPar p β)
    (hβ1 : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = 1 →
      ∀ x : C A, toLin (β.1 A) x = 0)
    {B : Type} [Fintype B] [DecidableEq B] (z : P B) : twD' β B (unitOf R C P B z) = 0 := by
  have h := twD'_mem_outerLt hβ hβ1
    (corolla_mem_outerSpan (R := R) (P := P) (GrCooperad.Coaug.one (R := R) (C := C)))
  rw [Fintype.card_unit, outerLt_one_eq_bot ⟨()⟩, Submodule.mem_bot] at h
  rw [unitOf_apply, twD'_map, twD'_act, h, map_zero, map_zero]

end FreeProps

/-! ## Naturality -/

section FreeNat

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
  {S : Type} [Fintype S] [DecidableEq S]

/-- **The twisted differential is natural along a morphism from an augmented graded operad**:
`1 ∘ g` intertwines `twD ε γ` and `twD' (g ∘ γ)`, for a homogeneous family `γ`. -/
theorem map₂_twD_twD' (ε : GrAug R Q) (g : GrOperadHom R Q P)
    {γ : GrOperad.Inv R (ConvOp R C Q)} {p : Bool} (hγ : GrOperad.Inv.IsPar p γ)
    (w : GrComposite R C Q S) :
    (map₂ idSpHom g.toGrSpeciesHom).app S (twD ε γ S w)
      = twD' (GrOperad.Inv.appHom (postHom (C := C) g) γ) S
          ((map₂ idSpHom g.toGrSpeciesHom).app S w) :=
  eq_of_corolla_hom g (fun S _ _ => (map₂ idSpHom g.toGrSpeciesHom).app S ∘ₗ twD ε γ S)
    (fun S _ _ => twD' (GrOperad.Inv.appHom (postHom (C := C) g) γ) S
      ∘ₗ (map₂ idSpHom g.toGrSpeciesHom).app S)
    (fun S S' _ _ _ _ σ w => by
      simp only [LinearMap.comp_apply, twD, twF_map]
      exact (map₂ idSpHom g.toGrSpeciesHom).app_map σ _)
    (fun S S' _ _ _ _ σ w => by
      simp only [LinearMap.comp_apply]
      rw [show (map₂ idSpHom g.toGrSpeciesHom).app S' (map σ w)
        = map σ ((map₂ idSpHom g.toGrSpeciesHom).app S w) from
          (map₂ idSpHom g.toGrSpeciesHom).app_map σ w, twD'_map])
    (fun S Y _ _ _ _ i z w => by simp only [LinearMap.comp_apply, twD, twF_act, map₂_act])
    (fun S Y _ _ _ _ i z w => by simp only [LinearMap.comp_apply, map₂_act, twD'_act])
    (fun A _ _ c => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, map₂_corolla, twD'_corolla]
      exact map₂_twD_corolla ε (FreeGrL.aug R P) g (freeEval R P) hγ
        (isPar_liftSp _ (isPar_appHom g hγ)) (fun A _ _ y => (freeEval_ι _).symm) c) w

/-- **The twisted differential is natural** in morphisms of graded operads. -/
theorem map₂_twD' (g : GrOperadHom R Q P) {β : GrOperad.Inv R (ConvOp R C Q)} {p : Bool}
    (hβ : GrOperad.Inv.IsPar p β) (w : GrComposite R C Q S) :
    (map₂ idSpHom g.toGrSpeciesHom).app S (twD' β S w)
      = twD' (GrOperad.Inv.appHom (postHom (C := C) g) β) S
          ((map₂ idSpHom g.toGrSpeciesHom).app S w) := by
  conv_lhs => rw [← map₂_eval_ι w, twD'_eval, map₂_map₂ _ _
    (g.comp (freeEval R Q)).toGrSpeciesHom (fun _ _ _ _ => rfl), map₂_twD_twD' (FreeGrL.aug R Q)
    _ (isPar_liftSp _ hβ)]
  rw [← map₂_map₂ g.toGrSpeciesHom (freeEval R Q).toGrSpeciesHom
    (g.comp (freeEval R Q)).toGrSpeciesHom (fun _ _ _ _ => rfl), map₂_eval_ι]
  congr 2
  exact Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    ConvOp.ext fun c => congrArg (g.app A) (freeEval_ι (toLin (β.1 A) c)))

end FreeNat

/-! ## The differential of the twisted composite product -/

section FreeDiff

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (D : GrDer (GrOperadHom.id R P) true) {S : Type} [Fintype S] [DecidableEq S]

/-- **The derivation of the free graded operad `T(P)` extending `D`** on the generators. -/
noncomputable abbrev freeDer : GrDer (GrOperadHom.id R (FreeGrL R P)) true :=
  FreeGrL.derSp D.toSpEnd

/-- `eval ∘ D⁺`, a derivation along the evaluation. -/
noncomputable def evalDer : GrDer (freeEval R P) true where
  app A _ _ := (freeEval R P).app A ∘ₗ (freeDer D).app A
  app_par c x := by simp only [LinearMap.comp_apply, GrDer.app_par, GrOperadHom.app_par]
  app_map σ' x := by simp only [LinearMap.comp_apply, GrDer.app_map, GrOperadHom.app_map]
  app_one := by simp only [LinearMap.comp_apply, GrDer.app_one, map_zero]
  app_comp i x y := by
    simp only [LinearMap.comp_apply, GrDer.app_comp, map_add, GrOperadHom.app_comp,
      GrOperadHom.app_tw]
    rfl

/-- `D ∘ eval`, a derivation along the evaluation. -/
noncomputable def derEval : GrDer (freeEval R P) true where
  app A _ _ := D.app A ∘ₗ (freeEval R P).app A
  app_par c x := by simp only [LinearMap.comp_apply, GrDer.app_par, GrOperadHom.app_par]
  app_map σ' x := by simp only [LinearMap.comp_apply, GrDer.app_map, GrOperadHom.app_map]
  app_one := by simp only [LinearMap.comp_apply, GrDer.app_one, GrOperadHom.app_one]
  app_comp i x y := by
    simp only [LinearMap.comp_apply, GrDer.app_comp, GrOperadHom.app_comp]
    rfl

/-- **The evaluation intertwines the extended derivation with `D`.** -/
lemma freeEval_freeDer {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R P A) :
    (freeEval R P).app A ((freeDer D).app A x) = D.app A ((freeEval R P).app A x) := by
  have h : evalDer D = derEval D := FreeGrL.der_ext fun A _ _ v => by
    show (freeEval R P).app A ((FreeGrL.derSp D.toSpEnd).app A ((FreeGrL.ι R P).app A v))
      = D.app A ((freeEval R P).app A ((FreeGrL.ι R P).app A v))
    rw [FreeGrL.derSp_ι, freeEval_ι, freeEval_ι]
    rfl
  exact congrArg (fun d : GrDer (freeEval R P) true => d.app A x) h

/-- **The extended derivation squares to zero** when `D` does. -/
lemma freeDer_sq (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), D.app A (D.app A x) = 0)
    {A : Type} [Fintype A] [DecidableEq A] (x : FreeGrL R P A) :
    (freeDer D).app A ((freeDer D).app A x) = 0 :=
  FreeGrL.sq_eq_zero (fun A _ _ v => by
    rw [FreeGrL.derSp_ι, FreeGrL.derSp_ι]
    show (FreeGrL.ι R P).app A (D.app A (D.app A v)) = 0
    rw [hD, map_zero]) x

/-- The evaluation undoes the generators, on derivatives of families. -/
lemma appHom_dFam_liftSp (α : GrOperad.Inv R (ConvOp R C P)) :
    GrOperad.Inv.appHom (postHom (C := C) (freeEval R P))
      (dFam (freeDer D) (liftSp (FreeGrL.ι R P) α)) = dFam D α :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun c => by
    show (freeEval R P).app A ((freeDer D).app A ((FreeGrL.ι R P).app A (toLin (α.1 A) c)))
      = D.app A (toLin (α.1 A) c)
    rw [freeEval_freeDer, freeEval_ι])

variable (R C) in
/-- **The differential of the twisted composite product** `C ∘_α P`, `d_α + 1 ∘' d_P`, for any
graded operad `P`. It is `twDiff R C ε D α` for every augmentation `ε` of `P`
(`GrComposite.twDiff'_eq`). -/
noncomputable def twDiff' (α : GrOperad.Inv R (ConvOp R C P)) (S : Type) [Fintype S]
    [DecidableEq S] : GrComposite R C P S →ₗ[R] GrComposite R C P S :=
  twD' α S + leafD R C D S

/-- **The differential is that of every augmentation of `P`.** -/
theorem twDiff'_eq (ε : GrAug R P) (α : GrOperad.Inv R (ConvOp R C P)) (S : Type) [Fintype S]
    [DecidableEq S] : twDiff' R C D α S = twDiff R C ε D α S := by
  rw [twDiff', twDiff, twD'_eq ε]

/-- The differential of `C ∘ P` is the image of that of `C ∘ T(P)`. -/
theorem twDiff'_eval (α : GrOperad.Inv R (ConvOp R C P)) (w : GrComposite R C (FreeGrL R P) S) :
    twDiff' R C D α S ((map₂ idSpHom (freeEval R P).toGrSpeciesHom).app S w)
      = (map₂ idSpHom (freeEval R P).toGrSpeciesHom).app S
          (twDiff R C (FreeGrL.aug R P) (freeDer D) (liftSp (FreeGrL.ι R P) α) S w) := by
  simp only [twDiff', twDiff, LinearMap.add_apply, map_add, twD'_eval]
  rw [map₂_leafMap idSpHom (fun _ _ _ _ => rfl) (freeEval R P).toGrSpeciesHom
    (freeDer D).toSpEnd D.toSpEnd (fun A _ _ y => freeEval_freeDer D y) w]

/-- **The square of the differential of a twisted composite product** is the twisted differential
of `α ⋆ α + d_P ∘ α`. -/
theorem twDiff'_sq_eq
    (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), D.app A (D.app A x) = 0)
    {α : GrOperad.Inv R (ConvOp R C P)} (hα : GrOperad.Inv.IsPar true α)
    (w : GrComposite R C P S) :
    twDiff' R C D α S (twDiff' R C D α S w)
      = twD' (dFam D α + GrOperad.Inv.star R _ α α) S w := by
  rw [← map₂_eval_ι w, twDiff'_eval, twDiff'_eval,
    twDiff_sq_eq _ _ (fun A _ _ x => freeDer_sq D hD x) (isPar_liftSp _ hα), twD'_eval]
  refine map₂_twD_congr (FreeGrL.aug R P) (freeEval R P)
    (isPar_add' (GrOperad.Inv.isPar_appDer _ (isPar_liftSp _ hα))
      (GrOperad.Inv.isPar_star (isPar_liftSp _ hα) (isPar_liftSp _ hα)))
    (isPar_liftSp _ (isPar_add' (GrOperad.Inv.isPar_appDer _ hα)
      (GrOperad.Inv.isPar_star hα hα))) (fun A _ _ y => ?_) _
  rw [toLin_liftSp, freeEval_ι]
  show toLin ((GrOperad.Inv.appHom (postHom (C := C) (freeEval R P)) _).1 A) y = _
  rw [map_add, GrOperad.Inv.appHom_star, appHom_liftSp, appHom_dFam_liftSp]

/-- **The twisted composite product of a twisting morphism is a complex**, for any graded operad
`P`. -/
theorem twDiff'_sq
    (hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), D.app A (D.app A x) = 0)
    {α : GrOperad.Inv R (ConvOp R C P)} (hα : GrOperad.Inv.IsPar true α)
    (hmc : dFam D α + GrOperad.Inv.star R _ α α = 0) (w : GrComposite R C P S) :
    twDiff' R C D α S (twDiff' R C D α S w) = 0 := by
  rw [twDiff'_sq_eq D hD hα, hmc, twD'_zero]

end FreeDiff

end GrComposite

end Operad
