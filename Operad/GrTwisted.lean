/-
# Twisted composite products

Let `C` be a graded cooperad, `P` a graded operad with an augmentation `ε`, and `β` an invariant
family of the convolution operad of `C` and `P`. **The twisted differential**
`d_β : C ∘ P → C ∘ P` (`GrComposite.twD`) decomposes the outer cooperation and composes the
image of its inner part under `β` with the inner operations below it:

  `d_β (c ⊗ y₁ ⊗ ⋯ ⊗ yₖ) = ∑ ± c' ⊗ (β(c'') ∘ (yₐ)_{a ∈ S}, (yₐ)_{a ∉ S})`.

It is built from operations already at hand. In the square-zero extension `𝒬 = P ⋉ (C ∘ P)`,
the corollas form an invariant family `cor` of the convolution operad of `C` and `𝒬`, and `β`
one with values in `P ⊆ 𝒬`; their convolution product `cor ⋆ β` has values in `C ∘ P`, and
`d_β` is its extension by the total composition of `𝒬` (`GrComposite.twF`). So:

* `d_β` is **a morphism of right `P`-modules** (`GrComposite.twF_act`), commuting with the
  relabellings (`GrComposite.twF_map`), and its value on a corolla is `cor ⋆ β`
  (`GrComposite.twF_corolla`);
* **`d_α ∘ d_β` is the extension of `(cor ⋆ α) ⋆ β`** (`GrComposite.twD_twD`), so by the
  associator of an odd family, **`d_α ∘ d_α` is the extension of `cor ⋆ (α ⋆ α)`**
  (`GrComposite.twD_sq`), and **`d_α` squares to zero for a twisting morphism** into a graded
  operad (`GrComposite.twD_twD_eq_zero`).
-/
import Operad.FreeGrGraft
import Operad.Twisting

universe u v w x

namespace Operad

open Function Sym GerBV

/-! ## Relabelling the inner operations along a morphism of operads -/

namespace GrComposite

section LeafHom

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {V' : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V' A)] [GrSpecies R V']
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrOperad R C]
  {C' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C' A)] [GrOperad R C']
  {S : Type} [Fintype S] [DecidableEq S] {Y : Type} [Fintype Y] [DecidableEq Y]

lemma app_actLin (ψ : GrOperadHom R C C') {A : Type} [DecidableEq A] (L : LinOrd A) (f : S → A)
    (i : S) (z : C Y) (q : Bool) (a : A) (y : C (Fib f a)) :
    ψ.app _ (actLin (R := R) L f i z q a y)
      = actLin (R := R) L f i (ψ.app Y z) q a (ψ.app _ y) := by
  by_cases h : f i = a
  · rw [actLin_eq _ _ _ _ _ _ h, actLin_eq _ _ _ _ _ _ h, ψ.app_map, ψ.app_comp]
  · rw [actLin_ne _ _ _ _ _ _ h, actLin_ne _ _ _ _ _ _ h, GrOperad.tw_apply, GrOperad.tw_apply,
      map_add, map_smul, ψ.app_par, ψ.app_par, ψ.app_map]

/-- **Relabelling the inner operations along a morphism of operads commutes with the action.** -/
lemma map₂_act (φ : SymSpeciesHom R V V') (ψ : GrOperadHom R C C') (i : S) (z : C Y)
    (w : GrComposite R V C S) :
    (map₂ φ ψ.toGrSpeciesHom).app _ (act R V i z w)
      = act R V' i (ψ.app Y z) ((map₂ φ ψ.toGrSpeciesHom).app S w) := by
  induction w using induction_on with
  | h0 => simp only [map_zero]
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul r x hx => simp only [map_smul, hx]
  | hmk g =>
    rw [mk_eq_ownGen (R := R) g, act_mk_ownGen, map₂_mk]
    rw [show genMap₂ φ ψ.toGrSpeciesHom (ownGen g.L g.m (owner g) fun a =>
        SymSpecies.map (R := R) (fibEquiv g a) (g.y a))
      = ownGen g.L (φ.app _ g.m) (owner g) (fun a => ψ.app _
        (SymSpecies.map (R := R) (fibEquiv g a) (g.y a))) from rfl, act_mk_ownGen]
    unfold actOwn
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map₂_mk, ← ψ.app_par]
    show mk R (ownGen _ _ _ fun a => ψ.app _ (actLin (R := R) g.L (owner g) i
        (GrOperad.par (R := R) q z) q a _))
      = mk R (ownGen _ _ _ fun a => actLin (R := R) g.L (owner g) i
        (ψ.app Y (GrOperad.par (R := R) q z)) q a _)
    congr 2
    funext a
    exact app_actLin ψ g.L (owner g) i _ q a _

end LeafHom

end GrComposite

/-! ## The twisted differential -/

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (ε : GrAug R P)

namespace GrComposite

open ConvOp

local notation "𝒬" => SqExt R C P ε

/-- The corollas, in the second factor of the square-zero extension. -/
noncomputable def corLin (A : Type) [Fintype A] [DecidableEq A] : C A →ₗ[R] 𝒬 A where
  toFun c := SqExt.mk 0 (corolla R P A c)
  map_add' c c' := SqExt.ext (by simp) (by simp)
  map_smul' r c := SqExt.ext (by simp) (by simp)

@[simp] lemma fst_corLin {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    SqExt.fst (corLin ε A c) = 0 := rfl

@[simp] lemma snd_corLin {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    SqExt.snd (corLin ε A c) = corolla R P A c := rfl

/-- **The corollas, as an invariant family** of the convolution operad of `C` and `𝒬`. -/
noncomputable def corFam : GrOperad.Inv R (ConvOp R C 𝒬) :=
  ⟨fun A _ _ => ConvOp.of (corLin ε A), fun A B _ _ _ _ e => by
    refine ConvOp.ext fun c => ?_
    show GrOperad.map (R := R) e (corLin ε A (SymSpecies.map (R := R) e.symm c)) = corLin ε B c
    refine SqExt.ext ?_ ?_
    · show GrOperad.map (R := R) e 0 = 0
      exact map_zero _
    · show map e (corolla R P A (SymSpecies.map (R := R) e.symm c)) = corolla R P B c
      rw [map_corolla, ← SymSpecies.map_trans, Equiv.symm_trans_self, SymSpecies.map_refl]⟩

variable (C) in
/-- **The inclusion `P → 𝒬`** as the first factor, a morphism of graded operads. -/
noncomputable def inclHom : GrOperadHom R P 𝒬 where
  app A _ _ :=
    { toFun := fun y => SqExt.mk y 0
      map_add' := fun y y' => SqExt.ext (by simp) (by simp)
      map_smul' := fun r y => SqExt.ext (by simp) (by simp) }
  app_par b y := SqExt.ext rfl (show (0 : GrComposite R C P _) = par R C P b 0 from
    (map_zero _).symm)
  app_map e y := SqExt.ext rfl (show (0 : GrComposite R C P _) = map e 0 from (map_zero _).symm)
  app_one := rfl
  app_comp i y y' := SqExt.ext rfl (show (0 : GrComposite R C P _) = act R C i y' 0
    + lact R C ε i y 0 by rw [map_zero, map_zero, add_zero])

@[simp] lemma fst_inclHom {A : Type} [Fintype A] [DecidableEq A] (y : P A) :
    SqExt.fst ((inclHom C ε).app A y) = y := rfl

@[simp] lemma snd_inclHom {A : Type} [Fintype A] [DecidableEq A] (y : P A) :
    SqExt.snd ((inclHom C ε).app A y) = 0 := rfl

/-- A family of the convolution operad of `C` and `P`, with values in `𝒬`. -/
noncomputable def liftFam : GrOperad.Inv R (ConvOp R C P) →ₗ[R] GrOperad.Inv R (ConvOp R C 𝒬) :=
  GrOperad.Inv.appHom (ConvOp.postHom (C := C) (inclHom C ε))

/-- An invariant family, as a morphism of linear species. -/
noncomputable def famHom (F : GrOperad.Inv R (ConvOp R C 𝒬)) : SymSpeciesHom R C 𝒬 where
  app A _ _ := ConvOp.toLin (F.1 A)
  app_map {A B} _ _ _ _ e c := by
    rw [← GrOperad.Inv.map_apply F e]
    show ConvOp.toLin (mapC e (F.1 A)) (SymSpecies.map (R := R) e c) = _
    rw [mapC_apply, ← SymSpecies.map_trans, Equiv.self_trans_symm, SymSpecies.map_refl]
    rfl

variable {S : Type} [Fintype S] [DecidableEq S]

/-- **The extension of a family** `F` with values in `𝒬` to `C ∘ P`: the inner operations
included in `𝒬`, total composition, and the second component. -/
noncomputable def twF (F : GrOperad.Inv R (ConvOp R C 𝒬)) (S : Type) [Fintype S]
    [DecidableEq S] : GrComposite R C P S →ₗ[R] GrComposite R C P S :=
  SqExt.snd ∘ₗ total R (famHom ε F) ∘ₗ (map₂ idSpHom (inclHom C ε).toGrSpeciesHom).app S

/-- **The extension is a morphism of right modules.** -/
theorem twF_act {Y : Type} [Fintype Y] [DecidableEq Y] (F : GrOperad.Inv R (ConvOp R C 𝒬))
    (i : S) (z : P Y) (w : GrComposite R C P S) :
    twF ε F _ (act R C i z w) = act R C i z (twF ε F S w) := by
  simp only [twF, LinearMap.comp_apply]
  rw [map₂_act, total_act, SqExt.comp_def, SqExt.snd_compE, fst_inclHom, snd_inclHom, map_zero,
    add_zero]

/-- **The extension commutes with the relabellings.** -/
theorem twF_map {S' : Type} [Fintype S'] [DecidableEq S'] (F : GrOperad.Inv R (ConvOp R C 𝒬))
    (σ : S ≃ S') (w : GrComposite R C P S) :
    twF ε F S' (map σ w) = map σ (twF ε F S w) := by
  simp only [twF, LinearMap.comp_apply]
  rw [show (map₂ idSpHom (inclHom C ε).toGrSpeciesHom).app S' (map σ w)
      = map σ ((map₂ idSpHom (inclHom C ε).toGrSpeciesHom).app S w) from
    (map₂ idSpHom (inclHom C ε).toGrSpeciesHom).app_map σ w, total_map]
  rfl

/-- **The value of the extension on a corolla.** -/
theorem twF_corolla {A : Type} [Fintype A] [DecidableEq A] (F : GrOperad.Inv R (ConvOp R C 𝒬))
    (c : C A) : twF ε F A (corolla R P A c) = SqExt.snd (ConvOp.toLin (F.1 A) c) := by
  simp only [twF, LinearMap.comp_apply]
  rw [corolla_apply, map₂_mk]
  rw [show genMap₂ idSpHom (inclHom C ε).toGrSpeciesHom
      (corGen (C := P) (R := R) (ordOf A) c (Equiv.refl A))
      = corGen (C := 𝒬) (R := R) (ordOf A) c (Equiv.refl A) from rfl, total_corGen,
    GrOperad.map_refl]
  rfl

/-! ## Natural morphisms of right modules are determined on the corollas -/

section Ext

variable {R' : Type u} [CommRing R']
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R' (V A)] [GrSpecies R' V]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R' (N A)] [GrOperad R' N]

/-- **Two families of linear maps of `V ∘ N` commuting with the relabellings and the action agree
as soon as they agree on the corollas.** -/
theorem eq_of_corolla
    (T T' : ∀ (S : Type) [Fintype S] [DecidableEq S],
      GrComposite R' V N S →ₗ[R'] GrComposite R' V N S)
    (hT : ∀ (S S' : Type) [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] (σ : S ≃ S')
      (w : GrComposite R' V N S), T S' (map σ w) = map σ (T S w))
    (hT' : ∀ (S S' : Type) [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] (σ : S ≃ S')
      (w : GrComposite R' V N S), T' S' (map σ w) = map σ (T' S w))
    (hTa : ∀ (S Y : Type) [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y] (i : S)
      (z : N Y) (w : GrComposite R' V N S), T _ (act R' V i z w) = act R' V i z (T S w))
    (hTa' : ∀ (S Y : Type) [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y] (i : S)
      (z : N Y) (w : GrComposite R' V N S), T' _ (act R' V i z w) = act R' V i z (T' S w))
    (hc : ∀ (A : Type) [Fintype A] [DecidableEq A] (v : V A),
      T A (corolla R' N A v) = T' A (corolla R' N A v))
    {S : Type} [Fintype S] [DecidableEq S] (w : GrComposite R' V N S) : T S w = T' S w :=
  induction_act (fun S _ _ w => T S w = T' S w) (fun S _ _ => by simp)
    (fun S _ _ x y hx hy => by simp only [map_add, hx, hy])
    (fun S _ _ r x hx => by simp only [map_smul, hx])
    (fun S S' _ _ _ _ σ x hx => by beta_reduce at hx ⊢; rw [hT, hT', hx])
    (fun S Y _ _ _ _ i z x hx => by beta_reduce at hx ⊢; rw [hTa, hTa', hx]) hc w

end Ext

/-! ## Products with the corollas -/

section Star

variable {X : Type} [Fintype X] [DecidableEq X]

lemma isParC_of_isPar {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q] {p : Bool}
    {β : GrOperad.Inv R (ConvOp R C Q)} (hβ : GrOperad.Inv.IsPar p β) (A : Type) [Fintype A]
    [DecidableEq A] : IsParC p (β.1 A) :=
  parC_eq_self_iff.1 (hβ A)

lemma isPar_liftFam {p : Bool} {β : GrOperad.Inv R (ConvOp R C P)}
    (hβ : GrOperad.Inv.IsPar p β) : GrOperad.Inv.IsPar p (liftFam ε β) := fun A _ _ => by
  show GrOperad.par (R := R) p ((ConvOp.postHom (C := C) (inclHom C ε)).app A (β.1 A)) = _
  rw [← GrOperadHom.app_par, hβ A]
  rfl

/-- The term of a product at a subset, applied. -/
lemma toLin_term {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    (G H : GrOperad.Inv R (ConvOp R C Q)) (S : Finset X) (c : C X) :
    toLin (GrOperad.Inv.term (R := R) G.1 H.1 X S) c
      = GrOperad.map (R := R) (splitEquiv S) (mu none (kap (G.1 (SOut S)) (H.1 (SIn S))
          (GrCooperad.decomp (R := R) none
            (SymSpecies.map (R := R) (splitEquiv S).symm c)))) := rfl

lemma toLin_star {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]
    (G H : GrOperad.Inv R (ConvOp R C Q)) (c : C X) :
    toLin ((GrOperad.Inv.star R (ConvOp R C Q) G H).1 X) c
      = ∑ S ∈ nonempties X, toLin (GrOperad.Inv.term (R := R) G.1 H.1 X S) c := by
  rw [GrOperad.Inv.star_apply, toLin_sum, LinearMap.coe_sum, Finset.sum_apply]

/-- **A product with a family with values in `C ∘ P` keeps its values there.** -/
lemma fst_star {G : GrOperad.Inv R (ConvOp R C 𝒬)}
    (hG : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : C A), SqExt.fst (toLin (G.1 A) c) = 0)
    (H : GrOperad.Inv R (ConvOp R C 𝒬)) (c : C X) :
    SqExt.fst (toLin ((GrOperad.Inv.star R (ConvOp R C 𝒬) G H).1 X) c) = 0 := by
  rw [toLin_star, map_sum]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [toLin_term, SqExt.map_def, SqExt.fst_mapE]
  generalize GrCooperad.decomp (R := R) (C := C) none
    (SymSpecies.map (R := R) (splitEquiv S).symm c) = t
  suffices h : SqExt.fst (mu (R := R) none (kap (G.1 (SOut S)) (H.1 (SIn S)) t)) = 0 by
    rw [h, map_zero]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [kap, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
      mu_tmul, LinearMap.comp_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [SqExt.comp_def, SqExt.fst_compE, hG, LinearMap.map_zero₂]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, add_zero]

lemma fst_corFam {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    SqExt.fst (toLin ((corFam ε).1 A) c) = 0 := rfl

variable {S : Type} [Fintype S] [DecidableEq S]

/-- **The extension of a family with values in `C ∘ P` on a product of the corollas.** -/
theorem twF_snd_star (F : GrOperad.Inv R (ConvOp R C 𝒬))
    (hF : ∀ (A : Type) [Fintype A] [DecidableEq A] (c : C A), SqExt.fst (toLin (F.1 A) c) = 0)
    {p : Bool} {β : GrOperad.Inv R (ConvOp R C P)} (hβ : GrOperad.Inv.IsPar p β) (c : C X) :
    twF ε F X (SqExt.snd (toLin ((GrOperad.Inv.star R _ (corFam ε) (liftFam ε β)).1 X) c))
      = SqExt.snd (toLin ((GrOperad.Inv.star R _ F (liftFam ε β)).1 X) c) := by
  rw [toLin_star, toLin_star, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [toLin_term, toLin_term, SqExt.map_def, SqExt.map_def, SqExt.snd_mapE, SqExt.snd_mapE,
    twF_map]
  congr 1
  generalize GrCooperad.decomp (R := R) (C := C) none
    (SymSpecies.map (R := R) (splitEquiv S).symm c) = t
  have hβ' := isParC_of_isPar (isPar_liftFam ε hβ) (SIn S)
  rw [kap_hom _ hβ', kap_hom _ hβ']
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, mu_tmul, LinearMap.comp_apply, SqExt.comp_def,
      SqExt.snd_compE, hF]
    rw [show toLin ((liftFam ε β).1 (SIn S)) y = (inclHom C ε).app _ (toLin (β.1 (SIn S)) y)
      from rfl, fst_inclHom, snd_inclHom, map_zero, add_zero, twF_act]
    rw [map_zero, add_zero]
    congr 1
    exact twF_corolla ε F (A := SOut S) _
  | add a b ha hb => simp only [map_add, ha, hb]

end Star

/-! ## The twisted differential -/

section TwD

variable {S : Type} [Fintype S] [DecidableEq S]

/-- **The twisted differential** `d_β` of `C ∘ P`, for an invariant family `β` of the convolution
operad: the extension of the product of the corollas with `β`. -/
noncomputable def twD (β : GrOperad.Inv R (ConvOp R C P)) (S : Type) [Fintype S]
    [DecidableEq S] : GrComposite R C P S →ₗ[R] GrComposite R C P S :=
  twF ε (GrOperad.Inv.star R _ (corFam ε) (liftFam ε β)) S

lemma twD_corolla {A : Type} [Fintype A] [DecidableEq A] (β : GrOperad.Inv R (ConvOp R C P))
    (c : C A) : twD ε β A (corolla R P A c)
      = SqExt.snd (toLin ((GrOperad.Inv.star R _ (corFam ε) (liftFam ε β)).1 A) c) :=
  twF_corolla ε _ c

/-- **The composite of two twisted differentials** is the extension of `(cor ⋆ α) ⋆ β`. -/
theorem twD_twD {α β : GrOperad.Inv R (ConvOp R C P)} {p : Bool}
    (hβ : GrOperad.Inv.IsPar p β) (w : GrComposite R C P S) :
    twD ε α S (twD ε β S w) = twF ε (GrOperad.Inv.star R _
      (GrOperad.Inv.star R _ (corFam ε) (liftFam ε α)) (liftFam ε β)) S w :=
  eq_of_corolla (fun S _ _ => twD ε α S ∘ₗ twD ε β S) (fun S _ _ => twF ε _ S)
    (fun S S' _ _ _ _ σ w => by simp only [LinearMap.comp_apply, twD, twF_map])
    (fun S S' _ _ _ _ σ w => twF_map ε _ σ w)
    (fun S Y _ _ _ _ i z w => by simp only [LinearMap.comp_apply, twD, twF_act])
    (fun S Y _ _ _ _ i z w => twF_act ε _ i z w)
    (fun A _ _ c => by
      rw [LinearMap.comp_apply, twD_corolla, twF_corolla]
      exact twF_snd_star ε (GrOperad.Inv.star R _ (corFam ε) (liftFam ε α))
        (fun A _ _ c => fst_star ε (fun A _ _ c => fst_corFam ε c) _ c) hβ c)
    w

/-- **The square of the twisted differential of an odd family** is the twisted differential of its
square. -/
theorem twD_sq {α : GrOperad.Inv R (ConvOp R C P)} (hα : GrOperad.Inv.IsPar true α)
    (w : GrComposite R C P S) :
    twD ε α S (twD ε α S w) = twD ε (GrOperad.Inv.star R _ α α) S w := by
  rw [twD_twD ε hα, GrOperad.Inv.assoc_odd _ _ (isPar_liftFam ε hα), twD, liftFam,
    GrOperad.Inv.appHom_star]

/-- The twisted differential of the zero family vanishes. -/
theorem twD_zero (w : GrComposite R C P S) : twD ε 0 S w = 0 :=
  eq_of_corolla (fun S _ _ => twD ε 0 S) (fun S _ _ => 0)
    (fun S S' _ _ _ _ σ w => twF_map ε _ σ w) (fun S S' _ _ _ _ σ w => by simp)
    (fun S Y _ _ _ _ i z w => twF_act ε _ i z w) (fun S Y _ _ _ _ i z w => by simp)
    (fun A _ _ c => by
      rw [twD_corolla, map_zero, map_zero, LinearMap.zero_apply]
      rfl)
    w

/-- **The twisted differential of an odd family with vanishing square squares to zero.** -/
theorem twD_twD_eq_zero {α : GrOperad.Inv R (ConvOp R C P)} (hα : GrOperad.Inv.IsPar true α)
    (h : GrOperad.Inv.star R _ α α = 0) (w : GrComposite R C P S) :
    twD ε α S (twD ε α S w) = 0 := by
  rw [twD_sq ε hα, h, twD_zero]

end TwD

end GrComposite

end Operad
