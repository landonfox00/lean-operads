/-
# Comparison of twisted composite products

The twisted composite product `C ∘_β P` is filtered by **the number of inputs of the outer
cooperation** (`GrComposite.outerSpan`): the differential at the inner operations preserves it,
and for a reduced cooperad `C` and a family `β` vanishing on the coaugmentation, **the twisted
differential lowers it** (`GrComposite.twD_mem_outerLt`), every term of `(cor ⋆ β)(c)` splitting
off at least two inputs of `c`. The twisted differential is natural in morphisms of graded
operads (`GrComposite.map₂_twD`).
-/
import Operad.GrTwistedDG
import Operad.GrLeafKunneth

universe u v w

namespace Operad

open Function Sym GerBV ConvOp

namespace GrComposite

/-! ## Spans of generators by the number of inputs of the outer operation -/

section OuterSpan

variable {R : Type u} [CommRing R]
  {M : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (M A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (M A)] [GrSpecies R M]
  {N : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N A)] [GrSpecies R N]
  {N' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (N' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (N' A)] [GrSpecies R N']
  {S : Type} [Fintype S] [DecidableEq S]

variable (R M N) in
/-- The span of the generators whose outer operation has a number of inputs satisfying `P`. -/
noncomputable def outerSpanP (S : Type) [Fintype S] [DecidableEq S] (P : ℕ → Prop) :
    Submodule R (GrComposite R M N S) :=
  Submodule.span R {x | ∃ g : GrCompGen M N S, P (Fintype.card g.A) ∧ x = mk R g}

variable (R M N) in
/-- **The composites with an outer operation of `k` inputs.** -/
noncomputable abbrev outerSpan (S : Type) [Fintype S] [DecidableEq S] (k : ℕ) :
    Submodule R (GrComposite R M N S) :=
  outerSpanP R M N S (· = k)

variable (R M N) in
/-- **The composites with an outer operation of fewer than `k` inputs.** -/
noncomputable abbrev outerLt (S : Type) [Fintype S] [DecidableEq S] (k : ℕ) :
    Submodule R (GrComposite R M N S) :=
  outerSpanP R M N S (· < k)

lemma mk_mem_outerSpanP {P : ℕ → Prop} (g : GrCompGen M N S) (h : P (Fintype.card g.A)) :
    mk R g ∈ outerSpanP R M N S P :=
  Submodule.subset_span ⟨g, h, rfl⟩

lemma outerSpanP_mono {P P' : ℕ → Prop} (h : ∀ k, P k → P' k) :
    outerSpanP R M N S P ≤ outerSpanP R M N S P' :=
  Submodule.span_mono fun _ ⟨g, hg, hx⟩ => ⟨g, h _ hg, hx⟩

/-- **A linear map sending the generators into a span sends the span there.** -/
lemma map_mem_outerSpanP {X : Type*} [AddCommGroup X] [Module R X] {P : ℕ → Prop}
    (T : GrComposite R M N S →ₗ[R] X) (W : Submodule R X)
    (hT : ∀ g : GrCompGen M N S, P (Fintype.card g.A) → T (mk R g) ∈ W) {x : GrComposite R M N S}
    (hx : x ∈ outerSpanP R M N S P) : T x ∈ W := by
  have h : outerSpanP R M N S P ≤ W.comap T :=
    Submodule.span_le.2 fun _ ⟨g, hg, hx⟩ => hx ▸ hT g hg
  exact h hx

lemma outerLt_zero : outerLt R M N S 0 = ⊥ := by
  rw [eq_bot_iff]
  apply Submodule.span_le.2
  rintro _ ⟨g, hg, -⟩
  exact absurd hg (Nat.not_lt_zero _)

lemma outerLt_succ (k : ℕ) :
    outerLt R M N S (k + 1) = outerSpan R M N S k ⊔ outerLt R M N S k := by
  refine le_antisymm ?_ (sup_le (outerSpanP_mono fun _ h => by omega)
    (outerSpanP_mono fun _ h => by omega))
  apply Submodule.span_le.2
  rintro _ ⟨g, hg, rfl⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hg with h | h
  · exact Submodule.mem_sup_right (mk_mem_outerSpanP g h)
  · exact Submodule.mem_sup_left (mk_mem_outerSpanP g h)

lemma outerSpanP_le_outerEig (k : ℕ) : outerSpan R M N S k ≤ outerEig R M N S k := by
  apply Submodule.span_le.2
  rintro _ ⟨g, hg, rfl⟩
  have := mk_mem_outerEig (R := R) g
  rwa [hg] at this

lemma outerLt_le_iSup (k : ℕ) :
    outerLt R M N S k ≤ ⨆ j : Fin k, outerEig R M N S (j : ℕ) := by
  apply Submodule.span_le.2
  rintro _ ⟨g, hg, rfl⟩
  exact Submodule.mem_iSup_of_mem (⟨_, hg⟩ : Fin k) (mk_mem_outerEig g)

/-- **The composites with an outer operation of `k` inputs and of fewer inputs are independent.**
-/
lemma disjoint_outerSpan_outerLt [IsDomain R] [CharZero R] [NoZeroSMulDivisors R (GrComposite R M N S)]
    (k : ℕ) : Disjoint (outerSpan R M N S k) (outerLt R M N S k) := by
  refine Disjoint.mono (outerSpanP_le_outerEig k) (outerLt_le_iSup k) ?_
  have hind := Module.End.eigenspaces_iSupIndep (outerN R M N S)
  have h := hind.disjoint_biSup (x := (k : R)) (y := Set.range fun j : Fin k => ((j : ℕ) : R))
    (by
      rintro ⟨j, hj⟩
      exact absurd (Nat.cast_injective hj) (Nat.ne_of_lt j.2))
  refine h.mono_right (iSup_le fun j => ?_)
  exact le_iSup₂_of_le ((j : ℕ) : R) ⟨j, rfl⟩ le_rfl

/-! ### Preservation -/

lemma map₂_mem_outerSpanP {P : ℕ → Prop} (ψ : GrSpeciesHom R N N') {x : GrComposite R M N S}
    (hx : x ∈ outerSpanP R M N S P) :
    (map₂ idSpHom ψ).app S x ∈ outerSpanP R M N' S P :=
  map_mem_outerSpanP _ _ (fun g hg => by
    rw [map₂_mk]
    exact mk_mem_outerSpanP _ hg) hx

lemma leafMap_mem_outerSpanP {P : ℕ → Prop} {q : Bool} (gm : GrSpEnd R N q)
    {x : GrComposite R M N S} (hx : x ∈ outerSpanP R M N S P) :
    leafMap R M gm x ∈ outerSpanP R M N S P :=
  map_mem_outerSpanP _ _ (fun g hg => by
    rw [leafMap_mk, leafFun]
    exact Submodule.sum_mem _ fun j _ => mk_mem_outerSpanP _ hg) hx

lemma relabel_mem_outerSpanP {P : ℕ → Prop} {S' : Type} [Fintype S'] [DecidableEq S'] (σ : S ≃ S')
    {x : GrComposite R M N S} (hx : x ∈ outerSpanP R M N S P) :
    map σ x ∈ outerSpanP R M N S' P :=
  map_mem_outerSpanP (map σ) _ (fun g hg => by
    rw [map_mk]
    exact mk_mem_outerSpanP _ hg) hx

end OuterSpan

section Act

variable {R : Type u} [CommRing R]
  {V : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (V A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (V A)] [GrSpecies R V]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {S : Type} [Fintype S] [DecidableEq S]

lemma act_mem_outerSpanP {Pr : ℕ → Prop} {Y : Type} [Fintype Y] [DecidableEq Y] (i : S)
    (z : P Y) {x : GrComposite R V P S} (hx : x ∈ outerSpanP R V P S Pr) :
    act R V i z x ∈ outerSpanP R V P _ Pr :=
  map_mem_outerSpanP (act R V i z) _ (fun g hg => by
    rw [act_mk, actFun, actOwn]
    exact Submodule.sum_mem _ fun q _ => mk_mem_outerSpanP _ hg) hx

lemma corolla_mem_outerSpan {A : Type} [Fintype A] [DecidableEq A] (v : V A) :
    corolla R P A v ∈ outerSpan R V P A (Fintype.card A) := by
  rw [corolla_apply]
  exact mk_mem_outerSpanP _ rfl

end Act

/-! ## The twisted differential lowers the number of inputs of the outer operation -/

section Lower

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  (ε : GrAug R P) {S : Type} [Fintype S] [DecidableEq S]

omit [GrCooperad R C] in
lemma card_sOut {X : Type} [Fintype X] [DecidableEq X] (T : Finset X) :
    Fintype.card (SOut T) = Fintype.card X - T.card + 1 := by
  rw [Fintype.card_option, Fintype.card_subtype_compl, Fintype.card_coe]

/-- **The twisted differential of a corolla has outer operations of fewer inputs**, for a family
vanishing in the arities of one element. -/
lemma twD_corolla_mem {β : GrOperad.Inv R (ConvOp R C P)} {p : Bool}
    (hβ : GrOperad.Inv.IsPar p β)
    (hβ1 : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = 1 →
      ∀ x : C A, toLin (β.1 A) x = 0)
    {X : Type} [Fintype X] [DecidableEq X] (c : C X) :
    twD ε β X (corolla R P X c) ∈ outerLt R C P X (Fintype.card X) := by
  rw [twD_corolla, toLin_star, map_sum]
  refine Submodule.sum_mem _ fun T hT => ?_
  rw [toLin_term, SqExt.map_def, SqExt.snd_mapE]
  refine relabel_mem_outerSpanP _ ?_
  generalize GrCooperad.decomp (R := R) (C := C) none
    (SymSpecies.map (R := R) (splitEquiv T).symm c) = t
  rw [kap_hom _ (isParC_of_isPar (isPar_liftFam ε hβ) (SIn T))]
  have hT1 : 1 ≤ T.card := Finset.card_pos.2 (Finset.mem_filter.1 hT).2
  have hTX : T.card ≤ Fintype.card X := Finset.card_le_univ T
  by_cases hcard : T.card = 1
  · have h0 : ∀ y : C (SIn T), toLin ((liftFam ε β).1 (SIn T)) y = 0 := fun y => by
      show (inclHom C ε).app _ (toLin (β.1 (SIn T)) y) = 0
      rw [hβ1 _ (by rw [Fintype.card_coe, hcard]) y, map_zero]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [TensorProduct.map_tmul, h0, TensorProduct.tmul_zero, map_zero, map_zero]
      exact zero_mem _
    | add a b ha hb =>
      rw [map_add, map_add, map_add]
      exact add_mem ha hb
  · have hlt : Fintype.card (SOut T) < Fintype.card X := by
      rw [card_sOut]
      omega
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [TensorProduct.map_tmul, mu_tmul, LinearMap.comp_apply, SqExt.comp_def,
        SqExt.snd_compE]
      rw [show toLin ((liftFam ε β).1 (SIn T)) y = (inclHom C ε).app _ (toLin (β.1 (SIn T)) y)
        from rfl, fst_inclHom, snd_inclHom, map_zero, add_zero]
      refine act_mem_outerSpanP _ _ (outerSpanP_mono (P := (· = Fintype.card (SOut T)))
        (fun _ h => h ▸ hlt) ?_)
      exact corolla_mem_outerSpan _
    | add a b ha hb =>
      rw [map_add, map_add, map_add]
      exact add_mem ha hb

/-- **The twisted differential lowers the number of inputs of the outer operation.** -/
theorem twD_mem_outerLt {β : GrOperad.Inv R (ConvOp R C P)} {p : Bool}
    (hβ : GrOperad.Inv.IsPar p β)
    (hβ1 : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = 1 →
      ∀ x : C A, toLin (β.1 A) x = 0)
    {k : ℕ} {x : GrComposite R C P S} (hx : x ∈ outerSpan R C P S k) :
    twD ε β S x ∈ outerLt R C P S k :=
  map_mem_outerSpanP (twD ε β S) _ (fun g hg =>
    induction_card (fun S _ _ w => twD ε β S w ∈ outerLt R C P S k)
      (fun S _ _ => by beta_reduce; simp)
      (fun S _ _ x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
      (fun S _ _ r x hx => by
        beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ r hx)
      (fun S S' _ _ _ _ σ x hx => by
        beta_reduce at hx ⊢
        rw [twD, twF_map]
        exact relabel_mem_outerSpanP σ hx)
      (fun S Y _ _ _ _ i z x hx => by
        beta_reduce at hx ⊢
        rw [twD, twF_act]
        exact act_mem_outerSpanP i z hx)
      (fun A _ _ w hA => by
        beta_reduce
        rw [← hA]
        exact twD_corolla_mem ε hβ hβ1 w) g hg) hx

lemma twD_mem_outerLt_of_lt {β : GrOperad.Inv R (ConvOp R C P)} {p : Bool}
    (hβ : GrOperad.Inv.IsPar p β)
    (hβ1 : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = 1 →
      ∀ x : C A, toLin (β.1 A) x = 0)
    {k : ℕ} {x : GrComposite R C P S} (hx : x ∈ outerLt R C P S k) :
    twD ε β S x ∈ outerLt R C P S k :=
  map_mem_outerSpanP (twD ε β S) _ (fun g hg => outerSpanP_mono (P := (· < Fintype.card g.A))
    (fun _ h => h.trans hg) (twD_mem_outerLt ε hβ hβ1 (mk_mem_outerSpanP g rfl))) hx

end Lower

/-! ## Naturality of the twisted differential -/

section Natural

variable {R : Type u} [CommRing R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [GrOperad R P']
  (ε : GrAug R P) (ε' : GrAug R P') (g : GrOperadHom R P' P)
  {S : Type} [Fintype S] [DecidableEq S]

lemma map₂_corolla {A : Type} [Fintype A] [DecidableEq A] (c : C A) :
    (map₂ idSpHom g.toGrSpeciesHom).app A (corolla R P' A c) = corolla R P A c := by
  rw [corolla_apply, corolla_apply, map₂_mk]
  show mk R ⟨A, fun _ => Unit, ordOf A, c, fun _ => g.app Unit (GrOperad.one (R := R)),
    (Equiv.sigmaPUnit A).trans (Equiv.refl A)⟩ = _
  simp only [g.app_one]

lemma isPar_appHom {β : GrOperad.Inv R (ConvOp R C P')} {p : Bool}
    (hβ : GrOperad.Inv.IsPar p β) :
    GrOperad.Inv.IsPar p (GrOperad.Inv.appHom (postHom (C := C) g) β) := fun A _ _ => by
  show GrOperad.par (R := R) p ((postHom (C := C) g).app A (β.1 A)) = _
  rw [← GrOperadHom.app_par, hβ A]
  rfl

/-- **The twisted differential is natural** in morphisms of graded operads. -/
theorem map₂_twD {β : GrOperad.Inv R (ConvOp R C P')} {p : Bool} (hβ : GrOperad.Inv.IsPar p β)
    (w : GrComposite R C P' S) :
    (map₂ idSpHom g.toGrSpeciesHom).app S (twD ε' β S w)
      = twD ε (GrOperad.Inv.appHom (postHom (C := C) g) β) S
          ((map₂ idSpHom g.toGrSpeciesHom).app S w) := by
  refine induction_act (fun S _ _ w => (map₂ idSpHom g.toGrSpeciesHom).app S (twD ε' β S w)
      = twD ε (GrOperad.Inv.appHom (postHom (C := C) g) β) S
          ((map₂ idSpHom g.toGrSpeciesHom).app S w))
    (fun S _ _ => by simp) (fun S _ _ x y hx hy => by simp only [map_add, hx, hy])
    (fun S _ _ r x hx => by simp only [map_smul, hx])
    (fun S S' _ _ _ _ σ x hx => ?_) (fun S Y _ _ _ _ i z x hx => ?_) (fun A _ _ c => ?_) w
  · beta_reduce at hx ⊢
    rw [twD, twF_map, show (map₂ idSpHom g.toGrSpeciesHom).app S' (map σ x)
      = map σ ((map₂ idSpHom g.toGrSpeciesHom).app S x) from
        (map₂ idSpHom g.toGrSpeciesHom).app_map σ x,
      show (map₂ idSpHom g.toGrSpeciesHom).app S' (map σ (twF ε' _ S x))
        = map σ ((map₂ idSpHom g.toGrSpeciesHom).app S (twF ε' _ S x)) from
        (map₂ idSpHom g.toGrSpeciesHom).app_map σ _, twD, twF_map]
    exact congrArg (map σ) hx
  · beta_reduce at hx ⊢
    rw [twD, twF_act, map₂_act, map₂_act, twD, twF_act]
    exact congrArg _ hx
  · beta_reduce
    rw [map₂_corolla, twD_corolla, twD_corolla, toLin_star, toLin_star, map_sum, map_sum,
      map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [toLin_term, toLin_term, SqExt.map_def, SqExt.map_def, SqExt.snd_mapE, SqExt.snd_mapE,
      show (map₂ idSpHom g.toGrSpeciesHom).app A (map (splitEquiv T) _)
        = map (splitEquiv T) ((map₂ idSpHom g.toGrSpeciesHom).app _ _) from
        (map₂ idSpHom g.toGrSpeciesHom).app_map _ _]
    congr 1
    generalize GrCooperad.decomp (R := R) (C := C) none
      (SymSpecies.map (R := R) (splitEquiv T).symm c) = t
    rw [kap_hom _ (isParC_of_isPar (isPar_liftFam ε' hβ) (SIn T)),
      kap_hom _ (isParC_of_isPar (isPar_liftFam ε (isPar_appHom g hβ)) (SIn T))]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [TensorProduct.map_tmul, mu_tmul, LinearMap.comp_apply, SqExt.comp_def,
        SqExt.snd_compE]
      rw [show toLin ((liftFam ε' β).1 (SIn T)) y
          = (inclHom C ε').app _ (toLin (β.1 (SIn T)) y) from rfl,
        show toLin ((liftFam ε (GrOperad.Inv.appHom (postHom (C := C) g) β)).1 (SIn T)) y
          = (inclHom C ε).app _ (g.app _ (toLin (β.1 (SIn T)) y)) from rfl,
        fst_inclHom, snd_inclHom, fst_inclHom, snd_inclHom, map_zero, add_zero, map_zero,
        add_zero, map₂_act]
      congr 1
      exact map₂_corolla g _
    | add a b ha hb => simp only [map_add, ha, hb]

end Natural

end GrComposite

end Operad
