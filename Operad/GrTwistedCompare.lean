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
import Operad.FreeGrCompare

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

/-- **The composites with an outer operation of `k` inputs and of fewer inputs are independent**,
over a `ℚ`-algebra. -/
lemma disjoint_outerSpan_outerLt [Algebra ℚ R] (k : ℕ) :
    Disjoint (outerSpan R M N S k) (outerLt R M N S k) := by
  have hind := iSupIndep_eigenspace_nat (R := R) (outerN R M N S)
  have h := hind.disjoint_biSup (x := k) (y := {j | j < k}) (by simp)
  refine h.mono (outerSpanP_le_outerEig k) ?_
  apply Submodule.span_le.2
  rintro _ ⟨g, hg, rfl⟩
  exact (le_biSup (fun j : ℕ => outerEig R M N S j) (show Fintype.card g.A ∈ {j | j < k} from hg))
    (mk_mem_outerEig g)

lemma mem_iSup_outerSpan (x : GrComposite R M N S) : x ∈ ⨆ j : ℕ, outerSpan R M N S j := by
  induction x using induction_on with
  | h0 => exact zero_mem _
  | hadd x y hx hy => exact add_mem hx hy
  | hsmul c x hx => exact Submodule.smul_mem _ c hx
  | hmk g => exact Submodule.mem_iSup_of_mem (Fintype.card g.A) (mk_mem_outerSpanP g rfl)

/-- **The eigenspaces of the number of inputs of the outer operation are the spans of the
generators**, over a `ℚ`-algebra. -/
theorem outerEig_le_outerSpan [Algebra ℚ R] (k : ℕ) :
    outerEig R M N S k ≤ outerSpan R M N S k := by
  intro x hx
  have hind := iSupIndep_eigenspace_nat (R := R) (outerN R M N S)
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).1 (mem_iSup_outerSpan x)
  let φ : GrComposite R M N S →ₗ[R] GrComposite R M N S :=
    outerN R M N S - (k : R) • LinearMap.id
  have hφ : ∀ j, φ (f j) = ((j : R) - k) • f j := fun j => by
    simp only [φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Module.End.mem_eigenspace_iff.1 (outerSpanP_le_outerEig j (hf j)), sub_smul]
  have h0 : ∀ j, φ (f j) = 0 := iSupIndep_finsupp_eq_zero hind (f.mapRange φ (map_zero φ))
    (fun j => by
      rw [Finsupp.mapRange_apply, hφ]
      exact Submodule.smul_mem _ _ (outerSpanP_le_outerEig j (hf j)))
    (by
      rw [Finsupp.sum_mapRange_index (fun _ => rfl), ← map_finsuppSum]
      simp only [φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Module.End.mem_eigenspace_iff.1 hx, sub_self])
  have hz : ∀ j, j ≠ k → f j = 0 := fun j hj => by
    have h1 := h0 j
    rw [hφ] at h1
    have hu : IsUnit ((j : R) - k) := by
      have : ((j : ℚ) - k) ≠ 0 := sub_ne_zero.2 (Nat.cast_injective.ne hj)
      have h2 := (isUnit_iff_ne_zero.2 this).map (algebraMap ℚ R)
      rwa [map_sub, map_natCast, map_natCast] at h2
    exact hu.smul_eq_zero.1 h1
  rw [Finsupp.sum_eq_single k (fun j _ hj => hz j hj) (fun _ => rfl)]
  exact hf k

/-- **Generators with more outer inputs than inputs vanish**, without inner operations with no
inputs. -/
lemma outerLt_eq_top
    (hN0 : ∀ (B : Type) [Fintype B] [DecidableEq B], IsEmpty B → ∀ y : N B, y = 0) :
    outerLt R M N S (Fintype.card S + 1) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  clear ‹x ∈ ⊤›
  induction x using induction_on with
  | h0 => exact zero_mem _
  | hadd x y hx hy => exact add_mem hx hy
  | hsmul c x hx => exact Submodule.smul_mem _ c hx
  | hmk g =>
    by_cases hg : Fintype.card g.A < Fintype.card S + 1
    · exact mk_mem_outerSpanP g hg
    · have hex : ∃ a, IsEmpty (g.B a) := by
        by_contra hne
        simp only [not_exists, not_isEmpty_iff] at hne
        have h1 : Fintype.card g.A ≤ Fintype.card S := by
          rw [← Fintype.card_congr g.e, Fintype.card_sigma]
          calc Fintype.card g.A = ∑ _a : g.A, 1 := by simp
            _ ≤ ∑ a, Fintype.card (g.B a) := Finset.sum_le_sum fun a _ =>
              Fintype.card_pos_iff.2 (hne a)
        omega
      obtain ⟨a, ha⟩ := hex
      rw [mk_of_y_eq_zero g (hN0 _ ha (g.y a))]
      exact zero_mem _


/-! ### Projections -/

variable (R M N) in
/-- **The projection onto the generators whose outer operation has a number of inputs satisfying
`P`.** -/
noncomputable def outerProj (S : Type) [Fintype S] [DecidableEq S] (P : ℕ → Prop)
    [DecidablePred P] : GrComposite R M N S →ₗ[R] GrComposite R M N S :=
  lift (fun g => if P (Fintype.card g.A) then mk R g else 0)
    { add_m := fun g m' => by
        dsimp only
        split_ifs
        · exact mk_add_m g m'
        · rw [add_zero]
      smul_m := fun g c => by
        dsimp only
        split_ifs
        · exact mk_smul_m g c
        · rw [smul_zero]
      add_y := fun g a z z' => by
        dsimp only
        split_ifs
        · exact mk_add_y g a z z'
        · rw [add_zero]
      smul_y := fun g a c z => by
        dsimp only
        split_ifs
        · exact mk_smul_y g a c z
        · rw [smul_zero]
      outer := fun g A _ _ σ m => by
        dsimp only
        rw [show Fintype.card A = Fintype.card g.A from Fintype.card_congr σ]
        split_ifs
        · exact mk_outer g σ m
        · rfl
      inner := fun g B _ _ τ => by
        dsimp only
        split_ifs
        · exact mk_inner g τ
        · rfl
      reorder := fun g L' c hy => by
        dsimp only
        split_ifs
        · exact mk_reorder g L' c hy
        · rw [smul_zero] }

lemma outerProj_mk (P : ℕ → Prop) [DecidablePred P] (g : GrCompGen M N S) :
    outerProj R M N S P (mk R g) = if P (Fintype.card g.A) then mk R g else 0 :=
  lift_mk _ _ g

lemma outerProj_mem (P : ℕ → Prop) [DecidablePred P] (x : GrComposite R M N S) :
    outerProj R M N S P x ∈ outerSpanP R M N S P := by
  induction x using induction_on with
  | h0 => rw [map_zero]; exact zero_mem _
  | hadd x y hx hy => rw [map_add]; exact add_mem hx hy
  | hsmul c x hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  | hmk g =>
    rw [outerProj_mk]
    split_ifs with h
    · exact mk_mem_outerSpanP g h
    · exact zero_mem _

lemma outerProj_of_mem (P : ℕ → Prop) [DecidablePred P] {x : GrComposite R M N S}
    (hx : x ∈ outerSpanP R M N S P) : outerProj R M N S P x = x := by
  have h : outerSpanP R M N S P ≤ LinearMap.ker (outerProj R M N S P - LinearMap.id) :=
    Submodule.span_le.2 fun _ ⟨g, hg, hx⟩ => by
      rw [hx, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, outerProj_mk, if_pos hg,
        LinearMap.id_apply, sub_self]
  have := h hx
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this

lemma outerProj_eq_zero (P Q : ℕ → Prop) [DecidablePred P] (hPQ : ∀ k, Q k → ¬ P k)
    {x : GrComposite R M N S} (hx : x ∈ outerSpanP R M N S Q) : outerProj R M N S P x = 0 := by
  have h : outerSpanP R M N S Q ≤ LinearMap.ker (outerProj R M N S P) :=
    Submodule.span_le.2 fun _ ⟨g, hg, hx⟩ => by
      rw [hx, SetLike.mem_coe, LinearMap.mem_ker, outerProj_mk, if_neg (hPQ _ hg)]
  exact h hx

lemma outerProj_add_compl (P : ℕ → Prop) [DecidablePred P] (x : GrComposite R M N S) :
    outerProj R M N S P x + outerProj R M N S (fun k => ¬ P k) x = x := by
  induction x using induction_on with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, add_add_add_comm, hx, hy]
  | hsmul c x hx => rw [map_smul, map_smul, ← smul_add, hx]
  | hmk g =>
    rw [outerProj_mk, outerProj_mk]
    by_cases h : P (Fintype.card g.A)
    · rw [if_pos h, if_neg (not_not.2 h), add_zero]
    · rw [if_neg h, if_pos h, zero_add]

lemma outerProj_map₂ (P : ℕ → Prop) [DecidablePred P] (ψ : GrSpeciesHom R N N')
    (x : GrComposite R M N S) :
    outerProj R M N' S P ((map₂ idSpHom ψ).app S x)
      = (map₂ idSpHom ψ).app S (outerProj R M N S P x) := by
  have h : (outerProj R M N' S P).comp ((map₂ idSpHom ψ).app S)
      = ((map₂ idSpHom ψ).app S).comp (outerProj R M N S P) := hom_ext fun g => by
    simp only [LinearMap.comp_apply, map₂_mk, outerProj_mk]
    split_ifs
    · rw [map₂_mk]
    · rw [map_zero]
  exact LinearMap.congr_fun h x

lemma outerProj_leafMap (P : ℕ → Prop) [DecidablePred P] {q : Bool} (gm : GrSpEnd R N q)
    (x : GrComposite R M N S) :
    outerProj R M N S P (leafMap R M gm x) = leafMap R M gm (outerProj R M N S P x) := by
  have h : (outerProj R M N S P).comp (leafMap R M gm)
      = (leafMap R M gm).comp (outerProj R M N S P) := hom_ext fun g => by
    simp only [LinearMap.comp_apply, leafMap_mk, leafFun, map_sum, outerProj_mk]
    split_ifs with hg
    · rw [leafMap_mk]
      rfl
    · rw [map_zero]
      exact Finset.sum_eq_zero fun j _ => rfl
  exact LinearMap.congr_fun h x

/-- Without generators with no inputs, there are none with an outer operation without inputs. -/
lemma outerLt_one_eq_bot (h : Nonempty S) : outerLt R M N S 1 = ⊥ := by
  rw [eq_bot_iff]
  apply Submodule.span_le.2
  rintro _ ⟨g, hg, rfl⟩
  have hA : IsEmpty g.A := Fintype.card_eq_zero_iff.1 (by omega)
  obtain ⟨s⟩ := h
  exact hA.elim (g.e.symm s).1

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

/-! ## Quasi-isomorphisms of twisted composite products -/

section Compare

variable {R : Type u} [Field R] [CharZero R]
  {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [GrOperad R P]
  {P' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P' A)] [GrOperad R P']
  (ε : GrAug R P) (ε' : GrAug R P')
  (D : GrDer (GrOperadHom.id R P) true) (D' : GrDer (GrOperadHom.id R P') true)
  (g : GrOperadHom R P' P)

/-- **The data of a comparison of twisted composite products** `C ∘_β' P' → C ∘_β P` along a
morphism `g : P' → P` of graded operads with differentials: odd families vanishing in the arities
of one element, related by `g`, with differentials squaring to zero, and no operations without
inputs. -/
structure TwCompareData (β : GrOperad.Inv R (ConvOp R C P))
    (β' : GrOperad.Inv R (ConvOp R C P')) : Prop where
  hD : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), D.app A (D.app A x) = 0
  hD' : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P' A), D'.app A (D'.app A x) = 0
  hg : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P' A),
    g.app A (D'.app A x) = D.app A (g.app A x)
  hβ : GrOperad.Inv.IsPar true β
  hβ' : GrOperad.Inv.IsPar true β'
  hβ1 : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = 1 →
    ∀ x : C A, toLin (β.1 A) x = 0
  hβ1' : ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = 1 →
    ∀ x : C A, toLin (β'.1 A) x = 0
  nat : ∀ (S : Type) [Fintype S] [DecidableEq S] (w : GrComposite R C P' S),
    (map₂ idSpHom g.toGrSpeciesHom).app S (twD ε' β' S w)
      = twD ε β S ((map₂ idSpHom g.toGrSpeciesHom).app S w)
  dd : ∀ (S : Type) [Fintype S] [DecidableEq S] (w : GrComposite R C P S),
    twDiff R C ε D β S (twDiff R C ε D β S w) = 0
  dd' : ∀ (S : Type) [Fintype S] [DecidableEq S] (w : GrComposite R C P' S),
    twDiff R C ε' D' β' S (twDiff R C ε' D' β' S w) = 0
  hP0 : ∀ (B : Type) [Fintype B] [DecidableEq B], IsEmpty B → ∀ y : P B, y = 0
  hP0' : ∀ (B : Type) [Fintype B] [DecidableEq B], IsEmpty B → ∀ y : P' B, y = 0

variable {ε ε' D D' g} {β : GrOperad.Inv R (ConvOp R C P)} {β' : GrOperad.Inv R (ConvOp R C P')}
  (hd : TwCompareData ε ε' D D' g β β') {S : Type} [Fintype S] [DecidableEq S]

include hd

omit [CharZero R] in
lemma TwCompareData.leaf_comm (x : GrComposite R C P' S) :
    (map₂ idSpHom g.toGrSpeciesHom).app S (leafD R C D' S x)
      = leafD R C D S ((map₂ idSpHom g.toGrSpeciesHom).app S x) :=
  map₂_leafMap idSpHom (fun _ _ _ _ => rfl) g.toGrSpeciesHom D'.toSpEnd D.toSpEnd
    (fun A _ _ y => hd.hg A y) x

/-- The graded pieces of the filtration by the number of outer inputs, from the most. -/
noncomputable def filtX (P₀ : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P₀ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P₀ A)] [GrOperad R P₀]
    (S : Type) [Fintype S] [DecidableEq S] (p : ℕ) : Submodule R (GrComposite R C P₀ S) :=
  if p ≤ Fintype.card S then outerSpan R C P₀ S (Fintype.card S - p) else ⊥

omit hd [CharZero R] in
lemma filt_sup (P₀ : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P₀ A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P₀ A)] [GrOperad R P₀] (p : ℕ) :
    outerLt R C P₀ S (Fintype.card S + 1 - p)
      = filtX P₀ S p ⊔ outerLt R C P₀ S (Fintype.card S + 1 - (p + 1)) := by
  unfold filtX
  split_ifs with hp
  · rw [show Fintype.card S + 1 - p = (Fintype.card S - p) + 1 by omega,
      show Fintype.card S + 1 - (p + 1) = Fintype.card S - p by omega, outerLt_succ]
  · rw [show Fintype.card S + 1 - p = 0 by omega, show Fintype.card S + 1 - (p + 1) = 0 by omega,
      bot_sup_eq]

lemma TwCompareData.filtData :
    QIso.FiltData (filtX P' S) (fun p => outerLt R C P' S (Fintype.card S + 1 - p))
      (filtX P S) (fun p => outerLt R C P S (Fintype.card S + 1 - p)) (Fintype.card S + 1)
      (leafD R C D' S) (twD ε' β' S) (leafD R C D S) (twD ε β S)
      ((map₂ idSpHom g.toGrSpeciesHom).app S) where
  split p := by
    refine ⟨?_, fun x => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw => ?_⟩
    · unfold filtX
      split_ifs with hp
      · rw [show Fintype.card S + 1 - (p + 1) = Fintype.card S - p by omega]
        exact disjoint_outerSpan_outerLt _
      · exact disjoint_bot_left
    · have := hd.dd' S x
      rwa [twDiff, add_comm] at this
    · unfold filtX at hu ⊢
      split_ifs at hu ⊢ with hp
      · exact leafMap_mem_outerSpanP _ hu
      · rw [Submodule.mem_bot] at hu ⊢
        rw [hu, map_zero]
    · unfold filtX at hu
      split_ifs at hu with hp
      · rw [show Fintype.card S + 1 - (p + 1) = Fintype.card S - p by omega]
        exact twD_mem_outerLt ε' hd.hβ' hd.hβ1' hu
      · rw [Submodule.mem_bot] at hu
        rw [hu, map_zero]
        exact zero_mem _
    · rw [LinearMap.add_apply]
      exact add_mem (leafMap_mem_outerSpanP _ hw) (twD_mem_outerLt_of_lt ε' hd.hβ' hd.hβ1' hw)
  split' p := by
    refine ⟨?_, fun x => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw => ?_⟩
    · unfold filtX
      split_ifs with hp
      · rw [show Fintype.card S + 1 - (p + 1) = Fintype.card S - p by omega]
        exact disjoint_outerSpan_outerLt _
      · exact disjoint_bot_left
    · have := hd.dd S x
      rwa [twDiff, add_comm] at this
    · unfold filtX at hu ⊢
      split_ifs at hu ⊢ with hp
      · exact leafMap_mem_outerSpanP _ hu
      · rw [Submodule.mem_bot] at hu ⊢
        rw [hu, map_zero]
    · unfold filtX at hu
      split_ifs at hu with hp
      · rw [show Fintype.card S + 1 - (p + 1) = Fintype.card S - p by omega]
        exact twD_mem_outerLt ε hd.hβ hd.hβ1 hu
      · rw [Submodule.mem_bot] at hu
        rw [hu, map_zero]
        exact zero_mem _
    · rw [LinearMap.add_apply]
      exact add_mem (leafMap_mem_outerSpanP _ hw) (twD_mem_outerLt_of_lt ε hd.hβ hd.hβ1 hw)
  hom p := by
    refine ⟨fun u hu => ?_, fun w hw => map₂_mem_outerSpanP _ hw, fun x => hd.leaf_comm x,
      fun x => hd.nat S x⟩
    unfold filtX at hu ⊢
    split_ifs at hu ⊢ with hp
    · exact map₂_mem_outerSpanP _ hu
    · rw [Submodule.mem_bot] at hu ⊢
      rw [hu, map_zero]
  sup p := filt_sup P' p
  sup' p := filt_sup P p
  top := by rw [Nat.sub_self, outerLt_zero]
  top' := by rw [Nat.sub_self, outerLt_zero]

/-- **The comparison lemma, forward**: if `g` is a quasi-isomorphism in every arity, so is
`1 ∘ g : C ∘_β' P' → C ∘_β P`, over a field of characteristic zero. -/
theorem TwCompareData.qiso
    (hs : ∀ (A : Type) [Fintype A] [DecidableEq A],
      FreeGrL.SurjAt R D'.toSpEnd D.toSpEnd g.toGrSpeciesHom A)
    (hi : ∀ (A : Type) [Fintype A] [DecidableEq A],
      FreeGrL.InjAt R D'.toSpEnd D.toSpEnd g.toGrSpeciesHom A) :
    QIso.Surj ⊤ ⊤ (twDiff R C ε' D' β' S) (twDiff R C ε D β S)
        ((map₂ idSpHom g.toGrSpeciesHom).app S)
      ∧ QIso.Inj ⊤ ⊤ (twDiff R C ε' D' β' S) (twDiff R C ε D β S)
        ((map₂ idSpHom g.toGrSpeciesHom).app S) := by
  obtain ⟨s'⟩ := Splitting.exists_of_field D'.toSpEnd (fun A _ _ x => hd.hD' A x)
  obtain ⟨s⟩ := Splitting.exists_of_field D.toSpEnd (fun A _ _ x => hd.hD A x)
  obtain ⟨k, hk⟩ := exists_compat g.toGrSpeciesHom (fun A _ _ x => (hd.hg A x).symm) s' s
    (fun _ => True) (fun n _ => hs (Fin n)) (fun n _ => hi (Fin n))
  have hpiece : ∀ p, QIso.Surj (filtX P' S p) (filtX P S p) (leafD R C D' S) (leafD R C D S)
        ((map₂ idSpHom g.toGrSpeciesHom).app S)
      ∧ QIso.Inj (filtX P' S p) (filtX P S p) (leafD R C D' S) (leafD R C D S)
        ((map₂ idSpHom g.toGrSpeciesHom).app S) := fun p => by
    unfold filtX
    split_ifs with hp
    · have hX := le_antisymm (outerSpanP_le_outerEig (R := R) (M := C) (N := P') (S := S)
        (Fintype.card S - p)) (outerEig_le_outerSpan _)
      have hX' := le_antisymm (outerSpanP_le_outerEig (R := R) (M := C) (N := P) (S := S)
        (Fintype.card S - p)) (outerEig_le_outerSpan _)
      rw [hX, hX']
      refine qiso_leaf s' s g.toGrSpeciesHom (fun A _ _ y => hd.hg A y) k _
        (fun x _ => ?_) (fun y _ => ?_)
      · rw [map₂_map₂ k (s.p.toHom.comp (g.toGrSpeciesHom.comp s'.p.toHom)) s'.p.toHom
          (fun A _ _ y => (hk A trivial).1 y)]
      · rw [map₂_map₂ (s.p.toHom.comp (g.toGrSpeciesHom.comp s'.p.toHom)) k s.p.toHom
          (fun A _ _ y => (hk A trivial).2 y)]
    · exact ⟨QIso.surj_bot _ _ _, QIso.inj_bot _ _ _⟩
  have h := QIso.qiso_filt hd.filtData (fun p => (hpiece p).1) (fun p => (hpiece p).2) 0
  rw [Nat.sub_zero, outerLt_eq_top hd.hP0', outerLt_eq_top hd.hP0] at h
  have e1 : leafD R C D' S + twD ε' β' S = twDiff R C ε' D' β' S := add_comm _ _
  have e2 : leafD R C D S + twD ε β S = twDiff R C ε D β S := add_comm _ _
  rwa [e1, e2] at h

end Compare

end GrComposite

end Operad
